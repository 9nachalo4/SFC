# -*- coding: utf-8 -*-
import os
import sys
import json
import queue
from collections import OrderedDict
import uuid
import tempfile
import base64
import secrets
import hmac
import traceback
import winsound
import math
import struct
import wave
from tkinter import ttk
from datetime import timedelta
import threading
import time
import hashlib
import ctypes
from ctypes import wintypes
import io
import re
import subprocess
import tkinter as tk
from tkinter import filedialog, messagebox, colorchooser, simpledialog
from tkinter import font as tkfont
from datetime import datetime

from PIL import Image, ImageTk, ImageOps
import mss

try:
    from pynput import mouse as pynput_mouse
    HAS_PYNPUT = True
except ImportError:
    HAS_PYNPUT = False

try:
    import firebase_admin
    from firebase_admin import credentials, db as fb_db
    HAS_FIREBASE = True
except (ImportError, OSError) as _firebase_import_error:
    HAS_FIREBASE = False
    FIREBASE_IMPORT_ERROR = repr(_firebase_import_error)
else:
    FIREBASE_IMPORT_ERROR = None

if getattr(sys, "frozen", False):
    BASE_DIR = os.path.dirname(os.path.abspath(sys.executable))
    if hasattr(sys, "_MEIPASS"):
        BUNDLE_DIR = sys._MEIPASS
    else:
        BUNDLE_DIR = BASE_DIR
else:
    BASE_DIR = os.path.dirname(os.path.abspath(__file__))
    BUNDLE_DIR = BASE_DIR

TESS_DIR = os.path.join(BUNDLE_DIR, "tesseract")
TESS_EXE = os.path.join(TESS_DIR, "tesseract.exe")
TESSDATA = os.path.join(TESS_DIR, "tessdata")
DEFAULT_IMAGES_DIR = os.path.join(BASE_DIR, "images")
CONFIG_PATH = os.path.join(BASE_DIR, "config.json")
HISTORY_PATH = os.path.join(BASE_DIR, "history.json")

# Console diagnostics are written to a persistent local file even in --windowed mode.
CONSOLE_LOG_PATH = os.path.join(BASE_DIR, "sfc_diagnostics.log")
CONSOLE_PASSWORD_PATH = os.path.join(BASE_DIR, ".sfc_console_auth.json")

DEBUG_LEVEL = os.environ.get("SFC_DEBUG_LEVEL", "DETAIL").upper()
_DEBUG_RANK = {"OFF": 0, "ERROR": 1, "INFO": 2, "DETAIL": 3}
_DEBUG_THROTTLE = {}
_DEBUG_LOCK = threading.RLock()

def debug_event(group, message, *, level="DETAIL", interval=0, **fields):
    """Structured log events. Never put passwords, service-account JSON or auth tokens here."""
    if _DEBUG_RANK.get(level, 3) > _DEBUG_RANK.get(DEBUG_LEVEL, 3):
        return
    try:
        now = time.monotonic()
        key = (group, message)
        with _DEBUG_LOCK:
            if interval and now - _DEBUG_THROTTLE.get(key, -1e10) < interval:
                return
            _DEBUG_THROTTLE[key] = now
        # Truncate values and keep structured output legible.
        parts = []
        for field, value in fields.items():
            if any(secret in field.lower() for secret in ("password", "secret", "token", "credential", "private", "keyfile")):
                continue
            if isinstance(value, (dict, list)):
                value = json.dumps(value, ensure_ascii=False, default=str)
            value = str(value).replace("\n", " ").replace("\r", " ")
            parts.append(f"{field}={value[:180]!r}")
        print(f"[{datetime.now().isoformat(timespec='milliseconds')}] [{level}] [{group}] {message} " + " ".join(parts), flush=True)
    except Exception:
        pass

def _install_tk_exception_logger(root):
    def callback(tp, value, tb):
        debug_event("TK", "Callback failed", level="ERROR", error=repr(value))
        traceback.print_exception(tp, value, tb)
    root.report_callback_exception = callback


class _LogWriter:
    """Thread-safe text sink for print(), stderr and tracebacks in a windowed EXE."""
    def __init__(self, path):
        self.lock = threading.RLock()
        self.path = path
        self.encoding = "utf-8"
        # Avoid infinite growth: rotate on startup if the previous log is large.
        try:
            if os.path.exists(path) and os.path.getsize(path) > 5 * 1024 * 1024:
                os.replace(path, path + ".old")
        except OSError:
            pass
        self.file = open(path, "a", encoding="utf-8", buffering=1, errors="replace")
        self.original_stdout = sys.stdout
        self.original_stderr = sys.stderr

    def write(self, value):
        if not isinstance(value, str):
            value = str(value)
        with self.lock:
            self.file.write(value)
            self.file.flush()
            if self.original_stdout is not None:
                try:
                    self.original_stdout.write(value)
                    self.original_stdout.flush()
                except Exception:
                    pass
        return len(value)

    def flush(self):
        with self.lock:
            self.file.flush()

    def isatty(self):
        return False


def _start_console_logging():
    log = _LogWriter(CONSOLE_LOG_PATH)
    sys.stdout = log
    sys.stderr = log
    def unhandled(tp, value, tb):
        traceback.print_exception(tp, value, tb, file=log)
    sys.excepthook = unhandled
    debug_event("START", "Diagnostics enabled", level="INFO", logfile=CONSOLE_LOG_PATH, debug_level=DEBUG_LEVEL, frozen=getattr(sys,"frozen",False), version=sys.version.split()[0])
    if hasattr(threading, "excepthook"):
        def thread_unhandled(args):
            unhandled(args.exc_type, args.exc_value, args.exc_traceback)
        threading.excepthook = thread_unhandled
    return log


def _password_hash(password, salt):
    return hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 260000)


def _check_console_password(parent, lang):
    """Create/verify password before granting UI access to the diagnostic log."""
    is_pl = lang == "pl"
    title = "Konsola diagnostyczna" if is_pl else "Консоль діагностики"
    try:
        if not os.path.isfile(CONSOLE_PASSWORD_PATH):
            messagebox.showinfo(title,
                "Ustaw hasło (co najmniej 8 znaków), aby chronić dostęp do logów."
                if is_pl else "Створіть пароль (від 8 символів) для доступу до логів.",
                parent=parent)
            p1 = simpledialog.askstring(title, "Nowe hasło:" if is_pl else "Новий пароль:",
                                        show="*", parent=parent)
            if p1 is None:
                return False
            if len(p1) < 8:
                messagebox.showwarning(title, "Minimum 8 znaków." if is_pl else "Мінімум 8 символів.", parent=parent)
                return False
            p2 = simpledialog.askstring(title, "Powtórz hasło:" if is_pl else "Повторіть пароль:",
                                        show="*", parent=parent)
            if p2 is None or not hmac.compare_digest(p1, p2):
                messagebox.showerror(title, "Hasła się różnią." if is_pl else "Паролі не збігаються.", parent=parent)
                return False
            salt = secrets.token_bytes(16)
            blob = {"version": 1, "salt": base64.b64encode(salt).decode("ascii"),
                    "hash": base64.b64encode(_password_hash(p1, salt)).decode("ascii")}
            with open(CONSOLE_PASSWORD_PATH, "x", encoding="utf-8") as f:
                json.dump(blob, f)
            return True
        with open(CONSOLE_PASSWORD_PATH, "r", encoding="utf-8") as f:
            blob = json.load(f)
        salt = base64.b64decode(blob["salt"], validate=True)
        expected = base64.b64decode(blob["hash"], validate=True)
        password = simpledialog.askstring(title,
            "Podaj hasło:" if is_pl else "Введіть пароль:", show="*", parent=parent)
        if password is None:
            return False
        if not hmac.compare_digest(_password_hash(password, salt), expected):
            messagebox.showerror(title, "Nieprawidłowe hasło." if is_pl else "Неправильний пароль.", parent=parent)
            return False
        return True
    except Exception as ex:
        print("Помилка захисту консолі:", repr(ex))
        messagebox.showerror(title, str(ex), parent=parent)
        return False


def _open_console_log(parent, lang):
    if not _check_console_password(parent, lang):
        return
    # The console is an independent viewer: closing it will not terminate OCR.
    try:
        if os.name != "nt":
            messagebox.showinfo("SFC Solutions", CONSOLE_LOG_PATH, parent=parent)
            return
        logpath = CONSOLE_LOG_PATH.replace("'", "''")
        command = ("Get-Content -LiteralPath '" + logpath +
                   "' -Encoding UTF8 -Tail 80 -Wait")
        subprocess.Popen(
            ["cmd.exe", "/d", "/k", "powershell.exe", "-NoProfile", "-Command", command],
            cwd=BASE_DIR,
            creationflags=getattr(subprocess, "CREATE_NEW_CONSOLE", 0),
            close_fds=True)
        print("[DIAGNOSTICS] Console viewer opened")
    except Exception as ex:
        print("[DIAGNOSTICS] Could not open console:", repr(ex))
        messagebox.showerror("SFC Solutions", str(ex), parent=parent)

FIREBASE_DB_URL = "https://gumanumber-89603-default-rtdb.firebaseio.com"
FIREBASE_ROOT = "workshop-1/history"

# ============================================================
# ВСТАВТЕ СЮДИ ВМІСТ ВАШОГО serviceAccountKey.json ЯК ОДИН РЯДОК
# ============================================================
# Place Firebase service-account JSON into firebase-service-account.json next to app.py.
# The original uploaded source contained a private key. Do not distribute that version.
SERVICE_ACCOUNT_PATH = os.environ.get("SFC_FIREBASE_KEY", os.path.join(BASE_DIR, "firebase-service-account.json"))


APP_NAME = "SFC Solutions"

TRANSLATIONS = {
    "uk": {
        "window_title": APP_NAME,
        "select_region_hint": "Виділіть область мишею. Esc — скасувати.",
        "title_ocr": APP_NAME,
        "no_match": "немає збігів",
        "image_open_error": "не вдалося відкрити файл",
        "select_images_dir": "Виберіть папку з фото",
        "lists_editor_title": "Редагування списків номерів",
        "lists": "Списки",
        "add": "+ Додати",
        "delete": "− Видалити",
        "key_label": "Ключ (латиницею, без пробілів):",
        "name_uk_label": "Назва (укр.):",
        "name_pl_label": "Назва (пол.):",
        "color_label": "Колір тексту:",
        "numbers_label": "Номери (по одному на рядок):",
        "save": "Зберегти",
        "cancel": "Скасувати",
        "new_list_title": "Новий список",
        "new_list_prompt": "Ключ (латиницею):",
        "key_exists": "Такий ключ уже існує",
        "cannot_delete_none": "Список 'none' видаляти не можна",
        "confirm_delete": "Видалити список '{key}'?",
        "confirm": "Підтвердження",
        "warning": "Увага",
        "lang_button": "PL",
        "history_title": "Історія номерів",
        "history_search": "Пошук:",
        "history_empty": "Історія порожня",
        "history_clear": "Очистити історію",
        "history_confirm_clear": "Очистити всю історію?",
        "history_found": "Знайдено: {count}",
        "history_not_found": "Не знайдено",
        "click_area_hint": "Виділіть область фіксації кліків. Esc — скасувати.",
        "click_area_set": "Область кліків: {w}×{h}",
        "click_area_none": "Область кліків не задана",
        "last_number": "Останній номер: {num}",
        "number_saved": "Збережено: {num}",
        "number_invalid": "Номер не відповідає формату",
        "pynput_missing": "Для фіксації кліків потрібен pynput. Встановіть: pip install pynput",
        "last_valid": "Останній валідний: {num}",
        "history_with_product": "{num} → {product}",
        "history_only_number": "{num}",
        "firebase_sent": "Надіслано на сервер: {num}",
        "firebase_error": "Помилка відправки: {err}",
        "menu_button": "Меню",
        "menu_images_dir": "Папка з фото…",
        "menu_select_region": "Виділити область OCR…",
        "menu_click_area": "Область кліків…",
        "menu_history": "Історія номерів…",
        "menu_lists": "Редагування списків…",
        "matched_by_number": "знайдено за номером",
        "matched_by_product": "знайдено за продуктом",
        "product_prefix": "продукт",
        "type_none": "НЕ В СПИСКУ",
        "type_none_color": "#888888",
    },
    "pl": {
        "window_title": APP_NAME,
        "select_region_hint": "Zaznacz obszar myszą. Esc — anuluj.",
        "title_ocr": APP_NAME,
        "no_match": "brak dopasowań",
        "image_open_error": "nie udało się otworzyć pliku",
        "select_images_dir": "Wybierz folder ze zdjęciami",
        "lists_editor_title": "Edycja list numerów",
        "lists": "Listy",
        "add": "+ Dodaj",
        "delete": "− Usuń",
        "key_label": "Klucz (łaciną, bez spacji):",
        "name_uk_label": "Nazwa (ukr.):",
        "name_pl_label": "Nazwa (pol.):",
        "color_label": "Kolor tekstu:",
        "numbers_label": "Numery (po jednym w wierszu):",
        "save": "Zapisz",
        "cancel": "Anuluj",
        "new_list_title": "Nowa lista",
        "new_list_prompt": "Klucz (łaciną):",
        "key_exists": "Taki klucz już istnieje",
        "cannot_delete_none": "Nie można usunąć listy 'none'",
        "confirm_delete": "Usunąć listę '{key}'?",
        "confirm": "Potwierdzenie",
        "warning": "Uwaga",
        "lang_button": "UA",
        "history_title": "Historia numerów",
        "history_search": "Szukaj:",
        "history_empty": "Historia jest pusta",
        "history_clear": "Wyczyść historię",
        "history_confirm_clear": "Wyczyścić całą historię?",
        "history_found": "Znaleziono: {count}",
        "history_not_found": "Nie znaleziono",
        "click_area_hint": "Zaznacz obszar rejestracji kliknięć. Esc — anuluj.",
        "click_area_set": "Obszar kliknięć: {w}×{h}",
        "click_area_none": "Obszar kliknięć nie ustawiony",
        "last_number": "Ostatni numer: {num}",
        "number_saved": "Zapisano: {num}",
        "number_invalid": "Numer nie pasuje do formatu",
        "pynput_missing": "Do rejestracji kliknięć wymagany jest pynput. Zainstaluj: pip install pynput",
        "last_valid": "Ostatni prawidłowy: {num}",
        "history_with_product": "{num} → {product}",
        "history_only_number": "{num}",
        "firebase_sent": "Wysłano na serwer: {num}",
        "firebase_error": "Błąd wysyłki: {err}",
        "menu_button": "Menu",
        "menu_images_dir": "Folder ze zdjęciami…",
        "menu_select_region": "Zaznacz obszar OCR…",
        "menu_click_area": "Obszar kliknięć…",
        "menu_history": "Historia numerów…",
        "menu_lists": "Edycja list…",
        "matched_by_number": "znaleziono po numerze",
        "matched_by_product": "znaleziono po produkcie",
        "product_prefix": "produkt",
        "type_none": "POZA LISTĄ",
        "type_none_color": "#888888",
    },
}


def tr(lang, key, **kwargs):
    text = TRANSLATIONS.get(lang, TRANSLATIONS["uk"]).get(key, key)
    if kwargs:
        try:
            text = text.format(**kwargs)
        except Exception:
            pass
    return text


def get_label(info, lang):
    label_uk = info.get("label_uk", info.get("label", ""))
    label_pl = info.get("label_pl", label_uk)
    if lang == "pl":
        return label_pl or label_uk
    return label_uk or label_pl


DEFAULT_CONFIG = {
    "region": {"left": 100, "top": 100, "width": 400, "height": 80},
    "click_region": None,
    "window_anchor": None,
    "theme": "dark",
    "transparency": 100,
    "sound_enabled": True,
    "font_sizes": {"number": 12, "type": 18, "interface": 10},
    "lists_pending": False,
    "work_numbers": [],
    "code_overrides": {},
    "missing_photo_pairs": [],
    "sync_enabled": True,
    "device_id": "",
    "interval": 0.2,
    "languages": "ukr+rus+eng",
    "window": {"width": 450, "height": 370, "margin_right": 10, "margin_bottom": 10},
    "upscale": 2,
    "psm": 6,
    "images_dir": "",
    "ui_language": "uk",
    "number_lists": {
        "romania": {"label_uk": "РУМУНІЯ", "label_pl": "RUMUNIA", "color": "#4CAF50", "numbers": []},
        "morocco": {"label_uk": "МАРОККО", "label_pl": "MAROKO", "color": "#FF9800", "numbers": []},
        "selection": {"label_uk": "СЕЛЕКЦІЯ", "label_pl": "SELEKCJA", "color": "#2196F3", "numbers": []},
        "none": {"label_uk": "", "label_pl": "", "color": "#888888", "numbers": []}
    }
}

IMAGE_EXTS = (".png", ".jpg", ".jpeg", ".gif", ".bmp", ".webp")


class ImageCatalog:
    """One directory scan per refresh, O(1) indexed filename lookup.

    The scan happens off the Tk thread. An exact-path fallback covers photos
    added just before the next refresh. Image bytes are never held here.
    """
    def __init__(self, directory, stop_event, refresh_seconds=8):
        self.directory = directory
        self.stop_event = stop_event
        self.refresh_seconds = refresh_seconds
        self._lock = threading.Lock()
        self._files = {}
        self.revision = 0
        self._ready = threading.Event()
        self._wakeup = threading.Event()
        self._thread = threading.Thread(target=self._run, name="SFCImageIndex", daemon=True)
        self._thread.start()

    def change_directory(self, directory):
        with self._lock:
            self.directory = directory
            self._files = {}
            self.revision += 1
            self._ready.clear()
        self._wakeup.set()

    def _run(self):
        while not self.stop_event.is_set():
            started = time.perf_counter()
            with self._lock:
                folder = self.directory
            found = {}
            scan_ok = True
            try:
                with os.scandir(folder) as entries:
                    for entry in entries:
                        if self.stop_event.is_set():
                            return
                        if not entry.is_file(follow_symlinks=False):
                            continue
                        stem, ext = os.path.splitext(entry.name)
                        if ext.lower() in IMAGE_EXTS and stem.strip():
                            # Preserve first matching extension for duplicate stems.
                            found.setdefault(stem.strip().casefold(), entry.name)
            except OSError as exc:
                scan_ok = False
                debug_event("PERFORMANCE", "Image index scan failed", level="ERROR", error=repr(exc))
            with self._lock:
                if self.directory == folder:
                    if self._files != found or self._ready.is_set() != scan_ok:
                        self.revision += 1
                    self._files = found
                    if scan_ok:
                        self._ready.set()
                    else:
                        self._ready.clear()
            debug_event("PERFORMANCE", "Image index ready", level="INFO",
                        count=len(found), scan_ms=round((time.perf_counter()-started)*1000, 2))
            self._wakeup.wait(self.refresh_seconds)
            self._wakeup.clear()

    def snapshot_names(self):
        with self._lock:
            return set(self._files)

    def lookup_number(self, number):
        number = str(number).strip().casefold()
        with self._lock:
            found = self._files.get(number)
            folder = self.directory
        if found:
            return found
        # Handle newly added files before the next directory scan.
        if number and (number.isdigit() or number.isalnum()):
            for ext in IMAGE_EXTS:
                for variant in (ext, ext.upper()):
                    candidate = number + variant
                    if os.path.isfile(os.path.join(folder, candidate)):
                        self._wakeup.set()
                        return candidate
        return None

    def lookup_text(self, text):
        normalized = " ".join(str(text).casefold().split())
        if not normalized:
            return None
        # Most SFC names are 5- or 7-digit numbers; direct dictionary lookup.
        tokens = re.findall(r"\w+", normalized, flags=re.UNICODE)
        best, longest = None, 0
        for token in tokens:
            name = self.lookup_number(token)
            if name and len(token) > longest:
                best, longest = name, len(token)
        return best


def load_config():
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))
    if os.path.exists(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                user = json.load(f)
            for k, v in user.items():
                if k not in ("number_lists", "code_overrides") and isinstance(v, dict) and isinstance(cfg.get(k), dict):
                    cfg[k].update(v)
                else:
                    cfg[k] = v
        except Exception as e:
            print("Помилка config.json:", e)
    for _key, info in cfg.get("number_lists", {}).items():
        if isinstance(info, dict):
            if "label" in info and "label_uk" not in info:
                info["label_uk"] = info.get("label", "")
            if "label_uk" not in info:
                info["label_uk"] = ""
            if "label_pl" not in info:
                info["label_pl"] = info.get("label_uk", "")
    return cfg


def save_setting(key, value):
    data = {}
    if os.path.exists(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            pass
    if key not in ("number_lists", "code_overrides") and isinstance(value, dict) and isinstance(data.get(key), dict):
        data[key].update(value)
    else:
        data[key] = value
    with open(CONFIG_PATH, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


def save_region(region):
    save_setting("region", region)


def save_click_region(region):
    save_setting("click_region", region)


def resolve_images_dir(cfg):
    d = (cfg.get("images_dir") or "").strip()
    if d and os.path.isdir(d):
        return d
    return DEFAULT_IMAGES_DIR


HISTORY_LOCK = threading.RLock()

def normalize_record(record):
    if not isinstance(record, dict):
        return None
    row = dict(record)
    if not row.get("id"):
        # Existing records should keep stable IDs across restarts.
        raw = json.dumps({k: row.get(k, "") for k in ("number", "product", "time")}, sort_keys=True, ensure_ascii=False)
        row["id"] = hashlib.sha256(raw.encode("utf-8")).hexdigest()[:32]
    row.setdefault("device_id", "legacy")
    row.setdefault("type_key", "")
    return row


def load_history():
    if os.path.exists(HISTORY_PATH):
        try:
            with open(HISTORY_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            rows = [x for row in data if (x := normalize_record(row))] if isinstance(data, list) else []
            debug_event("HISTORY", "Local history loaded", level="INFO", count=len(rows))
            return rows
        except Exception as exc:
            print("Помилка читання локальної історії:", exc)
    return []


def save_history(history):
    try:
        with HISTORY_LOCK:
            fd, temp = tempfile.mkstemp(prefix="history_", suffix=".tmp", dir=BASE_DIR)
            try:
                with os.fdopen(fd, "w", encoding="utf-8") as f:
                    json.dump(history, f, ensure_ascii=False, indent=2)
                os.replace(temp, HISTORY_PATH)
                debug_event("HISTORY", "Local history written", interval=5, count=len(history))
            finally:
                if os.path.exists(temp):
                    os.unlink(temp)
    except Exception as exc:
        print("Помилка запису історії:", exc)


def shift_info(timestamp=None):
    dt = datetime.fromisoformat(timestamp) if timestamp else datetime.now()
    # A night shift belongs to the day on which it began.
    if 6 <= dt.hour < 14:
        return dt.date().isoformat(), 1
    if 14 <= dt.hour < 22:
        return dt.date().isoformat(), 2
    day = dt.date() if dt.hour >= 22 else (dt - timedelta(days=1)).date()
    return day.isoformat(), 3


def current_shift_rows(history):
    day, shift = shift_info()
    result = []
    for row in history:
        try:
            if shift_info(row.get("time"))[0:2] == (day, shift):
                result.append(row)
        except (ValueError, TypeError):
            pass
    return result


def is_valid_number(num):
    num = str(num).strip()
    if not num.isdigit():
        return False
    if len(num) == 5 and num[:2] in ("15", "50", "51", "52", "53"):
        return True
    if len(num) == 7 and num[:2] == "16":
        return True
    return False


def build_product_index(history):
    """product -> number (останнє актуальне значення)."""
    index = {}
    for record in history:
        product = str(record.get("product", "")).strip()
        number = str(record.get("number", "")).strip()
        if product and number:
            index[product] = number
    return index


def build_number_index(history):
    """number -> product (останнє актуальне значення)."""
    index = {}
    for record in history:
        product = str(record.get("product", "")).strip()
        number = str(record.get("number", "")).strip()
        if product and number:
            index[number] = product
    return index


def ordered_product_codes(history, overrides=None):
    """Raw observed codes, newest first; corrections never rewrite print history."""
    result = {}
    for row in sorted(history, key=lambda r: str(r.get('time') or '')):
        num, code = str(row.get('number') or '').strip(), str(row.get('product') or '').strip()
        if is_valid_number(num) and code:
            codes = result.setdefault(num, {})
            codes.pop(code, None)
            codes[code] = None
    return {num: list(reversed(codes)) for num, codes in result.items()}


def effective_codes(number, raw_codes, overrides):
    rule = overrides.get(number, {}) or {}
    corrections = rule.get('corrections', {}) or {}
    codes = list(dict.fromkeys(str(corrections.get(code, code)) for code in raw_codes))
    preferred = rule.get('preferred')
    if preferred in codes:
        codes.remove(preferred)
        codes.insert(0, preferred)
    return codes


def parse_work_numbers(text):
    tokens = re.split(r'[\s,;]+', text.strip()) if text.strip() else []
    return list(dict.fromkeys(n for n in tokens if is_valid_number(n))), list(dict.fromkeys(n for n in tokens if not is_valid_number(n)))


# Numeric fields sometimes contain the insertion caret or brackets drawn by the
# source application. Remove only these artifacts, never a real digit (e.g. 1).
_OCR_ARTIFACTS = str.maketrans('', '',
    "|¦‖∣❘❙❚ǀǁ｜[]{}()［］｛｝（）【】〔〕⟦⟧⦗⦘!！‼❗❕¡"
    "▏▎▍▌▐▕│┃╎╏┆┇┊┋_‗·•`´'\u200b\u200c\u200d\u200e\u200f\ufeff")


def clean_ocr_text(text):
    return (text or '').translate(_OCR_ARTIFACTS)


def remove_ocr_edge_caret(frame):
    """Remove an isolated, unusually tall straight caret/bracket before OCR.

    Operate on a normalized dark-on-light image at original resolution.
    Reject ambiguous strokes, including normal-height digit 1 and touching
    glyphs. Ignore horizontal field borders when measuring glyph height.
    """
    w, h = frame.size
    if w < 5 or h < 5 or w > 1600 or h > 500:
        return frame
    mask = frame.point(lambda v: 255 if v < 160 else 0).tobytes()
    cols = [[] for _ in range(w)]
    for y in range(h):
        line = mask[y*w:(y+1)*w]
        if line.count(255) >= max(4, int(w * .75)):
            continue
        for x, value in enumerate(line):
            if value:
                cols[x].append(y)
    spans = []
    x = 0
    while x < w:
        if not cols[x]:
            x += 1
            continue
        a = x
        while x < w and cols[x]:
            x += 1
        b = x - 1
        ys = [y for xx in range(a, b + 1) for y in cols[xx]]
        spans.append((a, b, min(ys), max(ys)))
    if len(spans) < 2:
        return frame
    heights = sorted(y1-y0+1 for _, _, y0, y1 in spans)
    # Lower median avoids letting the single tall caret set the text height.
    normal = heights[(len(heights)-1)//2]
    if normal < 6:
        return frame
    result = frame
    # A pair of adjacent square brackets can merge into a closed rectangle
    # at small font sizes. Tesseract may read the entire pair as digit 1 or 0.
    # Require two full-height side rails, horizontal caps, an empty middle,
    # and a height exceeding that of the real digits. This is intentionally
    # stricter than a generic rectangle detector (never trim a normal 0).
    for a, b, y0, y1 in spans:
        width, height = b-a+1, y1-y0+1
        if (height < normal + max(2, round(normal*.15)) or width < 4
                or width > height*.85):
            continue
        rail_width = max(1, (width+2)//3)
        left = range(a, a+rail_width)
        right = range(b-rail_width+1, b+1)
        if max(len(cols[x]) for x in left) < height*.90:
            continue
        if max(len(cols[x]) for x in right) < height*.90:
            continue
        cap = max(1, round(height*.15))
        def coverage(y):
            return sum(y in cols[x] for x in range(a,b+1))
        if (max(coverage(y) for y in range(y0,y0+cap)) < width*.80 or
                max(coverage(y) for y in range(y1-cap+1,y1+1)) < width*.80):
            continue
        middle_x = range(a+rail_width,b-rail_width+1)
        middle_y = range(y0+cap,y1-cap+1)
        # A genuine interior gap is mandatory; do not remove solid glyphs.
        area = len(middle_x)*len(middle_y)
        if not area or sum(y in cols[x] for x in middle_x for y in middle_y) > area*.15:
            continue
        if result is frame:
            result = frame.copy()
        result.paste(255, (a, y0, b+1, y1+1))
        debug_event('OCR', 'Merged bracket pair removed', interval=2)
    # Estimate actual glyph baseline from several similarly sized characters.
    # Walk inwards from BOTH edges, removing a consecutive group of tall
    # caret/bracket strokes (e.g. 51117|[). Stop at the first ordinary glyph.
    core = [s for s in spans if abs((s[3]-s[2]+1)-normal) <= max(1, round(normal*.10))]
    if len(core) >= 3:
        tops = sorted(s[2] for s in core)
        bottoms = sorted(s[3] for s in core)
        top, bottom = tops[len(tops)//2], bottoms[len(bottoms)//2]
        aligned = [s for s in core if abs(s[2]-top) <= 1 and abs(s[3]-bottom) <= 1]
        if len(aligned) >= 3:
            def edge_artifact(s):
                a,b,y0,y1 = s
                width, height = b-a+1, y1-y0+1
                excess = max(2, round(normal*.18))
                if height < normal + excess or width > max(2, round(height*.40)):
                    return False
                # Taller than the normal text line, not simply a narrow 1.
                if max(top-y0, y1-bottom) < excess:
                    return False
                if min(y1,bottom)-max(y0,top)+1 < normal*.70:
                    return False
                rail = max(len(cols[x]) for x in range(a,b+1))
                if rail < height*.78:
                    return False
                middle = [sum(y in cols[x] for x in range(a,b+1))
                          for y in range(y0+height//4, y1-height//4+1)]
                return bool(middle) and sum(v <= max(2, round(width*.75)) for v in middle) >= len(middle)*.70
            # Previously removed rectangular bracket pairs must not block
            # detection of another caret just inside them.
            remaining = [s for s in spans if result is frame or
                         result.crop((s[0],s[2],s[1]+1,s[3]+1)).getextrema()[0] < 160]
            for direction in (1,-1):
                ordered = remaining if direction == 1 else remaining[::-1]
                for s in ordered:
                    if len(remaining) <= 3 or not edge_artifact(s):
                        break
                    a,b,y0,y1 = s
                    if result is frame:
                        result = frame.copy()
                    # Also clear antialiasing just above/below the stroke,
                    # but never widen the erased area into adjacent digits.
                    result.paste(255, (a, max(0,y0-1), b+1, min(h,y1+2)))
                    remaining = [other for other in remaining if other != s]
                    debug_event('OCR', 'Trailing/leading caret group removed', interval=2)
    for idx in (0, len(spans)-1):
        a,b,y0,y1 = spans[idx]
        width, height = b-a+1, y1-y0+1
        if height < normal + max(2, round(normal*.18)) or width > max(2, round(height*.40)):
            continue
        neighbor = spans[1] if idx == 0 else spans[-2]
        gap = neighbor[0]-b-1 if idx == 0 else a-neighbor[1]-1
        if gap < 1:
            continue
        # Same text line, but the cursor extends beyond normal glyphs.
        if min(y1,neighbor[3])-max(y0,neighbor[2])+1 < normal*.65:
            continue
        rail = max(len(cols[xx]) for xx in range(a,b+1))
        if rail < height*.78:
            continue
        # The middle of a bracket/caret has only a vertical stroke; a digit
        # with a diagonal or a rounded bowl is not removed.
        middle = [sum(y in cols[xx] for xx in range(a,b+1))
                  for y in range(y0+height//4, y1-height//4+1)]
        if not middle or max(middle) > max(2, round(width*.60)):
            continue
        if result is frame:
            result = frame.copy()
        result.paste(255, (a, y0, b+1, y1+1))
    return result


def ocr_contrast_images(img):
    """Choose the channel with the most contrast; retain grayscale as fallback."""
    def span(channel):
        hist = channel.histogram()
        count = channel.width * channel.height
        cutoff = max(1, int(count * .005))
        def edge(values):
            total = 0
            for i, n in enumerate(values):
                total += n
                if total >= cutoff:
                    return i
            return 0
        return 255 - edge(reversed(hist)) - edge(hist)
    def normalize(channel):
        # Tesseract prefers dark glyphs on a light background. Most pixels
        # in the selected OCR region are the field background.
        g = ImageOps.autocontrast(channel, cutoff=0.2)
        hist = g.histogram()
        if sum(hist[:128]) > sum(hist[128:]):
            g = ImageOps.invert(g)
        return g
    gray = img.convert('L')
    channels = [gray, *img.convert('RGB').split()]
    ranked = sorted(channels, key=span, reverse=True)
    first = normalize(ranked[0])
    second = normalize(gray if ranked[0] is not gray else ranked[1])
    return first, second if first.tobytes() != second.tobytes() else None


from collections import Counter

def ocr_remove_field_border(img):
    """Trim paired long field borders without trimming individual glyphs."""
    img = img.convert('RGB')
    w, h = img.size
    if w < 12 or h < 8 or w > 1600 or (h > 100):
        return img
    pix = img.load()
    lines = []
    for y in range(h):
        c, n = Counter((pix[x, y] for x in range(w))).most_common(1)[0]
        if n >= w * 0.65 and max(c) - min(c) < 15 and (65 <= sum(c) / 3 <= 220):
            lines.append(y)
    pairs = [(a, b) for a in lines for b in lines if 8 <= b - a <= 60]
    if pairs:
        a, b = max(pairs, key=lambda p: p[1] - p[0])
        img = img.crop((0, a + 1, w, b))
        w, h = img.size
    pix = img.load()
    borders = []
    for x in range(w):
        c, n = Counter((pix[x, y] for y in range(h))).most_common(1)[0]
        if n >= h * 0.85 and max(c) - min(c) < 15 and (65 <= sum(c) / 3 <= 220):
            borders.append(x)
    left = [x for x in borders if x < min(8, w * 0.12)]
    right = [x for x in borders if x >= w - min(8, w * 0.12)]
    if left and right and (max(left) + 1 < min(right)):
        img = img.crop((max(left) + 1, 0, min(right), h))
    return img

def ocr_flatten_selection(img):
    """Find coloured selection rectangle and normalize its local foreground contrast."""
    w, h = img.size
    if w > 1600 or h > 100:
        return None
    p = img.load()
    runs = []
    for y in range(h):
        x = 0
        while x < w:
            c = p[x, y]
            if max(c) - min(c) < 25:
                x += 1
                continue
            a = x
            x += 1
            while x < w and max((abs(p[x, y][i] - c[i]) for i in range(3))) <= 12:
                x += 1
            if x - a >= 8:
                runs.append((x - a, a, x, y, c))
    if len(runs) > 300:
        return None
    pairs = []
    for _, a, b, y, c in runs:
        for _, aa, bb, yy, cc in runs:
            if 5 <= yy - y <= 50 and abs(a - aa) <= 2 and (abs(b - bb) <= 2) and (max((abs(c[i] - cc[i]) for i in range(3))) <= 12):
                pairs.append((min(b, bb) - max(a, aa), yy - y, max(a, aa), min(b, bb), y, yy, c))
    if not pairs:
        return None
    _, _, a, b, y0, y1, c = max(pairs)
    vals = [p[x, y] for x in range(a, b) for y in range(y0, y1 + 1)]
    opts = []
    for i in range(3):
        diffs = sorted((v[i] - c[i] for v in vals))
        n = max(1, len(diffs) // 12)
        opts.extend([(-diffs[n], i, -1), (diffs[-n - 1], i, 1)])
    contrast, channel, sign = max(opts)
    if contrast < 15:
        return None
    g = img.convert('L')
    base = ImageOps.autocontrast(g, cutoff=0)
    out = base.copy()
    op = out.load()
    for x in range(max(0, a - 1), min(w, b + 1)):
        for y in range(h):
            if y0 <= y <= y1 and a <= x < b:
                op[x, y] = 255 - round(255 * min(1, max(0, sign * (p[x, y][channel] - c[channel])) / contrast))
            elif max(p[x, y]) - min(p[x, y]) >= 25:
                op[x, y] = 255
    return out

def ocr_remove_touching_edge_caret(frame):
    """Remove a uniform one-pixel edge rail only when it extends beyond
    the ordinary glyph line on BOTH sides. Never shave a digit by width.
    On ambiguous attached strokes, temporal capture is the safer method.
    """
    w, h = frame.size
    if not (10 <= w <= 1000 and 9 <= h <= 80):
        return frame
    p = frame.load()
    cols = [[y for y in range(h) if p[x,y] < 175] for x in range(w)]
    occupied = [x for x, ys in enumerate(cols) if ys]
    if len(occupied) < 10:
        return frame
    x = occupied[-1]
    ys = cols[x]
    if len(ys) < 8 or len(ys) != ys[-1]-ys[0]+1:
        return frame
    # A caret touching an antialiased digit can be a perfectly uniform rail.
    # Real glyph contours are not assumed to have that property.
    vals = [p[x,y] for y in ys[1:-1]]
    if not vals or max(vals)-min(vals) > 12:
        return frame
    # Baseline from the rest of the number, excluding the last glyph.
    core_end = x - max(4, round(len(ys)*.7))
    core = [y for xx in occupied if xx < core_end for y in cols[xx]]
    if not core or core_end <= occupied[0]+5:
        return frame
    top, bottom = min(core), max(core)
    if bottom-top+1 < 5 or ys[0] >= top or ys[-1] <= bottom:
        return frame
    if len(ys) < bottom-top+3:
        return frame
    result = frame.copy()
    result.paste(255,(x,ys[0],x+1,ys[-1]+1))
    debug_event('OCR', 'Uniform attached edge caret removed', interval=2)
    return result


def ocr_blink_pair(first, second):
    """Return the original caret-free frame when two captures differ ONLY
    by a narrow vertical stroke extending beyond the line of real digits.
    No image merging: retain a real capture, not a reconstructed digit.
    Return None for text changes, selection changes or ambiguous strokes.
    """
    if first.size != second.size:
        return None
    a, b = ocr_remove_field_border(first), ocr_remove_field_border(second)
    if a.size != b.size:
        return None
    w,h = a.size
    if not (10 <= w <= 1000 and 8 <= h <= 80):
        return None
    from PIL import ImageChops
    channels = ImageChops.difference(a,b).split()
    diff = ImageChops.lighter(ImageChops.lighter(channels[0],channels[1]),channels[2]).point(lambda v:255 if v>=8 else 0)
    box=diff.getbbox()
    if not box:
        return first
    l,t,r,bot=box
    width,height=r-l,bot-t
    if width>3 or height<7 or height<width*3:
        return None
    mask=diff.crop(box)
    if sum(mask.histogram()[1:]) < width*height*.55:
        return None
    if max(sum(diff.getpixel((x,y))>0 for y in range(t,bot)) for x in range(l,r)) < height*.85:
        return None
    # Background of the field, not a guess about which OCR string is valid.
    bg=Counter(a.getdata()).most_common(1)[0][0]
    def distance(pixel):
        return max(abs(pixel[i]-bg[i]) for i in range(3))
    pa,pb=a.load(),b.load()
    changed=[(x,y) for y in range(t,bot) for x in range(l,r) if diff.getpixel((x,y))]
    da=sum(distance(pa[x,y]) for x,y in changed)
    db=sum(distance(pb[x,y]) for x,y in changed)
    if abs(da-db) < max(20,len(changed)*12):
        return None
    clean,dirty=(a,b) if da<db else (b,a)
    cp,dp=clean.load(),dirty.load()
    # Require the dirty image to have more foreground at most changed pixels.
    if sum(distance(dp[x,y])>=distance(cp[x,y])+5 for x,y in changed)<len(changed)*.75:
        return None
    # Determine the text baseline from unchanged columns; exclude full-width
    # borders and the suspected caret columns, never assume a fixed number length.
    rows=[]
    for y in range(h):
        ink=sum(distance(cp[x,y])>=40 for x in range(w) if not l<=x<r)
        if 1<=ink<max(4,(w-width)*.65):
            rows.append(y)
    if not rows or max(rows)-min(rows)+1<5:
        return None
    if t>=min(rows) or bot<=max(rows)+1:
        return None
    return first if da<db else second


def ocr_capture_without_blink(initial, grab, wait, steps=6, delay=.13, observed=None):
    """Observe a full typical caret-on interval before accepting a new line.
    If the actual input changes mid-sampling, defer rather than mix characters.
    `wait` is the stop event's wait method, so shutdown remains responsive.
    """
    clean=initial
    seen={initial.tobytes()}
    if observed is not None:
        observed.update(seen)
    for _ in range(steps):
        if wait(delay):
            return None
        frame=grab()
        key=frame.tobytes()
        if key in seen:
            continue
        candidate=ocr_blink_pair(clean,frame)
        if candidate is None:
            return None
        seen.add(key)
        if observed is not None:
            observed.add(key)
        clean=candidate
    return clean


def ocr_prepare_line(frame, scale):
    """Normalize and pad a small single-line capture before Tesseract."""
    frame = ImageOps.autocontrast(frame, cutoff=0)
    hist = frame.histogram()
    if sum(hist[:128]) > sum(hist[128:]):
        frame = ImageOps.invert(frame)
    frame = remove_ocr_edge_caret(frame)
    frame = ocr_remove_touching_edge_caret(frame)
    mask = frame.point(lambda v: 255 if v < 170 else 0)
    box = mask.getbbox()
    if box:
        l,t,r,b = box
        frame = frame.crop((max(0,l-2), max(0,t-2), min(frame.width,r+2), min(frame.height,b+2)))
    frame = frame.resize((frame.width*scale, frame.height*scale), Image.Resampling.LANCZOS)
    return ImageOps.expand(frame, border=16, fill=255)


def ocr_numeric_signature(text):
    return tuple(re.findall(r"[0-9]+", clean_ocr_text(text)))


def recognize_ocr_line_first(img, recognize, upscale=2):
    """Fast preview: exactly the primary pass of the V7 verifier."""
    inner = ocr_remove_field_border(img)
    primary = ocr_flatten_selection(inner)
    if primary is None:
        primary = inner.convert('L')
    scale = max(3, min(6, int(upscale)))
    return clean_ocr_text(recognize(ocr_prepare_line(primary, scale), 7))


def recognize_ocr_line(img, recognize, upscale=2, first_result=None):
    """Two scale/channel views for short fields; do not choose a valid-looking
    number merely because its length happens to fit. Conflicts need agreement."""
    inner = ocr_remove_field_border(img)
    selection = ocr_flatten_selection(inner)
    gray = inner.convert('L')
    if selection is not None:
        primary = secondary = selection
        third = selection
    else:
        primary = gray
        best, alt = ocr_contrast_images(inner)
        secondary = best if best.tobytes() != gray.tobytes() else (alt or gray)
        third = gray
    scale = max(3, min(6, int(upscale)))
    first = (clean_ocr_text(recognize(ocr_prepare_line(primary, scale), 7))
             if first_result is None else first_result)
    second = clean_ocr_text(recognize(ocr_prepare_line(secondary, scale+1), 7))
    a, b = ocr_numeric_signature(first), ocr_numeric_signature(second)
    if a and a == b:
        return first
    third_text = clean_ocr_text(recognize(ocr_prepare_line(third, scale+2), 7))
    c = ocr_numeric_signature(third_text)
    if c and c == a:
        return first
    if c and c == b:
        return second
    # No confirmed number: leave the frame unresolved instead of guessing.
    debug_event('OCR', 'Single-line recognition unresolved', interval=2)
    return ''


def init_firebase():
    if not HAS_FIREBASE:
        debug_event("FIREBASE", "Import unavailable", level="ERROR", cause=FIREBASE_IMPORT_ERROR)
        print("firebase-admin не встановлено. Відправка на сервер вимкнена.")
        return False
    try:
        if not firebase_admin._apps:
            cred = credentials.Certificate(SERVICE_ACCOUNT_PATH)
            firebase_admin.initialize_app(cred, {"databaseURL": FIREBASE_DB_URL})
        debug_event("FIREBASE", "Initialized", level="INFO", key_present=os.path.isfile(SERVICE_ACCOUNT_PATH))
        print("Firebase успішно ініціалізовано.")
        return True
    except Exception as e:
        debug_event("FIREBASE", "Initialization failed", level="ERROR", error=repr(e), key_present=os.path.isfile(SERVICE_ACCOUNT_PATH))
        print(f"Помилка ініціалізації Firebase: {e}")
        return False


def send_to_firebase(record):
    if not HAS_FIREBASE or not firebase_admin._apps:
        return False, "Firebase не ініціалізовано"
    try:
        ref = fb_db.reference(FIREBASE_ROOT)
        ref.child(record["id"]).set(record)
        debug_event("FIREBASE", "Record uploaded", level="INFO", record_id=record.get("id"), kind=record.get("type_key"), shift=record.get("shift"))
        return True, ""
    except Exception as e:
        debug_event("FIREBASE", "Upload failed", level="ERROR", error=repr(e))
        print(f"Не вдалося надіслати в Firebase: {e}")
        return False, str(e)


def sync_once(history, device_id):
    if not HAS_FIREBASE or not firebase_admin._apps:
        return [], 0
    remote_ref = fb_db.reference(FIREBASE_ROOT)
    existing = remote_ref.get() or {}
    if not isinstance(existing, dict):
        existing = {}
    remote = {}
    for key, value in existing.items():
        if isinstance(value, dict):
            row = normalize_record(value)
            if row:
                remote[row["id"]] = row
    with HISTORY_LOCK:
        local = {row["id"]: dict(row) for row in history}
    to_upload = [row for key, row in local.items() if key not in remote and row.get("device_id") != "remote"]
    for row in to_upload:
        remote_ref.child(row["id"]).set(row)
    new_rows = [row for key, row in remote.items() if key not in local]
    debug_event("FIREBASE", "History sync", interval=60, local=len(local), remote=len(remote), received=len(new_rows), uploaded=len(to_upload))
    return new_rows, len(to_upload)


FIREBASE_LISTS_ROOT = "workshop-1/number_lists"

def remote_lists_get():
    if not HAS_FIREBASE or not firebase_admin._apps:
        return None
    value = fb_db.reference(FIREBASE_LISTS_ROOT).get()
    result = value if isinstance(value, dict) and isinstance(value.get("lists"), dict) else None
    debug_event("LISTS", "Remote list fetched", interval=60, available=bool(result), groups=len(result.get("lists", {})) if result else 0)
    return result


def remote_lists_set(lists, device_id):
    if not HAS_FIREBASE or not firebase_admin._apps:
        return False
    fb_db.reference(FIREBASE_LISTS_ROOT).set({
        "lists": lists, "device_id": device_id,
        "updated_at": datetime.now().isoformat(timespec="seconds")
    })
    debug_event("LISTS", "Remote lists saved", level="INFO", groups=len(lists), device=device_id)
    return True


def remote_history_get():
    if not HAS_FIREBASE or not firebase_admin._apps:
        return []
    value = fb_db.reference(FIREBASE_ROOT).get() or {}
    rows = [r for item in value.values() if (r := normalize_record(item))] if isinstance(value, dict) else []
    debug_event("HISTORY", "Remote history fetched", level="INFO", count=len(rows))
    return rows


def find_anchor_window(x, y, excluded_handle=0):
    if os.name != "nt":
        return None
    u = ctypes.windll.user32
    u.WindowFromPoint.argtypes = [wintypes.POINT]
    u.WindowFromPoint.restype = ctypes.c_void_p
    u.GetAncestor.argtypes = [ctypes.c_void_p, ctypes.c_uint]
    u.GetAncestor.restype = ctypes.c_void_p
    point = wintypes.POINT(int(x), int(y))
    hwnd = u.WindowFromPoint(point)
    if not hwnd:
        return None
    GA_ROOT = 2
    hwnd = u.GetAncestor(hwnd, GA_ROOT) or hwnd
    if hwnd == excluded_handle:
        return None
    return int(hwnd)


def window_client_origin(hwnd):
    u = ctypes.windll.user32
    u.IsWindow.argtypes = [ctypes.c_void_p]
    u.IsIconic.argtypes = [ctypes.c_void_p]
    u.ClientToScreen.argtypes = [ctypes.c_void_p, ctypes.POINTER(wintypes.POINT)]
    if not hwnd or not u.IsWindow(hwnd) or u.IsIconic(hwnd):
        return None
    point = wintypes.POINT(0, 0)
    if not u.ClientToScreen(hwnd, ctypes.byref(point)):
        return None
    return point.x, point.y


def relative_region(region, origin):
    return {**region, "left": region["left"] - origin[0], "top": region["top"] - origin[1]}


def absolute_region(region, origin):
    return {**region, "left": region["left"] + origin[0], "top": region["top"] + origin[1]}


def set_dpi_aware():
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass


def work_area():
    class RECT(ctypes.Structure):
        _fields_ = [("left", ctypes.c_long), ("top", ctypes.c_long),
                    ("right", ctypes.c_long), ("bottom", ctypes.c_long)]
    r = RECT()
    SPI_GETWORKAREA = 0x0030
    if ctypes.windll.user32.SystemParametersInfoW(SPI_GETWORKAREA, 0, ctypes.byref(r), 0):
        return r.left, r.top, r.right, r.bottom
    u = ctypes.windll.user32
    return 0, 0, u.GetSystemMetrics(0), u.GetSystemMetrics(1)


def pick_region(parent, lang, hint_key, on_done):
    u = ctypes.windll.user32
    vx, vy = u.GetSystemMetrics(76), u.GetSystemMetrics(77)
    vw, vh = u.GetSystemMetrics(78), u.GetSystemMetrics(79)

    top = tk.Toplevel(parent)
    top.overrideredirect(True)
    top.geometry(f"{vw}x{vh}{vx:+d}{vy:+d}")
    top.attributes("-topmost", True)
    top.attributes("-alpha", 0.3)
    top.configure(bg="black", cursor="crosshair")
    canvas = tk.Canvas(top, bg="black", highlightthickness=0, cursor="crosshair")
    canvas.pack(fill="both", expand=True)
    canvas.create_text(20, 20, anchor="nw", fill="white", font=("Segoe UI", 16),
                       text=tr(lang, hint_key))
    st = {"x": 0, "y": 0, "rect": None}

    def finish(region):
        top.destroy()
        on_done(region)

    def down(e):
        st["x"], st["y"] = e.x_root, e.y_root
        st["rect"] = canvas.create_rectangle(0, 0, 0, 0, outline="red", width=2)

    def move(e):
        if st["rect"]:
            canvas.coords(st["rect"], st["x"] - vx, st["y"] - vy, e.x_root - vx, e.y_root - vy)

    def up(e):
        x1, y1 = min(st["x"], e.x_root), min(st["y"], e.y_root)
        x2, y2 = max(st["x"], e.x_root), max(st["y"], e.y_root)
        if x2 - x1 > 5 and y2 - y1 > 5:
            finish({"left": x1, "top": y1, "width": x2 - x1, "height": y2 - y1})
        else:
            finish(None)

    canvas.bind("<ButtonPress-1>", down)
    canvas.bind("<B1-Motion>", move)
    canvas.bind("<ButtonRelease-1>", up)
    top.bind("<Escape>", lambda e: finish(None))
    top.focus_force()


def select_region(lang, hint_key="select_region_hint"):
    set_dpi_aware()
    root = tk.Tk()
    root.withdraw()

    def done(region):
        if region:
            save_region(region)
            print("Збережено в config.json:", region)
        root.destroy()

    pick_region(root, lang, hint_key, done)
    root.mainloop()


def fit_dialog(window, width, height, min_w=480, min_h=420):
    """Choose a usable initial size, capped by screen work area."""
    try:
        l, t, r, b = work_area()
        avail_w, avail_h = max(350, r - l - 36), max(300, b - t - 55)
        width, height = min(width, avail_w), min(height, avail_h)
        window.geometry(f"{width}x{height}")
        window.minsize(min(min_w, width), min(min_h, height))
    except Exception:
        window.geometry(f"{width}x{height}")



class ListsEditor(tk.Toplevel):
    def __init__(self, parent, cfg, lang, on_save):
        super().__init__(parent)
        self.cfg = cfg
        self.lang = lang
        self.on_save = on_save
        self.title(f"{APP_NAME} — {tr(lang, 'lists_editor_title')}")
        self.configure(bg="#202020")
        fit_dialog(self, 850, 690, 680, 540)
        self.resizable(False, False)
        self.transient(parent)
        self.grab_set()

        self.lists = json.loads(json.dumps(cfg.get("number_lists", {})))
        self._remote_baseline = json.loads(json.dumps(self.lists))
        self.current_key = tk.StringVar(value="")

        self._build_ui()
        self._refresh_list()
        if self.lists:
            self.listbox.selection_set(0)
            self._on_select()

    def _build_ui(self):
        for child in self.winfo_children():
            child.destroy()

        lang = self.lang

        left = tk.Frame(self, bg="#181818", width=170)
        left.pack(side="left", fill="y")
        left.pack_propagate(False)

        tk.Label(left, text=tr(lang, "lists"), bg="#181818", fg="#aaa",
                 font=("Segoe UI", 9, "bold")).pack(anchor="w", padx=8, pady=(8, 4))

        self.listbox = tk.Listbox(left, bg="#252525", fg="#ddd", bd=0,
                                  selectbackground="#1565c0", activestyle="none",
                                  font=("Segoe UI", 9), exportselection=False)
        self.listbox.pack(fill="both", expand=True, padx=6, pady=4)
        self.listbox.bind("<<ListboxSelect>>", self._on_select)

        btn_row = tk.Frame(left, bg="#181818")
        btn_row.pack(fill="x", padx=6, pady=6)
        tk.Button(btn_row, text=tr(lang, "add"), command=self._add_list,
                  bg="#2c2c2c", fg="#ddd", bd=0).pack(fill="x", pady=2)
        tk.Button(btn_row, text=tr(lang, "delete"), command=self._delete_list,
                  bg="#2c2c2c", fg="#ddd", bd=0).pack(fill="x", pady=2)

        right = tk.Frame(self, bg="#202020")
        right.pack(side="left", fill="both", expand=True, padx=10, pady=10)

        tk.Label(right, text=tr(lang, "key_label"), bg="#202020",
                 fg="#aaa", font=("Segoe UI", 8)).pack(anchor="w")
        self.key_entry = tk.Entry(right, bg="#2c2c2c", fg="#ddd", bd=0,
                                  insertbackground="#ddd", font=("Consolas", 10))
        self.key_entry.pack(fill="x", pady=(2, 8), ipady=4)

        tk.Label(right, text=tr(lang, "name_uk_label"), bg="#202020",
                 fg="#aaa", font=("Segoe UI", 8)).pack(anchor="w")
        self.label_uk_entry = tk.Entry(right, bg="#2c2c2c", fg="#ddd", bd=0,
                                       insertbackground="#ddd", font=("Segoe UI", 10))
        self.label_uk_entry.pack(fill="x", pady=(2, 8), ipady=4)

        tk.Label(right, text=tr(lang, "name_pl_label"), bg="#202020",
                 fg="#aaa", font=("Segoe UI", 8)).pack(anchor="w")
        self.label_pl_entry = tk.Entry(right, bg="#2c2c2c", fg="#ddd", bd=0,
                                       insertbackground="#ddd", font=("Segoe UI", 10))
        self.label_pl_entry.pack(fill="x", pady=(2, 8), ipady=4)

        tk.Label(right, text=tr(lang, "color_label"), bg="#202020",
                 fg="#aaa", font=("Segoe UI", 8)).pack(anchor="w")
        color_row = tk.Frame(right, bg="#202020")
        color_row.pack(fill="x", pady=(2, 8))
        self.color_btn = tk.Button(color_row, text="  ", width=4, bd=0,
                                   command=self._pick_color)
        self.color_btn.pack(side="left")
        self.color_lbl = tk.Label(color_row, text="#888888", bg="#202020",
                                  fg="#aaa", font=("Consolas", 9))
        self.color_lbl.pack(side="left", padx=8)

        tk.Label(right, text=tr(lang, "numbers_label"), bg="#202020",
                 fg="#aaa", font=("Segoe UI", 8)).pack(anchor="w")
        self.numbers_text = tk.Text(right, bg="#2c2c2c", fg="#ddd", bd=0,
                                    insertbackground="#ddd", font=("Consolas", 10),
                                    height=10, wrap="none")
        self.numbers_text.pack(fill="both", expand=True, pady=(2, 8))

        btns = tk.Frame(right, bg="#202020")
        btns.pack(fill="x")
        tk.Button(btns, text=tr(lang, "save"), command=self._save_all,
                  bg="#1b5e20", fg="#fff", bd=0, padx=16).pack(side="right", padx=4)
        tk.Button(btns, text=tr(lang, "cancel"), command=self.destroy,
                  bg="#2c2c2c", fg="#ddd", bd=0, padx=16).pack(side="right")

    def set_language(self, lang):
        self._save_current_silent()
        self.lang = lang
        self.title(f"{APP_NAME} — {tr(lang, 'lists_editor_title')}")
        self._build_ui()
        self._refresh_list()
        key = self.current_key.get()
        if key and key in self.lists:
            idx = list(self.lists.keys()).index(key)
            self.listbox.selection_set(idx)
            self._on_select()

    def apply_remote_lists(self, remote_lists):
        """Live refresh while editor is open; preserve all unsaved local edits.

        Remote is canonical for untouched groups. Edits already made in this
        editor remain a draft until Save is pressed and are never silently lost.
        """
        if not self.winfo_exists():
            return
        current_key = self.current_key.get()
        # Current visible form has not been committed to self.lists yet.
        self._save_current_silent()
        previous = self.lists
        baseline = getattr(self, "_remote_baseline", previous)
        changed_keys = {key for key in set(previous) | set(baseline)
                        if previous.get(key) != baseline.get(key)}
        merged = json.loads(json.dumps(remote_lists))
        for key in changed_keys:
            if key in previous:
                merged[key] = json.loads(json.dumps(previous[key]))
            else:
                merged.pop(key, None)
        self.lists = merged
        self._remote_baseline = json.loads(json.dumps(remote_lists))
        self.current_key.set("")
        self._refresh_list()
        if self.lists:
            key = current_key if current_key in self.lists else next(iter(self.lists))
            idx = list(self.lists).index(key)
            self.listbox.selection_set(idx)
            self._on_select()
        if changed_keys:
            self.title(f"{APP_NAME} — {tr(self.lang, 'lists_editor_title')} · незбережені зміни / niezapisane")
        debug_event("LISTS", "Editor refreshed live", level="INFO",
                    groups=len(self.lists), preserved_drafts=len(changed_keys))

    def _refresh_list(self):
        self.listbox.delete(0, tk.END)
        for key, info in self.lists.items():
            label = get_label(info, self.lang) or key
            self.listbox.insert(tk.END, f"{label}  ({key})")

    def _selected_key(self):
        sel = self.listbox.curselection()
        if not sel:
            return None
        return list(self.lists.keys())[sel[0]]

    def _on_select(self, event=None):
        key = self._selected_key()
        if not key:
            return
        self._save_current_silent()
        self.current_key.set(key)
        info = self.lists[key]
        self.key_entry.delete(0, tk.END)
        self.key_entry.insert(0, key)
        self.label_uk_entry.delete(0, tk.END)
        self.label_uk_entry.insert(0, info.get("label_uk", info.get("label", "")))
        self.label_pl_entry.delete(0, tk.END)
        self.label_pl_entry.insert(0, info.get("label_pl", info.get("label_uk", "")))
        self.color_lbl.config(text=info.get("color", "#888888"))
        self.color_btn.config(bg=info.get("color", "#888888"))
        self.numbers_text.delete("1.0", tk.END)
        self.numbers_text.insert("1.0", "\n".join(str(n) for n in info.get("numbers", [])))

    def _save_current_silent(self):
        key = self.current_key.get()
        if not key or key not in self.lists:
            return
        info = self.lists[key]
        info["label_uk"] = self.label_uk_entry.get().strip()
        info["label_pl"] = self.label_pl_entry.get().strip()
        info["color"] = self.color_lbl.cget("text")
        raw = self.numbers_text.get("1.0", tk.END)
        info["numbers"] = [ln.strip() for ln in raw.splitlines() if ln.strip()]

    def _pick_color(self):
        color = colorchooser.askcolor(color=self.color_lbl.cget("text"), parent=self)[1]
        if color:
            self.color_lbl.config(text=color)
            self.color_btn.config(bg=color)

    def _add_list(self):
        key = simpledialog.askstring(tr(self.lang, "new_list_title"),
                                     tr(self.lang, "new_list_prompt"), parent=self)
        if not key:
            return
        key = re.sub(r"\s+", "_", key.strip().lower())
        if key in self.lists:
            messagebox.showwarning(tr(self.lang, "warning"),
                                   tr(self.lang, "key_exists"), parent=self)
            return
        self.lists[key] = {"label_uk": key.upper(), "label_pl": key.upper(),
                           "color": "#4CAF50", "numbers": []}
        self._refresh_list()
        idx = list(self.lists.keys()).index(key)
        self.listbox.selection_clear(0, tk.END)
        self.listbox.selection_set(idx)
        self._on_select()

    def _delete_list(self):
        key = self._selected_key()
        if not key:
            return
        if key == "none":
            messagebox.showwarning(tr(self.lang, "warning"),
                                   tr(self.lang, "cannot_delete_none"), parent=self)
            return
        if not messagebox.askyesno(tr(self.lang, "confirm"),
                                   tr(self.lang, "confirm_delete", key=key), parent=self):
            return
        del self.lists[key]
        self.current_key.set("")
        self._refresh_list()
        if self.lists:
            self.listbox.selection_set(0)
            self._on_select()

    def _save_all(self):
        self._save_current_silent()
        self.cfg["number_lists"] = self.lists
        debug_event("LISTS", "List editor saved", level="INFO", groups=len(self.lists), item_count=sum(len(x.get("numbers",[])) for x in self.lists.values()))
        self.cfg["lists_pending"] = True
        save_setting("number_lists", self.lists)
        save_setting("lists_pending", True)
        self.on_save()
        self.destroy()


class HistoryWindow(tk.Toplevel):
    """Only the current active shift is accessible in the desktop UI."""
    def __init__(self, parent, lang, history, cloud_loader=None, number_lists=None):
        super().__init__(parent)
        self.lang, self.history = lang, history
        self.cloud_loader = cloud_loader
        self.number_lists = number_lists or {}
        self.cloud_rows = []
        self.cloud_status = ""
        self.mode = tk.StringVar(value="local")
        self._shift_identity = shift_info()
        self.title(f"{APP_NAME} — {tr(lang, 'history_title')}")
        fit_dialog(self, 1120, 710, 850, 530)
        self.transient(parent)

        bar = ttk.Frame(self)
        bar.pack(fill="x", padx=12, pady=(12, 5))
        self.heading = ttk.Label(bar, text="", style="Heading.TLabel")
        self.heading.pack(side="left", padx=(0, 18))
        self.local_btn = ttk.Radiobutton(bar, text="Локальна / Lokalna", variable=self.mode,
                                         value="local", command=self._mode_changed)
        self.local_btn.pack(side="left", padx=7)
        self.cloud_btn = ttk.Radiobutton(bar, text="Онлайн / Firebase", variable=self.mode,
                                         value="cloud", command=self._mode_changed)
        self.cloud_btn.pack(side="left", padx=7)
        self.reload_btn = ttk.Button(bar, text="↻", command=self.load_cloud)
        self.reload_btn.pack(side="right")

        filters = ttk.Frame(self)
        filters.pack(fill="x", padx=12, pady=9)
        self.search_var, self.hour_from, self.hour_to = tk.StringVar(), tk.StringVar(), tk.StringVar()
        self.type_var, self.device_var = tk.StringVar(), tk.StringVar()
        labels = (("Пошук / Szukaj", self.search_var, 17),
                  ("Від / Od HH:MM", self.hour_from, 7),
                  ("До / Do HH:MM", self.hour_to, 7))
        for text, variable, width in labels:
            item = ttk.Frame(filters)
            item.pack(side="left", padx=4)
            ttk.Label(item, text=text).pack(anchor="w", pady=(0, 3))
            ttk.Entry(item, textvariable=variable, width=width).pack()
            variable.trace_add("write", lambda *_: self._refresh())
        item = ttk.Frame(filters)
        item.pack(side="left", padx=4)
        ttk.Label(item, text="Тип / Typ").pack(anchor="w", pady=(0, 3))
        self.types = ttk.Combobox(item, textvariable=self.type_var, state="readonly", width=15)
        self.types.pack()
        self.types.bind("<<ComboboxSelected>>", lambda *_: self._refresh())
        item = ttk.Frame(filters)
        item.pack(side="left", padx=4)
        ttk.Label(item, text="Комп’ютер / PC").pack(anchor="w", pady=(0, 3))
        self.devices = ttk.Combobox(item, textvariable=self.device_var, state="readonly", width=17)
        self.devices.pack()
        self.devices.bind("<<ComboboxSelected>>", lambda *_: self._refresh())

        self.result_lbl = ttk.Label(self, text="")
        self.result_lbl.pack(fill="x", padx=15, pady=(2, 7))
        area = ttk.Frame(self)
        area.pack(fill="both", expand=True, padx=12, pady=(0, 12))
        columns = ("time", "number", "product", "type", "device")
        self.tree = ttk.Treeview(area, columns=columns, show="headings")
        for col, title, width in zip(columns, ("Дата / час", "Номер гуми", "Код продукту", "Тип гуми", "Комп’ютер"),
                                     (175, 120, 225, 165, 170)):
            self.tree.heading(col, text=title)
            self.tree.column(col, minwidth=70, width=width)
        yscroll = ttk.Scrollbar(area, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=yscroll.set)
        yscroll.pack(side="right", fill="y")
        self.tree.pack(fill="both", expand=True)
        self._refresh()
        self.after(1000, self._clock_tick)

    def set_language(self, lang):
        self.lang = lang
        self.title(f"{APP_NAME} — {tr(lang, 'history_title')}")
        self._refresh()

    def _clock_tick(self):
        if not self.winfo_exists():
            return
        # Firebase sync merges new rows into history in real time.
        # Refresh the online view even when the history window stays open.
        if self.mode.get() == "cloud":
            seen = {row.get("id") for row in self.cloud_rows}
            incoming = [row for row in current_shift_rows(self.history)
                        if row.get("id") not in seen]
            if incoming:
                self.cloud_rows.extend(incoming)
                self._refresh()
        current = shift_info()
        if current != self._shift_identity:
            self._shift_identity = current
            self.cloud_rows = []
            debug_event("SHIFT", "Current shift changed", level="INFO", active=current)
            self._refresh()
            if self.mode.get() == 'cloud':
                self.load_cloud()
        self.after(1000, self._clock_tick)

    def _mode_changed(self):
        debug_event("HISTORY", "Source changed", level="INFO", source=self.mode.get(), shift=shift_info())
        self._refresh()
        if self.mode.get() == "cloud":
            self.load_cloud()

    def load_cloud(self):
        if not self.cloud_loader:
            self.cloud_status = "Firebase недоступний"
            self._refresh()
            return
        debug_event("HISTORY", "Cloud history requested", level="INFO")
        self.cloud_status = "Завантаження / Ładowanie…"
        self._refresh()
        def worker():
            try:
                result, err = self.cloud_loader(), ""
            except Exception as exc:
                result, err = [], str(exc)
            def done():
                if not self.winfo_exists():
                    return
                if not err:
                    self.cloud_rows = result
                    debug_event("HISTORY", "Cloud history loaded", level="INFO", count=len(result))
                else:
                    debug_event("HISTORY", "Cloud history failed", level="ERROR", error=err)
                self.cloud_status = "Firebase: " + (err or "оновлено / odświeżono")
                self._refresh()
            try:
                self.after(0, done)
            except RuntimeError:
                pass
        threading.Thread(target=worker, daemon=True).start()

    def _refresh(self):
        if not self.winfo_exists():
            return
        day, shift = shift_info()
        shift_names = {1:"06:00–14:00",2:"14:00–22:00",3:"22:00–06:00"}
        self.heading.configure(text=("Поточна зміна" if self.lang == "uk" else "Bieżąca zmiana")
                               + f"  №{shift} · {day} · {shift_names[shift]}")
        # SCOPE FIRST: not even the filter options can reveal other shifts.
        rows = current_shift_rows(self.cloud_rows if self.mode.get() == "cloud" else self.history)
        kinds = sorted({str(row.get('type_key') or 'none') for row in rows})
        self.types['values'] = [''] + kinds
        if self.type_var.get() not in self.types['values']:
            self.type_var.set('')
        devices = sorted({str(row.get('device_id') or 'legacy') for row in rows})
        self.devices['values'] = [''] + devices
        if self.device_var.get() not in self.devices['values']:
            self.device_var.set('')
        query = self.search_var.get().strip().casefold()
        start, end = self.hour_from.get().strip(), self.hour_to.get().strip()
        kind, device = self.type_var.get(), self.device_var.get()
        self.tree.delete(*self.tree.get_children())
        count = 0
        for row in sorted(rows, key=lambda r: str(r.get('time','')), reverse=True):
            ts = str(row.get('time',''))
            if query and query not in (str(row.get('number','')) + ' ' + str(row.get('product',''))).casefold(): continue
            if kind and kind != str(row.get('type_key') or 'none'): continue
            if device and device != str(row.get('device_id') or 'legacy'): continue
            hour = ts[11:16]
            if start and len(start) == 5 and hour < start: continue
            if end and len(end) == 5 and hour > end: continue
            info = self.number_lists.get(row.get('type_key'), {})
            label = (row.get('type_pl') if self.lang == 'pl' else row.get('type_uk')) or \
                info.get('label_pl' if self.lang == 'pl' else 'label_uk', row.get('type_key', ''))
            self.tree.insert('', 'end', values=(ts[:19].replace('T',' '), row.get('number',''),
                                                 row.get('product',''), label, row.get('device_id','legacy')))
            count += 1
        status = f' · {self.cloud_status}' if self.mode.get() == 'cloud' else ''
        self.result_lbl.configure(text=f'{count} записів / wpisów{status}')

class WorkWindow(tk.Toplevel):
    """Separate operational list, missing-photo registry and code conflicts."""
    def __init__(self, app, tab='work'):
        super().__init__(app.root)
        self.app = app
        self.title('SFC Solutions — ' + self.t('Робочі списки', 'Listy robocze'))
        fit_dialog(self, 900, 590, 680, 480)
        self.transient(app.root)
        self.protocol('WM_DELETE_WINDOW', self.destroy)
        self._signature = None
        self._preview_key = None
        self._preview_photo = None
        self._building = False
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill='both', expand=True, padx=10, pady=10)
        self.pages = {}
        for key, title in [('work', self.t('Лист', 'Lista')), ('missing', self.t('Без фото', 'Bez zdjęć')), ('conflicts', self.t('Конфлікти кодів', 'Konflikty kodów'))]:
            page = ttk.Frame(self.notebook, padding=10)
            self.notebook.add(page, text=title)
            self.pages[key] = page
        self.build_work()
        self.build_missing()
        self.build_conflicts()
        self.notebook.bind('<<NotebookTabChanged>>', lambda e: self.refresh(force=True))
        self.select_tab(tab)
        self.refresh(force=True)
        self._tick_id = self.after(1200, self.tick)

    def destroy(self):
        if getattr(self, "_tick_id", None):
            try:
                self.after_cancel(self._tick_id)
            except tk.TclError:
                pass
            self._tick_id = None
        super().destroy()

    def t(self, uk, pl):
        return uk if self.app.lang == 'uk' else pl

    def select_tab(self, key):
        self.notebook.select(self.pages.get(key, self.pages['work']))

    def tree(self, parent, columns, headings, widths, mode='browse'):
        area = ttk.Frame(parent)
        area.pack(fill='both', expand=True)
        tree = ttk.Treeview(area, columns=columns, show='headings', selectmode=mode)
        for col, heading, width in zip(columns, headings, widths):
            tree.heading(col, text=heading)
            tree.column(col, width=width, minwidth=60, stretch=True)
        scroll = ttk.Scrollbar(area, orient='vertical', command=tree.yview)
        tree.configure(yscrollcommand=scroll.set)
        scroll.pack(side='right', fill='y')
        tree.pack(side='left', fill='both', expand=True)
        light = self.app.cfg.get('theme') == 'light'
        tree.tag_configure('done', foreground='#16723c' if light else '#75d99a')
        tree.tag_configure('pending', foreground='#657181' if light else '#aab2bf')
        tree.tag_configure('missing', foreground='#a74117' if light else '#ffac75')
        return tree

    def build_work(self):
        page = self.pages['work']
        self.work_summary = ttk.Label(page, style='Heading.TLabel')
        self.work_summary.pack(anchor='w', pady=(0,8))
        row = ttk.Frame(page)
        row.pack(fill='x', pady=(0,8))
        ttk.Button(row, text=self.t('+ Додати номери', '+ Dodaj numery'), command=self.add_numbers).pack(side='left')
        ttk.Button(row, text=self.t('Видалити вибрані', 'Usuń wybrane'), command=self.remove_numbers).pack(side='left', padx=5)
        ttk.Button(row, text=self.t('Очистити лист', 'Wyczyść listę'), command=self.clear_numbers).pack(side='left')
        self.pending_only = tk.BooleanVar(value=False)
        ttk.Checkbutton(row, text=self.t('Лише невиконані', 'Tylko niewykonane'), variable=self.pending_only, command=lambda: self.refresh(force=True)).pack(side='right')
        body = ttk.Frame(page)
        body.pack(fill='both', expand=True)
        left = ttk.Frame(body)
        left.pack(side='left', fill='both', expand=True)
        self.work_tree = self.tree(left, ('number','type','status'), (self.t('Номер','Numer'), self.t('Тип','Typ'), self.t('Статус','Status')), (95,145,140), 'extended')
        self.work_tree.bind('<<TreeviewSelect>>', self.preview)
        right = ttk.Frame(body, width=310)
        right.pack(side='right', fill='y', padx=(12,0))
        right.pack_propagate(False)
        self.preview_title = ttk.Label(right, text=self.t('Прев’ю','Podgląd'), style='Heading.TLabel')
        self.preview_title.pack(pady=8)
        self.preview_label = ttk.Label(right, text=self.t('Вибери номер','Wybierz numer'), anchor='center', wraplength=290)
        self.preview_label.pack(fill='both', expand=True)
        self.preview_codes = ttk.Label(right, text='', wraplength=290, justify='center')
        self.preview_codes.pack(fill='x', pady=6)
        nav = ttk.Frame(right)
        nav.pack(pady=6)
        ttk.Button(nav, text='←', command=lambda: self.navigate(-1)).pack(side='left', padx=4)
        ttk.Button(nav, text='→', command=lambda: self.navigate(1)).pack(side='left', padx=4)
        ttk.Label(page, text=self.t('Зелений — є запис у поточній зміні. Сірий — очікує друку.', 'Zielony — zapis w bieżącej zmianie. Szary — oczekuje wydruku.')).pack(anchor='w', pady=(8,0))

    def add_numbers(self):
        win = tk.Toplevel(self)
        win.title(self.t('Додати номери', 'Dodaj numery'))
        win.transient(self)
        win.grab_set()
        fit_dialog(win, 460, 340, 360, 260)
        ttk.Label(win, text=self.t('Встав номери: рядки, пробіли, коми або крапки з комою.', 'Wklej numery: wiersze, spacje, przecinki lub średniki.'), wraplength=420).pack(padx=12,pady=10)
        field = tk.Text(win, height=8, wrap='word')
        field.pack(fill='both', expand=True, padx=12)
        def save():
            numbers, invalid = parse_work_numbers(field.get('1.0','end'))
            if invalid:
                messagebox.showwarning(APP_NAME, self.t('Неправильні номери: ', 'Nieprawidłowe numery: ') + ', '.join(invalid), parent=win)
                return
            self.app.set_work_numbers(list(dict.fromkeys(self.app.work_numbers + numbers)))
            win.destroy()
            self.refresh(force=True)
        ttk.Button(win, text=self.t('Додати','Dodaj'), command=save).pack(pady=10)
        self.app._apply_dialog_theme(win)
        field.focus_set()

    def remove_numbers(self):
        remove = set(self.work_tree.selection())
        if remove:
            self.app.set_work_numbers([n for n in self.app.work_numbers if n not in remove])
            self.refresh(force=True)

    def clear_numbers(self):
        if self.app.work_numbers and messagebox.askyesno(APP_NAME, self.t('Очистити робочий лист? Історія залишиться.', 'Wyczyścić listę roboczą? Historia pozostanie.'), parent=self):
            self.app.set_work_numbers([])
            self.refresh(force=True)

    def navigate(self, delta):
        items = self.work_tree.get_children()
        if not items:
            return
        current = self.work_tree.focus()
        idx = items.index(current) if current in items else (-1 if delta > 0 else len(items))
        n = items[max(0,min(len(items)-1, idx+delta))]
        self.work_tree.selection_set(n)
        self.work_tree.focus(n)
        self.work_tree.see(n)
        self.preview()

    def preview(self, event=None):
        selected = self.work_tree.selection()
        n = self.work_tree.focus()
        if n not in selected:
            n = selected[0] if selected else ''
        if not n:
            self._preview_key = None
            self._preview_photo = None
            self.preview_label.configure(image='', text=self.t('Вибери номер','Wybierz numer'))
            self.preview_title.configure(text=self.t('Прев’ю','Podgląd'))
            self.preview_codes.configure(text='')
            return
        self.preview_title.configure(text=n + ' · ' + (self.app.classify_number(n)[0] or tr(self.app.lang, 'type_none')))
        self.preview_codes.configure(text='\n'.join(self.app.codes_for(n)))
        fn = self.app.photo_for(n)
        path = os.path.join(self.app.images_dir, fn) if fn else ''
        try:
            key = (path, os.stat(path).st_mtime_ns) if path else ('',n)
        except OSError:
            key = ('',n)
            path = ''
        if key == self._preview_key:
            return
        self._preview_key = key
        self._preview_photo = None
        if path:
            try:
                with Image.open(path) as src:
                    im = ImageOps.exif_transpose(src).convert('RGB')
                    im.thumbnail((300,245), Image.Resampling.LANCZOS)
                self._preview_photo = ImageTk.PhotoImage(im, master=self)
                self.preview_label.configure(image=self._preview_photo, text='')
                return
            except Exception as exc:
                debug_event('IMAGE','Preview failed', level='ERROR', error=repr(exc))
        self.preview_label.configure(image='', text=self.t('Немає фото','Brak zdjęcia'))

    def build_missing(self):
        page = self.pages['missing']
        self.missing_summary = ttk.Label(page, style='Heading.TLabel')
        self.missing_summary.pack(anchor='w', pady=(0,8))
        row = ttk.Frame(page)
        row.pack(fill='x', pady=(0,8))
        self.missing_search = tk.StringVar()
        ttk.Entry(row, textvariable=self.missing_search).pack(side='left', fill='x', expand=True)
        self.missing_search.trace_add('write', lambda *_: self.refresh(force=True))
        self.show_resolved = tk.BooleanVar(value=False)
        ttk.Checkbutton(row,text=self.t('Також з доданим фото','Także z dodanym zdjęciem'),variable=self.show_resolved,command=lambda: self.refresh(force=True)).pack(side='left',padx=8)
        ttk.Button(row,text='↻',command=lambda: self.refresh(force=True)).pack(side='right')
        self.missing_tree = self.tree(page, ('number','product','status'), (self.t('Номер гуми','Numer gumy'),self.t('Код продукту','Kod produktu'),self.t('Фото','Zdjęcie')), (120,270,170))
        ttk.Label(page,text=self.t('Усі відомі пари з історії без фото; повтори об’єднано.', 'Wszystkie znane pary z historii bez zdjęcia; bez powtórzeń.')).pack(anchor='w',pady=(8,0))

    def build_conflicts(self):
        page = self.pages['conflicts']
        self.conflict_summary = ttk.Label(page, style='Heading.TLabel')
        self.conflict_summary.pack(anchor='w', pady=(0,8))
        body = ttk.Frame(page)
        body.pack(fill='both', expand=True)
        left, right = ttk.Frame(body), ttk.Frame(body)
        left.pack(side='left', fill='both', expand=True, padx=(0,10))
        right.pack(side='left', fill='both', expand=True)
        self.conflict_tree = self.tree(left, ('number','count','main'), (self.t('Гума','Guma'),self.t('Кодів','Kodów'),self.t('Основний код','Kod główny')), (85,60,165))
        self.conflict_tree.bind('<<TreeviewSelect>>', self.show_codes)
        self.codes_tree = self.tree(right, ('raw','code','status'), (self.t('З історії','Z historii'),self.t('Актуальний','Aktualny'),self.t('Статус','Status')), (125,125,100))
        self.codes_tree.bind('<Double-1>', lambda e: self.edit_code())
        row = ttk.Frame(page)
        row.pack(fill='x',pady=8)
        ttk.Button(row,text=self.t('Підтвердити основний','Potwierdź główny'),command=self.confirm_code).pack(side='left')
        ttk.Button(row,text=self.t('Редагувати код','Edytuj kod'),command=self.edit_code).pack(side='left',padx=5)
        ttk.Button(row,text=self.t('Авто: найновіший','Auto: najnowszy'),command=self.auto_code).pack(side='left')
        ttk.Label(page,text=self.t('Початково основний код — найновіший. Виправлення не змінюють історію друку.', 'Domyślnie główny kod jest najnowszy. Korekty nie zmieniają historii wydruku.'),wraplength=820).pack(anchor='w')

    def selected_number(self):
        selection = self.conflict_tree.selection()
        return selection[0] if selection else ''

    def show_codes(self, event=None):
        num = self.selected_number()
        raw = self.app.raw_codes.get(num, [])
        rule = self.app.code_overrides.get(num, {})
        corrections = rule.get('corrections', {})
        effective = self.app.codes_for(num)
        main = effective[0] if effective else ''
        rows = []
        for code in raw:
            actual = corrections.get(code, code)
            status = self.t('Основний','Główny') if actual == main else self.t('Додатковий','Dodatkowy')
            rows.append((code,(code,actual,status),'done' if actual == main else 'pending'))
        self.fill(self.codes_tree, rows)

    def select_conflict(self, num):
        self.select_tab('conflicts')
        self.refresh(force=True)
        if self.conflict_tree.exists(num):
            self.conflict_tree.selection_set(num)
            self.conflict_tree.focus(num)
            self.conflict_tree.see(num)
            self.show_codes()

    def edit_code(self):
        num = self.selected_number()
        selected = self.codes_tree.selection()
        if not num or not selected:
            return
        raw = selected[0]
        rule = self.app.code_overrides.get(num, {})
        old = rule.get('corrections', {}).get(raw, raw)
        value = simpledialog.askstring(APP_NAME,self.t('Новий код продукту (від 8 цифр):','Nowy kod produktu (co najmniej 8 cyfr):'),initialvalue=old,parent=self)
        if value is None:
            return
        value = value.strip()
        if not re.fullmatch(r'[0-9]{8,}',value):
            messagebox.showwarning(APP_NAME,self.t('Код має містити щонайменше 8 цифр.','Kod musi mieć co najmniej 8 cyfr.'),parent=self)
            return
        other = self.app.product_index.get(value)
        if other and other != num:
            messagebox.showwarning(APP_NAME, self.t('Цей код уже пов’язано з іншим номером: ', 'Ten kod jest już przypisany do innego numeru: ') + other, parent=self)
            return
        self.app.set_code_correction(num, raw, value)
        self.refresh(force=True)
        self.show_codes()

    def confirm_code(self):
        num = self.selected_number()
        selected = self.codes_tree.selection()
        if num and selected:
            raw = selected[0]
            self.app.set_preferred_code(num,self.app.code_overrides.get(num,{}).get('corrections',{}).get(raw,raw))
            self.refresh(force=True)
            self.show_codes()

    def auto_code(self):
        num = self.selected_number()
        if num:
            self.app.set_preferred_code(num,None)
            self.refresh(force=True)
            self.show_codes()

    @staticmethod
    def fill(tree, rows):
        selected = tree.selection()
        focused = tree.focus()
        old = tree.get_children()
        if old:
            tree.delete(*old)
        for iid, values, tag in rows:
            tree.insert('', 'end', iid=iid, values=values, tags=(tag,) if tag else ())
        keep = [i for i in selected if tree.exists(i)]
        if keep:
            tree.selection_set(*keep)
        elif rows:
            tree.selection_set(rows[0][0])
        if tree.exists(focused):
            tree.focus(focused)
        elif tree.selection():
            tree.focus(tree.selection()[0])

    def tick(self):
        if self.winfo_exists():
            self.refresh()
            self._tick_id = self.after(1200,self.tick)

    def refresh(self, force=False):
        if self._building:
            return
        app = self.app
        tab = self.notebook.select()
        sig = (tab, app.history_revision, shift_info(), tuple(app.work_numbers), app.code_revision, app.images_dir, app._image_catalog.revision, id(app.cfg.get('number_lists')), app.lang, app.cfg.get('theme'))
        if not force and sig == self._signature:
            return
        self._signature = sig
        light = app.cfg.get('theme') == 'light'
        for tree in (self.work_tree, self.missing_tree, self.conflict_tree, self.codes_tree):
            tree.tag_configure('done', foreground='#16723c' if light else '#75d99a')
            tree.tag_configure('pending', foreground='#657181' if light else '#aab2bf')
            tree.tag_configure('missing', foreground='#a74117' if light else '#ffac75')
        self._building = True
        try:
            if tab == str(self.pages['work']):
                done = app.completed_work_numbers()
                count = sum(n in done for n in app.work_numbers)
                day, shift = shift_info()
                self.work_summary.configure(text=self.t('Виконано','Wykonano')+f' {count}/{len(app.work_numbers)}  ·  '+self.t('Зміна','Zmiana')+f' {shift} · {day}')
                rows = []
                for n in app.work_numbers:
                    finished = n in done
                    if finished and self.pending_only.get():
                        continue
                    rows.append((n,(n,app.classify_number(n)[0] or tr(app.lang,'type_none'),self.t('✓ Виконано','✓ Wykonano') if finished else self.t('Очікує','Oczekuje')),'done' if finished else 'pending'))
                self.fill(self.work_tree,rows)
                self.preview()
            elif tab == str(self.pages['missing']):
                rows = []
                query = self.missing_search.get().strip().casefold()
                ready = os.path.isdir(app.images_dir) and app._image_catalog._ready.is_set()
                if not ready:
                    self.missing_summary.configure(text=self.t('Перевіряємо папку фото / папка недоступна','Sprawdzanie folderu / folder niedostępny'))
                    self.fill(self.missing_tree, [])
                    return
                missing = 0
                names = app._image_catalog.snapshot_names()
                observed_missing = {(str(r.get('number') or ''), str(r.get('product') or '')) for r in app.history if r.get('photo_missing') is True}
                currently_missing = set()
                for n, p in app.missing_pairs():
                    has_photo = n.casefold() in names
                    if not has_photo:
                        missing += 1
                        currently_missing.add((n,p))
                    if has_photo and (not self.show_resolved.get() or (n,p) not in app._known_missing_pairs | observed_missing):
                        continue
                    if query and query not in (n+' '+p).casefold():
                        continue
                    rows.append((n+'|'+p,(n,p,self.t('Є фото','Jest zdjęcie') if has_photo else self.t('Немає фото','Brak zdjęcia')),'done' if has_photo else 'missing'))
                app.remember_missing(currently_missing | observed_missing)
                self.missing_summary.configure(text=self.t('Пар без фото: ','Pary bez zdjęcia: ')+str(missing))
                self.fill(self.missing_tree,rows)
            else:
                rows=[]
                for n, raw in sorted(app.raw_codes.items()):
                    if len(raw)>1:
                        codes=app.codes_for(n)
                        rows.append((n,(n,len(raw),codes[0] if codes else ''),'pending'))
                self.conflict_summary.configure(text=self.t('Номерів із різними кодами: ','Numerów z różnymi kodami: ')+str(len(rows)))
                self.fill(self.conflict_tree,rows)
                self.show_codes()
        finally:
            self._building = False


class App:
    TITLE_H = 22
    TEXT_H = 20
    MIN_W, MIN_H = 400, 300
    DEFAULT_W, DEFAULT_H = 450, 370

    def __init__(self, cfg):
        self.cfg = cfg
        self.lang = cfg.get("ui_language", "uk")
        # Upgrade tiny interface font left by older default configurations.
        # The SFC Solutions heading itself stays unchanged.
        if int(cfg.get("font_sizes", {}).get("interface", 10) or 10) <= 8:
            cfg.setdefault("font_sizes", {})["interface"] = 10
            save_setting("font_sizes", cfg["font_sizes"])
        self.q = queue.Queue()
        self.stop_evt = threading.Event()
        # 48 decoded display objects maximum, not every photo in the folder.
        self.img_cache = OrderedDict()
        self._image_cache_limit = 48
        self.current_file = object()
        self._image_request_id = 0
        self._image_jobs = queue.Queue(maxsize=2)
        self._image_catalog = None
        self._fit_area_signature = None
        self._fit_area_busy = False
        self._last_overlay_draw = None
        self.collapsed = False
        self.region = dict(cfg["region"])
        self.click_region = cfg.get("click_region")
        # Each selected screen area follows its own target window.
        # Never reuse HWNDs from a previous Windows session.
        self.anchors = {}
        self._anchor_last = {}
        if cfg.get("window_anchor"):
            print("Застарілу прив'язку вікна скинуто. Виберіть області ще раз (лише один раз).")
        self.reset_hash = False
        self.last_result = ("", None, "", "")
        self._ocr_generation = 0           # capture worker owns this counter
        self._ocr_verified_generation = -1 # Tk owns verified state
        self._ocr_verified_product = ""
        self._ocr_preview_generation = -1
        self._ocr_preview_text = ""
        self._ocr_deferred_click = None
        self._ocr_unverified_rubber = False
        self._display_number = ""
        self.last_valid_number = ""
        self.current_product = ""
        self._number_seen_at = 0.0
        self._product_seen_at = 0.0
        self._ocr_stage = "idle"  # rubber -> product -> saved
        self._last_saved_pair = None
        self._last_saved_monotonic = 0.0
        self._ocr_last_logged = None
        self.history = load_history()
        self.history_revision = 0
        self.code_revision = 0
        self._completed_cache = (None, set())
        numbers = cfg.get('work_numbers', [])
        self.work_numbers = list(dict.fromkeys(str(n) for n in numbers if is_valid_number(n))) if isinstance(numbers, list) else []
        overrides = cfg.get('code_overrides', {})
        self.code_overrides = overrides if isinstance(overrides, dict) else {}
        self._known_missing_pairs = {tuple(map(str, pair)) for pair in cfg.get('missing_photo_pairs', []) if isinstance(pair,(list,tuple)) and len(pair)==2}
        self.work_win = None
        self.device_id = cfg.get("device_id") or str(uuid.uuid4())
        self.cfg["device_id"] = self.device_id
        save_setting("device_id", self.device_id)
        self._last_sound_number = None
        self._last_sound_time = 0
        self._sound_missing_since = None
        # Audio is handled by one worker, not by a thread for each OCR frame.
        self._sound_events = queue.Queue(maxsize=8)
        threading.Thread(target=self._sound_worker, daemon=True,
                         name="SFCAudio").start()
        self.editor = None
        self.history_win = None
        self.mouse_listener = None

        self.refresh_code_indexes()

        self.images_dir = resolve_images_dir(cfg)
        self._image_catalog = ImageCatalog(self.images_dir, self.stop_evt)
        threading.Thread(target=self._image_decode_worker, name="SFCImageDecode",
                         daemon=True).start()
        debug_event("APP", "Initialization", level="INFO", device=self.device_id, local_history=len(self.history), image_directory_exists=os.path.isdir(self.images_dir), ocr_region=self.region, click_region=self.click_region)
        self.firebase_ready = init_firebase()
        self._remote_lists_hash = None
        self._remote_lists_seen = False
        self._sync_status = "offline"
        self._sync_wakeup = threading.Event()
        self._live_listeners = []
        if self.firebase_ready and self.cfg.get("sync_enabled", True):
            threading.Thread(target=self._sync_loop, daemon=True, name="SFCSync").start()
            threading.Thread(target=self._start_live_listeners, daemon=True,
                             name="SFCLiveFirebase").start()

        w = cfg["window"]
        # Upgrade old config.json sizes without overwriting a user's larger size.
        # Small values came from previous versions (220x180) and hide menu controls.
        self.W = max(self.MIN_W, self.DEFAULT_W, int(w.get("width", self.DEFAULT_W)))
        self.H = max(self.MIN_H, self.DEFAULT_H, int(w.get("height", self.DEFAULT_H)))
        if (self.W, self.H) != (w.get("width"), w.get("height")):
            self.cfg["window"].update({"width": self.W, "height": self.H})
            save_setting("window", {"width": self.W, "height": self.H})
            debug_event("UI", "Upgraded legacy small window size", level="INFO", width=self.W, height=self.H)
        self.root = tk.Tk()
        _install_tk_exception_logger(self.root)
        self.root.title(tr(self.lang, "window_title"))
        self.root.overrideredirect(True)
        self.root.attributes("-topmost", True)
        self.root.configure(bg="#202020")

        bar = tk.Frame(self.root, bg="#303030", height=self.TITLE_H)
        bar.pack(fill="x", side="top")
        bar.pack_propagate(False)

        self.grip = tk.Label(bar, text="◤", fg="#aaa", bg="#404040", cursor="size_nw_se",
                             font=("Segoe UI", 9), width=3)
        self.grip.pack(side="left", fill="y")
        self.grip.bind("<ButtonPress-1>", self._resize_start)
        self.grip.bind("<B1-Motion>", self._resize_move)
        self.grip.bind("<ButtonRelease-1>", self._resize_end)

        self.title_lbl = tk.Label(bar, text="",
                                  fg="#ddd", bg="#303030", font=("Segoe UI", 8))
        self.title_lbl.pack(side="left", padx=6)

        self.btn_close = tk.Button(bar, text="✕", command=self.quit, bd=0, fg="#ddd",
                                   bg="#303030", activebackground="#a33", width=3)
        self.btn_close.pack(side="right")

        self.btn_min = tk.Button(bar, text="—", command=self.toggle_collapse, bd=0,
                                 fg="#ddd", bg="#303030", activebackground="#555", width=3)
        self.btn_min.pack(side="right")

        self.btn_lang = tk.Button(bar, text=tr(self.lang, "lang_button"),
                                  command=self.toggle_language, bd=0,
                                  fg="#ddd", bg="#303030", activebackground="#555", width=3)
        self.btn_lang.pack(side="right")

        self.btn_menu = tk.Button(bar, text=tr(self.lang, "menu_button"),
                                  command=self.open_menu, bd=0,
                                  fg="#ddd", bg="#303030", activebackground="#555")
        self.btn_menu.pack(side="right", padx=(0, 4))

        self.content = tk.Frame(self.root, bg="#202020")
        self.content.pack(fill="both", expand=True)

        self.badge_lbl = tk.Label(self.content, bg="#101010", fg="#888", text="",
                                  font=("Segoe UI", 14, "bold"), anchor="center", height=2)
        self.badge_lbl.pack(side="bottom", fill="x")

        self.number_strip = tk.Frame(self.content, bg="#101010")
        self.number_strip.pack(side="bottom", fill="x")
        self.work_btn = tk.Button(self.number_strip, text="Лист", bd=0, padx=8,
                                  command=lambda: self.open_workspace('work'), bg="#303030", fg="#ddd")
        self.work_btn.pack(side="right", fill="y")
        self.conflict_btn = tk.Button(self.number_strip, bd=0, padx=6,
            command=lambda: self.open_workspace('conflicts', self._display_number), bg="#303030", fg="#ddd")
        self.text_lbl = tk.Label(self.number_strip, bg="#0a0a0a", fg="#555", text="—",
                                 font=("Consolas", 8), wraplength=0,
                                 justify="left", anchor="w", height=1)
        self.text_lbl.pack(side="left", fill="both", expand=True)

        self.body = tk.Label(self.content, bg="#202020", fg="#888", text="…",
                             font=("Segoe UI", 9))
        self.body.pack(fill="both", expand=True)

        for wdg in (bar, self.title_lbl):
            wdg.bind("<ButtonPress-1>", self._drag_start)
            wdg.bind("<B1-Motion>", self._drag_move)

        self.place_bottom_right()
        self._update_title()
        self.show_placeholder()

        self.worker = threading.Thread(target=self.loop, daemon=True)
        self.worker.start()
        self.root.after(100, self.poll)
        self.root.protocol("WM_DELETE_WINDOW", self.quit)

        self._setup_mouse_listener()
        debug_event("APP", "UI ready", level="INFO", firebase=self.firebase_ready, click_listener=bool(self.mouse_listener))
        self.root.after(500, self._track_anchor)
        self._opaque_overlay = None
        self._opaque_canvas = None
        self._overlay_sig = None
        self._last_overlay_draw = None
        self.apply_theme()
        self.apply_font_sizes()
        self.root.after(80, self._refresh_opaque_overlay)
        self.root.after(1000, self._workspace_tick)
        self._update_work_indicator()

    def refresh_code_indexes(self):
        self.raw_codes = ordered_product_codes(self.history)
        product_index = build_product_index(sorted(self.history, key=lambda r: str(r.get('time') or '')))
        # Prefer actual observed history if a manually corrected code overlaps
        # an existing code for another rubber number; never silently steal it.
        number_index = {}
        for num, raw in self.raw_codes.items():
            codes = self.codes_for(num)
            if codes:
                number_index[num] = codes[0]
            for code in codes:
                product_index.setdefault(code, num)
        self.number_index = number_index
        self.product_index = product_index

    def codes_for(self, num):
        return effective_codes(num, self.raw_codes.get(num, []), self.code_overrides)

    def set_code_correction(self, num, raw, value):
        rule = self.code_overrides.setdefault(num, {})
        corrections = rule.setdefault('corrections', {})
        old = corrections.get(raw, raw)
        if value == raw:
            corrections.pop(raw, None)
        else:
            corrections[raw] = value
        if rule.get('preferred') == old:
            rule['preferred'] = value
        self._save_code_overrides()

    def set_preferred_code(self, num, value):
        rule = self.code_overrides.setdefault(num, {})
        if value is None:
            rule.pop('preferred', None)
        elif value in self.codes_for(num):
            rule['preferred'] = value
        self._save_code_overrides()

    def _save_code_overrides(self):
        self.cfg['code_overrides'] = self.code_overrides
        save_setting('code_overrides', self.code_overrides)
        self.code_revision += 1
        self.refresh_code_indexes()
        self.redraw_result()

    def completed_work_numbers(self):
        key = (self.history_revision, shift_info())
        if self._completed_cache[0] != key:
            done = {str(r.get('number','')) for r in current_shift_rows(self.history) if str(r.get('product') or '').strip()}
            self._completed_cache = (key, done)
        return self._completed_cache[1]

    def set_work_numbers(self, numbers):
        self.work_numbers = list(dict.fromkeys(n for n in numbers if is_valid_number(n)))
        self.cfg['work_numbers'] = self.work_numbers
        save_setting('work_numbers', self.work_numbers)
        self._update_work_indicator()

    def photo_for(self, num):
        fn = self._image_catalog.lookup_number(num)
        return fn if fn and os.path.isfile(os.path.join(self.images_dir, fn)) else None

    def missing_pairs(self):
        return sorted({(str(r.get('number') or '').strip(), str(r.get('product') or '').strip()) for r in self.history if is_valid_number(r.get('number','')) and str(r.get('product') or '').strip()})

    def remember_missing(self, pairs):
        if not pairs.issubset(self._known_missing_pairs):
            self._known_missing_pairs.update(pairs)
            data = [list(pair) for pair in sorted(self._known_missing_pairs)]
            self.cfg['missing_photo_pairs'] = data
            try:
                save_setting('missing_photo_pairs', data)
            except OSError as exc:
                debug_event('HISTORY', 'Missing photo registry write failed', level='ERROR', error=repr(exc))

    def _update_work_indicator(self):
        num = self._display_number
        light = self.cfg.get('theme') == 'light'
        base = '#dfe5ee' if light else '#303030'
        fg = '#202938' if light else '#dddddd'
        title = 'ЛИСТ' if self.lang == 'uk' else 'LISTA'
        if num in self.work_numbers:
            done = num in self.completed_work_numbers()
            self.work_btn.configure(text=title + (' ✓' if done else ' •'), bg='#16723c' if done else '#626b78', fg='#ffffff', activebackground='#16723c' if done else '#626b78', activeforeground='#ffffff')
        else:
            self.work_btn.configure(text=title.capitalize(), bg=base, fg=fg, activebackground=base, activeforeground=fg)
        raw = self.raw_codes.get(num, [])
        if len(raw) > 1:
            self.conflict_btn.configure(text=('Коди' if self.lang == 'uk' else 'Kody') + ': '+str(len(raw)), bg='#9a4c12', fg='#ffffff', activeforeground='#ffffff', activebackground='#9a4c12')
            if not self.conflict_btn.winfo_manager():
                self.conflict_btn.pack(side='right', fill='y', before=self.text_lbl)
        elif self.conflict_btn.winfo_manager():
            self.conflict_btn.pack_forget()

    def _workspace_tick(self):
        if self.stop_evt.is_set():
            return
        self._update_work_indicator()
        # The catalog can discover a newly added image even while OCR is static.
        if self._display_number:
            actual = self.photo_for(self._display_number)
            if actual != self.current_file:
                self.redraw_result()
        self.root.after(1000, self._workspace_tick)

    def open_workspace(self, tab='work', number=''):
        if self.work_win is None or not self.work_win.winfo_exists():
            self.work_win = WorkWindow(self, tab)
            self._apply_dialog_theme(self.work_win)
        else:
            self.work_win.select_tab(tab)
            self.work_win.lift()
            self.work_win.refresh(force=True)
        if tab == 'conflicts' and number:
            self.work_win.select_conflict(number)

    def redraw_result(self):
        text = self.last_result[0]
        filename, match_type, token, number = self.find_image_by_history(text)
        self.show_result(text, filename, '', number, process_ocr=False)

    @staticmethod
    def _norm(s):
        return " ".join(str(s).lower().split())

    def _update_title(self):
        extra = ""
        if self.click_region:
            extra = f" · 🎯 {self.click_region['width']}×{self.click_region['height']}"
        fb = " ☁" if self.firebase_ready else ""
        self.title_lbl.config(
            text=f"{tr(self.lang, 'title_ocr')} {self.region['width']}×{self.region['height']}{extra}{fb} · "
                 f"{os.path.basename(self.images_dir) or self.images_dir}"
        )

    def open_menu(self):
        debug_event("UI", "Menu opened")
        menu = tk.Menu(self.root, tearoff=0,
                       bg="#f0f2f6" if self.cfg.get("theme") == "light" else "#2c2c2c",
                       fg="#202938" if self.cfg.get("theme") == "light" else "#ddd",
                       activebackground="#1565c0", activeforeground="#fff",
                       bd=0, font=("Segoe UI", 9))

        menu.add_command(label=tr(self.lang, "menu_images_dir"),
                         command=self.choose_images_dir)
        menu.add_command(label=tr(self.lang, "menu_select_region"),
                         command=self.choose_region)
        menu.add_command(label=tr(self.lang, "menu_click_area"),
                         command=self.choose_click_region)
        menu.add_separator()
        menu.add_command(label=tr(self.lang, "menu_history"),
                         command=self.open_history)
        menu.add_command(label=tr(self.lang, "menu_lists"),
                         command=self.open_lists_editor)
        menu.add_separator()
        menu.add_command(label="Лист" if self.lang == "uk" else "Lista robocza", command=lambda: self.open_workspace('work'))
        menu.add_command(label="Історія без фото" if self.lang == "uk" else "Historia bez zdjęć", command=lambda: self.open_workspace('missing'))
        menu.add_command(label="Конфлікти кодів" if self.lang == "uk" else "Konflikty kodów", command=lambda: self.open_workspace('conflicts'))
        menu.add_separator()
        menu.add_command(label="Налаштування / Ustawienia", command=self.open_settings)
        menu.add_command(label="Документація / Instrukcja", command=self.open_docs)
        menu.add_separator()
        menu.add_command(label="Консоль (пароль) / Konsola (hasło)",
                         command=lambda: _open_console_log(self.root, self.lang))

        x = self.btn_menu.winfo_rootx()
        y = self.btn_menu.winfo_rooty() + self.btn_menu.winfo_height()
        try:
            menu.tk_popup(x, y)
        finally:
            menu.grab_release()

    def toggle_language(self):
        self.lang = "pl" if self.lang == "uk" else "uk"
        self.cfg["ui_language"] = self.lang
        save_setting("ui_language", self.lang)
        self.btn_lang.config(text=tr(self.lang, "lang_button"))
        self.btn_menu.config(text=tr(self.lang, "menu_button"))
        self._update_title()
        self.redraw_result()
        if self.editor is not None and self.editor.winfo_exists():
            self.editor.set_language(self.lang)
        if self.history_win is not None and self.history_win.winfo_exists():
            self.history_win.set_language(self.lang)
        if self.work_win is not None and self.work_win.winfo_exists():
            selected = self.work_win.notebook.select()
            tab = next((k for k,v in self.work_win.pages.items() if str(v)==selected), 'work')
            self.work_win.destroy()
            self.work_win = None
            self.open_workspace(tab)

    def place_bottom_right(self):
        l, t, r, b = work_area()
        w = self.cfg["window"]
        h = self.TITLE_H if self.collapsed else self.H
        x = r - self.W - w["margin_right"]
        y = b - h - w["margin_bottom"]
        self.root.geometry(f"{self.W}x{h}+{x}+{y}")

    def choose_images_dir(self):
        initial = self.images_dir if os.path.isdir(self.images_dir) else BASE_DIR
        chosen = filedialog.askdirectory(parent=self.root,
                                         title=tr(self.lang, "select_images_dir"),
                                         initialdir=initial, mustexist=True)
        if not chosen:
            return
        chosen = os.path.normpath(chosen)
        self.images_dir = chosen
        debug_event("IMAGES", "Images directory selected", level="INFO", exists=os.path.isdir(chosen))
        save_setting("images_dir", chosen)
        self.img_cache.clear()
        self._image_request_id += 1
        self.current_file = object()
        self._image_catalog.change_directory(chosen)
        self._update_title()
        self.redraw_result()

    def choose_region(self):
        self.root.withdraw()

        def done(region):
            if region:
                self.region = region
                debug_event("OCR", "Capture region selected", level="INFO", bounds=region)
                self._set_anchor_for_region(region, "region")
                self.reset_hash = True
                save_region(region)
                self._update_title()
            self.root.deiconify()
            self.root.attributes("-topmost", True)

        self.root.after(150, lambda: pick_region(self.root, self.lang, "select_region_hint", done))

    def choose_click_region(self):
        self.root.withdraw()

        def done(region):
            if region:
                self.click_region = region
                debug_event("CLICK", "Click region selected", level="INFO", bounds=region)
                self._set_anchor_for_region(region, "click_region")
                save_click_region(region)
                self._update_title()
                self._setup_mouse_listener()
                print(f"Область натискання активна: {region}")
            self.root.deiconify()
            self.root.attributes("-topmost", True)

        self.root.after(150, lambda: pick_region(self.root, self.lang, "click_area_hint", done))

    def _setup_mouse_listener(self):
        if not HAS_PYNPUT:
            debug_event("CLICK", "Listener unavailable", level="ERROR", reason="pynput import failed")
            print(tr(self.lang, "pynput_missing"))
            messagebox.showwarning("SFC Solutions", tr(self.lang, "pynput_missing"), parent=self.root)
            return
        if self.mouse_listener is not None:
            try:
                self.mouse_listener.stop()
            except Exception:
                pass
            self.mouse_listener = None
        if not self.click_region:
            return

        def on_click(x, y, button, pressed):
            if not pressed:
                return
            r = self.click_region
            if r["left"] <= x <= r["left"] + r["width"] and \
               r["top"] <= y <= r["top"] + r["height"]:
                debug_event("CLICK", "Click inside monitored region", level="INFO", position=(int(x),int(y)), stage=self._ocr_stage, has_number=bool(self.last_valid_number), has_product=bool(self.current_product))
                # Capture generation is snapshotted at click time. A pending
                # preview can never directly write history or trigger Firebase.
                self.q.put(("OCR_CLICK", self._ocr_generation))

        self.mouse_listener = pynput_mouse.Listener(on_click=on_click)
        self.mouse_listener.daemon = True
        self.mouse_listener.start()
        debug_event("CLICK", "Mouse listener started", level="INFO", bounds=self.click_region)

    def _send_and_notify(self, record):
        ok, err = send_to_firebase(record)
        if ok:
            print(tr(self.lang, "firebase_sent", num=record.get("number", "")))
        else:
            print(tr(self.lang, "firebase_error", err=err))

    def _commit_record(self, num, product):
        if not num or not is_valid_number(num):
            debug_event("SAVE", "Invalid rubber number", level="INFO")
            return
        if not (product or "").strip():
            debug_event("SAVE", "Record skipped, missing product", level="INFO", has_rubber=bool(num), stage=self._ocr_stage)
            print("Клік виявлено, але запис пропущено: порожній номер продукту (потрібно розпізнати код продукту)")
            return
        pair = (num, product.strip())
        now = time.monotonic()
        if pair == self._last_saved_pair and now - self._last_saved_monotonic < 1.5:
            debug_event("SAVE", "Duplicate click suppressed", level="INFO")
            print("Повторний клік пропущено (захист від дублювання)")
            return
        self._last_saved_pair, self._last_saved_monotonic = pair, now
        kind = self.classify_key(num)
        type_info = self.cfg.get("number_lists", {}).get(kind, {})
        stamp = datetime.now().isoformat(timespec="seconds")
        day, shift = shift_info(stamp)
        record = {"id": str(uuid.uuid4()), "number": num,
                  "product": (product or "").strip(), "time": stamp,
                  "type_key": kind or "none",
                  "type_uk": get_label(type_info, "uk") if kind else "НЕ В СПИСКУ",
                  "type_pl": get_label(type_info, "pl") if kind else "POZA LISTĄ",
                  "shift_date": day, "shift": shift,
                  "device_id": self.device_id}
        if os.path.isdir(self.images_dir) and self._image_catalog._ready.is_set():
            record['photo_missing'] = not bool(self.photo_for(num))
        with HISTORY_LOCK:
            self.history.append(record)
            save_history(self.history)
            self.history_revision += 1
            self.refresh_code_indexes()
        self._ocr_stage = "saved"
        debug_event("SAVE", "Record committed", level="INFO", record_id=record["id"], shift=shift, type=kind, device=self.device_id)
        print(f"[SAVE] гума={num}, продукт={product}, тип={record['type_uk']}")
        self._on_number_saved(num)
        self._sync_wakeup.set()
        # Sync loop retries automatically when internet comes back.

    def _on_number_saved(self, num):
        self._update_work_indicator()
        if self.work_win and self.work_win.winfo_exists():
            self.work_win.refresh(force=True)
        if self.history_win is not None and self.history_win.winfo_exists():
            self.history_win._refresh()

    def open_history(self):
        if self.history_win is not None and self.history_win.winfo_exists():
            self.history_win.lift()
            return
        debug_event("HISTORY", "History window opened", level="INFO", shift=shift_info())
        self.history_win = HistoryWindow(self.root, self.lang, self.history,
                                         cloud_loader=remote_history_get,
                                         number_lists=self.cfg.get("number_lists", {}))
        self._apply_dialog_theme(self.history_win)
        self.history_win.protocol("WM_DELETE_WINDOW", self._close_history)

    def _close_history(self):
        if self.history_win is not None:
            self.history_win.destroy()
            self.history_win = None
        self.refresh_code_indexes()

    def open_lists_editor(self):
        def on_save():
            self.cfg["lists_pending"] = True
            self._sync_wakeup.set()
            self.redraw_result()
        if self.editor is not None and self.editor.winfo_exists():
            self.editor.lift()
            return
        if not _check_console_password(self.root, self.lang):
            debug_event("LISTS", "List editor access denied", level="INFO")
            return
        debug_event("LISTS", "List editor opened", level="INFO")
        self.editor = ListsEditor(self.root, self.cfg, self.lang, on_save)
        self._apply_dialog_theme(self.editor)
        self.editor.protocol("WM_DELETE_WINDOW", self._close_editor)

    def _close_editor(self):
        if self.editor is not None:
            self.editor.destroy()
            self.editor = None

    def toggle_collapse(self):
        self.collapsed = not self.collapsed
        if self.collapsed:
            self.content.pack_forget()
            self.btn_min.config(text="▢")
        else:
            self.content.pack(fill="both", expand=True)
            self.btn_min.config(text="—")
        self.place_bottom_right()

    def _resize_start(self, e):
        if self.collapsed:
            return
        self._rs = (self.root.winfo_x() + self.root.winfo_width(),
                    self.root.winfo_y() + self.root.winfo_height())

    def _resize_move(self, e):
        if self.collapsed or not hasattr(self, "_rs"):
            return
        right, bottom = self._rs
        l, t, r, b = work_area()
        w = max(self.MIN_W, min(right - e.x_root, r - l))
        h = max(self.MIN_H, min(bottom - e.y_root, b - t))
        self.W, self.H = int(w), int(h)
        self.root.geometry(f"{self.W}x{self.H}+{right - self.W}+{bottom - self.H}")

    def _resize_end(self, e):
        if self.collapsed or not hasattr(self, "_rs"):
            return
        del self._rs
        self.text_lbl.config(wraplength=0)
        self.img_cache.clear()
        self._image_request_id += 1
        self.current_file = object()
        self.redraw_result()
        self._fit_type_area()
        debug_event("UI", "Font sizes applied", level="INFO", sizes=self.cfg.get("font_sizes", {}))
        save_setting("window", {"width": self.W, "height": self.H})

    def _drag_start(self, e):
        self._dx, self._dy = e.x_root - self.root.winfo_x(), e.y_root - self.root.winfo_y()

    def _drag_move(self, e):
        self.root.geometry(f"+{e.x_root - self._dx}+{e.y_root - self._dy}")

    def quit(self):
        """Close Tk immediately; stop network listeners outside the GUI thread.

        Firebase SSE listener.close() may wait on a network read and must not
        run in a Tkinter button callback. All background workers use stop_evt.
        """
        if getattr(self, "_closing", False):
            return
        self._closing = True
        debug_event("APP", "Shutdown requested", level="INFO")
        self.stop_evt.set()
        self._sync_wakeup.set()

        # Detach listeners first so that callbacks cannot enqueue new UI work.
        listeners = list(getattr(self, "_live_listeners", []))
        self._live_listeners.clear()

        def close_network_listeners():
            for listener in listeners:
                try:
                    listener.close()
                    debug_event("FIREBASE", "Realtime listener closed", level="INFO")
                except Exception as exc:
                    debug_event("FIREBASE", "Listener close failed", level="ERROR", error=repr(exc))
            debug_event("APP", "Network listener shutdown completed", level="INFO")

        if listeners:
            threading.Thread(target=close_network_listeners,
                             name="SFCListenerShutdown", daemon=True).start()

        # Mouse hook stop can also be slow; never block the Tk mainloop.
        mouse_listener = self.mouse_listener
        self.mouse_listener = None
        if mouse_listener is not None:
            def stop_mouse():
                try:
                    mouse_listener.stop()
                except Exception as exc:
                    debug_event("CLICK", "Mouse listener stop failed", level="ERROR", error=repr(exc))
            threading.Thread(target=stop_mouse, name="SFCMouseShutdown", daemon=True).start()

        try:
            if self._opaque_overlay is not None:
                self._opaque_overlay.destroy()
                self._opaque_overlay = None
        except tk.TclError:
            pass
        try:
            self.root.destroy()
        except tk.TclError:
            pass
        debug_event("APP", "Tk window destroyed", level="INFO")

    def show_placeholder(self, text=None):
        if text is None:
            text = tr(self.lang, "no_match")
        self.body.config(image="", text=text)
        self.body.image = None

    def _image_target_size(self):
        # Called on Tk thread only. Stable throughout one image request.
        max_width = max(16, self.body.winfo_width() - 8, self.W - 12)
        available_height = self.H - self.TITLE_H - self.TEXT_H - self.badge_lbl.winfo_reqheight() - 16
        max_height = max(40, min(available_height, max(40, self.body.winfo_height() - 8)))
        return int(max_width), int(max_height)

    def _image_decode_worker(self):
        """Only Pillow work runs here; never call Tk from background threads."""
        while not self.stop_evt.is_set():
            try:
                request_id, filename, path, target_size = self._image_jobs.get(timeout=0.25)
            except queue.Empty:
                continue
            started = time.perf_counter()
            try:
                with Image.open(path) as source:
                    image = source.convert("RGBA")
                image.thumbnail(target_size, Image.Resampling.LANCZOS)
                error = None
            except Exception as exc:
                image = None
                error = repr(exc)
            if not self.stop_evt.is_set():
                self.q.put(("IMAGE_READY", request_id, filename, path, target_size,
                            image, error, round((time.perf_counter()-started)*1000, 2)))

    def load_image(self, filename):
        """Nonblocking display: return cached PhotoImage or schedule decode."""
        path = os.path.join(self.images_dir, filename)
        target_size = self._image_target_size()
        try:
            stat = os.stat(path)
            key = (path, stat.st_mtime_ns, stat.st_size, target_size)
        except OSError as exc:
            debug_event("IMAGE", "File missing", level="ERROR", file=filename, error=repr(exc))
            return None
        if key in self.img_cache:
            self.img_cache.move_to_end(key)
            debug_event("PERFORMANCE", "Image cache HIT", interval=2, file=filename)
            return self.img_cache[key]
        self._image_request_id += 1
        request_id = self._image_request_id
        # Discard stale pending images: the most recent OCR image takes priority.
        try:
            while True:
                self._image_jobs.get_nowait()
        except queue.Empty:
            pass
        try:
            self._image_jobs.put_nowait((request_id, filename, path, target_size))
            debug_event("PERFORMANCE", "Image queued", interval=2, file=filename)
        except queue.Full:
            debug_event("IMAGE", "Decode queue full", level="ERROR", file=filename)
        return None

    def _image_ready(self, args):
        _, request_id, filename, path, target_size, im, error, decode_ms = args
        if request_id != self._image_request_id or filename != self.current_file:
            return
        if path != os.path.join(self.images_dir, filename):
            return
        if error or im is None:
            debug_event("IMAGE", "Decode failed", level="ERROR", file=filename, error=error)
            self.show_placeholder(tr(self.lang, "image_open_error"))
            return
        started = time.perf_counter()
        try:
            stat = os.stat(path)
            key = (path, stat.st_mtime_ns, stat.st_size, target_size)
            ph = ImageTk.PhotoImage(im)
            self.img_cache[key] = ph
            self.img_cache.move_to_end(key)
            while len(self.img_cache) > self._image_cache_limit:
                self.img_cache.popitem(last=False)
            self.body.config(image=ph, text="")
            self.body.image = ph
            self._overlay_sig = None
            debug_event("PERFORMANCE", "Image displayed", level="INFO", file=filename,
                        decode_ms=decode_ms,
                        display_ms=round((time.perf_counter()-started)*1000, 2),
                        cache_size=len(self.img_cache))
        except (OSError, tk.TclError) as exc:
            debug_event("IMAGE", "Tk display failed", level="ERROR", file=filename, error=repr(exc))

    def _extract_valid_numbers(self, text):
        text = clean_ocr_text(text)
        if not text:
            return []
        result = []
        for seq in re.findall(r"\d+", text):
            if is_valid_number(seq):
                result.append(seq)
        return result

    def _extract_product_number(self, text):
        text = clean_ocr_text(text)
        if not text:
            return ""
        best = ""
        for seq in re.findall(r"\d+", text):
            if len(seq) >= 8 and len(seq) > len(best):
                best = seq
        return best

    def _extract_all_long_numbers(self, text):
        text = clean_ocr_text(text)
        if not text:
            return []
        return [seq for seq in re.findall(r"\d+", text) if len(seq) >= 8]

    def find_image_by_history(self, text):
        """Resolve numbers and historical codes even when a photo is absent."""
        candidates = self._extract_valid_numbers(text)
        if candidates:
            num = candidates[0]
            return self.photo_for(num), 'number', '', num
        for code in self._extract_all_long_numbers(text):
            num = self.product_index.get(code)
            if num:
                return self.photo_for(num), 'product', code, num
        return None, None, '', ''

    def classify_key(self, number):
        num = str(number).strip()
        for key, info in self.cfg.get("number_lists", {}).items():
            if key != "none" and num in set(map(str, info.get("numbers", []))):
                return key
        return ""

    @staticmethod
    def _make_notification_wav():
        """Generate a PCM WAV played through the Windows default audio output.

        Unlike winsound.Beep(), PlaySound uses the normal multimedia output.
        """
        sample_rate = 44100
        filename = None
        try:
            with tempfile.NamedTemporaryFile(prefix="sfc_sound_", suffix=".wav", delete=False) as tmp:
                filename = tmp.name
            # Short, distinct two-note chime with smooth envelopes.
            with wave.open(filename, "wb") as out:
                out.setnchannels(1)
                out.setsampwidth(2)
                out.setframerate(sample_rate)
                frames = bytearray()
                notes = ((880.0, 0.24), (1175.0, 0.28))
                for frequency, duration in notes:
                    count = round(sample_rate * duration)
                    ramp = max(1, round(sample_rate * 0.012))
                    for i in range(count):
                        envelope = min(1.0, i / ramp, (count - 1 - i) / ramp)
                        envelope = max(0.0, envelope)
                        sample = int(32767 * 0.75 * envelope * math.sin(2 * math.pi * frequency * i / sample_rate))
                        frames.extend(struct.pack("<h", sample))
                out.writeframes(frames)
            return filename
        except Exception:
            if filename:
                try:
                    os.unlink(filename)
                except OSError:
                    pass
            raise

    def _sound_worker(self):
        """Play sound on the default Windows output without blocking Tkinter."""
        wav_file = None
        try:
            wav_file = self._make_notification_wav()
            debug_event("SOUND", "WAV notification prepared", level="INFO", backend="PlaySound")
        except Exception as exc:
            debug_event("SOUND", "Cannot prepare WAV notification", level="ERROR", error=repr(exc))
        try:
            while not self.stop_evt.is_set():
                try:
                    number, rubber_type = self._sound_events.get(timeout=0.3)
                except queue.Empty:
                    continue
                try:
                    if wav_file is None:
                        raise RuntimeError("Notification WAV is unavailable")
                    winsound.PlaySound(wav_file, winsound.SND_FILENAME | winsound.SND_SYNC | winsound.SND_NODEFAULT)
                    debug_event("SOUND", "WAV playback completed", level="INFO",
                                rubber=number, rubber_type=rubber_type, backend="PlaySound")
                except Exception as exc:
                    debug_event("SOUND", "WAV playback failed, trying fallback", level="ERROR",
                                rubber=number, error=repr(exc))
                    try:
                        winsound.MessageBeep(winsound.MB_ICONEXCLAMATION)
                        debug_event("SOUND", "Fallback call returned", level="INFO", rubber=number)
                    except Exception as fallback_exc:
                        debug_event("SOUND", "All audio methods failed", level="ERROR",
                                    rubber=number, error=repr(fallback_exc))
                finally:
                    self._sound_events.task_done()
        finally:
            if wav_file:
                try:
                    os.unlink(wav_file)
                except OSError:
                    pass

    def _beep_if_selected(self, number):
        """Signal a newly seen valid listed rubber, or the same rubber re-entered later.

        Short OCR gaps caused by the blinking caret must not trigger repeats.
        """
        if not number or not self.cfg.get("sound_enabled", True):
            return
        rubber_type = self.classify_key(number)
        if not rubber_type:
            return
        now = time.monotonic()
        # A continuous valid OCR result counts as a single entry. The same
        # number triggers again only after >=2.5 seconds of invalid OCR.
        is_new = (number != self._last_sound_number or
                  (self._sound_missing_since is not None and
                   now - self._sound_missing_since >= 2.5))
        self._sound_missing_since = None
        if not is_new:
            return
        try:
            self._sound_events.put_nowait((number, rubber_type))
            self._last_sound_number = number
            self._last_sound_time = now
            debug_event("SOUND", "WAV queued", level="INFO",
                        rubber=number, rubber_type=rubber_type)
        except queue.Full:
            debug_event("SOUND", "Audio queue full", level="ERROR", rubber=number)

    def classify_number(self, number):
        """Визначити тип (РУМУНІЯ / МАРОККО / СЕЛЕКЦІЯ / None) за номером гуми."""
        if not number:
            return "", ""
        num = str(number).strip()
        lists = self.cfg.get("number_lists", {})
        for key, info in lists.items():
            if key == "none":
                continue
            label = get_label(info, self.lang)
            color = info.get("color", "#888888")
            numbers = set(str(n).strip() for n in info.get("numbers", []))
            if not numbers or not label:
                continue
            if num in numbers:
                return label, color
        return "", ""

    def show_result(self, text, filename, badge_text="", number_for_classify="", process_ocr=True):
        text = clean_ocr_text(text)
        self.last_result = (text, filename, badge_text, number_for_classify)

        shown = " ".join(text.split())
        if len(shown) > 70:
            shown = shown[:70] + "…"
        self.text_lbl.config(text=shown or "—")

        # OCR input workflow: rubber number -> product code -> click SAVE.
        # The rubber number is intentionally sticky and has NO time-based expiry.
        # An image found by historical product lookup must not start a new binding.
        candidates = self._extract_valid_numbers(text)
        detected_product = self._extract_product_number(text)
        detected_number = candidates[0] if candidates else ""

        if process_ocr:
            if detected_number:
                self._beep_if_selected(detected_number)
                # Only an actual valid 5/7-digit number seen by OCR starts a new
                # rubber entry. Looking up an 8+ digit product does not reset it.
                if self._ocr_stage != "rubber" or detected_number != self.last_valid_number:
                    self.last_valid_number = detected_number
                    self.current_product = ""  # prevent pairing with previous product
                    self._ocr_stage = "rubber"
                    debug_event("OCR", "Valid rubber detected", level="INFO", stage=self._ocr_stage, type=self.classify_key(detected_number))
                    print("[OCR] Запам'ятано номер гуми:", detected_number)
            elif detected_product:
                if self._sound_missing_since is None:
                    self._sound_missing_since = time.monotonic()
                # After the number is replaced by product code, keep the rubber
                # number until a NEW valid rubber entry (or program restart).
                if self.last_valid_number and self._ocr_stage in ("rubber", "product"):
                    self.current_product = detected_product
                    if self._ocr_stage != "product":
                        debug_event("OCR", "Switched to product stage", level="INFO", product_length=len(detected_product))
                    self._ocr_stage = "product"
                elif not self.last_valid_number:
                    # Historical product lookup still works without an active pair.
                    self.current_product = detected_product
                # Do not change the stored rubber number here.
            else:
                if self._sound_missing_since is None:
                    self._sound_missing_since = time.monotonic()
            # Blank/partial OCR, blinking caret, and editing do not clear anything.

            ocr_state = (text.strip(), self.last_valid_number, self.current_product, self._ocr_stage)
            if ocr_state != self._ocr_last_logged:
                debug_event("OCR", "Recognized content changed", stage=self._ocr_stage, text_length=len(text.strip()), rubber_known=bool(self.last_valid_number), product_known=bool(self.current_product))
                self._ocr_last_logged = ocr_state
                print("[OCR] текст:", repr(text.strip()[:160]),
                      "| гума:", repr(self.last_valid_number),
                      "| продукт:", repr(self.current_product),
                      "| етап:", self._ocr_stage)

        # --- ВИЗНАЧЕННЯ ТИПУ ---
        label = ""
        color = ""
        type_number = ""
        if detected_number:
            type_number = detected_number
        elif detected_product and self.last_valid_number and self._ocr_stage in ('product','saved') and detected_product == self.current_product:
            # Keep the active rubber visible while the product code is printed.
            type_number = self.last_valid_number
            filename = self.photo_for(type_number)
        elif number_for_classify:
            type_number = number_for_classify
        self._display_number = type_number
        if detected_number and len(self.raw_codes.get(detected_number, [])) > 1:
            primary = self.number_index.get(detected_number, '')
            if primary:
                self.text_lbl.configure(text=detected_number + ' · ' + primary)
        self._update_work_indicator()

        if type_number:
            label, color = self.classify_number(type_number)
            # Sound is emitted only for a newly recognized rubber number,
            # not for redraws, history lookups or partial OCR frames.

        if label:
            self.badge_lbl.config(text=label, fg=color, bg="#101010")
        elif type_number or filename is not None:
            # The rubber is known even if it has no image.
            self.badge_lbl.config(
                text=tr(self.lang, "type_none"),
                fg=tr(self.lang, "type_none_color"),
                bg="#101010"
            )
        else:
            self.badge_lbl.config(text="", bg="#101010")

        # Auto-grow the type label if a newly recognised list has a long name.
        self._fit_type_area()

        # --- ФОТО ---
        if filename is None:
            if self.current_file is not None:
                self._image_request_id += 1
            self.current_file = None
            placeholder = ('Немає фото / Brak zdjęcia' if type_number else tr(self.lang, 'no_match'))
            if self.body.image is not None or self.body.cget('text') != placeholder:
                self.show_placeholder(placeholder)
            return
        if filename == self.current_file:
            return
        self.current_file = filename
        ph = self.load_image(filename)
        if ph is None:
            # Asynchronous decode: keep the UI responsive and the type badge intact.
            self.body.config(image="", text="Завантаження фото…" if self.lang == "uk" else "Ładowanie zdjęcia…")
            self.body.image = None
        else:
            self.body.config(image=ph, text="")
            self.body.image = ph
            self._overlay_sig = None
            debug_event("IMAGE", "Image displayed in Tk", level="INFO", file=filename)

    def _ocr_result_args(self, text):
        filename, match_type, token, number = self.find_image_by_history(text)
        badge = (f"{tr(self.lang, 'matched_by_product')}: {token}" if match_type == 'product'
                 else tr(self.lang, 'matched_by_number') if match_type == 'number' else '')
        return text, filename, badge, number

    def _ocr_show_preview(self, generation, text):
        self._ocr_preview_generation = generation
        self._ocr_preview_text = text
        numbers = self._extract_valid_numbers(text)
        if numbers and numbers[0] != self.last_valid_number:
            self._ocr_unverified_rubber = True
        # When another capture is already in progress, don't flash stale photos.
        if generation != self._ocr_generation:
            return
        if text.strip():
            self.show_result(*self._ocr_result_args(text), process_ocr=False)

    def _ocr_handle_click(self, generation):
        if generation != self._ocr_generation or self.reset_hash:
            debug_event('CLICK', 'Capture changed before print validation', level='INFO')
            return
        if generation != self._ocr_verified_generation:
            # Defer the click only for the very same capture and rubber. A
            # corrected/ambiguous preview is not an authorization to save it.
            preview = (self._extract_product_number(self._ocr_preview_text)
                       if self._ocr_preview_generation == generation else '')
            self._ocr_deferred_click = (generation, self.last_valid_number, preview)
            debug_event('CLICK', 'Print click deferred for OCR confirmation', level='INFO')
            return
        if (self._ocr_stage == 'product' and self.last_valid_number
                and self.current_product and self.current_product == self._ocr_verified_product):
            self._commit_record(self.last_valid_number, self.current_product)
        else:
            debug_event('CLICK', 'Print click skipped: no verified rubber/product pair', level='INFO')

    def _ocr_finish_result(self, generation, text):
        numbers = self._extract_valid_numbers(text)
        product = self._extract_product_number(text)
        if numbers:
            self._ocr_unverified_rubber = False
        elif product and self._ocr_unverified_rubber:
            # A new rubber preview never finished verification. Do not pair
            # the next product with a previous rubber by accident.
            self.last_valid_number = self.current_product = ''
            self._ocr_stage = 'idle'
        self.show_result(*self._ocr_result_args(text))
        self._ocr_verified_generation = generation
        self._ocr_verified_product = product if not numbers else ''
        pending = self._ocr_deferred_click
        if pending and pending[0] <= generation:
            self._ocr_deferred_click = None
            if (pending[0] == generation == self._ocr_generation and not self.reset_hash
                    and pending[1] and pending[1] == self.last_valid_number
                    and (not pending[2] or pending[2] == product)
                    and product and not numbers):
                self._ocr_handle_click(generation)
            else:
                debug_event('CLICK', 'Deferred click skipped: input or preview changed', level='INFO')

    def poll(self):
        try:
            # Never empty an endlessly refilled queue in one Tk callback.
            # Bound processing to keep mouse events, window painting and dialogs responsive.
            deadline = time.perf_counter() + 0.012
            handled = 0
            while handled < 24 and time.perf_counter() < deadline:
                args = self.q.get_nowait()
                handled += 1
                if args[0] == "IMAGE_READY":
                    self._image_ready(args)
                elif args[0] == "OCR_PREVIEW":
                    self._ocr_show_preview(*args[1:])
                elif args[0] == "OCR_FINAL":
                    self._ocr_finish_result(*args[1:])
                elif args[0] == "OCR_CLICK":
                    self._ocr_handle_click(*args[1:])
                elif args[0] == "SAVE":
                    debug_event("QUEUE", "Save request received")
                    self._commit_record(*args[1:])
                elif args[0] == "LISTS_UPLOADED":
                    if json.dumps(self.cfg.get("number_lists", {}), sort_keys=True, ensure_ascii=False) == args[1]:
                        self.cfg["lists_pending"] = False
                        save_setting("lists_pending", False)
                        debug_event("LISTS", "Remote list upload acknowledged", level="INFO")
                elif args[0] == "LISTS_DOWNLOADED":
                    if not self.cfg.get("lists_pending", False):
                        debug_event("LISTS", "Applying remote lists", level="INFO", groups=len(args[1]))
                        self.cfg["number_lists"] = args[1]
                        save_setting("number_lists", args[1])
                        if self.history_win and self.history_win.winfo_exists():
                            self.history_win.number_lists = args[1]
                            self.history_win._refresh()
                        if self.editor and self.editor.winfo_exists():
                            self.editor.apply_remote_lists(args[1])
                            self._apply_dialog_theme(self.editor)
                        self.redraw_result()
                elif args[0] == "SYNC":
                    rows = args[1]
                    with HISTORY_LOCK:
                        known = {r["id"] for r in self.history}
                        added = [r for r in rows if r["id"] not in known]
                        if added:
                            debug_event("HISTORY", "New remote records applied", level="INFO", count=len(added))
                            self.history.extend(added)
                            self.history.sort(key=lambda r: r.get("time", ""))
                            save_history(self.history)
                            self.history_revision += 1
                            self.refresh_code_indexes()
                    if added:
                        self.redraw_result()
                        if self.work_win and self.work_win.winfo_exists():
                            self.work_win.refresh(force=True)
                    if self.history_win and self.history_win.winfo_exists():
                        if self.history_win.mode.get() == "cloud" and added:
                            cloud_map = {r["id"]: r for r in self.history_win.cloud_rows}
                            cloud_map.update({r["id"]: r for r in added})
                            self.history_win.cloud_rows = list(cloud_map.values())
                        self.history_win._refresh()
                else:
                    self.show_result(*args)
        except queue.Empty:
            pass
        except Exception as exc:
            debug_event("UI", "Queue processing failed", level="ERROR", error=repr(exc))
            traceback.print_exc()
        if not self.stop_evt.is_set():
            self.root.after(60, self.poll)

    def find_image(self, text):
        started = time.perf_counter()
        result = self._image_catalog.lookup_text(text)
        if result:
            debug_event("PERFORMANCE", "Image lookup", interval=4, file=result,
                        lookup_ms=round((time.perf_counter()-started)*1000, 3))
        return result

    def ocr(self, img, psm=None):
        buf = io.BytesIO()
        img.save(buf, format="PNG")
        cmd = [TESS_EXE, "stdin", "stdout",
               "-l", self.cfg["languages"],
               "--tessdata-dir", "tessdata",
               "--psm", str(int(self.cfg["psm"] if psm is None else psm))]
        flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
        started = time.perf_counter()
        r = subprocess.run(cmd, input=buf.getvalue(), stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, cwd=TESS_DIR, creationflags=flags)
        if r.returncode != 0:
            debug_event("OCR", "Tesseract execution failed", level="ERROR", returncode=r.returncode, stderr=r.stderr.decode("utf-8", "replace")[:180])
            raise RuntimeError(r.stderr.decode("utf-8", "replace").strip())
        debug_event("OCR", "Tesseract processed frame", interval=15, duration_ms=round((time.perf_counter()-started)*1000,1), bytes=len(buf.getvalue()), result_length=len(r.stdout))
        return r.stdout.decode("utf-8", "replace")

    def loop(self):
        interval = max(0.2, float(self.cfg["interval"]))
        up = max(1, int(self.cfg["upscale"]))
        last_hash = None
        settled_frames = set()
        confirmed_clean = None

        with (mss.MSS() if hasattr(mss, "MSS") else mss.mss()) as sct:
            while not self.stop_evt.is_set():
                t0 = time.time()
                try:
                    monitor = dict(self.region)
                    if self.reset_hash:
                        last_hash, self.reset_hash = None, False
                        settled_frames.clear()
                        confirmed_clean = None
                    def grab_frame():
                        capture = sct.grab(monitor)
                        return Image.frombytes("RGB", capture.size, capture.bgra, "raw", "BGRX")
                    img = grab_frame()
                    raw = img.tobytes()
                    h = hashlib.md5(raw).hexdigest()
                    if h != last_hash:
                        last_hash = h
                        # Suppress known blink phases only for the current
                        # verified field. A new input invalidates the cache.
                        if raw in settled_frames:
                            self.stop_evt.wait(interval)
                            continue
                        # A later caret-on phase may not have been captured
                        # during the first observation window. Ignore it only
                        # if the verified clean image is still the clean one.
                        if confirmed_clean is not None:
                            same = ocr_blink_pair(confirmed_clean, img)
                            if same is not None and same.tobytes() == confirmed_clean.tobytes():
                                if len(settled_frames) < 16:
                                    settled_frames.add(raw)
                                self.stop_evt.wait(interval)
                                continue
                        self._ocr_generation += 1
                        generation = self._ocr_generation
                        settled_frames.clear()
                        confirmed_clean = None
                        debug_event("CAPTURE", "Screen changed", interval=10, width=img.width, height=img.height)
                        if img.height <= 80 and img.width <= 1000 and img.width >= 1.5 * img.height:
                            # First pass immediately: no pre-OCR blink delay.
                            preview = recognize_ocr_line_first(img, self.ocr, up)
                            if self.reset_hash or monitor != self.region:
                                last_hash = None
                                continue
                            self.q.put(("OCR_PREVIEW", generation, preview))
                            observed = set()
                            # Grab again immediately after the first pass. If
                            # typing continued, start fresh without waiting .78s.
                            current = grab_frame()
                            candidate = img if raw == current.tobytes() else ocr_blink_pair(img, current)
                            if candidate is None:
                                last_hash = None
                                continue
                            observed.update((raw, current.tobytes()))
                            clean = ocr_capture_without_blink(candidate, grab_frame, self.stop_evt.wait, observed=observed)
                            if clean is None or self.reset_hash or monitor != self.region:
                                last_hash = None
                                continue
                            # Reuse the first pass only if its source is also
                            # the verified clean frame; otherwise redo it.
                            reuse = preview if clean.tobytes() == raw else None
                            text = recognize_ocr_line(clean, self.ocr, up, first_result=reuse)
                            # Check that typing did not change the field during
                            # the slower Tesseract confirmation passes.
                            current = grab_frame()
                            if self.reset_hash or monitor != self.region:
                                last_hash = None
                                continue
                            if current.tobytes() not in observed:
                                if ocr_blink_pair(clean, current) is None:
                                    last_hash = None
                                    continue
                                observed.add(current.tobytes())
                            # Even an unresolved static field should not flash
                            # the same provisional value repeatedly. A changed
                            # input (including an unseen blink phase) retries.
                            settled_frames = observed
                            if text.strip():
                                confirmed_clean = clean
                        else:
                            g, alternate = ocr_contrast_images(img)
                            def recognize(frame):
                                frame = remove_ocr_edge_caret(frame)
                                if up > 1:
                                    frame = frame.resize((frame.width * up, frame.height * up), Image.Resampling.LANCZOS)
                                # Tight OCR selections can make Tesseract omit a real
                                # final digit. Pad AFTER edge-artifact removal and
                                # resizing; never synthesize a digit missing from capture.
                                frame = ImageOps.expand(frame, border=10, fill=255)
                                return clean_ocr_text(self.ocr(frame))
                            text = recognize(g)
                            if alternate is not None and not (self._extract_valid_numbers(text) or self._extract_product_number(text)):
                                retry = recognize(alternate)
                                if self._extract_valid_numbers(retry) or self._extract_product_number(retry):
                                    text = retry
                                    debug_event('OCR', 'Alternate contrast recovered identifier', interval=2)
                        if self.reset_hash or monitor != self.region:
                            last_hash = None
                            continue
                        self.q.put(("OCR_FINAL", generation, text))
                except Exception as e:
                    last_hash = None
                    settled_frames.clear()
                    confirmed_clean = None
                    self._ocr_generation += 1
                    debug_event("OCR", "Capture/OCR loop exception", level="ERROR", error=repr(e))
                    traceback.print_exc()
                    print("Помилка циклу:", e)
                dt = time.time() - t0
                self.stop_evt.wait(max(0.05, interval - dt))

    def _start_live_listeners(self):
        """Listen for Firebase changes and wake the sync worker immediately.

        If listen() is unavailable (network/proxy limitations), short polling
        in _sync_loop continues to work automatically.
        """
        if not self.firebase_ready:
            return
        refs = (("lists", FIREBASE_LISTS_ROOT), ("history", FIREBASE_ROOT))
        for name, path in refs:
            if self.stop_evt.is_set():
                break
            try:
                def changed(event, category=name):
                    if not self.stop_evt.is_set():
                        debug_event("SYNC", "Realtime notification", interval=2, kind=category,
                                    path=getattr(event, "path", ""))
                        self._sync_wakeup.set()
                registration = fb_db.reference(path).listen(changed)
                self._live_listeners.append(registration)
                debug_event("SYNC", "Realtime listener active", level="INFO", kind=name)
            except Exception as exc:
                debug_event("SYNC", "Realtime listener unavailable; polling remains active",
                            level="ERROR", kind=name, error=repr(exc))

    def _sync_loop(self):
        while not self.stop_evt.is_set():
            try:
                new, sent = sync_once(self.history, self.device_id)
                # Shared Firebase list is canonical. Offline edits are uploaded when connectivity returns.
                pending = bool(self.cfg.get("lists_pending", False))
                if pending:
                    remote_lists_set(self.cfg.get("number_lists", {}), self.device_id)
                    self.q.put(("LISTS_UPLOADED", json.dumps(self.cfg.get("number_lists", {}), sort_keys=True, ensure_ascii=False)))
                else:
                    remote_doc = remote_lists_get()
                    if remote_doc is None:
                        if not self._remote_lists_seen:
                            remote_lists_set(self.cfg.get("number_lists", {}), self.device_id)
                            self._remote_lists_seen = True
                    else:
                        self._remote_lists_seen = True
                        remote_lists = remote_doc.get("lists", {})
                        if remote_lists != self.cfg.get("number_lists", {}):
                            self.q.put(("LISTS_DOWNLOADED", remote_lists))
                if new:
                    self.q.put(("SYNC", new))
                self._sync_status = f"online: +{len(new)} / ↑{sent}"
                debug_event("SYNC", "Sync cycle completed", interval=60, received=len(new), sent=sent, pending_lists=pending)
            except Exception as exc:
                self._sync_status = f"offline: {exc}"
                debug_event("SYNC", "Sync cycle failed", level="ERROR", interval=30, error=repr(exc))
                print("Синхронізація:", exc)
            # Wake immediately on Firebase event; 2-second safety poll if
            # an SSE notification is lost or live listening is unavailable.
            self._sync_wakeup.wait(timeout=2.0)
            self._sync_wakeup.clear()

    def _set_anchor_for_region(self, region, field):
        hwnd = find_anchor_window(region["left"] + region["width"] // 2,
                                  region["top"] + region["height"] // 2,
                                  self.root.winfo_id())
        origin = window_client_origin(hwnd)
        if not origin:
            self.anchors.pop(field, None)
            self._anchor_last.pop(field, None)
            debug_event("ANCHOR", "Using absolute coordinates", level="INFO", field=field)
            print(f"{field}: абсолютна область без прив'язки до вікна")
            return
        self.anchors[field] = {"hwnd": hwnd, "relative": relative_region(region, origin)}
        debug_event("ANCHOR", "Target window selected", level="INFO", field=field, hwnd=hwnd, relative=self.anchors[field]["relative"])
        self._anchor_last[field] = origin
        print(f"{field}: прив'язано до вікна HWND={hwnd}")

    def _track_anchor(self):
        for name, anchor in list(self.anchors.items()):
            origin = window_client_origin(anchor.get("hwnd"))
            if origin is None:
                # Continue to allow OCR/clicks at their last known screen positions.
                continue
            if origin != self._anchor_last.get(name):
                self._anchor_last[name] = origin
                region = absolute_region(anchor["relative"], origin)
                setattr(self, name, region)
                if name == "region":
                    self.reset_hash = True
                self._update_title()
        if not self.stop_evt.is_set():
            self.root.after(150, self._track_anchor)

    def _apply_dialog_theme(self, window):
        """One dark/light palette across standard Tk and ttk dialogs."""
        light = self.cfg.get("theme") == "light"
        bg = "#f2f4f7" if light else "#202020"
        card = "#ffffff" if light else "#292f3b"
        fg = "#202938" if light else "#e5eaf2"
        muted = "#4c5d75" if light else "#b9c6d9"
        accent = "#2863d7" if light else "#4385ed"
        sizes = self.cfg.get("font_sizes", {})
        try: font_size = max(7, min(42, int(sizes.get("interface", 9))))
        except (ValueError, TypeError): font_size = 9
        style = ttk.Style(window)
        style.theme_use("clam")
        style.configure("TFrame", background=bg)
        style.configure("TLabel", background=bg, foreground=fg, font=("Segoe UI", font_size))
        style.configure("Heading.TLabel", background=bg, foreground=fg, font=("Segoe UI", font_size + 2, "bold"))
        style.configure("TButton", background=card, foreground=fg, font=("Segoe UI", font_size), padding=(9, 5), borderwidth=1)
        style.map("TButton", background=[("active", accent)], foreground=[("active", "#ffffff")])
        style.configure("TRadiobutton", background=bg, foreground=fg, font=("Segoe UI", font_size))
        style.map("TRadiobutton", background=[("active", bg)])
        style.configure("TCheckbutton", background=bg, foreground=fg, font=("Segoe UI", font_size))
        style.configure("TEntry", fieldbackground=card, foreground=fg, font=("Segoe UI", font_size), padding=5)
        style.configure("TCombobox", fieldbackground=card, background=card, foreground=fg, arrowcolor=fg, padding=5)
        style.map("TCombobox", fieldbackground=[("readonly", card)], foreground=[("readonly", fg)])
        style.configure("Treeview", background=card, fieldbackground=card, foreground=fg,
                        font=("Segoe UI", font_size), rowheight=max(24, int(font_size * 2.5)), borderwidth=0)
        style.configure("Treeview.Heading", background=bg, foreground=fg, font=("Segoe UI", font_size, "bold"))
        style.map("Treeview", background=[("selected", accent)], foreground=[("selected", "#ffffff")])
        style.configure("TNotebook", background=bg, borderwidth=0)
        style.configure("TNotebook.Tab", background=card, foreground=fg, padding=(12, 6), font=("Segoe UI", font_size))
        style.map("TNotebook.Tab", background=[("selected", accent)], foreground=[("selected", "#ffffff")])
        style.configure("TScale", background=bg)
        try: window.configure(bg=bg)
        except tk.TclError: pass
        def walk(widget):
            try:
                klass = widget.winfo_class()
                if klass in ("Frame", "Toplevel", "LabelFrame"):
                    widget.configure(bg=bg)
                elif klass == "Label":
                    # The main OCR labels have independent font settings and
                    # the SFC Solutions title must remain completely static.
                    if widget in (self.title_lbl, self.text_lbl, self.badge_lbl, self.body):
                        return
                    current_fg = str(widget.cget("fg")).lower()
                    new_fg = muted if current_fg in ("#aaa", "#888", "#b9c6d9") else fg
                    widget.configure(bg=bg, fg=new_fg, font=("Segoe UI", font_size))
                elif klass in ("Entry", "Text", "Listbox", "Spinbox"):
                    widget.configure(bg=card, fg=fg, insertbackground=fg, selectbackground=accent,
                                     font=("Segoe UI", font_size))
                elif klass == "Button":
                    bg_before = str(widget.cget("bg")).lower()
                    if bg_before not in ("#1b5e20", "#b71c1c") and not (bg_before.startswith("#") and bg_before not in ("#2c2c2c", "#303030", "#e3e9f2", "#292f3b", "#ffffff")):
                        widget.configure(bg=card, fg=fg, activebackground=accent, activeforeground="#ffffff")
                    widget.configure(font=("Segoe UI", font_size))
            except (tk.TclError, ValueError):
                pass
            for child in widget.winfo_children():
                walk(child)
        walk(window)

    # Windows/Tk cannot apply alpha to selected widgets in a single HWND.
    # An independent color-keyed, mouse-click-through window therefore draws
    # the image and important text at full opacity above the dimmed base UI.
    def _create_opaque_overlay(self):
        if self._opaque_overlay is not None:
            return
        if sys.platform != "win32":
            return
        key = "#ff00fe"  # reserved chroma key, never used by the UI
        try:
            win = tk.Toplevel(self.root)
            win.withdraw()
            win.overrideredirect(True)
            win.configure(bg=key)
            win.wm_attributes("-transparentcolor", key)
            win.wm_attributes("-topmost", True)
            canvas = tk.Canvas(win, bg=key, highlightthickness=0,
                               bd=0, relief="flat")
            canvas.pack(fill="both", expand=True)
            win.update_idletasks()
            # WS_EX_TRANSPARENT = pass mouse activity to the application below.
            # WS_EX_NOACTIVATE = preserve focus of the target OCR application.
            user32 = ctypes.windll.user32
            hwnd = user32.GetParent(win.winfo_id()) or win.winfo_id()
            GWL_EXSTYLE = -20
            WS_EX_TRANSPARENT = 0x20
            WS_EX_NOACTIVATE = 0x08000000
            if ctypes.sizeof(ctypes.c_void_p) == 8:
                get_ex = user32.GetWindowLongPtrW
                set_ex = user32.SetWindowLongPtrW
            else:
                get_ex = user32.GetWindowLongW
                set_ex = user32.SetWindowLongW
            get_ex.argtypes = [ctypes.c_void_p, ctypes.c_int]
            get_ex.restype = ctypes.c_ssize_t
            set_ex.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_ssize_t]
            set_ex.restype = ctypes.c_ssize_t
            style = get_ex(hwnd, GWL_EXSTYLE)
            set_ex(hwnd, GWL_EXSTYLE, style | WS_EX_TRANSPARENT | WS_EX_NOACTIVATE)
            self._opaque_overlay = win
            self._opaque_canvas = canvas
        except Exception as e:
            print("[Прозорість] Не вдалося створити захисний шар:", e)
            try:
                win.destroy()
            except Exception:
                pass
            self._opaque_overlay = None
            self._opaque_canvas = None

    def _refresh_opaque_overlay(self):
        try:
            alpha = int(self.cfg.get("transparency", 100))
            if alpha >= 100 or self.collapsed or not self.root.winfo_viewable():
                if self._opaque_overlay is not None:
                    self._opaque_overlay.withdraw()
            else:
                self._create_opaque_overlay()
                win = self._opaque_overlay
                canvas = self._opaque_canvas
                if win is not None and canvas is not None:
                    x, y = self.root.winfo_rootx(), self.root.winfo_rooty()
                    width, height = self.root.winfo_width(), self.root.winfo_height()
                    geometry = f"{width}x{height}{x:+d}{y:+d}"
                    if win.geometry() != geometry:
                        win.geometry(geometry)
                    if not win.winfo_viewable():
                        win.deiconify()
                        win.lift(self.root)
                    # Repainting every 80ms even without changes causes severe
                    # Tk/Windows redraw load and may make the main UI unresponsive.
                    sig = (geometry, id(self.body.image), self.body.cget("text"),
                           self.text_lbl.cget("text"), self.badge_lbl.cget("text"),
                           self.badge_lbl.cget("font"), self.text_lbl.cget("font"),
                           self.badge_lbl.cget("fg"), self.text_lbl.cget("fg"),
                           self.body.winfo_width(), self.body.winfo_height(),
                           self.badge_lbl.winfo_height(), self.text_lbl.winfo_height())
                    if sig != self._overlay_sig:
                        self._overlay_sig = sig
                        canvas.delete("all")
                        self._draw_opaque_widgets(canvas, x, y)
        except tk.TclError:
            pass
        except Exception as e:
            debug_event("OVERLAY", "Overlay refresh failed", level="ERROR", error=repr(e))
        finally:
            if not self.stop_evt.is_set():
                self.root.after(120, self._refresh_opaque_overlay)

    def _draw_opaque_widgets(self, canvas, x, y):
        def widget_rect(widget):
            return (widget.winfo_rootx() - x, widget.winfo_rooty() - y,
                    widget.winfo_width(), widget.winfo_height())
        bx, by, bw, bh = widget_rect(self.body)
        if self.body.image is not None:
            canvas.create_image(bx + bw // 2, by + bh // 2,
                                image=self.body.image, anchor="center")
            canvas._image_ref = self.body.image
        else:
            canvas._image_ref = None
            placeholder = self.body.cget("text")
            if placeholder:
                canvas.create_text(bx + bw // 2, by + bh // 2,
                    text=placeholder, fill=self.body.cget("fg"),
                    font=self.body.cget("font"), anchor="center")
        tx, ty, tw, th = widget_rect(self.text_lbl)
        display_text = self.text_lbl.cget("text")
        if display_text:
            canvas.create_text(tx + 4, ty + th // 2,
                text=display_text, fill=self.text_lbl.cget("fg"),
                font=self.text_lbl.cget("font"), anchor="w", width=max(10, tw-8))
        cx, cy, cw, ch = widget_rect(self.badge_lbl)
        label = self.badge_lbl.cget("text")
        if label:
            canvas.create_text(cx + cw // 2, cy + ch // 2,
                text=label, fill=self.badge_lbl.cget("fg"),
                font=self.badge_lbl.cget("font"), anchor="center",
                width=max(10, cw-4))

    def apply_theme(self):
        light = self.cfg.get("theme") == "light"
        bg, bar, fg, field = ("#f2f4f7", "#dfe5ee", "#202938", "#ffffff") if light else ("#202020", "#303030", "#dddddd", "#101010")
        self.root.configure(bg=bg)
        self.content.configure(bg=bg)
        self.number_strip.configure(bg=field)
        for w in (self.body,):
            w.configure(bg=bg, fg=fg)
        for w in (self.text_lbl, self.badge_lbl):
            w.configure(bg=field)
        for w in (self.title_lbl, self.btn_close, self.btn_min, self.btn_lang, self.btn_menu):
            w.configure(bg=bar, fg=fg)
        self.grip.configure(bg=bar, fg=fg)
        self._update_work_indicator()
        for dialog in (self.history_win, self.editor, self.work_win):
            if dialog and dialog.winfo_exists():
                self._apply_dialog_theme(dialog)
        # Only the background HWND becomes semi-transparent.  The independent
        # color-keyed overlay restores photo / OCR number / rubber type to 100%.
        self.root.attributes("-alpha", max(0.35, min(1, self.cfg.get("transparency", 100) / 100)))
        debug_event("UI", "Theme applied", interval=3, theme=self.cfg.get("theme"), opacity=self.cfg.get("transparency"))

    def apply_font_sizes(self):
        sizes = self.cfg.get("font_sizes", {})
        def size(key, default):
            try: return max(7, min(42, int(sizes.get(key, default))))
            except (TypeError, ValueError): return default
        self.text_lbl.configure(font=("Consolas", size("number", 10)))
        self.badge_lbl.configure(font=("Segoe UI", size("type", 14), "bold"), height=1)
        base = size("interface", 9)
        # Do not touch self.title_lbl: SFC Solutions title is fixed.
        self.body.configure(font=("Segoe UI", base))
        for w in (self.btn_menu, self.btn_lang, self.btn_close, self.btn_min, self.grip):
            w.configure(font=("Segoe UI", base))
        self._apply_dialog_theme(self.root)
        self._update_work_indicator()
        for dialog in (self.history_win, self.editor, self.work_win):
            if dialog and dialog.winfo_exists():
                self._apply_dialog_theme(dialog)
        self._update_title()
        self._fit_type_area()

    def _fit_type_area(self, force=False):
        """Resize only when font or possible badge labels actually change.

        Frequent OCR frames MUST NOT trigger recursive Tk idle processing.
        """
        if self.collapsed or self._fit_area_busy:
            return
        try:
            font_name = str(self.badge_lbl.cget("font"))
            labels = [tr(self.lang, "type_none")]
            labels.extend(get_label(info, self.lang) for key, info in
                          self.cfg.get("number_lists", {}).items() if key != "none")
            labels.append(str(self.badge_lbl.cget("text") or ""))
            signature = (font_name, tuple(sorted(set(labels))), self.lang)
            if not force and signature == self._fit_area_signature:
                return
            self._fit_area_busy = True
            font = tkfont.Font(font=font_name)
            line_height = font.metrics("linespace")
            text_width = max((font.measure(str(v)) for v in labels if v), default=100)
            self.badge_lbl.configure(height=1, padx=6,
                                     pady=max(4, line_height // 6))
            badge_height = line_height + 2 * max(4, line_height // 6) + 8
            l, t, r, b = work_area()
            min_width = min(max(self.MIN_W, text_width + 22), max(self.MIN_W, r-l))
            min_height = min(max(self.MIN_H, self.TITLE_H + self.TEXT_H + badge_height + 85),
                             max(self.MIN_H, b-t))
            new_width = max(self.W, int(min_width))
            new_height = max(self.H, int(min_height))
            self._fit_area_signature = signature
            if (new_width, new_height) != (self.W, self.H):
                right = self.root.winfo_x() + self.root.winfo_width()
                bottom = self.root.winfo_y() + self.root.winfo_height()
                self.W, self.H = new_width, new_height
                new_x = max(l, min(right - self.W, r - self.W))
                new_y = max(t, min(bottom - self.H, b - self.H))
                self.root.geometry(f"{self.W}x{self.H}{new_x:+d}{new_y:+d}")
                self.text_lbl.configure(wraplength=0)
                self.img_cache.clear()
                self._image_request_id += 1
                self.current_file = object()
                # One deferred photo re-render, avoiding nested update_idletasks.
                self.root.after(40, lambda: self.redraw_result())
                debug_event("UI", "Type label resized", level="INFO", width=self.W, height=self.H)
        except (tk.TclError, ValueError) as exc:
            debug_event("UI", "Type label resize failed", level="ERROR", error=repr(exc))
        finally:
            self._fit_area_busy = False

    def open_settings(self):
        """Single settings page, no extra tabs; all widgets use shared theme."""
        debug_event("SETTINGS", "Settings opened", level="INFO")
        win = tk.Toplevel(self.root)
        win.title("SFC Solutions — Налаштування / Ustawienia")
        fit_dialog(win, 690, 680, 570, 560)
        win.resizable(False, False)
        win.attributes("-alpha", 1.0)
        win.transient(self.root)
        win.grab_set()
        frame = ttk.Frame(win, padding=20)
        frame.pack(fill="both", expand=True)
        ttk.Label(frame, text="Налаштування / Ustawienia", style="Heading.TLabel").pack(anchor="w", pady=(0, 16))
        light = tk.BooleanVar(value=self.cfg.get("theme") == "light")
        sound = tk.BooleanVar(value=self.cfg.get("sound_enabled", True))
        alpha = tk.IntVar(value=self.cfg.get("transparency", 100))
        sizes = self.cfg.get("font_sizes", {})
        number_size = tk.IntVar(value=sizes.get("number", 10))
        type_size = tk.IntVar(value=sizes.get("type", 14))
        ui_size = tk.IntVar(value=sizes.get("interface", 9))
        ttk.Checkbutton(frame, text="Світла тема / Jasny motyw", variable=light).pack(anchor="w", pady=5)
        ttk.Checkbutton(frame, text="Звуковий сигнал / Sygnał dźwiękowy", variable=sound).pack(anchor="w", pady=5)
        ttk.Label(frame, text="Видимість фону / Widoczność tła (%)").pack(anchor="w", pady=(14, 4))
        ttk.Scale(frame, from_=35, to=100, variable=alpha, orient="horizontal").pack(fill="x")
        ttk.Label(frame, text="Фото, номер та тип гуми — завжди 100% видимість.\nZdjęcie, numer i typ gumy — zawsze w pełni widoczne.").pack(anchor="w", pady=(5, 15))
        ttk.Label(frame, text="Розмір шрифтів / Rozmiar czcionek", style="Heading.TLabel").pack(anchor="w", pady=(2, 9))
        for name, variable in (("Номер гуми / Numer gumy", number_size),
                               ("Тип гуми / Typ gumy", type_size),
                               ("Інші елементи / Pozostałe elementy", ui_size)):
            row = ttk.Frame(frame)
            row.pack(fill="x", pady=5)
            ttk.Label(row, text=name).pack(side="left")
            ttk.Spinbox(row, from_=7, to=42, textvariable=variable, width=5).pack(side="right")
        ttk.Label(frame, text="SFC Solutions — статичний заголовок / stały nagłówek").pack(anchor="w", pady=(10, 0))
        buttons = ttk.Frame(frame)
        buttons.pack(fill="x", side="bottom", pady=(16, 0))
        def save():
            try:
                updated = {"number": max(7, min(42, int(number_size.get()))),
                           "type": max(7, min(42, int(type_size.get()))),
                           "interface": max(7, min(42, int(ui_size.get())))}
            except (ValueError, tk.TclError):
                messagebox.showwarning("SFC", "Некоректний розмір шрифту / Nieprawidłowy rozmiar", parent=win)
                return
            self.cfg["font_sizes"] = updated
            save_setting("font_sizes", updated)
            self.cfg["theme"] = "light" if light.get() else "dark"
            self.cfg["sound_enabled"] = bool(sound.get())
            self.cfg["transparency"] = int(alpha.get())
            for key in ("theme", "sound_enabled", "transparency"):
                save_setting(key, self.cfg[key])
            self.apply_theme()
            self.apply_font_sizes()
            debug_event("SETTINGS", "Settings saved", level="INFO", theme=self.cfg.get("theme"), opacity=self.cfg.get("transparency"), sizes=updated, sound=self.cfg.get("sound_enabled"))
            win.destroy()
        ttk.Button(buttons, text="Зберегти / Zapisz", command=save).pack(side="right")
        ttk.Button(buttons, text="Скасувати / Anuluj", command=win.destroy).pack(side="right", padx=8)
        self._apply_dialog_theme(win)

    def open_docs(self):
        win = tk.Toplevel(self.root)
        win.title("SFC Solutions — Інструкція / Instrukcja")
        fit_dialog(win, 820, 670, 620, 480)
        win.attributes("-alpha", 1.0)
        tabs = ttk.Notebook(win)
        tabs.pack(fill="both", expand=True)
        for lang, title in (("uk", "Українська"), ("pl", "Polski")):
            frame = ttk.Frame(tabs)
            tabs.add(frame, text=title)
            widget = tk.Text(frame, wrap="word", font=("Segoe UI", 11), padx=18, pady=15)
            widget.pack(fill="both", expand=True)
            widget.insert("1.0", DOC_UK if lang == "uk" else DOC_PL)
            widget.configure(state="disabled")
        self._apply_dialog_theme(win)

    def run(self):
        debug_event("APP", "Entering main event loop", level="INFO")
        self.root.mainloop()
        debug_event("APP", "Main event loop exited", level="INFO")


DOC_UK = """SFC Solutions — коротка інструкція

1. У меню виберіть «Папка з фото». Назви фото мають відповідати номерам гуми (наприклад 50123.jpg).
2. «Виділити область OCR» — обведіть поле, де інша програма показує введений номер.
3. «Область кліків» — обведіть кнопку підтвердження. Запис з'являється в історії тільки після кліку по цій області та якщо номер правильного формату.
4. «Редагування списків» — створіть Румунія, Селекція або власні списки, внесіть номери по одному на рядок, оберіть колір і збережіть.
5. Під час введення номера автоматично показується фото та кольорова назва списку. Якщо номер у списку, спрацьовує короткий сигнал.
6. «Історія номерів» — тільки поточна зміна, як локально, так і онлайн; інші зміни доступні лише на history_web.py. Зміни: 06–14, 14–22, 22–06. Нічна зміна належить даті її початку.
7. «Налаштування» — світла тема, звук, прозорість головного вікна. Вікно налаштувань завжди непрозоре.
8. Якщо є firebase-service-account.json та інтернет, історія і списки типів гум синхронізуються з іншими екземплярами програми приблизно кожні 8 секунд. Без інтернету записи залишаються локально.
9. Щоб область залишалася прив'язаною до іншої програми, виділіть її поверх цільового вікна. Позиція відстежується під час пересування вікна; при перезапуску Windows HWND може змінитися — виберіть область повторно. Скролінг сторінки всередині браузера не відстежується.
10. history_web.py відкриває окрему вебсторінку перегляду з фільтрами.
11. «Лист» — список потрібних гум, окремий від категорій. Зелений — номер у історії поточної зміни. Сірий — очікує. Обери рядок для прев’ю.
12. «Історія без фото» показує відсутні фотографії для відомих пар номер/код. «Конфлікти кодів» дозволяє обрати основний код (типово найновіший) та виправити альтернативні коди без зміни історії друку. Робочий лист та виправлення зберігаються локально.
"""
DOC_PL = """SFC Solutions — krótka instrukcja

1. W menu wybierz „Folder ze zdjęciami”. Nazwy plików muszą odpowiadać numerom gumy (np. 50123.jpg).
2. „Zaznacz obszar OCR” — wskaż pole, w którym drugi program wyświetla wpisany numer.
3. „Obszar kliknięć” — zaznacz przycisk zatwierdzający. Zapis powstaje tylko po kliknięciu w tym obszarze i dla poprawnego numeru.
4. „Edycja list” — dodaj Rumunia, Selekcja lub własne listy, wprowadź numery po jednym w wierszu, ustaw kolor i zapisz.
5. Po wpisaniu numeru aplikacja pokazuje zdjęcie i nazwę listy. Numer należący do listy wywołuje krótki sygnał.
6. „Historia numerów” — tylko aktualna zmiana lokalnie i online; pozostałe zmiany są dostępne tylko na stronie history_web.py. Zmiany: 06–14, 14–22, 22–06. Nocna zmiana należy do dnia jej rozpoczęcia.
7. „Ustawienia” — jasny motyw, dźwięk i przezroczystość głównego okna. Okno ustawień pozostaje nieprzezroczyste.
8. Z plikiem firebase-service-account.json i dostępem do Internetu historia oraz listy typów gumy synchronizują się z innymi kopiami mniej więcej co 8 sekund. Bez Internetu zapisy pozostają lokalne.
9. Aby obszar podążał za innym oknem, zaznacz go nad oknem docelowym. Po ponownym uruchomieniu Windows może być konieczne ponowne wskazanie obszaru. Przewijanie strony przeglądarki nie jest śledzone.
10. history_web.py uruchamia osobną stronę historii z filtrami.
11. „Lista” — niezależna lista robocza. Zielony — zapis w bieżącej zmianie, szary — oczekuje. Wybierz wiersz, aby zobaczyć zdjęcie.
12. „Historia bez zdjęć” pokazuje brakujące zdjęcia, a „Konflikty kodów” pozwalają wybrać kod główny (domyślnie najnowszy) i poprawić kody bez zmiany historii wydruków. Lista robocza i korekty są zapisywane lokalnie.
"""


def main():
    _start_console_logging()
    debug_event("START", "Dependencies", level="INFO", firebase_import=HAS_FIREBASE, firebase_error=FIREBASE_IMPORT_ERROR, pynput_import=HAS_PYNPUT, tesseract_present=os.path.isfile(TESS_EXE))
    cfg = load_config()
    lang = cfg.get("ui_language", "uk")
    if "--select" in sys.argv:
        select_region(lang)
        return
    set_dpi_aware()
    if not os.path.exists(TESS_EXE):
        print("Не знайдено", TESS_EXE)
    if not HAS_PYNPUT:
        print(tr(lang, "pynput_missing"))
    App(cfg).run()


if __name__ == "__main__":
    main()