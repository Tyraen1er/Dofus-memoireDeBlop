# -*- coding: utf-8 -*-
# === DPI AWARENESS - DOIT ETRE EN TOUT PREMIER ===
import ctypes
if hasattr(ctypes, "windll"):
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            try:
                ctypes.windll.user32.SetProcessDPIAware()
            except Exception:
                pass
# ================================================

import threading
import tkinter as tk
from tkinter import messagebox, ttk
from typing import Tuple, List, Optional, Dict
from concurrent.futures import ThreadPoolExecutor
from PIL import Image, ImageTk, ImageDraw, ImageChops, ImageStat
from pynput import mouse, keyboard
import mss
import ctypes as ct
from ctypes import wintypes
import time
import psutil
import sys
from pathlib import Path
import numpy as np
import cv2
try:
    import win32gui
    import win32process
except ImportError:
    win32gui = None
    win32process = None

Point = Tuple[float, float]

IS_WINDOWS = sys.platform.startswith("win")
IS_MAC = sys.platform == "darwin"
IS_LINUX = sys.platform.startswith("linux")

CONFIG = {
    "memory_window_ratio": 0.35,
    "capture_frames": 20,
    "capture_interval": 0.2,
    "animation_interval": 0.2,
    "max_capture_threads": 3,
    "canvas_horizontal_padding": 20,
    "canvas_vertical_padding": 40,
}

if CONFIG["capture_frames"] > 1:
    CONFIG["capture_interval"] = 1.0 / (CONFIG["capture_frames"] - 1)
else:
    CONFIG["capture_interval"] = 0.0

COLOR_HIST_BINS = 36

# === API Windows ===
if IS_WINDOWS and hasattr(ct, "windll"):
    try:
        user32 = ct.windll.user32
    except AttributeError:
        user32 = None
else:
    user32 = None

if IS_WINDOWS and hasattr(ct, "WINFUNCTYPE"):
    EnumWindowsProc = ct.WINFUNCTYPE(ct.c_bool, wintypes.HWND, wintypes.LPARAM)
else:
    EnumWindowsProc = None

class RECT(ct.Structure):
    _fields_ = [
        ("left", ct.c_long),
        ("top", ct.c_long),
        ("right", ct.c_long),
        ("bottom", ct.c_long)
    ]

def find_window_by_title(partial_title: str):
    if not IS_WINDOWS or user32 is None:
        return None
    hwnd = user32.GetTopWindow(None)
    while hwnd:
        length = user32.GetWindowTextLengthW(hwnd)
        if length > 0:
            buffer = ct.create_unicode_buffer(length + 1)
            user32.GetWindowTextW(hwnd, buffer, length + 1)
            if partial_title.lower() in buffer.value.lower():
                return hwnd
        hwnd = user32.GetWindow(hwnd, 2)
    return None

def get_window_rect(hwnd):
    if not IS_WINDOWS or user32 is None:
        return None
    rect = RECT()
    if user32.GetWindowRect(hwnd, ct.byref(rect)):
        return rect.left, rect.top, rect.right - rect.left, rect.bottom - rect.top
    return None

def get_work_area():
    if IS_WINDOWS and user32 is not None:
        try:
            rect = RECT()
            if user32.SystemParametersInfoW(0x0030, 0, ct.byref(rect), 0):
                return rect.left, rect.top, rect.right - rect.left, rect.bottom - rect.top
        except Exception:
            pass
    root = tk.Tk()
    root.withdraw()
    w, h = root.winfo_screenwidth(), root.winfo_screenheight()
    root.destroy()
    return 0, 0, w, h

def enumerate_windows_for_pids(pid_set: set) -> List[Tuple[int, str]]:
    if not IS_WINDOWS or win32process is None or win32gui is None or EnumWindowsProc is None or user32 is None:
        return []
    results: List[Tuple[int, str]] = []

    def _callback(hwnd, lparam):
        if not user32.IsWindowVisible(hwnd):
            return True
        _, pid = win32process.GetWindowThreadProcessId(hwnd)
        if pid not in pid_set:
            return True
        title = win32gui.GetWindowText(hwnd)
        if title and "release" in title.lower():
            results.append((hwnd, title.strip()))
        return True

    enum_cb = EnumWindowsProc(_callback)
    user32.EnumWindows(enum_cb, 0)
    return results

def focus_window(hwnd: int) -> bool:
    if not IS_WINDOWS or user32 is None or not hwnd:
        return False
    try:
        SW_RESTORE = 9
        user32.ShowWindow(hwnd, SW_RESTORE)
        user32.SetForegroundWindow(hwnd)
        return True
    except Exception:
        return False

# ------------------ Grille bilineaire ------------------
def grid_intersections_in_quad(c1, c2, c3, c4, n, m) -> List[List[Point]]:
    x1, y1 = map(float, c1)
    x2, y2 = map(float, c2)
    x3, y3 = map(float, c3)
    x4, y4 = map(float, c4)
    def bilinear(u: float, v: float) -> Point:
        return (
            (1 - u) * (1 - v) * x1 + u * (1 - v) * x2 + u * v * x3 + (1 - u) * v * x4,
            (1 - u) * (1 - v) * y1 + u * (1 - v) * y2 + u * v * y3 + (1 - u) * v * y4,
        )
    return [[bilinear(i / m, j / n) for i in range(m + 1)] for j in range(n + 1)]

def closest_point_with_indices(grid: List[List[Point]], target: Point):
    tx, ty = target
    best_pt, best_idx, best_d2 = None, (-1, -1), float("inf")
    for j, row in enumerate(grid):
        for i, (px, py) in enumerate(row):
            d2 = (px - tx) ** 2 + (py - ty) ** 2
            if d2 < best_d2:
                best_d2, best_pt, best_idx = d2, (px, py), (j, i)
    return best_pt, best_idx

# ------------------ Application principale ------------------
class QuadGridNodesApp:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("🧠 Memory Helper — Aide au jeu")
        self.root.wm_attributes("-topmost", True)

        self.mode = "start"
        self.points: List[Tuple[int, int]] = []
        self.default_ratios = [
            (0.5346, 0.2870),
            (0.7786, 0.5023),
            (0.6336, 0.6361),
            (0.3898, 0.4139)
        ]
        self.target_window_title = "Nodon"
        self.target_hwnd: Optional[int] = None
        self._next_point_index = 0
        self._quitting = False

        self.preview_label = None
        self.status = None
        self.n, self.m, self.cell = 3, 5, 200
        self.display_cell = self.cell
        self.tile_items = {}
        self.tile_images = {}
        self.tile_border_items = {}
        self.tile_frames = {}
        self.tile_text_items = {}
        self.tile_classification: Dict[Tuple[int, int], Dict[str, object]] = {}
        self.param_labels: Dict[str, tk.Label] = {}
        self._borderless = False
        self.last_click_point: Optional[Tuple[int, int]] = None
        self.grid: Optional[List[List[Point]]] = None
        self.debug_enabled = any(arg.lower() == "debug=true" for arg in sys.argv[1:])
        self.capture_executor = ThreadPoolExecutor(max_workers=CONFIG["max_capture_threads"])
        self.listener = None
        self.listener_lock = threading.Lock()
        self.click_history: List[Dict[str, object]] = []
        self.click_map_label = None
        self.side_panel = None
        self.main_frame = None
        self.controls_frame = None
        self.selector_var: Optional[tk.StringVar] = None
        self.dofus_entries: List[Dict[str, object]] = []
        self.reference_img: Optional[Image.Image] = None
        self._capture_start_pending = False
        self._f1_origin_mode: Optional[str] = None
        self._resize_job = None
        self._selection_pending = False
        self.snapshot_series_dir: Optional[Path] = None
        self.root_dir = Path(__file__).resolve().parent
        self.log_file_path = self.root_dir / "log.txt"
        self.log_file = None
        self.orb = None
        self.bf_matcher = None
        self.orb_references: List[Dict[str, object]] = []
        self.color_references: List[Dict[str, object]] = []

        self.sct = mss.mss()
        self.vmon = self.sct.monitors[0]
        self.pixel_ratio = self._detect_pixel_ratio()
        self._initialize_debug_logger()
        self._initialize_orb_pipeline()
        self._load_color_reference_library()

        self.show_dofus_gate()
        self.root.protocol("WM_DELETE_WINDOW", self.on_quit)
        self.root.bind("<Configure>", self._on_root_configure)
        self.start_keyboard_listener()
        self.root.mainloop()

    def _clear_root_widgets(self):
        """Retire tout le contenu principal pour preparer une nouvelle vue."""
        for widget in self.root.winfo_children():
            widget.destroy()

    def _set_borderless(self, enabled: bool):
        if self._borderless == enabled:
            return
        self._borderless = enabled
        try:
            self.root.overrideredirect(1 if enabled else 0)
            # Renforce le mode topmost après le changement de style de la fenêtre.
            self.root.wm_attributes("-topmost", True)
        except tk.TclError:
            pass

    def _initialize_debug_logger(self):
        if not self.debug_enabled:
            self.log_file = None
            return
        try:
            self.log_file_path.parent.mkdir(exist_ok=True)
            self.log_file = open(self.log_file_path, "a", encoding="utf-8")
            header = f"\n===== Session {time.strftime('%Y-%m-%d %H:%M:%S')} =====\n"
            self.log_file.write(header)
            self.log_file.flush()
        except Exception as exc:
            self.log_file = None
            print(f"[DEBUG] Impossible d'ouvrir {self.log_file_path}: {exc}")
            self.debug_enabled = False

    def _debug_log(self, message):
        if not self.debug_enabled:
            return
        try:
            if callable(message):
                message = message()
        except Exception:
            return
        if message is None:
            return
        entry = f"[{time.strftime('%H:%M:%S')}] {message}\n"
        if self.log_file:
            try:
                self.log_file.write(entry)
                self.log_file.flush()
                return
            except Exception:
                pass
        try:
            with self.log_file_path.open("a", encoding="utf-8") as fallback:
                fallback.write(entry)
        except Exception:
            pass

    def capture_target_window_image(self) -> bool:
        """Capture la fenetre cible et renvoie True si la fenetre Dofus est trouvee."""
        hwnd = self.target_hwnd or find_window_by_title(self.target_window_title)
        if hwnd:
            rect = get_window_rect(hwnd)
            if rect:
                x, y, w, h = rect
                monitor = {"top": y, "left": x, "width": w, "height": h}
                raw = self.sct.grab(monitor)
                self.initial_img = Image.frombytes("RGB", (raw.width, raw.height), raw.rgb)
                self.target_rect = (x, y, w, h)
                self.original_w, self.original_h = w, h
                self.target_hwnd = hwnd
                return True
        # Fallback : ecran entier
        raw = self.sct.grab(self.vmon)
        self.initial_img = Image.frombytes("RGB", (raw.width, raw.height), raw.rgb)
        self.target_rect = (self.vmon["left"], self.vmon["top"], self.vmon["width"], self.vmon["height"])
        self.original_w, self.original_h = self.vmon["width"], self.vmon["height"]
        return False

    def load_points_from_ratios(self, ratios):
        x, y, w, h = self.target_rect
        return [(int(x + rx * w), int(y + ry * h)) for (rx, ry) in ratios]

    def _detect_pixel_ratio(self) -> float:
        if not IS_MAC:
            return 1.0
        try:
            logical_w = max(1, int(self.root.winfo_screenwidth()))
            physical_w = int(self.vmon.get("width", logical_w))
            ratio = float(physical_w) / float(logical_w)
            if ratio < 1.0:
                ratio = 1.0
            return ratio
        except Exception:
            return 1.0

    def _logical_to_physical_point(self, point: Tuple[float, float]) -> Tuple[int, int]:
        x, y = point
        if self.pixel_ratio == 1.0:
            return int(round(x)), int(round(y))
        return int(round(x * self.pixel_ratio)), int(round(y * self.pixel_ratio))

    def scan_dofus_windows(self) -> List[Dict[str, object]]:
        entries: List[Dict[str, object]] = []
        if win32gui is None or win32process is None:
            return entries
        pid_set = set()
        for proc in psutil.process_iter(["pid", "name"]):
            try:
                name = (proc.info["name"] or "").lower()
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                continue
            if name == "dofus.exe":
                pid_set.add(proc.info["pid"])
                for child in proc.children(recursive=True):
                    pid_set.add(child.pid)
        if not pid_set:
            return entries
        seen = set()
        for hwnd, title in enumerate_windows_for_pids(pid_set):
            if hwnd in seen:
                continue
            seen.add(hwnd)
            rect = get_window_rect(hwnd)
            if not rect:
                continue
            entries.append({
                "hwnd": hwnd,
                "title": title,
                "rect": rect,
                "label": f"{title} — 0x{hwnd:08X}"
            })
        entries.sort(key=lambda e: e["title"].lower())
        return entries

    def _pywin32_ready(self) -> bool:
        """Indique si les dependances PyWin32 sont presentes."""
        return not (win32gui is None or win32process is None)

    def _prepare_gate_frame(self):
        """Construit le conteneur principal de la porte Dofus."""
        self._clear_root_widgets()
        gate_frame = tk.Frame(self.root, padx=20, pady=20)
        gate_frame.pack(fill="both", expand=True)
        return gate_frame

    def _render_gate_missing_pywin32(self, parent):
        """Affiche l aide lorsque PyWin32 manque."""
        tk.Label(
            parent,
            text="PyWin32 est requis pour détecter Dofus.",
            font=("Arial", 12, "bold")
        ).pack(pady=10)
        tk.Label(
            parent,
            text="Installez pywin32 puis relancez le programme.",
            font=("Arial", 10)
        ).pack(pady=5)
        tk.Button(parent, text="Fermer", command=self.on_quit).pack(pady=15)

    def _render_gate_selection(self, parent):
        """Affiche la liste des fenetres disponibles."""
        tk.Label(
            parent,
            text="Fenêtres Dofus détectées (Release)",
            font=("Arial", 12, "bold")
        ).pack(pady=(0, 10))
        self.selector_var = tk.StringVar(value=self.dofus_entries[0]["label"])
        combo = ttk.Combobox(
            parent,
            textvariable=self.selector_var,
            state="readonly",
            values=[entry["label"] for entry in self.dofus_entries]
        )
        combo.pack(fill="x", padx=10, pady=5)

        btn_frame = tk.Frame(parent)
        btn_frame.pack(pady=15)
        tk.Button(btn_frame, text="Valider", command=self.on_validate_dofus_selection).pack(side="left", padx=10)
        tk.Button(btn_frame, text="Fermer", command=self.on_quit).pack(side="right", padx=10)

    def _render_gate_retry_panel(self, parent):
        """Affiche les actions quand aucune fenetre n est detectee."""
        tk.Label(
            parent,
            text="Aucune fenêtre Dofus 'Release' détectée.",
            font=("Arial", 12, "bold")
        ).pack(pady=10)
        tk.Label(
            parent,
            text="Connectez-vous à Dofus puis cliquez sur Réessayer.",
            font=("Arial", 10)
        ).pack(pady=5)
        btn_frame = tk.Frame(parent)
        btn_frame.pack(pady=15)
        tk.Button(btn_frame, text="Réessayer", command=self.show_dofus_gate).pack(side="left", padx=10)
        tk.Button(btn_frame, text="Fermer", command=self.on_quit).pack(side="right", padx=10)

    def show_dofus_gate(self):
        self.mode = "gate"
        self._set_borderless(False)
        gate_frame = self._prepare_gate_frame()

        if not self._pywin32_ready():
            self._render_gate_missing_pywin32(gate_frame)
            return

        self.dofus_entries = self.scan_dofus_windows()
        if self.dofus_entries:
            self._render_gate_selection(gate_frame)
        else:
            self._render_gate_retry_panel(gate_frame)

    def on_validate_dofus_selection(self):
        if not self.dofus_entries or self.selector_var is None:
            return
        if self._selection_pending:
            return
        label = self.selector_var.get()
        entry = next((e for e in self.dofus_entries if e["label"] == label), None)
        if not entry:
            messagebox.showwarning("Sélection", "Veuillez choisir une fenêtre valide.")
            return
        self.target_hwnd = entry["hwnd"]
        self.target_window_title = entry["title"]
        focus_window(self.target_hwnd)
        self._selection_pending = True
        self.root.after(500, self._complete_selection_after_focus)

    def _complete_selection_after_focus(self):
        self._selection_pending = False
        if not self.capture_target_window_image():
            messagebox.showerror("Capture", "Impossible de capturer la fenêtre sélectionnée.")
            self.show_dofus_gate()
            return
        self.points = self.load_points_from_ratios(self.default_ratios)
        self.setup_start_ui()

    def _create_preview_container(self, scale: float):
        """Cree le conteneur visuel pour l apercu initial."""
        preview_w = int(self.original_w * scale)
        preview_h = int(self.original_h * scale)
        self.preview_frame = tk.Frame(self.root, width=preview_w, height=preview_h, bg="black")
        self.preview_frame.pack(pady=10)
        self.preview_frame.pack_propagate(False)
        self.preview_label = tk.Label(self.preview_frame, bg="black")
        self.preview_label.place(relx=0.5, rely=0.5, anchor="center")

    def _create_start_buttons(self):
        """Ajoute les boutons principaux de la page d accueil."""
        btn_frame = tk.Frame(self.root)
        btn_frame.pack(pady=10)
        tk.Button(
            btn_frame, text="🔧 Configurer les 4 points",
            command=lambda: self.enter_config_mode(), font=("Arial", 10)
        ).pack(side="left", padx=10)
        tk.Button(
            btn_frame, text="Nouv. aperçu",
            command=self.refresh_preview_capture, font=("Arial", 10)
        ).pack(side="left", padx=10)

    def _create_start_instruction(self):
        """Affiche un rappel sur la touche F1."""
        tk.Label(
            self.root,
            text="Presser F1 pour commencer le mini-jeu et les captures.",
            font=("Arial", 10, "italic")
        ).pack(pady=(0, 10))

    def _create_start_status(self):
        """Met en place le texte de statut initial."""
        self.status = tk.Label(
            self.root,
            text=f"Cible : '{self.target_window_title}'. Aperçu à 25%.",
            font=("Arial", 10)
        )
        self.status.pack(fill="x", pady=5)

    def setup_start_ui(self, preserve_points: bool = False):
        self.mode = "start"
        self._set_borderless(False)
        self.stop_global_listener()
        self._clear_root_widgets()
        self.controls_frame = None
        self.main_frame = None
        self.side_panel = None
        self.canvas = None
        self.click_map_label = None
        self.param_labels = {}
        self.last_click_point = None
        self.grid = None

        scale = 0.25
        self._create_preview_container(scale)
        self._create_start_buttons()
        self._create_start_instruction()
        self._create_start_status()
        if not preserve_points or len(self.points) != 4:
            self.points = self.load_points_from_ratios(self.default_ratios)
        self.root.after(50, self._update_preview_image)
        self.root.after(150, self._place_config_window)

    def refresh_preview_capture(self):
        """Reprend la capture de la fenetre cible pour mettre a jour l apercu."""
        success = self.capture_target_window_image()
        if not success:
            messagebox.showwarning(
                "Capture",
                "Impossible de retrouver la fenêtre sélectionnée, capture de l'écran complet utilisée."
            )

        if hasattr(self, "preview_frame") and self.preview_frame is not None:
            scale = 0.25
            self.preview_frame.config(
                width=int(self.original_w * scale),
                height=int(self.original_h * scale)
            )

        self._update_preview_image()
        if self.status is not None:
            self.status.config(text=f"Cible : '{self.target_window_title}'. Aperçu rafraîchi.")

    def on_f1(self, event=None):
        if self.mode == "capture":
            self.reset()
            self._prepare_snapshot_series_dir()
            self._capture_reference_board(warn_on_failure=True)
            if self.status:
                self.status.config(text="Snapshots effacés et référence rafraîchie (F1).")
            return
        if self._capture_start_pending:
            return
        if self.mode not in ("start", "config"):
            return
        if self.mode == "config" and self._next_point_index < 4:
            if self.status is not None:
                self.status.config(text="Définissez d'abord les 4 coins (ESPACE ×4) avant de presser F1.")
            return
        self._capture_start_pending = True
        self._f1_origin_mode = self.mode
        if self.status is not None:
            self.status.config(text="F1 détecté. Capture de référence dans 0.5s…")
        self.root.after(500, self._start_capture_after_f1)

    def _start_capture_after_f1(self):
        origin_mode = self._f1_origin_mode or "start"
        self._capture_start_pending = False
        self._f1_origin_mode = None
        if self._quitting:
            return
        self._capture_reference_board(warn_on_failure=True)
        if origin_mode == "config":
            self._next_point_index = 4
        self._prepare_snapshot_series_dir()
        self._enter_capture_mode()

    def _capture_reference_board(self, warn_on_failure: bool = False) -> bool:
        success = self.capture_target_window_image()
        if not success and warn_on_failure:
            messagebox.showwarning(
                "Capture",
                "Fenêtre Dofus introuvable, capture de l'écran complet utilisée."
            )
        if hasattr(self, "initial_img") and self.initial_img is not None:
            self.reference_img = self.initial_img.copy()
        else:
            self.reference_img = None
        return success


    def _update_preview_image(self):
        if not hasattr(self, 'initial_img') or self.initial_img is None:
            return

        scale = 0.25
        img_w, img_h = self.initial_img.size
        new_w = int(img_w * scale)
        new_h = int(img_h * scale)
        if new_w <= 0 or new_h <= 0:
            return

        resized = self.initial_img.copy().resize((new_w, new_h), Image.LANCZOS)
        draw = ImageDraw.Draw(resized)

        # Convertir les points absolus en coordonnees relatives a la fenetre cible
        x0, y0, _, _ = self.target_rect
        relative_points = [(px - x0, py - y0) for (px, py) in self.points]

        # Mettre a l echelle pour l apercu
        scaled_pts = [(int(rx * scale), int(ry * scale)) for (rx, ry) in relative_points]

        for i, (x, y) in enumerate(scaled_pts, 1):
            r = 4
            draw.ellipse((x - r, y - r, x + r, y + r), fill="yellow", outline="red", width=2)
            draw.text((x + r, y - r), str(i), fill="white")
        if len(scaled_pts) == 4:
            draw.polygon(scaled_pts, outline="red", width=2)

        if self.mode == "config" and self.last_click_point is not None:
            lx, ly = self.last_click_point
            rel_x = lx - x0
            rel_y = ly - y0
            if 0 <= rel_x <= img_w and 0 <= rel_y <= img_h:
                half = self.cell / 2.0
                left = (rel_x - half) * scale
                top = (rel_y - half) * scale
                right = (rel_x + half) * scale
                bottom = (rel_y + half) * scale
                left = max(0, min(new_w - 1, int(left)))
                top = max(0, min(new_h - 1, int(top)))
                right = max(left + 1, min(new_w, int(right)))
                bottom = max(top + 1, min(new_h, int(bottom)))
                draw.rectangle((left, top, right, bottom), outline="#00aaff", width=2)

        tk_img = ImageTk.PhotoImage(resized)
        self.preview_label.config(image=tk_img)
        self.preview_label.image = tk_img  # keep reference

    def _place_config_window(self):
        _, _, work_w, work_h = get_work_area()
        self.root.update_idletasks()
        win_w = self.root.winfo_width()
        win_h = self.root.winfo_height()
        # Verifier que la fenetre reste visible
        if win_w > work_w:
            win_w = work_w
        if win_h > work_h:
            win_h = work_h
        x = 0
        y = work_h - win_h
        if y < 0:
            y = 0
        self.root.geometry(f"{win_w}x{win_h}+{x}+{y}")

    def _memory_window_limits(self):
        _, _, work_w, work_h = get_work_area()
        ratio = CONFIG["memory_window_ratio"]
        max_w = max(1, int(work_w * ratio))
        max_h = max(1, int(work_h * ratio))
        return max_w, max_h

    def _place_memory_window(self):
        _, _, work_w, work_h = get_work_area()
        win_w, win_h = self._memory_window_limits()
        x = 0
        y = work_h - win_h
        if y < 0: y = 0
        self.root.geometry(f"{win_w}x{win_h}+{x}+{y}")

    def enter_config_mode(self, preserve_points: bool = False):
        self.mode = "config"
        self._set_borderless(False)
        if not preserve_points or len(self.points) != 4:
            self.points = self.load_points_from_ratios(self.default_ratios)
            self._next_point_index = 0
        else:
            self._next_point_index = 4
        if self.status is not None:
            if self._next_point_index < 4:
                self.status.config(text="Appuyez sur ESPACE ×4 pour redéfinir les coins.")
            else:
                self.status.config(text="Coins conservés. Pressez F1 pour relancer les captures.")

        self._clear_root_widgets()
        self.controls_frame = None
        self.main_frame = None
        self.side_panel = None
        self.canvas = None
        self.click_map_label = None
        self.param_labels = {}
        self.last_click_point = None
        self.grid = None

        ctrl_frame = tk.Frame(self.root)
        ctrl_frame.pack(pady=8)
        self._create_param_control(ctrl_frame, "n", "Lignes", step=1, minimum=1)
        self._create_param_control(ctrl_frame, "m", "Colonnes", step=1, minimum=1)
        self._create_param_control(ctrl_frame, "cell", "Taille (px)", step=10, minimum=30, maximum=600)

        self.preview_label = tk.Label(self.root, bg="black")
        self.preview_label.pack(fill="both", expand=True)
        self.preview_label.bind("<Button-1>", self._on_local_config_click)

        btn_frame = tk.Frame(self.root)
        btn_frame.pack(pady=10)
        tk.Button(
            btn_frame,
            text="Nouv. aperçu",
            command=self.refresh_preview_capture,
            font=("Arial", 10)
        ).pack(side="left", padx=10)
        tk.Button(btn_frame, text="🔄 Recharger par défaut", command=self.reload_default_for_config, font=("Arial", 10)).pack(side="left", padx=10)

        default_status = "Appuyez sur ESPACE ×4 puis sur F1 pour lancer les captures."
        if self._next_point_index >= 4:
            default_status = "Coins conservés. Pressez F1 pour relancer les captures."
        self.status = tk.Label(self.root, text=default_status, font=("Arial", 10))
        self.status.pack(fill="x", pady=5)

        self._update_preview_image()
        self.root.after(100, self._place_config_window)
        self.start_global_listener()

    def reload_default_for_config(self):
        self.points = self.load_points_from_ratios(self.default_ratios)
        self._next_point_index = 0
        self.last_click_point = None
        if self.status is not None:
            self.status.config(text="Configuration réinitialisée. Appuyez sur ESPACE ×4 puis F1.")
        self._update_preview_image()

    def _enter_capture_mode(self):
        self.mode = "capture"
        self._set_borderless(False)
        self.root.resizable(True, True)
        self._clear_root_widgets()
        self.controls_frame = None
        self.param_labels = {}
        self.status = None
        self._build_capture_body()
        self._initialize_capture_state()

    def _build_capture_body(self):
        """Assemble la zone principale avec canvas et panneau lateral."""
        self.click_history.clear()
        self.tile_classification.clear()
        self.tile_text_items.clear()
        self.tile_items.clear()
        self.tile_border_items.clear()
        self.tile_frames.clear()
        self.tile_images.clear()
        if self.main_frame:
            self.main_frame.destroy()
        self.main_frame = tk.Frame(self.root)
        self.main_frame.pack(fill="both", expand=True)

        self.canvas = tk.Canvas(self.main_frame, bg="#111", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)

        self.side_panel = None
        self.click_map_label = None

    def _initialize_capture_state(self):
        """Lance la logique de grille apres la creation des widgets."""
        self.read_params()
        c1, c2, c3, c4 = self.points
        self.grid = grid_intersections_in_quad(c1, c2, c3, c4, self.n, self.m)
        self.update_canvas_size()
        self.start_global_listener()
        self.root.after(100, self._place_memory_window)

    def clear_click_history(self):
        self.click_history.clear()
        if self.click_map_label:
            self.click_map_label.config(image="", text="Aucun clic pour l'instant")
            self.click_map_label.image = None

    def update_click_map_preview(self):
        if not self.click_map_label or not hasattr(self, "initial_img") or self.initial_img is None:
            return
        if not self.click_history:
            self.click_map_label.config(image="", text="Aucun clic pour l'instant")
            self.click_map_label.image = None
            return

        base = self.initial_img.copy()
        draw = ImageDraw.Draw(base)
        colors = ["#ff5252", "#ffa502", "#2ed573", "#1e90ff", "#a29bfe"]
        for idx, snapshot in enumerate(self.click_history, 1):
            rx, ry = snapshot.get("relative_point", (0, 0))
            color = colors[(idx - 1) % len(colors)]
            r = max(6, self.original_w // 80)
            draw.ellipse((rx - r, ry - r, rx + r, ry + r), outline=color, width=3)
            draw.text((rx + r + 2, ry - r), str(idx), fill=color)

        scale = min(0.4, max(0.15, 260 / max(self.original_w, self.original_h)))
        new_w = max(1, int(self.original_w * scale))
        new_h = max(1, int(self.original_h * scale))
        preview = base.resize((new_w, new_h), Image.LANCZOS)
        tk_img = ImageTk.PhotoImage(preview)
        self.click_map_label.config(image=tk_img, text="")
        self.click_map_label.image = tk_img

    def read_params(self):
        try:
            self.n = max(1, int(self.n))
        except Exception:
            self.n = 3
        try:
            self.m = max(1, int(self.m))
        except Exception:
            self.m = 5
        try:
            self.cell = max(10, int(self.cell))
        except Exception:
            self.cell = 200

    def update_canvas_size(self):
        """Adapte la zone d affichage a la taille courante de la fenetre."""
        if not self.canvas:
            return
        self.read_params()
        self.root.update_idletasks()
        win_w = max(1, self.root.winfo_width())
        win_h = max(1, self.root.winfo_height())
        if win_w <= 1 or win_h <= 1:
            win_w = max(1, self.root.winfo_reqwidth())
            win_h = max(1, self.root.winfo_reqheight())

        side_panel_w = 0
        if self.side_panel:
            side_panel_w = max(self.side_panel.winfo_width(), self.side_panel.winfo_reqwidth())
        controls_h = 0
        if self.controls_frame:
            controls_h = max(self.controls_frame.winfo_height(), self.controls_frame.winfo_reqheight())
        status_h = 0
        if self.status:
            status_h = max(self.status.winfo_height(), self.status.winfo_reqheight())

        horizontal_padding = CONFIG["canvas_horizontal_padding"]
        vertical_padding = CONFIG["canvas_vertical_padding"]
        available_w = max(1, win_w - side_panel_w - horizontal_padding)
        available_h = max(1, win_h - controls_h - status_h - vertical_padding)

        width_based = max(1, available_w // max(1, (self.m + 1)))
        height_based = max(1, available_h // max(1, (self.n + 1)))
        self.display_cell = max(1, min(self.cell, width_based, height_based))

        canvas_w = self.display_cell * (self.m + 1)
        canvas_h = self.display_cell * (self.n + 1)
        self.canvas.config(width=canvas_w, height=canvas_h)
        self.canvas.configure(scrollregion=(0, 0, canvas_w, canvas_h))
        self._redraw_tiles()

    def on_space(self, event=None):
        if self.mode != "config" or self._next_point_index >= 4:
            return
        coords = self._logical_to_physical_point((self.root.winfo_pointerx(), self.root.winfo_pointery()))
        self.points[self._next_point_index] = coords
        self._next_point_index += 1
        self._update_preview_image()
        if self._next_point_index < 4:
            self.status.config(text=f"Coin {self._next_point_index} défini. Encore {4 - self._next_point_index} × ESPACE…")
        else:
            self.status.config(text="✅ 4 coins définis. Pressez F1 pour démarrer les captures.")

    def reset(self, update_status: bool = True):
        self.clear_click_history()
        if self.canvas:
            for d in (self.tile_items, self.tile_border_items, self.tile_text_items):
                for item in list(d.values()):
                    self.canvas.delete(item)
                d.clear()
        else:
            self.tile_items.clear()
            self.tile_border_items.clear()
            self.tile_text_items.clear()
        self.tile_images.clear()
        self.tile_frames.clear()
        self.tile_classification.clear()
        if update_status and self.status:
            self.status.config(text="Snapshots effacés.")

    def start_keyboard_listener(self):
        def on_press(key):
            try:
                if key == keyboard.Key.esc:
                    self.on_quit()
                elif key == keyboard.Key.space:
                    self.on_space()
                elif key == keyboard.Key.f1:
                    self.on_f1()
                elif hasattr(key, "char") and key.char and key.char.lower() == "r":
                    if self.mode == "capture":
                        self.return_to_config_from_capture()
            except: pass
        listener = keyboard.Listener(on_press=on_press)
        listener.daemon = True
        listener.start()
        self.kb_listener = listener

    def on_quit(self):
        if self._quitting:
            return
        self._quitting = True
        self.stop_global_listener()
        if hasattr(self, "capture_executor") and self.capture_executor is not None:
            try:
                self.capture_executor.shutdown(wait=False, cancel_futures=True)
            except TypeError:
                self.capture_executor.shutdown(wait=False)
            self.capture_executor = None
        if getattr(self, "log_file", None):
            try:
                self.log_file.close()
            except Exception:
                pass
            self.log_file = None
        try: self.kb_listener.stop()
        except: pass
        self.root.destroy()

    def start_global_listener(self):
        with self.listener_lock:
            if self.listener: return
            self.listener = mouse.Listener(on_click=self.on_global_click)
            self.listener.daemon = True
            self.listener.start()

    def stop_global_listener(self):
        with self.listener_lock:
            if self.listener:
                try: self.listener.stop()
                except: pass
                self.listener = None

    def on_global_click(self, x, y, button, pressed):
        if not pressed or str(button) != "Button.left":
            return
        if self.mode == "config":
            self.root.after(0, lambda: self._record_config_click(x, y))
            return
        if self.grid is None:
            return
        self.root.after(200, lambda: self.update_tile_from_intersection(x, y))

    def update_tile_from_intersection(self, sx, sy):
        if self.grid is None:
            return
        sx, sy = self._logical_to_physical_point((sx, sy))
        (px, py), (j, i) = closest_point_with_indices(self.grid, (sx, sy))
        self.read_params()
        half = self.cell // 2
        monitor = {
            "left": int(px - half),
            "top": int(py - half),
            "width": self.cell,
            "height": self.cell
        }
        coord = (j, i)
        self._debug_log(lambda: f"[CAPTURE] Demande snapshot coord={coord} center=({px},{py}) monitor={monitor}")
        if self.status:
            self.status.config(text=f"Capture en cours pour ({j},{i})…")
        if not hasattr(self, "capture_executor") or self.capture_executor is None:
            return
        try:
            self.capture_executor.submit(self._capture_sequence_for_tile, coord, monitor, px, py)
        except RuntimeError:
            self._debug_log("[CAPTURE] Soumission thread impossible (RuntimeError)")
            pass

    def _crop_reference_tile(self, monitor) -> Optional[Image.Image]:
        """Extrait la zone de reference correspondant au snapshot."""
        if self.reference_img is None or not hasattr(self, "target_rect"):
            return None
        x0, y0, _, _ = self.target_rect
        left = int(monitor["left"] - x0)
        top = int(monitor["top"] - y0)
        right = left + monitor["width"]
        bottom = top + monitor["height"]
        img_w, img_h = self.reference_img.size
        if left < 0 or top < 0 or right > img_w or bottom > img_h:
            return None
        return self.reference_img.crop((left, top, right, bottom))

    def _difference_score(self, frame: Image.Image, reference: Image.Image) -> float:
        """Calcule l ecart moyen entre deux zones."""
        if frame.size != reference.size:
            reference = reference.resize(frame.size, Image.BILINEAR)
        diff = ImageChops.difference(frame, reference)
        stats = ImageStat.Stat(diff)
        frame_gray = frame.convert("L")
        ref_gray = reference.convert("L")
        brightness_diff = abs(ImageStat.Stat(frame_gray).mean[0] - ImageStat.Stat(ref_gray).mean[0])
        return sum(stats.mean) - brightness_diff * 1.5

    def _initialize_orb_pipeline(self):
        try:
            self.orb = cv2.ORB_create(nfeatures=500)
            self.bf_matcher = cv2.BFMatcher(cv2.NORM_HAMMING, crossCheck=True)
        except Exception as exc:
            self.orb = None
            self.bf_matcher = None
            self._debug_log(lambda: f"[ORB] Initialisation impossible: {exc}")
        self._load_orb_reference_library()

    def _load_orb_reference_library(self):
        self.orb_references = []
        if not self.orb:
            return
        ref_dir = self.root_dir / "Ref_blop"
        if not ref_dir.exists():
            return
        search_dirs = []
        taille_dir = ref_dir / "taille"
        if taille_dir.exists():
            search_dirs.append(taille_dir)
        else:
            search_dirs.append(ref_dir)
        for base_dir in search_dirs:
            for image_path in sorted(base_dir.glob("*")):
                if not image_path.suffix.lower() in {".png", ".jpg", ".jpeg", ".bmp"}:
                    continue
                try:
                    with Image.open(image_path) as img:
                        pil_img = img.convert("RGB")
                except Exception:
                    continue
                descriptors = self._compute_orb_descriptors(pil_img)
                if descriptors is None:
                    continue
                self.orb_references.append({
                    "name": image_path.stem,
                    "path": image_path,
                    "image": pil_img,
                    "descriptors": descriptors
                })
        self._debug_log(lambda: f"[ORB] Références chargées: {len(self.orb_references)}")

    def _load_color_reference_library(self):
        self.color_references = []
        color_dirs = []
        for base_name in ("Ref_blop", "Ref_clop"):
            candidate = self.root_dir / base_name / "couleur"
            if candidate.exists():
                color_dirs.append(candidate)
        if not color_dirs:
            return
        for color_dir in color_dirs:
            for image_path in sorted(color_dir.glob("*")):
                if image_path.suffix.lower() not in {".png", ".jpg", ".jpeg", ".bmp"}:
                    continue
                try:
                    with Image.open(image_path) as img:
                        rgba = img.convert("RGBA")
                except Exception:
                    continue
                hist = self._compute_reference_color_histogram(rgba)
                if hist is None:
                    continue
                normalized = self._normalize_color_label(image_path.stem)
                display = self._format_color_display(normalized or image_path.stem)
                letter = self._letter_for_color(normalized)
                self.color_references.append({
                    "name": image_path.stem,
                    "path": image_path,
                    "hist": hist,
                    "label": normalized,
                    "display": display,
                "letter": letter
            })
        self._debug_log(lambda: f"[COLOR] Références chargées: {len(self.color_references)}")

    def _compute_reference_color_histogram(self, image: Image.Image):
        if image is None:
            return None
        rgba = image.convert("RGBA")
        arr = np.array(rgba)
        if arr.size == 0:
            return None
        rgb = arr[..., :3]
        alpha = arr[..., 3]
        mask = alpha > 25
        return self._build_color_histogram_from_rgb(rgb, mask)

    def _build_color_histogram_from_rgb(self, rgb_array: np.ndarray, mask=None):
        if rgb_array.size == 0:
            return None
        hsv = cv2.cvtColor(rgb_array, cv2.COLOR_RGB2HSV)
        return self._build_hue_histogram_from_hsv(hsv, mask)

    def _build_hue_histogram_from_hsv(self, hsv_array: np.ndarray, mask=None):
        if hsv_array.size == 0:
            return None
        hue = hsv_array[..., 0]
        if mask is not None:
            mask_flat = mask.reshape(-1).astype(bool)
            hue_flat = hue.reshape(-1)
            if np.any(mask_flat):
                hue_values = hue_flat[mask_flat]
            else:
                hue_values = hue_flat
        else:
            hue_values = hue.reshape(-1)
        if hue_values.size == 0:
            hue_values = hue.reshape(-1)
        hist, _ = np.histogram(hue_values, bins=COLOR_HIST_BINS, range=(0, 180))
        hist = hist.astype(np.float32)
        total = hist.sum()
        if total > 0:
            hist /= total
        else:
            hist.fill(1.0 / COLOR_HIST_BINS)
        return hist

    def _compute_orb_descriptors(self, image: Image.Image) -> Optional[np.ndarray]:
        if not self.orb or image is None:
            return None
        try:
            rgb = image.convert("RGB")
            arr = np.array(rgb)
            gray = cv2.cvtColor(arr, cv2.COLOR_RGB2GRAY)
            _, descriptors = self.orb.detectAndCompute(gray, None)
            if descriptors is None or len(descriptors) == 0:
                return None
            return descriptors
        except Exception as exc:
            self._debug_log(lambda: f"[ORB] Extraction impossible: {exc}")
            return None

    def _orb_match_score(self, frame: Image.Image, reference):
        """Retourne un score de similarite ORB entre 0 et 1 (1 = meilleur match)."""
        if not self.bf_matcher:
            return None
        ref_image = reference
        ref_desc = None
        if isinstance(reference, dict):
            ref_desc = reference.get("descriptors")
            ref_image = reference.get("image")
        frame_desc = self._compute_orb_descriptors(frame)
        if frame_desc is None:
            return None
        if ref_desc is None:
            ref_desc = self._compute_orb_descriptors(ref_image)
        if ref_desc is None:
            return None
        try:
            matches = self.bf_matcher.match(frame_desc, ref_desc)
        except Exception as exc:
            self._debug_log(lambda: f"[ORB] BFMatcher erreur: {exc}")
            return None
        if not matches:
            return None
        avg_distance = sum(m.distance for m in matches) / (len(matches) * 256.0)
        overlap = len(matches) / max(len(frame_desc), len(ref_desc))
        score = max(0.0, min(1.0, overlap * (1.0 - avg_distance)))
        return score

    def _evaluate_orb_score_for_frame(self, frame: Image.Image):
        if not self.orb_references:
            return None, None
        best_score = None
        best_ref = None
        for ref_entry in self.orb_references:
            score = self._orb_match_score(frame, ref_entry)
            if score is None:
                continue
            if best_score is None or score > best_score:
                best_score = score
                best_ref = ref_entry
        return best_score, best_ref

    def _normalize_blop_label(self, raw_name: str) -> str:
        if not raw_name:
            return ""
        label = raw_name.lower()
        for prefix in ("ref_blop_", "ref_", "blop_"):
            if label.startswith(prefix):
                label = label[len(prefix):]
                break
        label = label.replace("blop", "")
        return label.strip("_- ")

    def _format_blop_display(self, label_key: str) -> str:
        if not label_key:
            return "Type inconnu"
        normalized = label_key.lower()
        mapping = {
            "grand": "Blop grand",
            "moyen": "Blop moyen",
            "petit": "Blop petit"
        }
        if normalized in mapping:
            return mapping[normalized]
        return f"Blop {label_key.capitalize()}"

    def _letter_for_label(self, label_key: str) -> str:
        if not label_key:
            return "?"
        normalized = label_key.lower()
        mapping = {"grand": "G", "moyen": "M", "petit": "P"}
        if normalized in mapping:
            return mapping[normalized]
        return label_key[:1].upper()

    def _normalize_color_label(self, raw_name: str) -> str:
        if not raw_name:
            return ""
        label = raw_name.lower()
        for prefix in ("ref_blop_", "ref_", "color_", "couleur_", "blop_"):
            if label.startswith(prefix):
                label = label[len(prefix):]
                break
        label = label.replace("couleur", "")
        label = label.strip("_- ")
        if "-" in label:
            label = label.split("-")[0]
        return label.strip("_- ")

    def _format_color_display(self, label_key: str) -> str:
        if not label_key:
            return "Couleur inconnue"
        normalized = label_key.lower()
        mapping = {
            "bleu": "Couleur Bleu Indigo",
            "rouge": "Couleur Rouge Griotte",
            "vert": "Couleur Vert Reinette",
            "jaune": "Couleur Jaune Coco"
        }
        if normalized in mapping:
            return mapping[normalized]
        return f"Couleur {label_key.replace('-', ' ').title()}"

    def _letter_for_color(self, label_key: str) -> str:
        if not label_key:
            return "?"
        normalized = label_key.lower()
        mapping = {"bleu": "B", "rouge": "R", "vert": "V", "jaune": "J"}
        if normalized in mapping:
            return mapping[normalized]
        return label_key[:1].upper()

    def _aggregate_classification_votes(self, frame_votes: List[Dict[str, object]]):
        if not frame_votes:
            return None
        totals: Dict[str, float] = {}
        for vote in frame_votes:
            label = str(vote.get("label", "")).strip().lower()
            if not label:
                continue
            score = float(vote.get("score", 0.0))
            totals[label] = totals.get(label, 0.0) + score
        if not totals:
            return None
        best_label, best_score = max(totals.items(), key=lambda item: item[1])
        total_score = sum(totals.values())
        confidence = best_score / total_score if total_score > 0 else 0.0
        return {
            "label": best_label,
            "display": self._format_blop_display(best_label),
            "letter": self._letter_for_label(best_label),
            "confidence": confidence,
            "votes": totals,
            "frame_votes": frame_votes,
            "total_score": total_score
        }

    def _compose_classification_result(self, size_data: Optional[Dict[str, object]], color_data: Optional[Dict[str, object]]):
        if not size_data and not color_data:
            return None
        combined: Dict[str, object] = dict(size_data) if size_data else {}
        if color_data:
            combined["color"] = color_data
            combined["color_score"] = color_data.get("score")
        size_letter = ""
        if size_data:
            size_letter = size_data.get("letter") or self._letter_for_label(size_data.get("label"))
        color_letter = color_data.get("letter") if color_data else ""
        letters = "".join(filter(None, [size_letter, color_letter]))
        if letters:
            combined["letter"] = letters
        display_parts: List[str] = []
        if size_data:
            display_parts.append(size_data.get("display") or self._format_blop_display(size_data.get("label")))
        if color_data:
            display_parts.append(color_data.get("display") or self._format_color_display(color_data.get("label")))
        if display_parts:
            combined["display"] = " — ".join(part for part in display_parts if part)
        elif size_data and size_data.get("display"):
            combined["display"] = size_data.get("display")
        elif color_data and color_data.get("display"):
            combined["display"] = color_data.get("display")
        return combined

    def _extract_frame_color_histogram(self, frame: Image.Image, reference: Optional[Image.Image] = None):
        if frame is None:
            return None
        rgb = np.array(frame.convert("RGB"))
        if rgb.size == 0:
            return None
        hsv = cv2.cvtColor(rgb, cv2.COLOR_RGB2HSV)
        sat_mask = hsv[..., 1] > 40
        val_mask = hsv[..., 2] > 50
        mask = sat_mask & val_mask
        if reference is not None:
            ref_rgb = np.array(reference.convert("RGB"))
            if ref_rgb.shape[:2] != rgb.shape[:2]:
                ref_rgb = cv2.resize(ref_rgb, (rgb.shape[1], rgb.shape[0]))
            diff = cv2.absdiff(rgb, ref_rgb)
            diff_gray = cv2.cvtColor(diff, cv2.COLOR_RGB2GRAY)
            diff_mask = diff_gray > 20
            if np.any(diff_mask):
                mask = mask & diff_mask
                if not np.any(mask):
                    mask = diff_mask
        hist = self._build_hue_histogram_from_hsv(hsv, mask)
        mask_size = mask.size if hasattr(mask, "size") else hsv[..., 0].size
        coverage = float(mask.sum()) / mask_size if mask_size else 0.0
        return {"hist": hist, "coverage": coverage}

    def _color_hist_similarity(self, hist_a, hist_b):
        if hist_a is None or hist_b is None:
            return 0.0
        a = np.asarray(hist_a, dtype=np.float32)
        b = np.asarray(hist_b, dtype=np.float32)
        if a.size == 0 or b.size == 0:
            return 0.0
        bc = float(np.sum(np.sqrt(np.clip(a, 0.0, 1.0) * np.clip(b, 0.0, 1.0))))
        return max(0.0, min(1.0, bc))

    def _classify_color_from_frame(self, frame: Image.Image, reference: Optional[Image.Image] = None):
        if not self.color_references:
            return None
        signature = self._extract_frame_color_histogram(frame, reference)
        if not signature:
            return None
        hist = signature.get("hist")
        if hist is None:
            return None
        best_entry = None
        best_score = -1.0
        for ref in self.color_references:
            score = self._color_hist_similarity(hist, ref.get("hist"))
            if score > best_score:
                best_score = score
                best_entry = ref
        if not best_entry:
            return None
        normalized = best_entry.get("label") or self._normalize_color_label(best_entry.get("name"))
        return {
            "label": normalized,
            "raw_label": best_entry.get("name"),
            "display": best_entry.get("display") or self._format_color_display(normalized),
            "letter": best_entry.get("letter") or self._letter_for_color(normalized),
            "score": best_score,
            "coverage": signature.get("coverage")
        }

    def _select_most_different_frame(self, frames: List[Image.Image], monitor):
        """Choisit la frame retenue et calcule le vote blop correspondant."""
        if not frames:
            return None, None
        self._debug_log(lambda: f"[CAPTURE] Sélection parmi {len(frames)} frames")
        best_frame = None
        best_orb_score = -1.0
        classification = None
        orb_enabled = bool(self.orb and self.bf_matcher and self.orb_references)
        ref_crop = self._crop_reference_tile(monitor)
        frame_votes: List[Dict[str, object]] = []
        if orb_enabled:
            for idx, frame in enumerate(frames):
                try:
                    score, ref_entry = self._evaluate_orb_score_for_frame(frame)
                except Exception as exc:
                    self._debug_log(lambda e=exc, i=idx: f"[ORB] Exception frame {i}: {e}")
                    score, ref_entry = None, None
                ref_name = ref_entry["name"] if ref_entry else "N/A"
                if score is not None:
                    self._debug_log(lambda s=score, n=ref_name, i=idx: f"[ORB] Frame {i} ↔ {n} => {s:.3f}")
                    normalized = self._normalize_blop_label(ref_name)
                    if normalized:
                        frame_votes.append({
                            "index": idx + 1,
                            "label": normalized,
                            "raw_label": ref_name,
                            "score": score
                        })
                    if score > best_orb_score:
                        best_orb_score = score
                        best_frame = frame
                else:
                    self._debug_log(lambda n=ref_name, i=idx: f"[ORB] Frame {i} ↔ {n} => score indisponible")
            classification = self._aggregate_classification_votes(frame_votes)
            if best_frame is not None:
                color_vote = self._classify_color_from_frame(best_frame, ref_crop)
                classification = self._compose_classification_result(classification, color_vote)
                self._debug_log(lambda: f"[CAPTURE] Frame retenue par ORB avec score {best_orb_score:.3f}")
                return best_frame, classification
            else:
                self._debug_log("[ORB] Aucun score valide, utilisation du fallback différentiel.")
        if ref_crop is None:
            self._debug_log("[CAPTURE] ref_crop introuvable, sélection default frame[0]")
            default_frame = frames[0]
            color_vote = self._classify_color_from_frame(default_frame, ref_crop)
            classification = self._compose_classification_result(classification, color_vote)
            return default_frame, classification
        best_frame = frames[0]
        best_score = self._difference_score(best_frame, ref_crop)
        for frame in frames[1:]:
            score = self._difference_score(frame, ref_crop)
            if score > best_score:
                best_frame = frame
                best_score = score
        self._debug_log(lambda: f"[CAPTURE] Frame retenue par fallback score={best_score:.2f}")
        color_vote = self._classify_color_from_frame(best_frame, ref_crop)
        classification = self._compose_classification_result(classification, color_vote)
        return best_frame, classification

    def _capture_sequence_for_tile(self, coord, monitor, px, py):
        frames: List[Image.Image] = []
        local_sct = mss.mss()
        self._debug_log(lambda: f"[CAPTURE] Thread démarré pour {coord}, monitor={monitor}")
        try:
            time.sleep(0.1)
            for idx in range(CONFIG["capture_frames"]):
                raw = local_sct.grab(monitor)
                img = Image.frombytes("RGB", (raw.width, raw.height), raw.rgb)
                frames.append(img.copy())
                if idx < CONFIG["capture_frames"] - 1:
                    time.sleep(CONFIG["capture_interval"])
        finally:
            try:
                local_sct.close()
            except Exception:
                pass
        best_frame, classification = self._select_most_different_frame(frames, monitor)
        if best_frame is None:
            self._debug_log(lambda: f"[CAPTURE] Aucune frame retenue pour {coord}")
            return
        try:
            self.root.after(0, lambda: self._apply_tile_snapshot(coord, best_frame, px, py, classification))
        except tk.TclError:
            self._debug_log(lambda: f"[CAPTURE] root.after échoue pour {coord}")
            return

    def _apply_tile_snapshot(self, coord, frame, px, py, classification=None):
        if frame is None or not self.canvas or self.mode != "capture":
            self._debug_log(lambda: f"[CAPTURE] _apply_tile_snapshot ignoré, frame/canvas/mode invalide pour {coord}")
            return
        j, i = coord
        snapshot_index = len(self.click_history) + 1
        self._persist_snapshot_image(frame, snapshot_index, j, i)
        self.tile_frames[coord] = frame.copy()
        if classification:
            self.tile_classification[coord] = classification
        elif coord in self.tile_classification:
            self.tile_classification.pop(coord, None)
        self._render_tile_image(coord, frame)
        self._debug_log(lambda: f"[CAPTURE] Snapshot appliqué coord={coord}, index={snapshot_index}")

        target_rect = getattr(self, "target_rect", (self.vmon["left"], self.vmon["top"], self.vmon["width"], self.vmon["height"]))
        rel_point = (int(px - target_rect[0]), int(py - target_rect[1]))
        snapshot_data = {
            "index": len(self.click_history) + 1,
            "coord": coord,
            "relative_point": rel_point,
            "timestamp": time.strftime("%H:%M:%S"),
            "frame": frame,
            "classification": classification
        }
        self.click_history.append(snapshot_data)
        self.update_click_map_preview()
        if self.status:
            status_msg = f"Snapshot retenu pour ({j},{i})"
            if classification and classification.get("display"):
                conf = classification.get("confidence")
                if conf is not None:
                    status_msg += f" — {classification['display']} ({conf * 100:.0f}%)"
                else:
                    status_msg += f" — {classification['display']}"
            self.status.config(text=status_msg)

    def _prepare_snapshot_series_dir(self):
        base_dir = self.root_dir / "snapshots"
        try:
            base_dir.mkdir(exist_ok=True)
        except Exception:
            pass
        timestamp = time.strftime("%Y%m%d-%H%M%S")
        series_dir = base_dir / timestamp
        suffix = 1
        while series_dir.exists():
            suffix += 1
            series_dir = base_dir / f"{timestamp}_{suffix:02d}"
        try:
            series_dir.mkdir(parents=True, exist_ok=False)
            self.snapshot_series_dir = series_dir
        except Exception as exc:
            self._debug_log(lambda: f"[Snapshots] Impossible de créer le dossier: {exc}")
            self.snapshot_series_dir = None

    def _persist_snapshot_image(self, frame: Image.Image, snapshot_index: int, row: int, col: int):
        if not self.snapshot_series_dir:
            return
        filename = f"{snapshot_index:02d}_r{row}_c{col}.png"
        path = self.snapshot_series_dir / filename
        try:
            frame.save(path)
        except Exception as exc:
            self._debug_log(lambda: f"[Snapshots] Sauvegarde impossible pour {path}: {exc}")

    def return_to_config_from_capture(self):
        if self.mode != "capture":
            return
        self.stop_global_listener()
        self.reset(update_status=False)
        self.enter_config_mode(preserve_points=True)

    def _record_config_click(self, x, y):
        if self.mode != "config":
            return
        px, py = self._logical_to_physical_point((x, y))
        self.last_click_point = (px, py)
        self._update_preview_image()

    def _on_local_config_click(self, event):
        if self.mode != "config":
            return
        self.last_click_point = self._logical_to_physical_point((event.x_root, event.y_root))
        self._update_preview_image()

    def _render_tile_image(self, coord, frame):
        if not self.canvas:
            return
        j, i = coord
        display_size = max(1, int(self.display_cell))
        resized = frame.resize((display_size, display_size), Image.LANCZOS)
        photo = ImageTk.PhotoImage(resized)
        self.tile_images[coord] = photo

        cx = i * self.display_cell + self.display_cell // 2
        cy = j * self.display_cell + self.display_cell // 2
        if coord in self.tile_items:
            self.canvas.coords(self.tile_items[coord], cx, cy)
            self.canvas.itemconfig(self.tile_items[coord], image=photo)
        else:
            self.tile_items[coord] = self.canvas.create_image(cx, cy, image=photo)

        rect_coords = (
            i * self.display_cell, j * self.display_cell,
            (i + 1) * self.display_cell, (j + 1) * self.display_cell,
        )
        if coord in self.tile_border_items:
            self.canvas.coords(self.tile_border_items[coord], *rect_coords)
        else:
            self.tile_border_items[coord] = self.canvas.create_rectangle(*rect_coords, outline="#ff3366", width=2)

        label_data = self.tile_classification.get(coord)
        existing_label_item = self.tile_text_items.get(coord)
        if label_data and self.canvas:
            label_text = label_data.get("letter") or self._letter_for_label(label_data.get("label"))
            label_text = (label_text or "").strip()
            if label_text:
                font_size = max(10, int(self.display_cell * 0.11))
                cx_label = i * self.display_cell + self.display_cell // 2
                cy_label = (j + 1) * self.display_cell - 6
                if existing_label_item:
                    self.canvas.coords(existing_label_item, cx_label, cy_label)
                    self.canvas.itemconfig(existing_label_item, text=label_text, font=("Arial", font_size, "bold"), fill="#000000")
                else:
                    self.tile_text_items[coord] = self.canvas.create_text(
                        cx_label,
                        cy_label,
                        text=label_text,
                        fill="#000000",
                        font=("Arial", font_size, "bold"),
                        anchor="s",
                        justify="center"
                    )
        elif existing_label_item:
            self.canvas.delete(existing_label_item)
            self.tile_text_items.pop(coord, None)

    def _redraw_tiles(self):
        if not self.canvas or not self.tile_frames:
            return
        for coord, frame in self.tile_frames.items():
            self._render_tile_image(coord, frame)

    def _create_param_control(self, parent, key, label_text, step=1, minimum=1, maximum=None):
        container = tk.Frame(parent)
        container.pack(side="left", padx=6, pady=4)
        tk.Label(container, text=label_text + " :", font=("Arial", 11, "bold")).pack(side="left", padx=(0, 4))
        tk.Button(
            container, text="-", width=2,
            command=lambda: self._adjust_param(key, -step, minimum, maximum)
        ).pack(side="left")
        value_label = tk.Label(container, text=str(getattr(self, key)), width=4, font=("Arial", 11))
        value_label.pack(side="left", padx=3)
        tk.Button(
            container, text="+", width=2,
            command=lambda: self._adjust_param(key, step, minimum, maximum)
        ).pack(side="left")
        self.param_labels[key] = value_label

    def _adjust_param(self, key, delta, minimum, maximum):
        current_value = getattr(self, key)
        new_value = current_value + delta
        if key == "cell":
            minimum = max(minimum, 10)
        if maximum is not None:
            new_value = max(minimum, min(new_value, maximum))
        else:
            new_value = max(minimum, new_value)
        if new_value == current_value:
            return
        setattr(self, key, new_value)
        self.read_params()
        self._refresh_param_label(key)
        if key in ("n", "m"):
            self._rebuild_grid()
        if self.mode == "capture":
            self.reset()
            if self.canvas:
                self.update_canvas_size()
            if self.status:
                labels = {"n": "n", "m": "m", "cell": "Taille (px)"}
                self.status.config(text=f"{labels.get(key, key)} = {new_value}. Snapshots effacés.")
        else:
            if key == "cell":
                self._update_preview_image()

    def _refresh_param_label(self, key):
        if key in self.param_labels:
            self.param_labels[key].config(text=str(getattr(self, key)))

    def _rebuild_grid(self):
        if len(self.points) == 4:
            c1, c2, c3, c4 = self.points
            self.grid = grid_intersections_in_quad(c1, c2, c3, c4, self.n, self.m)

    def _on_root_configure(self, event):
        if event.widget is not self.root or self.mode != "capture":
            return
        if self._resize_job is not None:
            self.root.after_cancel(self._resize_job)
        self._resize_job = self.root.after(120, self._apply_resize_update)

    def _apply_resize_update(self):
        self._resize_job = None
        self.update_canvas_size()

if __name__ == "__main__":
    QuadGridNodesApp()
