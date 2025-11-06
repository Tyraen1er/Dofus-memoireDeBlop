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
    "capture_frames": 10,
    "capture_interval": 0.2,
    "animation_interval": 0.2,
    "max_capture_threads": 3,
    "canvas_horizontal_padding": 20,
    "canvas_vertical_padding": 40,
}

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

        self.sct = mss.mss()
        self.vmon = self.sct.monitors[0]
        self.pixel_ratio = self._detect_pixel_ratio()

        self.show_dofus_gate()
        self.root.protocol("WM_DELETE_WINDOW", self.on_quit)
        self.start_keyboard_listener()
        self.root.mainloop()

    def _clear_root_widgets(self):
        """Retire tout le contenu principal pour preparer une nouvelle vue."""
        for widget in self.root.winfo_children():
            widget.destroy()

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
        label = self.selector_var.get()
        entry = next((e for e in self.dofus_entries if e["label"] == label), None)
        if not entry:
            messagebox.showwarning("Sélection", "Veuillez choisir une fenêtre valide.")
            return
        self.target_hwnd = entry["hwnd"]
        self.target_window_title = entry["title"]
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
            command=self.enter_config_mode, font=("Arial", 10)
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

    def setup_start_ui(self):
        self.mode = "start"
        self._clear_root_widgets()
        scale = 0.25
        self._create_preview_container(scale)
        self._create_start_buttons()
        self._create_start_instruction()
        self._create_start_status()
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
        success = self.capture_target_window_image()
        if not success:
            messagebox.showwarning(
                "Capture",
                "Fenêtre Dofus introuvable, capture de l'écran complet utilisée."
            )
        if hasattr(self, "initial_img") and self.initial_img is not None:
            self.reference_img = self.initial_img.copy()
        else:
            self.reference_img = None
        if origin_mode == "config":
            self._next_point_index = 4
        self._enter_capture_mode()


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

    def enter_config_mode(self):
        self.mode = "config"
        self._next_point_index = 0
        self.points = self.load_points_from_ratios(self.default_ratios)
        if self.status is not None:
            self.status.config(text="Appuyez sur ESPACE ×4 pour redéfinir les coins.")

        self._clear_root_widgets()

        self.preview_label = tk.Label(self.root, bg="black")
        self.preview_label.pack(fill="both", expand=True)

        btn_frame = tk.Frame(self.root)
        btn_frame.pack(pady=10)
        tk.Button(btn_frame, text="🔄 Recharger par défaut", command=self.reload_default_for_config, font=("Arial", 10)).pack(side="left", padx=10)

        self.status = tk.Label(self.root, text="Appuyez sur ESPACE ×4 puis sur F1 pour lancer les captures.", font=("Arial", 10))
        self.status.pack(fill="x", pady=5)

        self._update_preview_image()
        self.root.after(100, self._place_config_window)

    def reload_default_for_config(self):
        self.points = self.load_points_from_ratios(self.default_ratios)
        self._next_point_index = 0
        if self.status is not None:
            self.status.config(text="Configuration réinitialisée. Appuyez sur ESPACE ×4 puis F1.")
        self._update_preview_image()

    def _enter_capture_mode(self):
        self.mode = "capture"
        self._clear_root_widgets()
        self._build_capture_controls()
        self._build_capture_status_label()
        self._build_capture_body()
        self._initialize_capture_state()

    def _build_capture_controls(self):
        """Cree la zone de saisie des parametres de grille."""
        top = tk.Frame(self.root)
        self.controls_frame = top
        top.pack(fill="x")
        tk.Label(top, text="n:", font=("Arial", 12, "bold")).pack(side="left")
        self.n_var = tk.StringVar(value=str(self.n))
        tk.Entry(top, textvariable=self.n_var, width=4).pack(side="left", padx=5)
        tk.Label(top, text="m:", font=("Arial", 12, "bold")).pack(side="left")
        self.m_var = tk.StringVar(value=str(self.m))
        tk.Entry(top, textvariable=self.m_var, width=4).pack(side="left", padx=5)
        tk.Label(top, text="Taille(px):", font=("Arial", 12, "bold")).pack(side="left")
        self.cell_var = tk.StringVar(value=str(self.cell))
        tk.Entry(top, textvariable=self.cell_var, width=6).pack(side="left", padx=5)
        tk.Button(top, text="Réinitialiser (R)", command=self.reset, font=("Arial", 10, "bold")).pack(side="right", padx=8, pady=4)

    def _build_capture_status_label(self):
        """Ajoute un rappel d etat pour le mode capture."""
        self.status = tk.Label(self.root, text="✅ Mode capture activé.", font=("Arial", 11))
        self.status.pack(fill="x", pady=3)

    def _build_capture_body(self):
        """Assemble la zone principale avec canvas et panneau lateral."""
        self.click_history.clear()
        if self.main_frame:
            self.main_frame.destroy()
        self.main_frame = tk.Frame(self.root)
        self.main_frame.pack(fill="both", expand=True)

        self.canvas = tk.Canvas(self.main_frame, bg="#111", highlightthickness=0)
        self.canvas.pack(side="left", fill="both", expand=True)

        self.side_panel = tk.Frame(self.main_frame, width=260, bg="#1b1b1b")
        self.side_panel.pack(side="right", fill="y")
        self.side_panel.pack_propagate(False)
        self._build_side_panel()

    def _initialize_capture_state(self):
        """Lance la logique de grille apres la creation des widgets."""
        self.read_params()
        c1, c2, c3, c4 = self.points
        self.grid = grid_intersections_in_quad(c1, c2, c3, c4, self.n, self.m)
        self.update_canvas_size()
        self.start_global_listener()
        self.root.after(100, self._place_memory_window)

    def _build_side_panel(self):
        if not self.side_panel:
            return
        for child in self.side_panel.winfo_children():
            child.destroy()
        tk.Label(
            self.side_panel,
            text="Aperçu des zones cliquées",
            fg="#f2f2f2",
            bg="#1b1b1b",
            font=("Arial", 11, "bold")
        ).pack(anchor="w", padx=8, pady=(10, 4))

        self.click_map_label = tk.Label(
            self.side_panel,
            bg="#1b1b1b",
            fg="#dddddd",
            text="Aucun clic pour l'instant",
            wraplength=210,
            justify="center"
        )
        self.click_map_label.pack(fill="x", padx=8, pady=(4, 10))

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
        try: self.n = max(1, int(self.n_var.get()))
        except: self.n = 3
        try: self.m = max(1, int(self.m_var.get()))
        except: self.m = 5
        try: self.cell = max(10, int(self.cell_var.get()))
        except: self.cell = 200

    def update_canvas_size(self):
        """Redimensionne la zone d affichage pour rester dans la limite de 35 pourcent de l ecran."""
        if not self.canvas:
            return
        self.read_params()
        self.root.update_idletasks()
        max_win_w, max_win_h = self._memory_window_limits()

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
        available_w = max(1, max_win_w - side_panel_w - horizontal_padding)
        available_h = max(1, max_win_h - controls_h - status_h - vertical_padding)

        width_based = max(1, available_w // max(1, (self.m + 1)))
        height_based = max(1, available_h // max(1, (self.n + 1)))
        self.display_cell = max(1, min(self.cell, width_based, height_based))

        canvas_w = self.display_cell * (self.m + 1)
        canvas_h = self.display_cell * (self.n + 1)
        self.canvas.config(width=canvas_w, height=canvas_h)
        self.canvas.configure(scrollregion=(0, 0, canvas_w, canvas_h))

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

    def reset(self):
        self.clear_click_history()
        for d in (self.tile_items, self.tile_border_items):
            for item in list(d.values()):
                self.canvas.delete(item)
            d.clear()
        self.tile_images.clear()
        if self.status:
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
                        self.reset()
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
        if not pressed or str(button) != "Button.left" or self.grid is None:
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
        if self.status:
            self.status.config(text=f"Capture en cours pour ({j},{i})…")
        if not hasattr(self, "capture_executor") or self.capture_executor is None:
            return
        try:
            self.capture_executor.submit(self._capture_sequence_for_tile, coord, monitor, px, py)
        except RuntimeError:
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

    def _select_most_different_frame(self, frames: List[Image.Image], monitor) -> Optional[Image.Image]:
        """Choisit l image la plus differente du reference screen."""
        if not frames:
            return None
        ref_crop = self._crop_reference_tile(monitor)
        if ref_crop is None:
            return frames[0]
        best_frame = frames[0]
        best_score = self._difference_score(best_frame, ref_crop)
        for frame in frames[1:]:
            score = self._difference_score(frame, ref_crop)
            if score > best_score:
                best_frame = frame
                best_score = score
        return best_frame

    def _capture_sequence_for_tile(self, coord, monitor, px, py):
        frames: List[Image.Image] = []
        local_sct = mss.mss()
        try:
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
        best_frame = self._select_most_different_frame(frames, monitor)
        if best_frame is None:
            return
        try:
            self.root.after(0, lambda: self._apply_tile_snapshot(coord, best_frame, px, py))
        except tk.TclError:
            return

    def _apply_tile_snapshot(self, coord, frame, px, py):
        if frame is None or not self.canvas:
            return
        j, i = coord
        display_size = max(1, int(self.display_cell))
        photo = ImageTk.PhotoImage(frame.resize((display_size, display_size), Image.LANCZOS))
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

        target_rect = getattr(self, "target_rect", (self.vmon["left"], self.vmon["top"], self.vmon["width"], self.vmon["height"]))
        rel_point = (int(px - target_rect[0]), int(py - target_rect[1]))
        snapshot_data = {
            "index": len(self.click_history) + 1,
            "coord": coord,
            "relative_point": rel_point,
            "timestamp": time.strftime("%H:%M:%S"),
            "frame": frame
        }
        self.click_history.append(snapshot_data)
        self.update_click_map_preview()
        if self.status:
            self.status.config(text=f"Snapshot retenu pour ({j},{i})")

if __name__ == "__main__":
    QuadGridNodesApp()
