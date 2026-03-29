from __future__ import annotations

import json
import random
import sys
from dataclasses import dataclass
from datetime import date, datetime
from pathlib import Path

import imageio.v2 as imageio
import numpy as np
from PySide6.QtCore import QDate, QDateTime, QEasingCurve, QItemSelectionModel, QMimeData, QPointF, QRect, QRectF, QSize, Qt, QTimer, QVariantAnimation, Signal
from PySide6.QtGui import QColor, QDrag, QFont, QIcon, QImage, QImageReader, QKeySequence, QPainter, QPainterPath, QPalette, QPen, QPixmap, QPolygonF, QShortcut, QTransform
from PySide6.QtWidgets import (
    QAbstractSpinBox,
    QApplication,
    QComboBox,
    QColorDialog,
    QDateEdit,
    QDateTimeEdit,
    QDialog,
    QDialogButtonBox,
    QFileDialog,
    QFrame,
    QGraphicsDropShadowEffect,
    QHBoxLayout,
    QInputDialog,
    QLabel,
    QLineEdit,
    QListWidget,
    QListWidgetItem,
    QMainWindow,
    QMessageBox,
    QPushButton,
    QSizePolicy,
    QSlider,
    QSpinBox,
    QSplitter,
    QStatusBar,
    QToolButton,
    QProgressBar,
    QVBoxLayout,
    QWidget,
)


SUPPORTED_SUFFIXES = {".jpg", ".jpeg", ".png", ".bmp", ".gif", ".webp"}
THUMBNAIL_SIZE = QSize(136, 104)
DISPLAY_PRESETS = [
    ("Screen Fit", None),
    ("1280 x 720 (HD)", QSize(1280, 720)),
    ("1600 x 900", QSize(1600, 900)),
    ("1920 x 1080 (Full HD)", QSize(1920, 1080)),
    ("2560 x 1440 (QHD)", QSize(2560, 1440)),
    ("3840 x 2160 (4K)", QSize(3840, 2160)),
]
ASPECT_PRESETS = [
    ("16:9", (16, 9)),
    ("4:3", (4, 3)),
    ("3:2", (3, 2)),
    ("1:1", (1, 1)),
    ("9:16", (9, 16)),
    ("9:20", (9, 20)),
    ("9:21", (9, 21)),
    ("カスタム", "custom"),
]
TRANSITION_STYLE = "cross_dissolve"
TRANSITION_STYLES = [
    ("ランダム", "random"),
    ("クロスディゾルブ", "cross_dissolve"),
    ("スライド", "slide"),
    ("プッシュ", "push"),
    ("ワイプ", "wipe"),
    ("ホワイトアウト", "white_out"),
    ("ズームフェード", "zoom_fade"),
    ("カット", "cut"),
]

_RANDOM_BASE_POOL = ["cross_dissolve", "slide", "push", "wipe", "white_out", "zoom_fade"]
_RANDOM_DIRECTIONS = ["right", "left", "down", "up"]

DIRECTION_CHOICES = [
    ("ランダム", ""),
    ("➤ 右へ", "right"),
    ("◄ 左へ", "left"),
    ("▼ 下へ", "down"),
    ("▲ 上へ", "up"),
]

DIRECTIONAL_TRANSITIONS = {"slide", "push", "wipe"}
APP_STATE_FILE = "photo_app_state.json"
APP_BACKGROUND_COLOR = "#13131a"


TRANSITION_DURATION_MS_DEFAULT = 1200
PREVIEW_ZOOM_MIN = 0.10
PREVIEW_ZOOM_MAX = 1.00
PREVIEW_ZOOM_STEP = 0.01

DIRECTION_VECTORS = {
    "slide_right": QPointF(1.0, 0.0),
    "slide_left": QPointF(-1.0, 0.0),
    "slide_down": QPointF(0.0, 1.0),
    "slide_up": QPointF(0.0, -1.0),
    "push_right": QPointF(1.0, 0.0),
    "push_left": QPointF(-1.0, 0.0),
    "push_down": QPointF(0.0, 1.0),
    "push_up": QPointF(0.0, -1.0),
    "wipe_right": QPointF(1.0, 0.0),
    "wipe_left": QPointF(-1.0, 0.0),
    "wipe_down": QPointF(0.0, 1.0),
    "wipe_up": QPointF(0.0, -1.0),
}


def _normalize_rotation_quadrants(value: int) -> int:
    return value % 4


def _rotated_dimensions(width: int, height: int, rotation_quadrants: int) -> tuple[int, int]:
    if _normalize_rotation_quadrants(rotation_quadrants) % 2 == 1:
        return height, width
    return width, height


def _rotate_pixmap_quadrants(pixmap: QPixmap, rotation_quadrants: int) -> QPixmap:
    quadrants = _normalize_rotation_quadrants(rotation_quadrants)
    if quadrants == 0 or pixmap.isNull():
        return pixmap
    transform = QTransform()
    transform.rotate(90 * quadrants)
    return pixmap.transformed(transform, Qt.TransformationMode.SmoothTransformation)


@dataclass(slots=True)
class PhotoItem:
    path: Path
    width: int
    height: int
    modified_at: datetime
    transition_style: str = TRANSITION_STYLE
    transition_duration_ms: int = TRANSITION_DURATION_MS_DEFAULT
    rotation_quadrants: int = 0

    @property
    def display_width(self) -> int:
        return _rotated_dimensions(self.width, self.height, self.rotation_quadrants)[0]

    @property
    def display_height(self) -> int:
        return _rotated_dimensions(self.width, self.height, self.rotation_quadrants)[1]

    @property
    def orientation(self) -> str:
        return "Portrait" if self.display_height > self.display_width else "Landscape"

    @property
    def label(self) -> str:
        return self.path.stem.replace("_", " ").replace("-", " ").strip() or self.path.name


class PhotoCanvas(QWidget):
    def __init__(self) -> None:
        super().__init__()
        self._path: Path | None = None
        self._current_pixmap: QPixmap | None = None
        self._previous_pixmap: QPixmap | None = None
        self._previous_path: Path | None = None
        self._display_resolution: QSize | None = None
        self._display_aspect_ratio: tuple[int, int] | None = None
        self._playback_mode = False
        self._fade_zoom_enabled = False
        self._transition_style = TRANSITION_STYLE
        self._random_history: list[str] = []  # ランダム履歴
        self._random_deck: list[str] = []  # 現在のデッキ（残り）
        self._random_dir_history: list[QPointF] = []  # 方向ランダム履歴
        self._random_dir_str_history: list[str] = []  # トランジションランダム用方向履歴
        self._incoming_pan_start = QPointF(0.0, 0.0)
        self._incoming_pan_end = QPointF(0.0, 0.0)
        self._outgoing_pan_start = QPointF(0.0, 0.0)
        self._outgoing_pan_end = QPointF(0.0, 0.0)
        self._transition_direction = QPointF(1.0, 0.0)
        self._placeholder_text = "画像フォルダを開くと、ここに大きく表示されます"
        self._transition_value = 1.0
        self._manual_pan_by_path: dict[str, QPointF] = {}
        self._dragging_manual_pan = False
        self._drag_start_pos = QPointF(0.0, 0.0)
        self._drag_start_pan = QPointF(0.0, 0.0)
        self._preview_mode = False
        self._preview_completion_callback: callable | None = None
        self._preview_saved_display_resolution: QSize | None = None
        self._show_size_for_border: QSize | None = None
        self._screen_size_for_border: QSize | None = None
        self._manual_zoom_by_path: dict[str, float] = {}
        self._background_color = QColor("#13131a")
        self.setMinimumHeight(360)
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        self._transition = QVariantAnimation(self)
        self._transition.setDuration(520)
        self._transition.setStartValue(0.0)
        self._transition.setEndValue(1.0)
        self._transition.setEasingCurve(QEasingCurve.Type.Linear)
        self._transition.valueChanged.connect(self._on_transition_changed)
        self._transition.finished.connect(self._on_transition_finished)
        self._apply_canvas_style()

    def set_transition_duration_ms(self, duration_ms: int) -> None:
        """トランジション時間を設定（ミリ秒）。指定時間内に必ず完了する。"""
        self._transition.setDuration(max(0, duration_ms))

    def _on_transition_finished(self) -> None:
        """トランジション完了時の処理。プレビューモード完了を通知。"""
        if self._preview_mode and self._preview_completion_callback is not None:
            self._preview_completion_callback()
            self._preview_mode = False
            self._preview_completion_callback = None

    def set_fade_zoom_enabled(self, enabled: bool) -> None:
        self._fade_zoom_enabled = enabled
        self.update()

    def set_background_color(self, color: QColor) -> None:
        updated = QColor(color)
        updated.setAlpha(255)
        self._background_color = updated
        self._apply_canvas_style()
        self.update()

    def set_transition_style(self, style: str) -> None:
        if style == "random":
            style = self._pick_random_transition()
        self._transition_style = style
        if style in DIRECTION_VECTORS:
            self._transition_direction = DIRECTION_VECTORS[style]
        self.update()

    def _pick_random_transition(self) -> str:
        # デッキが空なら新しい周を開始
        if not self._random_deck:
            self._random_deck = _RANDOM_BASE_POOL[:]
            random.shuffle(self._random_deck)
        # 直近2回と同じベースを避けて選択
        recent = set(self._random_history[-2:])
        available = [b for b in self._random_deck if b not in recent]
        if not available:
            # デッキ残りが全て直近と被る場合はデッキをリセット
            self._random_deck = _RANDOM_BASE_POOL[:]
            random.shuffle(self._random_deck)
            available = [b for b in self._random_deck if b not in recent]
            if not available:
                available = self._random_deck[:]
        base = random.choice(available)
        self._random_deck.remove(base)
        if base in DIRECTIONAL_TRANSITIONS:
            dirs = _RANDOM_DIRECTIONS[:]
            recent_dirs = set(self._random_dir_str_history[-2:])
            filtered = [d for d in dirs if d not in recent_dirs]
            if not filtered:
                filtered = dirs
            direction = random.choice(filtered)
            self._random_dir_str_history.append(direction)
            if len(self._random_dir_str_history) > 10:
                self._random_dir_str_history = self._random_dir_str_history[-5:]
            result = f"{base}_{direction}"
        else:
            result = base
        self._random_history.append(base)
        if len(self._random_history) > 10:
            self._random_history = self._random_history[-5:]
        return result

    def preview_transition(self, next_pixmap: QPixmap | None = None, next_path: Path | None = None, completion_callback: callable | None = None) -> None:
        """トランジション選択時のプレビュー再生。次の写真へのトランジションを見せて、完了後に元に戻す。"""
        if self._current_pixmap is None or self._transition.duration() <= 0:
            return
        
        # 現在の写真を前の写真として保存
        self._previous_pixmap = self._current_pixmap
        self._previous_path = self._path
        
        # 次の写真を現在の写真として設定
        if next_pixmap is not None:
            self._current_pixmap = next_pixmap
            self._path = next_path
        
        self._preview_mode = True
        self._preview_completion_callback = completion_callback
        # プレビュー前の設定を保存
        self._preview_saved_display_resolution = self._display_resolution
        self._prepare_transition_motion()
        self._transition.stop()
        self._transition_value = 0.0
        self._transition.start()

    def restore_preview_display(self) -> None:
        """プレビュー前の設定を復元。"""
        self._display_resolution = self._preview_saved_display_resolution
        self._preview_saved_display_resolution = None

    def set_photo(self, path: Path | None, rotation_quadrants: int = 0, animate: bool = True) -> None:
        previous_path = self._path
        self._path = path
        if path is None:
            self._previous_pixmap = None
            self._previous_path = None
            self._current_pixmap = None
            self._reset_motion()
            self._placeholder_text = "表示できる画像がありません"
            self._transition.stop()
            self._transition_value = 1.0
            self._dragging_manual_pan = False
            self.update()
            return

        pixmap = _rotate_pixmap_quadrants(QPixmap(str(path)), rotation_quadrants)
        if pixmap.isNull():
            self._previous_pixmap = None
            self._previous_path = None
            self._current_pixmap = None
            self._reset_motion()
            self._placeholder_text = "この画像は読み込めませんでした"
            self._transition.stop()
            self._transition_value = 1.0
            self._dragging_manual_pan = False
            self.update()
            return

        self._placeholder_text = ""
        self._previous_pixmap = self._current_pixmap if animate else None
        self._previous_path = previous_path if self._previous_pixmap is not None else None
        self._current_pixmap = pixmap
        self._dragging_manual_pan = False
        self._transition.stop()
        if animate and self._previous_pixmap is not None and self._transition.duration() > 0:
            self._prepare_transition_motion()
            self._transition_value = 0.0
            self._transition.start()
        else:
            self._transition_value = 1.0
            self._previous_pixmap = None
            self._previous_path = None
            self._reset_motion()
            self.update()

    def resizeEvent(self, event) -> None:  # type: ignore[override]
        super().resizeEvent(event)
        self.update()

    def set_display_resolution(self, size: QSize | None) -> None:
        self._display_resolution = size
        self.update()

    def set_show_size_for_border(self, size: QSize | None) -> None:
        """ショーサイズ枠線とホワイトアウト範囲用のサイズを設定。"""
        self._show_size_for_border = size
        self.update()

    def set_screen_size_for_border(self, size: QSize | None) -> None:
        """画面サイズ枠線用のサイズを設定。"""
        self._screen_size_for_border = size
        self.update()

    def _show_size_bounds(self, base_bounds: QRectF | None = None) -> QRectF | None:
        """ショーサイズのアスペクト比で計算した表示領域を返す。"""
        if self._show_size_for_border is None or self._show_size_for_border.width() <= 0 or self._show_size_for_border.height() <= 0:
            return None
        available = base_bounds if base_bounds is not None else self._target_bounds()
        if available.width() <= 0 or available.height() <= 0:
            return None
        return self._fit_rect_to_ratio(
            available,
            self._show_size_for_border.width() / self._show_size_for_border.height(),
        )

    def _screen_size_bounds(self, base_bounds: QRectF | None = None) -> QRectF | None:
        """画面サイズ（解像度）のアスペクト比で計算した表示領域を返す。"""
        if self._screen_size_for_border is None or self._screen_size_for_border.width() <= 0 or self._screen_size_for_border.height() <= 0:
            return None
        available = base_bounds if base_bounds is not None else self._target_bounds()
        if available.width() <= 0 or available.height() <= 0:
            return None
        return self._fit_rect_to_ratio(
            available,
            self._screen_size_for_border.width() / self._screen_size_for_border.height(),
        )

    def set_display_aspect_ratio(self, ratio: tuple[int, int] | None) -> None:
        self._display_aspect_ratio = ratio
        self.update()

    def set_playback_mode(self, enabled: bool) -> None:
        self._playback_mode = enabled
        self._dragging_manual_pan = False
        self._apply_canvas_style()
        self.update()

    def set_manual_zoom_factor_for_path(self, photo_path: Path | str | None, zoom_factor: float) -> float:
        clamped_zoom = max(PREVIEW_ZOOM_MIN, min(PREVIEW_ZOOM_MAX, zoom_factor))
        if photo_path is not None:
            self._manual_zoom_by_path[str(photo_path)] = clamped_zoom
        self.update()
        return clamped_zoom

    def manual_zoom_factor_for_path(self, photo_path: Path | str | None) -> float:
        if photo_path is None:
            return 1.0
        return self._manual_zoom_by_path.get(str(photo_path), 1.0)

    def current_manual_zoom_factor(self) -> float:
        return self.manual_zoom_factor_for_path(self._path)

    def manual_zoom_state(self) -> dict[str, float]:
        return dict(self._manual_zoom_by_path)

    def set_manual_zoom_state(self, state: dict[str, float]) -> None:
        self._manual_zoom_by_path = {
            path: max(PREVIEW_ZOOM_MIN, min(PREVIEW_ZOOM_MAX, float(zoom_factor)))
            for path, zoom_factor in state.items()
        }
        self.update()

    def _display_zoom_factor_for_path(self, photo_path: Path | str | None) -> float:
        return self.manual_zoom_factor_for_path(photo_path)

    def manual_pan_state(self) -> dict[str, QPointF]:
        return {path: QPointF(offset.x(), offset.y()) for path, offset in self._manual_pan_by_path.items()}

    def set_manual_pan_state(self, state: dict[str, QPointF]) -> None:
        self._manual_pan_by_path = {path: QPointF(offset.x(), offset.y()) for path, offset in state.items()}
        self.update()

    def mousePressEvent(self, event) -> None:  # type: ignore[override]
        if event.button() != Qt.MouseButton.LeftButton:
            super().mousePressEvent(event)
            return

        if self._playback_mode:
            super().mousePressEvent(event)
            return

        if self._path is None or self._current_pixmap is None:
            super().mousePressEvent(event)
            return

        bounds = self._target_bounds()
        if not bounds.contains(event.position()):
            super().mousePressEvent(event)
            return

        self._dragging_manual_pan = True
        self._drag_start_pos = event.position()
        self._drag_start_pan = self._manual_pan_by_path.get(str(self._path), QPointF(0.0, 0.0))
        self.setCursor(Qt.CursorShape.ClosedHandCursor)
        event.accept()

    def mouseMoveEvent(self, event) -> None:  # type: ignore[override]
        if not self._dragging_manual_pan or self._path is None or self._current_pixmap is None:
            super().mouseMoveEvent(event)
            return

        bounds = self._target_bounds()
        if bounds.width() <= 0 or bounds.height() <= 0:
            super().mouseMoveEvent(event)
            return

        delta = event.position() - self._drag_start_pos
        candidate_pan = QPointF(
            self._drag_start_pan.x() + (delta.x() / bounds.width()),
            self._drag_start_pan.y() + (delta.y() / bounds.height()),
        )
        clamped_pan = self._clamp_manual_pan(candidate_pan, self._current_pixmap, bounds)
        self._manual_pan_by_path[str(self._path)] = clamped_pan
        self.update()
        event.accept()

    def mouseReleaseEvent(self, event) -> None:  # type: ignore[override]
        if event.button() == Qt.MouseButton.LeftButton and self._dragging_manual_pan:
            self._dragging_manual_pan = False
            self.unsetCursor()
            event.accept()
            return
        super().mouseReleaseEvent(event)

    def paintEvent(self, event) -> None:  # type: ignore[override]
        super().paintEvent(event)

        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)

        bounds = self._target_bounds()
        if bounds.width() <= 0 or bounds.height() <= 0:
            return

        canvas_bounds = self._screen_size_bounds(bounds)
        if canvas_bounds is None:
            canvas_bounds = bounds

        painter.save()
        painter.fillRect(canvas_bounds, self._background_color)
        painter.restore()

        if self._current_pixmap is None:
            painter.setPen(QColor(73, 56, 35, 180))
            painter.setFont(QFont("Yu Gothic UI", 15))
            painter.drawText(bounds, Qt.AlignmentFlag.AlignCenter | Qt.TextFlag.TextWordWrap, self._placeholder_text)
            return

        painter.save()
        painter.setClipRect(bounds)
        timeline_progress = self._timeline_progress()
        fade_progress = self._crossfade_progress(timeline_progress)
        zoom_progress = self._zoom_progress(timeline_progress)
        if self._previous_pixmap is None:
            self._draw_pixmap(
                painter,
                self._current_pixmap,
                bounds,
                self._incoming_zoom_factor(zoom_progress),
                self._interpolate_pan(self._incoming_pan_start, self._incoming_pan_end, timeline_progress),
                self._path,
            )
        elif self._transition_style == "slide" or self._transition_style.startswith("slide_"):
            self._paint_slide_transition(painter, bounds, timeline_progress, zoom_progress)
        elif self._transition_style == "push" or self._transition_style.startswith("push_"):
            self._paint_push_transition(painter, bounds, timeline_progress, zoom_progress)
        elif self._transition_style.startswith("wipe"):
            self._paint_wipe_transition(painter, bounds, timeline_progress, zoom_progress)
        elif self._transition_style == "white_out":
            self._paint_white_out_transition(painter, bounds, fade_progress, zoom_progress)
        elif self._transition_style == "zoom_fade":
            self._paint_zoom_fade_transition(painter, bounds, timeline_progress, fade_progress)
        elif self._transition_style == "cut":
            # カット: 即座に次の写真を表示
            self._draw_pixmap(
                painter,
                self._current_pixmap,
                bounds,
                self._incoming_zoom_factor(zoom_progress),
                self._interpolate_pan(self._incoming_pan_start, self._incoming_pan_end, timeline_progress),
                self._path,
            )
        else:
            self._paint_cross_dissolve_transition(painter, bounds, timeline_progress, fade_progress, zoom_progress)

        painter.setOpacity(1.0)
        painter.restore()

        if self._current_pixmap is not None and canvas_bounds != bounds:
            painter.save()
            self._fill_outside_rect(painter, bounds, canvas_bounds, QColor(APP_BACKGROUND_COLOR))
            painter.restore()

        # マスク外を背景色で塗りつぶし（最上位レイヤー）
        show_bounds = self._show_size_bounds(bounds)
        if show_bounds is not None and self._current_pixmap is not None:
            painter.save()
            self._fill_outside_rect(painter, canvas_bounds, show_bounds, QColor("#000000"))
            painter.restore()

        if not self._playback_mode:
            # ショーサイズの枠線を常時表示（黄色破線）
            show_bounds = self._show_size_bounds(bounds)
            if show_bounds is not None and self._current_pixmap is not None:
                painter.save()
                pen = QPen(QColor(255, 200, 0, 200))
                pen.setWidth(2)
                pen.setStyle(Qt.PenStyle.DashLine)
                painter.setPen(pen)
                painter.drawRect(show_bounds)
                painter.restore()

            # 画面サイズの枠線を常時表示（赤色破線）
            screen_bounds = self._screen_size_bounds(bounds)
            if screen_bounds is not None and self._current_pixmap is not None:
                painter.save()
                pen = QPen(QColor(255, 60, 60, 200))
                pen.setWidth(2)
                pen.setStyle(Qt.PenStyle.DashLine)
                painter.setPen(pen)
                painter.drawRect(screen_bounds)
                painter.restore()

    def _paint_cross_dissolve_transition(
        self,
        painter: QPainter,
        bounds: QRectF,
        timeline_progress: float,
        fade_progress: float,
        zoom_progress: float,
    ) -> None:
        if self._is_plain_crossfade_mode():
            painter.setOpacity(1.0 - fade_progress)
            self._draw_pixmap(painter, self._previous_pixmap, bounds, 1.0, QPointF(0.0, 0.0), self._previous_path)
            painter.setOpacity(fade_progress)
            self._draw_pixmap(painter, self._current_pixmap, bounds, 1.0, QPointF(0.0, 0.0), self._path)
            return

        painter.setOpacity(self._outgoing_opacity(fade_progress))
        outgoing_pan = self._interpolate_pan(self._outgoing_pan_start, self._outgoing_pan_end, timeline_progress)
        self._draw_pixmap(
            painter,
            self._previous_pixmap,
            bounds,
            self._outgoing_zoom_factor(zoom_progress),
            outgoing_pan,
            self._previous_path,
        )

        incoming_pan = self._interpolate_pan(self._incoming_pan_start, self._incoming_pan_end, timeline_progress)
        painter.setOpacity(self._incoming_opacity(fade_progress))
        self._draw_pixmap(
            painter,
            self._current_pixmap,
            bounds,
            self._incoming_zoom_factor(zoom_progress),
            incoming_pan,
            self._path,
        )

    def _is_plain_crossfade_mode(self) -> bool:
        return self._transition_style == "cross_dissolve" and not self._fade_zoom_enabled

    def _paint_slide_transition(
        self,
        painter: QPainter,
        bounds: QRectF,
        timeline_progress: float,
        zoom_progress: float,
    ) -> None:
        direction = self._transition_direction
        eased = self._easing_in_out_cubic(timeline_progress)
        # マスク境界を基準に開始位置を決める（方向はゴール=出ていく方向）
        show_bounds = self._show_size_bounds(bounds)
        clip = show_bounds if show_bounds is not None else bounds
        incoming_left = bounds.left()
        incoming_top = bounds.top()
        if direction.x() > 0:
            start_left = clip.left() - bounds.width()
            incoming_left = start_left + (bounds.left() - start_left) * eased
        elif direction.x() < 0:
            start_left = clip.right()
            incoming_left = start_left + (bounds.left() - start_left) * eased
        if direction.y() > 0:
            start_top = clip.top() - bounds.height()
            incoming_top = start_top + (bounds.top() - start_top) * eased
        elif direction.y() < 0:
            start_top = clip.bottom()
            incoming_top = start_top + (bounds.top() - start_top) * eased

        # 前の写真: そのままの位置に描画
        self._draw_pixmap(
            painter,
            self._previous_pixmap,
            bounds,
            self._outgoing_zoom_factor(zoom_progress),
            self._interpolate_pan(self._outgoing_pan_start, self._outgoing_pan_end, timeline_progress),
            self._previous_path,
        )

        # 次の写真: マスク端からスライドイン
        painter.save()
        painter.setClipRect(clip)
        shifted_bounds = QRectF(incoming_left, incoming_top, bounds.width(), bounds.height())
        self._draw_pixmap(
            painter,
            self._current_pixmap,
            shifted_bounds,
            self._incoming_zoom_factor(zoom_progress),
            self._interpolate_pan(self._incoming_pan_start, self._incoming_pan_end, timeline_progress),
            self._path,
        )
        painter.restore()

    def _paint_push_transition(
        self,
        painter: QPainter,
        bounds: QRectF,
        timeline_progress: float,
        zoom_progress: float,
    ) -> None:
        direction = self._transition_direction
        eased = self._easing_in_out_cubic(timeline_progress)
        # マスク境界を基準に開始位置と終了位置を決める（方向はゴール=出ていく方向）
        show_bounds = self._show_size_bounds(bounds)
        clip = show_bounds if show_bounds is not None else bounds
        out_left = bounds.left()
        out_top = bounds.top()
        in_left = bounds.left()
        in_top = bounds.top()
        if direction.x() > 0:
            out_end_left = clip.right()
            in_start_left = clip.left() - bounds.width()
            out_left = bounds.left() + (out_end_left - bounds.left()) * eased
            in_left = in_start_left + (bounds.left() - in_start_left) * eased
        elif direction.x() < 0:
            out_end_left = clip.left() - bounds.width()
            in_start_left = clip.right()
            out_left = bounds.left() + (out_end_left - bounds.left()) * eased
            in_left = in_start_left + (bounds.left() - in_start_left) * eased
        if direction.y() > 0:
            out_end_top = clip.bottom()
            in_start_top = clip.top() - bounds.height()
            out_top = bounds.top() + (out_end_top - bounds.top()) * eased
            in_top = in_start_top + (bounds.top() - in_start_top) * eased
        elif direction.y() < 0:
            out_end_top = clip.top() - bounds.height()
            in_start_top = clip.bottom()
            out_top = bounds.top() + (out_end_top - bounds.top()) * eased
            in_top = in_start_top + (bounds.top() - in_start_top) * eased

        painter.save()
        painter.setClipRect(clip)

        out_bounds = QRectF(out_left, out_top, bounds.width(), bounds.height())
        self._draw_pixmap(
            painter,
            self._previous_pixmap,
            out_bounds,
            self._outgoing_zoom_factor(zoom_progress),
            self._interpolate_pan(self._outgoing_pan_start, self._outgoing_pan_end, timeline_progress),
            self._previous_path,
        )

        in_bounds = QRectF(in_left, in_top, bounds.width(), bounds.height())
        self._draw_pixmap(
            painter,
            self._current_pixmap,
            in_bounds,
            1.0,
            QPointF(0.0, 0.0),
            self._path,
        )
        painter.restore()

    def _paint_wipe_transition(
        self,
        painter: QPainter,
        bounds: QRectF,
        timeline_progress: float,
        zoom_progress: float,
    ) -> None:
        eased_progress = self._easing_in_out_cubic(timeline_progress)
        self._draw_pixmap(
            painter,
            self._previous_pixmap,
            bounds,
            1.0,
            QPointF(0.0, 0.0),
            self._previous_path,
        )

        direction = self._transition_direction
        dx = direction.x()
        dy = direction.y()
        is_diagonal = abs(dx) > 0 and abs(dy) > 0

        painter.save()
        if is_diagonal:
            # 斜め45度: 斜線がスイープするワイプ
            corners = [
                QPointF(bounds.left(), bounds.top()),
                QPointF(bounds.right(), bounds.top()),
                QPointF(bounds.right(), bounds.bottom()),
                QPointF(bounds.left(), bounds.bottom()),
            ]
            projections = [dx * c.x() + dy * c.y() for c in corners]
            min_proj = min(projections)
            max_proj = max(projections)
            threshold = min_proj + eased_progress * (max_proj - min_proj)
            # Sutherland-Hodgman: 半平面 dx*x+dy*y <= threshold で矩形をクリップ
            clipped: list[QPointF] = []
            n = len(corners)
            for i in range(n):
                curr = corners[i]
                nxt = corners[(i + 1) % n]
                cp = projections[i]
                np_ = projections[(i + 1) % n]
                if cp <= threshold:
                    clipped.append(curr)
                if (cp <= threshold) != (np_ <= threshold):
                    t = (threshold - cp) / (np_ - cp)
                    clipped.append(QPointF(
                        curr.x() + t * (nxt.x() - curr.x()),
                        curr.y() + t * (nxt.y() - curr.y()),
                    ))
            clip_path = QPainterPath()
            if clipped:
                clip_path.addPolygon(QPolygonF(clipped))
                clip_path.closeSubpath()
            painter.setClipPath(clip_path)
        elif abs(dx) >= abs(dy):
            # 横ワイプ: クロップ幅に合わせる
            show_bounds = self._show_size_bounds(bounds)
            ref = show_bounds if show_bounds is not None else bounds
            width = ref.width() * eased_progress
            if dx > 0:
                clip_rect = QRectF(ref.left(), bounds.top(), width, bounds.height())
            else:
                clip_rect = QRectF(ref.right() - width, bounds.top(), width, bounds.height())
            painter.setClipRect(clip_rect)
        else:
            # 縦ワイプ: クロップ高さに合わせる
            show_bounds = self._show_size_bounds(bounds)
            ref = show_bounds if show_bounds is not None else bounds
            height = ref.height() * eased_progress
            if dy > 0:
                clip_rect = QRectF(bounds.left(), ref.top(), bounds.width(), height)
            else:
                clip_rect = QRectF(bounds.left(), ref.bottom() - height, bounds.width(), height)
            painter.setClipRect(clip_rect)
        self._draw_pixmap(
            painter,
            self._current_pixmap,
            bounds,
            1.0,
            QPointF(0.0, 0.0),
            self._path,
        )
        painter.restore()

    def _paint_zoom_fade_transition(
        self,
        painter: QPainter,
        bounds: QRectF,
        timeline_progress: float,
        fade_progress: float,
    ) -> None:
        # ズームは全期間、フェードは100ms遅延して開始しトランジション終了まで
        duration_ms = max(1, self._transition.duration())
        delay = min(100.0 / duration_ms, 0.9)
        if fade_progress <= delay:
            fade_t = 0.0
        else:
            fade_t = min(1.0, (fade_progress - delay) / (1.0 - delay))

        zoom_eased = fade_progress ** 2
        out_scale = 1.0 + 0.15 * zoom_eased

        # 前の写真: ズームイン + フェードアウト
        painter.setOpacity(1.0 - fade_t)
        self._draw_pixmap(
            painter, self._previous_pixmap, bounds, out_scale,
            self._interpolate_pan(self._outgoing_pan_start, self._outgoing_pan_end, timeline_progress),
            self._previous_path,
        )

        # 次の写真: 通常スケールでフェードイン
        painter.setOpacity(fade_t)
        self._draw_pixmap(
            painter, self._current_pixmap, bounds, 1.0,
            QPointF(0.0, 0.0),
            self._path,
        )

    def _paint_white_out_transition(
        self,
        painter: QPainter,
        bounds: QRectF,
        fade_progress: float,
        zoom_progress: float,
    ) -> None:
        timeline_progress = self._timeline_progress()
        duration_ms = self._transition.duration()
        # 白100%保持時間 100ms をタイムライン比率に変換
        hold_ratio = min(0.2, 100.0 / max(1, duration_ms))
        fade_out_end = (1.0 - hold_ratio) / 2.0   # 前半: 前の写真 → 白
        fade_in_start = fade_out_end + hold_ratio   # 後半: 白 → 次の写真

        white_area = self._mask_bounds(bounds)

        if timeline_progress <= fade_out_end:
            # フェーズ1: 前の写真 → 白100%
            phase_progress = timeline_progress / max(0.001, fade_out_end)
            self._draw_pixmap(
                painter,
                self._previous_pixmap,
                bounds,
                self._outgoing_zoom_factor(zoom_progress),
                self._interpolate_pan(self._outgoing_pan_start, self._outgoing_pan_end, phase_progress),
                self._previous_path,
            )
            painter.save()
            painter.setClipRect(white_area)
            painter.fillRect(white_area, QColor(255, 255, 255, int(255 * phase_progress)))
            painter.restore()
        elif timeline_progress <= fade_in_start:
            # フェーズ2: 白100%保持
            painter.save()
            painter.setClipRect(white_area)
            painter.fillRect(white_area, QColor(255, 255, 255, 255))
            painter.restore()
        else:
            # フェーズ3: 白 → 次の写真へフェード
            phase_progress = (timeline_progress - fade_in_start) / max(0.001, 1.0 - fade_in_start)
            painter.save()
            painter.setClipRect(white_area)
            painter.fillRect(white_area, QColor(255, 255, 255, 255))
            painter.restore()
            painter.save()
            painter.setClipRect(white_area)
            painter.setOpacity(phase_progress)
            self._draw_pixmap(
                painter,
                self._current_pixmap,
                bounds,
                self._incoming_zoom_factor(zoom_progress),
                QPointF(0.0, 0.0),
                self._path,
            )
            painter.restore()

    def _mask_bounds(self, bounds: QRectF) -> QRectF:
        mask = self._show_size_bounds(bounds)
        if mask is None:
            return QRectF(bounds)
        return QRectF(mask.toAlignedRect())

    def _fill_outside_rect(self, painter: QPainter, outer: QRectF, inner: QRectF, color: QColor) -> None:
        outer_rect = QRectF(outer.toAlignedRect())
        inner_rect = QRectF(inner.toAlignedRect()).intersected(outer_rect)
        if outer_rect.isEmpty() or inner_rect == outer_rect:
            return
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(color)
        if inner_rect.top() > outer_rect.top():
            painter.drawRect(QRectF(outer_rect.left(), outer_rect.top(), outer_rect.width(), inner_rect.top() - outer_rect.top()))
        if inner_rect.bottom() < outer_rect.bottom():
            painter.drawRect(QRectF(outer_rect.left(), inner_rect.bottom(), outer_rect.width(), outer_rect.bottom() - inner_rect.bottom()))
        if inner_rect.left() > outer_rect.left():
            painter.drawRect(QRectF(outer_rect.left(), inner_rect.top(), inner_rect.left() - outer_rect.left(), inner_rect.height()))
        if inner_rect.right() < outer_rect.right():
            painter.drawRect(QRectF(inner_rect.right(), inner_rect.top(), outer_rect.right() - inner_rect.right(), inner_rect.height()))

    def _target_bounds(self) -> QRectF:
        available = QRectF(self.contentsRect())
        if available.width() <= 0 or available.height() <= 0:
            return available

        bounds = QRectF(available)
        if self._display_resolution is not None and self._display_resolution.width() > 0 and self._display_resolution.height() > 0:
            bounds = self._fit_rect_to_ratio(
                bounds,
                self._display_resolution.width() / self._display_resolution.height(),
            )

        return bounds

    def _fit_rect_to_ratio(self, base_rect: QRectF, target_ratio: float) -> QRectF:
        if target_ratio <= 0 or base_rect.width() <= 0 or base_rect.height() <= 0:
            return base_rect

        base_ratio = base_rect.width() / base_rect.height()
        if base_ratio > target_ratio:
            target_height = base_rect.height()
            target_width = target_height * target_ratio
        else:
            target_width = base_rect.width()
            target_height = target_width / target_ratio

        return QRectF(
            base_rect.center().x() - (target_width / 2),
            base_rect.center().y() - (target_height / 2),
            target_width,
            target_height,
        )

    def _draw_pixmap(
        self,
        painter: QPainter,
        pixmap: QPixmap,
        bounds: QRectF,
        zoom: float = 1.0,
        pan: QPointF | None = None,
        photo_path: Path | None = None,
    ) -> None:
        if pixmap.width() <= 0 or pixmap.height() <= 0 or bounds.width() <= 0 or bounds.height() <= 0:
            return

        manual_pan = QPointF(0.0, 0.0)
        if photo_path is not None:
            manual_pan = self._manual_pan_by_path.get(str(photo_path), QPointF(0.0, 0.0))
            manual_pan = self._clamp_manual_pan(manual_pan, pixmap, bounds)

        source_rect = self._source_rect_for_aspect(pixmap, manual_pan)
        if source_rect.width() <= 0 or source_rect.height() <= 0:
            return

        zoom *= self._display_zoom_factor_for_path(photo_path)
        scale = bounds.height() / source_rect.height()
        draw_width = source_rect.width() * scale * zoom
        draw_height = source_rect.height() * scale * zoom
        animation_pan = pan if pan is not None else QPointF(0.0, 0.0)
        pan_offset = QPointF(animation_pan.x() + manual_pan.x(), animation_pan.y() + manual_pan.y())
        max_pan_x, max_pan_y = self._manual_pan_limits(pixmap, bounds)
        pan_offset = QPointF(
            max(-max_pan_x, min(max_pan_x, pan_offset.x())),
            max(-max_pan_y, min(max_pan_y, pan_offset.y())),
        )
        center_x = bounds.center().x() + (bounds.width() * pan_offset.x())
        center_y = bounds.center().y() + (bounds.height() * pan_offset.y())
        draw_rect = QRectF(
            center_x - draw_width / 2,
            center_y - draw_height / 2,
            draw_width,
            draw_height,
        )
        painter.drawPixmap(draw_rect, pixmap, source_rect)

    def _source_rect_for_aspect(self, pixmap: QPixmap, manual_pan: QPointF | None = None) -> QRectF:
        return QRectF(pixmap.rect())

    def _manual_pan_limits(self, pixmap: QPixmap, bounds: QRectF) -> tuple[float, float]:
        if pixmap.isNull() or bounds.width() <= 0 or bounds.height() <= 0:
            return 0.0, 0.0

        return 0.5, 0.5

    def _transition_pan_limits(self, pixmap: QPixmap, bounds: QRectF, photo_path: Path | str | None = None) -> tuple[float, float]:
        source_rect = QRectF(pixmap.rect())
        if source_rect.width() <= 0 or source_rect.height() <= 0 or bounds.width() <= 0 or bounds.height() <= 0:
            return 0.0, 0.0

        scale = (bounds.height() / source_rect.height()) * self._display_zoom_factor_for_path(photo_path)
        draw_width = source_rect.width() * scale
        draw_height = source_rect.height() * scale
        # マスク（ショーサイズ）が設定されている場合、マスク領域内でのパンを許可
        show = self._show_size_bounds(bounds)
        visible_w = show.width() if show is not None else bounds.width()
        visible_h = show.height() if show is not None else bounds.height()
        max_pan_x = max(0.0, (draw_width - visible_w) / (2 * max(1.0, bounds.width())))
        max_pan_y = max(0.0, (draw_height - visible_h) / (2 * max(1.0, bounds.height())))
        return max_pan_x, max_pan_y

    def _clamp_manual_pan(self, pan: QPointF, pixmap: QPixmap, bounds: QRectF) -> QPointF:
        max_pan_x, max_pan_y = self._manual_pan_limits(pixmap, bounds)
        return QPointF(
            max(-max_pan_x, min(max_pan_x, pan.x())),
            max(-max_pan_y, min(max_pan_y, pan.y())),
        )

    def _prepare_transition_motion(self) -> None:
        bounds = self._target_bounds()
        incoming_can_pan = self._transition_uses_pan_motion(self._current_pixmap, bounds, self._path)
        outgoing_can_pan = self._transition_uses_pan_motion(self._previous_pixmap, bounds, self._previous_path)
        if incoming_can_pan:
            self._incoming_pan_start = self._random_pan(0.018)
            self._incoming_pan_end = self._random_pan(0.006)
        else:
            self._incoming_pan_start = QPointF(0.0, 0.0)
            self._incoming_pan_end = QPointF(0.0, 0.0)
        if outgoing_can_pan:
            self._outgoing_pan_start = QPointF(0.0, 0.0)
            self._outgoing_pan_end = self._random_pan(0.012)
        else:
            self._outgoing_pan_start = QPointF(0.0, 0.0)
            self._outgoing_pan_end = QPointF(0.0, 0.0)
        # 方向指定付きトランジションはユーザー指定の方向を維持、それ以外はランダム
        if self._transition_style not in DIRECTION_VECTORS:
            directions = [
                QPointF(1.0, 0.0),
                QPointF(-1.0, 0.0),
                QPointF(0.0, 1.0),
                QPointF(0.0, -1.0),
            ]
            recent = set((d.x(), d.y()) for d in self._random_dir_history[-2:])
            filtered = [d for d in directions if (d.x(), d.y()) not in recent]
            if not filtered:
                filtered = directions
            chosen = random.choice(filtered)
            self._random_dir_history.append(chosen)
            if len(self._random_dir_history) > 10:
                self._random_dir_history = self._random_dir_history[-5:]
            self._transition_direction = chosen

    def _reset_motion(self) -> None:
        self._incoming_pan_start = QPointF(0.0, 0.0)
        self._incoming_pan_end = QPointF(0.0, 0.0)
        self._outgoing_pan_start = QPointF(0.0, 0.0)
        self._outgoing_pan_end = QPointF(0.0, 0.0)
        self._transition_direction = QPointF(1.0, 0.0)

    def _transition_uses_pan_motion(self, pixmap: QPixmap | None, bounds: QRectF, photo_path: Path | str | None = None) -> bool:
        if pixmap is None or pixmap.isNull():
            return False
        if self._transition_style == "cut" or self._transition_style.startswith("wipe"):
            return False
        max_pan_x, max_pan_y = self._transition_pan_limits(pixmap, bounds, photo_path)
        return max_pan_x > 0.0 or max_pan_y > 0.0

    def _transition_uses_zoom_motion(self) -> bool:
        return self._transition_style == "zoom_fade"

    def _random_pan(self, amount: float) -> QPointF:
        return QPointF(random.uniform(-amount, amount), random.uniform(-amount, amount))

    def _interpolate_pan(self, start: QPointF, end: QPointF, progress: float) -> QPointF:
        t = max(0.0, min(1.0, progress))
        return QPointF(self._lerp(start.x(), end.x(), t), self._lerp(start.y(), end.y(), t))

    def _timeline_progress(self) -> float:
        value = max(0.0, min(1.0, self._transition_value))

        return value

    def _crossfade_progress(self, timeline_progress: float) -> float:
        return max(0.0, min(1.0, timeline_progress))

    def _zoom_progress(self, timeline_progress: float) -> float:
        # ズームは時間軸に対して最後まで連続して進める。
        return max(0.0, min(1.0, timeline_progress))

    def _easing_in_out_cubic(self, t: float) -> float:
        """Cubic ease-in-out easing function for smoother transitions."""
        t = max(0.0, min(1.0, t))
        if t < 0.5:
            return 4 * t * t * t
        else:
            return 1 - ((-2 * t + 2) ** 3) / 2

    def _incoming_zoom_factor(self, progress: float) -> float:
        if not self._fade_zoom_enabled or not self._transition_uses_zoom_motion():
            return 1.0

        clamped = max(0.0, min(1.0, progress))
        return self._lerp(1.07, 1.0, clamped)

    def _outgoing_zoom_factor(self, progress: float) -> float:
        if not self._fade_zoom_enabled or not self._transition_uses_zoom_motion():
            return 1.0

        clamped = max(0.0, min(1.0, progress))
        return self._lerp(1.0, 1.03, clamped)

    def _lerp(self, start: float, end: float, t: float) -> float:
        clamped = max(0.0, min(1.0, t))
        return start + ((end - start) * clamped)

    def _incoming_opacity(self, progress: float) -> float:
        clamped = max(0.0, min(1.0, progress))
        return min(1.0, 0.12 + (clamped * 0.88))

    def _outgoing_opacity(self, progress: float) -> float:
        clamped = max(0.0, min(1.0, progress))
        return max(0.0, 1.0 - (clamped * 0.92))

    def _on_transition_changed(self, value: object) -> None:
        self._transition_value = float(value)
        if self._transition_value >= 1.0:
            self._previous_pixmap = None
            self._previous_path = None
            self._reset_motion()
        self.update()

    def _apply_canvas_style(self) -> None:
        self.setStyleSheet(
            """
            QWidget {{
                border: none;
                border-radius: 0px;
                background: transparent;
                color: rgba(73, 56, 35, 0.72);
                font-size: 20px;
                padding: 0px;
            }}
            """
        )


class ThumbnailList(QListWidget):
    reordered = Signal()
    gapSelected = Signal(int)  # gap index: アイテムiとi+1の間 = gap i
    filesDropped = Signal(list, int)  # (file_paths, insert_index)
    resized = Signal()

    def __init__(self) -> None:
        super().__init__()
        self.setViewMode(QListWidget.ViewMode.IconMode)
        self.setFlow(QListWidget.Flow.LeftToRight)
        self.setMovement(QListWidget.Movement.Snap)
        self.setIconSize(THUMBNAIL_SIZE)
        self.setResizeMode(QListWidget.ResizeMode.Adjust)
        self.setWrapping(False)
        self.setSpacing(16)
        self.setWordWrap(True)
        self.setHorizontalScrollMode(QListWidget.ScrollMode.ScrollPerPixel)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setSelectionMode(QListWidget.SelectionMode.ExtendedSelection)
        self.setDragDropMode(QListWidget.DragDropMode.DragDrop)
        self.setDefaultDropAction(Qt.DropAction.MoveAction)
        self.setAcceptDrops(True)
        self._drag_start_index = -1
        self._selected_gap = -1  # -1=ギャップ未選択
        self._scroll_timer = QTimer(self)
        self._scroll_timer.setInterval(20)
        self._scroll_timer.timeout.connect(self._auto_scroll_tick)
        self._scroll_speed = 0
        self.setStyleSheet(
            """
            QListWidget {
                border: none;
                background: transparent;
                padding: 8px 2px 8px 2px;
                outline: none;
            }
            QListWidget::item {
                width: 160px;
                padding: 8px;
                border-radius: 14px;
                color: #c8c8dc;
                background: rgba(255, 255, 255, 0.05);
            }
            QListWidget::item:selected {
                background: rgba(110, 120, 255, 0.20);
                border: 1px solid rgba(140, 148, 255, 0.40);
            }
            QListWidget::item:hover {
                background: rgba(255, 255, 255, 0.10);
            }
            """
        )

    def _drop_target_index(self, pos) -> int:
        if not self.isWrapping():
            for i in range(self.count()):
                rect = self.visualItemRect(self.item(i))
                if pos.x() < rect.center().x():
                    return i
            return self.count()
        # グリッド表示: Y→X の順で判定
        for i in range(self.count()):
            rect = self.visualItemRect(self.item(i))
            if pos.y() < rect.top():
                return i
            if rect.top() <= pos.y() <= rect.bottom():
                if pos.x() < rect.center().x():
                    return i
        return self.count()

    def _find_gap_at(self, pos) -> int:
        """posがアイテム間のギャップ領域にあればそのgapインデックスを返す。なければ-1。"""
        gap_margin = 12  # ギャップ判定の余白(px)
        for i in range(self.count() - 1):
            rect_cur = self.visualItemRect(self.item(i))
            rect_next = self.visualItemRect(self.item(i + 1))
            if self.flow() == QListWidget.Flow.LeftToRight and not self.isWrapping():
                gap_left = rect_cur.right() - gap_margin
                gap_right = rect_next.left() + gap_margin
                if gap_left <= pos.x() <= gap_right and rect_cur.top() <= pos.y() <= rect_cur.bottom():
                    return i
            else:
                # グリッド: 同じ行で隣り合うアイテム間
                if abs(rect_cur.top() - rect_next.top()) < rect_cur.height() // 2:
                    gap_left = rect_cur.right() - gap_margin
                    gap_right = rect_next.left() + gap_margin
                    if gap_left <= pos.x() <= gap_right and rect_cur.top() <= pos.y() <= rect_cur.bottom():
                        return i
        return -1

    def mousePressEvent(self, event) -> None:
        if event.button() == Qt.MouseButton.LeftButton:
            pos = event.position().toPoint()
            item = self.itemAt(pos)
            gap = self._find_gap_at(pos)
            if gap >= 0 and item is None:
                # ギャップをクリック
                self._selected_gap = gap
                self._drag_start_index = -1
                self.gapSelected.emit(gap)
                self.viewport().update()
                return
            # アイテムをクリック → ギャップ選択解除
            self._selected_gap = -1
            if item is not None:
                self._drag_start_index = self.row(item)
            else:
                self._drag_start_index = -1
        super().mousePressEvent(event)

    def _has_supported_files(self, mime_data) -> bool:
        if not mime_data.hasUrls():
            return False
        for url in mime_data.urls():
            if url.isLocalFile():
                path = Path(url.toLocalFile())
                if path.suffix.lower() in SUPPORTED_SUFFIXES:
                    return True
        return False

    def dropEvent(self, event) -> None:
        self._selected_gap = -1
        # 外部ファイルドロップ
        if event.source() is not self and event.mimeData().hasUrls():
            paths = []
            for url in event.mimeData().urls():
                if url.isLocalFile():
                    p = Path(url.toLocalFile())
                    if p.suffix.lower() in SUPPORTED_SUFFIXES:
                        paths.append(p)
            if paths:
                insert_at = self._drop_target_index(event.position().toPoint())
                self.filesDropped.emit(paths, insert_at)
                event.acceptProposedAction()
            else:
                event.ignore()
            return
        # 内部ドラッグ並び替え
        if self._drag_start_index < 0:
            event.ignore()
            return
        drop_index = self._drop_target_index(event.position().toPoint())
        src = self._drag_start_index
        if src == drop_index or src + 1 == drop_index:
            event.ignore()
            return
        self.blockSignals(True)
        item = self.takeItem(src)
        if drop_index > src:
            drop_index -= 1
        self.insertItem(drop_index, item)
        self.setCurrentRow(drop_index)
        self.blockSignals(False)
        self._drag_start_index = -1
        self.reordered.emit()

    def dragEnterEvent(self, event) -> None:
        if event.source() is self:
            event.acceptProposedAction()
        elif self._has_supported_files(event.mimeData()):
            event.acceptProposedAction()
        else:
            event.ignore()

    def dragMoveEvent(self, event) -> None:
        accepted = False
        if event.source() is self:
            event.acceptProposedAction()
            accepted = True
            pos = event.position().toPoint()
            drop_idx = self._drop_target_index(pos)
            if drop_idx > 0 and drop_idx < self.count():
                self._selected_gap = drop_idx - 1
            elif drop_idx == 0 and self.count() > 1:
                self._selected_gap = -1
            else:
                self._selected_gap = max(0, self.count() - 2)
            self.viewport().update()
        elif self._has_supported_files(event.mimeData()):
            event.acceptProposedAction()
            accepted = True
            pos = event.position().toPoint()
            drop_idx = self._drop_target_index(pos)
            if drop_idx > 0 and drop_idx < self.count():
                self._selected_gap = drop_idx - 1
            elif self.count() > 0:
                self._selected_gap = max(0, self.count() - 2)
            self.viewport().update()
        else:
            event.ignore()
        if accepted and not self.isWrapping():
            self._update_auto_scroll(event.position().toPoint())
        elif not accepted:
            self._stop_auto_scroll()

    def _update_auto_scroll(self, pos) -> None:
        edge = 60
        vw = self.viewport().width()
        x = pos.x()
        if x < edge:
            ratio = 1.0 - x / edge
            self._scroll_speed = -int(4 + 16 * ratio)
        elif x > vw - edge:
            ratio = 1.0 - (vw - x) / edge
            self._scroll_speed = int(4 + 16 * ratio)
        else:
            self._scroll_speed = 0
        if self._scroll_speed != 0:
            if not self._scroll_timer.isActive():
                self._scroll_timer.start()
        else:
            self._scroll_timer.stop()

    def _auto_scroll_tick(self) -> None:
        bar = self.horizontalScrollBar()
        bar.setValue(bar.value() + self._scroll_speed)

    def _stop_auto_scroll(self) -> None:
        self._scroll_speed = 0
        self._scroll_timer.stop()

    def dragLeaveEvent(self, event) -> None:
        self._stop_auto_scroll()
        super().dragLeaveEvent(event)

    def startDrag(self, supportedActions) -> None:
        if len(self.selectedItems()) != 1:
            self._drag_start_index = -1
            return
        drag = QDrag(self)
        drag.setMimeData(QMimeData())
        item = self.currentItem()
        if item is not None:
            pixmap = item.icon().pixmap(THUMBNAIL_SIZE)
            drag.setPixmap(pixmap)
            drag.setHotSpot(pixmap.rect().center())
        drag.exec(Qt.DropAction.MoveAction)
        self._stop_auto_scroll()

    def resizeEvent(self, event) -> None:  # type: ignore[override]
        super().resizeEvent(event)
        self.resized.emit()

    def paintEvent(self, event) -> None:
        super().paintEvent(event)
        gap = self._selected_gap
        if gap < 0 or gap >= self.count() - 1:
            return
        item_left = self.item(gap)
        item_right = self.item(gap + 1)
        if item_left is None or item_right is None:
            return
        rect_left = self.visualItemRect(item_left)
        rect_right = self.visualItemRect(item_right)
        painter = QPainter(self.viewport())
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        color = QColor(140, 148, 255, 200)
        pen = QPen(color)
        pen.setWidth(3)
        painter.setPen(pen)
        painter.setBrush(color)
        if self.flow() == QListWidget.Flow.LeftToRight and not self.isWrapping():
            # 横並び: 間の中央に縦線+三角
            cx = (rect_left.right() + rect_right.left()) // 2
            top = rect_left.top() + 2
            bottom = rect_left.bottom() - 2
            painter.drawLine(cx, top, cx, bottom)
            tri_top = QPolygonF([
                QPointF(cx - 6, top),
                QPointF(cx + 6, top),
                QPointF(cx, top + 8),
            ])
            painter.drawPolygon(tri_top)
            tri_bottom = QPolygonF([
                QPointF(cx - 6, bottom),
                QPointF(cx + 6, bottom),
                QPointF(cx, bottom - 8),
            ])
            painter.drawPolygon(tri_bottom)
        else:
            # グリッド表示
            if abs(rect_left.top() - rect_right.top()) < rect_left.height() // 2:
                cx = (rect_left.right() + rect_right.left()) // 2
                top = rect_left.top() + 2
                bottom = rect_left.bottom() - 2
                painter.drawLine(cx, top, cx, bottom)
                tri_top = QPolygonF([
                    QPointF(cx - 6, top),
                    QPointF(cx + 6, top),
                    QPointF(cx, top + 8),
                ])
                painter.drawPolygon(tri_top)
                tri_bottom = QPolygonF([
                    QPointF(cx - 6, bottom),
                    QPointF(cx + 6, bottom),
                    QPointF(cx, bottom - 8),
                ])
                painter.drawPolygon(tri_bottom)
        painter.end()


class GlassPanel(QFrame):
    def __init__(self) -> None:
        super().__init__()
        self.setObjectName("glassPanel")
        shadow = QGraphicsDropShadowEffect(self)
        shadow.setBlurRadius(20)
        shadow.setOffset(0, 4)
        shadow.setColor(QColor(0, 0, 0, 80))
        self.setGraphicsEffect(shadow)


class MainWindow(QMainWindow):
    def __init__(self) -> None:
        super().__init__()
        self.setWindowTitle("LumiSlide")
        self.resize(1600, 900)
        self._background_color = QColor("#13131a")

        self.photos: list[PhotoItem] = []
        self.filtered_photos: list[PhotoItem] = []
        self.current_index = -1
        self.current_folder: Path | None = None
        self._clipboard_photos: list[PhotoItem] = []
        self.is_playback_fullscreen = False
        self._undo_stack: list[tuple[int, list[tuple[str, str, int]]]] = []  # (index, [(path, style, duration)])
        self._max_undo = 50
        self._photo_shuffle_history: list[str] = []
        self._photo_shuffle_deck: list[str] = []

        self.slideshow_timer = QTimer(self)
        self.slideshow_timer.timeout.connect(self.show_next_photo)

        self._apply_main_window_style()

        self._build_ui()
        self._install_shortcuts()
        self._load_app_state()
        if not self._state_file_path().exists():
            self._save_app_state()
        self._update_expiry_label()
        self._check_expiry()

    def _main_window_style(self) -> str:
        return """
            QMainWindow, QWidget#root {
                background: #13131a;
            }
            #glassPanel {
                border: 1px solid rgba(255, 255, 255, 0.07);
                border-radius: 18px;
                background: rgba(28, 28, 36, 0.94);
            }
            QLabel#headline {
                color: #e8e8f0;
                font-size: 28px;
                font-weight: 600;
            }
            QLabel#subhead {
                color: rgba(180, 178, 200, 0.80);
                font-size: 14px;
            }
            QLabel#subhead:disabled {
                color: rgba(180, 178, 200, 0.30);
            }
            QLabel#sectionTitle {
                color: rgba(160, 158, 185, 0.85);
                font-size: 11px;
                letter-spacing: 2px;
                text-transform: uppercase;
                font-weight: 700;
            }
            QPushButton, QToolButton {
                border: none;
                border-radius: 14px;
                background: rgba(255, 255, 255, 0.09);
                color: #dcdce8;
                padding: 9px 14px;
                font-size: 14px;
            }
            QPushButton:hover, QToolButton:hover {
                background: rgba(255, 255, 255, 0.15);
            }
            QPushButton:checked, QToolButton:checked {
                background: rgba(110, 120, 255, 0.22);
                border: 1px solid rgba(140, 148, 255, 0.45);
            }
            QComboBox, QSpinBox {
                min-height: 36px;
                border: 1px solid rgba(255, 255, 255, 0.09);
                border-radius: 12px;
                padding: 4px 10px;
                background: rgba(255, 255, 255, 0.07);
                color: #dcdce8;
                selection-background-color: rgba(110, 120, 255, 0.28);
            }
            QComboBox::drop-down {
                width: 24px;
                border: none;
            }
            QSpinBox:disabled {
                background: rgba(255, 255, 255, 0.03);
                color: rgba(180, 178, 200, 0.35);
            }
            QComboBox:disabled {
                background: rgba(255, 255, 255, 0.03);
                color: rgba(180, 178, 200, 0.35);
            }
            QSlider::groove:horizontal {
                border-radius: 4px;
                height: 6px;
                background: rgba(255, 255, 255, 0.10);
            }
            QSlider::sub-page:horizontal {
                border-radius: 4px;
                background: rgba(130, 140, 255, 0.72);
            }
            QSlider::handle:horizontal {
                width: 16px;
                margin: -5px 0;
                border-radius: 8px;
                background: #c8c8e0;
                border: none;
            }
            QStatusBar {
                background: transparent;
                color: rgba(160, 158, 185, 0.75);
            }
            QSplitter::handle { background: transparent; }
        """

    def _apply_main_window_style(self) -> None:
        self.setStyleSheet(self._main_window_style())
        if hasattr(self, "root_widget"):
            palette = self.root_widget.palette()
            palette.setColor(self.root_widget.backgroundRole(), QColor("#13131a"))
            self.root_widget.setPalette(palette)
        if hasattr(self, "canvas"):
            self.canvas.set_background_color(self._background_color)
        if hasattr(self, "background_color_button"):
            self._update_background_color_button()

    def _state_file_path(self) -> Path:
        return Path(__file__).resolve().with_name(APP_STATE_FILE)

    def _expiry_file_path(self) -> Path:
        return Path(__file__).resolve().with_name("photo_app_expiry.json")

    def _update_expiry_label(self) -> None:
        expiry_path = self._expiry_file_path()
        if expiry_path.exists():
            try:
                data = json.loads(expiry_path.read_text(encoding="utf-8"))
                expiry_str = data.get("expiry_date")
                if expiry_str:
                    self.expiry_label.setText(expiry_str)
                    return
            except (OSError, json.JSONDecodeError):
                pass
        self.expiry_label.setText("未設定")

    def _check_expiry(self) -> None:
        expiry_path = self._expiry_file_path()
        if not expiry_path.exists():
            return
        try:
            data = json.loads(expiry_path.read_text(encoding="utf-8"))
            expiry_str = data.get("expiry_date")
            if not expiry_str:
                return
            expiry_dt = datetime.strptime(expiry_str, "%Y-%m-%d %H:%M")
            if datetime.now() > expiry_dt:
                self._show_warning("利用期限切れ", f"利用期限（{expiry_str}）を過ぎています。")
                self._lock_ui()
        except (OSError, json.JSONDecodeError, ValueError):
            pass

    def _lock_ui(self) -> None:
        for widget in (
            self.open_button, self.prev_button, self.next_button,
            self.rotate_left_button, self.rotate_right_button,
            self.play_button, self.shuffle_button,
            self.transition_combo, self.apply_transition_to_all_button,
            self.interval_slider, self.fade_spin,
            self.resolution_combo, self.background_color_button, self.aspect_combo,
            self.aspect_width_spin, self.aspect_height_spin,
            self.export_mp4_button,
            self.save_state_button, self.load_state_button,
            self.new_project_button,
            self.thumbnail_list, self.canvas,
        ):
            widget.setEnabled(False)

    def _unlock_ui(self) -> None:
        for widget in (
            self.open_button, self.prev_button, self.next_button,
            self.rotate_left_button, self.rotate_right_button,
            self.play_button, self.shuffle_button,
            self.transition_combo, self.apply_transition_to_all_button,
            self.interval_slider, self.fade_spin,
            self.resolution_combo, self.background_color_button, self.aspect_combo,
            self.aspect_width_spin, self.aspect_height_spin,
            self.export_mp4_button,
            self.save_state_button, self.load_state_button,
            self.new_project_button,
            self.thumbnail_list, self.canvas,
        ):
            widget.setEnabled(True)

    def _dialog_style(self) -> str:
        return """
            QDialog { background: #1c1c24; color: #dcdce8; }
            QLabel { color: #dcdce8; }
            QPushButton {
                border: none; border-radius: 10px;
                background: rgba(255,255,255,0.10);
                color: #dcdce8; padding: 8px 18px; font-size: 14px;
            }
            QPushButton:hover { background: rgba(255,255,255,0.18); }
            QPushButton:default {
                background: rgba(110,120,255,0.30);
                border: 1px solid rgba(140,148,255,0.55);
            }
            QDateTimeEdit, QLineEdit, QSpinBox, QComboBox {
                background: rgba(255,255,255,0.07);
                border: 1px solid rgba(255,255,255,0.09);
                border-radius: 10px; padding: 6px 10px;
                color: #dcdce8; font-size: 13px;
            }
        """

    def _background_color_hex(self) -> str:
        return self._background_color.name(QColor.NameFormat.HexRgb)

    def _update_background_color_button(self) -> None:
        text_color = "#101014" if self._background_color.lightnessF() > 0.65 else "#f3f3f8"
        self.background_color_button.setText(self._background_color_hex().upper())
        self.background_color_button.setStyleSheet(
            f"QPushButton {{ background: {self._background_color_hex()}; color: {text_color}; border: 1px solid rgba(255,255,255,0.18); }}"
            f" QPushButton:hover {{ background: {self._background_color_hex()}; color: {text_color}; border: 1px solid rgba(255,255,255,0.30); }}"
        )

    def _choose_background_color(self) -> None:
        dialog = QColorDialog(self)
        dialog.setWindowTitle("背景色を選択")
        dialog.setCurrentColor(self._background_color)
        dialog.setOption(QColorDialog.ColorDialogOption.DontUseNativeDialog, True)
        dialog.setStyleSheet(self._dialog_style())
        if dialog.exec() != QDialog.DialogCode.Accepted:
            return
        chosen = dialog.selectedColor()
        chosen.setAlpha(255)
        self._background_color = chosen
        self._apply_main_window_style()

    def _show_message(self, icon: QMessageBox.Icon, title: str, text: str) -> None:
        box = QMessageBox(self)
        box.setIcon(icon)
        box.setWindowTitle(title)
        box.setText(text)
        box.setStandardButtons(QMessageBox.StandardButton.Ok)
        box.setStyleSheet(self._dialog_style())
        box.exec()

    def _show_info(self, title: str, text: str) -> None:
        self._show_message(QMessageBox.Icon.Information, title, text)

    def _show_warning(self, title: str, text: str) -> None:
        self._show_message(QMessageBox.Icon.Warning, title, text)

    def _set_expiry_date(self) -> None:
        dialog = QDialog(self)
        dialog.setWindowTitle("利用期限を設定")
        dialog.setStyleSheet(self._dialog_style())
        dlg_layout = QVBoxLayout(dialog)

        dt_edit = QDateTimeEdit()
        dt_edit.setCalendarPopup(True)
        dt_edit.setDisplayFormat("yyyy-MM-dd HH:mm")

        expiry_path = self._expiry_file_path()
        current_qdt = QDateTime.currentDateTime()
        if expiry_path.exists():
            try:
                data = json.loads(expiry_path.read_text(encoding="utf-8"))
                expiry_str = data.get("expiry_date")
                if expiry_str:
                    parsed = QDateTime.fromString(expiry_str, "yyyy-MM-dd HH:mm")
                    if parsed.isValid():
                        current_qdt = parsed
            except (OSError, json.JSONDecodeError):
                pass
        dt_edit.setDateTime(current_qdt)

        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel
        )
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)

        dlg_layout.addWidget(QLabel("利用期限日時を選択してください:"))
        dlg_layout.addWidget(dt_edit)
        dlg_layout.addWidget(buttons)

        if dialog.exec() == QDialog.DialogCode.Accepted:
            expiry_str = dt_edit.dateTime().toString("yyyy-MM-dd HH:mm")
            try:
                expiry_path.write_text(
                    json.dumps({"expiry_date": expiry_str}, ensure_ascii=False, indent=2),
                    encoding="utf-8",
                )
                self.expiry_label.setText(expiry_str)
                self.statusBar().showMessage(f"利用期限を設定しました: {expiry_str}")
            except OSError:
                self._show_warning("エラー", "利用期限を保存できませんでした。")

    def _clear_expiry_date(self) -> None:
        password, ok = QInputDialog.getText(
            self, "認証", "パスワードを入力してください:", QLineEdit.EchoMode.Password
        )
        if not ok:
            return
        if password != "password":
            self._show_warning("認証エラー", "パスワードが正しくありません。")
            return
        expiry_path = self._expiry_file_path()
        if not expiry_path.exists():
            self.statusBar().showMessage("利用期限は設定されていません。")
            self.clear_expiry_button.hide()
            return
        try:
            expiry_path.unlink()
            self.expiry_label.setText("未設定")
            self.statusBar().showMessage("利用期限を解除しました。")
            self.clear_expiry_button.hide()
            self.set_expiry_button.hide()
            self._unlock_ui()
        except OSError:
            self._show_warning("エラー", "利用期限ファイルを削除できませんでした。")

    def _new_project(self) -> None:
        dialog = QDialog(self)
        dialog.setWindowTitle("新規作成")
        dialog.setStyleSheet(self._dialog_style())
        dlg_layout = QVBoxLayout(dialog)
        dlg_layout.setSpacing(16)

        label = QLabel("現在の状態をリセットしますか？")
        dlg_layout.addWidget(label)

        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel
        )
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)
        dlg_layout.addWidget(buttons)

        if dialog.exec() != QDialog.DialogCode.Accepted:
            return

        # スライドショー停止
        self.slideshow_timer.stop()
        self.play_button.setChecked(False)

        # データリセット
        self.photos = []
        self.filtered_photos = []
        self.current_index = -1
        self.current_folder = None

        # UIリセット
        self.thumbnail_list.clear()
        self.canvas.set_photo(None, animate=False)
        self.canvas.set_manual_pan_state({})
        self.canvas.set_manual_zoom_state({})
        self.path_label.setText("フォルダを開いてください")
        self.count_label.setText("0 photos")
        self.selection_label.setText("ライブラリ未選択")
        self.photo_title.setText("No Selection")
        self.photo_meta.setText("画像の解像度や日時がここに出ます")
        self._update_preview_zoom_controls()

        # 設定初期化
        self.interval_slider.setValue(40)
        self.fade_spin.setValue(1200)
        self.resolution_combo.setCurrentIndex(3)
        self.aspect_combo.setCurrentIndex(0)
        self.shuffle_button.setChecked(False)

        # 状態ファイル削除
        state_path = self._state_file_path()
        if state_path.exists():
            try:
                state_path.unlink()
            except OSError:
                pass

        self.statusBar().showMessage("新規作成しました")

    def _toggle_clear_expiry_button(self) -> None:
        visible = not self.clear_expiry_button.isVisible()
        self.set_expiry_button.setVisible(visible)
        self.clear_expiry_button.setVisible(visible)

    def _save_app_state(self, state_path: Path | None = None) -> bool:
        target_path = state_path if state_path is not None else self._state_file_path()
        current_photo_path: str | None = None
        if 0 <= self.current_index < len(self.filtered_photos):
            current_photo_path = str(self.filtered_photos[self.current_index].path)

        manual_pan_raw = self.canvas.manual_pan_state()
        manual_pan_serialized = {
            path: {"x": offset.x(), "y": offset.y()} for path, offset in manual_pan_raw.items()
        }
        manual_zoom_serialized = self.canvas.manual_zoom_state()

        state = {
            "version": 2,
            "window": {
                "size": {"width": self.width(), "height": self.height()},
                "splitter_sizes": self.splitter.sizes(),
            },
            "settings": {
                "interval_slider": self.interval_slider.value(),
                "transition_ms": self.fade_spin.value(),
                "shuffle": self.shuffle_button.isChecked(),
                "background_color": self._background_color_hex(),
                "resolution_index": self.resolution_combo.currentIndex(),
                "aspect_index": self.aspect_combo.currentIndex(),
                "custom_aspect": {
                    "width": self.aspect_width_spin.value(),
                    "height": self.aspect_height_spin.value(),
                },
            },
            "library": {
                "folder": str(self.current_folder) if self.current_folder is not None else None,
                "current_photo_path": current_photo_path,
                "photo_transitions": {
                    str(photo.path): {
                        "style": photo.transition_style,
                        "duration_ms": photo.transition_duration_ms,
                    }
                    for photo in self.filtered_photos
                },
            },
            "canvas": {
                "manual_pan": manual_pan_serialized,
                "manual_zoom": manual_zoom_serialized,
            },
        }

        try:
            target_path.parent.mkdir(parents=True, exist_ok=True)
            target_path.write_text(
                json.dumps(state, ensure_ascii=False, indent=2),
                encoding="utf-8",
            )
            return True
        except OSError:
            return False

    def _load_app_state(self, state_path: Path | None = None) -> bool:
        path = state_path if state_path is not None else self._state_file_path()
        if not path.exists():
            return False

        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return False

        window_data = data.get("window", {})
        size_data = window_data.get("size", {})
        width = size_data.get("width")
        height = size_data.get("height")
        if isinstance(width, int) and isinstance(height, int) and width >= 800 and height >= 600:
            self.resize(width, height)

        splitter_sizes = window_data.get("splitter_sizes")
        if isinstance(splitter_sizes, list) and splitter_sizes and all(isinstance(value, int) for value in splitter_sizes):
            self.splitter.setSizes(splitter_sizes)

        settings = data.get("settings", {})
        interval = settings.get("interval_slider")
        if isinstance(interval, int):
            self.interval_slider.setValue(max(self.interval_slider.minimum(), min(self.interval_slider.maximum(), interval)))

        fade_ms = settings.get("fade_ms") or settings.get("transition_ms")
        if isinstance(fade_ms, int):
            self.fade_spin.setValue(max(self.fade_spin.minimum(), min(self.fade_spin.maximum(), fade_ms)))

        shuffle = settings.get("shuffle")
        if isinstance(shuffle, bool):
            self.shuffle_button.setChecked(shuffle)

        background_color = settings.get("background_color")
        if isinstance(background_color, str):
            candidate = QColor(background_color)
            if candidate.isValid():
                candidate.setAlpha(255)
                self._background_color = candidate
                self._apply_main_window_style()

        resolution_index = settings.get("resolution_index")
        if isinstance(resolution_index, int) and 0 <= resolution_index < self.resolution_combo.count():
            self.resolution_combo.setCurrentIndex(resolution_index)

        aspect_index = settings.get("aspect_index")
        if isinstance(aspect_index, int) and 0 <= aspect_index < self.aspect_combo.count():
            self.aspect_combo.setCurrentIndex(aspect_index)

        custom_aspect = settings.get("custom_aspect", {})
        custom_width = custom_aspect.get("width")
        custom_height = custom_aspect.get("height")
        if isinstance(custom_width, int):
            self.aspect_width_spin.setValue(max(self.aspect_width_spin.minimum(), min(self.aspect_width_spin.maximum(), custom_width)))
        if isinstance(custom_height, int):
            self.aspect_height_spin.setValue(max(self.aspect_height_spin.minimum(), min(self.aspect_height_spin.maximum(), custom_height)))

        canvas_data = data.get("canvas", {})
        manual_pan_data = canvas_data.get("manual_pan", {})
        loaded_manual_pan: dict[str, QPointF] = {}
        if isinstance(manual_pan_data, dict):
            for photo_path, offsets in manual_pan_data.items():
                if not isinstance(photo_path, str) or not isinstance(offsets, dict):
                    continue
                x = offsets.get("x")
                y = offsets.get("y")
                if isinstance(x, (int, float)) and isinstance(y, (int, float)):
                    loaded_manual_pan[photo_path] = QPointF(float(x), float(y))
        self.canvas.set_manual_pan_state(loaded_manual_pan)

        manual_zoom_data = canvas_data.get("manual_zoom", {})
        loaded_manual_zoom: dict[str, float] = {}
        if isinstance(manual_zoom_data, dict):
            for photo_path, zoom_factor in manual_zoom_data.items():
                if isinstance(photo_path, str) and isinstance(zoom_factor, (int, float)):
                    loaded_manual_zoom[photo_path] = float(zoom_factor)
        self.canvas.set_manual_zoom_state(loaded_manual_zoom)

        library = data.get("library", {})
        folder = library.get("folder")
        current_photo_path = library.get("current_photo_path")
        photo_transitions_data = library.get("photo_transitions", {})
        if isinstance(photo_transitions_data, dict):
            for photo in self.filtered_photos:
                stored = photo_transitions_data.get(str(photo.path))
                if isinstance(stored, dict):
                    style = stored.get("style")
                    if isinstance(style, str):
                        # 後方互換: 旧形式の "wipe" + wipe_direction
                        if style == "wipe":
                            wipe_dir = stored.get("wipe_direction", "right")
                            style = f"wipe_{wipe_dir}"
                        photo.transition_style = style
                    duration = stored.get("duration_ms")
                    if isinstance(duration, int):
                        photo.transition_duration_ms = duration
                elif isinstance(stored, str):
                    # 後方互換: 旧形式のスタイルのみ
                    photo.transition_style = stored
        if isinstance(folder, str) and folder:
            folder_path = Path(folder)
            if folder_path.exists() and folder_path.is_dir():
                self.load_folder(folder_path)
                if isinstance(current_photo_path, str) and current_photo_path:
                    current_index = next(
                        (
                            index
                            for index, photo in enumerate(self.filtered_photos)
                            if str(photo.path) == current_photo_path
                        ),
                        -1,
                    )
                    if current_index >= 0:
                        self.thumbnail_list.setCurrentRow(current_index)
        return True

    def _save_state_to_file(self) -> None:
        default_path = str(self._state_file_path())
        file_path, _ = QFileDialog.getSaveFileName(
            self,
            "設定を保存",
            default_path,
            "JSON Files (*.json)",
        )
        if not file_path:
            return
        if not file_path.lower().endswith(".json"):
            file_path = f"{file_path}.json"

        if self._save_app_state(Path(file_path)):
            self.statusBar().showMessage(f"設定を保存しました: {file_path}")
        else:
            self._show_warning("保存エラー", "設定ファイルを保存できませんでした。")

    def _load_state_from_file(self) -> None:
        default_path = str(self._state_file_path())
        file_path, _ = QFileDialog.getOpenFileName(
            self,
            "設定ファイルを読み込む",
            default_path,
            "JSON Files (*.json)",
        )
        if not file_path:
            return

        if self._load_app_state(Path(file_path)):
            self.statusBar().showMessage(f"設定を読み込みました: {file_path}")
        else:
            self._show_warning("読込エラー", "設定ファイルを読み込めませんでした。")

    def closeEvent(self, event) -> None:  # type: ignore[override]
        self._save_app_state()
        super().closeEvent(event)

    def _build_ui(self) -> None:
        root = QWidget()
        root.setObjectName("root")
        root.setAutoFillBackground(True)
        self.root_widget = root
        self._apply_main_window_style()
        root_layout = QVBoxLayout(root)
        root_layout.setContentsMargins(0, 0, 0, 0)
        root_layout.setSpacing(0)

        title = QLabel("LumiSlide(仮)")
        title.setObjectName("headline")
        title.setFont(QFont("Georgia", 16))
        title.setContentsMargins(20, 8, 0, 8)
        title.setFixedHeight(title.sizeHint().height() + 16)
        title.setFixedWidth(220)

        version_label = QLabel("Ver.Beta")
        version_label.setObjectName("subhead")
        version_label.setContentsMargins(0, 8, 0, 8)
        version_label.setFixedHeight(version_label.sizeHint().height() + 16)
        version_label.setFixedWidth(90)

        self.hero_panel = GlassPanel()
        hero_layout = QVBoxLayout(self.hero_panel)
        hero_layout.setContentsMargins(14, 4, 14, 4)
        hero_layout.setSpacing(0)

        # --- 1段目: 再生操作 + トランジション ---
        row1 = QHBoxLayout()
        row1.setSpacing(10)

        self.open_button = QPushButton("画像フォルダ選択")
        self.open_button.clicked.connect(self.choose_folder)

        self.play_button = QToolButton()
        self.play_button.setText("再生(F5)")
        self.play_button.setCheckable(True)
        self.play_button.clicked.connect(self.toggle_slideshow)

        self.prev_button = QToolButton()
        self.prev_button.setText("前へ")
        self.prev_button.clicked.connect(self.show_previous_photo)

        self.next_button = QToolButton()
        self.next_button.setText("次へ")
        self.next_button.clicked.connect(self.show_next_photo)

        self.rotate_left_button = QToolButton()
        self.rotate_left_button.setText("左回転")
        self.rotate_left_button.clicked.connect(lambda: self._rotate_current_photo(-1))

        self.rotate_right_button = QToolButton()
        self.rotate_right_button.setText("右回転")
        self.rotate_right_button.clicked.connect(lambda: self._rotate_current_photo(1))

        self.center_photo_button = QToolButton()
        self.center_photo_button.setText("中央")
        self.center_photo_button.clicked.connect(self._center_current_photo)

        self.shuffle_button = QToolButton()
        self.shuffle_button.setText("シャッフル")
        self.shuffle_button.setCheckable(True)
        self.shuffle_button.toggled.connect(self._on_shuffle_toggled)

        transition_label = QLabel("トランジション")
        transition_label.setObjectName("subhead")

        self.transition_combo = QComboBox()
        self.transition_combo.setMinimumWidth(150)
        for label, value in TRANSITION_STYLES:
            self.transition_combo.addItem(label, value)
        self.transition_combo.setCurrentIndex(0)
        self.transition_combo.currentIndexChanged.connect(self._on_transition_changed)

        self.direction_combo = QComboBox()
        self.direction_combo.setMinimumWidth(100)
        for label, value in DIRECTION_CHOICES:
            self.direction_combo.addItem(label, value)
        self.direction_combo.setCurrentIndex(0)
        self.direction_combo.setEnabled(False)
        self.direction_combo.currentIndexChanged.connect(self._on_direction_changed)

        self.direction_label = QLabel("方向")
        self.direction_label.setObjectName("subhead")
        self.direction_label.setEnabled(False)

        self.apply_transition_to_all_button = QPushButton("一括適用")
        self.apply_transition_to_all_button.setFixedWidth(80)
        self.apply_transition_to_all_button.clicked.connect(self._apply_transition_to_all_photos)

        interval_label = QLabel("切替")
        interval_label.setObjectName("subhead")

        self.interval_value_label = QLabel("4.0秒")
        self.interval_value_label.setObjectName("subhead")

        self.interval_slider = QSlider(Qt.Orientation.Horizontal)
        self.interval_slider.setRange(20, 100)
        self.interval_slider.setValue(40)
        self.interval_slider.setFixedWidth(120)
        self.interval_slider.valueChanged.connect(self._update_interval_label)

        fade_label = QLabel("トランジション時間")
        fade_label.setObjectName("subhead")

        self.fade_spin = QSpinBox()
        self.fade_spin.setRange(0, 5000)
        self.fade_spin.setSpecialValueText("なし")
        self.fade_spin.setSuffix(" ms")
        self.fade_spin.setSingleStep(50)
        self.fade_spin.setValue(1200)
        self.fade_spin.setFixedWidth(110)
        self.fade_spin.valueChanged.connect(self._on_fade_duration_changed)

        aspect_label = QLabel("マスク")
        aspect_label.setObjectName("subhead")

        self.aspect_combo = QComboBox()
        self.aspect_combo.setMinimumWidth(120)
        for label, value in ASPECT_PRESETS:
            self.aspect_combo.addItem(label, value)
        self.aspect_combo.currentIndexChanged.connect(self._on_aspect_changed)

        self.aspect_width_spin = QSpinBox()
        self.aspect_width_spin.setRange(1, 10000)
        self.aspect_width_spin.setValue(9)
        self.aspect_width_spin.setSuffix(" w")
        self.aspect_width_spin.setFixedWidth(86)
        self.aspect_width_spin.valueChanged.connect(self._on_custom_aspect_changed)

        self.aspect_height_spin = QSpinBox()
        self.aspect_height_spin.setRange(1, 10000)
        self.aspect_height_spin.setValue(16)
        self.aspect_height_spin.setSuffix(" h")
        self.aspect_height_spin.setFixedWidth(86)
        self.aspect_height_spin.valueChanged.connect(self._on_custom_aspect_changed)

        resolution_label = QLabel("画面サイズ")
        resolution_label.setObjectName("subhead")

        self.resolution_combo = QComboBox()
        self.resolution_combo.setMinimumWidth(160)
        for label, value in DISPLAY_PRESETS:
            self.resolution_combo.addItem(label, value)
        self.resolution_combo.currentIndexChanged.connect(self._on_resolution_preset_changed)

        self.background_color_label = QLabel("キャンバス背景")
        self.background_color_label.setObjectName("subhead")

        self.background_color_button = QPushButton()
        self.background_color_button.setFixedWidth(110)
        self.background_color_button.clicked.connect(self._choose_background_color)
        self._update_background_color_button()

        # --- 1段メニュー ---
        row1.addWidget(transition_label)
        row1.addWidget(self.transition_combo)
        row1.addWidget(self.direction_label)
        row1.addWidget(self.direction_combo)
        row1.addWidget(fade_label)
        row1.addWidget(self.fade_spin)
        row1.addWidget(self.apply_transition_to_all_button)
        row1.addSpacing(10)
        row1.addWidget(interval_label)
        row1.addWidget(self.interval_slider)
        row1.addWidget(self.interval_value_label)
        row1.addSpacing(10)
        row1.addWidget(resolution_label)
        row1.addWidget(self.resolution_combo)
        row1.addSpacing(10)
        row1.addWidget(aspect_label)
        row1.addWidget(self.aspect_combo)
        row1.addWidget(self.aspect_width_spin)
        row1.addWidget(self.aspect_height_spin)
        row1.addStretch(1)

        hero_layout.addLayout(row1)

        self.top_bar_widget = QWidget()
        top_bar = QHBoxLayout(self.top_bar_widget)
        top_bar.setContentsMargins(0, 0, 0, 0)
        top_bar.setSpacing(0)
        top_bar.addWidget(title)
        top_bar.addWidget(version_label)
        top_bar.addWidget(self.hero_panel, 1)
        root_layout.addWidget(self.top_bar_widget)

        self.splitter = QSplitter(Qt.Orientation.Horizontal)
        self.splitter.setHandleWidth(0)
        self.sidebar_panel = self._build_sidebar()
        self.viewer_panel = self._build_viewer()
        self.splitter.addWidget(self.sidebar_panel)
        self.splitter.addWidget(self.viewer_panel)
        self.splitter.setStretchFactor(0, 0)
        self.splitter.setStretchFactor(1, 1)
        self.splitter.setSizes([300, 1040])

        root_layout.addWidget(self.splitter, 1)

        self.setCentralWidget(root)

        status = QStatusBar()
        self.setStatusBar(status)
        self.clear_status_button = QToolButton()
        self.clear_status_button.setText("ステータス削除")
        self.clear_status_button.clicked.connect(self._clear_status_message)
        self.statusBar().addPermanentWidget(self.clear_status_button)
        self.statusBar().messageChanged.connect(self._sync_status_button_state)
        self.statusBar().showMessage("フォルダを開いて画像を読み込んでください")
        self._sync_status_button_state(self.statusBar().currentMessage())
        self.resolution_combo.setCurrentIndex(3)
        self._on_resolution_preset_changed()
        self._on_aspect_changed()
        self._on_fade_duration_changed()
        self._update_actual_display_size_label()
        self.canvas.set_fade_zoom_enabled(False)
        self.canvas.set_transition_style(TRANSITION_STYLE)

    def _build_sidebar(self) -> QWidget:
        panel = GlassPanel()
        panel.setMinimumWidth(240)
        layout = QVBoxLayout(panel)
        layout.setContentsMargins(24, 22, 24, 22)
        layout.setSpacing(14)

        path_title = QLabel("FOLDER PATH")
        path_title.setObjectName("sectionTitle")

        self.path_label = QLabel("フォルダを開いてください")
        self.path_label.setWordWrap(True)
        self.path_label.setStyleSheet("color: rgba(180, 178, 200, 0.82);")

        file_actions = QVBoxLayout()
        file_actions.setSpacing(8)

        file_actions.addWidget(self.open_button)

        self.add_files_button = QPushButton("画像ファイル追加")
        self.add_files_button.clicked.connect(self.choose_files)
        file_actions.addWidget(self.add_files_button)

        self.save_state_button = QPushButton("保存")
        self.save_state_button.clicked.connect(self._save_state_to_file)

        self.load_state_button = QPushButton("ファイル読込")
        self.load_state_button.clicked.connect(self._load_state_from_file)

        self.export_mp4_button = QPushButton("MP4書出し")
        self.export_mp4_button.clicked.connect(self._export_slideshow_to_mp4)

        self.new_project_button = QPushButton("新規作成")
        self.new_project_button.clicked.connect(self._new_project)

        file_actions.addWidget(self.new_project_button)
        file_actions.addWidget(self.save_state_button)
        file_actions.addWidget(self.load_state_button)
        file_actions.addWidget(self.export_mp4_button)

        # --- 表示切替ボタン ---
        view_title = QLabel("表示モード")
        view_title.setObjectName("sectionTitle")

        view_actions = QHBoxLayout()
        view_actions.setSpacing(8)

        self.preview_mode_button = QPushButton("プレビュー")
        self.preview_mode_button.setCheckable(True)
        self.preview_mode_button.setChecked(True)
        self.preview_mode_button.clicked.connect(lambda: self._switch_view_mode("preview"))

        self.grid_mode_button = QPushButton("画像一覧")
        self.grid_mode_button.setCheckable(True)
        self.grid_mode_button.clicked.connect(lambda: self._switch_view_mode("grid"))

        view_actions.addWidget(self.preview_mode_button)
        view_actions.addWidget(self.grid_mode_button)

        expiry_title = QLabel("利用期限")
        expiry_title.setObjectName("sectionTitle")

        self.expiry_label = QLabel("未設定")
        self.expiry_label.setStyleSheet("color: rgba(180, 178, 200, 0.82);")

        expiry_actions = QHBoxLayout()
        expiry_actions.setSpacing(10)

        self.set_expiry_button = QPushButton("設定")
        self.set_expiry_button.clicked.connect(self._set_expiry_date)
        self.set_expiry_button.hide()

        self.clear_expiry_button = QPushButton("解除")
        self.clear_expiry_button.clicked.connect(self._clear_expiry_date)
        self.clear_expiry_button.hide()

        expiry_actions.addWidget(self.set_expiry_button)
        expiry_actions.addWidget(self.clear_expiry_button)

        info_card = QFrame()
        info_card.setStyleSheet(
            "QFrame { border-radius: 14px; background: rgba(255, 255, 255, 0.05); }"
        )
        info_layout = QVBoxLayout(info_card)
        info_layout.setContentsMargins(14, 14, 14, 14)
        info_layout.setSpacing(6)

        self.count_label = QLabel("0 photos")
        self.count_label.setFont(QFont("Segoe UI Semibold", 16))
        self.count_label.setStyleSheet("color: #e0e0ec;")

        self.selection_label = QLabel("ライブラリ未選択")
        self.selection_label.setWordWrap(True)
        self.selection_label.setStyleSheet("color: rgba(180, 178, 200, 0.82);")

        self.tip_label = QLabel("ヒント: Spaceで再生、左右キーで送り戻し")
        self.tip_label.setWordWrap(True)
        self.tip_label.setStyleSheet("color: rgba(140, 138, 168, 0.72);")

        info_layout.addWidget(self.count_label)
        info_layout.addWidget(self.selection_label)
        info_layout.addWidget(self.tip_label)

        copyright_label = QLabel("© Pleine since2026")
        copyright_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        copyright_label.setStyleSheet("color: white; font-size: 11px;")

        layout.addWidget(path_title)
        layout.addWidget(self.path_label)
        layout.addLayout(file_actions)
        layout.addWidget(view_title)
        layout.addLayout(view_actions)
        layout.addWidget(expiry_title)
        layout.addWidget(self.expiry_label)
        layout.addLayout(expiry_actions)
        layout.addStretch(1)
        layout.addWidget(info_card)
        layout.addWidget(copyright_label)
        return panel

    def _build_viewer(self) -> QWidget:
        wrapper = QWidget()
        layout = QVBoxLayout(wrapper)
        self.viewer_layout = layout
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(4)

        self.canvas_panel = GlassPanel()
        canvas_layout = QVBoxLayout(self.canvas_panel)
        canvas_layout.setContentsMargins(0, 0, 0, 0)
        canvas_layout.setSpacing(0)

        self.canvas = PhotoCanvas()

        self.metadata_card = QFrame()
        self.metadata_card.setStyleSheet(
            "QFrame { border-top: 1px solid rgba(255,255,255,0.06); background: rgba(22, 22, 30, 0.95); }"
        )
        metadata_layout = QVBoxLayout(self.metadata_card)
        metadata_layout.setContentsMargins(16, 6, 16, 6)
        metadata_layout.setSpacing(2)

        self.photo_title = QLabel("No Selection")
        self.photo_title.setFont(QFont("Segoe UI", 14))
        self.photo_title.setStyleSheet("color: #e0e0ec;")

        self.photo_meta = QLabel("画像の解像度や日時がここに出ます")
        self.photo_meta.setStyleSheet("color: white; font-size: 14px;")

        metadata_layout.addWidget(self.photo_title)
        metadata_layout.addWidget(self.photo_meta)

        canvas_layout.addWidget(self.canvas, 1)
        canvas_layout.addWidget(self.metadata_card)

        self.playback_bar = QWidget()
        playback_bar_layout = QHBoxLayout(self.playback_bar)
        playback_bar_layout.setContentsMargins(14, 4, 14, 4)
        playback_bar_layout.setSpacing(10)
        playback_bar_layout.addStretch(1)
        playback_bar_layout.addWidget(self.prev_button)
        playback_bar_layout.addWidget(self.next_button)
        playback_bar_layout.addWidget(self.shuffle_button)
        playback_bar_layout.addWidget(self.play_button)
        self.preview_zoom_label = QLabel("ズーム")
        self.preview_zoom_label.setObjectName("subhead")

        self.preview_zoom_out_button = QToolButton()
        self.preview_zoom_out_button.setText("-")
        self.preview_zoom_out_button.clicked.connect(lambda: self._change_preview_zoom(-PREVIEW_ZOOM_STEP))

        self.preview_zoom_spin = QSpinBox()
        self.preview_zoom_spin.setRange(10, 100)
        self.preview_zoom_spin.setSingleStep(1)
        self.preview_zoom_spin.setSuffix("%")
        self.preview_zoom_spin.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.preview_zoom_spin.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.NoButtons)
        self.preview_zoom_spin.setFixedWidth(78)
        self.preview_zoom_spin.valueChanged.connect(self._on_preview_zoom_changed)

        self.preview_zoom_in_button = QToolButton()
        self.preview_zoom_in_button.setText("+")
        self.preview_zoom_in_button.clicked.connect(lambda: self._change_preview_zoom(PREVIEW_ZOOM_STEP))

        playback_bar_layout.addSpacing(10)
        playback_bar_layout.addWidget(self.preview_zoom_label)
        playback_bar_layout.addWidget(self.preview_zoom_out_button)
        playback_bar_layout.addWidget(self.preview_zoom_spin)
        playback_bar_layout.addWidget(self.preview_zoom_in_button)
        playback_bar_layout.addWidget(self.rotate_left_button)
        playback_bar_layout.addWidget(self.rotate_right_button)
        playback_bar_layout.addWidget(self.center_photo_button)
        playback_bar_layout.addWidget(self.background_color_label)
        playback_bar_layout.addWidget(self.background_color_button)
        playback_bar_layout.addStretch(1)

        self.grid_playback_gap = QWidget()
        self.grid_playback_gap.setFixedHeight(12)
        self.grid_playback_gap.hide()

        self.film_panel = GlassPanel()
        film_layout = QVBoxLayout(self.film_panel)
        film_layout.setContentsMargins(14, 10, 14, 10)
        film_layout.setSpacing(12)

        strip_title = QLabel("FILM STRIP")
        strip_title.setObjectName("sectionTitle")

        self.thumbnail_list = ThumbnailList()
        self.thumbnail_list.currentRowChanged.connect(self._display_photo_by_index)
        self.thumbnail_list.itemSelectionChanged.connect(self._on_thumbnail_selection_changed)
        self.thumbnail_list.resized.connect(self._on_thumbnail_list_resized)
        self.thumbnail_list.reordered.connect(self._on_thumbnail_reordered)
        self.thumbnail_list.itemDoubleClicked.connect(self._on_thumbnail_double_clicked)
        self.thumbnail_list.gapSelected.connect(self._on_gap_selected)
        self.thumbnail_list.filesDropped.connect(self._on_files_dropped)
        self._grid_view_active = False

        film_layout.addWidget(strip_title)
        film_layout.addWidget(self.thumbnail_list)

        layout.addWidget(self.canvas_panel, 5)
        layout.addWidget(self.playback_bar)
        layout.addWidget(self.grid_playback_gap)
        layout.addWidget(self.film_panel, 2)
        layout.setStretch(0, 5)
        layout.setStretch(1, 0)
        layout.setStretch(2, 0)
        layout.setStretch(3, 2)
        self._update_preview_zoom_controls()
        self._set_preview_zoom_controls_visible(True)
        return wrapper

    def _install_shortcuts(self) -> None:
        QShortcut(QKeySequence(Qt.Key.Key_Space), self, activated=self.play_button.click)
        QShortcut(QKeySequence(Qt.Key.Key_Right), self, activated=self.show_next_photo)
        QShortcut(QKeySequence(Qt.Key.Key_Left), self, activated=self.show_previous_photo)
        QShortcut(QKeySequence(Qt.Key.Key_Escape), self, activated=self.exit_playback_mode)
        QShortcut(QKeySequence(Qt.Key.Key_F5), self, activated=self._toggle_fullscreen)
        QShortcut(QKeySequence.StandardKey.Open, self, activated=self.choose_folder)
        QShortcut(QKeySequence.StandardKey.Undo, self, activated=self._undo)
        QShortcut(QKeySequence.StandardKey.Copy, self, activated=self._copy_thumbnail)
        QShortcut(QKeySequence.StandardKey.Paste, self, activated=self._paste_thumbnail)
        QShortcut(QKeySequence.StandardKey.Delete, self, activated=self._delete_thumbnail)
        QShortcut(QKeySequence("Ctrl+Alt+P"), self, activated=self._toggle_clear_expiry_button)

    def _save_undo(self) -> None:
        snapshot = (
            self.current_index,
            [
                (
                    str(p.path), p.width, p.height, p.modified_at.isoformat(),
                    p.transition_style, p.transition_duration_ms, p.rotation_quadrants,
                )
                for p in self.filtered_photos
            ],
        )
        self._undo_stack.append(snapshot)
        if len(self._undo_stack) > self._max_undo:
            self._undo_stack.pop(0)

    def _undo(self) -> None:
        if not self._undo_stack:
            self.statusBar().showMessage("元に戻す操作はありません")
            return
        prev_index, prev_state = self._undo_stack.pop()
        restored = []
        for path_str, width, height, modified_at, style, duration, rotation_quadrants in prev_state:
            restored.append(
                PhotoItem(
                    path=Path(path_str),
                    width=width,
                    height=height,
                    modified_at=datetime.fromisoformat(modified_at),
                    transition_style=style,
                    transition_duration_ms=duration,
                    rotation_quadrants=rotation_quadrants,
                )
            )
        self.filtered_photos = restored
        self._populate_thumbnails()
        target = min(prev_index, len(self.filtered_photos) - 1)
        if target >= 0:
            self._select_thumbnail_rows([target], current_row=target)
        self.statusBar().showMessage("元に戻しました")

    def _clone_photo_item(self, photo: PhotoItem) -> PhotoItem:
        return PhotoItem(
            path=photo.path,
            width=photo.width,
            height=photo.height,
            modified_at=photo.modified_at,
            transition_style=photo.transition_style,
            transition_duration_ms=photo.transition_duration_ms,
            rotation_quadrants=photo.rotation_quadrants,
        )

    def _selected_thumbnail_indexes(self) -> list[int]:
        return sorted(
            {
                self.thumbnail_list.row(item)
                for item in self.thumbnail_list.selectedItems()
                if self.thumbnail_list.row(item) >= 0
            }
        )

    def _command_target_indexes(self) -> list[int]:
        selected_indexes = self._selected_thumbnail_indexes()
        if selected_indexes:
            return selected_indexes
        if 0 <= self.current_index < len(self.filtered_photos):
            return [self.current_index]
        return []

    def _apply_selection_summary(self) -> None:
        total = len(self.filtered_photos)
        if total <= 0:
            return
        selected_count = len(self._selected_thumbnail_indexes())
        if selected_count <= 0:
            self.selection_label.setText(f"全{total}枚")
        elif selected_count == 1:
            self.selection_label.setText(f"1枚選択中 / 全{total}枚")
        else:
            self.selection_label.setText(f"{selected_count}枚選択中 / 全{total}枚")

    def _select_thumbnail_rows(self, rows: list[int], current_row: int | None = None) -> None:
        valid_rows = sorted({row for row in rows if 0 <= row < self.thumbnail_list.count()})
        anchor_row = current_row if current_row is not None else (valid_rows[0] if valid_rows else -1)
        if anchor_row >= 0 and anchor_row not in valid_rows:
            valid_rows.append(anchor_row)
            valid_rows.sort()

        self.thumbnail_list.blockSignals(True)
        self.thumbnail_list.clearSelection()
        if 0 <= anchor_row < self.thumbnail_list.count():
            self.thumbnail_list.setCurrentRow(anchor_row, QItemSelectionModel.SelectionFlag.ClearAndSelect)
        for row in valid_rows:
            item = self.thumbnail_list.item(row)
            if item is not None:
                item.setSelected(True)
        self.thumbnail_list.blockSignals(False)

        if 0 <= anchor_row < len(self.filtered_photos):
            self._display_photo_by_index(anchor_row)
        else:
            self._apply_selection_summary()

    def _on_thumbnail_selection_changed(self) -> None:
        if self.thumbnail_list._selected_gap >= 0 and self._selected_thumbnail_indexes():
            self.thumbnail_list._selected_gap = -1
            self.thumbnail_list.viewport().update()
        self._apply_selection_summary()

    def _copy_thumbnail(self) -> None:
        target_indexes = self._command_target_indexes()
        if not target_indexes:
            self.statusBar().showMessage("コピーする画像がありません")
            return
        self._clipboard_photos = [self._clone_photo_item(self.filtered_photos[index]) for index in target_indexes]
        if len(target_indexes) == 1:
            self.statusBar().showMessage("コピーしました")
        else:
            self.statusBar().showMessage(f"{len(target_indexes)}枚をコピーしました")

    def _paste_thumbnail(self) -> None:
        if not self._clipboard_photos:
            self.statusBar().showMessage("ペーストする画像がありません")
            return
        self._save_undo()
        target_indexes = self._command_target_indexes()
        insert_at = max(target_indexes) + 1 if target_indexes else len(self.filtered_photos)
        for offset, photo in enumerate(self._clipboard_photos):
            self.filtered_photos.insert(insert_at + offset, self._clone_photo_item(photo))
        self._populate_thumbnails()
        inserted_rows = list(range(insert_at, insert_at + len(self._clipboard_photos)))
        self._select_thumbnail_rows(inserted_rows, current_row=inserted_rows[-1])
        self.count_label.setText(f"{len(self.filtered_photos)} photos")
        if len(inserted_rows) == 1:
            self.statusBar().showMessage("ペーストしました")
        else:
            self.statusBar().showMessage(f"{len(inserted_rows)}枚をペーストしました")

    def _photo_pixmap(self, photo: PhotoItem) -> QPixmap:
        return _rotate_pixmap_quadrants(QPixmap(str(photo.path)), photo.rotation_quadrants)

    def _update_thumbnail_icon(self, index: int) -> None:
        if not (0 <= index < len(self.filtered_photos)):
            return
        item = self.thumbnail_list.item(index)
        if item is None:
            return
        photo = self.filtered_photos[index]
        thumb = self._photo_pixmap(photo).scaled(
            THUMBNAIL_SIZE,
            Qt.AspectRatioMode.KeepAspectRatioByExpanding,
            Qt.TransformationMode.SmoothTransformation,
        )
        item.setIcon(QIcon(self._rounded_pixmap(thumb, 18)))

    def _rotate_current_photo(self, delta_quadrants: int) -> None:
        target_indexes = self._command_target_indexes()
        if not target_indexes:
            self.statusBar().showMessage("回転する画像がありません")
            return
        self._save_undo()
        for index in target_indexes:
            photo = self.filtered_photos[index]
            photo.rotation_quadrants = _normalize_rotation_quadrants(photo.rotation_quadrants + delta_quadrants)
            self._update_thumbnail_icon(index)
        anchor_index = self.current_index if self.current_index in target_indexes else target_indexes[-1]
        self._select_thumbnail_rows(target_indexes, current_row=anchor_index)
        if len(target_indexes) == 1:
            self.statusBar().showMessage("画像を回転しました")
        else:
            self.statusBar().showMessage(f"{len(target_indexes)}枚の画像を回転しました")

    def _center_current_photo(self) -> None:
        if not (0 <= self.current_index < len(self.filtered_photos)):
            self.statusBar().showMessage("中央に戻す画像がありません")
            return

        photo = self.filtered_photos[self.current_index]
        manual_pan = self.canvas.manual_pan_state()
        manual_pan[str(photo.path)] = QPointF(0.0, 0.0)
        self.canvas.set_manual_pan_state(manual_pan)
        self.statusBar().showMessage("画像を中央に戻しました")

    def _delete_thumbnail(self) -> None:
        target_indexes = self._command_target_indexes()
        if not target_indexes:
            return
        self._save_undo()
        for index in reversed(target_indexes):
            self.filtered_photos.pop(index)
        self._populate_thumbnails()
        new_index = min(target_indexes[0], len(self.filtered_photos) - 1)
        if new_index >= 0:
            self._select_thumbnail_rows([new_index], current_row=new_index)
        self.count_label.setText(f"{len(self.filtered_photos)} photos")
        if len(target_indexes) == 1:
            self.statusBar().showMessage("削除しました")
        else:
            self.statusBar().showMessage(f"{len(target_indexes)}枚を削除しました")

    def _on_resolution_preset_changed(self) -> None:
        self._apply_display_resolution()

    def _on_aspect_changed(self) -> None:
        selected = self.aspect_combo.currentData()
        if isinstance(selected, tuple) and len(selected) == 2:
            width, height = selected
            if isinstance(width, int) and isinstance(height, int) and width > 0 and height > 0:
                self.canvas.set_display_aspect_ratio((width, height))
                self.aspect_width_spin.setReadOnly(True)
                self.aspect_height_spin.setReadOnly(True)
                self.aspect_width_spin.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.NoButtons)
                self.aspect_height_spin.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.NoButtons)
                self._update_actual_display_size_label()
                return

        if selected == "custom":
            self.aspect_width_spin.setReadOnly(False)
            self.aspect_height_spin.setReadOnly(False)
            self.aspect_width_spin.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.UpDownArrows)
            self.aspect_height_spin.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.UpDownArrows)
            self.aspect_width_spin.setSuffix(" w")
            self.aspect_height_spin.setSuffix(" h")
            self.canvas.set_display_aspect_ratio((self.aspect_width_spin.value(), self.aspect_height_spin.value()))
            self._update_actual_display_size_label()
            return

    def _on_custom_aspect_changed(self) -> None:
        if self.aspect_combo.currentData() != "custom":
            self.aspect_combo.blockSignals(True)
            self.aspect_combo.setCurrentIndex(self.aspect_combo.count() - 1)
            self.aspect_combo.blockSignals(False)
        self.aspect_width_spin.setSuffix(" w")
        self.aspect_height_spin.setSuffix(" h")
        self.aspect_width_spin.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.UpDownArrows)
        self.aspect_height_spin.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.UpDownArrows)
        self.aspect_width_spin.setReadOnly(False)
        self.aspect_height_spin.setReadOnly(False)
        self.canvas.set_display_aspect_ratio((self.aspect_width_spin.value(), self.aspect_height_spin.value()))
        self._update_actual_display_size_label()

    def _apply_display_resolution(self) -> None:
        selected = self.resolution_combo.currentData()
        if selected is None:
            resolution_size: QSize | None = None
            resolution_text = "画面に合わせる"
        else:
            resolution_size = selected
            resolution_text = f"{selected.width()} x {selected.height()}"

        # スライドショー中のみ選択したサイズを適用する。
        if self.is_playback_fullscreen:
            self.canvas.set_display_resolution(resolution_size)
        else:
            self.canvas.set_display_resolution(None)

        # 画面サイズの赤い破線ガイドを更新
        self.canvas.set_screen_size_for_border(resolution_size)

        if self.is_playback_fullscreen:
            self.statusBar().showMessage(f"全画面再生中 | 画面サイズ {resolution_text} | Escで終了")
        self._update_actual_display_size_label()

    def _update_actual_display_size_label(self) -> None:
        width, height = self._calculated_size_from_slideshow_and_aspect()
        # ショーサイズの枠線とホワイトアウト範囲用にキャンバスに通知
        self.canvas.set_show_size_for_border(QSize(width, height))
        if self.aspect_combo.currentData() != "custom":
            self.aspect_width_spin.blockSignals(True)
            self.aspect_height_spin.blockSignals(True)
            self.aspect_width_spin.setSuffix(" px")
            self.aspect_height_spin.setSuffix(" px")
            self.aspect_width_spin.setValue(width)
            self.aspect_height_spin.setValue(height)
            self.aspect_width_spin.blockSignals(False)
            self.aspect_height_spin.blockSignals(False)

    def _calculated_size_from_slideshow_and_aspect(self) -> tuple[int, int]:
        base_width, base_height = self._base_slideshow_size()
        ratio = self._selected_aspect_ratio_for_display()
        if ratio is None:
            return base_width, base_height

        ratio_width, ratio_height = ratio
        if ratio_width <= 0 or ratio_height <= 0:
            return base_width, base_height

        target_ratio = ratio_width / ratio_height
        base_ratio = base_width / base_height

        if base_ratio > target_ratio:
            fitted_height = base_height
            fitted_width = int(round(fitted_height * target_ratio))
        else:
            fitted_width = base_width
            fitted_height = int(round(fitted_width / target_ratio))

        return max(1, fitted_width), max(1, fitted_height)

    def _base_slideshow_size(self) -> tuple[int, int]:
        selected = self.resolution_combo.currentData()
        if isinstance(selected, QSize) and selected.width() > 0 and selected.height() > 0:
            return selected.width(), selected.height()

        rect = self.canvas.contentsRect()
        fallback_width = max(1, rect.width())
        fallback_height = max(1, rect.height())
        return fallback_width, fallback_height

    def _selected_aspect_ratio_for_display(self) -> tuple[int, int] | None:
        selected = self.aspect_combo.currentData()
        if isinstance(selected, tuple) and len(selected) == 2:
            width, height = selected
            if isinstance(width, int) and isinstance(height, int):
                return width, height

        if selected == "custom":
            return self.aspect_width_spin.value(), self.aspect_height_spin.value()

        return None

    def _update_interval_label(self) -> None:
        seconds = self.interval_slider.value() / 10
        self.interval_value_label.setText(f"{seconds:.1f}秒")
        if self.slideshow_timer.isActive():
            self.slideshow_timer.start(self._effective_slideshow_interval_ms())

    def _on_fade_duration_changed(self) -> None:
        duration = self.fade_spin.value()
        self.canvas.set_transition_duration_ms(duration)
        target_indexes = self._command_target_indexes()
        if target_indexes:
            self._save_undo()
            for index in target_indexes:
                self.filtered_photos[index].transition_duration_ms = duration
                self._update_thumbnail_label(index)
        if self.slideshow_timer.isActive():
            self.slideshow_timer.start(self._effective_slideshow_interval_ms())
        if self.is_playback_fullscreen:
            self.statusBar().showMessage(
                f"全画面再生中 | トランジション {self._format_transition_duration(duration)} | Escで終了"
            )

    def _get_effective_style(self) -> str:
        base = self.transition_combo.currentData() or "cut"
        direction = self.direction_combo.currentData() or ""
        if base in DIRECTIONAL_TRANSITIONS and direction:
            return f"{base}_{direction}"
        return base

    def _split_style(self, style: str) -> tuple[str, str]:
        for base in DIRECTIONAL_TRANSITIONS:
            if style.startswith(base + "_"):
                direction = style[len(base) + 1:]
                return base, direction
        return style, ""

    def _on_transition_changed(self) -> None:
        selected = self.transition_combo.currentData()
        if selected is not None:
            target_indexes = self._command_target_indexes()
            if target_indexes:
                self._save_undo()
            is_random = str(selected) == "random"
            # 方向コンボの有効/無効を切り替え
            is_directional = str(selected) in DIRECTIONAL_TRANSITIONS
            self.direction_combo.setEnabled(is_directional and not is_random)
            self.direction_label.setEnabled(is_directional and not is_random)
            if not is_directional or is_random:
                self.direction_combo.setCurrentIndex(0)

            effective = self._get_effective_style()
            self.canvas.set_transition_style(effective)
            for index in target_indexes:
                self.filtered_photos[index].transition_style = effective
                self._update_thumbnail_label(index)
            # ランダム・ホワイトアウト・カットはトランジションタイムに依存しない
            self.fade_spin.setEnabled(str(selected) not in ("white_out", "cut", "random"))
            # 方向ありトランジションは方向選択時にプレビューするのでここではスキップ
            if not is_directional or is_random:
                self.transition_combo.setEnabled(False)
                self.fade_spin.setEnabled(False)
                self._preview_current_transition()

    def _preview_current_transition(self) -> None:
        # プレビュー中はUI操作を無効化
        self.transition_combo.setEnabled(False)
        self.direction_combo.setEnabled(False)
        self.fade_spin.setEnabled(False)
        # トランジション効果をプレビュー。次の写真でトランジションを見せる
        show_size = self.resolution_combo.currentData()
        if show_size is not None:
            self.canvas.set_display_resolution(show_size)
        # 次の写真を取得
        next_pixmap = None
        next_path = None
        if len(self.filtered_photos) > 1:
            next_index = (self.current_index + 1) % len(self.filtered_photos)
            next_photo = self.filtered_photos[next_index]
            next_pixmap = self._photo_pixmap(next_photo)
            next_path = next_photo.path
        self.canvas.preview_transition(
            next_pixmap=next_pixmap,
            next_path=next_path,
            completion_callback=self._on_transition_preview_complete,
        )

    def _on_transition_preview_complete(self) -> None:
        """トランジションプレビュー完了後、1秒待ってからカットで元の写真に戻す。"""
        QTimer.singleShot(1000, self._restore_after_preview)

    def _restore_after_preview(self) -> None:
        self.canvas.restore_preview_display()
        if 0 <= self.current_index < len(self.filtered_photos):
            photo = self.filtered_photos[self.current_index]
            self.canvas.set_photo(photo.path, rotation_quadrants=photo.rotation_quadrants, animate=False)
            self.canvas.set_transition_style(photo.transition_style)
            self.canvas.set_transition_duration_ms(photo.transition_duration_ms)
        # プレビュー完了後にUI操作を再有効化
        self.transition_combo.setEnabled(True)
        selected = self.transition_combo.currentData()
        is_directional = str(selected) in DIRECTIONAL_TRANSITIONS if selected else False
        self.direction_combo.setEnabled(is_directional)
        self.direction_label.setEnabled(is_directional)
        self.fade_spin.setEnabled(str(selected) not in ("white_out", "cut", "random") if selected else True)

    def _on_direction_changed(self) -> None:
        target_indexes = self._command_target_indexes()
        if target_indexes:
            self._save_undo()
        effective = self._get_effective_style()
        self.canvas.set_transition_style(effective)
        for index in target_indexes:
            self.filtered_photos[index].transition_style = effective
            self._update_thumbnail_label(index)
        # プレビュー中はUI操作を無効化
        self.transition_combo.setEnabled(False)
        self.direction_combo.setEnabled(False)
        self.direction_label.setEnabled(False)
        self.fade_spin.setEnabled(False)
        # プレビュー実行
        self._preview_current_transition()

    def _apply_transition_to_all_photos(self) -> None:
        self._save_undo()
        effective = self._get_effective_style()
        duration = self.fade_spin.value()
        for photo in self.filtered_photos:
            photo.transition_style = effective
            photo.transition_duration_ms = duration
        self._update_all_thumbnail_labels()
        self.statusBar().showMessage(
            f"全画像にトランジション '{self.transition_combo.currentText()}' / {self._format_transition_duration(duration)} を適用しました"
        )

    def _effective_slideshow_interval_ms(self) -> int:
        """スライドショー間隔を計算（トランジション時間を必ず含める）。"""
        interval_ms = int((self.interval_slider.value() / 10) * 1000)
        transition_ms = self.fade_spin.value()
        # スライドショー間隔はトランジション時間以上に必ず設定
        return max(interval_ms, transition_ms)

    def _format_transition_duration(self, duration_ms: int) -> str:
        if duration_ms <= 0:
            return "なし"
        return f"{duration_ms / 1000:.2f}秒"

    def _thumbnail_label(self, photo: PhotoItem) -> str:
        style_map = {v: k for k, v in TRANSITION_STYLES}
        dir_map = {"right": "➤", "left": "◄", "down": "▼", "up": "▲"}
        base, direction = self._split_style(photo.transition_style)
        name = style_map.get(base, base)
        if base == "random":
            return f"{photo.label}\n{name}"
        if direction:
            name += f" {dir_map.get(direction, direction)}"
        elif base in DIRECTIONAL_TRANSITIONS:
            name += " R"
        if base not in ("cut", "white_out"):
            name += f" {photo.transition_duration_ms / 1000:.1f}s"
        return f"{photo.label}\n{name}"

    def _update_thumbnail_label(self, index: int) -> None:
        if 0 <= index < len(self.filtered_photos):
            item = self.thumbnail_list.item(index)
            if item:
                item.setText(self._thumbnail_label(self.filtered_photos[index]))

    def _update_all_thumbnail_labels(self) -> None:
        for i in range(len(self.filtered_photos)):
            self._update_thumbnail_label(i)

    def _ask_export_options(self) -> tuple[int, str, str] | None:
        dialog = QDialog(self)
        dialog.setWindowTitle("MP4書出し")
        dialog.setStyleSheet(self._dialog_style())

        layout = QVBoxLayout(dialog)
        layout.setContentsMargins(18, 18, 18, 18)
        layout.setSpacing(12)

        fps_label = QLabel("フレームレート (FPS):")
        fps_spin = QSpinBox()
        fps_spin.setRange(10, 60)
        fps_spin.setValue(30)
        fps_spin.setSingleStep(1)

        mode_label = QLabel("動画の書き出し方法:")
        mode_combo = QComboBox()
        mode_combo.addItem("表示領域のみ（クロップ）", "crop")
        mode_combo.addItem("黒味入り（レターボックス）", "letterbox")

        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel
        )
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)

        layout.addWidget(fps_label)
        layout.addWidget(fps_spin)
        layout.addWidget(mode_label)
        layout.addWidget(mode_combo)
        layout.addWidget(buttons)

        if dialog.exec() != QDialog.DialogCode.Accepted:
            return None

        selected_label = mode_combo.currentText()
        render_mode = str(mode_combo.currentData())
        return fps_spin.value(), selected_label, render_mode

    def _create_export_progress_dialog(self) -> tuple[QDialog, QLabel, QProgressBar, QLabel]:
        dialog = QDialog(self)
        dialog.setWindowTitle("MP4書出し中")
        dialog.setStyleSheet(self._dialog_style())
        dialog.setWindowModality(Qt.WindowModality.WindowModal)

        layout = QVBoxLayout(dialog)
        layout.setContentsMargins(18, 18, 18, 18)
        layout.setSpacing(10)

        title_label = QLabel("動画を書き出しています...")
        detail_label = QLabel("準備中")
        progress_bar = QProgressBar()
        progress_bar.setRange(0, 100)
        progress_bar.setValue(0)
        percent_label = QLabel("0%")
        percent_label.setAlignment(Qt.AlignmentFlag.AlignCenter)

        layout.addWidget(title_label)
        layout.addWidget(detail_label)
        layout.addWidget(progress_bar)
        layout.addWidget(percent_label)
        return dialog, detail_label, progress_bar, percent_label

    def _update_export_progress(
        self,
        progress_bar: QProgressBar,
        percent_label: QLabel,
        detail_label: QLabel,
        progress_value: int,
        detail: str,
    ) -> None:
        clamped = max(0, min(100, progress_value))
        progress_bar.setValue(clamped)
        percent_label.setText(f"{clamped}%")
        detail_label.setText(detail)
        QApplication.processEvents()

    def _export_slideshow_to_mp4(self) -> None:
        if not self.filtered_photos:
            self._show_info("画像がありません", "先に画像フォルダを開いてください。")
            return

        export_options = self._ask_export_options()
        if export_options is None:
            return
        fps, selected_label, render_mode = export_options

        default_folder = self.current_folder if self.current_folder is not None else Path.cwd()
        default_name = f"{default_folder.name or 'slideshow'}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.mp4"
        default_path = str(default_folder / default_name)
        file_path, _ = QFileDialog.getSaveFileName(
            self,
            "MP4を書き出し",
            default_path,
            "MP4 Files (*.mp4)",
        )
        if not file_path:
            return
        if not file_path.lower().endswith(".mp4"):
            file_path = f"{file_path}.mp4"

        output_path = Path(file_path)
        if render_mode == "letterbox":
            frame_width, frame_height = self._base_slideshow_size()
        else:
            frame_width, frame_height = self._calculated_size_from_slideshow_and_aspect()
        frame_width = max(2, frame_width - (frame_width % 2))
        frame_height = max(2, frame_height - (frame_height % 2))

        interval_ms = self._effective_slideshow_interval_ms()
        fade_ms = min(self.fade_spin.value(), interval_ms)
        interval_frames = max(1, int(round((interval_ms / 1000) * fps)))
        fade_frames = int(round((fade_ms / 1000) * fps)) if fade_ms > 0 else 0
        hold_frames = max(0, interval_frames - fade_frames)

        photos = list(self.filtered_photos)
        total_frames = 0
        for index in range(len(photos)):
            if index < len(photos) - 1:
                total_frames += hold_frames + fade_frames
            else:
                total_frames += interval_frames

        if total_frames <= 0:
            self._show_warning("書出しエラー", "動画のフレーム数が0です。設定を見直してください。")
            return

        progress_dialog, progress_detail_label, progress_bar, progress_percent_label = self._create_export_progress_dialog()
        progress_dialog.show()
        self.statusBar().showMessage(f"MP4書出しを開始しました（{selected_label}）")
        QApplication.processEvents()

        try:
            manual_pan_by_path = self.canvas.manual_pan_state()
            rendered_frames: list[np.ndarray] = []
            total_steps = len(photos) + total_frames
            completed_steps = 0

            for photo in photos:
                rendered_frames.append(
                    self._render_photo_for_video(photo, frame_width, frame_height, render_mode, manual_pan_by_path)
                )
                completed_steps += 1
                prep_progress = int((completed_steps / max(1, total_steps)) * 100)
                self._update_export_progress(
                    progress_bar,
                    progress_percent_label,
                    progress_detail_label,
                    prep_progress,
                    "フレーム準備中...",
                )

            with imageio.get_writer(
                str(output_path),
                format="FFMPEG",
                mode="I",
                fps=fps,
                codec="libx264",
                macro_block_size=None,
            ) as writer:
                frames_written = 0
                last_progress = -1
                for index, current_frame in enumerate(rendered_frames):
                    is_last = index == len(rendered_frames) - 1

                    if is_last:
                        for _ in range(interval_frames):
                            writer.append_data(current_frame)
                            frames_written += 1
                            completed_steps += 1
                            progress = int((completed_steps / max(1, total_steps)) * 100)
                            if progress != last_progress:
                                last_progress = progress
                                self._update_export_progress(
                                    progress_bar,
                                    progress_percent_label,
                                    progress_detail_label,
                                    progress,
                                    "動画を書き込み中...",
                                )
                    else:
                        for _ in range(hold_frames):
                            writer.append_data(current_frame)
                            frames_written += 1
                            completed_steps += 1
                            progress = int((completed_steps / max(1, total_steps)) * 100)
                            if progress != last_progress:
                                last_progress = progress
                                self._update_export_progress(
                                    progress_bar,
                                    progress_percent_label,
                                    progress_detail_label,
                                    progress,
                                    "動画を書き込み中...",
                                )

                        next_frame = rendered_frames[index + 1]
                        for fade_index in range(fade_frames):
                            alpha = (fade_index + 1) / fade_frames
                            blended = (
                                current_frame.astype(np.float32) * (1.0 - alpha)
                                + next_frame.astype(np.float32) * alpha
                            ).astype(np.uint8)
                            writer.append_data(blended)
                            frames_written += 1
                            completed_steps += 1
                            progress = int((completed_steps / max(1, total_steps)) * 100)
                            if progress != last_progress:
                                last_progress = progress
                                self._update_export_progress(
                                    progress_bar,
                                    progress_percent_label,
                                    progress_detail_label,
                                    progress,
                                    "動画を書き込み中...",
                                )

            self._update_export_progress(
                progress_bar,
                progress_percent_label,
                progress_detail_label,
                100,
                "完了",
            )
            self.statusBar().showMessage(f"MP4を書き出しました: {output_path}")
            self._show_info("書出し完了", f"MP4を書き出しました。\n{output_path}")
        except Exception as exc:
            self.statusBar().showMessage("MP4書出しに失敗しました")
            self._show_warning("書出しエラー", f"MP4の書出しに失敗しました。\n{exc}")
        finally:
            progress_dialog.close()

    def _aspect_cropped_source_rect_for_export(
        self,
        pixmap: QPixmap,
        path: Path,
        manual_pan_by_path: dict[str, QPointF],
    ) -> QRectF:
        source_rect = QRectF(pixmap.rect())
        ratio = self._selected_aspect_ratio_for_display()
        if ratio is None:
            return source_rect

        ratio_width, ratio_height = ratio
        if ratio_width <= 0 or ratio_height <= 0:
            return source_rect

        target_ratio = ratio_width / ratio_height
        source_ratio = source_rect.width() / source_rect.height()
        pan = manual_pan_by_path.get(str(path), QPointF(0.0, 0.0))

        if source_ratio > target_ratio:
            crop_width = source_rect.height() * target_ratio
            extra_x = max(0.0, source_rect.width() - crop_width)
            pan_x = max(-0.5, min(0.5, pan.x()))
            crop_x = source_rect.left() + (extra_x * (0.5 + pan_x))
            return QRectF(crop_x, source_rect.top(), crop_width, source_rect.height())

        crop_height = source_rect.width() / target_ratio
        extra_y = max(0.0, source_rect.height() - crop_height)
        pan_y = max(-0.5, min(0.5, pan.y()))
        crop_y = source_rect.top() + (extra_y * (0.5 + pan_y))
        return QRectF(source_rect.left(), crop_y, source_rect.width(), crop_height)

    def _render_photo_for_video(
        self,
        photo: PhotoItem,
        width: int,
        height: int,
        render_mode: str,
        manual_pan_by_path: dict[str, QPointF],
    ) -> np.ndarray:
        path = photo.path
        pixmap = _rotate_pixmap_quadrants(QPixmap(str(path)), photo.rotation_quadrants)
        if pixmap.isNull():
            raise ValueError(f"画像を読み込めません: {path}")

        source_rect = self._aspect_cropped_source_rect_for_export(pixmap, path, manual_pan_by_path)
        use_aspect_crop = self._selected_aspect_ratio_for_display() is not None

        if render_mode == "letterbox":
            image = QImage(width, height, QImage.Format.Format_RGB888)
            image.fill(QColor(0, 0, 0))
            painter = QPainter(image)
            painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)

            if use_aspect_crop:
                source_ratio = source_rect.width() / max(1.0, source_rect.height())
                target_ratio = width / max(1.0, height)
                if target_ratio > source_ratio:
                    draw_height = float(height)
                    draw_width = draw_height * source_ratio
                else:
                    draw_width = float(width)
                    draw_height = draw_width / source_ratio
                draw_rect = QRectF(
                    (width - draw_width) / 2,
                    (height - draw_height) / 2,
                    draw_width,
                    draw_height,
                )
                painter.drawPixmap(draw_rect, pixmap, source_rect)
            else:
                scaled = pixmap.scaled(
                    width,
                    height,
                    Qt.AspectRatioMode.KeepAspectRatio,
                    Qt.TransformationMode.SmoothTransformation,
                )
                offset_x = max(0, (width - scaled.width()) // 2)
                offset_y = max(0, (height - scaled.height()) // 2)
                painter.drawPixmap(offset_x, offset_y, scaled)

            painter.end()
        else:
            if use_aspect_crop:
                image = QImage(width, height, QImage.Format.Format_RGB888)
                image.fill(QColor(0, 0, 0))
                painter = QPainter(image)
                painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)
                painter.drawPixmap(QRectF(0.0, 0.0, float(width), float(height)), pixmap, source_rect)
                painter.end()
            else:
                scaled = pixmap.scaled(
                    width,
                    height,
                    Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                    Qt.TransformationMode.SmoothTransformation,
                )
                x = max(0, (scaled.width() - width) // 2)
                y = max(0, (scaled.height() - height) // 2)
                cropped = scaled.copy(x, y, width, height)
                image = cropped.toImage().convertToFormat(QImage.Format.Format_RGB888)

        ptr = image.bits()
        byte_count = image.sizeInBytes()
        data = np.frombuffer(bytes(ptr), dtype=np.uint8, count=byte_count)
        frame = data.reshape((height, width, 3)).copy()
        return frame

    def _clear_status_message(self) -> None:
        self.statusBar().clearMessage()

    def _sync_status_button_state(self, message: str) -> None:
        self.clear_status_button.setEnabled(bool(message.strip()))

    def choose_folder(self) -> None:
        folder = QFileDialog.getExistingDirectory(self, "画像フォルダを選択")
        if folder:
            self.load_folder(Path(folder))

    def choose_files(self) -> None:
        self._save_undo()
        suffix_filter = " ".join(f"*{s}" for s in sorted(SUPPORTED_SUFFIXES))
        files, _ = QFileDialog.getOpenFileNames(
            self, "画像ファイルを選択", "",
            f"画像ファイル ({suffix_filter})"
        )
        if not files:
            return
        existing_paths = {str(p.path) for p in self.filtered_photos}
        added = 0
        for f in files:
            path = Path(f)
            if str(path) in existing_paths:
                continue
            reader = QImageReader(str(path))
            size = reader.size()
            if not size.isValid():
                continue
            modified_at = datetime.fromtimestamp(path.stat().st_mtime)
            photo = PhotoItem(
                path=path, width=size.width(), height=size.height(),
                modified_at=modified_at,
            )
            self.photos.append(photo)
            self.filtered_photos.append(photo)
            existing_paths.add(str(path))
            added += 1
        if added > 0:
            self._populate_thumbnails()
            self.count_label.setText(f"{len(self.filtered_photos)} photos")
            self.statusBar().showMessage(f"{added}枚の画像を追加しました")

    def _on_files_dropped(self, paths: list, insert_index: int) -> None:
        self._save_undo()
        added = 0
        existing_paths = {str(p.path) for p in self.filtered_photos}
        for path in paths:
            if str(path) in existing_paths:
                continue
            reader = QImageReader(str(path))
            size = reader.size()
            if not size.isValid():
                continue
            modified_at = datetime.fromtimestamp(path.stat().st_mtime)
            photo = PhotoItem(
                path=path, width=size.width(), height=size.height(),
                modified_at=modified_at,
            )
            self.photos.append(photo)
            self.filtered_photos.insert(insert_index + added, photo)
            existing_paths.add(str(path))
            added += 1
        if added > 0:
            self._populate_thumbnails()
            target_row = min(insert_index, len(self.filtered_photos) - 1)
            self._select_thumbnail_rows([target_row], current_row=target_row)
            self.count_label.setText(f"{len(self.filtered_photos)} photos")
            self.statusBar().showMessage(f"{added}枚の画像をドロップで追加しました")

    def load_folder(self, folder: Path) -> None:
        self.current_folder = folder
        discovered = self._scan_photos(folder)
        self.photos = sorted(discovered, key=lambda item: item.modified_at, reverse=True)
        self.path_label.setText(str(folder))
        self.filtered_photos = list(self.photos)

        if not self.photos:
            self.filtered_photos = []
            self.current_index = -1
            self.thumbnail_list.clear()
            self.canvas.set_photo(None, animate=False)
            self.photo_title.setText("No Selection")
            self.photo_meta.setText("対応画像が見つかりませんでした")
            self.count_label.setText("0 photos")
            self.selection_label.setText("このフォルダには .jpg / .png などの画像がありません")
            self._update_preview_zoom_controls()
            self.statusBar().showMessage("画像が見つかりませんでした")
            return

        self._populate_thumbnails()
        self.count_label.setText(f"{len(self.photos)} photos")
        self._apply_selection_summary()
        self.statusBar().showMessage(f"{len(self.photos)}枚の画像を読み込みました")

    def _scan_photos(self, folder: Path) -> list[PhotoItem]:
        items: list[PhotoItem] = []
        for path in folder.rglob("*"):
            if not path.is_file() or path.suffix.lower() not in SUPPORTED_SUFFIXES:
                continue

            reader = QImageReader(str(path))
            size = reader.size()
            if not size.isValid():
                continue

            modified_at = datetime.fromtimestamp(path.stat().st_mtime)
            items.append(
                PhotoItem(
                    path=path,
                    width=size.width(),
                    height=size.height(),
                    modified_at=modified_at,
                )
            )
        return items

    def _populate_thumbnails(self) -> None:
        self._reset_photo_shuffle_cycle()
        self.thumbnail_list.blockSignals(True)
        self.thumbnail_list.clear()

        for photo in self.filtered_photos:
            thumb = self._photo_pixmap(photo).scaled(
                THUMBNAIL_SIZE,
                Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                Qt.TransformationMode.SmoothTransformation,
            )
            icon = QIcon(self._rounded_pixmap(thumb, 18))
            item = QListWidgetItem(icon, self._thumbnail_label(photo))
            item.setData(Qt.ItemDataRole.UserRole, str(photo.path))
            item.setTextAlignment(Qt.AlignmentFlag.AlignHCenter)
            self.thumbnail_list.addItem(item)

        self.thumbnail_list.blockSignals(False)

        if self.filtered_photos:
            self._select_thumbnail_rows([0], current_row=0)
            self._refresh_grid_thumbnail_layout()
        else:
            self.current_index = -1
            self.canvas.set_photo(None, animate=False)
            self.photo_title.setText("No Selection")
            self.photo_meta.setText("このアルバムに表示できる画像はありません")
            self._update_preview_zoom_controls()

    def _rounded_pixmap(self, source: QPixmap, radius: int) -> QPixmap:
        canvas = QPixmap(source.size())
        canvas.fill(Qt.GlobalColor.transparent)

        painter = QPainter(canvas)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        path = QPainterPath()
        path.addRoundedRect(QRect(0, 0, source.width(), source.height()), radius, radius)
        painter.setClipPath(path)
        painter.drawPixmap(0, 0, source)
        painter.end()
        return canvas

    def _reset_photo_shuffle_cycle(self) -> None:
        self._photo_shuffle_history.clear()
        self._photo_shuffle_deck.clear()

    def _remember_current_photo_for_shuffle(self) -> None:
        if not (0 <= self.current_index < len(self.filtered_photos)):
            return
        current_path = str(self.filtered_photos[self.current_index].path)
        if self._photo_shuffle_history and self._photo_shuffle_history[-1] == current_path:
            return
        self._photo_shuffle_history.append(current_path)
        if len(self._photo_shuffle_history) > 10:
            self._photo_shuffle_history = self._photo_shuffle_history[-5:]
        if current_path in self._photo_shuffle_deck:
            self._photo_shuffle_deck = [path for path in self._photo_shuffle_deck if path != current_path]

    def _on_shuffle_toggled(self, checked: bool) -> None:
        self._reset_photo_shuffle_cycle()
        if checked:
            self._remember_current_photo_for_shuffle()

    def _pick_next_shuffled_index(self) -> int:
        if len(self.filtered_photos) <= 1:
            return 0

        self._remember_current_photo_for_shuffle()
        current_path = ""
        if 0 <= self.current_index < len(self.filtered_photos):
            current_path = str(self.filtered_photos[self.current_index].path)

        all_paths = [str(photo.path) for photo in self.filtered_photos]
        remaining_paths = {path for path in all_paths if path != current_path}
        self._photo_shuffle_deck = [path for path in self._photo_shuffle_deck if path in remaining_paths]

        if not self._photo_shuffle_deck:
            self._photo_shuffle_deck = list(remaining_paths)
            random.shuffle(self._photo_shuffle_deck)

        recent = set(self._photo_shuffle_history[-2:])
        available = [path for path in self._photo_shuffle_deck if path not in recent]
        if not available:
            self._photo_shuffle_deck = list(remaining_paths)
            random.shuffle(self._photo_shuffle_deck)
            available = [path for path in self._photo_shuffle_deck if path not in recent]
            if not available:
                available = [path for path in self._photo_shuffle_deck if path != current_path]
            if not available:
                available = self._photo_shuffle_deck[:]

        next_path = random.choice(available)
        self._photo_shuffle_deck.remove(next_path)
        for index, photo in enumerate(self.filtered_photos):
            if str(photo.path) == next_path:
                return index

        return (self.current_index + 1) % len(self.filtered_photos)

    def _on_thumbnail_reordered(self) -> None:
        self._save_undo()
        path_to_photo = {str(p.path): p for p in self.filtered_photos}
        new_order = []
        for i in range(self.thumbnail_list.count()):
            item = self.thumbnail_list.item(i)
            path = item.data(Qt.ItemDataRole.UserRole)
            if path in path_to_photo:
                new_order.append(path_to_photo[path])
        if len(new_order) == len(self.filtered_photos):
            self.filtered_photos = new_order
            self.current_index = self.thumbnail_list.currentRow()

    def _on_gap_selected(self, gap_index: int) -> None:
        """ギャップ(写真と写真の間)がクリックされた時: gap_index番目の写真の次へのトランジションを表示。"""
        # gap_index + 1 の写真のトランジション設定を表示（次の写真への遷移）
        target = gap_index + 1
        if 0 <= target < len(self.filtered_photos):
            photo = self.filtered_photos[target]
            base_style, direction = self._split_style(photo.transition_style)

            self.transition_combo.blockSignals(True)
            combo_index = self.transition_combo.findData(base_style)
            if combo_index >= 0:
                self.transition_combo.setCurrentIndex(combo_index)
            self.transition_combo.blockSignals(False)

            is_directional = base_style in DIRECTIONAL_TRANSITIONS
            self.direction_combo.blockSignals(True)
            dir_index = self.direction_combo.findData(direction)
            if dir_index >= 0:
                self.direction_combo.setCurrentIndex(dir_index)
            self.direction_combo.blockSignals(False)
            self.direction_combo.setEnabled(is_directional)
            self.direction_label.setEnabled(is_directional)

            self.fade_spin.blockSignals(True)
            self.fade_spin.setValue(photo.transition_duration_ms)
            self.fade_spin.blockSignals(False)
            self.fade_spin.setEnabled(base_style not in ("cut", "white_out"))

            self.statusBar().showMessage(
                f"トランジション: {gap_index + 1} → {gap_index + 2} 枚目"
            )

    def _switch_view_mode(self, mode: str) -> None:
        if mode == "preview":
            self.canvas_panel.show()
            self.playback_bar.show()
            self.grid_playback_gap.hide()
            self.viewer_layout.setStretch(0, 5)
            self.viewer_layout.setStretch(1, 0)
            self.viewer_layout.setStretch(2, 0)
            self.viewer_layout.setStretch(3, 2)
            self.thumbnail_list.setWrapping(False)
            self.thumbnail_list.setFlow(QListWidget.Flow.LeftToRight)
            self.thumbnail_list.setIconSize(THUMBNAIL_SIZE)
            self.thumbnail_list.setGridSize(QSize())
            self._apply_thumbnail_item_size_hints(160, 164)
            self.thumbnail_list.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
            self.thumbnail_list.setHorizontalScrollMode(QListWidget.ScrollMode.ScrollPerPixel)
            self.thumbnail_list.updateGeometries()
            self.thumbnail_list.viewport().update()
            self.preview_mode_button.setChecked(True)
            self.grid_mode_button.setChecked(False)
            self._grid_view_active = False
            self._set_preview_zoom_controls_visible(True)
            self.center_photo_button.setVisible(True)
            self.background_color_label.setVisible(True)
            self.background_color_button.setVisible(True)
        else:
            self.canvas_panel.hide()
            self.playback_bar.show()
            self.grid_playback_gap.show()
            self.viewer_layout.setStretch(0, 0)
            self.viewer_layout.setStretch(1, 0)
            self.viewer_layout.setStretch(2, 0)
            self.viewer_layout.setStretch(3, 1)
            self.thumbnail_list.setWrapping(True)
            self.thumbnail_list.setFlow(QListWidget.Flow.LeftToRight)
            self.thumbnail_list.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
            self.thumbnail_list.setVerticalScrollMode(QListWidget.ScrollMode.ScrollPerPixel)
            self.preview_mode_button.setChecked(False)
            self.grid_mode_button.setChecked(True)
            self._grid_view_active = True
            self._set_preview_zoom_controls_visible(False)
            self.center_photo_button.setVisible(False)
            self.background_color_label.setVisible(False)
            self.background_color_button.setVisible(False)
            self._refresh_grid_thumbnail_layout()

    def _change_preview_zoom(self, delta: float) -> None:
        current_percent = self._current_preview_zoom_percent()
        self._set_current_photo_zoom_percent(current_percent + int(round(delta * 100)))

    def _on_preview_zoom_changed(self, value: int) -> None:
        self._set_current_photo_zoom_percent(value)

    def _current_preview_zoom_percent(self) -> int:
        if 0 <= self.current_index < len(self.filtered_photos):
            photo = self.filtered_photos[self.current_index]
            return int(round(self.canvas.manual_zoom_factor_for_path(photo.path) * 100))
        return 100

    def _set_current_photo_zoom_percent(self, percent: int) -> None:
        if 0 <= self.current_index < len(self.filtered_photos):
            photo = self.filtered_photos[self.current_index]
            clamped_percent = max(10, min(100, int(percent)))
            self.canvas.set_manual_zoom_factor_for_path(photo.path, clamped_percent / 100)
        self._update_preview_zoom_controls()

    def _update_preview_zoom_controls(self) -> None:
        has_photo = 0 <= self.current_index < len(self.filtered_photos)
        percent = self._current_preview_zoom_percent() if has_photo else 100
        self.preview_zoom_label.setEnabled(has_photo)
        self.preview_zoom_spin.blockSignals(True)
        self.preview_zoom_spin.setValue(percent)
        self.preview_zoom_spin.blockSignals(False)
        self.preview_zoom_spin.setEnabled(has_photo)
        self.preview_zoom_out_button.setEnabled(has_photo and percent > 10)
        self.preview_zoom_in_button.setEnabled(has_photo and percent < 100)

    def _set_preview_zoom_controls_visible(self, visible: bool) -> None:
        widgets = (
            self.preview_zoom_label,
            self.preview_zoom_out_button,
            self.preview_zoom_spin,
            self.preview_zoom_in_button,
        )
        for widget in widgets:
            widget.setVisible(visible)

    def _apply_thumbnail_item_size_hints(self, item_width: int, item_height: int) -> None:
        hint = QSize(item_width, item_height)
        for index in range(self.thumbnail_list.count()):
            item = self.thumbnail_list.item(index)
            if item is not None:
                item.setSizeHint(hint)

    def _refresh_grid_thumbnail_layout(self) -> None:
        if not getattr(self, '_grid_view_active', False):
            return
        viewport_width = max(1, self.thumbnail_list.viewport().width())
        spacing = self.thumbnail_list.spacing()
        target_tile_width = 180
        cols = max(1, min(8, viewport_width // target_tile_width))
        available_width = max(140, viewport_width - spacing * max(0, cols - 1) - 8)
        item_width = max(120, available_width // cols)
        icon_width = max(96, item_width - 24)
        icon_height = max(72, int(icon_width * 3 / 4))
        item_height = icon_height + 64
        self.thumbnail_list.setIconSize(QSize(icon_width, icon_height))
        self.thumbnail_list.setGridSize(QSize(item_width + spacing, item_height))
        self._apply_thumbnail_item_size_hints(item_width, item_height)
        self.thumbnail_list.doItemsLayout()
        self.thumbnail_list.updateGeometries()
        self.thumbnail_list.viewport().update()

    def _on_thumbnail_list_resized(self) -> None:
        self._refresh_grid_thumbnail_layout()

    def _on_thumbnail_double_clicked(self, item: QListWidgetItem) -> None:
        if getattr(self, '_grid_view_active', False):
            self._switch_view_mode("preview")

    def _display_photo_by_index(self, index: int) -> None:
        if index < 0 or index >= len(self.filtered_photos):
            self.current_index = -1
            self._update_preview_zoom_controls()
            return

        # アイテム選択時はギャップ選択を解除
        self.thumbnail_list._selected_gap = -1
        self.thumbnail_list.viewport().update()

        self.current_index = index
        photo = self.filtered_photos[index]
        self._remember_current_photo_for_shuffle()
        self.canvas.set_photo(photo.path, rotation_quadrants=photo.rotation_quadrants, animate=True)
        self.canvas.set_transition_style(photo.transition_style)
        self.canvas.set_transition_duration_ms(photo.transition_duration_ms)
        self._update_preview_zoom_controls()

        # スタイルをベース+方向に分解してコンボに反映
        base_style, direction = self._split_style(photo.transition_style)

        self.transition_combo.blockSignals(True)
        combo_index = self.transition_combo.findData(base_style)
        if combo_index >= 0:
            self.transition_combo.setCurrentIndex(combo_index)
        self.transition_combo.blockSignals(False)

        self.direction_combo.blockSignals(True)
        dir_index = self.direction_combo.findData(direction)
        if dir_index >= 0:
            self.direction_combo.setCurrentIndex(dir_index)
        self.direction_combo.blockSignals(False)
        self.direction_combo.setEnabled(base_style in DIRECTIONAL_TRANSITIONS)
        self.direction_label.setEnabled(base_style in DIRECTIONAL_TRANSITIONS)

        self.fade_spin.blockSignals(True)
        self.fade_spin.setValue(photo.transition_duration_ms)
        self.fade_spin.blockSignals(False)
        # ホワイトアウト・カット時はトランジションタイムをグレーアウト
        self.fade_spin.setEnabled(photo.transition_style not in ("white_out", "cut"))
        self.photo_title.setText(photo.label)
        self.photo_meta.setText(
            f"{photo.display_width} x {photo.display_height} px  |  {photo.modified_at.strftime('%Y-%m-%d %H:%M')}  |  {photo.orientation}"
        )
        current_item = self.thumbnail_list.item(index)
        if current_item is not None:
            self.thumbnail_list.scrollToItem(current_item, QListWidget.ScrollHint.PositionAtCenter)
        self._apply_selection_summary()
        self.statusBar().showMessage(f"{index + 1} / {len(self.filtered_photos)} を表示中")

    def toggle_slideshow(self, checked: bool) -> None:
        if not self.filtered_photos:
            self.play_button.setChecked(False)
            self._show_info("画像がありません", "先に画像フォルダを開いてください。")
            return

        if checked:
            # 最初のスライドから再生
            self.thumbnail_list.setCurrentRow(0)
            interval_ms = self._effective_slideshow_interval_ms()
            self.slideshow_timer.start(interval_ms)
            self.enter_playback_mode()
            self.play_button.setText("停止(F5)")
            self._apply_display_resolution()
        else:
            self.slideshow_timer.stop()
            self.play_button.setText("再生(F5)")
            self.exit_playback_mode()
            self.statusBar().showMessage("スライドショーを停止しました")

    def _toggle_fullscreen(self) -> None:
        if self.is_playback_fullscreen:
            self.play_button.setChecked(False)
            self.toggle_slideshow(False)
        else:
            self.play_button.setChecked(True)
            self.toggle_slideshow(True)

    def enter_playback_mode(self) -> None:
        if self.is_playback_fullscreen:
            return

        self._was_grid_view = getattr(self, '_grid_view_active', False)
        if self._was_grid_view:
            self._switch_view_mode("preview")

        self.is_playback_fullscreen = True
        self.top_bar_widget.hide()
        self.sidebar_panel.hide()
        self.film_panel.hide()
        self.playback_bar.hide()
        self.metadata_card.hide()
        self.statusBar().hide()
        self.canvas.set_playback_mode(True)
        self.canvas_panel.setStyleSheet(
            "QFrame { border: none; border-radius: 0px; background: #0a0a0d; }"
        )
        self.setCursor(Qt.CursorShape.BlankCursor)
        self.showFullScreen()
        self._update_actual_display_size_label()

    def exit_playback_mode(self) -> None:
        if not self.is_playback_fullscreen:
            return

        self.is_playback_fullscreen = False
        self.showNormal()
        self.top_bar_widget.show()
        self.sidebar_panel.show()
        self.film_panel.show()
        self.statusBar().show()

        if getattr(self, '_was_grid_view', False):
            self._switch_view_mode("grid")
        else:
            self.playback_bar.show()
            self.metadata_card.show()
        self.canvas.set_playback_mode(False)
        self.canvas.set_display_resolution(None)
        self.canvas_panel.setStyleSheet("")
        self.unsetCursor()
        self._update_actual_display_size_label()
        if self.play_button.isChecked():
            self.play_button.setChecked(False)
            self.play_button.setText("再生(F5)")
            self.slideshow_timer.stop()
            self.statusBar().showMessage("全画面再生を終了しました")

    def resizeEvent(self, event) -> None:  # type: ignore[override]
        super().resizeEvent(event)
        self._update_actual_display_size_label()

    def show_next_photo(self) -> None:
        if not self.filtered_photos:
            return

        if self.shuffle_button.isChecked() and len(self.filtered_photos) > 1:
            next_index = self._pick_next_shuffled_index()
        else:
            next_index = (self.current_index + 1) % len(self.filtered_photos)

        self.thumbnail_list.setCurrentRow(next_index)

    def show_previous_photo(self) -> None:
        if not self.filtered_photos:
            return

        previous_index = (self.current_index - 1) % len(self.filtered_photos)
        self.thumbnail_list.setCurrentRow(previous_index)


def main() -> None:
    app = QApplication(sys.argv)
    app.setApplicationName("LumiSlide")
    window = MainWindow()
    window.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()