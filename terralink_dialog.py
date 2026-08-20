import os
import time

import re
from typing import Dict, List, Optional, Tuple, Union

from qgis.PyQt import uic
from qgis.PyQt.QtCore import Qt, QTimer, QCoreApplication
from qgis.PyQt.QtGui import QTextOption
from qgis.PyQt.QtWidgets import (
    QFileDialog,
    QDialog,
    QTextBrowser,
    QHBoxLayout,
    QWidget,
    QTextEdit,
    QSplitter,
    QSizePolicy,
    QListWidgetItem,
    QLabel,
    QFormLayout,
    QVBoxLayout,
    QTabWidget,
    QScrollArea,
    QPlainTextEdit,
    QProgressBar,
    QDialogButtonBox,
    QListWidget,
    QLineEdit,
    QToolButton,
    QStackedWidget,
    QMessageBox,
)
from qgis.core import QgsApplication, Qgis, QgsProject, QgsRasterLayer, QgsVectorLayer, QgsWkbTypes, QgsUnitTypes, QgsFeature, QgsGeometry
from qgis.gui import QgsCollapsibleGroupBox

FORM_CLASS, _ = uic.loadUiType(os.path.join(
    os.path.dirname(__file__), 'terralink_dialog_base.ui'))


STRATEGY_CHOICES_BY_LAYER = {
    "raster": [
        ("Largest Single Network", "largest_single_network"),
        ("Most Connected Networks A", "most_connected_networks_2"),
        ("Most Connected Networks B", "most_connected_networks"),
        ("Landscape Fluidity", "landscape_fluidity"),
    ],
    "vector": [
        ("Largest Single Network", "largest_single_network"),
        ("Most Connected Networks A", "most_connected_networks_2"),
        ("Most Connected Networks B", "most_connected_networks"),
        ("Landscape Fluidity", "landscape_fluidity"),
    ],
}

STRATEGY_FALLBACK_BY_LAYER = {
    # Back-compat for older saved projects/settings.
    ("raster", "largest_network"): "largest_single_network",
    ("vector", "largest_network"): "largest_single_network",
    ("raster", "landscape_fluidity_a1"): "landscape_fluidity",
    ("vector", "landscape_fluidity_a"): "landscape_fluidity",
    ("vector", "landscape_fluidity_a1"): "landscape_fluidity",
}


class TerraLinkDialog(QDialog, FORM_CLASS):
    def __init__(self, iface, parent=None):
        super(TerraLinkDialog, self).__init__(parent)
        self.setupUi(self)
        self.iface = iface
        self._help_browser: Optional[QTextBrowser] = None
        self._log_text: Optional[QPlainTextEdit] = None
        self._progress_bar: Optional[QProgressBar] = None
        self._progress_status_label: Optional[QLabel] = None
        self._last_progress_value: Optional[int] = None
        self._last_progress_message: Optional[str] = None
        self._last_logged_progress_message: Optional[str] = None
        self._last_logged_progress_value: Optional[int] = None
        self._last_actual_progress_value: Optional[int] = None
        self._progress_stall_ticks: int = 0
        self._display_progress_value: int = 0
        self._progress_soft_ceiling: int = 0
        self._progress_heartbeat_timer: Optional[QTimer] = None
        self._help_visible: bool = False
        self._run_completed_successfully: bool = False
        self._run_in_progress: bool = False
        self._reframe_ui()

        self.output_dir_line.setPlaceholderText("Select output folder…")
        self._parameters = {}
        self.available_layers = {}
        self._current_layer_type = "raster"
        self._selected_layer_id: Optional[str] = None

        self._connect_signals()
        self._configure_defaults()
        self._auto_select_layer_type_from_active_layer()
        self._on_layer_type_changed(self.layer_type_combo.currentText())
        QTimer.singleShot(0, self._ensure_initial_size)
        self._init_progress_heartbeat()

        try:
            ok_btn = self.button_box.button(QDialogButtonBox.Ok)
            if ok_btn is not None:
                ok_btn.setText("Run")
            cancel_btn = self.button_box.button(QDialogButtonBox.Cancel)
            if cancel_btn is not None:
                cancel_btn.setText("Close")
        except Exception:  # nosec
            pass

        try:
            self.help_button = self.button_box.addButton("Help", QDialogButtonBox.HelpRole)
            self.help_button.clicked.connect(self._toggle_help_panel)
        except Exception:
            self.help_button = None

    def _ensure_initial_size(self) -> None:
        # QGIS/Qt can sometimes ignore early resize() calls; enforce a sane minimum on first show.
        target_w, target_h = 900, 700
        try:
            self.setMinimumSize(820, 620)
        except Exception:  # nosec
            pass
        try:
            if self.width() < target_w or self.height() < target_h:
                self.resize(max(self.width(), target_w), max(self.height(), target_h))
        except Exception:  # nosec
            pass

    def _auto_select_layer_type_from_active_layer(self) -> None:
        try:
            active = self.iface.activeLayer() if self.iface else None
        except Exception:
            active = None
        if active is None:
            return
        try:
            if isinstance(active, QgsVectorLayer):
                idx = self.layer_type_combo.findText("Vector")
                if idx >= 0:
                    self.layer_type_combo.setCurrentIndex(idx)
            elif isinstance(active, QgsRasterLayer):
                idx = self.layer_type_combo.findText("Raster")
                if idx >= 0:
                    self.layer_type_combo.setCurrentIndex(idx)
        except Exception:  # nosec
            pass

    # ------------------------------------------------------------------
    # UI setup helpers
    # ------------------------------------------------------------------

    def _set_collapsed(self, box: QWidget, collapsed: bool) -> None:
        try:
            if hasattr(box, "setCollapsed"):
                box.setCollapsed(bool(collapsed))  # type: ignore[attr-defined]
        except Exception:  # nosec
            pass

    # Simple/Expert mode was removed: the UI is controlled by collapsible sections only.

    def _reframe_ui(self) -> None:
        """
        Reframe the dialog around user decisions (Input → Goal → Constraints → Impassables → Advanced → Output)
        while reusing existing widgets so the processing logic remains unchanged.
        """
        base_layout = self.layout()
        if base_layout is None:
            return

        # Hide legacy group boxes; we'll re-parent the important controls into new sections.
        for legacy in (
            getattr(self, "inputGroup", None),
            getattr(self, "patchGroup", None),
            getattr(self, "strategyGroup", None),
            getattr(self, "paramGroup", None),
            getattr(self, "obstacleGroup", None),
            getattr(self, "vectorGroup", None),
            getattr(self, "vectorObstacleGroup", None),
            getattr(self, "outputGroup", None),
        ):
            if isinstance(legacy, QWidget):
                legacy.setVisible(False)

        # Clear the base layout items.
        while base_layout.count():
            item = base_layout.takeAt(0)
            w = item.widget()
            if w is not None:
                w.setParent(None)

        # Root layout: left (tabs) + optional right help panel.
        self.main_splitter = QSplitter(Qt.Horizontal)
        self.main_splitter.setChildrenCollapsible(False)
        base_layout.addWidget(self.main_splitter)

        self.left_panel = QWidget()
        self.left_panel_layout = QVBoxLayout(self.left_panel)
        self.left_panel_layout.setContentsMargins(0, 0, 0, 0)
        self.left_panel_layout.setSpacing(8)

        self.help_panel = QTextBrowser()
        self.help_panel.setOpenExternalLinks(True)
        self.help_panel.setVisible(False)
        self.help_panel.setMinimumWidth(280)
        self._help_browser = self.help_panel
        self._load_help_content()

        self.main_splitter.addWidget(self.left_panel)
        self.main_splitter.addWidget(self.help_panel)
        try:
            self.main_splitter.setSizes([9999, 0])
        except Exception:  # nosec
            pass

        # Tabs: Parameters | Log
        self.tabs = QTabWidget(self)

        self.params_tab = QWidget()
        self.params_tab_layout = QVBoxLayout(self.params_tab)
        self.params_tab_layout.setContentsMargins(0, 0, 0, 0)
        self.params_tab_layout.setSpacing(0)

        self.scroll = QScrollArea()
        self.scroll.setWidgetResizable(True)
        self.scroll.setFrameShape(QScrollArea.NoFrame)

        self.content = QWidget()
        self.content_layout = QVBoxLayout(self.content)
        self.content_layout.setContentsMargins(12, 12, 12, 12)
        self.content_layout.setSpacing(10)
        self.scroll.setWidget(self.content)
        self.params_tab_layout.addWidget(self.scroll)

        self.log_tab = QWidget()
        self.log_tab_layout = QVBoxLayout(self.log_tab)
        self.log_tab_layout.setContentsMargins(12, 12, 12, 12)
        status_row = QWidget()
        status_layout = QHBoxLayout(status_row)
        status_layout.setContentsMargins(0, 0, 0, 6)
        status_layout.setSpacing(8)
        self._progress_status_label = QLabel("Idle")
        self._progress_status_label.setWordWrap(True)
        self._progress_bar = QProgressBar()
        self._progress_bar.setRange(0, 100)
        self._progress_bar.setValue(0)
        self._progress_bar.setTextVisible(False)
        status_layout.addWidget(self._progress_status_label, 1)
        status_layout.addWidget(self._progress_bar)
        self.log_tab_layout.addWidget(status_row)
        self.log_text = QPlainTextEdit()
        self.log_text.setReadOnly(True)
        self.log_text.setLineWrapMode(QPlainTextEdit.NoWrap)
        self.log_tab_layout.addWidget(self.log_text)
        self._log_text = self.log_text

        self.tabs.addTab(self.params_tab, "Parameters")
        self.tabs.addTab(self.log_tab, "Log")

        self.left_panel_layout.addWidget(self.tabs)

        # --- Input ---
        self.section_input = QgsCollapsibleGroupBox("🧩 Input")
        input_layout = QFormLayout(self.section_input)
        input_layout.addRow("Layer type:", self.layer_type_combo)
        input_layout.addRow("Input layer:", self.input_layer_combo)

        # Units are a top-level choice for raster analysis.
        self._raster_units_row = QWidget()
        raster_units_layout = QFormLayout(self._raster_units_row)
        raster_units_layout.setContentsMargins(0, 0, 0, 0)
        raster_units_layout.addRow(self.label_raster_units, self.raster_units_combo)
        input_layout.addRow(self._raster_units_row)

        # Units are a top-level choice for vector analysis.
        self._vector_units_row = QWidget()
        vector_units_layout = QFormLayout(self._vector_units_row)
        vector_units_layout.setContentsMargins(0, 0, 0, 0)
        vector_units_layout.addRow(self.label_vector_units, self.vector_units_combo)
        input_layout.addRow(self._vector_units_row)

        # Pixel neighborhood is a top-level choice for raster analysis.
        self._raster_neighborhood_row = QWidget()
        raster_neighborhood_layout = QFormLayout(self._raster_neighborhood_row)
        raster_neighborhood_layout.setContentsMargins(0, 0, 0, 0)
        raster_neighborhood_layout.addRow(self.label_5, self.pixel_neighborhood_combo)
        input_layout.addRow(self._raster_neighborhood_row)

        # Patch definition (conditional by layer type).
        self._raster_patch_row = QWidget()
        raster_patch_layout = QFormLayout(self._raster_patch_row)
        raster_patch_layout.setContentsMargins(0, 0, 0, 0)
        raster_patch_layout.addRow(self.label_patch_value, self.patch_value_line)
        raster_patch_layout.addRow(self.label_7, self.min_patch_size_spin)
        input_layout.addRow(self._raster_patch_row)

        self._vector_patch_row = QWidget()
        vector_patch_layout = QFormLayout(self._vector_patch_row)
        vector_patch_layout.setContentsMargins(0, 0, 0, 0)
        vector_patch_layout.addRow(self.label_vector_min_patch, self.vector_min_patch_size_spin)
        input_layout.addRow(self._vector_patch_row)

        self.content_layout.addWidget(self.section_input)

        # --- Optimization Goal ---
        self.section_goal = QgsCollapsibleGroupBox("🎯 Optimization Goal")
        goal_layout = QVBoxLayout(self.section_goal)
        goal_layout.setContentsMargins(6, 6, 6, 6)
        goal_row = QWidget()
        goal_row_layout = QHBoxLayout(goal_row)
        goal_row_layout.setContentsMargins(0, 0, 0, 0)
        goal_row_layout.addWidget(QLabel("Optimization mode:"))
        goal_row_layout.addWidget(self.strategy_combo, 1)
        goal_layout.addWidget(goal_row)
        self.strategy_help_label = QLabel("")
        self.strategy_help_label.setWordWrap(True)
        goal_layout.addWidget(self.strategy_help_label)
        self.content_layout.addWidget(self.section_goal)

        # --- Core Constraints ---
        self.section_constraints = QgsCollapsibleGroupBox("📏 Core Constraints")
        constraints_layout = QVBoxLayout(self.section_constraints)
        constraints_layout.setContentsMargins(6, 6, 6, 6)

        self._raster_constraints_row = QWidget()
        raster_constraints_layout = QFormLayout(self._raster_constraints_row)
        raster_constraints_layout.setContentsMargins(0, 0, 0, 0)
        raster_constraints_layout.addRow(self.label_8, self.budget_spin)
        raster_constraints_layout.addRow(self.label_10, self.min_corridor_width_spin)
        raster_constraints_layout.addRow(self.label_9, self.max_search_spin)
        constraints_layout.addWidget(self._raster_constraints_row)

        self._vector_constraints_row = QWidget()
        vector_constraints_layout = QFormLayout(self._vector_constraints_row)
        vector_constraints_layout.setContentsMargins(0, 0, 0, 0)
        vector_constraints_layout.addRow(self.label_vector_budget, self.vector_budget_spin)
        vector_constraints_layout.addRow(self.label_vector_min_width, self.vector_min_corridor_width_spin)
        vector_constraints_layout.addRow(self.label_vector_max_search, self.vector_max_search_spin)
        constraints_layout.addWidget(self._vector_constraints_row)

        self.content_layout.addWidget(self.section_constraints)

        # --- Impassable Land Classes ---
        self.section_obstacles = QgsCollapsibleGroupBox("🚧 Impassable Land Classes")
        obstacles_layout = QVBoxLayout(self.section_obstacles)
        obstacles_layout.setContentsMargins(6, 6, 6, 6)

        self._raster_obstacles_row = QWidget()
        raster_obs_layout = QVBoxLayout(self._raster_obstacles_row)
        raster_obs_layout.setContentsMargins(0, 0, 0, 0)
        raster_obs_form = QFormLayout()
        raster_obs_form.setContentsMargins(0, 0, 0, 0)
        self.label_obstacle_value.setText("Impassable values:")
        raster_obs_form.addRow(self.label_obstacle_value, self.obstacle_value_line)
        raster_obs_layout.addLayout(raster_obs_form)
        raster_obs_layout.addWidget(self.allow_bottlenecks_checkbox)
        self._vector_obstacles_row = QWidget()
        vector_obs_layout = QVBoxLayout(self._vector_obstacles_row)
        vector_obs_layout.setContentsMargins(0, 0, 0, 0)
        vector_obs_form = QFormLayout()
        vector_obs_form.setContentsMargins(0, 0, 0, 0)
        self.vector_obstacle_layer_list.setVisible(False)
        obstacle_pick_row = QWidget()
        obstacle_pick_layout = QHBoxLayout(obstacle_pick_row)
        obstacle_pick_layout.setContentsMargins(0, 0, 0, 0)
        self.vector_obstacle_selection_line = QLineEdit()
        self.vector_obstacle_selection_line.setReadOnly(True)
        self.vector_obstacle_selection_line.setText("0 inputs selected")
        self.vector_obstacle_select_button = QToolButton()
        self.vector_obstacle_select_button.setText("…")
        self.vector_obstacle_select_button.clicked.connect(self._choose_vector_obstacle_layers)
        obstacle_pick_layout.addWidget(self.vector_obstacle_selection_line, 1)
        obstacle_pick_layout.addWidget(self.vector_obstacle_select_button)
        self.label_vector_obstacle_layer.setText("Impassable layers:")
        vector_obs_form.addRow(self.label_vector_obstacle_layer, obstacle_pick_row)
        self.label_vector_obstacle_resolution.setText("Grid cell size:")
        vector_obs_form.addRow(self.label_vector_obstacle_resolution, self.vector_obstacle_resolution_spin)
        vector_obs_layout.addLayout(vector_obs_form)
        # Stack raster/vector impassable controls to prevent any duplication in the layout.
        self._obstacles_stack = QStackedWidget()
        self._obstacles_stack.addWidget(self._raster_obstacles_row)
        self._obstacles_stack.addWidget(self._vector_obstacles_row)
        obstacles_layout.addWidget(self._obstacles_stack)

        self.content_layout.addWidget(self.section_obstacles)

        # --- Output ---
        self.section_output = QgsCollapsibleGroupBox("💾 Output")
        out_layout = QVBoxLayout(self.section_output)
        out_layout.setContentsMargins(6, 6, 6, 6)

        out_form = QFormLayout()
        out_form.setContentsMargins(0, 0, 0, 0)
        out_dir_row = QWidget()
        out_dir_layout = QHBoxLayout(out_dir_row)
        out_dir_layout.setContentsMargins(0, 0, 0, 0)
        out_dir_layout.addWidget(self.output_dir_line, 1)
        out_dir_layout.addWidget(self.output_browse_button)
        out_dir_layout.addWidget(self.temporary_output_checkbox)
        out_form.addRow("Output folder:", out_dir_row)
        out_layout.addLayout(out_form)

        self._vector_output_name_row = QWidget()
        vector_out_form = QFormLayout(self._vector_output_name_row)
        vector_out_form.setContentsMargins(0, 0, 0, 0)
        vector_out_form.addRow(self.label_vector_output, self.vector_output_name_line)
        out_layout.addWidget(self._vector_output_name_row)

        self.content_layout.addWidget(self.section_output)
        self.content_layout.addStretch(1)

        self.left_panel_layout.addWidget(self.button_box)

        # Initial collapse states
        self._set_collapsed(self.section_input, False)
        self._set_collapsed(self.section_goal, False)
        self._set_collapsed(self.section_output, False)
        self._set_collapsed(self.section_constraints, False)
        self._set_collapsed(self.section_obstacles, True)
        self._update_strategy_help()
        try:
            self.resize(900, 700)
        except Exception:  # nosec
            pass
        self._update_vector_obstacle_selector_text()

    def _update_strategy_help(self) -> None:
        if not hasattr(self, "strategy_help_label"):
            return
        key = self._normalize_strategy_key(self.strategy_combo.currentData() or self.strategy_combo.currentText())
        text = ""
        if key == "largest_single_network":
            text = "Prioritize one dominant connected network under budget."
        elif key == "most_connected_networks":
            text = (
                "Favors total connected subnetwork area with additional search and cleanup logic that can still "
                "consolidate stronger subnetworks."
            )
        elif key == "most_connected_networks_2":
            text = (
                "Rank corridor candidates by the value of the subnetworks they join per unit cost. Patches already "
                "inside connected subnetworks can still be used in additional valuable joins."
            )
        elif key == "landscape_fluidity":
            text = "Improve landscape fluidity by adding corridors that meaningfully reduce detours and increase internal mobility."
        self.strategy_help_label.setText(text)

    @staticmethod
    def _normalize_strategy_key(strategy: Optional[str]) -> str:
        key = str(strategy or "most_connected_networks_2").strip().lower().replace(" ", "_").replace("-", "_")
        aliases = {
            # Back-compat
            "largest_network": "largest_single_network",
            "most_connected_network": "most_connected_networks",
            "most_connected_network_1": "most_connected_networks",
            "most_connected_networks_1": "most_connected_networks",
            "mcn1": "most_connected_networks",
            "most_connected_network_a": "most_connected_networks_2",
            "most_connected_networks_a": "most_connected_networks_2",
            "mcna": "most_connected_networks_2",
            "mcn_a": "most_connected_networks_2",
            "most_connected_network_2": "most_connected_networks_2",
            "mcn2": "most_connected_networks_2",
            "most_connected_network_b": "most_connected_networks",
            "most_connected_networks_b": "most_connected_networks",
            "mcnb": "most_connected_networks",
            "mcn_b": "most_connected_networks",
            "landscape_fluidity_a": "landscape_fluidity",
            "landscape_fluidity_a1": "landscape_fluidity",
            "lf_a": "landscape_fluidity",
            "lfa": "landscape_fluidity",
            "lf_a1": "landscape_fluidity",
            "lfa1": "landscape_fluidity",
        }
        key = aliases.get(key, key)
        valid = {
            "largest_single_network",
            "most_connected_networks",
            "most_connected_networks_2",
            "landscape_fluidity",
        }
        if key not in valid:
            key = "most_connected_networks_2"
        return key

    @classmethod
    def _strategy_display_name(cls, strategy: Optional[str]) -> str:
        key = cls._normalize_strategy_key(strategy)
        names = {
            "largest_single_network": "Largest Single Network",
            "most_connected_networks": "Most Connected Networks B",
            "most_connected_networks_2": "Most Connected Networks A",
            "landscape_fluidity": "Landscape Fluidity",
        }
        return names.get(key, "Most Connected Networks A")

    def _inject_help_panel(self) -> None:
        """Add a right-hand help panel fed by a markdown file."""
        # Deprecated: replaced by the Parameters|Log tab layout.
        return
        base_layout = self.layout()
        if base_layout is None:
            return

        contents_margins = base_layout.contentsMargins()
        contents_spacing = base_layout.spacing()

        # Wrap the existing layout in a container widget so we can place it beside the help panel.
        left_container = QWidget()
        left_container.setLayout(base_layout)
        left_container.setSizePolicy(QSizePolicy.Preferred, QSizePolicy.Expanding)

        help_browser = QTextBrowser()
        help_browser.setObjectName("help_browser")
        help_browser.setOpenExternalLinks(True)
        help_browser.setMinimumWidth(220)
        help_browser.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        help_browser.setLineWrapMode(QTextEdit.WidgetWidth)
        help_browser.setWordWrapMode(QTextOption.WordWrap)
        help_browser.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)

        splitter = QSplitter(Qt.Horizontal)
        splitter.setChildrenCollapsible(False)
        splitter.addWidget(left_container)
        splitter.addWidget(help_browser)
        splitter.setStretchFactor(0, 3)
        splitter.setStretchFactor(1, 2)

        wrapper = QHBoxLayout()
        wrapper.setContentsMargins(contents_margins)
        wrapper.setSpacing(contents_spacing)
        wrapper.addWidget(splitter)

        self.setLayout(wrapper)
        self._help_browser = help_browser
        self.splitter = splitter
        self.left_panel = left_container
        self.help_panel = help_browser
        self._load_help_content()
        return

    # ------------------------------------------------------------------
    # Log helpers
    # ------------------------------------------------------------------

    def _append_log(self, message: str, level: str = "INFO") -> None:
        msg = (message or "").rstrip()
        if not msg:
            return
        line = f"[{level}] {msg}"
        if self._log_text is not None:
            try:
                self._log_text.appendPlainText(line)
            except Exception:  # nosec
                pass
        try:
            level_key = (level or "INFO").upper()
            qgis_level = Qgis.Info
            if level_key in ("WARN", "WARNING"):
                qgis_level = Qgis.Warning
            elif level_key in ("ERR", "ERROR"):
                qgis_level = Qgis.Critical
            elif level_key in ("CRIT", "CRITICAL"):
                qgis_level = Qgis.Critical
            QgsApplication.messageLog().logMessage(msg, "TerraLink", level=qgis_level)
        except Exception:  # nosec
            pass
        try:
            QCoreApplication.processEvents()
        except Exception:  # nosec
            pass

    def _format_run_error(self, err_text: str) -> List[str]:
        text = (err_text or "").strip()
        if not text:
            return ["Run stopped.", "No outputs were generated.", "Reason: Unknown error."]
        if "Corridor search too large" in text:
            lines = [
                "Run stopped: corridor search too large for the current settings.",
                "No outputs were generated.",
            ]
            details = ""
            suggestions = ""
            if ")" in text:
                prefix, _, rest = text.partition(")")
                if "(" in prefix:
                    details = prefix.split("(", 1)[1].strip()
                suggestions = rest.strip()
                if suggestions.startswith("."):
                    suggestions = suggestions[1:].strip()
            if details:
                detail_chunks = [chunk.strip() for chunk in details.split(";") if chunk.strip()]
                if detail_chunks:
                    lines.append(f"Details: {detail_chunks[0]}.")
                if len(detail_chunks) > 1:
                    lines.append(f"Params: {detail_chunks[1].rstrip('.')}.")
            if suggestions:
                lines.append(suggestions)
            return lines
        return ["Run stopped.", "No outputs were generated.", f"Reason: {text}"]

    def _progress_log(self, value: int, message: Optional[str] = None) -> None:
        try:
            pct = int(max(0, min(100, value)))
        except Exception:
            pct = 0
        msg = (message or "").strip() if message else ""
        same_as_last = pct == self._last_progress_value and msg == (self._last_progress_message or "")
        if self._last_actual_progress_value is None or pct > int(self._last_actual_progress_value):
            self._last_actual_progress_value = pct
            self._progress_stall_ticks = 0
        self._last_progress_value = pct
        self._last_progress_message = msg
        self._display_progress_value = int(max(self._display_progress_value, pct))
        if pct >= 100:
            self._progress_soft_ceiling = 100
        else:
            headroom = 12 if pct < 90 else 6
            self._progress_soft_ceiling = int(max(self._display_progress_value, min(99, pct + headroom)))
        try:
            if self._progress_bar is not None:
                self._progress_bar.setValue(int(self._display_progress_value))
            if self._progress_status_label is not None:
                if msg:
                    self._progress_status_label.setText(f"{msg} ({int(self._display_progress_value)}%)")
                else:
                    self._progress_status_label.setText(f"{int(self._display_progress_value)}%")
        except Exception:  # nosec
            pass

        if same_as_last:
            return

        per_patch = bool(msg) and re.match(r"^(analyzing|finished) patch\\s+\\d+/\\d+", msg, re.IGNORECASE) is not None
        if msg and (not per_patch):
            log_step = 5
            last_pct = self._last_logged_progress_value
            last_msg = self._last_logged_progress_message or ""
            last_ts = float(getattr(self, "_last_logged_progress_ts", 0.0) or 0.0)
            now = time.perf_counter()
            should_log = False
            if last_pct is None or pct > int(last_pct):
                should_log = True
            elif abs(pct - int(last_pct)) >= log_step:
                should_log = True
            elif pct == int(last_pct) and msg != last_msg and (now - last_ts) >= 1.5:
                should_log = True
            if should_log:
                self._last_logged_progress_message = msg
                self._last_logged_progress_value = pct
                self._last_logged_progress_ts = now
                self._append_log(f"{pct}% - {msg}", "PROGRESS")
        try:
            QCoreApplication.processEvents()
        except Exception:  # nosec
            pass

    def _init_progress_heartbeat(self) -> None:
        try:
            timer = QTimer(self)
            timer.setInterval(900)
            timer.timeout.connect(self._progress_heartbeat_tick)
            self._progress_heartbeat_timer = timer
        except Exception:
            self._progress_heartbeat_timer = None

    def _set_progress_heartbeat_active(self, active: bool) -> None:
        timer = self._progress_heartbeat_timer
        if timer is None:
            return
        try:
            if bool(active):
                if not timer.isActive():
                    timer.start()
            else:
                if timer.isActive():
                    timer.stop()
        except Exception:  # nosec
            pass

    def _progress_heartbeat_tick(self) -> None:
        if not getattr(self, "_run_in_progress", False):
            return
        actual = int(self._last_progress_value or 0)
        display = int(self._display_progress_value or 0)
        ceiling = int(max(display, self._progress_soft_ceiling or 0))
        if self._last_actual_progress_value is None:
            self._last_actual_progress_value = actual
        if actual > int(self._last_actual_progress_value or 0):
            self._last_actual_progress_value = actual
            self._progress_stall_ticks = 0
        else:
            self._progress_stall_ticks = int(self._progress_stall_ticks or 0) + 1
            if display >= ceiling and actual < 99 and self._progress_stall_ticks >= 3:
                ceiling = min(99, max(ceiling + 1, actual + 1))
                self._progress_soft_ceiling = int(ceiling)
        if actual >= 100 or display >= 100:
            return
        if display >= ceiling:
            return
        display = min(display + 1, ceiling, 99)
        self._display_progress_value = int(display)
        msg = (self._last_progress_message or "").strip()
        try:
            if self._progress_bar is not None:
                self._progress_bar.setValue(int(display))
            if self._progress_status_label is not None:
                if msg:
                    self._progress_status_label.setText(f"{msg} ({int(display)}%)")
                else:
                    self._progress_status_label.setText(f"{int(display)}%")
        except Exception:  # nosec
            pass
        try:
            QCoreApplication.processEvents()
        except Exception:  # nosec
            pass

    def _reset_progress_display(self) -> None:
        self._last_progress_value = None
        self._last_progress_message = None
        self._last_logged_progress_message = None
        self._last_logged_progress_value = None
        self._last_actual_progress_value = None
        self._progress_stall_ticks = 0
        self._display_progress_value = 0
        self._progress_soft_ceiling = 0
        try:
            if self._progress_bar is not None:
                self._progress_bar.setValue(0)
            if self._progress_status_label is not None:
                self._progress_status_label.setText("Starting…")
        except Exception:  # nosec
            pass

    def _finish_progress_display(self, final_value: Optional[int] = None, status_text: Optional[str] = None) -> None:
        self._set_progress_heartbeat_active(False)
        if final_value is None:
            try:
                final_value = int(max(0, min(100, self._last_progress_value or self._display_progress_value or 0)))
            except Exception:
                final_value = 0
        self._display_progress_value = int(max(0, min(100, final_value)))
        if self._display_progress_value >= 100:
            self._progress_soft_ceiling = 100
        else:
            self._progress_soft_ceiling = int(max(self._display_progress_value, self._progress_soft_ceiling or 0))
        msg = (status_text or self._last_progress_message or "").strip()
        try:
            if self._progress_bar is not None:
                self._progress_bar.setValue(int(self._display_progress_value))
            if self._progress_status_label is not None:
                if msg:
                    if self._display_progress_value > 0:
                        self._progress_status_label.setText(f"{msg} ({int(self._display_progress_value)}%)")
                    else:
                        self._progress_status_label.setText(msg)
                else:
                    self._progress_status_label.setText(f"{int(self._display_progress_value)}%")
        except Exception:  # nosec
            pass

    def _connect_signals(self):
        self.output_browse_button.clicked.connect(self._choose_output_dir)
        self.input_layer_combo.currentIndexChanged.connect(self._on_layer_changed)
        self.layer_type_combo.currentTextChanged.connect(self._on_layer_type_changed)
        self.temporary_output_checkbox.toggled.connect(self._on_temporary_toggled)
        self.raster_units_combo.currentTextChanged.connect(self._update_raster_units_labels)
        self.vector_units_combo.currentTextChanged.connect(self._update_vector_units_labels)
        self.strategy_combo.currentIndexChanged.connect(self._on_strategy_changed)
    def _populate_strategy_combo(self, preferred_strategy: Optional[str] = None) -> None:
        layer_type = "vector" if self._current_layer_type == "vector" else "raster"
        strategy_rows = STRATEGY_CHOICES_BY_LAYER.get(layer_type, STRATEGY_CHOICES_BY_LAYER["raster"])
        target_strategy = str(preferred_strategy or self.strategy_combo.currentData() or "most_connected_networks_2")
        target_strategy = self._normalize_strategy_key(target_strategy)
        target_strategy = STRATEGY_FALLBACK_BY_LAYER.get((layer_type, target_strategy), target_strategy)
        self.strategy_combo.clear()
        for label, key in strategy_rows:
            self.strategy_combo.addItem(label, key)
        idx = self.strategy_combo.findData(target_strategy)
        if idx < 0:
            idx = self.strategy_combo.findData("most_connected_networks_2")
        if idx < 0:
            idx = 0
        self.strategy_combo.setCurrentIndex(idx)

    def _configure_defaults(self):
        self._raster_unit_system = "pixels"
        self._vector_unit_system = "metric"
        self._populate_strategy_combo()
        self.temporary_output_checkbox.setChecked(True)
        self.raster_units_combo.setItemData(0, "pixels")
        self.raster_units_combo.setItemData(1, "metric")
        self.raster_units_combo.setItemData(2, "imperial")
        self.vector_units_combo.setItemData(0, "metric")
        self.vector_units_combo.setItemData(1, "imperial")
        idx = self.pixel_neighborhood_combo.findText("8")
        if idx >= 0:
            self.pixel_neighborhood_combo.setCurrentIndex(idx)
        self._on_temporary_toggled(self.temporary_output_checkbox.isChecked())
        self._update_raster_units_labels(self.raster_units_combo.currentText())
        self._update_vector_units_labels(self.vector_units_combo.currentText())
        try:
            self.label_obstacle_value.setEnabled(True)
            self.obstacle_value_line.setEnabled(True)
        except Exception:  # nosec
            pass
        try:
            self.label_vector_obstacle_layer.setEnabled(True)
            self.label_vector_obstacle_resolution.setEnabled(True)
            self.vector_obstacle_resolution_spin.setEnabled(True)
        except Exception:  # nosec
            pass

        # Optional-by-default controls: show blank at 0 and treat it as "unset".
        try:
            self.min_patch_size_spin.setMinimum(0)
            self.min_patch_size_spin.setSpecialValueText("")
            # Raster defaults: 10 px minimum patch size.
            self.min_patch_size_spin.setValue(10)
        except Exception:  # nosec
            pass
        try:
            self.vector_min_patch_size_spin.setMinimum(0.0)
            self.vector_min_patch_size_spin.setSpecialValueText("")
            self.vector_min_patch_size_spin.setValue(0.0)
        except Exception:  # nosec
            pass
        try:
            # Raster defaults: 20 px budget.
            self.budget_spin.setValue(20)
        except Exception:  # nosec
            pass
        try:
            # Raster defaults: 3 px corridor width.
            self.min_corridor_width_spin.setValue(3)
        except Exception:  # nosec
            pass
        try:
            # Raster defaults: 300 px search distance.
            self.max_search_spin.setValue(300)
        except Exception:  # nosec
            pass
        try:
            # Vector defaults: 1 ha budget, 20 m corridor width, 5 km search radius.
            if self.vector_units_combo.currentData() == "imperial":
                self.vector_budget_spin.setValue(round(1.0 * 2.471053814, 4))  # ha -> ac
                self.vector_min_corridor_width_spin.setValue(round(20.0 * 3.280839895, 4))  # m -> ft
                self.vector_max_search_spin.setValue(round(5.0 * 0.621371192237334, 4))  # km -> mi
            else:
                self.vector_budget_spin.setValue(1.0)
                self.vector_min_corridor_width_spin.setValue(20.0)
                self.vector_max_search_spin.setValue(5.0)
        except Exception:  # nosec
            pass
    def _load_help_content(self) -> None:
        """Load markdown help content into the right-hand panel."""
        if self._help_browser is None:
            return
        help_path = os.path.join(os.path.dirname(__file__), "terralink_help.md")
        if not os.path.exists(help_path):
            self._help_browser.setPlainText("TerraLink\n\nHelp file not found.")
            return
        try:
            with open(help_path, "r", encoding="utf-8") as fh:
                text = fh.read()
            # Try to render Markdown
            try:
                import markdown  # type: ignore
                html = markdown.markdown(text, extensions=["extra"])
                self._help_browser.setHtml(html)
            except ImportError:
                # Fallback if markdown lib is missing: Use plain text (wrap mode handles long lines).
                self._help_browser.setPlainText(text)
            except Exception as e:
                # Fallback for other errors
                self._help_browser.setPlainText(f"Error loading help:\n{e}\n\n{text}")

        except Exception as exc:  # pragma: no cover - UI only
            self._help_browser.setPlainText(f"TerraLink help could not be loaded:\n{exc}")

    def populate_layers(self):
        self.available_layers.clear()
        self.input_layer_combo.clear()

        project = QgsProject.instance()
        selected_type = self._current_layer_type
        if selected_type == "vector":
            target_cls = QgsVectorLayer
        else:
            target_cls = QgsRasterLayer

        layers = [
            layer
            for layer in project.mapLayers().values()
            if isinstance(layer, target_cls) and layer.isValid()
        ]

        if not layers:
            label = "No raster layers available" if selected_type == "raster" else "No vector layers available"
            self.input_layer_combo.addItem(label, None)
            self.input_layer_combo.setEnabled(False)
            self._selected_layer_id = None
            return

        self.input_layer_combo.setEnabled(True)
        for lyr in layers:
            self.available_layers[lyr.id()] = lyr
            self.input_layer_combo.addItem(lyr.name(), lyr.id())

        active_layer = self.iface.activeLayer() if self.iface else None
        if isinstance(active_layer, target_cls) and active_layer.id() in self.available_layers:
            index = self.input_layer_combo.findData(active_layer.id())
            if index >= 0:
                self.input_layer_combo.setCurrentIndex(index)
        else:
            self.input_layer_combo.setCurrentIndex(0)

        self._on_layer_changed(self.input_layer_combo.currentIndex())
        self._populate_vector_obstacle_layers()
        self._update_vector_obstacle_selector_text()

    def _populate_vector_obstacle_layers(self):
        lst = self.vector_obstacle_layer_list
        lst.blockSignals(True)
        lst.clear()
        try:
            lst.setSelectionMode(QListWidget.MultiSelection)
        except Exception:  # nosec
            pass
        project = QgsProject.instance()
        valid_layers = 0
        for layer in project.mapLayers().values():
            if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
                continue
            if QgsWkbTypes.geometryType(layer.wkbType()) != QgsWkbTypes.PolygonGeometry:
                continue
            item = QListWidgetItem(layer.name())
            item.setData(Qt.UserRole, layer.id())
            lst.addItem(item)
            valid_layers += 1

        if valid_layers == 0:
            placeholder = QListWidgetItem("No polygon layers available")
            placeholder.setFlags(Qt.NoItemFlags)
            lst.addItem(placeholder)
            lst.setEnabled(False)
        else:
            lst.setEnabled(True)

        lst.blockSignals(False)
        self._update_vector_obstacle_selector_text()
        self._update_vector_obstacle_controls(True)

    def _selected_vector_obstacle_layer_ids(self) -> List[str]:
        ids: List[str] = []
        for i in range(self.vector_obstacle_layer_list.count()):
            item = self.vector_obstacle_layer_list.item(i)
            if item is None or not item.isSelected():
                continue
            if not (item.flags() & Qt.ItemIsEnabled):
                continue
            layer_id = item.data(Qt.UserRole)
            if layer_id:
                ids.append(layer_id)
        return ids

    def _update_vector_obstacle_selector_text(self) -> None:
        if not hasattr(self, "vector_obstacle_selection_line"):
            return
        ids = self._selected_vector_obstacle_layer_ids()
        n = len(ids)
        if n == 0:
            text = "0 inputs selected"
        elif n == 1:
            text = "1 layer selected"
        else:
            text = f"{n} layers selected"
        try:
            self.vector_obstacle_selection_line.setText(text)
        except Exception:  # nosec
            pass
        try:
            project = QgsProject.instance()
            names = []
            for lid in ids:
                lyr = project.mapLayer(lid)
                if lyr is not None:
                    names.append(lyr.name())
            tooltip = "\n".join(names) if names else text
            self.vector_obstacle_selection_line.setToolTip(tooltip)
        except Exception:  # nosec
            pass

    def _choose_vector_obstacle_layers(self) -> None:
        dlg = QDialog(self)
        dlg.setWindowTitle("Select impassable layers")
        layout = QVBoxLayout(dlg)
        layers_list = QListWidget()
        layers_list.setSelectionMode(QListWidget.MultiSelection)
        layout.addWidget(layers_list)

        current_ids = set(self._selected_vector_obstacle_layer_ids())
        project = QgsProject.instance()
        for layer in project.mapLayers().values():
            if not isinstance(layer, QgsVectorLayer) or not layer.isValid():
                continue
            if QgsWkbTypes.geometryType(layer.wkbType()) != QgsWkbTypes.PolygonGeometry:
                continue
            item = QListWidgetItem(layer.name())
            item.setData(Qt.UserRole, layer.id())
            if layer.id() in current_ids:
                item.setSelected(True)
            layers_list.addItem(item)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        layout.addWidget(buttons)
        buttons.accepted.connect(dlg.accept)
        buttons.rejected.connect(dlg.reject)

        if dlg.exec_() != QDialog.Accepted:
            return

        chosen = set()
        for i in range(layers_list.count()):
            item = layers_list.item(i)
            if item is None or not item.isSelected():
                continue
            layer_id = item.data(Qt.UserRole)
            if layer_id:
                chosen.add(layer_id)

        self.vector_obstacle_layer_list.blockSignals(True)
        for i in range(self.vector_obstacle_layer_list.count()):
            item = self.vector_obstacle_layer_list.item(i)
            if item is None:
                continue
            layer_id = item.data(Qt.UserRole)
            item.setSelected(bool(layer_id and layer_id in chosen))
        self.vector_obstacle_layer_list.blockSignals(False)
        self._update_vector_obstacle_selector_text()

    def _toggle_help_panel(self) -> None:
        if not hasattr(self, "help_panel") or not hasattr(self, "main_splitter"):
            return
        self._help_visible = not bool(getattr(self, "_help_visible", False))
        try:
            self.help_panel.setVisible(self._help_visible)
        except Exception:
            return
        try:
            if self._help_visible:
                self._load_help_content()
                self.main_splitter.setSizes([9999, 380])
            else:
                self.main_splitter.setSizes([9999, 0])
        except Exception:  # nosec
            pass

    # ------------------------------------------------------------------
    # Slots
    # ------------------------------------------------------------------

    def _choose_output_dir(self):
        start_dir = self.output_dir_line.text() or os.path.expanduser("~")
        directory = QFileDialog.getExistingDirectory(self, "Select Output Directory", start_dir)
        if directory:
            self.output_dir_line.setText(directory)

    def _on_layer_changed(self, index: int):
        layer = self._layer_from_index(index)
        if layer:
            self._selected_layer_id = layer.id()
            if not self.temporary_output_checkbox.isChecked() and not self.output_dir_line.text():
                self.output_dir_line.setText(os.path.dirname(layer.source()))
            if (
                self._current_layer_type == "vector"
                and self.vector_output_name_line.text().strip() in ("", "optimized_corridors.gpkg", "terralink_corridors.gpkg")
            ):
                base_name = f"{layer.name()}_terralink.gpkg"
                self.vector_output_name_line.setText(base_name)
            self._update_vector_obstacle_selector_text()

    def _on_temporary_toggled(self, checked: bool):
        self.output_dir_line.setEnabled(not checked)
        self.output_browse_button.setEnabled(not checked)
        if checked:
            self.output_dir_line.clear()

    def _update_vector_units_labels(self, _: str):
        new_units = self.vector_units_combo.currentData()
        if not hasattr(self, "_vector_unit_system"):
            self._vector_unit_system = "metric"

        if new_units == self._vector_unit_system:
            # Still update labels in case they were not initialised
            pass
        else:
            if new_units == "imperial":
                # Convert existing values from metric to imperial
                self.vector_min_corridor_width_spin.setValue(
                    round(self.vector_min_corridor_width_spin.value() * 3.280839895, 4)
                )
                self.vector_max_search_spin.setValue(
                    round(self.vector_max_search_spin.value() * 0.621371192237334, 4)
                )
                self.vector_min_patch_size_spin.setValue(
                    round(self.vector_min_patch_size_spin.value() * 2.471053814, 4)
                )
                self.vector_budget_spin.setValue(
                    round(self.vector_budget_spin.value() * 2.471053814, 4)
                )
            else:
                # Convert imperial to metric
                self.vector_min_corridor_width_spin.setValue(
                    round(self.vector_min_corridor_width_spin.value() * 0.3048, 4)
                )
                self.vector_max_search_spin.setValue(
                    round(self.vector_max_search_spin.value() * 1.609344, 4)
                )
                self.vector_min_patch_size_spin.setValue(
                    round(self.vector_min_patch_size_spin.value() * 0.404685642, 4)
                )
                self.vector_budget_spin.setValue(
                    round(self.vector_budget_spin.value() * 0.404685642, 4)
                )
            self._vector_unit_system = new_units

        if self.vector_units_combo.currentData() == "imperial":
            self.label_vector_min_width.setText("Corridor Width (ft):")
            self.label_vector_max_search.setText("Search Radius (mi):")
            self.label_vector_min_patch.setText("Min Patch Size (ac):")
            self.label_vector_budget.setText("Budget (ac):")
            if hasattr(self, "label_vector_max_area"):
                self.label_vector_max_area.setText("Max Corridor Area (ac):")
        else:
            self.label_vector_min_width.setText("Corridor Width (m):")
            self.label_vector_max_search.setText("Search Radius (km):")
            self.label_vector_min_patch.setText("Min Patch Size (ha):")
            self.label_vector_budget.setText("Budget (ha):")
            if hasattr(self, "label_vector_max_area"):
                self.label_vector_max_area.setText("Max Corridor Area (ha):")

    def _map_units_to_meters(self, units: int) -> Optional[float]:
        if units == QgsUnitTypes.DistanceMeters:
            return 1.0
        if units == QgsUnitTypes.DistanceFeet:
            return 0.3048
        # QGIS enum names for US survey feet vary by version.
        feet_us_candidates = (
            getattr(QgsUnitTypes, "DistanceFeetUS", None),
            getattr(QgsUnitTypes, "DistanceUSSurveyFeet", None),
            getattr(QgsUnitTypes, "DistanceFootUS", None),
            getattr(QgsUnitTypes, "DistanceUSSurveyFoot", None),
        )
        for enum_val in feet_us_candidates:
            if enum_val is not None and units == enum_val:
                return 0.3048006096
        return None

    def _raster_pixel_size_m(self) -> Optional[Tuple[float, float]]:
        layer = self._layer_from_index(self.input_layer_combo.currentIndex())
        if layer is None or not isinstance(layer, QgsRasterLayer) or not layer.isValid():
            return None
        try:
            res_x = abs(float(layer.rasterUnitsPerPixelX()))
            res_y = abs(float(layer.rasterUnitsPerPixelY()))
        except Exception:
            return None
        if res_x <= 0 or res_y <= 0:
            return None
        units_to_m = self._map_units_to_meters(layer.crs().mapUnits())
        if units_to_m is None:
            return None
        return res_x * units_to_m, res_y * units_to_m

    def _update_raster_units_labels(self, _: str):
        new_units = self.raster_units_combo.currentData() or "pixels"
        if not hasattr(self, "_raster_unit_system"):
            self._raster_unit_system = "pixels"

        if new_units != self._raster_unit_system:
            pixel_sizes = self._raster_pixel_size_m()
            if pixel_sizes is None:
                self._append_log(
                    "Raster unit conversion requires a projected CRS (meters/feet). "
                    "Values left unchanged; reproject or switch to Pixels.",
                    "WARNING",
                )
            else:
                res_x_m, res_y_m = pixel_sizes
                pixel_area_m2 = res_x_m * res_y_m
                pixel_size_m = max(res_x_m, res_y_m)

                def area_to_pixels(value: float, units: str) -> float:
                    if units == "pixels":
                        return value
                    if units == "metric":
                        return value * 10000.0 / pixel_area_m2
                    return value * 4046.8564224 / pixel_area_m2

                def area_from_pixels(value: float, units: str) -> float:
                    if units == "pixels":
                        return value
                    if units == "metric":
                        return value * pixel_area_m2 / 10000.0
                    return value * pixel_area_m2 / 4046.8564224

                def width_to_pixels(value: float, units: str) -> float:
                    if units == "pixels":
                        return value
                    if units == "metric":
                        return value / pixel_size_m
                    return (value * 0.3048) / pixel_size_m

                def width_from_pixels(value: float, units: str) -> float:
                    if units == "pixels":
                        return value
                    if units == "metric":
                        return value * pixel_size_m
                    return value * pixel_size_m / 0.3048

                def search_to_pixels(value: float, units: str) -> float:
                    if units == "pixels":
                        return value
                    if units == "metric":
                        return (value * 1000.0) / pixel_size_m
                    return (value * 1609.344) / pixel_size_m

                def search_from_pixels(value: float, units: str) -> float:
                    if units == "pixels":
                        return value
                    if units == "metric":
                        return (value * pixel_size_m) / 1000.0
                    return (value * pixel_size_m) / 1609.344

                old_units = self._raster_unit_system
                min_patch_px = area_to_pixels(float(self.min_patch_size_spin.value()), old_units)
                budget_px = area_to_pixels(float(self.budget_spin.value()), old_units)
                min_width_px = width_to_pixels(float(self.min_corridor_width_spin.value()), old_units)
                max_search_px = search_to_pixels(float(self.max_search_spin.value()), old_units)
                self.min_patch_size_spin.setValue(int(round(max(0.0, area_from_pixels(min_patch_px, new_units)))))
                self.budget_spin.setValue(int(round(max(0.0, area_from_pixels(budget_px, new_units)))))
                self.min_corridor_width_spin.setValue(
                    int(round(max(1.0, width_from_pixels(min_width_px, new_units))))
                )
                self.max_search_spin.setValue(int(round(max(0.0, search_from_pixels(max_search_px, new_units)))))

        self._raster_unit_system = new_units
        if new_units == "imperial":
            self.label_7.setText("Min patch size (ac):")
            self.label_8.setText("Budget (ac):")
            self.label_10.setText("Corridor width (ft):")
            self.label_9.setText("Search radius (mi):")
        elif new_units == "metric":
            self.label_7.setText("Min patch size (ha):")
            self.label_8.setText("Budget (ha):")
            self.label_10.setText("Corridor width (m):")
            self.label_9.setText("Search radius (km):")
        else:
            self.label_7.setText("Min patch size (px):")
            self.label_8.setText("Budget (px):")
            self.label_10.setText("Corridor width (px):")
            self.label_9.setText("Search radius (px):")

    def _on_strategy_changed(self, _index: int):
        self._update_strategy_help()

    def _update_obstacle_controls(self, enabled: bool):
        is_enabled = bool(enabled)
        self.label_obstacle_value.setEnabled(is_enabled)
        self.obstacle_value_line.setEnabled(is_enabled)
        if not is_enabled:
            self.obstacle_value_line.clear()

    def _update_vector_obstacle_controls(self, enabled: bool):
        is_enabled = bool(enabled)
        self.label_vector_obstacle_layer.setEnabled(is_enabled)
        selectable = any(
            self.vector_obstacle_layer_list.item(i).flags() & Qt.ItemIsEnabled
            for i in range(self.vector_obstacle_layer_list.count())
        )
        if hasattr(self, "vector_obstacle_selection_line"):
            self.vector_obstacle_selection_line.setEnabled(is_enabled and selectable)
        if hasattr(self, "vector_obstacle_select_button"):
            self.vector_obstacle_select_button.setEnabled(is_enabled and selectable)
        self.label_vector_obstacle_resolution.setEnabled(is_enabled)
        self.vector_obstacle_resolution_spin.setEnabled(is_enabled)
        if not is_enabled:
            self.vector_obstacle_layer_list.clearSelection()
            self._update_vector_obstacle_selector_text()

    def _on_layer_type_changed(self, text: str):
        previous_strategy = self.strategy_combo.currentData() or self.strategy_combo.currentText()
        self._current_layer_type = (text or "Raster").lower()
        self._populate_strategy_combo(str(previous_strategy or "most_connected_networks_2"))
        self._update_group_visibility()
        self.populate_layers()

    def _update_group_visibility(self):
        is_raster = self._current_layer_type == "raster"
        # Conditional rows inside reframed UI.
        if hasattr(self, "_raster_patch_row"):
            self._raster_patch_row.setVisible(is_raster)
        if hasattr(self, "_vector_patch_row"):
            self._vector_patch_row.setVisible(not is_raster)
        if hasattr(self, "_raster_units_row"):
            self._raster_units_row.setVisible(is_raster)
        if hasattr(self, "_vector_units_row"):
            self._vector_units_row.setVisible(not is_raster)
        if hasattr(self, "_raster_neighborhood_row"):
            self._raster_neighborhood_row.setVisible(is_raster)
        if hasattr(self, "_raster_constraints_row"):
            self._raster_constraints_row.setVisible(is_raster)
        if hasattr(self, "_vector_constraints_row"):
            self._vector_constraints_row.setVisible(not is_raster)
        if hasattr(self, "_raster_obstacles_row"):
            self._raster_obstacles_row.setVisible(is_raster)
        if hasattr(self, "_vector_obstacles_row"):
            self._vector_obstacles_row.setVisible(not is_raster)
        if hasattr(self, "_obstacles_stack"):
            try:
                self._obstacles_stack.setCurrentIndex(0 if is_raster else 1)
            except Exception:  # nosec
                pass
        if hasattr(self, "_vector_output_name_row"):
            self._vector_output_name_row.setVisible(not is_raster)

    # ------------------------------------------------------------------
    # Data extraction helpers
    # ------------------------------------------------------------------

    def _layer_from_index(self, index: int) -> Optional[Union[QgsRasterLayer, QgsVectorLayer]]:
        layer_id = self.input_layer_combo.itemData(index)
        if not layer_id:
            return None
        return self.available_layers.get(layer_id)

    def get_selected_layer(self) -> Optional[QgsRasterLayer]:
        layer_id = self._parameters.get("layer_id") or self._selected_layer_id
        if not layer_id:
            return None
        layer = QgsProject.instance().mapLayer(layer_id)
        if isinstance(layer, (QgsRasterLayer, QgsVectorLayer)) and layer.isValid():
            return layer
        return self.available_layers.get(layer_id)

    def get_layer_id(self) -> Optional[str]:
        return self._parameters.get("layer_id")

    def get_output_directory(self) -> str:
        return self._parameters.get("output_dir", "")

    def get_parameters(self) -> Dict:
        return self._parameters.get("params", {})

    def get_strategy(self) -> str:
        return str(self.strategy_combo.currentData() or "most_connected_networks_2")

    def use_temporary_output(self) -> bool:
        return self._parameters.get("use_temporary_output", False)

    def get_layer_type(self) -> str:
        return self._parameters.get("layer_type", self._current_layer_type)

    # ------------------------------------------------------------------
    # Validation and acceptance
    # ------------------------------------------------------------------

    def _parse_values(self, text: str) -> List[float]:
        if not text.strip():
            return []
        values = []
        for token in text.split(","):
            token = token.strip()
            if not token:
                continue
            try:
                values.append(float(token))
            except ValueError as exc:
                raise ValueError(f"Invalid value '{token}' in Ecosystem Values.") from exc
        return values

    def _count_feature_polygon_parts(self, layer: QgsVectorLayer) -> Dict[str, object]:
        """
        Detect features that contain multiple polygon parts (multipart geometries).
        Each multipart feature can silently combine distinct patches into one patch.
        """
        summary: Dict[str, object] = {
            "multipart_features": 0,
            "multipart_parts_total": 0,
            "max_parts_in_feature": 0,
            "examples": [],
        }
        try:
            if QgsWkbTypes.geometryType(layer.wkbType()) != QgsWkbTypes.PolygonGeometry:
                return summary
        except Exception:
            return summary

        examples: List[str] = []
        multipart_features = 0
        multipart_parts_total = 0
        max_parts = 0

        for feature in layer.getFeatures():
            try:
                geom = feature.geometry()
            except Exception:  # nosec
                continue
            if geom is None or geom.isEmpty() or (not geom.isMultipart()):
                continue
            try:
                parts = len(geom.asMultiPolygon() or [])
            except Exception:
                parts = 0
            if parts <= 1:
                continue
            multipart_features += 1
            multipart_parts_total += int(parts)
            max_parts = max(max_parts, int(parts))
            if len(examples) < 3:
                examples.append(f"feature {feature.id()} ({parts} parts)")

        summary["multipart_features"] = int(multipart_features)
        summary["multipart_parts_total"] = int(multipart_parts_total)
        summary["max_parts_in_feature"] = int(max_parts)
        summary["examples"] = examples
        return summary

    def _confirm_vector_shared_patch_features(
        self,
        layer: QgsVectorLayer,
        summary: Optional[Dict[str, object]] = None,
    ) -> str:
        if summary is None:
            summary = self._count_feature_polygon_parts(layer)
        multipart_features = int(summary.get("multipart_features", 0) or 0)
        if multipart_features <= 0:
            return "continue"

        multipart_parts_total = int(summary.get("multipart_parts_total", 0) or 0)
        max_parts = int(summary.get("max_parts_in_feature", 0) or 0)
        examples = list(summary.get("examples", []) or [])
        examples_text = ", ".join(str(x) for x in examples) if examples else "none listed"

        msg = QMessageBox(self)
        msg.setIcon(QMessageBox.Warning)
        msg.setWindowTitle("Shared Patch Features Detected")
        msg.setText(
            "Some input features contain multiple patch groups in a single feature "
            "(multipart polygons)."
        )
        msg.setInformativeText(
            "TerraLink treats each feature as one patch before optimization.\n\n"
            f"Detected multipart features: {multipart_features}\n"
            f"Total multipart parts: {multipart_parts_total}\n"
            f"Max parts in one feature: {max_parts}\n"
            f"Examples: {examples_text}\n\n"
            "Choose Split to automatically create a singleparts copy, Continue if this is intentional, "
            "or Cancel to stop."
        )
        split_btn = msg.addButton("Split Features (recommended)", QMessageBox.ActionRole)
        continue_btn = msg.addButton("Continue (Intentional)", QMessageBox.AcceptRole)
        cancel_btn = msg.addButton("Cancel", QMessageBox.RejectRole)
        msg.setDefaultButton(cancel_btn)
        msg.exec_()
        clicked = msg.clickedButton()
        if clicked == split_btn:
            return "split"
        if clicked == continue_btn:
            return "continue"
        return "cancel"

    def _split_vector_layer_to_singleparts(self, layer: QgsVectorLayer) -> Optional[QgsVectorLayer]:
        """
        Create a temporary singleparts copy of a polygon layer and add it to the project.
        """
        try:
            crs_authid = layer.crs().authid() or "EPSG:4326"
            split_name = f"{layer.name()}_singleparts"
            out = QgsVectorLayer(f"Polygon?crs={crs_authid}", split_name, "memory")
            if not out.isValid():
                return None
            provider = out.dataProvider()
            provider.addAttributes(list(layer.fields()))
            out.updateFields()

            out_features: List[QgsFeature] = []
            for feature in layer.getFeatures():
                try:
                    src_geom = feature.geometry()
                except Exception:  # nosec
                    continue
                if src_geom is None or src_geom.isEmpty():
                    continue

                parts: List[QgsGeometry] = []
                if src_geom.isMultipart():
                    try:
                        mp = src_geom.asMultiPolygon() or []
                    except Exception:
                        mp = []
                    for poly in mp:
                        try:
                            part_geom = QgsGeometry.fromPolygonXY(poly)
                        except Exception:
                            part_geom = None
                        if part_geom is not None and not part_geom.isEmpty():
                            parts.append(part_geom)
                if not parts:
                    parts = [QgsGeometry(src_geom)]

                attrs = feature.attributes()
                for geom_part in parts:
                    out_feat = QgsFeature(out.fields())
                    out_feat.setGeometry(geom_part)
                    out_feat.setAttributes(attrs)
                    out_features.append(out_feat)

            if not out_features:
                return None

            provider.addFeatures(out_features)
            out.updateExtents()
            QgsProject.instance().addMapLayer(out)
            return out
        except Exception:
            return None

    def _confirm_vector_geometry_simplify(
        self,
        layer: QgsVectorLayer,
        summary: Dict[str, object],
    ) -> str:
        total_vertices = int(summary.get("total_vertices", 0) or 0)
        avg_vertices = float(summary.get("avg_vertices_per_feature", 0.0) or 0.0)
        max_feature_vertices = int(summary.get("max_feature_vertices", 0) or 0)
        hard_reasons = list(summary.get("hard_reasons", []) or [])
        example_rows = list(summary.get("top_examples", []) or [])
        example_text = ", ".join(
            f"feature {fid} ({count:,} vertices)" for count, fid in example_rows
        ) or "none listed"

        msg = QMessageBox(self)
        msg.setIcon(QMessageBox.Warning)
        msg.setWindowTitle("Geometry Too Complex")
        msg.setText(
            f"'{layer.name()}' is too geometrically complex for TerraLink to run reliably."
        )
        msg.setInformativeText(
            f"Patches: {int(summary.get('feature_count', 0) or 0):,}\n"
            f"Total vertices: {total_vertices:,}\n"
            f"Average vertices per patch: {avg_vertices:,.0f}\n"
            f"Largest patch vertices: {max_feature_vertices:,}\n"
            f"Examples: {example_text}\n\n"
            f"Triggered limits:\n- " + "\n- ".join(str(x) for x in hard_reasons) + "\n\n"
            "Choose Simplify to create a simplified copy and retry, or Cancel to stop."
        )
        simplify_btn = msg.addButton("Simplify", QMessageBox.ActionRole)
        cancel_btn = msg.addButton("Cancel", QMessageBox.RejectRole)
        msg.setDefaultButton(cancel_btn)
        msg.exec_()
        return "simplify" if msg.clickedButton() == simplify_btn else "cancel"

    def _suggest_vector_simplify_tolerance(self, layer: QgsVectorLayer) -> float:
        try:
            ext = layer.extent()
            max_dim = max(float(ext.width()), float(ext.height()))
        except Exception:
            max_dim = 0.0
        if max_dim <= 0.0:
            return 1.0
        return max(max_dim / 5000.0, max_dim / 50000.0)

    def _create_simplified_vector_copy(
        self,
        layer: QgsVectorLayer,
        tolerance: float,
    ) -> Optional[QgsVectorLayer]:
        try:
            geom_type_name = QgsWkbTypes.displayString(layer.wkbType()) or "MultiPolygon"
            crs_authid = layer.crs().authid() or "EPSG:4326"
            suffix = str(f"{float(tolerance):.6f}").rstrip("0").rstrip(".").replace(".", "p")
            out = QgsVectorLayer(f"{geom_type_name}?crs={crs_authid}", f"{layer.name()}_simplified_{suffix}", "memory")
            if not out.isValid():
                out = QgsVectorLayer(f"MultiPolygon?crs={crs_authid}", f"{layer.name()}_simplified_{suffix}", "memory")
            if not out.isValid():
                return None

            provider = out.dataProvider()
            provider.addAttributes(list(layer.fields()))
            out.updateFields()

            out_features: List[QgsFeature] = []
            for feature in layer.getFeatures():
                try:
                    geom = feature.geometry()
                except Exception:
                    geom = None
                if geom is None or geom.isEmpty():
                    continue
                try:
                    simplified = geom.simplify(float(tolerance))
                except Exception:
                    simplified = QgsGeometry(geom)
                if simplified is None or simplified.isEmpty():
                    simplified = QgsGeometry(geom)
                try:
                    simplified = simplified.makeValid()
                except Exception:  # nosec
                    pass
                if simplified is None or simplified.isEmpty():
                    continue
                out_feat = QgsFeature(out.fields())
                out_feat.setAttributes(feature.attributes())
                out_feat.setGeometry(simplified)
                out_features.append(out_feat)

            if not out_features:
                return None

            provider.addFeatures(out_features)
            out.updateExtents()
            QgsProject.instance().addMapLayer(out)
            return out
        except Exception:
            return None

    def _simplify_vector_layer_until_threshold(self, layer: QgsVectorLayer) -> Tuple[Optional[QgsVectorLayer], Optional[Dict[str, object]], Optional[float]]:
        from .analysis_vector import assess_vector_geometry_complexity

        base_tolerance = self._suggest_vector_simplify_tolerance(layer)
        tolerance = max(float(base_tolerance), 1e-9)
        last_summary: Optional[Dict[str, object]] = None

        for _ in range(6):
            simplified = self._create_simplified_vector_copy(layer, tolerance)
            if simplified is None or not simplified.isValid():
                return None, None, None
            summary = assess_vector_geometry_complexity(simplified)
            last_summary = summary
            if not bool(summary.get("exceeds_hard_limit", False)):
                return simplified, summary, float(tolerance)
            tolerance *= 2.0

        return None, last_summary, float(tolerance / 2.0)

    def _collect_parameters(self) -> Dict:
        params = self._collect_vector_parameters() if self._current_layer_type == "vector" else self._collect_raster_parameters()
        params["strategy"] = self.strategy_combo.currentData() or "most_connected_networks_2"
        return params

    def _collect_connectivity_metric_params(
        self,
        *,
        distance_scale: float = 1.0,
    ) -> Dict:
        alpha_raw = 1000.0
        cutoff_raw = 3000.0
        alpha_analysis = alpha_raw * max(float(distance_scale), 1e-12)
        cutoff_analysis = cutoff_raw * max(float(distance_scale), 1e-12)
        if cutoff_analysis <= 0.0:
            cutoff_analysis = 3.0 * alpha_analysis

        return {
            "pc_alpha": alpha_raw,
            "pc_cutoff": cutoff_raw,
            "pc_alpha_analysis": float(alpha_analysis),
            "pc_cutoff_analysis": float(cutoff_analysis),
            "redundancy_method": "ime",
            "sample_points": 50,
            "pair_samples": 200,
            "landscape_fluidity_shortcut_threshold": 3.0,
            "resiliency_shortcut_threshold": 3.0,
        }

    def _collect_raster_parameters(self) -> Dict:
        connectivity = int(self.pixel_neighborhood_combo.currentText())
        units = self.raster_units_combo.currentData() or "pixels"
        layer = self._layer_from_index(self.input_layer_combo.currentIndex())
        analysis_is_metric = bool(
            isinstance(layer, QgsRasterLayer)
            and layer.isValid()
            and layer.crs().mapUnits() == QgsUnitTypes.DistanceMeters
        )
        min_patch_value = float(self.min_patch_size_spin.value())
        budget_value = float(self.budget_spin.value())
        min_width_value = float(self.min_corridor_width_spin.value())
        max_search_value = float(self.max_search_spin.value())

        if units == "pixels":
            min_patch_px = int(round(min_patch_value))
            budget_px = int(round(budget_value))
            min_width_px = int(round(min_width_value))
            max_search_px = int(round(max_search_value))
            pixel_sizes = self._raster_pixel_size_m()
            pixel_size_m = max(pixel_sizes) if pixel_sizes is not None else None
            if analysis_is_metric and pixel_size_m and pixel_size_m > 0:
                connectivity_distance_scale = pixel_size_m
            else:
                connectivity_distance_scale = 1.0
        else:
            pixel_sizes = self._raster_pixel_size_m()
            if pixel_sizes is None:
                raise ValueError(
                    "Raster CRS must be projected (meters/feet) to use ha/ac units. "
                    "Reproject the raster or switch to Pixels."
                )
            res_x_m, res_y_m = pixel_sizes
            pixel_area_m2 = res_x_m * res_y_m
            pixel_size_m = max(res_x_m, res_y_m)
            if units == "metric":
                area_factor = 10000.0
                width_dist_factor = 1.0
                search_dist_factor = 1000.0
            else:
                area_factor = 4046.8564224
                width_dist_factor = 0.3048
                search_dist_factor = 1609.344
            min_patch_px = int(round((min_patch_value * area_factor) / pixel_area_m2))
            budget_px = int(round((budget_value * area_factor) / pixel_area_m2))
            min_width_px = int(round((min_width_value * width_dist_factor) / pixel_size_m))
            max_search_px = int(round((max_search_value * search_dist_factor) / pixel_size_m))
            if analysis_is_metric:
                connectivity_distance_scale = width_dist_factor
            else:
                connectivity_distance_scale = width_dist_factor / max(pixel_size_m, 1e-12)
        params = {
            "patch_connectivity": connectivity,
            "patch_mode": "value",
            "patch_values": [],
            "range_lower": None,
            "range_upper": None,
            "value_tolerance": 1e-6,
            "nodata_fallback": -9999.0,
            "min_patch_size": max(0, min_patch_px),
            "allow_sub_min_corridor": True,
            "budget_pixels": max(0, budget_px),
            "max_search_distance": max(0, max_search_px),
            "min_corridor_width": max(1, min_width_px),
            "allow_bottlenecks": self.allow_bottlenecks_checkbox.isChecked(),
            "obstacle_enabled": False,
            "obstacle_mode": "value",
            "obstacle_values": [],
            "obstacle_range_lower": None,
            "obstacle_range_upper": None,
            "raster_units": units,
            "corridor_cell_assignment": "sum_total_network_area",
        }

        if pixel_sizes is not None:
            if units == "metric":
                params["delegate_min_patch_size_ha"] = float(min_patch_value)
                params["delegate_budget_area_ha"] = float(budget_value)
                params["delegate_min_corridor_width_m"] = float(min_width_value)
                params["delegate_max_search_distance_m"] = float(max_search_value) * 1000.0
            elif units == "imperial":
                params["delegate_min_patch_size_ha"] = float(min_patch_value) * 4046.8564224 / 10000.0
                params["delegate_budget_area_ha"] = float(budget_value) * 4046.8564224 / 10000.0
                params["delegate_min_corridor_width_m"] = float(min_width_value) * 0.3048
                params["delegate_max_search_distance_m"] = float(max_search_value) * 1609.344

        values = self._parse_values(self.patch_value_line.text())
        if not values:
            raise ValueError("Enter at least one patch value.")
        params["patch_values"] = values

        obstacle_values = self._parse_values(self.obstacle_value_line.text())
        if obstacle_values:
            params["obstacle_enabled"] = True
            params["obstacle_values"] = obstacle_values

        params.update(
            self._collect_connectivity_metric_params(
                distance_scale=connectivity_distance_scale,
            )
        )

        return params

    def _collect_vector_parameters(self) -> Dict:
        output_name = self.vector_output_name_line.text().strip() or "terralink_corridors.gpkg"
        units = self.vector_units_combo.currentData() or "metric"

        width_value = self.vector_min_corridor_width_spin.value()
        search_value = self.vector_max_search_spin.value()
        min_patch_value = self.vector_min_patch_size_spin.value()
        budget_value = self.vector_budget_spin.value()
        resolution_value = self.vector_obstacle_resolution_spin.value()
        obstacle_layer_ids: List[str] = []
        for i in range(self.vector_obstacle_layer_list.count()):
            item = self.vector_obstacle_layer_list.item(i)
            if item is None or not item.isSelected():
                continue
            if not (item.flags() & Qt.ItemIsEnabled):
                continue
            layer_id = item.data(Qt.UserRole)
            if layer_id:
                obstacle_layer_ids.append(layer_id)

        if units == "imperial":
            width_value *= 0.3048
            search_value *= 1609.344
            min_patch_value *= 0.404685642
            budget_value *= 0.404685642
            resolution_value *= 0.3048
            connectivity_distance_scale = 0.3048
        else:
            search_value *= 1000.0
            connectivity_distance_scale = 1.0
        # Max corridor area removed from UI; no explicit limit is passed.

        obstacle_enabled = bool(obstacle_layer_ids)
        params = {
            "min_corridor_width": width_value,
            "min_patch_size": min_patch_value,
            "budget_area": budget_value,
            "max_search_distance": search_value,
            "output_name": output_name,
            "unit_system": units,
            "obstacle_enabled": obstacle_enabled,
            "obstacle_layer_ids": obstacle_layer_ids,
            "obstacle_layer_id": obstacle_layer_ids[0] if obstacle_layer_ids else None,
            "grid_resolution": resolution_value,
        }
        params.update(
            self._collect_connectivity_metric_params(
                distance_scale=connectivity_distance_scale,
            )
        )
        return params

    def accept(self):
        if getattr(self, "_run_in_progress", False):
            return

        # Run in-dialog so the Log tab can show progress and results.
        try:
            if hasattr(self, "tabs") and hasattr(self, "log_tab"):
                self.tabs.setCurrentWidget(self.log_tab)
        except Exception:  # nosec
            pass

        self._run_in_progress = True
        ok_btn = None
        try:
            ok_btn = self.button_box.button(QDialogButtonBox.Ok)
            if ok_btn is not None:
                ok_btn.setEnabled(False)
        except Exception:
            ok_btn = None

        self._reset_progress_display()
        self._set_progress_heartbeat_active(True)
        self._append_log("Starting TerraLink run…", "INFO")

        layer = self._layer_from_index(self.input_layer_combo.currentIndex())
        expected_cls = QgsRasterLayer if self._current_layer_type == "raster" else QgsVectorLayer
        if layer is None or not isinstance(layer, expected_cls) or not layer.isValid():
            msg = (
                "Select a valid raster layer before running."
                if self._current_layer_type == "raster"
                else "Select a valid vector layer before running."
            )
            self._append_log(msg, "ERROR")
            self._finish_progress_display(final_value=0, status_text="Run stopped")
            self._run_in_progress = False
            try:
                if ok_btn is not None:
                    ok_btn.setEnabled(True)
            except Exception:  # nosec
                pass
            return

        use_temporary = self.temporary_output_checkbox.isChecked()
        output_dir = self.output_dir_line.text().strip()
        if not use_temporary and not output_dir:
            msg = "Select an output directory (or enable Temporary output)."
            self._append_log(msg, "ERROR")
            self._finish_progress_display(final_value=0, status_text="Run stopped")
            self._run_in_progress = False
            try:
                if ok_btn is not None:
                    ok_btn.setEnabled(True)
            except Exception:  # nosec
                pass
            return

        try:
            params = self._collect_parameters()
            params["result_input_name"] = layer.name()
        except ValueError as exc:
            self._append_log(str(exc), "ERROR")
            self._finish_progress_display(final_value=0, status_text="Run stopped")
            self._run_in_progress = False
            try:
                if ok_btn is not None:
                    ok_btn.setEnabled(True)
            except Exception:  # nosec
                pass
            return

        strategy = params.pop("strategy", "most_connected_networks_2")

        # Ensure usable output directory (even for temporary runs)
        if use_temporary:
            if not output_dir:
                import tempfile

                output_dir = tempfile.mkdtemp(prefix="terralink_temp_")
                self._append_log(f"Created temporary output directory: {output_dir}", "INFO")
        else:
            try:
                os.makedirs(output_dir, exist_ok=True)
            except OSError as exc:
                msg = f"Unable to create or access the output directory:\n{exc}"
                self._append_log(msg, "ERROR")
                self._finish_progress_display(final_value=0, status_text="Run stopped")
                self._run_in_progress = False
                try:
                    if ok_btn is not None:
                        ok_btn.setEnabled(True)
                except Exception:  # nosec
                    pass
                return

        self._append_log(f"Layer: {layer.name()} ({self._current_layer_type})", "INFO")
        self._append_log(f"Strategy: {self._strategy_display_name(strategy)}", "INFO")

        # Keep the legacy parameter bundle updated (used by older call sites).
        self._parameters = {
            "layer_id": layer.id(),
            "layer_type": self._current_layer_type,
            "output_dir": output_dir,
            "params": params,
            "strategy": strategy,
            "use_temporary_output": use_temporary,
        }

        try:
            if self._current_layer_type == "vector":
                feat_count = 0
                try:
                    feat_count = layer.featureCount()
                except Exception:
                    feat_count = 0
                from .analysis_vector import (
                    _format_vector_landscape_scale_error,
                    assess_vector_geometry_complexity,
                    assess_vector_landscape_scale,
                    get_utm_crs_from_extent,
                )

                shared_summary = self._count_feature_polygon_parts(layer)
                has_shared_feature_groups = int(shared_summary.get("multipart_features", 0) or 0) > 0
                if feat_count <= 1 and not has_shared_feature_groups:
                    msg = (
                        "Vector mode requires multiple features (one per patch). "
                        "Your layer currently contains a single feature."
                    )
                    self._append_log(msg, "ERROR")
                    self._finish_progress_display(final_value=0, status_text="Run stopped")
                    self._run_in_progress = False
                    try:
                        if ok_btn is not None:
                            ok_btn.setEnabled(True)
                    except Exception:  # nosec
                        pass
                    return
                complexity_summary = assess_vector_geometry_complexity(layer)
                if bool(complexity_summary.get("exceeds_hard_limit", False)):
                    complexity_action = self._confirm_vector_geometry_simplify(layer, complexity_summary)
                    if complexity_action == "cancel":
                        self._append_log(
                            "Run canceled by user. Simplify the vector geometry and rerun.",
                            "WARNING",
                        )
                        self._finish_progress_display(final_value=0, status_text="Run canceled")
                        self._run_in_progress = False
                        try:
                            if ok_btn is not None:
                                ok_btn.setEnabled(True)
                        except Exception:  # nosec
                            pass
                        return
                    self._append_log(
                        "Input geometry exceeds TerraLink complexity limits. Attempting iterative simplification.",
                        "WARNING",
                    )
                    simplified_layer, simplified_summary, used_tolerance = self._simplify_vector_layer_until_threshold(layer)
                    if simplified_layer is None or not simplified_layer.isValid():
                        if simplified_summary:
                            self._append_log(
                                (
                                    "Automatic simplification did not reduce the layer below TerraLink's "
                                    f"complexity limit. Remaining totals: "
                                    f"{int(simplified_summary.get('total_vertices', 0) or 0):,} total vertices, "
                                    f"{float(simplified_summary.get('avg_vertices_per_feature', 0.0) or 0.0):,.0f} average vertices/patch."
                                ),
                                "ERROR",
                            )
                        else:
                            self._append_log(
                                "Automatic simplification failed before TerraLink could retry the run.",
                                "ERROR",
                            )
                        self._finish_progress_display(final_value=0, status_text="Run stopped")
                        self._run_in_progress = False
                        try:
                            if ok_btn is not None:
                                ok_btn.setEnabled(True)
                        except Exception:  # nosec
                            pass
                        return
                    layer = simplified_layer
                    self._append_log(
                        (
                            f"Created simplified layer '{layer.name()}' using tolerance {float(used_tolerance or 0.0):.6f}. "
                            f"Continuing with {int(simplified_summary.get('total_vertices', 0) or 0):,} total vertices."
                        ),
                        "INFO",
                    )
                    shared_summary = self._count_feature_polygon_parts(layer)
                    try:
                        self._parameters["layer_id"] = layer.id()
                    except Exception:  # nosec
                        pass
                    complexity_summary = assess_vector_geometry_complexity(layer)
                    if bool(complexity_summary.get("exceeds_hard_limit", False)):
                        for line in self._format_run_error(
                            "Automatic simplification completed, but the simplified layer still exceeds TerraLink's "
                            "geometry complexity limits."
                        ):
                            self._append_log(line, "ERROR")
                        self._finish_progress_display(final_value=0, status_text="Run stopped")
                        self._run_in_progress = False
                        try:
                            if ok_btn is not None:
                                ok_btn.setEnabled(True)
                        except Exception:  # nosec
                            pass
                        return
                try:
                    target_crs = get_utm_crs_from_extent(layer)
                    scale_summary = assess_vector_landscape_scale(
                        layer,
                        target_crs,
                        requested_max_search_distance=float(params.get("max_search_distance", 0.0) or 0.0),
                    )
                except Exception:
                    scale_summary = {}
                if bool(scale_summary.get("exceeds_hard_limit", False)):
                    for line in _format_vector_landscape_scale_error(scale_summary).splitlines():
                        self._append_log(line, "ERROR")
                    self._finish_progress_display(final_value=0, status_text="Run stopped")
                    self._run_in_progress = False
                    try:
                        if ok_btn is not None:
                            ok_btn.setEnabled(True)
                    except Exception:  # nosec
                        pass
                    return
                if bool(scale_summary.get("exceeds_warning_limit", False)):
                    warning_text = "; ".join(str(x) for x in list(scale_summary.get("warning_reasons", []) or []))
                    if warning_text:
                        self._append_log(f"Landscape scale warning: {warning_text}", "WARNING")
                shared_action = self._confirm_vector_shared_patch_features(layer, summary=shared_summary)
                if shared_action == "cancel":
                    self._append_log(
                        "Run canceled by user. Split multipart patch features into separate features, then rerun.",
                        "WARNING",
                    )
                    self._finish_progress_display(final_value=0, status_text="Run canceled")
                    self._run_in_progress = False
                    try:
                        if ok_btn is not None:
                            ok_btn.setEnabled(True)
                    except Exception:  # nosec
                        pass
                    return
                if shared_action == "split":
                    split_layer = self._split_vector_layer_to_singleparts(layer)
                    if split_layer is None or not split_layer.isValid():
                        self._append_log(
                            "Unable to split multipart features automatically. Please split manually and rerun.",
                            "ERROR",
                        )
                        self._finish_progress_display(final_value=0, status_text="Run stopped")
                        self._run_in_progress = False
                        try:
                            if ok_btn is not None:
                                ok_btn.setEnabled(True)
                        except Exception:  # nosec
                            pass
                        return
                    try:
                        self._append_log(
                            f"Created split layer '{split_layer.name()}' with {split_layer.featureCount()} features. Continuing with split layer.",
                            "INFO",
                        )
                    except Exception:
                        self._append_log(
                            f"Created split layer '{split_layer.name()}'. Continuing with split layer.",
                            "INFO",
                        )
                    layer = split_layer
                    try:
                        self._parameters["layer_id"] = layer.id()
                    except Exception:  # nosec
                        pass

            results = []
            if self._current_layer_type == "vector":
                from .analysis_vector import run_vector_analysis

                results = run_vector_analysis(
                    layer,
                    output_dir,
                    params,
                    strategy=strategy,
                    temporary=use_temporary,
                    iface=self.iface,
                    progress_cb=self._progress_log,
                    log_cb=self._append_log,
                )
            else:
                from .analysis_raster import run_raster_analysis

                results = run_raster_analysis(
                    layer,
                    output_dir,
                    params,
                    strategy=strategy,
                    temporary=use_temporary,
                    iface=self.iface,
                    progress_cb=self._progress_log,
                )

        except Exception as exc:  # noqa: BLE001
            for line in self._format_run_error(str(exc)):
                self._append_log(line, "CRITICAL")
            self._finish_progress_display(final_value=0, status_text="Run stopped (see Log)")
            self._run_in_progress = False
            try:
                if ok_btn is not None:
                    ok_btn.setEnabled(True)
            except Exception:  # nosec
                pass
            return

        if results:
            self._append_log("TerraLink analysis complete.", "INFO")
            for result in results:
                stats = result.get("stats", {}) or {}
                title = stats.get("layer_name", result.get("strategy", strategy))
                self._append_log(title, "SUMMARY")
                corridors_created = stats.get("corridors_used")
                patches_connected = stats.get("patches_connected") or stats.get("patches_merged")
                budget_used = stats.get("budget_used_display") or stats.get("budget_used")
                budget_total = stats.get("budget_total_display") or stats.get("budget_total")
                if corridors_created is not None:
                    self._append_log(f"  Corridors created: {corridors_created}", "SUMMARY")
                if patches_connected is not None:
                    self._append_log(f"  Patches connected: {patches_connected}", "SUMMARY")
                if budget_used is not None and budget_total is not None:
                    is_raster = "raster_rows" in stats or "raster_cols" in stats
                    if is_raster:
                        try:
                            budget_used = f"{float(budget_used):.2f}"
                            budget_total = f"{float(budget_total):.2f}"
                        except Exception:  # nosec
                            pass
                    self._append_log(f"  Budget used: {budget_used}/{budget_total}", "SUMMARY")
                if "networkmerge_objective_post" in stats:
                    area_value = stats.get("networkmerge_objective_post", 0)
                    area_units = ""
                    if self._current_layer_type == "vector":
                        area_value = stats.get("networkmerge_objective_display", area_value)
                        area_units = str(stats.get("area_units_label", "") or "").strip()
                        try:
                            area_display = f"{float(area_value):.2f}"
                        except Exception:
                            area_display = str(area_value)
                    else:
                        area_units = str(stats.get("raster_area_label", "") or "").strip()
                        try:
                            area_display = str(int(area_value))
                        except Exception:
                            area_display = str(area_value)
                    if area_units:
                        area_display = f"{area_display} {area_units}"
                    self._append_log(
                        f"  Connected network area: {area_display}",
                        "SUMMARY",
                    )
                if "networkmerge_proven_optimal" in stats:
                    self._append_log(
                        f"  Connected network area (proven optimal): {bool(stats.get('networkmerge_proven_optimal', False))}",
                        "SUMMARY",
                    )
                metrics_path = (stats.get("landscape_metrics_path") or "").strip()
                if metrics_path:
                    self._append_log(f"  Landscape metrics: {metrics_path}", "SUMMARY")
        else:
            self._append_log("No results were produced by the run.", "WARNING")

        self._finish_progress_display(final_value=100, status_text="Complete")
        # Keep dialog ready for additional runs without changing button labels.
        self._run_completed_successfully = False
        self._run_in_progress = False
        try:
            if ok_btn is not None:
                ok_btn.setEnabled(True)
        except Exception:  # nosec
            pass

        # Keep dialog open so the Log tab remains available.
        return
