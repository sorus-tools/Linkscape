import os

from qgis.PyQt.QtGui import QIcon
from qgis.PyQt.QtWidgets import QAction
from qgis.core import QgsApplication

from .processing_provider import TerraLinkProcessingProvider
try:
    from qgis.PyQt import sip
except Exception:  # pragma: no cover
    sip = None


class TerraLinkPlugin:
    def __init__(self, iface):
        self.iface = iface
        self.plugin_dir = os.path.dirname(__file__)
        self.action = None
        self.provider = None

    def _plugin_version_label(self) -> str:
        meta_path = os.path.join(self.plugin_dir, "metadata.txt")
        try:
            with open(meta_path, "r", encoding="utf-8") as fh:
                for raw in fh:
                    line = raw.strip()
                    if not line or line.startswith("#") or "=" not in line:
                        continue
                    key, val = line.split("=", 1)
                    if key.strip().lower() == "version":
                        v = val.strip()
                        return f"v{v}" if v else ""
        except Exception:  # nosec
            pass
        return ""

    def initGui(self):
        version_label = self._plugin_version_label()
        action_label = "Run TerraLink" if not version_label else f"Run TerraLink ({version_label})"
        self.action = QAction(action_label, self.iface.mainWindow())
        icon_path = os.path.join(self.plugin_dir, "icon.png")
        icon = QIcon(icon_path)
        if not icon.isNull():
            self.action.setIcon(icon)
        self.action.triggered.connect(self.run)
        self.iface.addToolBarIcon(self.action)
        menu_label = "&TerraLink" if not version_label else f"&TerraLink ({version_label})"
        self.iface.addPluginToMenu(menu_label, self.action)

        if self.provider is None:
            self.provider = TerraLinkProcessingProvider(self)
            QgsApplication.processingRegistry().addProvider(self.provider)

    def unload(self):
        if self.action is not None:
            self.iface.removeToolBarIcon(self.action)
            version_label = self._plugin_version_label()
            menu_label = "&TerraLink" if not version_label else f"&TerraLink ({version_label})"
            self.iface.removePluginMenu(menu_label, self.action)
        if self.provider is not None:
            try:
                registry = QgsApplication.processingRegistry()
                if registry is not None:
                    if sip is None or not sip.isdeleted(self.provider):
                        registry.removeProvider(self.provider)
            except RuntimeError:
                pass
            self.provider = None

    def run(self):
        from .terralink_dialog import TerraLinkDialog

        dialog = TerraLinkDialog(self.iface)
        dialog.exec_()
