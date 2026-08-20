from qgis.PyQt.QtCore import QCoreApplication
from qgis.core import QgsProcessingAlgorithm, QgsProcessingProvider


class TerraLinkLaunchAlgorithm(QgsProcessingAlgorithm):
    """Processing entry that opens the TerraLink dialog."""

    ALG_ID = "terralink_v1_7_corridor_generation"

    def __init__(self, plugin):
        super().__init__()
        self._plugin = plugin

    def name(self) -> str:
        return self.ALG_ID

    def displayName(self) -> str:
        return self.tr("Open TerraLink")

    def group(self) -> str:
        return self.tr("TerraLink")

    def groupId(self) -> str:
        return "terralink"

    def shortHelpString(self) -> str:
        return self.tr("Opens the TerraLink dialog so you can configure and run analyses.")

    def flags(self):
        return super().flags() | QgsProcessingAlgorithm.Flag.FlagNoThreading

    def tr(self, string: str) -> str:
        return QCoreApplication.translate("TerraLinkLaunchAlgorithm", string)

    def initAlgorithm(self, config=None):  # noqa: D401 - required override
        """No parameters to declare."""
        return

    def processAlgorithm(self, parameters, context, feedback):
        feedback.pushInfo(self.tr("Opening TerraLink dialog..."))
        self._plugin.run()
        return {}

    def createInstance(self):
        return TerraLinkLaunchAlgorithm(self._plugin)


class TerraLinkProcessingProvider(QgsProcessingProvider):
    """Processing provider that exposes the TerraLink launcher."""

    def __init__(self, plugin):
        super().__init__()
        self._plugin = plugin

    def id(self) -> str:
        return "terralink_v1_7"

    def name(self) -> str:
        return self.tr("SORUS")

    def tr(self, string: str) -> str:
        return QCoreApplication.translate("TerraLinkProcessingProvider", string)

    def loadAlgorithms(self):
        self.addAlgorithm(TerraLinkLaunchAlgorithm(self._plugin))
