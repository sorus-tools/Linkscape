import time
from typing import Callable, Dict, Optional, Tuple

from qgis.core import Qgis
from qgis.PyQt.QtCore import QCoreApplication


_LAST_PROCESS_EVENTS_TS = 0.0
_LAST_PROGRESS_BY_CB: Dict[int, Tuple[int, str, float]] = {}


def emit_progress(cb: Optional[Callable[[int, Optional[str]], None]], value: float, msg: Optional[str] = None) -> None:
    """Safe progress emitter that tolerates callback errors."""
    global _LAST_PROCESS_EVENTS_TS
    if cb is None:
        return
    pct = int(max(0, min(100, value)))
    text = str(msg or "")
    try:
        now = time.perf_counter()
        cb_key = id(cb)
        last = _LAST_PROGRESS_BY_CB.get(cb_key)
        should_emit = True
        if last is not None:
            last_pct, last_msg, last_ts = last
            if pct == int(last_pct):
                if text == last_msg:
                    should_emit = False
                elif (now - float(last_ts)) < 0.75:
                    should_emit = False
        if should_emit:
            cb(pct, msg)
            _LAST_PROGRESS_BY_CB[cb_key] = (int(pct), text, float(now))
    except Exception:
        pass
    try:
        now = time.perf_counter()
        if (now - float(_LAST_PROCESS_EVENTS_TS)) >= 0.1:
            _LAST_PROCESS_EVENTS_TS = now
            QCoreApplication.processEvents()
    except Exception:
        pass


def log_error(iface, title: str, msg: str, level: int = Qgis.Critical) -> None:
    """Display an error via QGIS message bar if available, else print."""
    try:
        if iface and hasattr(iface, "messageBar"):
            iface.messageBar().pushMessage(title, msg, level=level)
        else:
            print(f"{title}: {msg}")
    except Exception:
        print(f"{title}: {msg}")
    raise RuntimeError(msg)
