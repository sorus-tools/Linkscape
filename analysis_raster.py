"""
TerraLink raster analysis.

Habitat inputs are polygonized into a temporary vector layer and processed by the
vector corridor engine. Raster impassables stay on the raster grid and are passed
through as a width-aware routing mask so obstacle runs do not pay repeated vector
geometry costs.
"""

from __future__ import annotations

import math
import os
import tempfile
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple

import numpy as np

try:
    from osgeo import gdal, ogr, osr
except ImportError:  # pragma: no cover
    gdal = None  # type: ignore
    ogr = None  # type: ignore
    osr = None  # type: ignore

try:
    from qgis.core import (
        QgsCoordinateTransform,
        QgsPointXY,
        QgsProject,
        QgsRasterLayer,
        QgsUnitTypes,
        QgsVectorLayer,
    )
except ImportError:  # pragma: no cover
    QgsCoordinateTransform = None  # type: ignore
    QgsPointXY = None  # type: ignore
    QgsProject = None  # type: ignore
    QgsRasterLayer = None  # type: ignore
    QgsUnitTypes = None  # type: ignore
    QgsVectorLayer = None  # type: ignore

from .landscape_metrics import _perform_landscape_analysis
from .utils import emit_progress

GTIFF_OPTIONS = ["COMPRESS=LZW", "TILED=YES", "BIGTIFF=IF_SAFER"]


class RasterAnalysisError(RuntimeError):
    """Raised when the raster analysis cannot be completed."""


@dataclass
class RasterRunParams:
    patch_connectivity: int
    patch_mode: str
    patch_values: List[float]
    range_lower: Optional[float]
    range_upper: Optional[float]
    obstacle_enabled: bool
    obstacle_mode: str
    obstacle_values: List[float]
    obstacle_range_lower: Optional[float]
    obstacle_range_upper: Optional[float]
    value_tolerance: float
    nodata_fallback: float
    min_patch_size: int
    budget_pixels: int
    max_search_distance: int
    min_corridor_width: int
    allow_bottlenecks: bool
    corridor_cell_assignment: str = "sum_total_network_area"


def _safe_filename(name: str, max_len: int = 64) -> str:
    safe = "".join(ch if (ch.isalnum() or ch in ("-", "_")) else "_" for ch in (name or ""))
    safe = safe.strip("_") or "layer"
    return safe[:max_len]


def _emit_progress(
    progress_cb: Optional[Callable[[int, Optional[str]], None]],
    value: float,
    message: Optional[str] = None,
) -> None:
    emit_progress(progress_cb, value, message)


def _normalize_corridor_cell_assignment(mode: Optional[str]) -> str:
    key = str(mode or "sum_total_network_area").strip().lower().replace(" ", "_")
    legacy = {
        "sum_patches_connected": "sum_direct_connected_patches",
        "newly_connected_area": "sum_total_network_area",
    }
    key = legacy.get(key, key)
    if key not in ("sum_direct_connected_patches", "sum_total_network_area", "efficiency"):
        key = "sum_total_network_area"
    return key


def read_band(
    band: "gdal.Band",
    rows: int,
    cols: int,
    progress_cb: Optional[Callable[[int, Optional[str]], None]] = None,
    progress_start: int = 0,
    progress_end: int = 10,
) -> np.ndarray:
    """Read a raster band as a numpy array with incremental progress updates."""
    data = np.empty((rows, cols), dtype=np.float32)
    chunk_rows = max(1, min(1024, rows // 50 or 1))
    span = max(progress_end - progress_start, 1)

    for start_row in range(0, rows, chunk_rows):
        this_rows = min(chunk_rows, rows - start_row)
        buf = band.ReadRaster(0, start_row, cols, this_rows, cols, this_rows, gdal.GDT_Float32)
        if not buf:
            raise RasterAnalysisError("Failed to read raster data chunk.")
        arr = np.frombuffer(buf, dtype=np.float32, count=cols * this_rows).reshape(this_rows, cols)
        data[start_row: start_row + this_rows] = arr

        if progress_cb is not None:
            ratio = (start_row + this_rows) / max(rows, 1)
            progress_value = progress_start + ratio * span
            _emit_progress(progress_cb, progress_value, "Reading raster data...")

    return data


def define_habitat(data: np.ndarray, nodata_mask: np.ndarray, params: RasterRunParams) -> np.ndarray:
    """Identify patch pixels based on the selected configuration."""
    valid = ~nodata_mask
    patches = np.zeros(data.shape, dtype=np.uint8)
    mode = params.patch_mode.lower()
    tol = params.value_tolerance

    if mode == "value" and params.patch_values:
        for val in params.patch_values:
            patches |= (np.abs(data - val) < tol) & valid
    elif mode == "range" and params.range_lower is not None and params.range_upper is not None:
        patches = ((data >= params.range_lower) & (data <= params.range_upper)) & valid
    else:
        raise RasterAnalysisError("Patch configuration did not yield any valid pixels.")

    return patches


def define_obstacles(data: np.ndarray, nodata_mask: np.ndarray, patch_mask: np.ndarray, params: RasterRunParams) -> np.ndarray:
    """Create a boolean mask for impassable pixels corridors must avoid."""
    del patch_mask
    if not params.obstacle_enabled:
        return np.zeros(data.shape, dtype=bool)

    mask = np.zeros(data.shape, dtype=bool)
    tol = params.value_tolerance
    mode = params.obstacle_mode.lower()

    if mode == "range" and params.obstacle_range_lower is not None and params.obstacle_range_upper is not None:
        lower = min(params.obstacle_range_lower, params.obstacle_range_upper)
        upper = max(params.obstacle_range_lower, params.obstacle_range_upper)
        mask = (data >= lower) & (data <= upper)
    elif mode == "value" and params.obstacle_values:
        for val in params.obstacle_values:
            mask |= np.abs(data - val) < tol
    else:
        return np.zeros(data.shape, dtype=bool)

    mask &= ~nodata_mask
    return mask


def _to_dataclass(params: Dict) -> RasterRunParams:
    return RasterRunParams(
        patch_connectivity=int(params.get("patch_connectivity", 4)),
        patch_mode=str(params.get("patch_mode", "value")).lower(),
        patch_values=list(params.get("patch_values", [])),
        range_lower=params.get("range_lower"),
        range_upper=params.get("range_upper"),
        obstacle_enabled=bool(params.get("obstacle_enabled", False)),
        obstacle_mode=str(params.get("obstacle_mode", "value")).lower(),
        obstacle_values=list(params.get("obstacle_values", [])),
        obstacle_range_lower=params.get("obstacle_range_lower"),
        obstacle_range_upper=params.get("obstacle_range_upper"),
        value_tolerance=float(params.get("value_tolerance", 1e-6)),
        nodata_fallback=float(params.get("nodata_fallback", -9999)),
        min_patch_size=int(params.get("min_patch_size", 30)),
        budget_pixels=int(params.get("budget_pixels", 10)),
        max_search_distance=int(params.get("max_search_distance", 50)),
        min_corridor_width=int(params.get("min_corridor_width", 1)),
        allow_bottlenecks=bool(params.get("allow_bottlenecks", True)),
        corridor_cell_assignment=_normalize_corridor_cell_assignment(params.get("corridor_cell_assignment")),
    )


def _map_units_to_meters(units: object) -> Optional[float]:
    if QgsUnitTypes is None:
        return None
    try:
        if units == QgsUnitTypes.DistanceMeters:
            return 1.0
        if units == QgsUnitTypes.DistanceFeet:
            return 0.3048
        feet_us_candidates = (
            getattr(QgsUnitTypes, "DistanceFeetUS", None),
            getattr(QgsUnitTypes, "DistanceUSSurveyFeet", None),
            getattr(QgsUnitTypes, "DistanceFootUS", None),
            getattr(QgsUnitTypes, "DistanceUSSurveyFoot", None),
        )
        for enum_val in feet_us_candidates:
            if enum_val is not None and units == enum_val:
                return 0.3048006096
    except Exception:
        return None
    return None


def _raster_pixel_size_m(layer: "QgsRasterLayer", gt: Tuple[float, ...]) -> Optional[Tuple[float, float]]:
    if layer is None or not layer.isValid():
        return None
    try:
        src_factor = _map_units_to_meters(layer.crs().mapUnits())
        if src_factor is not None:
            return abs(float(gt[1])) * src_factor, abs(float(gt[5] or gt[1])) * src_factor
    except Exception:  # nosec
        pass

    if QgsCoordinateTransform is None or QgsPointXY is None or QgsProject is None:
        return None

    try:
        from .analysis_vector import get_utm_crs_from_extent

        target_crs = get_utm_crs_from_extent(layer)
        transform = QgsCoordinateTransform(layer.crs(), target_crs, QgsProject.instance())
        extent = layer.extent()
        center = extent.center()
        p0 = transform.transform(QgsPointXY(center.x(), center.y()))
        px = transform.transform(QgsPointXY(center.x() + abs(float(gt[1])), center.y()))
        py = transform.transform(QgsPointXY(center.x(), center.y() + abs(float(gt[5] or gt[1]))))
        size_x = math.hypot(float(px.x()) - float(p0.x()), float(px.y()) - float(p0.y()))
        size_y = math.hypot(float(py.x()) - float(p0.x()), float(py.y()) - float(p0.y()))
        if size_x > 0.0 and size_y > 0.0:
            return float(size_x), float(size_y)
    except Exception:
        return None
    return None


def _write_mask_raster(path: str, mask: np.ndarray, gt: Tuple[float, ...], proj: str) -> None:
    drv = gdal.GetDriverByName("GTiff")
    rows, cols = mask.shape
    ds = drv.Create(path, cols, rows, 1, gdal.GDT_Byte, options=GTIFF_OPTIONS)
    if ds is None:
        raise RasterAnalysisError(f"Unable to create temporary mask raster: {path}")
    ds.SetGeoTransform(gt)
    ds.SetProjection(proj)
    band = ds.GetRasterBand(1)
    band.SetNoDataValue(0)
    band.WriteArray(mask.astype(np.uint8, copy=False))
    band.FlushCache()
    ds = None


def _simplify_polygon_layer_inplace(path: str, layer_name: str, tolerance: float) -> None:
    if ogr is None or tolerance <= 0.0:
        return
    ds = ogr.Open(path, update=1)
    if ds is None:
        return
    layer = ds.GetLayerByName(layer_name)
    if layer is None:
        ds = None
        return
    layer.ResetReading()
    for feat in layer:
        geom = feat.GetGeometryRef()
        if geom is None:
            continue
        try:
            simplified = geom.SimplifyPreserveTopology(float(tolerance))
        except Exception:
            simplified = None
        if simplified is None or simplified.IsEmpty():
            continue
        feat.SetGeometry(simplified)
        layer.SetFeature(feat)
    layer = None
    ds = None


def _polygonize_binary_mask(
    *,
    mask: np.ndarray,
    gt: Tuple[float, ...],
    proj: str,
    work_dir: str,
    stem: str,
    connectivity: int,
    display_name: str,
    simplify_tolerance: float = 0.0,
) -> "QgsVectorLayer":
    if gdal is None or ogr is None or osr is None or QgsVectorLayer is None:
        raise RasterAnalysisError("Raster-to-vector bridge requires GDAL/OGR and QGIS vector support.")

    safe_stem = _safe_filename(stem)
    raster_path = os.path.join(work_dir, f"{safe_stem}.tif")
    gpkg_path = os.path.join(work_dir, f"{safe_stem}.gpkg")
    layer_name = safe_stem or "mask"

    _write_mask_raster(raster_path, mask, gt, proj)

    gpkg_driver = ogr.GetDriverByName("GPKG")
    if gpkg_driver is None:
        raise RasterAnalysisError("OGR GPKG driver is unavailable.")
    if os.path.exists(gpkg_path):
        try:
            gpkg_driver.DeleteDataSource(gpkg_path)
        except Exception:  # nosec
            pass
    ds = gpkg_driver.CreateDataSource(gpkg_path)
    if ds is None:
        raise RasterAnalysisError(f"Unable to create temporary polygon layer: {gpkg_path}")

    srs = None
    if proj:
        try:
            srs = osr.SpatialReference()
            srs.ImportFromWkt(proj)
        except Exception:
            srs = None
    out_layer = ds.CreateLayer(layer_name, srs=srs, geom_type=ogr.wkbPolygon)
    if out_layer is None:
        ds = None
        raise RasterAnalysisError(f"Unable to create polygon layer '{layer_name}' in {gpkg_path}")
    out_layer.CreateField(ogr.FieldDefn("value", ogr.OFTInteger))

    src_ds = gdal.Open(raster_path)
    if src_ds is None:
        ds = None
        raise RasterAnalysisError(f"Unable to reopen temporary mask raster: {raster_path}")
    src_band = src_ds.GetRasterBand(1)
    options = ["8CONNECTED=8"] if int(connectivity) == 8 else []
    gdal.Polygonize(src_band, None, out_layer, 0, options)
    out_layer = None
    ds = None
    src_ds = None

    if simplify_tolerance > 0.0:
        _simplify_polygon_layer_inplace(gpkg_path, layer_name, simplify_tolerance)

    layer = QgsVectorLayer(f"{gpkg_path}|layername={layer_name}", display_name, "ogr")
    if not layer.isValid():
        raise RasterAnalysisError(f"Polygonized layer is invalid: {gpkg_path}|layername={layer_name}")
    try:
        layer.setSubsetString('"value" = 1')
    except Exception:  # nosec
        pass
    try:
        if int(layer.featureCount()) <= 0:
            raise RasterAnalysisError(f"Polygonized layer '{display_name}' contains no habitat polygons.")
    except RasterAnalysisError:
        raise
    except Exception:  # nosec
        pass
    return layer


def _build_vector_delegate_params(
    *,
    layer: "QgsRasterLayer",
    raw_params: Dict,
    params: RasterRunParams,
    gt: Tuple[float, ...],
    obstacle_layer_ids: Optional[List[str]] = None,
) -> Dict:
    obstacle_layer_ids = [str(val) for val in (obstacle_layer_ids or []) if val]
    pixel_metrics = _raster_pixel_size_m(layer, gt)
    if pixel_metrics is None:
        raise RasterAnalysisError(
            "Raster-to-vector bridge requires a raster CRS that can be measured in meters. "
            "Reproject the raster to a projected CRS and rerun."
        )

    pixel_w_m, pixel_h_m = pixel_metrics
    pixel_size_m = max(float(pixel_w_m), float(pixel_h_m), 1e-9)
    pixel_area_ha = (float(pixel_w_m) * float(pixel_h_m)) / 10000.0
    unit_mode = str((raw_params or {}).get("raster_units", "pixels") or "pixels").strip().lower()

    def _float_or(default: float, *keys: str) -> float:
        for key in keys:
            if key not in raw_params:
                continue
            val = raw_params.get(key)
            if val is None or str(val).strip() == "":
                continue
            try:
                return float(val)
            except Exception:  # nosec
                continue
        return float(default)

    min_patch_size_ha = _float_or(float(params.min_patch_size) * pixel_area_ha, "delegate_min_patch_size_ha")
    budget_area_ha = _float_or(float(params.budget_pixels) * pixel_area_ha, "delegate_budget_area_ha")
    min_corridor_width_m = _float_or(float(params.min_corridor_width) * pixel_size_m, "delegate_min_corridor_width_m")
    max_search_distance_m = _float_or(float(params.max_search_distance) * pixel_size_m, "delegate_max_search_distance_m")

    vector_params = dict(raw_params or {})
    vector_params.update(
        {
            "min_corridor_width": float(min_corridor_width_m),
            "min_patch_size": float(min_patch_size_ha),
            "budget_area": float(budget_area_ha),
            "max_search_distance": float(max_search_distance_m),
            "output_name": str((raw_params or {}).get("output_name") or "terralink_corridors.gpkg"),
            "unit_system": "imperial" if unit_mode == "imperial" else "metric",
            "grid_resolution": float(max(pixel_size_m, 1.0)),
            "obstacle_enabled": bool(obstacle_layer_ids),
            "obstacle_layer_ids": obstacle_layer_ids,
            "obstacle_layer_id": obstacle_layer_ids[0] if obstacle_layer_ids else None,
            "result_input_name": str((raw_params or {}).get("result_input_name") or layer.name()),
            "result_input_layer_id": str((raw_params or {}).get("result_input_layer_id") or layer.id() or ""),
        }
    )
    return vector_params


def _augment_raster_delegate_stats(
    *,
    stats: Dict,
    layer: "QgsRasterLayer",
    params: RasterRunParams,
    raw_params: Dict,
    rows: int,
    cols: int,
    total_pixels: int,
    habitat_layer: "QgsVectorLayer",
    obstacle_layer: Optional["QgsVectorLayer"],
    obstacle_source: str = "",
    obstacle_count: int = 0,
    workspace: str,
    gt: Tuple[float, ...],
) -> Dict:
    out = dict(stats or {})
    pixel_metrics = _raster_pixel_size_m(layer, gt)
    if pixel_metrics is not None:
        pixel_w_m, pixel_h_m = pixel_metrics
        out["source_raster_pixel_width_m"] = float(pixel_w_m)
        out["source_raster_pixel_height_m"] = float(pixel_h_m)
        out["source_raster_pixel_area_ha"] = float((pixel_w_m * pixel_h_m) / 10000.0)
    out["source_raster_rows"] = int(rows)
    out["source_raster_cols"] = int(cols)
    out["source_raster_pixels_total"] = int(total_pixels)
    out["raster_delegate_backend"] = "vector_polygonize"
    out["raster_bridge_workspace"] = workspace
    out["raster_patch_connectivity"] = int(params.patch_connectivity)
    out["raster_patch_mode"] = str(params.patch_mode)
    out["raster_patch_values"] = list(params.patch_values)
    out["raster_obstacle_enabled"] = bool(params.obstacle_enabled)
    out["raster_obstacle_mode"] = str(params.obstacle_mode)
    out["raster_obstacle_values"] = list(params.obstacle_values)
    out["raster_input_units"] = str((raw_params or {}).get("raster_units", "pixels") or "pixels")
    out["raster_source_layer_name"] = str(layer.name())
    out["raster_polygon_patch_source"] = str(habitat_layer.source())
    out["raster_polygon_patch_count"] = int(habitat_layer.featureCount())
    if obstacle_source:
        out["raster_polygon_obstacle_source"] = str(obstacle_source)
        out["raster_polygon_obstacle_count"] = int(obstacle_count)
    elif obstacle_layer is not None:
        out["raster_polygon_obstacle_source"] = str(obstacle_layer.source())
        try:
            out["raster_polygon_obstacle_count"] = int(obstacle_layer.featureCount())
        except Exception:
            out["raster_polygon_obstacle_count"] = 0
    if "area_units_label" in out and "raster_area_label" not in out:
        out["raster_area_label"] = str(out.get("area_units_label", "") or "")
    if "budget_used_display" in out and "budget_total_display" in out:
        out["budget_used"] = float(out.get("budget_used_display", 0.0) or 0.0)
        out["budget_total"] = float(out.get("budget_total_display", 0.0) or 0.0)
    return out


def _run_raster_analysis_via_vector(
    layer: "QgsRasterLayer",
    output_dir: str,
    raw_params: Dict,
    strategy: str,
    temporary: bool,
    iface,
    progress_cb: Optional[Callable[[int, Optional[str]], None]],
    params: RasterRunParams,
) -> List[Dict]:
    if gdal is None:
        raise RasterAnalysisError("GDAL is required for the raster-to-vector bridge.")

    bridge_dir = tempfile.mkdtemp(prefix="terralink_raster_bridge_", dir=(output_dir or None))
    ds = gdal.Open(layer.source())
    if ds is None:
        raise RasterAnalysisError(f"Cannot open raster source: {layer.source()}")

    rows, cols = ds.RasterYSize, ds.RasterXSize
    total_pixels = int(rows * cols)
    gt = ds.GetGeoTransform()
    proj = ds.GetProjection()
    band = ds.GetRasterBand(1)
    nodata = band.GetNoDataValue()
    if nodata is None:
        nodata = params.nodata_fallback

    _emit_progress(progress_cb, 5, "Reading raster data...")
    data = read_band(
        band,
        rows,
        cols,
        progress_cb=progress_cb,
        progress_start=5,
        progress_end=18,
    )
    nodata_mask = np.abs(data - nodata) < params.value_tolerance if nodata is not None else np.zeros_like(
        data, dtype=bool
    )
    habitat_mask = define_habitat(data, nodata_mask, params).astype(np.uint8)
    if not np.any(habitat_mask):
        raise RasterAnalysisError("Selected habitat values did not produce any habitat pixels.")

    obstacle_mask = define_obstacles(data, nodata_mask, habitat_mask, params)
    ds = None

    _emit_progress(progress_cb, 22, "Polygonizing habitat...")
    habitat_layer = _polygonize_binary_mask(
        mask=habitat_mask,
        gt=gt,
        proj=proj,
        work_dir=bridge_dir,
        stem=f"{_safe_filename(layer.name())}_habitat",
        connectivity=params.patch_connectivity,
        display_name=str(layer.name()),
    )

    obstacle_layer: Optional[QgsVectorLayer] = None
    obstacle_layer_ids: List[str] = []
    obstacle_source = ""
    obstacle_count = 0
    if params.obstacle_enabled and np.any(obstacle_mask):
        _emit_progress(progress_cb, 28, "Preparing impassable routing mask...")

    vector_params = _build_vector_delegate_params(
        layer=layer,
        raw_params=raw_params,
        params=params,
        gt=gt,
        obstacle_layer_ids=obstacle_layer_ids,
    )
    if params.obstacle_enabled and np.any(obstacle_mask):
        vector_params["obstacle_enabled"] = True
        vector_params["_raster_obstacle_mask"] = obstacle_mask.astype(bool, copy=False)
        vector_params["_raster_obstacle_gt"] = tuple(float(v) for v in gt)
        vector_params["analysis_crs_authid"] = str(layer.crs().authid() or "")

    _emit_progress(progress_cb, 32, "Delegating to vector corridor engine...")
    from .analysis_vector import run_vector_analysis

    delegate_progress_start = 32.0
    delegate_progress_end = 100.0

    def _delegate_progress_cb(value: int, message: Optional[str] = None) -> None:
        try:
            inner = max(0.0, min(100.0, float(value)))
        except Exception:
            inner = 0.0
        outer = delegate_progress_start + ((delegate_progress_end - delegate_progress_start) * (inner / 100.0))
        _emit_progress(progress_cb, outer, message)

    try:
        results = run_vector_analysis(
            habitat_layer,
            output_dir,
            vector_params,
            strategy=strategy,
            temporary=temporary,
            iface=iface,
            progress_cb=_delegate_progress_cb if progress_cb is not None else None,
        )
    finally:
        if obstacle_layer is not None and QgsProject is not None:
            try:
                QgsProject.instance().removeMapLayer(obstacle_layer.id())
            except Exception:  # nosec
                pass

    for result in results or []:
        result_stats = result.get("stats", {}) or {}
        result["stats"] = _augment_raster_delegate_stats(
            stats=result_stats,
            layer=layer,
            params=params,
            raw_params=raw_params,
            rows=rows,
            cols=cols,
            total_pixels=total_pixels,
            habitat_layer=habitat_layer,
            obstacle_layer=obstacle_layer,
            obstacle_source=obstacle_source,
            obstacle_count=obstacle_count,
            workspace=bridge_dir,
            gt=gt,
        )
        if params.obstacle_enabled and np.any(obstacle_mask):
            result["stats"]["raster_delegate_backend"] = "vector_polygonize_raster_impassable_mask"
            result["stats"]["raster_obstacle_pixels"] = int(np.count_nonzero(obstacle_mask))
    return results or []


def run_raster_analysis(
    layer: "QgsRasterLayer",
    output_dir: str,
    raw_params: Dict,
    strategy: str = "most_connected_networks",
    temporary: bool = False,
    iface=None,
    progress_cb: Optional[Callable[[int, Optional[str]], None]] = None,
) -> List[Dict]:
    """Execute the raster corridor analysis for the provided layer."""
    if not isinstance(layer, QgsRasterLayer) or not layer.isValid():
        raise RasterAnalysisError("Selected layer is not a valid raster layer.")

    params = _to_dataclass(raw_params or {})
    return _run_raster_analysis_via_vector(
        layer,
        output_dir,
        raw_params or {},
        strategy,
        temporary,
        iface,
        progress_cb,
        params,
    )


__all__ = [
    "RasterAnalysisError",
    "RasterRunParams",
    "_perform_landscape_analysis",
    "run_raster_analysis",
]
