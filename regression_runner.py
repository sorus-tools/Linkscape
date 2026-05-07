from __future__ import annotations

import importlib
import json
import shutil
import sys
from pathlib import Path

import numpy as np
from osgeo import gdal, osr
from qgis.PyQt.QtCore import QVariant
from qgis.core import (
    QgsFeature,
    QgsField,
    QgsGeometry,
    QgsPointXY,
    QgsProject,
    QgsVectorFileWriter,
    QgsVectorLayer,
)


PLUGIN_ROOT = Path(__file__).resolve().parent
PARENT_DIR = PLUGIN_ROOT.parent
ARTIFACT_ROOT = PARENT_DIR / "TerraLink_regression_artifacts"
BASELINE_JSON = ARTIFACT_ROOT / "baseline_results.json"
POSTFIX_JSON = ARTIFACT_ROOT / "postfix_results.json"


def _reload(name: str):
    return importlib.reload(importlib.import_module(name))


analysis_vector = _reload("TerraLink_v1_7.analysis_vector")
analysis_raster = _reload("TerraLink_v1_7.analysis_raster")


def _reset_dir(path: Path) -> None:
    if path.exists():
        shutil.rmtree(path)
    path.mkdir(parents=True, exist_ok=True)


def _rect(xmin: float, ymin: float, xmax: float, ymax: float) -> QgsGeometry:
    pts = [
        QgsPointXY(xmin, ymin),
        QgsPointXY(xmax, ymin),
        QgsPointXY(xmax, ymax),
        QgsPointXY(xmin, ymax),
        QgsPointXY(xmin, ymin),
    ]
    return QgsGeometry.fromPolygonXY([pts])


def _create_vector_layer(workdir: Path) -> QgsVectorLayer:
    layer = QgsVectorLayer("Polygon?crs=EPSG:3857", "Regression Vector Input", "memory")
    provider = layer.dataProvider()
    provider.addAttributes(
        [
            QgsField("patch_id", QVariant.Int),
            QgsField("quality", QVariant.Double),
        ]
    )
    layer.updateFields()

    specs = [
        (1, 1.0, 0.0, 0.0, 120.0, 120.0),
        (2, 0.8, 220.0, 20.0, 320.0, 120.0),
        (3, 0.6, 500.0, 0.0, 620.0, 120.0),
        (4, 0.9, 0.0, 260.0, 140.0, 380.0),
        (5, 0.7, 260.0, 260.0, 380.0, 380.0),
    ]
    features = []
    for patch_id, quality, xmin, ymin, xmax, ymax in specs:
        feat = QgsFeature(layer.fields())
        feat.setGeometry(_rect(xmin, ymin, xmax, ymax))
        feat["patch_id"] = int(patch_id)
        feat["quality"] = float(quality)
        features.append(feat)
    provider.addFeatures(features)
    layer.updateExtents()

    gpkg = workdir / "vector_input.gpkg"
    options = QgsVectorFileWriter.SaveVectorOptions()
    options.driverName = "GPKG"
    options.layerName = "patches"
    QgsVectorFileWriter.writeAsVectorFormatV3(
        layer,
        str(gpkg),
        QgsProject.instance().transformContext(),
        options,
    )
    persisted = QgsVectorLayer(f"{gpkg}|layername=patches", "Regression Vector Input", "ogr")
    if not persisted.isValid():
        raise RuntimeError(f"Could not load persisted vector input from {gpkg}")
    return persisted


def _create_raster_layer(workdir: Path):
    arr = np.zeros((30, 30), dtype=np.uint8)
    arr[2:8, 2:8] = 1
    arr[3:9, 12:18] = 1
    arr[12:18, 5:11] = 1
    arr[20:26, 20:26] = 1

    path = workdir / "raster_input.tif"
    driver = gdal.GetDriverByName("GTiff")
    ds = driver.Create(str(path), int(arr.shape[1]), int(arr.shape[0]), 1, gdal.GDT_Byte)
    ds.SetGeoTransform((0.0, 20.0, 0.0, 600.0, 0.0, -20.0))
    sr = osr.SpatialReference()
    sr.ImportFromEPSG(3857)
    ds.SetProjection(sr.ExportToWkt())
    band = ds.GetRasterBand(1)
    band.WriteArray(arr)
    band.SetNoDataValue(0)
    band.FlushCache()
    ds.FlushCache()
    ds = None

    from qgis.core import QgsRasterLayer

    layer = QgsRasterLayer(str(path), "Regression Raster Input")
    if not layer.isValid():
        raise RuntimeError(f"Could not load raster input from {path}")
    return layer


def _vector_params(output_name: str) -> dict:
    return {
        "min_corridor_width": 20.0,
        "min_patch_size": 0.05,
        "budget_area": 3.0,
        "max_search_distance": 250.0,
        "output_name": output_name,
        "unit_system": "metric",
        "obstacle_enabled": False,
        "obstacle_layer_ids": [],
        "grid_resolution": 20.0,
        "add_to_project": False,
        "species_dispersal_distance_analysis": 250.0,
        "species_dispersal_kernel": "exponential",
        "min_patch_area_for_species_analysis": 0.05,
        "patch_quality_weight_field": "quality",
        "patch_area_scaling": "sqrt",
    }


def _raster_params() -> dict:
    return {
        "patch_connectivity": 8,
        "patch_mode": "value",
        "patch_values": [1.0],
        "range_lower": None,
        "range_upper": None,
        "value_tolerance": 1e-6,
        "nodata_fallback": 0.0,
        "min_patch_size": 4,
        "allow_sub_min_corridor": True,
        "budget_pixels": 60,
        "max_search_distance": 10,
        "min_corridor_width": 1,
        "allow_bottlenecks": True,
        "obstacle_enabled": False,
        "obstacle_mode": "value",
        "obstacle_values": [],
        "obstacle_range_lower": None,
        "obstacle_range_upper": None,
        "raster_units": "pixels",
        "corridor_cell_assignment": "sum_total_network_area",
        "add_to_project": False,
        "species_dispersal_distance_analysis": 10.0,
        "species_dispersal_kernel": "exponential",
        "min_patch_area_for_species_analysis": 0.0,
        "patch_area_scaling": "sqrt",
    }


def _extract_stats(stats: dict) -> dict:
    keys = [
        "corridors_used",
        "budget_used_ha",
        "budget_used",
        "budget_total",
        "budget_total_display",
        "total_connected_area_ha",
        "total_connected_area_display",
        "largest_group_area_ha",
        "largest_group_area_display",
        "habitat_availability_before",
        "habitat_availability_after",
        "percent_increase",
        "mean_reachable_area_before",
        "mean_reachable_area",
        "largest_reachable_habitat_cluster",
        "largest_reachable_habitat_cluster_before",
        "mean_effective_resistance_pre",
        "mean_effective_resistance_post",
        "mean_effective_resistance_pre_exact",
        "mean_effective_resistance_post_exact",
        "landscape_fluidity_pre_exact",
        "landscape_fluidity_post_exact",
        "components_remaining",
        "avg_degree",
        "redundant_links",
    ]
    out = {}
    for key in keys:
        if key in stats:
            val = stats[key]
            if isinstance(val, (np.floating, np.integer)):
                val = val.item()
            out[key] = val
    return out


def run_suite(label: str) -> dict:
    _reset_dir(ARTIFACT_ROOT / label)
    workdir = ARTIFACT_ROOT / label
    vector_input = _create_vector_layer(workdir)
    raster_input = _create_raster_layer(workdir)

    vector_results = {}
    for strategy in [
        "largest_single_network",
        "most_connected_habitat",
        "landscape_fluidity",
        "reachable_habitat_advanced",
    ]:
        outdir = workdir / f"vector_{strategy}"
        outdir.mkdir(parents=True, exist_ok=True)
        res = analysis_vector.run_vector_analysis(
            vector_input,
            str(outdir),
            _vector_params(f"{strategy}.gpkg"),
            strategy=strategy,
            temporary=False,
            iface=False,
        )[0]
        vector_results[strategy] = _extract_stats(dict(res.get("stats") or {}))

    raster_results = {}
    for strategy in [
        "largest_single_network",
        "most_connected_habitat",
        "landscape_fluidity",
        "reachable_habitat_advanced",
    ]:
        outdir = workdir / f"raster_{strategy}"
        outdir.mkdir(parents=True, exist_ok=True)
        res = analysis_raster.run_raster_analysis(
            raster_input,
            str(outdir),
            _raster_params(),
            strategy=strategy,
            temporary=False,
            iface=False,
        )[0]
        raster_results[strategy] = _extract_stats(dict(res.get("stats") or {}))

    return {
        "label": label,
        "artifact_root": str(workdir),
        "vector": vector_results,
        "raster": raster_results,
    }


def main(label: str, output_json: Path) -> dict:
    result = run_suite(label)
    output_json.write_text(json.dumps(result, indent=2, sort_keys=True), encoding="utf-8")
    print(f"REGRESSION_JSON={output_json}")
    print(json.dumps(result, sort_keys=True))
    return result


if __name__ == "__main__":
    out = BASELINE_JSON
    label = "baseline"
    if len(sys.argv) > 1:
        label = str(sys.argv[1])
    if len(sys.argv) > 2:
        out = Path(sys.argv[2])
    main(label, out)
