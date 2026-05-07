"""
Shared rasterized landscape metrics used by both raster and vector TerraLink runs.
"""

from __future__ import annotations

import heapq
import math
import random
from collections import defaultdict
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

import numpy as np

if not hasattr(np, "int"):  # pragma: no cover
    np.int = int  # type: ignore[attr-defined]

try:
    from scipy import ndimage

    HAS_NDIMAGE = True
except Exception:  # pragma: no cover
    ndimage = None  # type: ignore
    HAS_NDIMAGE = False

try:
    from scipy import sparse as scipy_sparse
    from scipy.sparse.linalg import factorized as scipy_factorized

    HAS_SCIPY_SPARSE = True
except Exception:  # pragma: no cover
    scipy_sparse = None  # type: ignore
    scipy_factorized = None  # type: ignore
    HAS_SCIPY_SPARSE = False

try:
    import cv2

    HAS_CV2 = True
except ImportError:  # pragma: no cover
    cv2 = None  # type: ignore
    HAS_CV2 = False

try:
    from . import terralink_graph as nx
except ImportError:  # pragma: no cover
    nx = None  # type: ignore

class UnionFind:
    """Union-Find data structure for tracking connected components."""

    def __init__(self):
        self.parent: Dict[int, int] = {}
        self.size: Dict[int, int] = {}
        self.count: Dict[int, int] = {}

    def find(self, x: int) -> int:
        if x not in self.parent:
            self.parent[x] = x
            self.size[x] = 0
            self.count[x] = 0
        if self.parent[x] != x:
            self.parent[x] = self.find(self.parent[x])
        return self.parent[x]

    def union(self, a: int, b: int) -> int:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return ra
        sa, sb = self.size.get(ra, 0), self.size.get(rb, 0)
        if sa < sb:
            ra, rb = rb, ra
            sa, sb = sb, sa
        self.parent[rb] = ra
        self.size[ra] = sa + sb
        self.count[ra] = self.count.get(ra, 0) + self.count.get(rb, 0)
        return ra

    def get_size(self, x: int) -> int:
        return self.size.get(self.find(x), 0)

    def get_count(self, x: int) -> int:
        return self.count.get(self.find(x), 0)


def label_components_numpy(binary_array: np.ndarray, connectivity: int = 8) -> Tuple[np.ndarray, int]:
    """Label connected components using numpy (no external dependencies)."""
    rows, cols = binary_array.shape
    uf = UnionFind()
    if connectivity == 4:
        neighbors = [(-1, 0), (0, -1)]
    else:
        neighbors = [(-1, -1), (-1, 0), (-1, 1), (0, -1)]

    for i in range(rows):
        for j in range(cols):
            if binary_array[i, j]:
                cur = (i, j)
                uf.find(cur)
                for di, dj in neighbors:
                    ni, nj = i + di, j + dj
                    if 0 <= ni < rows and 0 <= nj < cols and binary_array[ni, nj]:
                        uf.union(cur, (ni, nj))

    root_to_label: Dict[Tuple[int, int], int] = {}
    next_label = 1
    labeled = np.zeros_like(binary_array, dtype=np.int32)
    for i in range(rows):
        for j in range(cols):
            if binary_array[i, j]:
                root = uf.find((i, j))
                if root not in root_to_label:
                    root_to_label[root] = next_label
                    next_label += 1
                labeled[i, j] = root_to_label[root]

    return labeled, next_label - 1


def label_components_opencv(binary_array: np.ndarray, connectivity: int = 8) -> Tuple[np.ndarray, int]:
    """Label connected components using OpenCV when available."""
    cv_conn = 4 if connectivity == 4 else 8
    n_labels, labeled = cv2.connectedComponents(binary_array.astype(np.uint8), connectivity=cv_conn)
    return labeled.astype(np.int32), n_labels - 1


def label_patches(binary_array: np.ndarray, connectivity: int = 8) -> Tuple[np.ndarray, int]:
    """Label connected components using the fastest available approach."""
    if HAS_CV2:
        print("  Using OpenCV for labeling...")
        return label_components_opencv(binary_array, connectivity)
    print("  Using numpy for labeling...")
    return label_components_numpy(binary_array, connectivity)


def _perform_landscape_analysis(
    arr: np.ndarray,
    layer_name: str,
    res_x: float,
    res_y: float,
    is_metric: bool,
    params: Optional[Any] = None,
    pre_arr: Optional[np.ndarray] = None,
) -> List[str]:
    """Calculate landscape metrics for the output raster (contiguous networks)."""
    use_ndimage = HAS_NDIMAGE and ndimage is not None
    results: List[str] = []

    if is_metric:
        pixel_area_ha = (res_x * res_y) / 10000.0
        dist_factor = 1000.0
    else:
        pixel_area_ha, dist_factor = 1.0, 1.0

    pixel_size = max(abs(float(res_x or 0.0)), abs(float(res_y or 0.0))) if is_metric else 1.0
    if pixel_size <= 0:
        pixel_size = 1.0

    def _clamp01(v: float) -> float:
        return max(0.0, min(1.0, float(v)))

    def _param_value(key: str, default: Any = None) -> Any:
        if params is None:
            return default
        if isinstance(params, dict):
            return params.get(key, default)
        return getattr(params, key, default)

    def _param_first(keys: Sequence[str], default: Any = None) -> Any:
        for key in keys:
            val = _param_value(key, None)
            if val is not None and str(val) != "":
                return val
        return default

    def _param_float(keys: Sequence[str], default: float) -> float:
        val = _param_first(keys, default)
        try:
            return float(val)
        except Exception:
            return float(default)

    def _param_int(keys: Sequence[str], default: int) -> int:
        val = _param_first(keys, default)
        try:
            return int(val)
        except Exception:
            return int(default)

    def _distance_to_analysis_units(value: float) -> float:
        units = str(_param_first(("raster_units", "unit_system"), "metric" if is_metric else "pixels")).strip().lower()
        val = float(value)
        if is_metric:
            if units == "imperial":
                return val * 0.3048
            if units == "pixels":
                return val * pixel_size
            return val
        if units in ("metric", "meters", "m"):
            return val
        if units in ("imperial", "feet", "ft"):
            return val * 0.3048
        return val

    def _estimate_pc_alpha_from_coords(coords_yx: np.ndarray, sample_cap: int = 256) -> float:
        if coords_yx is None or len(coords_yx) < 2:
            return 0.0
        n = int(len(coords_yx))
        if n <= int(sample_cap):
            sample_idx = np.arange(n, dtype=int)
        else:
            sample_idx = np.linspace(0, n - 1, num=int(sample_cap), dtype=int)

        nn_distances: List[float] = []
        for idx in sample_idx.tolist():
            dy = coords_yx[:, 0] - float(coords_yx[int(idx), 0])
            dx = coords_yx[:, 1] - float(coords_yx[int(idx), 1])
            dist = np.hypot(dx, dy)
            dist[int(idx)] = np.inf
            finite = dist[np.isfinite(dist) & (dist > 1e-9)]
            if finite.size <= 0:
                continue
            nn_distances.append(float(np.min(finite)))

        if not nn_distances:
            return 0.0
        vals = np.asarray(nn_distances, dtype=float)
        try:
            return float(max(np.quantile(vals, 0.75), 1e-6))
        except Exception:
            return float(max(np.median(vals), 1e-6))

    def _normalize_weights(raw: Sequence[float]) -> List[float]:
        vals = [max(0.0, float(v)) for v in raw]
        total = sum(vals)
        if total <= 0:
            return [0.2, 0.2, 0.2, 0.2, 0.2]
        return [v / total for v in vals]

    def _neighbor_count_4(mask: np.ndarray) -> np.ndarray:
        """4-neighbor count with zero padding (numpy fallback for scipy.convolve)."""
        m = mask.astype(np.uint8, copy=False)
        p = np.pad(m, ((1, 1), (1, 1)), mode="constant", constant_values=0)
        return (
            p[:-2, 1:-1].astype(np.int16)
            + p[2:, 1:-1].astype(np.int16)
            + p[1:-1, :-2].astype(np.int16)
            + p[1:-1, 2:].astype(np.int16)
        )

    def _binary_erosion_cross(mask: np.ndarray) -> np.ndarray:
        """Cross-structure erosion fallback to approximate scipy.ndimage.binary_erosion default."""
        m = mask.astype(bool, copy=False)
        p = np.pad(m, ((1, 1), (1, 1)), mode="constant", constant_values=False)
        return (
            p[1:-1, 1:-1]
            & p[:-2, 1:-1]
            & p[2:, 1:-1]
            & p[1:-1, :-2]
            & p[1:-1, 2:]
        )

    def _metrics_from_mask(mask: np.ndarray) -> Tuple[Dict[str, float], bool, np.ndarray, int]:
        hab_pixels = int(np.sum(mask))
        if hab_pixels <= 0:
            empty_labels = np.zeros_like(mask, dtype=int)
            return {
                "total_area": 0.0,
                "num_patches": 0.0,
                "mesh": 0.0,
                "lps": 0.0,
                "split": 0.0,
                "pd": 0.0,
                "lpi": 0.0,
                "total_edge": 0.0,
                "msi": 0.0,
                "ed": 0.0,
                "mean_para": 0.0,
                "frac": 0.0,
                "ai": 0.0,
                "cai": 0.0,
                "mean_gyrate": 0.0,
            }, True, empty_labels, 0

        if use_ndimage:
            s = ndimage.generate_binary_structure(2, 2)
            labeled_array, num_patches = ndimage.label(mask, structure=s)
        else:
            labeled_array, num_patches = label_patches(mask.astype(np.uint8), connectivity=8)

        patch_ids = np.arange(1, num_patches + 1)
        patch_pixel_counts = np.bincount(labeled_array.ravel())[1:] if num_patches > 0 else np.array([], dtype=float)

        if use_ndimage:
            kernel = np.array([[0, 1, 0], [1, 0, 1], [0, 1, 0]])
            neighbor_count = ndimage.convolve(mask.astype(float), kernel, mode="constant", cval=0)
        else:
            neighbor_count = _neighbor_count_4(mask)
        edge_map = (4.0 - neighbor_count) * mask

        patch_areas_ha = patch_pixel_counts * pixel_area_ha
        if num_patches > 0:
            if use_ndimage:
                patch_perim_px = ndimage.sum(edge_map, labeled_array, index=patch_ids)
            else:
                patch_perim_px = np.bincount(
                    labeled_array.ravel(),
                    weights=edge_map.ravel(),
                    minlength=num_patches + 1,
                )[1:]
            patch_perims_m = patch_perim_px * (res_x if is_metric else 1.0)
        else:
            patch_perims_m = np.array([], dtype=float)
        patch_areas_m2 = patch_pixel_counts * (res_x * res_y if is_metric else 1.0)
        total_area_ha = hab_pixels * pixel_area_ha
        total_edge_m = float(np.sum(edge_map)) * (res_x if is_metric else 1.0)

        pd = (num_patches / total_area_ha) * 100 if total_area_ha > 0 else 0.0
        mesh = float(np.sum(patch_areas_ha**2) / total_area_ha) if total_area_ha > 0 else 0.0
        split = float((total_area_ha**2) / np.sum(patch_areas_ha**2)) if np.sum(patch_areas_ha**2) > 0 else 0.0
        lps_ha = float(np.max(patch_areas_ha)) if num_patches > 0 else 0.0
        lpi = (lps_ha / total_area_ha) * 100 if total_area_ha > 0 else 0.0

        denom_ai = (2 * hab_pixels - 2 * int(np.sqrt(hab_pixels)) - 2)
        ai = ((hab_pixels * 4 - np.sum(edge_map)) / 2) / denom_ai * 100 if denom_ai > 0 else 0.0

        ed = total_edge_m / total_area_ha if total_area_ha > 0 else 0.0
        with np.errstate(divide="ignore", invalid="ignore"):
            msi = float(np.mean(0.25 * patch_perims_m / np.sqrt(patch_areas_m2))) if num_patches > 0 else 0.0
            mean_para = float(np.mean(patch_perims_m / patch_areas_m2)) if num_patches > 0 else 0.0
            frac_vals = (2 * np.log(0.25 * patch_perims_m)) / np.log(patch_areas_m2) if num_patches > 0 else np.array([], dtype=float)
            frac = float(np.nanmean(frac_vals)) if num_patches > 0 and frac_vals.size else 0.0

        if use_ndimage:
            core_mask = ndimage.binary_erosion(mask)
        else:
            core_mask = _binary_erosion_cross(mask)
        cai = (float(np.sum(core_mask)) / hab_pixels) * 100 if hab_pixels > 0 else 0.0

        gyrations = []
        for p_id in patch_ids:
            if num_patches > 1000 and p_id > 200:
                break
            coords = np.argwhere(labeled_array == p_id)
            if len(coords) < 2:
                continue
            gyrations.append(
                np.sqrt(np.mean(np.sum((coords - coords.mean(axis=0)) ** 2, axis=1))) * (res_x if is_metric else 1.0)
            )
        mean_gyrate = float(np.mean(gyrations)) if gyrations else 0.0

        return {
            "total_area": float(total_area_ha),
            "num_patches": float(num_patches),
            "mesh": float(mesh),
            "lps": float(lps_ha),
            "split": float(split),
            "pd": float(pd),
            "lpi": float(lpi),
            "total_edge": float(total_edge_m / dist_factor),
            "msi": float(msi),
            "ed": float(ed),
            "mean_para": float(mean_para),
            "frac": float(frac),
            "ai": float(ai),
            "cai": float(cai),
            "mean_gyrate": float(mean_gyrate),
        }, False, labeled_array, int(num_patches)

    def _spatial_hash_pairs_within_cutoff(
        patch_ids: np.ndarray,
        coords_yx: np.ndarray,
        cutoff: float,
    ) -> List[Tuple[int, int, float]]:
        n = int(len(patch_ids))
        if n <= 1:
            return []
        if cutoff <= 0.0 or (not np.isfinite(cutoff)):
            out: List[Tuple[int, int, float]] = []
            for i in range(n):
                yi, xi = float(coords_yx[i, 0]), float(coords_yx[i, 1])
                pi = int(patch_ids[i])
                for j in range(i + 1, n):
                    yj, xj = float(coords_yx[j, 0]), float(coords_yx[j, 1])
                    d = float(math.hypot(yi - yj, xi - xj))
                    out.append((pi, int(patch_ids[j]), d))
            return out

        cell_size = max(float(cutoff), 1e-9)
        buckets: Dict[Tuple[int, int], List[int]] = defaultdict(list)
        for idx in range(n):
            yv, xv = float(coords_yx[idx, 0]), float(coords_yx[idx, 1])
            key = (int(math.floor(xv / cell_size)), int(math.floor(yv / cell_size)))
            buckets[key].append(idx)

        out: List[Tuple[int, int, float]] = []
        for i in range(n):
            yi, xi = float(coords_yx[i, 0]), float(coords_yx[i, 1])
            pi = int(patch_ids[i])
            key = (int(math.floor(xi / cell_size)), int(math.floor(yi / cell_size)))
            for dx in (-1, 0, 1):
                for dy in (-1, 0, 1):
                    cand = buckets.get((key[0] + dx, key[1] + dy), [])
                    for j in cand:
                        if j <= i:
                            continue
                        yj, xj = float(coords_yx[j, 0]), float(coords_yx[j, 1])
                        d = float(math.hypot(yi - yj, xi - xj))
                        if d <= cutoff:
                            out.append((pi, int(patch_ids[j]), d))
        return out

    def _added_component_patch_touches(
        added_labels: np.ndarray,
        pre_labels_arr: np.ndarray,
        n_added: int,
    ) -> Dict[int, Set[int]]:
        touches: Dict[int, Set[int]] = {int(cid): set() for cid in range(1, int(n_added) + 1)}
        if n_added <= 0:
            return touches
        rows, cols = added_labels.shape
        offsets = (
            (-1, -1), (-1, 0), (-1, 1),
            (0, -1),            (0, 1),
            (1, -1),  (1, 0),   (1, 1),
        )
        for dr, dc in offsets:
            r0 = max(0, -dr)
            r1 = min(rows, rows - dr)
            c0 = max(0, -dc)
            c1 = min(cols, cols - dc)
            if r0 >= r1 or c0 >= c1:
                continue
            src = added_labels[r0:r1, c0:c1]
            dst = pre_labels_arr[r0 + dr:r1 + dr, c0 + dc:c1 + dc]
            mask = (src > 0) & (dst > 0)
            if not np.any(mask):
                continue
            src_vals = src[mask].astype(np.int64, copy=False)
            dst_vals = dst[mask].astype(np.int64, copy=False)
            encoded = (src_vals << 32) | dst_vals
            for code in np.unique(encoded):
                cid = int((int(code) >> 32) & 0xFFFFFFFF)
                pid = int(int(code) & 0xFFFFFFFF)
                if cid > 0 and pid > 0:
                    touches.setdefault(cid, set()).add(pid)
        return touches

    def _all_pairs_shortest_lengths(graph: Optional["nx.MultiGraph"]) -> Dict[int, Dict[int, float]]:
        if graph is None or nx is None:
            return {}
        if graph.number_of_nodes() <= 0 or graph.number_of_edges() <= 0:
            return {}
        try:
            return {
                int(src): {int(dst): float(val) for dst, val in dist.items()}
                for src, dist in nx.all_pairs_dijkstra_path_length(graph, weight="weight")
            }
        except Exception:
            return {}

    def _compute_pc_norm(
        candidate_pairs: Sequence[Tuple[int, int, float]],
        areas_by_pid: Dict[int, float],
        total_area: float,
        alpha_val: float,
        graph_shortest: Optional[Dict[int, Dict[int, float]]] = None,
    ) -> float:
        if total_area <= 0.0:
            return 0.0
        alpha_safe = max(float(alpha_val), 1e-9)
        self_term = 0.0
        for area in areas_by_pid.values():
            a = max(float(area), 0.0)
            self_term += a * a
        pair_term = 0.0
        for p1, p2, eu_d in candidate_pairs:
            a1 = max(float(areas_by_pid.get(int(p1), 0.0)), 0.0)
            a2 = max(float(areas_by_pid.get(int(p2), 0.0)), 0.0)
            if a1 <= 0.0 or a2 <= 0.0:
                continue
            d = float(eu_d)
            if graph_shortest:
                g_d = graph_shortest.get(int(p1), {}).get(int(p2), float("inf"))
                if g_d < d:
                    d = float(g_d)
            if not np.isfinite(d):
                continue
            pij = float(math.exp(-max(d, 0.0) / alpha_safe))
            pair_term += a1 * a2 * pij
        pc = (self_term + (2.0 * pair_term)) / max(total_area * total_area, 1e-12)
        return _clamp01(pc)

    def _downsample_or(mask: np.ndarray, factor: int) -> np.ndarray:
        f = max(1, int(factor))
        if f == 1:
            return mask.astype(bool, copy=True)
        rows, cols = mask.shape
        out_rows = (rows + f - 1) // f
        out_cols = (cols + f - 1) // f
        out = np.zeros((out_rows, out_cols), dtype=bool)
        src = mask.astype(bool, copy=False)
        for rr in range(f):
            for cc in range(f):
                sub = src[rr::f, cc::f]
                if sub.size == 0:
                    continue
                out[: sub.shape[0], : sub.shape[1]] |= sub
        return out

    def _sample_terminals_stratified(mask: np.ndarray, k: int, seed: int = 13) -> List[Tuple[int, int]]:
        points: List[Tuple[int, int]] = []
        total_cells = int(np.sum(mask))
        if total_cells <= 0:
            return points
        target_k = max(2, min(int(k), int(total_cells)))
        labels, n_comp = label_patches(mask.astype(np.uint8), connectivity=8)
        if n_comp <= 0:
            return points
        counts = np.bincount(labels.ravel())[1:].astype(np.int64)
        if counts.size == 0:
            return points
        total = int(np.sum(counts))
        if total <= 0:
            return points

        alloc = np.floor((counts / float(total)) * float(target_k)).astype(np.int64)
        alloc = np.maximum(alloc, 1)
        while int(np.sum(alloc)) > target_k:
            idx = int(np.argmax(alloc))
            if alloc[idx] <= 1:
                break
            alloc[idx] -= 1
        while int(np.sum(alloc)) < target_k:
            idx = int(np.argmax(counts))
            alloc[idx] += 1

        rng = random.Random(int(seed))
        for cid, need in enumerate(alloc, start=1):
            need_i = int(max(0, need))
            if need_i <= 0:
                continue
            coords = np.argwhere(labels == int(cid))
            if coords.size == 0:
                continue
            if need_i >= len(coords):
                chosen = coords
            else:
                idxs = list(range(len(coords)))
                rng.shuffle(idxs)
                chosen = coords[idxs[:need_i]]
            for rc in chosen:
                points.append((int(rc[0]), int(rc[1])))
        if len(points) > target_k:
            rng.shuffle(points)
            points = points[:target_k]
        return points

    def _sample_pairs(n_points: int, pair_target: int, seed: int = 17) -> List[Tuple[int, int]]:
        if n_points < 2:
            return []
        total_pairs = (n_points * (n_points - 1)) // 2
        p_target = max(1, min(int(pair_target), int(total_pairs)))
        if p_target >= total_pairs:
            return [(i, j) for i in range(n_points) for j in range(i + 1, n_points)]
        rng = random.Random(int(seed))
        picked: Set[Tuple[int, int]] = set()
        while len(picked) < p_target:
            i = rng.randrange(0, n_points - 1)
            j = rng.randrange(i + 1, n_points)
            picked.add((i, j))
        return sorted(picked)

    def _dijkstra_to_targets(
        passable: np.ndarray,
        src: Tuple[int, int],
        targets: Set[Tuple[int, int]],
        step: float,
    ) -> Dict[Tuple[int, int], float]:
        rows, cols = passable.shape
        sr, sc = int(src[0]), int(src[1])
        if sr < 0 or sr >= rows or sc < 0 or sc >= cols:
            return {}
        if not passable[sr, sc]:
            return {}
        if not targets:
            return {}
        cost_orth = float(step)
        cost_diag = float(step * math.sqrt(2.0))
        moves = (
            (-1, 0, cost_orth), (1, 0, cost_orth),
            (0, -1, cost_orth), (0, 1, cost_orth),
            (-1, -1, cost_diag), (-1, 1, cost_diag),
            (1, -1, cost_diag), (1, 1, cost_diag),
        )

        target_set = set((int(r), int(c)) for r, c in targets)
        found: Dict[Tuple[int, int], float] = {}
        best: Dict[Tuple[int, int], float] = {(sr, sc): 0.0}
        heap: List[Tuple[float, Tuple[int, int]]] = [(0.0, (sr, sc))]

        while heap and target_set:
            dist_cur, (r, c) = heapq.heappop(heap)
            prev = best.get((r, c), float("inf"))
            if dist_cur > prev + 1e-12:
                continue
            if (r, c) in target_set:
                found[(r, c)] = float(dist_cur)
                target_set.discard((r, c))
                if not target_set:
                    break
            for dr, dc, move_cost in moves:
                nr, nc = r + dr, c + dc
                if nr < 0 or nr >= rows or nc < 0 or nc >= cols:
                    continue
                if not passable[nr, nc]:
                    continue
                nd = float(dist_cur + move_cost)
                old = best.get((nr, nc), float("inf"))
                if nd + 1e-12 < old:
                    best[(nr, nc)] = nd
                    heapq.heappush(heap, (nd, (nr, nc)))
        return found

    def _pair_shortest_distances(
        passable: np.ndarray,
        points: Sequence[Tuple[int, int]],
        pairs: Sequence[Tuple[int, int]],
        step: float,
    ) -> Dict[Tuple[int, int], float]:
        dists: Dict[Tuple[int, int], float] = {
            (int(i), int(j)): float("inf")
            for i, j in pairs
        }
        if not pairs:
            return dists
        groups: Dict[int, Set[int]] = defaultdict(set)
        for i, j in pairs:
            groups[int(i)].add(int(j))
            groups[int(j)].add(int(i))
        for src_idx, target_idxs in groups.items():
            src_pt = points[int(src_idx)]
            target_coords = {points[int(ti)] for ti in target_idxs}
            found = _dijkstra_to_targets(passable, src_pt, target_coords, step=step)
            for ti in target_idxs:
                key = (int(src_idx), int(ti)) if src_idx < ti else (int(ti), int(src_idx))
                target_coord = points[int(ti)]
                if target_coord in found:
                    dists[key] = min(float(dists.get(key, float("inf"))), float(found[target_coord]))
        return dists

    def _ime_norm(
        pair_dists: Dict[Tuple[int, int], float],
        pair_euclid: Dict[Tuple[int, int], float],
    ) -> float:
        if not pair_euclid:
            return 0.0
        eps = 1e-9
        num = 0.0
        den = 0.0
        n = 0
        for key, eu in pair_euclid.items():
            eu_d = max(float(eu), 0.0)
            d = float(pair_dists.get(key, float("inf")))
            num += (1.0 / (d + eps)) if np.isfinite(d) else 0.0
            den += 1.0 / (eu_d + eps)
            n += 1
        if n <= 0 or den <= 0.0:
            return 0.0
        return _clamp01(num / den)

    def _mean_path_resistance(
        pair_dists: Dict[Tuple[int, int], float],
        pair_euclid: Dict[Tuple[int, int], float],
    ) -> float:
        if not pair_euclid:
            return 0.0
        max_eu = max((float(v) for v in pair_euclid.values()), default=1.0)
        penalty = max(1.0, max_eu * 20.0)
        vals: List[float] = []
        for key in pair_euclid.keys():
            d = float(pair_dists.get(key, float("inf")))
            if np.isfinite(d):
                vals.append(max(float(d), 0.0))
            else:
                vals.append(float(penalty))
        if not vals:
            return 0.0
        return float(sum(vals) / max(len(vals), 1))

    def _strategic_mobility_score(
        pair_dists: Dict[Tuple[int, int], float],
        pair_euclid: Dict[Tuple[int, int], float],
        detour_cap: float,
    ) -> float:
        if not pair_euclid:
            return 0.0
        cap = max(float(detour_cap), 1.0)
        ratios: List[float] = []
        for key, eu in pair_euclid.items():
            eu_d = max(float(eu), 1e-9)
            d = float(pair_dists.get(key, float("inf")))
            if np.isfinite(d):
                ratio = max(1.0, float(d) / eu_d)
            else:
                ratio = cap
            ratios.append(min(cap, ratio))
        if not ratios:
            return 0.0
        mean_ratio = float(sum(ratios) / max(len(ratios), 1))
        if mean_ratio <= 0.0:
            return 0.0
        return _clamp01(1.0 / mean_ratio)

    def _fri_norm(
        pair_dists: Dict[Tuple[int, int], float],
        pair_euclid: Dict[Tuple[int, int], float],
        n_points: int,
    ) -> float:
        if (not HAS_SCIPY_SPARSE) or scipy_sparse is None or scipy_factorized is None:
            return 0.0
        if n_points < 2 or not pair_dists or not pair_euclid:
            return 0.0

        parent: Dict[int, int] = {}

        def _find(x: int) -> int:
            if x not in parent:
                parent[x] = x
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def _union(a: int, b: int) -> None:
            ra, rb = _find(a), _find(b)
            if ra != rb:
                parent[rb] = ra

        edge_pairs: List[Tuple[int, int, float]] = []
        for (i, j), d in pair_dists.items():
            dij = float(d)
            if (not np.isfinite(dij)) or dij <= 0.0:
                continue
            edge_pairs.append((int(i), int(j), dij))
            _union(int(i), int(j))

        if not edge_pairs:
            return 0.0

        comp_nodes: Dict[int, List[int]] = defaultdict(list)
        for node in range(int(n_points)):
            comp_nodes[_find(int(node))].append(int(node))

        pair_by_comp: Dict[int, List[Tuple[int, int]]] = defaultdict(list)
        for (i, j) in pair_euclid.keys():
            if _find(int(i)) == _find(int(j)):
                pair_by_comp[_find(int(i))].append((int(i), int(j)))

        resist_vals: List[float] = []
        eu_vals: List[float] = []
        for root, nodes in comp_nodes.items():
            if len(nodes) < 2:
                continue
            local_index = {node: idx for idx, node in enumerate(nodes)}
            n_local = len(nodes)
            degree = np.zeros(n_local, dtype=float)
            rows_l: List[int] = []
            cols_l: List[int] = []
            data_l: List[float] = []
            for i, j, d in edge_pairs:
                if i not in local_index or j not in local_index:
                    continue
                li = local_index[i]
                lj = local_index[j]
                c = 1.0 / max(float(d), 1e-9)
                degree[li] += c
                degree[lj] += c
                rows_l.extend([li, lj])
                cols_l.extend([lj, li])
                data_l.extend([-c, -c])
            for idx, deg in enumerate(degree):
                rows_l.append(idx)
                cols_l.append(idx)
                data_l.append(float(deg))

            if n_local <= 1:
                continue
            lap = scipy_sparse.csr_matrix((data_l, (rows_l, cols_l)), shape=(n_local, n_local))
            ref = n_local - 1
            lap_r = lap[:ref, :ref]
            try:
                solve = scipy_factorized(lap_r.tocsc())
            except Exception:
                continue

            for i, j in pair_by_comp.get(root, []):
                li = local_index.get(int(i))
                lj = local_index.get(int(j))
                if li is None or lj is None:
                    continue
                if li == lj:
                    continue
                b = np.zeros(ref, dtype=float)
                if li != ref:
                    b[li] += 1.0
                if lj != ref:
                    b[lj] -= 1.0
                try:
                    x = solve(b)
                except Exception:
                    continue
                vi = 0.0 if li == ref else float(x[li])
                vj = 0.0 if lj == ref else float(x[lj])
                r_eff = abs(vi - vj)
                if np.isfinite(r_eff):
                    resist_vals.append(float(r_eff))
                    eu_vals.append(float(pair_euclid.get((i, j), 0.0)))

        if not resist_vals or not eu_vals:
            return 0.0
        r_bar = float(np.mean(resist_vals))
        eu_bar = float(np.mean(eu_vals))
        if eu_bar <= 0.0:
            return 0.0
        r_scaled = r_bar / max(eu_bar, 1e-9)
        return _clamp01(1.0 / (1.0 + r_scaled))

    pre_mask = (pre_arr if pre_arr is not None else arr) > 0
    post_mask = arr > 0

    pre_metrics, pre_empty, pre_labels, _ = _metrics_from_mask(pre_mask)
    post_metrics, post_empty, post_labels, post_count = _metrics_from_mask(post_mask)

    header = "=" * 100
    results.append(header)
    results.append(f" LANDSCAPE ANALYSIS: {layer_name}")
    results.append(header)
    if pre_empty:
        results.append("Note: pre-corridor habitat mask contains no habitat pixels.")
    if post_empty:
        results.append("Note: post-corridor habitat mask contains no habitat pixels.")

    # ------------------------------------------------------------------
    # Reduced connectivity metrics: Total Area, habitat-normalized mesh, LCC, PC, resistance, flow.
    # ------------------------------------------------------------------
    pre_counts = np.bincount(pre_labels.ravel())[1:] if np.any(pre_labels) else np.array([], dtype=float)
    post_counts = np.bincount(post_labels.ravel())[1:] if np.any(post_labels) else np.array([], dtype=float)
    total_habitat_pixels = float(np.sum(pre_mask))
    total_habitat_area = total_habitat_pixels * pixel_area_ha
    mesh_h_pre = float(pre_metrics.get("mesh", 0.0) or 0.0)
    mesh_h_post = float(post_metrics.get("mesh", 0.0) or 0.0)
    pre_hab_area = float(pre_metrics.get("total_area", 0.0) or 0.0)
    post_hab_area = float(post_metrics.get("total_area", 0.0) or 0.0)
    mesh_h_pre_norm = _clamp01(mesh_h_pre / pre_hab_area) if pre_hab_area > 0.0 else 0.0
    mesh_h_post_norm = _clamp01(mesh_h_post / post_hab_area) if post_hab_area > 0.0 else 0.0
    mesh_override_pre = _param_float(("mesh_override_pre_norm",), -1.0)
    mesh_override_post = _param_float(("mesh_override_post_norm",), -1.0)
    if mesh_override_pre >= 0.0:
        mesh_h_pre_norm = _clamp01(mesh_override_pre)
    if mesh_override_post >= 0.0:
        mesh_h_post_norm = _clamp01(mesh_override_post)

    lcc_pre_area = (float(np.max(pre_counts)) * pixel_area_ha) if pre_counts.size else 0.0
    lcc_post_area = (float(np.max(post_counts)) * pixel_area_ha) if post_counts.size else 0.0
    if total_habitat_area > 0:
        lcc_pre_norm = _clamp01(lcc_pre_area / total_habitat_area)
        lcc_post_norm = _clamp01(lcc_post_area / total_habitat_area)
    else:
        lcc_pre_norm = 0.0
        lcc_post_norm = 0.0
    lcc_override_pre = _param_float(("lcc_override_pre_norm",), -1.0)
    lcc_override_post = _param_float(("lcc_override_post_norm",), -1.0)
    if lcc_override_pre >= 0.0:
        lcc_pre_norm = _clamp01(lcc_override_pre)
    if lcc_override_post >= 0.0:
        lcc_post_norm = _clamp01(lcc_override_post)
    _ = (mesh_h_pre_norm, mesh_h_post_norm, lcc_pre_norm, lcc_post_norm)

    n_patches = int(pre_counts.size)
    patch_ids = np.arange(1, n_patches + 1, dtype=int)
    areas_by_pid: Dict[int, float] = {
        int(pid): float(pre_counts[int(pid) - 1] * pixel_area_ha)
        for pid in patch_ids.tolist()
    }
    total_patch_area = float(sum(areas_by_pid.values()))

    alpha = _param_float(("pc_alpha_analysis",), 0.0)
    alpha_raw = _param_float(
        ("pc_alpha", "pc_alpha_distance", "landscape_pc_alpha", "connectivity_pc_alpha"),
        0.0,
    )
    max_search_raw = _param_float(("max_search_distance",), 0.0)
    if alpha <= 0.0:
        alpha = _distance_to_analysis_units(alpha_raw) if alpha_raw > 0 else 0.0
    centroids_yx = np.zeros((n_patches, 2), dtype=float)
    if n_patches > 0:
        ys, xs = np.nonzero(pre_labels > 0)
        if ys.size > 0:
            pid_vals = pre_labels[ys, xs].astype(np.int32, copy=False)
            counts = np.bincount(pid_vals, minlength=n_patches + 1).astype(np.float64)[1:]
            sum_y = np.bincount(pid_vals, weights=ys.astype(np.float64), minlength=n_patches + 1)[1:]
            sum_x = np.bincount(pid_vals, weights=xs.astype(np.float64), minlength=n_patches + 1)[1:]
            with np.errstate(divide="ignore", invalid="ignore"):
                centroids_yx[:, 0] = np.where(counts > 0, sum_y / counts, 0.0) * pixel_size
                centroids_yx[:, 1] = np.where(counts > 0, sum_x / counts, 0.0) * pixel_size

    if alpha <= 0.0:
        alpha = _estimate_pc_alpha_from_coords(centroids_yx)
    if alpha <= 0.0:
        auto = max_search_raw if max_search_raw > 0 else (1000.0 if is_metric else 100.0)
        alpha = _distance_to_analysis_units(float(auto))
    alpha = max(alpha, 1e-6)

    cutoff = _param_float(("pc_cutoff_analysis",), 0.0)
    cutoff_raw = _param_float(
        ("pc_cutoff", "pc_cutoff_distance", "landscape_pc_cutoff", "connectivity_pc_cutoff"),
        0.0,
    )
    if cutoff <= 0.0:
        cutoff = _distance_to_analysis_units(cutoff_raw) if cutoff_raw > 0 else 0.0
    if cutoff <= 0.0:
        cutoff = 3.0 * alpha
    cutoff = max(cutoff, alpha)

    pc_pairs = _spatial_hash_pairs_within_cutoff(
        patch_ids=patch_ids,
        coords_yx=centroids_yx,
        cutoff=float(cutoff),
    )

    added_mask = post_mask & (~pre_mask)
    if np.any(added_mask):
        if use_ndimage:
            struct = ndimage.generate_binary_structure(2, 2)
            added_labels, n_added = ndimage.label(added_mask.astype(np.uint8), structure=struct)
        else:
            added_labels, n_added = label_patches(added_mask.astype(np.uint8), connectivity=8)
    else:
        added_labels = np.zeros_like(post_mask, dtype=np.int32)
        n_added = 0

    touches = _added_component_patch_touches(added_labels, pre_labels, int(n_added))
    added_sizes = np.bincount(added_labels.ravel())[1:] if int(n_added) > 0 else np.array([], dtype=np.int64)
    corridor_records: List[Dict[str, Any]] = []
    for cid in range(1, int(n_added) + 1):
        area_px = int(added_sizes[cid - 1]) if cid - 1 < len(added_sizes) else 0
        if area_px <= 0:
            continue
        touched = sorted(int(v) for v in touches.get(int(cid), set()) if int(v) > 0)
        est_length = max(math.sqrt(float(area_px)) * pixel_size, pixel_size)
        area_cost = float(area_px * pixel_area_ha)
        benefit = 0.0
        if len(touched) >= 2:
            for i in range(len(touched)):
                for j in range(i + 1, len(touched)):
                    a1 = float(areas_by_pid.get(int(touched[i]), 0.0))
                    a2 = float(areas_by_pid.get(int(touched[j]), 0.0))
                    benefit = max(benefit, a1 * a2)
        elif len(touched) == 1:
            benefit = float(areas_by_pid.get(int(touched[0]), 0.0))
        score = benefit / max(area_cost, 1e-9)
        corridor_records.append(
            {
                "id": int(cid),
                "patch_ids": touched,
                "area_cost": float(area_cost),
                "length": float(est_length),
                "score": float(score),
            }
        )

    post_graph: Optional["nx.MultiGraph"] = None
    if nx is not None:
        try:
            post_graph = nx.MultiGraph()
            post_graph.add_nodes_from([int(pid) for pid in patch_ids.tolist()])
            for rec in corridor_records:
                touched = list(rec.get("patch_ids", []))
                if len(touched) < 2:
                    continue
                w = max(float(rec.get("length", pixel_size) or pixel_size), 1e-9)
                cid = int(rec.get("id", 0) or 0)
                for i in range(len(touched)):
                    for j in range(i + 1, len(touched)):
                        post_graph.add_edge(
                            int(touched[i]),
                            int(touched[j]),
                            weight=w,
                            corridor_id=cid,
                        )
        except Exception:
            post_graph = None

    post_shortest = _all_pairs_shortest_lengths(post_graph)
    pc_pre = _compute_pc_norm(pc_pairs, areas_by_pid, total_patch_area, alpha, graph_shortest=None)
    pc_post = _compute_pc_norm(pc_pairs, areas_by_pid, total_patch_area, alpha, graph_shortest=post_shortest)
    pc_override_pre = _param_float(("probability_connectivity_override_pre", "pc_override_pre"), -1.0)
    pc_override_post = _param_float(("probability_connectivity_override_post", "pc_override_post"), -1.0)
    if pc_override_pre >= 0.0:
        pc_pre = float(pc_override_pre)
    if pc_override_post >= 0.0:
        pc_post = float(pc_override_post)
    sample_points = max(2, min(200, _param_int(("sample_points", "redundancy_sample_points"), 50)))
    pair_samples = max(1, _param_int(("pair_samples", "redundancy_pair_samples"), 200))

    max_dim = max(int(pre_mask.shape[0]), int(pre_mask.shape[1]))
    ds_factor = max(1, int(math.ceil(float(max_dim) / 320.0)))
    pre_ds = _downsample_or(pre_mask.astype(bool), ds_factor)
    post_ds = _downsample_or(post_mask.astype(bool), ds_factor)
    step_size = float(pixel_size * ds_factor)
    term_points = _sample_terminals_stratified(pre_ds, sample_points, seed=31)
    sampled_pairs = _sample_pairs(len(term_points), pair_samples, seed=37)

    pair_euclid: Dict[Tuple[int, int], float] = {}
    for i, j in sampled_pairs:
        r1, c1 = term_points[int(i)]
        r2, c2 = term_points[int(j)]
        pair_euclid[(int(i), int(j))] = float(math.hypot((r1 - r2) * step_size, (c1 - c2) * step_size))

    pre_pair_d = _pair_shortest_distances(pre_ds, term_points, sampled_pairs, step=step_size)
    post_pair_d = _pair_shortest_distances(post_ds, term_points, sampled_pairs, step=step_size)
    mean_res_pre = _mean_path_resistance(pre_pair_d, pair_euclid)
    mean_res_post = _mean_path_resistance(post_pair_d, pair_euclid)
    mean_res_override_pre = _param_float(("mean_effective_resistance_override_pre",), -1.0)
    mean_res_override_post = _param_float(("mean_effective_resistance_override_post",), -1.0)
    if mean_res_override_pre >= 0.0:
        mean_res_pre = float(mean_res_override_pre)
    if mean_res_override_post >= 0.0:
        mean_res_post = float(mean_res_override_post)
    fluidity_pre = _param_float(("landscape_fluidity_override_pre",), -1.0)
    fluidity_post = _param_float(("landscape_fluidity_override_post",), -1.0)
    if fluidity_pre < 0.0 or fluidity_post < 0.0:
        fluidity_pre = 1.0 / max(float(mean_res_pre), 1e-9)
        fluidity_post = 1.0 / max(float(mean_res_post), 1e-9)
    ime_pre = _ime_norm(pre_pair_d, pair_euclid)
    ime_post = _ime_norm(post_pair_d, pair_euclid)
    fri_pre = _fri_norm(pre_pair_d, pair_euclid, n_points=len(term_points))
    fri_post = _fri_norm(post_pair_d, pair_euclid, n_points=len(term_points))
    fri_available = HAS_SCIPY_SPARSE and scipy_sparse is not None and scipy_factorized is not None
    requested_flow_method = str(_param_first(("redundancy_method",), "ime")).strip().lower()
    if requested_flow_method == "fri" and fri_available:
        _flow_pre = float(fri_pre)
        _flow_post = float(fri_post)
        _flow_method_label = "FRI"
    else:
        _flow_pre = float(ime_pre)
        _flow_post = float(ime_post)
        _flow_method_label = "IME" if requested_flow_method != "fri" else "IME (FRI unavailable)"
    _ = (_flow_pre, _flow_post, _flow_method_label)

    def _fmt_value(val: float, decimals: int = 6) -> str:
        v = float(val)
        if not np.isfinite(v):
            return ""
        if abs(v) >= 1000:
            return f"{v:,.2f}"
        return f"{v:.{int(max(0, decimals))}f}"

    def _add_metric_row(
        *,
        metric_name: str,
        pre_val: float,
        post_val: float,
        description: str,
        source: str,
        higher_is_better: bool,
        bounded_unit_interval: bool = False,
        show_percent_change: bool = True,
        decimals: int = 6,
    ) -> None:
        pre_v = float(pre_val)
        post_v = float(post_val)
        delta = float(post_v - pre_v)
        pre_abs = abs(pre_v)
        delta_pct = float((delta / pre_abs) * 100.0) if pre_abs > 1e-12 else 0.0

        pre_s = _fmt_value(pre_v, decimals=decimals)
        post_s = _fmt_value(post_v, decimals=decimals)
        if show_percent_change:
            delta_pct_s = f"{delta_pct:+.3f}%"
        else:
            delta_pct_s = "n/a"

        results.append(
            f"{metric_name:<44} | {pre_s:<15} | {post_s:<15} | {delta_pct_s:<11} | "
            f"{description:<72} | {source:<26}"
        )

    col_header = (
        f"{'METRIC NAME':<44} | {'PRE':<15} | {'POST':<15} | {'DELTA %':<11} | "
        f"{'DESCRIPTION':<72} | {'SOURCE':<26}"
    )
    results.append(col_header)
    results.append("-" * len(col_header))

    # --------------------------------------------------------------
    # Keep only the requested metrics in the report output.
    # --------------------------------------------------------------
    # Patch-graph connectivity stats based on corridor-added components.
    def _component_stats_from_corridors() -> Tuple[float, float, float]:
        parent: Dict[int, int] = {int(pid): int(pid) for pid in patch_ids.tolist()}
        comp_area: Dict[int, float] = {}
        comp_count: Dict[int, int] = {}

        def _find(x: int) -> int:
            root = int(x)
            while parent.get(root, root) != root:
                root = parent[root]
            while parent.get(x, x) != x:
                nxt = parent[x]
                parent[x] = root
                x = nxt
            return root

        def _union(a: int, b: int) -> None:
            ra = _find(int(a))
            rb = _find(int(b))
            if ra != rb:
                parent[rb] = ra

        for rec in corridor_records:
            touched = [int(v) for v in (rec.get("patch_ids", []) or []) if int(v) > 0]
            if len(touched) < 2:
                continue
            base = int(touched[0])
            for other in touched[1:]:
                _union(base, int(other))

        for pid in patch_ids.tolist():
            r = _find(int(pid))
            comp_count[r] = int(comp_count.get(r, 0) + 1)
            comp_area[r] = float(comp_area.get(r, 0.0) + float(areas_by_pid.get(int(pid), 0.0) or 0.0))

        largest_area = float(max(comp_area.values(), default=0.0))
        total_connected_multi = float(
            sum(float(a) for r, a in comp_area.items() if int(comp_count.get(r, 0)) >= 2)
        )
        return total_connected_multi, largest_area, float(max(areas_by_pid.values(), default=0.0))

    connected_area_post, largest_network_post, largest_patch_pre = _component_stats_from_corridors()
    connected_area_pre = 0.0
    largest_network_pre = float(largest_patch_pre)
    connected_area_override_pre = _param_float(("total_connected_area_override_pre",), -1.0)
    connected_area_override_post = _param_float(("total_connected_area_override_post",), -1.0)
    largest_network_override_pre = _param_float(("largest_network_area_override_pre",), -1.0)
    largest_network_override_post = _param_float(("largest_network_area_override_post",), -1.0)
    if connected_area_override_pre >= 0.0:
        connected_area_pre = float(connected_area_override_pre)
    if connected_area_override_post >= 0.0:
        connected_area_post = float(connected_area_override_post)
    if largest_network_override_pre >= 0.0:
        largest_network_pre = float(largest_network_override_pre)
    if largest_network_override_post >= 0.0:
        largest_network_post = float(largest_network_override_post)

    _add_metric_row(
        metric_name="Total Connected Habitat Area",
        pre_val=float(connected_area_pre),
        post_val=float(connected_area_post),
        description="Habitat area connected into multi-patch networks",
        source="",
        higher_is_better=True,
        bounded_unit_interval=False,
        show_percent_change=False,
        decimals=2,
    )
    _add_metric_row(
        metric_name="Largest Network Area",
        pre_val=float(largest_network_pre),
        post_val=float(largest_network_post),
        description="Habitat area in the largest connected network",
        source="",
        higher_is_better=True,
        bounded_unit_interval=False,
        decimals=2,
    )
    _add_metric_row(
        metric_name="Probability of Connectivity",
        pre_val=float(pc_pre),
        post_val=float(pc_post),
        description="Functionally connected habitat area from patch area and distance-decayed connectivity",
        source="Saura & Pascual-Hortal 2007",
        higher_is_better=True,
        bounded_unit_interval=True,
        decimals=6,
    )
    _add_metric_row(
        metric_name="Mean Effective Resistance",
        pre_val=float(mean_res_pre),
        post_val=float(mean_res_post),
        description="Average difficulty of movement across network",
        source="Wagner & Fortin 2005",
        higher_is_better=False,
        bounded_unit_interval=False,
        decimals=4,
    )
    results.append(header)
    return results
