"""
TerraLink Sub-Patch Decomposition for Raster Landscape Fluidity
---------------------------------------------------------------
Detects internal bottlenecks within patches and decomposes them into
virtual sub-nodes so the effective-resistance framework can naturally
value intra-patch corridor candidates.

This module is designed to be imported into analysis_raster.py and
called before the LF optimizer builds its graph.

Usage:
    from .subpatch_decompose import decompose_patches_for_lf, generate_ipc_candidates

    sub_sizes, sub_to_parent, bn_edges = decompose_patches_for_lf(labels, patch_sizes)
    ipc_cands = generate_ipc_candidates(bn_edges, labels, min_corridor_width, obstacle_mask)
    # Merge ipc_cands into all_candidates, build graph with sub_sizes
"""

from __future__ import annotations

import math
from typing import Any, Dict, List, Optional, Set, Tuple

import numpy as np

try:
    from scipy.ndimage import (
        binary_dilation,
        distance_transform_edt,
        generate_binary_structure,
        label as ndlabel,
    )
    HAS_SCIPY = True
except ImportError:
    HAS_SCIPY = False


# ---------------------------------------------------------------------------
# Bottleneck Detection
# ---------------------------------------------------------------------------

def detect_patch_bottlenecks(
    labels: np.ndarray,
    pid: int,
    *,
    min_width_threshold: float = 2.5,
    min_patch_area: int = 40,
    min_sub_fraction: float = 0.05,
    max_bottlenecks: int = 3,
) -> List[Dict[str, Any]]:
    """
    Detect narrow internal passages (bottlenecks) within a single patch
    using the distance-transform ridgeline method.

    Algorithm:
      1. Compute distance transform of the patch interior.
      2. Threshold at an adaptive width to separate "wide" interior regions.
      3. If thresholding produces >= 2 disjoint wide regions, the narrow band
         between them is a bottleneck.
      4. Find the narrowest point in each connecting narrow band.

    Parameters
    ----------
    labels : ndarray
        Patch label raster (0 = matrix, >0 = patch IDs).
    pid : int
        Patch ID to analyze.
    min_width_threshold : float
        Absolute minimum passage width (in pixels, full-width) below which
        a passage is considered a bottleneck.
    min_patch_area : int
        Patches smaller than this are never decomposed.
    min_sub_fraction : float
        Each sub-region must be at least this fraction of total patch area
        to be considered meaningful.
    max_bottlenecks : int
        Maximum bottlenecks to return per patch.

    Returns
    -------
    list of dict
        Each dict describes one bottleneck with keys:
            pinch_row, pinch_col : location of narrowest point
            width : passage width at pinch point (pixels, full-width)
            sub_areas : (area_a, area_b) of the two separated wide regions
            sub_wide_ids : (id_a, id_b) labels in the wide-region labeling
            wide_labels : ndarray of labeled wide regions (transient)
            severity : float 0-1, how severe the bottleneck is
            bridge_cost : number of narrow-band pixels in the connecting passage
            connecting_narrow_pixels : frozenset of (r,c) in the narrow passage
    """
    if not HAS_SCIPY:
        return []

    patch_mask = (labels == int(pid)).astype(np.uint8)
    area = int(np.count_nonzero(patch_mask))
    if area < min_patch_area:
        return []

    # Step 1: Distance transform
    dt = distance_transform_edt(patch_mask).astype(np.float32)
    interior_dt = dt[patch_mask > 0]
    if len(interior_dt) == 0:
        return []

    median_width = float(np.median(interior_dt))
    p75_width = float(np.percentile(interior_dt, 75))

    if median_width < 1.5:
        return []  # Uniformly narrow, no meaningful internal structure

    # Adaptive threshold: passage is "narrow" if dt < this value
    # dt gives distance to nearest boundary ≈ half the passage width.
    # We want to separate the "wide interior" from narrow connectors.
    # A good threshold is between the narrow passage dt (~1 for 1-2px wide)
    # and the interior dt (median, typically 2-5+).
    #
    # Strategy: use a fraction of the median that sits between narrow
    # passages and interior bulk. 0.55 * median works well empirically:
    # - Patch with median dt=2.0: threshold=1.1 → catches 1px bridges (dt=1.0)
    # - Patch with median dt=5.0: threshold=2.75 → catches passages <5px wide
    dt_threshold = max(
        1.05,  # Absolute minimum: must be > 1.0 to catch 1-pixel bridges
        min(
            float(min_width_threshold),
            median_width * 0.55,
        ),
    )

    # Step 2: Separate wide interior from narrow band
    wide_mask = (patch_mask > 0) & (dt >= dt_threshold)
    narrow_band = (patch_mask > 0) & (dt < dt_threshold) & (dt > 0)

    if not np.any(narrow_band) or not np.any(wide_mask):
        return []

    wide_labels, n_wide = ndlabel(wide_mask)
    if n_wide < 2:
        return []  # No separation at this threshold

    # Step 3: Find significant wide regions
    min_sub_area = max(5, int(min_sub_fraction * area))
    wide_sizes: Dict[int, int] = {}
    for sid in range(1, n_wide + 1):
        sz = int(np.count_nonzero(wide_labels == sid))
        if sz >= min_sub_area:
            wide_sizes[sid] = sz

    if len(wide_sizes) < 2:
        return []

    wide_ids = sorted(wide_sizes.keys(), key=lambda k: -wide_sizes[k])

    # Step 4: For each pair of significant wide regions, find connecting passage
    struct_3x3 = generate_binary_structure(2, 2)  # 8-connectivity
    narrow_labels, n_narrow = ndlabel(narrow_band)

    bottlenecks: List[Dict[str, Any]] = []

    for i in range(min(len(wide_ids), 4)):
        for j in range(i + 1, min(len(wide_ids), 4)):
            sid_a, sid_b = wide_ids[i], wide_ids[j]
            area_a, area_b = wide_sizes[sid_a], wide_sizes[sid_b]

            # Dilate each wide region to find adjacent narrow-band pixels
            border_a = binary_dilation(wide_labels == sid_a, structure=struct_3x3) & narrow_band
            border_b = binary_dilation(wide_labels == sid_b, structure=struct_3x3) & narrow_band

            # Find narrow-band components that touch both wide regions
            connecting_nids: Set[int] = set()
            for nid in range(1, n_narrow + 1):
                nid_mask = (narrow_labels == nid)
                if np.any(nid_mask & border_a) and np.any(nid_mask & border_b):
                    connecting_nids.add(nid)

            if not connecting_nids:
                continue

            for nid in connecting_nids:
                conn_mask = (narrow_labels == nid)
                conn_coords = np.argwhere(conn_mask)
                if len(conn_coords) == 0:
                    continue

                conn_dt = dt[conn_mask]
                min_dt = float(np.min(conn_dt))
                pinch_local_idx = int(np.argmin(conn_dt))
                pinch_r = int(conn_coords[pinch_local_idx, 0])
                pinch_c = int(conn_coords[pinch_local_idx, 1])

                passage_width = float(2.0 * min_dt)  # dt = half-width
                severity = max(0.0, min(1.0, 1.0 - (passage_width / max(2.0 * p75_width, 1.0))))
                bridge_cost = int(len(conn_coords))

                bottlenecks.append({
                    "pinch_row": pinch_r,
                    "pinch_col": pinch_c,
                    "width": passage_width,
                    "sub_areas": (area_a, area_b),
                    "sub_wide_ids": (sid_a, sid_b),
                    "wide_labels": wide_labels,
                    "severity": severity,
                    "bridge_cost": bridge_cost,
                    "connecting_narrow_pixels": frozenset(map(tuple, conn_coords)),
                    "dt_threshold": dt_threshold,
                    "median_dt": median_width,
                })

    # Deduplicate: keep most severe per spatial zone
    if len(bottlenecks) > 1:
        bottlenecks.sort(key=lambda b: -b["severity"])
        kept: List[Dict[str, Any]] = []
        used_zones: Set[Tuple[int, int]] = set()
        for bn in bottlenecks:
            zone = (bn["pinch_row"] // 12, bn["pinch_col"] // 12)
            if zone in used_zones:
                continue
            used_zones.add(zone)
            kept.append(bn)
        bottlenecks = kept

    return bottlenecks[:max_bottlenecks]


# ---------------------------------------------------------------------------
# Sub-Patch Decomposition
# ---------------------------------------------------------------------------

def decompose_patches_for_lf(
    labels: np.ndarray,
    patch_sizes: Dict[int, int],
    *,
    min_decompose_area: int = 40,
    max_bottlenecks_per_patch: int = 3,
    min_width_threshold: float = 2.5,
    virtual_id_offset: int = 100_000,
) -> Tuple[Dict[int, int], Dict[int, int], List[Dict[str, Any]]]:
    """
    Decompose patches with internal bottlenecks into virtual sub-nodes.

    Patches without bottlenecks pass through unchanged. Patches with
    detected bottlenecks are split into 2+ virtual sub-nodes connected
    by high-resistance virtual edges.

    Parameters
    ----------
    labels : ndarray
        Patch label raster.
    patch_sizes : dict
        {patch_id: area_in_pixels}.
    min_decompose_area : int
        Only consider patches larger than this for decomposition.
    max_bottlenecks_per_patch : int
        Maximum cuts per patch.
    min_width_threshold : float
        Passage width threshold for bottleneck detection.
    virtual_id_offset : int
        Starting offset for virtual node IDs to avoid collisions.

    Returns
    -------
    sub_patch_sizes : dict
        {node_id: area_pixels} for all nodes (original + virtual).
    sub_to_parent : dict
        {node_id: original_patch_id}.
    bottleneck_edges : list of dict
        Virtual edges representing bottleneck passages. Each dict has:
            node_a, node_b : virtual sub-node IDs
            parent_pid : original patch ID
            resistance : float (high = severe bottleneck)
            ipc_pixels : frozenset of (r,c) in the narrow passage
            bridge_cost : int (pixel count)
            severity : float 0-1
            width : float (passage width)
            pinch_row, pinch_col : location
    """
    sub_patch_sizes: Dict[int, int] = {}
    sub_to_parent: Dict[int, int] = {}
    bottleneck_edges: List[Dict[str, Any]] = []

    next_vid = int(virtual_id_offset)
    if patch_sizes:
        next_vid = max(max(patch_sizes.keys()) + virtual_id_offset, virtual_id_offset)

    for pid, area in sorted(patch_sizes.items()):
        if area < min_decompose_area:
            sub_patch_sizes[pid] = area
            sub_to_parent[pid] = pid
            continue

        bottlenecks = detect_patch_bottlenecks(
            labels,
            pid,
            min_width_threshold=min_width_threshold,
            min_patch_area=min_decompose_area,
            max_bottlenecks=max_bottlenecks_per_patch,
        )

        if not bottlenecks:
            sub_patch_sizes[pid] = area
            sub_to_parent[pid] = pid
            continue

        # Use the most severe bottleneck for primary decomposition
        bn = bottlenecks[0]
        area_a, area_b = bn["sub_areas"]

        vid_a = next_vid
        vid_b = next_vid + 1
        next_vid += 2

        # Distribute narrow-band pixels proportionally
        narrow_pixels = max(0, area - area_a - area_b)
        sub_patch_sizes[vid_a] = area_a + narrow_pixels // 2
        sub_patch_sizes[vid_b] = area_b + (narrow_pixels - narrow_pixels // 2)
        sub_to_parent[vid_a] = pid
        sub_to_parent[vid_b] = pid

        # Compute bottleneck edge resistance
        # Resistance ~ passage_length / passage_cross_section
        passage_width = max(bn["width"], 0.5)
        bridge_cost = max(bn.get("bridge_cost", 1), 1)
        # The resistance should be HIGH for narrow passages
        # Empirically: R = cost / width works well
        bottleneck_resistance = float(bridge_cost) / max(passage_width, 0.1)

        bottleneck_edges.append({
            "node_a": vid_a,
            "node_b": vid_b,
            "parent_pid": pid,
            "resistance": bottleneck_resistance,
            "ipc_pixels": bn.get("connecting_narrow_pixels", frozenset()),
            "bridge_cost": bridge_cost,
            "severity": bn["severity"],
            "width": passage_width,
            "pinch_row": bn["pinch_row"],
            "pinch_col": bn["pinch_col"],
            "wide_labels": bn.get("wide_labels"),
            "sub_wide_ids": bn.get("sub_wide_ids"),
            "_sub_wide_ids_a": bn.get("sub_wide_ids", (-1, -1))[0],
            "_sub_wide_ids_b": bn.get("sub_wide_ids", (-1, -1))[1],
        })

        # Handle additional bottlenecks (secondary cuts)
        # These create additional sub-nodes from one of the existing sub-regions
        for bn_extra in bottlenecks[1:]:
            # Check if this bottleneck is within sub-region A or B
            pr, pc = bn_extra["pinch_row"], bn_extra["pinch_col"]
            wide_labels = bn.get("wide_labels")
            if wide_labels is None:
                continue

            # Determine which sub-region this secondary bottleneck falls in
            # by checking the wide-region label at the pinch point
            sid_a_primary, sid_b_primary = bn["sub_wide_ids"]
            try:
                wl_at_pinch = int(wide_labels[pr, pc])
            except (IndexError, ValueError):
                continue

            if wl_at_pinch == sid_a_primary:
                parent_vid = vid_a
                parent_area = sub_patch_sizes[vid_a]
            elif wl_at_pinch == sid_b_primary:
                parent_vid = vid_b
                parent_area = sub_patch_sizes[vid_b]
            else:
                continue  # Pinch point in narrow band, skip

            ea, eb = bn_extra["sub_areas"]
            if ea + eb < parent_area * 0.3:
                continue  # Too small relative to parent sub-region

            vid_c = next_vid
            next_vid += 1
            split_area = min(eb, parent_area // 3)  # Don't over-split
            sub_patch_sizes[vid_c] = split_area
            sub_patch_sizes[parent_vid] = max(1, sub_patch_sizes[parent_vid] - split_area)
            sub_to_parent[vid_c] = pid

            pw = max(bn_extra["width"], 0.5)
            bc = max(bn_extra.get("bridge_cost", 1), 1)
            bottleneck_edges.append({
                "node_a": parent_vid,
                "node_b": vid_c,
                "parent_pid": pid,
                "resistance": float(bc) / max(pw, 0.1),
                "ipc_pixels": bn_extra.get("connecting_narrow_pixels", frozenset()),
                "bridge_cost": bc,
                "severity": bn_extra["severity"],
                "width": pw,
                "pinch_row": bn_extra["pinch_row"],
                "pinch_col": bn_extra["pinch_col"],
                "wide_labels": bn_extra.get("wide_labels"),
                "sub_wide_ids": bn_extra.get("sub_wide_ids"),
                "_sub_wide_ids_a": bn_extra.get("sub_wide_ids", (-1, -1))[0],
                "_sub_wide_ids_b": bn_extra.get("sub_wide_ids", (-1, -1))[1],
            })

    return sub_patch_sizes, sub_to_parent, bottleneck_edges


# ---------------------------------------------------------------------------
# IPC Candidate Generation from Bottlenecks
# ---------------------------------------------------------------------------

def generate_ipc_candidates(
    bottleneck_edges: List[Dict[str, Any]],
    labels: np.ndarray,
    min_corridor_width: int,
    obstacle_mask: Optional[np.ndarray] = None,
    inflate_fn=None,  # Pass _inflate_corridor_pixels from analysis_raster
) -> List[Dict[str, Any]]:
    """
    Convert detected bottleneck edges into standard corridor candidates.

    Each bottleneck gets a candidate whose selection adds a low-resistance
    parallel edge between the two sub-nodes, substantially reducing
    effective resistance through the bottleneck.

    Parameters
    ----------
    bottleneck_edges : list of dict
        From decompose_patches_for_lf().
    labels : ndarray
        Patch label raster.
    min_corridor_width : int
        Minimum corridor width for buffering.
    obstacle_mask : ndarray or None
        Boolean obstacle mask.
    inflate_fn : callable or None
        Function to buffer corridor pixels to minimum width.
        Signature: (pixels_set, offsets, rows, cols, obstacle_mask) -> set
        If None, no buffering is applied.

    Returns
    -------
    list of dict
        Standard corridor candidate dicts compatible with the LF optimizer.
    """
    rows, cols = labels.shape
    candidates: List[Dict[str, Any]] = []

    # Precompute corridor offsets if inflate_fn is provided
    offsets = None
    if inflate_fn is not None:
        width = max(1, int(min_corridor_width))
        if width <= 1:
            offsets = [(0, 0)]
        else:
            rad = int(math.ceil((float(width) - 1.0) / 2.0))
            offsets = [
                (dr, dc)
                for dr in range(-rad, rad + 1)
                for dc in range(-rad, rad + 1)
                if dr * dr + dc * dc <= rad * rad + 1
            ]

    for bn_edge in bottleneck_edges:
        ipc_raw_pixels = bn_edge.get("ipc_pixels", frozenset())
        if not ipc_raw_pixels:
            continue

        # Buffer to corridor width if possible
        if inflate_fn is not None and offsets is not None:
            buffered = inflate_fn(set(ipc_raw_pixels), offsets, rows, cols, obstacle_mask=obstacle_mask)
        else:
            buffered = set(ipc_raw_pixels)

        if not buffered:
            buffered = set(ipc_raw_pixels)

        # Cost = only non-habitat pixels that need conversion
        # For isthmus bottlenecks, the narrow passage is already habitat,
        # so the cost is just the buffer expansion into non-habitat.
        gap_pixels = frozenset(
            (r, c) for r, c in buffered
            if 0 <= r < rows and 0 <= c < cols and int(labels[r, c]) == 0
        )
        # Also count non-habitat in the raw IPC pixels (concavity closures)
        raw_gap = frozenset(
            (r, c) for r, c in ipc_raw_pixels
            if 0 <= r < rows and 0 <= c < cols and int(labels[r, c]) == 0
        )
        # Only emit a visible IPC when the bottleneck includes a real matrix gap.
        # If the passage is entirely habitat, buffering can create random side pixels
        # that do not represent a meaningful closure on the raster.
        if not raw_gap:
            continue
        # Use the larger of the two gap sets
        if len(raw_gap) > len(gap_pixels):
            gap_pixels = raw_gap
        
        # Cost is the number of new pixels to build.
        # For isthmus bottlenecks (passage already habitat), cost is very low
        # (just the side-buffer for corridor width), which is correct —
        # these are essentially free improvements.
        cost = max(1, len(gap_pixels))  # At least 1 to avoid division by zero

        # IPC resistance: much lower than the bottleneck resistance
        # The IPC builds a proper corridor, so its resistance is based on
        # a short passage at full corridor width.
        # passage_length ≈ sqrt(bridge_cost) (characteristic passage dimension)
        # passage_width = min_corridor_width (or wider)
        # R_ipc << R_bottleneck ensures selecting the IPC gives large gain
        bridge_cost = max(bn_edge.get("bridge_cost", cost), 1)
        passage_length = max(1.0, math.sqrt(float(bridge_cost)))
        ipc_resistance = max(0.5, passage_length / max(float(min_corridor_width), 1.0))

        parent_pid = bn_edge["parent_pid"]
        node_a = bn_edge["node_a"]
        node_b = bn_edge["node_b"]

        candidates.append({
            # Standard candidate fields (compatible with _raster_lf_build_candidate_specs)
            "patch1": node_a,
            "patch2": node_b,
            "p1": node_a,
            "p2": node_b,
            "pixels": gap_pixels,
            "buffered_pixels": frozenset(buffered),
            "habitat_pixels": frozenset(),
            "area": cost,
            "length": ipc_resistance,
            "patch_ids": {node_a, node_b},
            "raw_patch_ids": {parent_pid},

            # IPC metadata
            "type": "bottleneck_ipc",
            "variant": "bottleneck_ipc",
            "flow_ipc": True,
            "intra_patch": False,
            "intra_patch_id": parent_pid,
            "bottleneck_severity": bn_edge["severity"],
            "bottleneck_width": bn_edge["width"],
            "bottleneck_resistance": bn_edge["resistance"],
            "pinch_row": bn_edge["pinch_row"],
            "pinch_col": bn_edge["pinch_col"],
            "mouth_row": float(bn_edge["pinch_row"]),
            "mouth_col": float(bn_edge["pinch_col"]),

            # Anchors for downstream rendering
            "anchors": {
                "a_row": bn_edge["pinch_row"],
                "a_col": bn_edge["pinch_col"],
                "b_row": bn_edge["pinch_row"],
                "b_col": bn_edge["pinch_col"],
            },
        })

    return candidates


# ---------------------------------------------------------------------------
# Candidate Remapping for Decomposed Patches
# ---------------------------------------------------------------------------

def remap_candidates_to_subnodes(
    candidates: List[Dict[str, Any]],
    labels: Optional[np.ndarray],
    sub_to_parent: Dict[int, int],
    sub_patch_sizes: Dict[int, int],
    bottleneck_edges: List[Dict[str, Any]],
) -> List[Dict[str, Any]]:
    """
    Remap inter-patch candidates so that endpoints pointing to decomposed
    patches are redirected to the nearest virtual sub-node.

    For each candidate with an endpoint at a decomposed patch, assign it
    to the sub-node whose wide region is closest to the candidate's
    anchor/centroid point.

    Parameters
    ----------
    candidates : list of dict
        Original inter-patch corridor candidates.
    labels : ndarray
        Patch label raster.
    sub_to_parent : dict
        {virtual_node_id: original_patch_id}.
    sub_patch_sizes : dict
        {node_id: area} for all nodes.
    bottleneck_edges : list of dict
        Bottleneck edge descriptors (contain wide_labels info transitionally).

    Returns
    -------
    list of dict
        Candidates with remapped patch IDs.
    """
    # Build reverse map: original_pid -> list of (virtual_id, wide_label_id, bn_edge)
    parent_to_subs: Dict[int, List[Tuple[int, int, Dict]]] = {}
    for vid, parent in sub_to_parent.items():
        if vid != parent:
            for bn in bottleneck_edges:
                if bn["parent_pid"] == parent:
                    if bn["node_a"] == vid:
                        sid = bn.get("_sub_wide_ids_a", -1)
                    elif bn["node_b"] == vid:
                        sid = bn.get("_sub_wide_ids_b", -1)
                    else:
                        sid = -1
                    parent_to_subs.setdefault(parent, []).append((vid, sid, bn))

    # Build centroid lookup for each sub-node
    # (Using the bottleneck location as a dividing plane)
    decomposed_pids = set()
    bn_by_parent: Dict[int, Dict] = {}
    for bn in bottleneck_edges:
        pid = bn["parent_pid"]
        decomposed_pids.add(pid)
        bn_by_parent.setdefault(pid, bn)

    if not decomposed_pids:
        return candidates  # Nothing to remap

    def _nearest_subnode(pid: int, row: float, col: float) -> int:
        """Pick the virtual sub-node closest to the given position."""
        bn = bn_by_parent.get(pid)
        if bn is None:
            return pid  # Not decomposed

        vid_a = bn["node_a"]
        vid_b = bn["node_b"]
        pr, pc = bn["pinch_row"], bn["pinch_col"]

        # Simple heuristic: which side of the pinch point is (row, col) on?
        # Use the wide_labels array if available
        wide_labels = bn.get("wide_labels")
        if wide_labels is not None:
            ri, ci = int(round(row)), int(round(col))
            ri = max(0, min(ri, wide_labels.shape[0] - 1))
            ci = max(0, min(ci, wide_labels.shape[1] - 1))
            wl = int(wide_labels[ri, ci])
            sid_a, sid_b = bn["sub_wide_ids"]
            if wl == sid_a:
                return vid_a
            elif wl == sid_b:
                return vid_b

        # Fallback: distance to pinch point as tie-breaker
        # Assign to vid_a if closer to "above" the pinch, vid_b otherwise
        if row < pr or (row == pr and col < pc):
            return vid_a
        return vid_b

    remapped: List[Dict[str, Any]] = []
    for cand in candidates:
        cand = dict(cand)  # Shallow copy

        p1 = int(cand.get("patch1", cand.get("p1", 0)) or 0)
        p2 = int(cand.get("patch2", cand.get("p2", 0)) or 0)

        if p1 in decomposed_pids:
            # Get anchor point for this endpoint
            cr = float(cand.get("centroid_row", cand.get("mouth_row", 0.0)) or 0.0)
            cc = float(cand.get("centroid_col", cand.get("mouth_col", 0.0)) or 0.0)
            if cr == 0.0 and cc == 0.0:
                # Estimate from pixels
                pixels = cand.get("pixels") or cand.get("buffered_pixels") or frozenset()
                if pixels:
                    cr = float(sum(p[0] for p in pixels)) / max(len(pixels), 1)
                    cc = float(sum(p[1] for p in pixels)) / max(len(pixels), 1)
            new_p1 = _nearest_subnode(p1, cr, cc)
            cand["patch1"] = new_p1
            cand["p1"] = new_p1

        if p2 in decomposed_pids:
            cr = float(cand.get("centroid_row", cand.get("mouth_row", 0.0)) or 0.0)
            cc = float(cand.get("centroid_col", cand.get("mouth_col", 0.0)) or 0.0)
            if cr == 0.0 and cc == 0.0:
                pixels = cand.get("pixels") or cand.get("buffered_pixels") or frozenset()
                if pixels:
                    cr = float(sum(p[0] for p in pixels)) / max(len(pixels), 1)
                    cc = float(sum(p[1] for p in pixels)) / max(len(pixels), 1)
            new_p2 = _nearest_subnode(p2, cr, cc)
            cand["patch2"] = new_p2
            cand["p2"] = new_p2

        p1_new = int(cand.get("patch1", cand.get("p1", 0)) or 0)
        p2_new = int(cand.get("patch2", cand.get("p2", 0)) or 0)
        pids_new = {p for p in (p1_new, p2_new) if int(p) > 0}
        cand["patch_ids"] = pids_new

        remapped.append(cand)

    return remapped


# ---------------------------------------------------------------------------
# Area-Weighted Disconnection Penalty
# ---------------------------------------------------------------------------

def scaled_disconnected_penalty(
    base_penalty: float,
    area_u: float,
    area_v: float,
    total_area: float,
) -> float:
    """
    Scale disconnected penalty by the importance of the smaller patch.

    Connecting a patch that represents 0.1% of total habitat should
    contribute far less to the objective than connecting one that
    represents 10% of total habitat.

    Parameters
    ----------
    base_penalty : float
        The default disconnection penalty.
    area_u, area_v : float
        Areas of the two disconnected nodes.
    total_area : float
        Total habitat area across all patches.

    Returns
    -------
    float
        Scaled penalty.
    """
    min_area = min(float(area_u), float(area_v))
    total = max(float(total_area), 1.0)
    share = min_area / total

    if share < 0.005:
        # Very tiny patch: 5-10% of base penalty
        scale = max(0.05, share / 0.005 * 0.10)
    elif share < 0.01:
        # Small patch: 10-30% of base penalty
        scale = 0.10 + 0.20 * (share - 0.005) / 0.005
    elif share < 0.05:
        # Moderate: 30-100%
        scale = 0.30 + 0.70 * (share - 0.01) / 0.04
    else:
        scale = 1.0

    return float(base_penalty * scale)


# ---------------------------------------------------------------------------
# Result Remapping (Sub-Nodes Back to Original Patch IDs)
# ---------------------------------------------------------------------------

def remap_results_to_original_pids(
    selected: Dict[int, Dict[str, Any]],
    sub_to_parent: Dict[int, int],
) -> Dict[int, Dict[str, Any]]:
    """
    After optimization, remap virtual sub-node IDs in selected corridors
    back to their original parent patch IDs for rendering and reporting.
    """
    for cid, corr in selected.items():
        p1 = corr.get("p1")
        p2 = corr.get("p2")

        if p1 is not None and int(p1) in sub_to_parent:
            corr["p1_subnode"] = int(p1)
            corr["p1"] = sub_to_parent[int(p1)]
        if p2 is not None and int(p2) in sub_to_parent:
            corr["p2_subnode"] = int(p2)
            corr["p2"] = sub_to_parent[int(p2)]

        # Also remap patch_ids
        pids = corr.get("patch_ids")
        if isinstance(pids, (set, frozenset)):
            corr["patch_ids"] = {sub_to_parent.get(int(p), int(p)) for p in pids}

    return selected
