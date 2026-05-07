from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np


HABITAT_AVAILABILITY_DEFAULT_KERNEL = "exponential"
HABITAT_AVAILABILITY_DEFAULT_SCALING = "sqrt"
HABITAT_AVAILABILITY_CUTOFF_MULTIPLIER = 3.0
HABITAT_AVAILABILITY_REDUNDANT_PROB_THRESHOLD = 0.7
HABITAT_AVAILABILITY_REDUNDANT_GAIN_FACTOR = 0.25


def normalize_habitat_availability_kernel(value: object) -> str:
    key = str(value or HABITAT_AVAILABILITY_DEFAULT_KERNEL).strip().lower().replace(" ", "_").replace("-", "_")
    if key not in {"exponential"}:
        key = HABITAT_AVAILABILITY_DEFAULT_KERNEL
    return key


def normalize_patch_area_scaling(value: object) -> str:
    key = str(value or HABITAT_AVAILABILITY_DEFAULT_SCALING).strip().lower().replace(" ", "_").replace("-", "_")
    aliases = {
        "square_root": "sqrt",
        "root": "sqrt",
        "logarithmic": "log",
        "ln": "log",
    }
    key = aliases.get(key, key)
    if key not in {"sqrt", "log"}:
        key = HABITAT_AVAILABILITY_DEFAULT_SCALING
    return key


def habitat_availability_alpha(dispersal_distance: float) -> float:
    return max(float(dispersal_distance or 0.0) / 3.0, 1e-9)


def scale_patch_area(area: float, *, quality_weight: float = 1.0, scaling: object = "sqrt") -> float:
    raw = max(0.0, float(area or 0.0)) * max(0.0, float(quality_weight or 0.0))
    mode = normalize_patch_area_scaling(scaling)
    if raw <= 0.0:
        return 0.0
    if mode == "log":
        return float(math.log1p(raw))
    return float(math.sqrt(raw))


def habitat_probability(distance: float, *, alpha: float, kernel: object = "exponential", cutoff: Optional[float] = None) -> float:
    if not np.isfinite(float(distance)):
        return 0.0
    d = max(0.0, float(distance))
    if cutoff is not None and d > float(cutoff):
        return 0.0
    key = normalize_habitat_availability_kernel(kernel)
    if key == "exponential":
        return float(math.exp(-d / max(float(alpha), 1e-9)))
    return float(math.exp(-d / max(float(alpha), 1e-9)))


@dataclass(frozen=True)
class HabitatAvailabilityNode:
    node_id: int
    raw_area: float
    effective_area: float


class HabitatAvailabilityEvaluator:
    """
    Patch-graph evaluator for Reachable Habitat Score:
      HA = Σ_i Σ_j (Ai * Aj * p_ij)

    The evaluator keeps a thresholded shortest-path matrix and updates it
    incrementally when a new corridor edge is added.
    """

    def __init__(
        self,
        nodes: Sequence[HabitatAvailabilityNode],
        *,
        dispersal_distance: float,
        kernel: object = HABITAT_AVAILABILITY_DEFAULT_KERNEL,
        cutoff_multiplier: float = HABITAT_AVAILABILITY_CUTOFF_MULTIPLIER,
    ) -> None:
        kept = [n for n in nodes if max(float(n.effective_area or 0.0), 0.0) > 0.0]
        self.nodes: List[HabitatAvailabilityNode] = sorted(kept, key=lambda n: int(n.node_id))
        self.node_ids: List[int] = [int(n.node_id) for n in self.nodes]
        self.index_by_id: Dict[int, int] = {int(nid): idx for idx, nid in enumerate(self.node_ids)}
        self.raw_areas = np.array([max(0.0, float(n.raw_area or 0.0)) for n in self.nodes], dtype=float)
        self.weights = np.array([max(0.0, float(n.effective_area or 0.0)) for n in self.nodes], dtype=float)
        self.dispersal_distance = max(float(dispersal_distance or 0.0), 1e-9)
        self.alpha = habitat_availability_alpha(self.dispersal_distance)
        self.kernel = normalize_habitat_availability_kernel(kernel)
        self.cutoff = max(float(cutoff_multiplier or 0.0), 1.0) * self.dispersal_distance
        self.graph_edges: Dict[Tuple[int, int], float] = {}

        size = len(self.nodes)
        self.dist = np.full((size, size), np.inf, dtype=float)
        if size > 0:
            np.fill_diagonal(self.dist, 0.0)
        self.prob = self._distance_to_probability_matrix(self.dist)
        self.reachable_area = self.prob.dot(self.weights) if size > 0 else np.zeros(0, dtype=float)
        self.habitat_availability = float(self.weights.dot(self.reachable_area)) if size > 0 else 0.0

    def _distance_to_probability_matrix(self, dist: np.ndarray) -> np.ndarray:
        if dist.size == 0:
            return np.zeros_like(dist, dtype=float)
        out = np.zeros_like(dist, dtype=float)
        valid = np.isfinite(dist) & (dist <= self.cutoff + 1e-12)
        if np.any(valid):
            out[valid] = np.exp(-np.maximum(dist[valid], 0.0) / self.alpha)
        if out.shape[0] == out.shape[1]:
            np.fill_diagonal(out, 1.0)
        return out

    def _cluster_area_within_threshold(self) -> float:
        size = len(self.node_ids)
        if size <= 0:
            return 0.0
        parent = list(range(size))

        def _find(idx: int) -> int:
            root = idx
            while parent[root] != root:
                root = parent[root]
            while parent[idx] != idx:
                nxt = parent[idx]
                parent[idx] = root
                idx = nxt
            return root

        def _union(a: int, b: int) -> None:
            ra = _find(a)
            rb = _find(b)
            if ra != rb:
                parent[rb] = ra

        thr = max(float(self.dispersal_distance), 0.0)
        for i in range(size):
            for j in range(i + 1, size):
                if self.dist[i, j] <= thr + 1e-12:
                    _union(i, j)

        cluster_area: Dict[int, float] = {}
        for idx, area in enumerate(self.raw_areas):
            root = _find(idx)
            cluster_area[root] = float(cluster_area.get(root, 0.0) + max(float(area), 0.0))
        return float(max(cluster_area.values())) if cluster_area else 0.0

    def _metrics_from_state(
        self,
        *,
        dist: Optional[np.ndarray] = None,
        prob: Optional[np.ndarray] = None,
        reachable_area: Optional[np.ndarray] = None,
        habitat_availability: Optional[float] = None,
    ) -> Dict[str, float]:
        dist_arr = self.dist if dist is None else dist
        reachable = self.reachable_area if reachable_area is None else reachable_area
        ha_val = self.habitat_availability if habitat_availability is None else float(habitat_availability)
        if reachable.size <= 0:
            mean_reachable = 0.0
            median_reachable = 0.0
        else:
            mean_reachable = float(np.mean(reachable))
            median_reachable = float(np.median(reachable))
        saved_dist = self.dist
        if dist is not None:
            self.dist = dist_arr
        try:
            largest_cluster = self._cluster_area_within_threshold()
        finally:
            if dist is not None:
                self.dist = saved_dist
        return {
            "habitat_availability": float(ha_val),
            "mean_reachable_area": float(mean_reachable),
            "median_reachable_area": float(median_reachable),
            "largest_reachable_habitat_cluster": float(largest_cluster),
        }

    def snapshot_metrics(self) -> Dict[str, float]:
        return self._metrics_from_state()

    def _apply_edge_to_distance_matrix(self, dist: np.ndarray, u_idx: int, v_idx: int, length: float) -> np.ndarray:
        if u_idx == v_idx or length <= 0.0:
            return dist
        if dist[u_idx, v_idx] <= length + 1e-12:
            return dist
        out = np.array(dist, copy=True)
        out[u_idx, v_idx] = min(float(out[u_idx, v_idx]), float(length))
        out[v_idx, u_idx] = min(float(out[v_idx, u_idx]), float(length))
        via_uv = dist[:, [u_idx]] + float(length) + dist[[v_idx], :]
        via_vu = dist[:, [v_idx]] + float(length) + dist[[u_idx], :]
        out = np.minimum(out, via_uv)
        out = np.minimum(out, via_vu)
        out[out > self.cutoff] = np.inf
        if out.shape[0] == out.shape[1]:
            np.fill_diagonal(out, 0.0)
        return out

    @staticmethod
    def normalize_candidate_edges(
        patch_ids: Iterable[int],
        *,
        length: float,
        valid_node_ids: Optional[Iterable[int]] = None,
    ) -> List[Tuple[int, int, float]]:
        valid = None if valid_node_ids is None else {int(v) for v in valid_node_ids}
        ids: List[int] = []
        seen: set[int] = set()
        for pid in patch_ids:
            try:
                ipid = int(pid)
            except Exception:
                continue
            if valid is not None and ipid not in valid:
                continue
            if ipid in seen:
                continue
            seen.add(ipid)
            ids.append(ipid)
        edges: List[Tuple[int, int, float]] = []
        if len(ids) < 2:
            return edges
        edge_len = max(float(length or 0.0), 1e-9)
        for i in range(len(ids)):
            for j in range(i + 1, len(ids)):
                a = int(ids[i])
                b = int(ids[j])
                if a == b:
                    continue
                if a > b:
                    a, b = b, a
                edges.append((a, b, edge_len))
        return edges

    def evaluate_candidate(
        self,
        edge_specs: Sequence[Tuple[int, int, float]],
        *,
        corridor_cost: float,
    ) -> Optional[Dict[str, object]]:
        cost = max(float(corridor_cost or 0.0), 0.0)
        if cost <= 0.0 or len(self.node_ids) < 2:
            return None
        temp_dist = self.dist
        applied_edges: List[Tuple[int, int, float]] = []
        endpoint_probs_before: List[float] = []
        for u_id, v_id, edge_len in edge_specs:
            u_idx = self.index_by_id.get(int(u_id))
            v_idx = self.index_by_id.get(int(v_id))
            if u_idx is None or v_idx is None or u_idx == v_idx:
                continue
            prev_dist = float(temp_dist[u_idx, v_idx])
            endpoint_probs_before.append(
                habitat_probability(prev_dist, alpha=self.alpha, kernel=self.kernel, cutoff=self.cutoff)
            )
            new_temp = self._apply_edge_to_distance_matrix(temp_dist, u_idx, v_idx, float(edge_len))
            if np.array_equal(new_temp, temp_dist):
                continue
            temp_dist = new_temp
            applied_edges.append((int(u_id), int(v_id), float(edge_len)))
        if not applied_edges:
            return None

        old_prob = self.prob
        new_prob = self._distance_to_probability_matrix(temp_dist)
        delta_prob = new_prob - old_prob
        if not np.any(np.abs(delta_prob) > 1e-12):
            return None
        new_reachable = self.reachable_area + delta_prob.dot(self.weights)
        new_ha = float(self.weights.dot(new_reachable))
        gain = float(new_ha - self.habitat_availability)
        if gain <= 1e-12:
            return None
        penalized_gain = float(gain)
        if endpoint_probs_before and max(endpoint_probs_before) > HABITAT_AVAILABILITY_REDUNDANT_PROB_THRESHOLD:
            penalized_gain *= HABITAT_AVAILABILITY_REDUNDANT_GAIN_FACTOR
        score = float(penalized_gain / max(cost, 1e-12))
        metrics = self._metrics_from_state(
            dist=temp_dist,
            prob=new_prob,
            reachable_area=new_reachable,
            habitat_availability=new_ha,
        )
        return {
            "score": float(score),
            "gain": float(gain),
            "penalized_gain": float(penalized_gain),
            "cost": float(cost),
            "applied_edges": list(applied_edges),
            "dist": temp_dist,
            "prob": new_prob,
            "reachable_area": new_reachable,
            "metrics": metrics,
        }

    def apply_candidate(self, evaluation: Dict[str, object]) -> None:
        for u_id, v_id, edge_len in evaluation.get("applied_edges", []) or []:
            key = (int(min(u_id, v_id)), int(max(u_id, v_id)))
            prev = self.graph_edges.get(key)
            if prev is None or float(edge_len) + 1e-12 < float(prev):
                self.graph_edges[key] = float(edge_len)
        dist = evaluation.get("dist")
        prob = evaluation.get("prob")
        reachable = evaluation.get("reachable_area")
        if isinstance(dist, np.ndarray):
            self.dist = dist
        if isinstance(prob, np.ndarray):
            self.prob = prob
        if isinstance(reachable, np.ndarray):
            self.reachable_area = reachable
        self.habitat_availability = float(evaluation.get("metrics", {}).get("habitat_availability", self.habitat_availability))
