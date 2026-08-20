from __future__ import annotations

import heapq
import math
from collections import defaultdict
from dataclasses import dataclass
from typing import Callable, DefaultDict, Dict, Generic, Iterable, List, Optional, Sequence, Tuple, TypeVar

from .terralink_engine import UnionFind
from . import terralink_graph as nx

T = TypeVar("T")


@dataclass(frozen=True)
class BackbonePick(Generic[T]):
    candidate: T
    corr_type: str
    score: float
    overlap_ratio: float


def select_backbone_utility(
    candidates: Iterable[T],
    *,
    budget: float,
    get_patch_ids: Callable[[T], Sequence[int]],
    get_pair_key: Callable[[T], Tuple[int, int]],
    get_cost: Callable[[T], float],
    get_base_roi: Callable[[T], float],
    get_length: Callable[[T], float],
    get_patch_size: Callable[[int], float],
    overlap_ratio: Callable[[T, Sequence[object]], float],
    global_overlap_ratio: Optional[Callable[[T, Sequence[object]], float]] = None,
    overlap_obj: Callable[[T], object],
    redundancy_distance_ok: Optional[Callable[[T, Sequence[object]], bool]] = None,
    overlap_reject_ratio: float = 0.30,
    global_overlap_reject_ratio: float = 0.60,
    max_prior_per_pair: int = 3,
    diminishing_base: float = 0.5,
    shortcut_ratio_high: float = 3.0,
    shortcut_ratio_mid: float = 1.5,
    shortcut_ratio_low: float = 1.5,
    shortcut_mult_high: float = 0.9,
    shortcut_mult_mid: float = 0.5,
    shortcut_mult_low: float = 0.1,
    enable_bridge_pairs: bool = True,
    bridge_max_per_patch: int = 25,
    distance_guard_for_primary: bool = False,
    global_overlap_for_primary: bool = False,
    parallel_dominance_ratio: float = 1.35,
    parallel_overlap_penalty_floor: float = 0.20,
    debug_hook: Optional[Callable[[str, Dict[str, object]], None]] = None,
) -> Tuple[List[BackbonePick[T]], Dict[str, object]]:
    """
    Shared Most Connectivity greedy selector used by raster + vector.

    score = base_roi * multiplier

    multiplier:
      1.0  if candidate connects different components
      diminishing_base^(k+1) if already connected but spatially distinct (k = count already selected for this pair)
      0.01 if overlaps existing corridor for the pair by > overlap_reject_ratio
    """
    remaining = float(budget or 0.0)
    budget_used = 0.0
    primary_links = 0
    redundant_links = 0
    wasteful_links = 0

    uf = UnionFind()

    # Selected overlap representations by pair (limit memory per pair).
    selected_overlap_by_pair: DefaultDict[Tuple[int, int], List[object]] = defaultdict(list)
    selected_count_by_pair: DefaultDict[Tuple[int, int], int] = defaultdict(int)
    selected_overlap_by_component: DefaultDict[int, List[object]] = defaultdict(list)
    selected_overlap_global: List[object] = []
    reject_counts: DefaultDict[str, int] = defaultdict(int)
    trace_counts: DefaultDict[str, int] = defaultdict(int)
    heap_pushes = 0
    heap_pops = 0

    # Heap entries store a stamp so we can "re-score" candidates dynamically.
    heap: List[Tuple[float, int, int, T]] = []
    counter = 0
    stamps: Dict[int, int] = {}

    # Convert candidates to list once if iterable is one-shot.
    cand_list = list(candidates)
    cand_id_map: Dict[int, int] = {id(c): i + 1 for i, c in enumerate(cand_list)}

    def _cid(cand: T) -> int:
        return int(cand_id_map.get(id(cand), -1))

    def _emit(event: str, **payload: object) -> None:
        trace_counts[event] += 1
        if debug_hook is None:
            return
        try:
            debug_hook(event, payload)
        except Exception:  # nosec
            pass
    all_patch_ids: List[int] = []
    seen_patch_ids: set[int] = set()
    for cand in cand_list:
        for pid in get_patch_ids(cand) or []:
            try:
                pid_int = int(pid)
            except Exception:  # nosec
                continue
            if pid_int in seen_patch_ids:
                continue
            seen_patch_ids.add(pid_int)
            all_patch_ids.append(pid_int)

    for pid in all_patch_ids:
        uf.find(pid)
        try:
            uf.size[pid] = float(get_patch_size(pid) or 0.0)
            uf.count[pid] = 1
        except Exception:
            uf.size[pid] = float(uf.size.get(pid, 0.0) or 0.0)

    G = None
    if nx is not None:
        try:
            G = nx.Graph()
            G.add_nodes_from(all_patch_ids)
        except Exception:
            G = None

    def _stamp_key(cand: T) -> int:
        return id(cand)

    def _shortcut_multiplier(p1: int, p2: int, length: float) -> float:
        if length <= 0:
            return float(shortcut_mult_low)
        if G is None:
            return float(diminishing_base)
        try:
            current_len = float(nx.shortest_path_length(G, p1, p2, weight="weight"))
        except Exception:
            return float(diminishing_base)
        ratio = current_len / max(length, 1e-9)
        if ratio >= float(shortcut_ratio_high):
            return float(shortcut_mult_high)
        if ratio >= float(shortcut_ratio_mid):
            return float(shortcut_mult_mid)
        if ratio <= float(shortcut_ratio_low):
            return float(shortcut_mult_low)
        return float(shortcut_mult_low)

    for cand in cand_list:
        base = float(get_base_roi(cand) or 0.0)
        cost = float(get_cost(cand) or 0.0)
        if base <= 0.0 or cost <= 0.0:
            reject_counts["seed_invalid_base_or_cost"] += 1
            _emit("seed_skip", cid=_cid(cand), base=float(base), cost=float(cost), reason="invalid_base_or_cost")
            continue
        counter += 1
        k = _stamp_key(cand)
        stamps[k] = stamps.get(k, 0) + 1
        heapq.heappush(heap, (-base, counter, stamps[k], cand))
        heap_pushes += 1
        try:
            pids_dbg = [int(pid) for pid in get_patch_ids(cand) if pid is not None]
        except Exception:
            pids_dbg = []
        try:
            pair_dbg = list(get_pair_key(cand))
        except Exception:
            pair_dbg = []
        _emit(
            "seed_push",
            cid=_cid(cand),
            base=float(base),
            cost=float(cost),
            pair=pair_dbg,
            pids=pids_dbg,
        )

    picks: List[BackbonePick[T]] = []
    selected_ids: set[int] = set()

    if enable_bridge_pairs and remaining > 0:
        bridge_by_mid: Dict[int, List[Tuple[float, T, int, int, float]]] = defaultdict(list)
        for cand in cand_list:
            pids = [int(pid) for pid in get_patch_ids(cand) if pid is not None]
            if len(pids) != 2:
                continue
            p1, p2 = int(pids[0]), int(pids[1])
            base = float(get_base_roi(cand) or 0.0)
            cost = float(get_cost(cand) or 0.0)
            if base <= 0.0 or cost <= 0.0:
                continue
            bridge_by_mid[p1].append((base, cand, p1, p2, cost))
            bridge_by_mid[p2].append((base, cand, p2, p1, cost))

        for mid, items in bridge_by_mid.items():
            if len(items) <= bridge_max_per_patch:
                continue
            items.sort(key=lambda x: x[0], reverse=True)
            bridge_by_mid[mid] = items[: bridge_max_per_patch]

        bridge_pairs: List[Tuple[float, float, T, T, int, int]] = []
        for mid, items in bridge_by_mid.items():
            n = len(items)
            if n < 2:
                continue
            for i in range(n):
                _base1, cand1, _m1, other1, cost1 = items[i]
                for j in range(i + 1, n):
                    _base2, cand2, _m2, other2, cost2 = items[j]
                    if other1 == other2:
                        continue
                    total_cost = float(cost1 + cost2)
                    if total_cost <= 0.0 or total_cost > remaining:
                        continue
                    s1 = float(get_patch_size(int(other1)) or 0.0)
                    s2 = float(get_patch_size(int(other2)) or 0.0)
                    if s1 <= 0.0 or s2 <= 0.0:
                        continue
                    score = math.sqrt(s1 * s2) / total_cost
                    bridge_pairs.append((score, total_cost, cand1, cand2, int(other1), int(other2)))

        bridge_pairs.sort(key=lambda x: x[0], reverse=True)
        for score, total_cost, cand1, cand2, a, c in bridge_pairs:
            if total_cost > remaining:
                reject_counts["bridge_over_budget"] += 1
                continue
            if a == c:
                reject_counts["bridge_same_endpoint"] += 1
                continue
            if int(uf.find(a)) == int(uf.find(c)):
                reject_counts["bridge_already_connected"] += 1
                continue
            k1 = _stamp_key(cand1)
            k2 = _stamp_key(cand2)
            if k1 in selected_ids or k2 in selected_ids:
                reject_counts["bridge_candidate_already_selected"] += 1
                continue

            for cand in (cand1, cand2):
                pids = [int(pid) for pid in get_patch_ids(cand) if pid is not None]
                if len(pids) < 2:
                    reject_counts["bridge_bad_patch_ids"] += 1
                    _emit("bridge_skip", cid=_cid(cand), reason="bad_patch_ids")
                    continue
                cost = float(get_cost(cand) or 0.0)
                if cost <= 0.0 or cost > remaining:
                    reject_counts["bridge_cost_invalid_or_budget"] += 1
                    _emit("bridge_skip", cid=_cid(cand), reason="cost_invalid_or_budget", cost=float(cost), remaining=float(remaining))
                    continue
                if (
                    distance_guard_for_primary
                    and redundancy_distance_ok is not None
                    and selected_overlap_global
                ):
                    try:
                        if not bool(redundancy_distance_ok(cand, selected_overlap_global)):
                            reject_counts["bridge_distance_guard_primary"] += 1
                            _emit("bridge_skip", cid=_cid(cand), reason="distance_guard_primary")
                            continue
                    except Exception:
                        reject_counts["bridge_distance_guard_exception"] += 1
                        pass

                for pid in pids:
                    uf.find(int(pid))
                anchor = int(pids[0])
                for other in pids[1:]:
                    uf.union(anchor, int(other))

                remaining -= cost
                budget_used += cost
                primary_links += 1
                picks.append(BackbonePick(candidate=cand, corr_type="primary", score=float(score), overlap_ratio=0.0))
                _emit(
                    "commit",
                    stage="bridge_pairs",
                    cid=_cid(cand),
                    corr_type="primary",
                    score=float(score),
                    cost=float(cost),
                    remaining=float(remaining),
                    pair=list(get_pair_key(cand)),
                    pids=[int(x) for x in pids],
                )

                try:
                    obj = overlap_obj(cand)
                except Exception:
                    obj = None
                if obj is not None:
                    pair = get_pair_key(cand)
                    lst = selected_overlap_by_pair[pair]
                    lst.append(obj)
                    if len(lst) > int(max_prior_per_pair):
                        del lst[0]
                    selected_overlap_global.append(obj)
                    try:
                        roots_list = {int(uf.find(int(pid))) for pid in pids}
                        merged: List[object] = []
                        for r in roots_list:
                            merged.extend(selected_overlap_by_component.get(int(r), []))
                        merged.append(obj)
                        new_root = int(uf.find(anchor))
                        selected_overlap_by_component[new_root] = merged
                        for r in roots_list:
                            if int(r) != new_root:
                                selected_overlap_by_component.pop(int(r), None)
                    except Exception:  # nosec
                        pass

                selected_count_by_pair[get_pair_key(cand)] += 1
                if G is not None:
                    try:
                        length = float(get_length(cand) or 0.0)
                        if length <= 0:
                            length = cost
                        for other in pids[1:]:
                            G.add_edge(anchor, int(other), weight=float(length))
                    except Exception:  # nosec
                        pass

                selected_ids.add(_stamp_key(cand))

            if remaining <= 0:
                break

    while heap and remaining > 0:
        neg_score, _idx, stamp, cand = heapq.heappop(heap)
        heap_pops += 1
        k = _stamp_key(cand)
        if stamps.get(k, 0) != int(stamp):
            reject_counts["heap_stale_stamp"] += 1
            continue
        if k in selected_ids:
            reject_counts["heap_already_selected"] += 1
            continue
        old_score = -float(neg_score)

        cost = float(get_cost(cand) or 0.0)
        if cost <= 0.0 or cost > remaining:
            reject_counts["heap_cost_invalid_or_budget"] += 1
            _emit("heap_skip", cid=_cid(cand), reason="cost_invalid_or_budget", cost=float(cost), remaining=float(remaining))
            continue

        base_roi = float(get_base_roi(cand) or 0.0)
        if base_roi <= 0.0:
            reject_counts["heap_base_roi_invalid"] += 1
            _emit("heap_skip", cid=_cid(cand), reason="base_roi_invalid", base_roi=float(base_roi))
            continue

        pids = [int(pid) for pid in get_patch_ids(cand) if pid is not None]
        if len(pids) < 2:
            reject_counts["heap_bad_patch_ids"] += 1
            _emit("heap_skip", cid=_cid(cand), reason="bad_patch_ids")
            continue

        try:
            roots = {int(uf.find(int(pid))) for pid in pids}
        except Exception:
            roots = {int(uf.find(int(pids[0]))), int(uf.find(int(pids[-1])))}

        pair = get_pair_key(cand)
        overlap_r = 0.0
        global_overlap_r = 0.0
        if len(roots) > 1:
            if (
                distance_guard_for_primary
                and redundancy_distance_ok is not None
                and selected_overlap_global
            ):
                try:
                    if not bool(redundancy_distance_ok(cand, selected_overlap_global)):
                        reject_counts["primary_distance_guard"] += 1
                        _emit("heap_skip", cid=_cid(cand), reason="primary_distance_guard", pair=list(pair), roots=list(roots))
                        continue
                except Exception:
                    reject_counts["primary_distance_guard_exception"] += 1
                    pass
            if global_overlap_for_primary and global_overlap_ratio is not None and selected_overlap_global:
                try:
                    global_overlap_r = float(global_overlap_ratio(cand, selected_overlap_global) or 0.0)
                except Exception:
                    global_overlap_r = 0.0
                if global_overlap_r > float(global_overlap_reject_ratio):
                    reject_counts["primary_global_overlap_reject"] += 1
                    _emit(
                        "heap_skip",
                        cid=_cid(cand),
                        reason="primary_global_overlap_reject",
                        global_overlap=float(global_overlap_r),
                        threshold=float(global_overlap_reject_ratio),
                        pair=list(pair),
                    )
                    continue
            root_sizes = [float(uf.size.get(r, 0.0) or 0.0) for r in roots]
            target_importance = min(root_sizes) if root_sizes else 1.0
            if target_importance <= 0:
                target_importance = 1.0
            mult = float(target_importance)
        else:
            if redundancy_distance_ok is not None and selected_overlap_global:
                try:
                    if not bool(redundancy_distance_ok(cand, selected_overlap_global)):
                        reject_counts["redundant_distance_guard"] += 1
                        _emit("heap_skip", cid=_cid(cand), reason="redundant_distance_guard", pair=list(pair))
                        continue
                except Exception:
                    reject_counts["redundant_distance_guard_exception"] += 1
                    pass
            if global_overlap_ratio is not None and selected_overlap_global:
                try:
                    global_overlap_r = float(global_overlap_ratio(cand, selected_overlap_global) or 0.0)
                except Exception:
                    global_overlap_r = 0.0
                if global_overlap_r > float(global_overlap_reject_ratio):
                    reject_counts["redundant_global_overlap_reject"] += 1
                    _emit(
                        "heap_skip",
                        cid=_cid(cand),
                        reason="redundant_global_overlap_reject",
                        global_overlap=float(global_overlap_r),
                        threshold=float(global_overlap_reject_ratio),
                        pair=list(pair),
                    )
                    continue
            prior = selected_overlap_by_pair.get(pair, [])
            overlap_r = float(overlap_ratio(cand, prior) or 0.0)
            if overlap_r > float(overlap_reject_ratio):
                mult = 0.01
            else:
                length = float(get_length(cand) or 0.0)
                if length <= 0:
                    length = cost
                mult = _shortcut_multiplier(int(pids[0]), int(pids[-1]), float(length))
                # Penalize globally parallel redundancy when existing route is already competitive.
                if global_overlap_r > 0.0:
                    penalty = max(float(parallel_overlap_penalty_floor), 1.0 - float(global_overlap_r))
                    mult *= penalty
                    if G is not None:
                        try:
                            cur_len = float(nx.shortest_path_length(G, int(pids[0]), int(pids[-1]), weight="weight"))
                            ratio = cur_len / max(float(length), 1e-9)
                            if ratio <= float(parallel_dominance_ratio):
                                mult = min(mult, float(shortcut_mult_low) * 0.5)
                        except Exception:  # nosec
                            pass

        new_score = base_roi * mult
        if abs(new_score - old_score) > 1e-12:
            counter += 1
            stamps[k] = stamps.get(k, 0) + 1
            heapq.heappush(heap, (-new_score, counter, stamps[k], cand))
            heap_pushes += 1
            _emit(
                "heap_rescore",
                cid=_cid(cand),
                old_score=float(old_score),
                new_score=float(new_score),
                roots_count=int(len(roots)),
                pair=list(pair),
                overlap=float(overlap_r),
                global_overlap=float(global_overlap_r),
                mult=float(mult),
            )
            continue

        if len(roots) > 1:
            corr_type = "primary"
            primary_links += 1
        else:
            corr_type = "redundant"
            redundant_links += 1
            if mult <= float(shortcut_mult_low) or mult <= 0.01:
                corr_type = "wasteful"
                wasteful_links += 1

        # Commit: union all patch ids.
        for pid in pids:
            uf.find(int(pid))
        anchor = int(pids[0])
        for other in pids[1:]:
            uf.union(anchor, int(other))

        remaining -= cost
        budget_used += cost

        picks.append(BackbonePick(candidate=cand, corr_type=corr_type, score=float(new_score), overlap_ratio=float(overlap_r)))
        _emit(
            "commit",
            stage="heap",
            cid=_cid(cand),
            corr_type=str(corr_type),
            score=float(new_score),
            cost=float(cost),
            remaining=float(remaining),
            roots_count=int(len(roots)),
            pair=list(pair),
            pids=[int(x) for x in pids],
            overlap=float(overlap_r),
            global_overlap=float(global_overlap_r),
            mult=float(mult),
        )

        try:
            obj = overlap_obj(cand)
        except Exception:
            obj = None
        if obj is not None:
            lst = selected_overlap_by_pair[pair]
            lst.append(obj)
            if len(lst) > int(max_prior_per_pair):
                del lst[0]
            selected_overlap_global.append(obj)
            try:
                roots_list = list(roots)
                merged: List[object] = []
                for r in roots_list:
                    merged.extend(selected_overlap_by_component.get(int(r), []))
                merged.append(obj)
                new_root = int(uf.find(anchor))
                selected_overlap_by_component[new_root] = merged
                for r in roots_list:
                    if int(r) != new_root:
                        selected_overlap_by_component.pop(int(r), None)
            except Exception:  # nosec
                pass
        selected_count_by_pair[pair] += 1

        if G is not None:
            try:
                length = float(get_length(cand) or 0.0)
                if length <= 0:
                    length = cost
                for other in pids[1:]:
                    G.add_edge(anchor, int(other), weight=float(length))
            except Exception:  # nosec
                pass

    stats: Dict[str, object] = {
        "budget_used": budget_used,
        "budget_remaining": remaining,
        "primary_links": primary_links,
        "redundant_links": redundant_links,
        "wasteful_links": wasteful_links,
        "corridors_used": len(picks),
        "debug_reject_counts": dict(reject_counts),
        "debug_trace_counts": dict(trace_counts),
        "debug_heap_pushes": int(heap_pushes),
        "debug_heap_pops": int(heap_pops),
        "debug_candidate_count": int(len(cand_list)),
    }
    return picks, stats


# Back-compat aliases for older scripts and notebooks.
CircuitPick = BackbonePick
select_circuit_utility = select_backbone_utility
