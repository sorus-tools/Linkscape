"""
Graph Math Library for TerraLink
--------------------------------
Provides core graph-theoretic calculations for summary metrics such as entropy,
robustness, and redundancy.
"""

import math
import random
import numpy as np
from typing import Dict, List, Tuple, Sequence, Optional

from . import terralink_graph as nx

def build_graph_from_corridors(patches: Dict[int, Dict], corridors: List[Dict]) -> nx.Graph:
    """Helper to convert TerraLink patches/corridors to a NetworkX graph."""
    G = nx.Graph()
    for pid in patches:
        G.add_node(pid)
    
    for c in corridors:
        p1, p2 = c['patch1'], c['patch2']
        # Use distance if available, otherwise estimate from area (sqrt) or generic 1.0
        dist = c.get('distance_m', 1.0)
        G.add_edge(p1, p2, weight=dist, distance=dist, id=c.get('id'))
    return G

# --- ENTROPY CALCULATIONS ---

def calculate_movement_entropy(G: nx.Graph, alpha: float = 0.002) -> float:
    """
    Calculate movement entropy H_mov based on dispersal kernel.
    H_mov = -Σ p_i log(p_i)
    """
    H_total = 0.0
    n = G.number_of_nodes()
    if n == 0: return 0.0

    for node in G.nodes():
        neighbors = list(G.neighbors(node))
        if not neighbors:
            continue
            
        probs = []
        for nbr in neighbors:
            d = G[node][nbr].get('distance', 1.0)
            # Simplified dispersal kernel: exp(-alpha * distance)
            p = math.exp(-alpha * d)
            probs.append(p)
        
        # Normalize probabilities
        prob_sum = sum(probs)
        if prob_sum > 0:
            norm_probs = [p / prob_sum for p in probs]
            # Shannon entropy for this node
            H_i = -sum(p * math.log(p + 1e-10) for p in norm_probs)
            H_total += H_i

    return H_total / n

def calculate_topology_penalty(G: nx.Graph) -> float:
    """
    F(L): Penalizes deviation from dendritic (tree) structure.
    Returns number of cycles (extra edges beyond MST).
    """
    if G.number_of_nodes() == 0: return 0.0
    
    n_edges = G.number_of_edges()
    n_nodes = G.number_of_nodes()
    n_components = nx.number_connected_components(G)
    
    # For a forest (collection of trees), edges = nodes - components
    # Any excess edges imply cycles
    min_edges_needed = n_nodes - n_components
    cycles = max(0, n_edges - min_edges_needed)
    return float(cycles)

def calculate_disturbance_penalty(G: nx.Graph) -> float:
    """
    D(L): Penalizes long disturbance response times (diameter).
    Normalized by network size.
    """
    n = G.number_of_nodes()
    if n < 2: return 0.0
    
    if nx.is_connected(G):
        # Calculate diameter (longest shortest path)
        try:
            d = nx.diameter(G)
            return d / n
        except Exception:
            return 1.0
    else:
        # Penalize disconnection
        return 1.0

def calculate_total_entropy(G: nx.Graph, 
                          lambda_c: float = 1.0, 
                          lambda_f: float = 1.0, 
                          lambda_d: float = 1.0) -> Dict[str, float]:
    """Aggregate entropy metrics."""
    h_mov = calculate_movement_entropy(G)
    
    # Connectivity Constraint C(L): Simplified as number of components penalty
    n_comp = nx.number_connected_components(G)
    c_val = float(n_comp - 1) if n_comp > 0 else 0.0
    
    f_val = calculate_topology_penalty(G)
    d_val = calculate_disturbance_penalty(G)
    
    h_total = h_mov + (lambda_c * c_val) + (lambda_f * f_val) + (lambda_d * d_val)
    
    return {
        "H_total": h_total,
        "H_mov": h_mov,
        "C_connectivity": c_val,
        "F_topology": f_val,
        "D_disturbance": d_val
    }

# --- ROBUSTNESS CALCULATIONS ---

def calculate_two_edge_connectivity(G: nx.Graph) -> float:
    """
    Calculate rho_2: Fraction of node pairs with 2 edge-disjoint paths.
    Using a sampling approach for performance on large graphs, or full calculation for small ones.
    """
    n = G.number_of_nodes()
    if n < 3: return 0.0
    
    # For performance, we calculate the size of the 2-edge-connected components
    # This is a good proxy for rho_2 and much faster than all-pairs checks
    
    try:
        # k_edge_components returns sets of nodes in each 2-edge-connected component
        components = list(nx.k_edge_components(G, k=2))
        
        # Count pairs within these components
        two_connected_pairs = 0
        for comp in components:
            size = len(comp)
            two_connected_pairs += size * (size - 1) // 2
            
        total_pairs = n * (n - 1) // 2
        return two_connected_pairs / total_pairs if total_pairs > 0 else 0.0
    except Exception:
        return 0.0

def calculate_failure_probability(G: nx.Graph, k_failures: int = 1, iterations: int = 100) -> float:
    """
    Estimate P_fail(k): Probability that removing k edges disconnects the graph.
    Monte Carlo simulation.
    """
    edges = list(G.edges())
    m = len(edges)
    if m <= k_failures: return 1.0
    
    failures = 0
    for _ in range(iterations):
        # Randomly remove k edges
        G_test = G.copy()
        remove_indices = np.random.choice(m, k_failures, replace=False)
        for idx in remove_indices:
            G_test.remove_edge(*edges[idx])
            
        if not nx.is_connected(G_test) and nx.number_connected_components(G_test) > nx.number_connected_components(G):
             failures += 1
             
    return failures / iterations

def score_edge_for_loops(G_base: nx.Graph, u, v, weight) -> float:
    """
    Score a potential loop edge based on Betweenness Centrality Reduction.
    Higher score = better candidate for strategic redundancy.
    """
    # Simple heuristic: Connect nodes that are far apart in the current tree
    # This reduces diameter and provides shortcuts (high betweenness reduction)
    try:
        path_len = nx.shortest_path_length(G_base, u, v, weight='weight')
        # Score is path length in tree (shortcut value) divided by cost of new edge
        w = max(float(weight or 0.0), 1e-9)
        return float(path_len) / w
    except nx.NetworkXNoPath:
        return 0.0

# --- OPTIMIZATION METRICS ---

def calculate_effective_resistance(G: nx.Graph, weight_attr: str = 'weight') -> float:
    """
    Calculate a metric inversely proportional to the sum of effective resistances.
    We return an inverse of the total effective resistance to represent "C", which we want to maximize.
    """
    if not nx.is_connected(G):
        return 0.0
    n = G.number_of_nodes()
    if n < 2:
        return 0.0

    try:
        L = nx.laplacian_matrix(G, weight=weight_attr).toarray()
        L_pinv = np.linalg.pinv(L)
        # The sum of all pairwise effective resistances is n * trace(L_pinv)
        total_R = n * np.trace(L_pinv)
        if total_R > 0:
            return 1.0 / total_R
        return 0.0
    except Exception:
        return 0.0


def sample_spatially_separated_pairs(
    coords_xy: Dict[int, Tuple[float, float]],
    pair_count: int = 300,
    seed: int = 41,
) -> List[Tuple[int, int, float]]:
    """
    Deterministically sample node pairs, biased toward larger Euclidean separation.
    Returns tuples: (u, v, euclidean_distance).
    """
    nodes = sorted(int(n) for n in coords_xy.keys())
    if len(nodes) < 2:
        return []

    all_pairs: List[Tuple[int, int, float]] = []
    for i in range(len(nodes)):
        u = int(nodes[i])
        x1, y1 = coords_xy[u]
        for j in range(i + 1, len(nodes)):
            v = int(nodes[j])
            x2, y2 = coords_xy[v]
            d = float(math.hypot(float(x1) - float(x2), float(y1) - float(y2)))
            all_pairs.append((u, v, d))
    if not all_pairs:
        return []

    target = max(1, min(int(pair_count), len(all_pairs)))
    if target >= len(all_pairs):
        return sorted(all_pairs, key=lambda t: (-float(t[2]), int(t[0]), int(t[1])))

    ranked = sorted(all_pairs, key=lambda t: (-float(t[2]), int(t[0]), int(t[1])))
    pool_size = min(len(ranked), max(target, target * 4))
    pool = ranked[:pool_size]

    rng = random.Random(int(seed))  # nosec
    selected: List[Tuple[int, int, float]] = []
    work = list(pool)
    while work and len(selected) < target:
        total_w = float(sum(max(float(d), 1e-9) for _, _, d in work))
        if total_w <= 0.0:
            idx = int(rng.randrange(0, len(work)))
        else:
            r = float(rng.random() * total_w)
            acc = 0.0
            idx = len(work) - 1
            for k, (_u, _v, d) in enumerate(work):
                acc += max(float(d), 1e-9)
                if acc >= r:
                    idx = int(k)
                    break
        selected.append(work.pop(idx))

    selected.sort(key=lambda t: (int(t[0]), int(t[1])))
    return selected


def mean_effective_resistance_sampled(
    G: nx.Graph,
    sampled_pairs: Sequence[Tuple[int, int, float]],
    cost_attr: str = "weight",
    disconnected_penalty: Optional[float] = None,
    patch_sizes: Optional[Dict[int, float]] = None,
    total_habitat_area: Optional[float] = None,
    disconnected_penalty_scale_fn=None,
) -> float:
    """
    Mean effective resistance across sampled node pairs.
    For disconnected pairs, a deterministic finite penalty is used.
    """
    if not sampled_pairs:
        return 0.0
    if G.number_of_nodes() <= 0:
        return float(disconnected_penalty or 1.0)

    pair_max_eu = max((max(float(p[2]), 0.0) for p in sampled_pairs), default=1.0)
    penalty = float(disconnected_penalty) if disconnected_penalty is not None else max(1.0, pair_max_eu * 20.0)

    comp_index: Dict[int, int] = {}
    components = [sorted(int(n) for n in comp) for comp in nx.connected_components(G)]
    for cidx, comp in enumerate(components):
        for n in comp:
            comp_index[int(n)] = int(cidx)

    pinv_by_comp: Dict[int, Tuple[np.ndarray, Dict[int, int]]] = {}
    for cidx, comp in enumerate(components):
        if len(comp) < 2:
            continue
        idx_map = {int(node): i for i, node in enumerate(comp)}
        n_local = len(comp)
        A = np.zeros((n_local, n_local), dtype=float)
        for i, u in enumerate(comp):
            for j in range(i + 1, n_local):
                v = comp[j]
                if not G.has_edge(int(u), int(v)):
                    continue
                try:
                    cost = float(G[int(u)][int(v)].get(cost_attr, G[int(u)][int(v)].get("weight", 1.0)) or 1.0)
                except Exception:
                    cost = 1.0
                cost = max(cost, 1e-9)
                conductance = 1.0 / cost
                A[i, j] += conductance
                A[j, i] += conductance
        L = np.diag(np.sum(A, axis=1)) - A
        try:
            L_pinv = np.linalg.pinv(L)
        except Exception:  # nosec
            continue
        pinv_by_comp[int(cidx)] = (L_pinv, idx_map)

    total = 0.0
    n_pairs = 0
    for u, v, _eu in sampled_pairs:
        iu = int(u)
        iv = int(v)
        if iu == iv:
            continue
        cu = comp_index.get(iu, -1)
        cv = comp_index.get(iv, -1)
        pair_penalty = penalty
        if disconnected_penalty_scale_fn is not None and patch_sizes is not None and total_habitat_area is not None:
            try:
                pair_penalty = float(
                    disconnected_penalty_scale_fn(
                        penalty,
                        float(patch_sizes.get(iu, 1.0) or 1.0),
                        float(patch_sizes.get(iv, 1.0) or 1.0),
                        float(total_habitat_area or 1.0),
                    )
                )
            except Exception:
                pair_penalty = penalty
        if cu < 0 or cv < 0 or cu != cv:
            total += pair_penalty
            n_pairs += 1
            continue
        pinv_rec = pinv_by_comp.get(int(cu))
        if pinv_rec is None:
            total += pair_penalty
            n_pairs += 1
            continue
        L_pinv, idx_map = pinv_rec
        i = idx_map.get(iu)
        j = idx_map.get(iv)
        if i is None or j is None:
            total += pair_penalty
            n_pairs += 1
            continue
        rij = float(L_pinv[i, i] + L_pinv[j, j] - (2.0 * L_pinv[i, j]))
        if (not np.isfinite(rij)) or rij < 0.0:
            rij = pair_penalty
        total += float(rij)
        n_pairs += 1

    if n_pairs <= 0:
        return penalty
    return float(total / float(n_pairs))


def weighted_mean_effective_resistance_sampled(
    G: nx.Graph,
    sampled_pairs: Sequence[Tuple[int, int, float]],
    pair_weights: Dict[Tuple[int, int], float],
    cost_attr: str = "weight",
    disconnected_penalty: Optional[float] = None,
    patch_sizes: Optional[Dict[int, float]] = None,
    total_habitat_area: Optional[float] = None,
    disconnected_penalty_scale_fn=None,
) -> float:
    """
    Weighted mean effective resistance across sampled node pairs.
    `pair_weights` keys are normalized (min(u,v), max(u,v)).
    """
    if not sampled_pairs:
        return 0.0
    if G.number_of_nodes() <= 0:
        return float(disconnected_penalty or 1.0)

    pair_max_eu = max((max(float(p[2]), 0.0) for p in sampled_pairs), default=1.0)
    penalty = float(disconnected_penalty) if disconnected_penalty is not None else max(1.0, pair_max_eu * 20.0)

    comp_index: Dict[int, int] = {}
    components = [sorted(int(n) for n in comp) for comp in nx.connected_components(G)]
    for cidx, comp in enumerate(components):
        for n in comp:
            comp_index[int(n)] = int(cidx)

    pinv_by_comp: Dict[int, Tuple[np.ndarray, Dict[int, int]]] = {}
    for cidx, comp in enumerate(components):
        if len(comp) < 2:
            continue
        idx_map = {int(node): i for i, node in enumerate(comp)}
        n_local = len(comp)
        A = np.zeros((n_local, n_local), dtype=float)
        for i, u in enumerate(comp):
            for j in range(i + 1, n_local):
                v = comp[j]
                if not G.has_edge(int(u), int(v)):
                    continue
                try:
                    cost = float(G[int(u)][int(v)].get(cost_attr, G[int(u)][int(v)].get("weight", 1.0)) or 1.0)
                except Exception:
                    cost = 1.0
                cost = max(cost, 1e-9)
                conductance = 1.0 / cost
                A[i, j] += conductance
                A[j, i] += conductance
        L = np.diag(np.sum(A, axis=1)) - A
        try:
            L_pinv = np.linalg.pinv(L)
        except Exception:  # nosec
            continue
        pinv_by_comp[int(cidx)] = (L_pinv, idx_map)

    weighted_total = 0.0
    weight_sum = 0.0
    for u, v, _eu in sampled_pairs:
        iu = int(u)
        iv = int(v)
        if iu == iv:
            continue
        a, b = (iu, iv) if iu < iv else (iv, iu)
        w_pair = float(pair_weights.get((int(a), int(b)), 0.0) or 0.0)
        if w_pair <= 0.0:
            continue
        cu = comp_index.get(iu, -1)
        cv = comp_index.get(iv, -1)
        pair_penalty = penalty
        if disconnected_penalty_scale_fn is not None and patch_sizes is not None and total_habitat_area is not None:
            try:
                pair_penalty = float(
                    disconnected_penalty_scale_fn(
                        penalty,
                        float(patch_sizes.get(iu, 1.0) or 1.0),
                        float(patch_sizes.get(iv, 1.0) or 1.0),
                        float(total_habitat_area or 1.0),
                    )
                )
            except Exception:
                pair_penalty = penalty
        if cu < 0 or cv < 0 or cu != cv:
            weighted_total += w_pair * pair_penalty
            weight_sum += w_pair
            continue
        pinv_rec = pinv_by_comp.get(int(cu))
        if pinv_rec is None:
            weighted_total += w_pair * pair_penalty
            weight_sum += w_pair
            continue
        L_pinv, idx_map = pinv_rec
        i = idx_map.get(iu)
        j = idx_map.get(iv)
        if i is None or j is None:
            weighted_total += w_pair * pair_penalty
            weight_sum += w_pair
            continue
        rij = float(L_pinv[i, i] + L_pinv[j, j] - (2.0 * L_pinv[i, j]))
        if (not np.isfinite(rij)) or rij < 0.0:
            rij = pair_penalty
        weighted_total += w_pair * float(rij)
        weight_sum += w_pair

    if weight_sum <= 0.0:
        return penalty
    return float(weighted_total / weight_sum)

def calculate_algebraic_connectivity(G: nx.Graph, weight_attr: str = 'weight') -> float:
    """
    Calculate lambda_2 (Fiedler value) of the Laplacian.
    Maximizing this makes the network more globally connected.
    """
    if G.number_of_nodes() < 2:
        return 0.0
    if not nx.is_connected(G):
        return 0.0
    try:
        # The local graph backend provides an algebraic_connectivity helper.
        lambda_2 = nx.algebraic_connectivity(G, weight=weight_attr, method='tracemin_pcg')
        return float(lambda_2)
    except Exception:
        try:
            L = nx.laplacian_matrix(G, weight=weight_attr).toarray()
            evals = np.linalg.eigvalsh(L)
            if len(evals) > 1:
                return float(evals[1])
            return 0.0
        except Exception:
            return 0.0

def calculate_probability_of_connectivity(G: nx.Graph, patches: Dict[int, Dict], alpha: float = 0.002, weight_attr: str = 'weight') -> float:
    """
    PC = Sum over i < j (a_i * a_j * p_ij)
    where p_ij = exp(-alpha * d_ij)
    """
    if G.number_of_nodes() < 2:
        return 0.0
    
    components = list(nx.connected_components(G))
    pc_total = 0.0
    
    for comp in components:
        subG = G.subgraph(comp)
        try:
            lengths = dict(nx.shortest_path_length(subG, weight=weight_attr))
            for u in comp:
                a_u = float(patches.get(u, {}).get("area_ha", 1.0) or 1.0)
                for v in comp:
                    if u < v:
                        a_v = float(patches.get(v, {}).get("area_ha", 1.0) or 1.0)
                        d_uv = lengths.get(u, {}).get(v, float('inf'))
                        if d_uv != float('inf'):
                            p_uv = math.exp(-alpha * d_uv)
                            pc_total += a_u * a_v * p_uv
        except Exception:  # nosec
            pass
            
    return pc_total

def calculate_wmr(G: nx.Graph, gamma: float = 0.1, delta: float = 0.5) -> float:
    """
    Composite Metric WMR.
    WMR = C * (1 + gamma * AltPaths) * (1 - delta * Fragility)
    """
    if G.number_of_nodes() < 2:
        return 0.0
    
    C = calculate_effective_resistance(G)
    if C == 0.0:
        return 0.0
        
    alt_paths = calculate_two_edge_connectivity(G)
    fragility = calculate_failure_probability(G, k_failures=1, iterations=20)
    
    wmr = C * (1.0 + gamma * alt_paths) * (1.0 - delta * fragility)
    return wmr
