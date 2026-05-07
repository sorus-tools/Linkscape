from enum import Enum
from typing import Dict, List, Set, Tuple, Optional


class StrategyType(str, Enum):
    # Canonical strategy keys (snake_case, matching UI labels).
    LARGEST_SINGLE_NETWORK = "largest_single_network"
    MOST_CONNECTED_NETWORKS = "most_connected_networks"
    MOST_CONNECTED_NETWORKS_2 = "most_connected_networks_2"
    LANDSCAPE_FLUIDITY = "landscape_fluidity"

    # Back-compat aliases for older saved projects/settings.
    LARGEST_NETWORK = "largest_single_network"
    LANDSCAPE_FLUIDITY_A = "landscape_fluidity"
    LANDSCAPE_FLUIDITY_A1 = "landscape_fluidity"


class UnionFind:
    """Optimized Union-Find data structure."""

    __slots__ = ("parent", "size", "count")

    def __init__(self):
        self.parent: Dict[int, int] = {}
        self.size: Dict[int, float] = {}
        self.count: Dict[int, int] = {}

    def find(self, x: int) -> int:
        """
        Iterative find with path compression; initializes unseen nodes with empty stats.
        """
        if x not in self.parent:
            self.parent[x] = x
            self.size[x] = 0.0
            self.count[x] = 0
            return x

        path: List[int] = [x]
        root = x
        while self.parent.get(root, root) != root:
            root = self.parent[root]
            path.append(root)

        for node in path:
            self.parent[node] = root

        return root

    def union(self, a: int, b: int) -> bool:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return False
        sa, sb = self.size.get(ra, 0.0), self.size.get(rb, 0.0)
        if sa < sb:
            ra, rb = rb, ra
            sa, sb = sb, sa
        self.parent[rb] = ra
        self.size[ra] = sa + sb
        self.count[ra] = self.count.get(ra, 0) + self.count.get(rb, 0)
        return True

    def get_size(self, x: int) -> float:
        return self.size.get(self.find(x), 0.0)

    def get_count(self, x: int) -> int:
        return self.count.get(self.find(x), 0)


class Edge:
    __slots__ = ("u", "v", "id", "cost")

    def __init__(self, u: int, v: int, eid: int, cost: float):
        self.u = u
        self.v = v
        self.id = eid
        self.cost = cost


class NetworkOptimizer:
    """
    Shared graph engine for corridor selection. Works on abstract nodes/edges only.
    Phase 1: build an MST backbone. Phase 2: spend leftover budget on short loops/branches.
    """

    def __init__(self, nodes: Dict[int, float]):
        self.nodes = nodes
        self.edges: List[Edge] = []
        self.uf = UnionFind()
        # Pre-seed UF maps for known nodes to avoid repeated dict hits
        for n, v in nodes.items():
            self.uf.parent[n] = n
            self.uf.size[n] = v
            self.uf.count[n] = 1

    def add_candidate(self, u: int, v: int, cand_id: int, cost: float) -> None:
        if u == v:
            return
        self.edges.append(Edge(u, v, cand_id, cost))

    def find(self, node: int) -> int:
        """Expose UF find for callers that need component ids (used by raster/vector stats)."""
        return self.uf.find(node)

    def solve(
        self,
        budget: float,
        loop_fraction: Optional[float] = 0.05,
        max_redundancy: int = 2,
    ) -> Tuple[Set[int], Dict[int, float], Dict[int, int], float]:
        selected: Set[int] = set()
        current_cost = 0.0
        edges_sorted = sorted(self.edges, key=lambda e: e.cost)

        # Phase 1: MST backbone
        for edge in edges_sorted:
            if current_cost + edge.cost > budget:
                break
            if self.uf.union(edge.u, edge.v):
                selected.add(edge.id)
                current_cost += edge.cost

        # Phase 2: short loops/branches if budget remains
        redundancy_count: Dict[int, int] = {}
        if current_cost < budget:
            loop_thresh = budget * loop_fraction if loop_fraction not in (None, 0) else None
            for edge in edges_sorted:
                if edge.id in selected:
                    continue
                remaining = budget - current_cost
                if edge.cost > remaining:
                    break
                # Optionally skip very expensive loops if user-provided fraction is tiny
                if loop_thresh is not None and edge.cost > loop_thresh:
                    continue

                root_u = self.uf.find(edge.u)
                root_v = self.uf.find(edge.v)
                if root_u == root_v:
                    count = redundancy_count.get(root_u, 0)
                    if count >= max_redundancy:
                        continue
                    redundancy_count[root_u] = count + 1
                # Add even if already connected to allow daisy-chaining/loops
                selected.add(edge.id)
                current_cost += edge.cost
                # Maintain union-find for bookkeeping (even if already connected)
                self.uf.union(edge.u, edge.v)

        # Normalize size/count to current roots
        final_sizes: Dict[int, float] = {}
        final_counts: Dict[int, int] = {}
        for node in self.nodes:
            root = self.uf.find(node)
            final_sizes[root] = self.uf.size.get(root, 0.0)
            final_counts[root] = self.uf.count.get(root, 1)

        return selected, final_sizes, final_counts, current_cost
