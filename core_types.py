from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, FrozenSet, Tuple


@dataclass(frozen=True)
class Patch:
    """Backend-agnostic patch metadata."""

    id: int
    weight: float


@dataclass
class Candidate:
    """
    Backend-agnostic corridor candidate.

    `path` and `overlap_repr` are intentionally `Any` so raster/vector can store their
    native representations (pixel sets, QgsGeometry, etc.) without importing backend libs.
    """

    patch_ids: FrozenSet[int]
    cost: float
    weight: float
    path: Any = None
    overlap_repr: Any = None
    meta: dict = field(default_factory=dict)

    @property
    def pair_key(self) -> Tuple[int, int]:
        ids = sorted(self.patch_ids)
        if len(ids) >= 2:
            return (int(ids[0]), int(ids[1]))
        if len(ids) == 1:
            return (int(ids[0]), int(ids[0]))
        return (0, 0)
