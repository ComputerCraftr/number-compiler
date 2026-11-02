"""Bounded ordered prefix-rank actions for authenticated prime sources."""

from __future__ import annotations

from collections.abc import Iterable, Iterator
from dataclasses import dataclass

ORDERED_WHEEL_210_TERMS: tuple[tuple[int, int], ...] = (
    (1, 1),
    (2, -1),
    (3, -1),
    (5, -1),
    (7, -1),
    (6, 1),
    (10, 1),
    (14, 1),
    (15, 1),
    (21, 1),
    (35, 1),
    (30, -1),
    (42, -1),
    (70, -1),
    (105, -1),
    (210, 1),
)

_FACTORS_210 = (2, 3, 5, 7)
_BOUNDARY_LENGTH = 2310
_BOUNDARY_SURVIVORS = 480
_BOUNDARY_CHUNKS = 37
ORDERED_BOUNDARY_NODE_COST = 125
MAX_SUFFIX_FACTORS = 4


@dataclass(frozen=True, slots=True)
class OrderedRankBoundary2310:
    """Pure fixed boundary data; it does not carry source or phase authority.

    The production DAG admits this conditional action only after validating its
    own consecutive ``(2, 3, 5, 7, 11)`` source prefix. Constructing this value
    directly is useful for arithmetic tests but does not issue that authority.
    """

    chunks: tuple[int, ...]
    cumulative: tuple[int, ...]

    def __post_init__(self) -> None:
        if (
            type(self.chunks) is not tuple
            or len(self.chunks) != _BOUNDARY_CHUNKS
            or type(self.cumulative) is not tuple
            or len(self.cumulative) != _BOUNDARY_CHUNKS + 1
            or type(self.cumulative[0]) is not int
            or self.cumulative[0] != 0
        ):
            raise ValueError("ordered 2310-period boundary has an invalid shape")
        total = 0
        for index, chunk in enumerate(self.chunks):
            if type(chunk) is not int or not 0 <= chunk < 1 << 64:
                raise ValueError("ordered 2310-period boundary has an invalid chunk")
            if type(self.cumulative[index + 1]) is not int:
                raise ValueError("ordered 2310-period boundary has invalid ranks")
            total += chunk.bit_count()
            if self.cumulative[index + 1] != total:
                raise ValueError("ordered 2310-period boundary ranks disagree")
        if self.chunks[-1] >> 6 or total != _BOUNDARY_SURVIVORS:
            raise ValueError("ordered 2310-period boundary has an invalid endpoint")

    @classmethod
    def build(cls) -> OrderedRankBoundary2310:
        """Build the fixed 210-to-2310 boundary without extending parent wheels.

        The caller owns resource reservation and source admission. This helper
        only constructs the small immutable mathematical action.
        """
        residues = tuple(
            candidate
            for candidate in range(1, 211)
            if all(candidate % factor for factor in _FACTORS_210)
        )
        if len(residues) != 48:
            raise RuntimeError("fixed 210-period boundary is malformed")
        chunks = [0] * _BOUNDARY_CHUNKS
        for copy in range(11):
            for residue in residues:
                position = copy * 210 + residue
                if position % 11:
                    index = position - 1
                    chunks[index >> 6] |= 1 << (index & 63)
        cumulative = [0]
        for chunk in chunks:
            cumulative.append(cumulative[-1] + chunk.bit_count())
        if cumulative[-1] != _BOUNDARY_SURVIVORS:
            raise RuntimeError("fixed 2310-period boundary is malformed")
        return cls(tuple(chunks), tuple(cumulative))

    def rank(self, limit: int) -> int:
        """Count positive source positions ``<= limit`` in the boundary."""
        if type(limit) is not int:
            raise TypeError("ordered rank limit must be an exact integer")
        if limit < 1:
            return 0
        full, remainder = divmod(limit, _BOUNDARY_LENGTH)
        block, bits = divmod(remainder, 64)
        prefix = self.cumulative[block]
        if bits:
            prefix += (self.chunks[block] & ((1 << bits) - 1)).bit_count()
        return full * _BOUNDARY_SURVIVORS + prefix


class OrderedRankBoundaryStore:
    """Node-only resource container for one immutable boundary action."""

    __slots__ = ("_boundary",)

    def __init__(self) -> None:
        self._boundary: OrderedRankBoundary2310 | None = None

    def __len__(self) -> int:
        # The boundary is a fixed action payload, not a recurrence state.
        return 0

    def node_count(self) -> int:
        return ORDERED_BOUNDARY_NODE_COST if self._boundary is not None else 0

    def payloads(self) -> Iterator[object]:
        boundary = self._boundary
        if boundary is not None:
            yield boundary

    @property
    def boundary(self) -> OrderedRankBoundary2310 | None:
        return self._boundary

    def publish(self, boundary: OrderedRankBoundary2310) -> None:
        if type(boundary) is not OrderedRankBoundary2310 or self._boundary is not None:
            raise RuntimeError("ordered boundary store is already occupied")
        self._boundary = boundary

    def clear(self) -> bool:
        if self._boundary is None:
            return False
        self._boundary = None
        return True


def ordered_cyclotomic_suffix_rank(
    limit: int,
    boundary: OrderedRankBoundary2310,
    suffix_factors: Iterable[int],
) -> int:
    """Apply exact signed zero-phase pullbacks to the fixed boundary.

    This function is called inside the caller's bounded scratch reservation.
    The suffix is intentionally limited to four factors, so the temporary
    inclusion-exclusion packet contains at most sixteen terms. It is a pure
    arithmetic action: callers must separately authenticate the ordered
    factor source before treating its result as a prime rank.
    """
    if type(limit) is not int or limit < 0:
        raise ValueError("ordered suffix rank limit must be a nonnegative integer")
    if type(boundary) is not OrderedRankBoundary2310:
        raise TypeError("ordered suffix rank requires its boundary owner")
    terms: list[tuple[int, int]] = [(1, 1)]
    suffix_length = 0
    for factor in suffix_factors:
        if type(factor) is not int or factor < 2:
            raise ValueError("ordered suffix factors must be exact integers >= 2")
        suffix_length += 1
        if suffix_length > MAX_SUFFIX_FACTORS:
            raise ValueError("ordered suffix exceeds its bounded packet capacity")
        prior_terms = tuple(terms)
        terms.extend((divisor * factor, -sign) for divisor, sign in prior_terms)
    result = sum(sign * boundary.rank(limit // divisor) for divisor, sign in terms)
    if not 0 <= result <= limit:
        raise RuntimeError("ordered prime rank produced an invalid result")
    return result


__all__ = (
    "MAX_SUFFIX_FACTORS",
    "ORDERED_BOUNDARY_NODE_COST",
    "ORDERED_WHEEL_210_TERMS",
    "OrderedRankBoundary2310",
    "OrderedRankBoundaryStore",
    "ordered_cyclotomic_suffix_rank",
)
