"""Affine interval lenses in one shared extent/growth environment.

These maps reindex a cylinder; they do not compose arithmetic return actions.
In particular, two charts may be fused only when their extent and growth names
refer to the same environment. Temporal transport must supply that environment.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class CylinderChart:
    """The map i -> slope*i + offset + extent_scale*M + growth_scale*G."""

    slope: int = 1
    offset: int = 0
    extent_scale: int = 0
    growth_scale: int = 0

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (self.slope, self.offset, self.extent_scale, self.growth_scale)
        ):
            raise TypeError("cylinder chart coefficients must be exact integers")
        if self.slope not in (-1, 1):
            raise ValueError("cylinder chart slope must be -1 or 1")

    def then(self, after: CylinderChart) -> CylinderChart:
        """Compose index maps in the same M/G environment, first self then after."""
        self.__post_init__()
        if type(after) is not CylinderChart:
            raise TypeError("cylinder charts require a typed affine map")
        after.__post_init__()
        return CylinderChart(
            after.slope * self.slope,
            after.slope * self.offset + after.offset,
            after.slope * self.extent_scale + after.extent_scale,
            after.slope * self.growth_scale + after.growth_scale,
        )

    def shift(self, extent: int, growth: int) -> int:
        self.__post_init__()
        if type(extent) is not int or type(growth) is not int:
            raise TypeError("cylinder chart environment must contain exact integers")
        if extent < 0 or growth < 0:
            raise ValueError("cylinder extent and growth must be nonnegative")
        return self.offset + self.extent_scale * extent + self.growth_scale * growth

    def cartier_section(
        self, lane: int, *, extent: int, growth: int
    ) -> tuple[int, CylinderChart]:
        """Transport an even/odd coefficient section through this index map.

        If this chart is ``chi``, return ``(a, psi)`` such that
        ``chi(2*i + lane) = 2*psi(i) + a`` for every signed integer ``i``.
        Thus sectioning ``F(chi(i))`` selects lane ``a`` of ``F`` and then
        applies ``psi``. Python's floor division is essential at negative
        offsets and reflected coordinates.

        The returned chart is closed in the explicitly supplied M/G
        environment. This is coordinate transport only: it supplies neither
        a source section, a carry-prefix fold nor source/action admission.
        """
        if type(lane) is not int:
            raise TypeError("Cartier lane must be an exact integer")
        if lane not in (0, 1):
            raise ValueError("Cartier lane must be zero or one")
        quotient, source_lane = divmod(
            self.slope * lane + self.shift(extent, growth), 2
        )
        return source_lane, CylinderChart(self.slope, quotient)

    def image(self, start: int, stop: int, extent: int, growth: int) -> tuple[int, int]:
        """Image of [start, stop) as an ascending half-open integer interval.

        Orientation remains in slope. Signed coordinates are allowed; source
        admission, not this geometry operation, checks range containment.
        """
        if type(start) is not int or type(stop) is not int:
            raise TypeError("cylinder interval endpoints must be exact integers")
        if start > stop:
            raise ValueError("cylinder interval endpoints are reversed")
        shift = self.shift(extent, growth)
        if self.slope == 1:
            return start + shift, stop + shift
        return shift - stop + 1, shift - start + 1


def right_dyadic_blocks(start: int, stop: int) -> Iterator[tuple[int, int]]:
    """Yield the canonical dyadic cover of [start, stop), rightmost first.

    The number of iterations/fragments is logarithmic in the coordinate
    magnitude; each iteration uses integer arithmetic on those coordinates.
    No cell is visited by this geometric decomposition.
    """
    if type(start) is not int or type(stop) is not int:
        raise TypeError("dyadic interval endpoints must be exact integers")
    if not 0 <= start <= stop:
        raise ValueError("dyadic interval must be nonnegative and ordered")
    end = stop
    while end > start:
        remaining = end - start
        span = min(end & -end, 1 << (remaining.bit_length() - 1))
        end -= span
        yield end, span
