"""Bounded class-95 composition using the production F5 arithmetic owner.

Inputs are already discovered, output-aligned carrier words. This reference
does not admit source images or discover a right block from a left image.
Its callbacks deliberately count every scanned cell; finite rule counts are
not a complexity bound. Production handle composition uses F5AffineTransport
with ledger-owned arithmetic handles instead of these tuple callbacks.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field

from devtools.experiments.reverse_add.powered_f5f2_carrier import PoweredCocycleBlock
from number_compiler.arithmetic.polynomials.f5_transport import F5SpatialTransport


def split_class95(value: int) -> tuple[int, int]:
    if type(value) is not int or not 0 <= value < 95:
        raise ValueError("class95 requires an exact integer in 0..94")
    return divmod(value, 5)


@dataclass(slots=True)
class TransitionGrammarAudit:
    """Leaf work and rule diversity are intentionally separate measurements."""

    add_rules: Counter[tuple[int, int]] = field(default_factory=Counter)
    scale_rules: Counter[tuple[int, int]] = field(default_factory=Counter)
    attach_rules: Counter[tuple[int, int]] = field(default_factory=Counter)
    shift_passes: Counter[int] = field(default_factory=Counter)
    shifted_cells: int = 0
    decoded_cells: int = 0

    @property
    def added_cells(self) -> int:
        return self.add_rules.total()

    @property
    def scaled_cells(self) -> int:
        return self.scale_rules.total()

    @property
    def attached_cells(self) -> int:
        return self.attach_rules.total()


def square_class95_words(
    left_classes: tuple[int, ...],
    right_classes: tuple[int, ...],
    right: PoweredCocycleBlock,
    *,
    audit: TransitionGrammarAudit | None = None,
) -> tuple[int, ...]:
    """Compose supplied observations without another decimal carry scan.

    The right word already supplies the output carrier. Width checks catch
    misalignment but do not authenticate its source. This is not a scheduler
    publication interface, and passing it arbitrary words proves no trajectory.
    """
    if right.no_growths < 1:
        raise ValueError("class95 requires an annihilated homogeneous F2 source")
    if (
        len(left_classes) != right.source_width
        or len(right_classes) != right.target_width
        or right.target_width != right.source_width + right.growths
    ):
        raise ValueError("carrier words have mismatched input/output extents")
    left = tuple(split_class95(value)[1] for value in left_classes)
    right_parts = tuple(split_class95(value) for value in right_classes)
    if audit is None:
        audit = TransitionGrammarAudit()
    audit.decoded_cells += len(left) + len(right_parts)
    width = len(right_parts)
    source = left + (0,) * (width - len(left))

    def shift(values: tuple[int, ...], distance: int) -> tuple[int, ...]:
        audit.shift_passes[distance] += 1
        audit.shifted_cells += width
        if distance >= width:
            return (0,) * width
        return (0,) * distance + values[: width - distance]

    def add(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
        pairs = tuple(zip(a, b, strict=True))
        audit.add_rules.update(pairs)
        return tuple((x + y) % 5 for x, y in pairs)

    def scale(values: tuple[int, ...], scalar: int) -> tuple[int, ...]:
        audit.scale_rules.update((scalar, value) for value in values)
        return tuple(scalar * value % 5 for value in values)

    # One canonical Frobenius factorization: no copied polynomial/power loop.
    forcing = F5SpatialTransport(
        right.no_growths, right.growths
    ).apply_with_output_forcing(
        source,
        tuple(value for _, value in right_parts),
        shift=shift,
        add=add,
        scale=scale,
    )
    attached = tuple(
        (carrier, value)
        for (carrier, _), value in zip(right_parts, forcing, strict=True)
    )
    audit.attach_rules.update(attached)
    return tuple(5 * carrier + value for carrier, value in attached)
