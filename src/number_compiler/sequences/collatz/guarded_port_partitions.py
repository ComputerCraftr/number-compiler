"""Source-pulled future partitions for authenticated Collatz port joins."""

from __future__ import annotations

from math import gcd

from number_compiler.sequences.collatz.border_identity import (
    CollatzSegmentIdentity,
    NonBorderSegment,
)
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.guarded_port_join import GuardedPortJoin
from number_compiler.sequences.collatz.guarded_port_source import (
    restrict_source,
)
from number_compiler.sequences.collatz.joint_radix_border import (
    candidate_family_for_residue160,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    SourceClosedPortAction,
    SourceCongruence,
)


def future_family_partition(
    joined: GuardedPortJoin,
) -> tuple[tuple[CollatzSegmentIdentity | None, CollatzTwoSidedCylinder], ...]:
    """Partition the original source by modulo-160 successor family.

    The family label is a candidate only; it does not authorize a new
    repetition count or valuation. Every partition is pulled back through the
    issued action to its original source cylinder.
    """
    target = joined.bridge.target
    period = 160 // gcd(160, target.modulus)
    count = min(target.count, period)
    result: list[tuple[CollatzSegmentIdentity | None, CollatzTwoSidedCylinder]] = []
    for i in range(count):
        residue = (target.first + i * target.modulus) % 160
        pulled = SourceCongruence(residue, 160).pullback(joined.port.action)
        guard = None if pulled is None else joined.port.guard.meet(pulled)
        root = None if guard is None else restrict_source(joined.source, guard)
        if root is not None:
            family: CollatzSegmentIdentity | None = candidate_family_for_residue160(
                residue
            )
            if family is None and residue % 2 == 0:
                family = NonBorderSegment.ZERO_RUN
            result.append((family, root))
    if sum(root.count for _, root in result) != joined.source.count:
        raise ArithmeticError("source-bound candidate partition lost alternatives")
    return tuple(result)


def future_border_partition(
    joined: GuardedPortJoin,
) -> tuple[tuple[int, GuardedPortJoin], ...]:
    """Partition all source alternatives by their next decimal border."""
    alternatives = tuple(
        (digit, part)
        for digit in range(10)
        if (part := joined.future_border(digit)) is not None
    )
    if sum(part.source.count for _, part in alternatives) != joined.source.count:
        raise ArithmeticError("joined future-border punctures lost alternatives")
    return alternatives


def future_tails(
    joined: GuardedPortJoin,
    *,
    max_tail: int = 12,
) -> tuple[tuple[int | None, GuardedPortJoin], ...]:
    """Pull the exact 3-border tail partition back to the source cylinder."""
    if type(max_tail) is not int or not 1 <= max_tail <= 64:
        raise ValueError("future border tail budget must be 1..64")
    if joined.bridge.target.forced_residue(10) != 3:
        raise ValueError("next 6305 tails require a forced 3-ending border")
    output: list[tuple[int | None, GuardedPortJoin]] = []
    for tail, target in joined.bridge.target.conditional_next_tails(max_tail=max_tail):
        pulled = SourceCongruence(target.residue, target.modulus).pullback(
            joined.port.action
        )
        if pulled is None:
            continue
        root_guard = joined.port.guard.meet(pulled)
        if root_guard is None:
            continue
        root = restrict_source(joined.source, root_guard)
        if root is None:
            continue
        image = root.transport(joined.port.action)
        if (image.first, image.last, image.count) != (
            target.first,
            target.last,
            target.count,
        ):
            raise ArithmeticError(
                "future tail inverse image lost an affine source fiber"
            )
        revised = SourceClosedPortAction(
            joined.port.action,
            root_guard,
            joined.port.odd_events,
            joined.port.clock,
            joined.port.trace,
        )
        bridge = joined.bridge.restrict_to(root)
        output.append(
            (
                tail,
                GuardedPortJoin(root, revised, bridge, parity_tape=joined._tape()),
            )
        )
    if sum(part.source.count for _, part in output) != joined.source.count:
        raise ArithmeticError("guarded future tail partition omitted a source")
    return tuple(output)


__all__ = [
    "future_border_partition",
    "future_family_partition",
    "future_tails",
]
