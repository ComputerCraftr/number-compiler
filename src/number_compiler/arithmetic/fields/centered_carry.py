"""Exact symbolic arithmetic for the centered decimal pair-field clock.

The temporal residual is the *whole* polynomial Delta = P - 9 E_m.  A
first-reset tail is a spatial decomposition of Delta, not a replacement for
that temporal state.  These operations use the existing innovation arena;
they neither discover carries nor grant source/successor admission.  In
particular, a supplied beta or growth bit is not a checked clock extraction.
"""

from __future__ import annotations

from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.fields.radial_innovation import (
    InnovationID,
    RadialMultiplier,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.metric_keys import (
    arithmetic_fields as _fields_keys,
)


def _extent(extent: int) -> None:
    if type(extent) is not int:
        raise TypeError("centered clock extent must be an exact integer")
    if extent < 1:
        raise ValueError("centered clock extent must be positive")


def _growth(growth: int) -> None:
    if type(growth) is not int:
        raise TypeError("centered clock growth must be an exact integer")
    if growth not in (0, 1):
        raise ValueError("centered clock growth must be zero or one")


def center_pair_field(
    arena: SymbolicInnovationArena, pair: InnovationID, *, extent: int
) -> InnovationID:
    """Construct P - 9 E_m, with zero coefficients outside the finite window."""
    _extent(extent)
    arena.resolve(pair)
    return arena.linear_combination(((1, pair), (-9, arena.interval(extent))))


def uncenter_pair_field(
    arena: SymbolicInnovationArena, residual: InnovationID, *, extent: int
) -> InnovationID:
    """Construct Delta + 9 E_m; this does not establish digit-pair admission."""
    _extent(extent)
    arena.resolve(residual)
    return arena.linear_combination(((1, residual), (9, arena.interval(extent))))


def carry_coboundary(
    arena: SymbolicInnovationArena, outgoing: InnovationID, *, base: int
) -> InnovationID:
    """Construct (z-base)Q using the same coordinate convention as the publisher."""
    if type(base) is not int:
        raise TypeError("carry coboundary base must be an exact integer")
    if base < 2:
        raise ValueError("carry coboundary base must be at least two")
    arena.resolve(outgoing)
    shifted = arena.chart(outgoing, CylinderChart(1, -1))
    return arena.linear_combination(((1, shifted), (-base, outgoing)))


def reflected_innovation(
    arena: SymbolicInnovationArena,
    correction: InnovationID,
    *,
    extent: int,
    growth: int,
) -> InnovationID:
    """Construct beta = correction + R_(m+g-1) correction.

    Reflection uses the output extent; it is not a reversed physical carry.
    """
    _extent(extent)
    _growth(growth)
    arena.resolve(correction)
    reflected = arena.chart(correction, CylinderChart(-1, extent + growth - 1))
    return arena.add(correction, reflected)


def advance_centered_residual(
    arena: SymbolicInnovationArena,
    residual: InnovationID,
    innovation: InnovationID,
    *,
    extent: int,
    growth: int,
) -> InnovationID:
    """Construct M_g Delta + beta + 9(M_g E_m - E_(m+g)).

    Each branch uses a constant number of arena operations, independent of
    extent.  This bound excludes discovering Q, g and beta from Delta.  The
    caller must establish their source-bound relationship before publishing
    any successor; this function cannot turn supplied evidence into admission.
    """
    _extent(extent)
    _growth(growth)
    # Reject foreign/stale operands before allocating any new arithmetic node.
    arena.resolve(residual)
    arena.resolve(innovation)
    if growth == 0:
        radial = arena.radial(residual, RadialMultiplier(1, 0))
        window = arena.interval(extent)
    else:
        radial = arena.radial(residual, RadialMultiplier(0, 1))
        window = arena.chart(arena.interval(extent - 1), CylinderChart(1, -1))
    arena.ledger.bump(_fields_keys.CENTERED_CARRY_ALGEBRA_ADVANCE_ATTEMPTS)
    return arena.linear_combination(((1, radial), (1, innovation), (9, window)))
