"""Source boundary phases and the shared physical growth clock for 2rev10."""

from __future__ import annotations


def outer_digits(phase: int) -> tuple[int, int]:
    """Return the leading and units digits of a protected outer phase."""
    if type(phase) is not int or not 0 <= phase < 4:
        raise ValueError("invalid 2rev10 border phase")
    return (1 if phase < 2 else 4, 8 if phase in (0, 3) else 2)


def edge_phase(upper: tuple[int, int], lower: tuple[int, int]) -> int | None:
    """Classify a source by its exact two digit borders."""
    if upper == (1, 7):
        if lower == (4, 2):
            return 1
        if lower in ((6, 8), (8, 8)):
            return 0
    elif upper in ((4, 8), (4, 9)):
        if lower == (4, 2):
            return 2
        if lower in ((6, 8), (8, 8)):
            return 3
    return None


def edge_phase_of_integer(value: int) -> int | None:
    """Classify the actual outer digit pairs of one exact integer source."""
    if type(value) is not int or value < 0:
        raise ValueError("border phase requires a nonnegative exact integer")
    if value < 1000:
        return None
    lower_pair = value % 100
    upper_prefix = value // 100
    while upper_prefix >= 100:
        upper_prefix //= 10
    return edge_phase(divmod(upper_prefix, 10), divmod(lower_pair, 10))


def growth_ports(phase: int, steps: int) -> tuple[int, int]:
    """Return exact left/right cell births after ``steps`` applications of F."""
    if type(phase) is not int or phase not in (0, 1, 2, 3):
        raise ValueError("invalid 2rev10 border phase")
    if type(steps) is not int or steps < 0:
        raise ValueError("2rev10 F-step count must be nonnegative")
    low = steps // 2
    high = (steps + 1) // 2
    return (
        high if phase in (2, 3) else low,
        high if phase in (0, 3) else low,
    )


# The physical events are right, left, right, left in two consecutive F=T²
# steps. Derive them from the authenticated boundary-port action.
PHYSICAL_GROWTH_CYCLES: tuple[tuple[int, int, int, int], ...] = tuple(
    (
        growth_ports(phase, 1)[1],
        growth_ports(phase, 1)[0],
        growth_ports((phase + 2) % 4, 1)[1],
        growth_ports((phase + 2) % 4, 1)[0],
    )
    for phase in range(4)
)


def advance_residue_clock(
    phase: int, width_parity: int, residue: int, modulus: int = 99
) -> tuple[int, int, int]:
    """Apply one step of the authenticated four-phase decimal width clock."""
    if type(modulus) is not int or modulus not in (99, 198):
        raise ValueError("source-closed scalar quotient is modulo 99 or 198")
    if (
        type(phase) is not int
        or phase not in range(4)
        or type(width_parity) is not int
        or width_parity not in (0, 1)
        or type(residue) is not int
        or not 0 <= residue < modulus
    ):
        raise ValueError("invalid source-issued residue-clock state")
    return (
        (phase + 1) % 4,
        (width_parity + PHYSICAL_GROWTH_CYCLES[phase][0]) % 2,
        (residue * (2 if width_parity else 20)) % modulus,
    )


__all__ = [
    "PHYSICAL_GROWTH_CYCLES",
    "advance_residue_clock",
    "edge_phase",
    "edge_phase_of_integer",
    "growth_ports",
    "outer_digits",
]
