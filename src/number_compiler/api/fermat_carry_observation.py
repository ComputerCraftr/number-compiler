"""Explicit bounded ordered-carry demand; never a Fermat primality certificate."""

from __future__ import annotations

from dataclasses import asdict

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.ordered_tripling_carry import (
    OrderedTriplingCarry,
)


def fermat_carry_packet(index: int) -> dict[str, object]:
    """Observe the terminal tripling source through fixed bounded radix windows."""
    require_integer(index, "Fermat carry source index", 0, 16)
    level = (1 << index) - 1
    windows = []
    for base, position in ((2, 63), (5, 6), (7, 5), (10, 8), (10, 2)):
        program = OrderedTriplingCarry.at_dyadic_phase(base, position, level, 4)
        windows.append(
            {
                "radix": base,
                "position": position,
                "source_period": program.period,
                "phase": program.phase,
                "physical_ticks": program.duration,
                "ordered_carries": [asdict(program.sample(i)) for i in range(4)],
            }
        )
    return {
        "source": {"base": 3, "exponent": {"encoding": "power2", "exponent": level}},
        "windows": windows,
        "scope": "exact finite ordered physical-tripling carry projections",
        "full_binary_square_carry_cochain_certified": False,
        "primality_authority": False,
    }
