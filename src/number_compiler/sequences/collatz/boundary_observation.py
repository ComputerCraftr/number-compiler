"""Demanded observations of producer-authenticated physical boundary macros."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.boundary_macros import CollatzBoundaryMacro


def observe_guarded_boundary(
    seed: int,
    witness: tuple[int, CollatzBoundaryMacro] | None,
    modulus: int | None,
    ledger: ResourceLedger,
) -> dict[str, object]:
    """Use the issued macro directly; do not rediscover its source action."""
    require_integer(seed, "Collatz source", 1)
    ledger.bump("collatz_boundary_observation_requests")
    tick, macro = witness if witness is not None else (0, None)
    packet: dict[str, object] = {
        "scope": "first executed guarded macro; not a global endpoint ActionID",
        "executed_macro_actions": {
            family: ledger.counters.get(
                f"collatz_physical_boundary_{family}_macro_actions", 0
            )
            for family in ("421", "4721", "630", "989")
        },
        "source_prefix": macro.observation()
        if macro is not None and tick == 0
        else None,
        "first_executed_macro": (
            {"starting_physical_tick": tick, **macro.observation()}
            if macro is not None
            else None
        ),
    }
    if modulus is None:
        return packet
    from number_compiler.sequences.collatz.innovation_carry_cocycle import (
        CollatzInnovationCocycle,
    )

    source_modulus = 4 * modulus
    residue = seed % source_modulus
    ledger.bump(
        "collatz_innovation_source_operand_bits",
        seed.bit_length() + source_modulus.bit_length(),
    )
    source = CollatzInnovationCocycle(residue, source_modulus)
    operation, sign = source.operation()
    packet["source_second_innovation"] = {
        "source_residue": residue,
        "source_modulus": source_modulus,
        "operation": operation,
        "result_sign": sign,
        "event": "borrow" if operation == "sub" else "carry",
        "flag": source.kappa(modulus),
        "scope": "initial normalized source; no implied future closure",
    }
    if macro is None:
        packet.update(
            borrow_scope="no executed boundary witness is certified",
            borrow_clock_status="unresolved",
            status="partial",
        )
    else:
        from number_compiler.sequences.collatz.innovation_temporal_tape import (
            observed_innovation_macro_tape,
        )

        packet["normalized_temporal_tape"] = observed_innovation_macro_tape(
            macro, modulus, ledger=ledger
        )
    return packet
