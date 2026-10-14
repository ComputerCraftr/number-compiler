"""Demanded observations of producer-authenticated physical boundary macros."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.boundary_macros import (
    boundary_macro_26847_phase,
)
from number_compiler.sequences.collatz.decimal_boundary import physical_boundary_packet

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.border_return_grammar import (
        BorderReturnMacro,
    )
    from number_compiler.sequences.collatz.boundary_macros import CollatzBoundaryMacro
    from number_compiler.sequences.collatz.innovation_port_moore import (
        InnovationTapeObservation,
    )


def observe_guarded_boundary(
    seed: int,
    witness: tuple[int, CollatzBoundaryMacro | BorderReturnMacro] | None,
    modulus: int | None,
    ledger: ResourceLedger,
    global_tape: InnovationTapeObservation | None = None,
) -> dict[str, object]:
    """Use the issued macro directly; do not rediscover its source action."""
    require_integer(seed, "Collatz source", 1)
    ledger.bump("collatz_boundary_observation_requests")
    if global_tape is not None:
        from number_compiler.sequences.collatz.innovation_port_moore import (
            InnovationTapeObservation,
        )

        if (
            type(global_tape) is not InnovationTapeObservation
            or not global_tape.producer_issued
            or global_tape.source != seed
            or global_tape.modulus != modulus
        ):
            raise ValueError("global innovation tape belongs to another source/modulus")
    tick, macro = witness if witness is not None else (0, None)
    packet: dict[str, object] = {
        "physical_decimal_boundary": physical_boundary_packet(seed, ledger),
        "scope": "first executed decimal boundary macro; not a global endpoint ActionID",
        "executed_macro_actions": {
            family: ledger.counters.get(
                f"collatz_physical_boundary_{family}_macro_actions", 0
            )
            for family in (
                "421",
                "4721",
                "0563",
                "26847",
                "26847P1",
                "26847P2",
                "26847P3",
                "26847P4",
                "630",
                "305",
                "989",
                "6305R",
            )
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
    if global_tape is not None:
        packet["normalized_signed_tape"] = global_tape.packet()
    if macro is None:
        packet.update(
            borrow_scope="no executed boundary witness is certified",
            borrow_clock_status="unresolved",
            status="complete" if global_tape is not None else "partial",
        )
    else:
        from number_compiler.sequences.collatz.border_return_grammar import (
            BorderReturnMacro,
        )

        if (
            type(macro) is BorderReturnMacro
            or macro.family == "0563"
            or (boundary_macro_26847_phase(macro.family) is not None)
        ):
            # The complete normalized tape is already compiled through the
            # source-run signed input-driven Moore port when requested. Do not
            # construct it as a side effect of asking for boundary metadata.
            packet["normalized_temporal_tape"] = {
                "scope": (
                    "complete source-run signed port grammar"
                    if global_tape is not None
                    else "not constructed by the boundary-macro observer"
                ),
                "border": macro.observation(),
                "global_signed_tape_available": global_tape is not None,
            }
        else:
            from number_compiler.sequences.collatz.boundary_macros import (
                CollatzBoundaryMacro,
            )
            from number_compiler.sequences.collatz.innovation_temporal_tape import (
                observed_innovation_macro_tape,
            )

            if type(macro) is not CollatzBoundaryMacro:
                raise TypeError("boundary witness has another macro authority")
            packet["normalized_temporal_tape"] = observed_innovation_macro_tape(
                macro, modulus, ledger=ledger
            )
    return packet
