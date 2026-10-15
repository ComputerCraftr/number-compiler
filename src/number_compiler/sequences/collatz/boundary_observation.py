"""Demanded observations of producer-authenticated physical boundary macros."""

from __future__ import annotations

from dataclasses import asdict
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_0563,
    ENTRY_89_AT_NINE,
    ENTRY_421,
    ENTRY_4721,
    ENTRY_26847_PHASES,
    PATH_305,
    PATH_630,
    BoundaryActionIdentity,
    border_return_path,
)
from number_compiler.sequences.collatz.boundary_macros import (
    boundary_macro_26847_phase,
    boundary_metric_suffix,
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
    ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_OBSERVATION_REQUESTS)
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
    observed_identities: tuple[BoundaryActionIdentity, ...] = (
        ENTRY_421,
        ENTRY_4721,
        ENTRY_0563,
        *ENTRY_26847_PHASES,
        PATH_630,
        PATH_305,
        ENTRY_89_AT_NINE,
        border_return_path(3, 3),
    )
    packet: dict[str, object] = {
        "physical_decimal_boundary": physical_boundary_packet(seed, ledger),
        "unified_skew_composed_actions": ledger.counters.get(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_COMPOSED_ACTIONS, 0
        ),
        "unified_skew_applied_actions": ledger.counters.get(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_APPLIED_ACTIONS, 0
        ),
        "unified_skew_terminal_actions": ledger.counters.get(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_TERMINAL_ACTIONS, 0
        ),
        "unified_skew_joined_segments": ledger.counters.get(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_JOINED_SEGMENTS, 0
        ),
        "unified_skew_clock_checks": ledger.counters.get(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_CLOCK_CHECKS, 0
        ),
        "unified_skew_selector_checks": ledger.counters.get(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_SELECTOR_CHECKS, 0
        ),
        "unified_skew_parent_admissions": ledger.counters.get(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_PARENT_ADMISSIONS, 0
        ),
        "unified_skew_parent_rejections": ledger.counters.get(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_PARENT_REJECTIONS, 0
        ),
        "unified_skew_existing_mixed_parent_yields": ledger.counters.get(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_EXISTING_MIXED_PARENT_YIELDS,
            0,
        ),
        "unified_skew_selection_operand_bits": ledger.counters.get(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_SELECTION_OPERAND_BITS, 0
        ),
        "unified_skew_discarded_operand_bits": ledger.counters.get(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_DISCARDED_OPERAND_BITS, 0
        ),
        "unified_skew_retained_operand_bits": ledger.counters.get(
            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_CHAIN_RETAINED_OPERAND_BITS,
            0,
        ),
        "scope": "first executed decimal boundary macro; not a global endpoint ActionID",
        "executed_macro_actions": {
            suffix: ledger.counters.get(
                f"collatz_physical_boundary_{suffix}_macro_actions", 0
            )
            for suffix in tuple(
                dict.fromkeys(
                    boundary_metric_suffix(identity) for identity in observed_identities
                )
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
        if macro is not None:
            from number_compiler.sequences.collatz.border_return_grammar import (
                BorderReturnMacro,
            )
            from number_compiler.sequences.collatz.boundary_macros import (
                CollatzBoundaryMacro,
            )
            from number_compiler.sequences.collatz.radial_boundary_coupling import (
                CollatzRadialBoundarySeam,
            )
            from number_compiler.sequences.collatz.skew_cylinder_repeat import (
                GuardedSkewCylinderPower,
            )

            if type(macro) is BorderReturnMacro or type(macro) is CollatzBoundaryMacro:
                action = macro.fields
                odd_symbols = macro.odd_symbols
                identity = macro.identity
            else:
                raise TypeError("boundary witness has another macro authority")
            seam = CollatzRadialBoundarySeam(
                identity,
                macro.source,
                macro.endpoint,
                odd_symbols,
                action,
                macro,
            )
            with GrowthArithmeticEvaluator(ledger) as evaluator:
                coupled = seam.observation(
                    evaluator,
                    width=8,
                    previous_odds=0,
                    previous_halvings=0,
                    next_identity=None,
                )
                if type(macro) is BorderReturnMacro:
                    cylinder, power = GuardedSkewCylinderPower.inspect_border_return(
                        macro, 2, evaluator=evaluator
                    )
                elif type(macro) is CollatzBoundaryMacro:
                    cylinder, power = GuardedSkewCylinderPower.inspect_boundary_macro(
                        macro, 2, evaluator=evaluator
                    )
                else:
                    raise TypeError("boundary witness has another macro authority")
                repeated: dict[str, object] = {
                    "fixed_point_denominator": cylinder.fixed_point_denominator,
                    "two_adic_defect": cylinder.defect,
                    "repeat_moore_class": cylinder.remaining_repetitions,
                    "infinite_repeat_class": cylinder.defect == 0,
                    "square_admitted": power is not None,
                    "scope": "same source-admitted parity word only",
                }
                if power is not None:
                    try:
                        repeated.update(power.observation(evaluator))
                        bound = power.materialization_bound_bits
                        if bound <= 4096:
                            high = power.high_digit_transport(
                                8,
                                max_materialization_bits=4096,
                                evaluator=evaluator,
                            )
                            repeated.update(
                                squared_homogeneous_high_binary=(
                                    high.homogeneous_high_binary
                                ),
                                squared_endpoint_high_binary=(
                                    high.endpoint_high_binary
                                ),
                                squared_high_xor_binary=high.high_xor_binary,
                                squared_high_digit_transport=asdict(high),
                                materialization_status="available",
                            )
                        else:
                            repeated["materialization_status"] = "over_4096_bit_budget"
                    except BlockContextBudgetExceeded:
                        repeated["materialization_status"] = "budget_refused"
                else:
                    repeated["materialization_status"] = "refused_by_parity_cylinder"
            coupled["repeated_skew_cylinder"] = repeated
            packet["coupled_radial_boundary"] = coupled
        return packet
    from number_compiler.sequences.collatz.innovation_carry_cocycle import (
        CollatzInnovationCocycle,
    )

    source_modulus = 4 * modulus
    residue = seed % source_modulus
    ledger.bump(
        _collatz_keys.COLLATZ_INNOVATION_SOURCE_OPERAND_BITS,
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
            or macro.identity == ENTRY_0563
            or (boundary_macro_26847_phase(macro.identity) is not None)
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
