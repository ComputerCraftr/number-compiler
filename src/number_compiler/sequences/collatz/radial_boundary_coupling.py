"""Demanded high-digit and radial observations of issued Collatz seams.

The family name comes from an already-selected source guard.  The radial
factor is homogeneous, while the signed high-bit transport uses the same
action's affine offset and endpoint.  This module selects no successors.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.affine_high_digits import (
    affine_high_digit_transport,
)
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.radial_sturmian import RadialSturmianClock
from number_compiler.sequences.collatz.border_identity import (
    BorderEntryPort,
    BorderExitPort,
    CollatzSegmentIdentity,
    CycleEntryPhase,
    GuardedBorderPath,
    NonBorderSegment,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.joint_radix_border import JointRadix6Source

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.border_return_grammar import (
        BorderReturnMacro,
    )


@dataclass(frozen=True, slots=True)
class CollatzRadialBoundarySeam:
    """One source-authenticated selected action and its exact endpoint."""

    identity: CollatzSegmentIdentity
    source: int
    endpoint: int
    odd_symbols: int
    action: DyadicTerminalFieldAction
    witness: object | None = None
    joint_source: JointRadix6Source | None = None
    joint_endpoint: JointRadix6Source | None = None

    @property
    def normalized_steps(self) -> int:
        return self.action.steps

    def verify(self) -> None:
        if (self.joint_source is None) != (self.joint_endpoint is None):
            raise ValueError("coupled radix border lost a transported register")
        if (
            self.joint_source is not None
            and self.joint_endpoint is not None
            and (
                type(self.joint_source) is not JointRadix6Source
                or type(self.joint_endpoint) is not JointRadix6Source
                or self.joint_source.source != self.source
                or self.joint_endpoint.source != self.endpoint
                or self.joint_source.after_action(
                    self.action, self.endpoint, self.odd_symbols
                )
                != self.joint_endpoint
            )
        ):
            raise ValueError("coupled radix state disagrees with its source action")
        if (
            type(self.identity)
            not in (
                NonBorderSegment,
                CycleEntryPhase,
                GuardedBorderPath,
            )
            or type(self.source) is not int
            or self.source <= 0
            or type(self.endpoint) is not int
            or self.endpoint <= 0
            or type(self.odd_symbols) is not int
            or self.odd_symbols < 0
            or type(self.action) is not DyadicTerminalFieldAction
            or not self.action.producer_issued
            or not 0 <= self.odd_symbols <= self.action.steps
        ):
            raise ValueError("Collatz seam lacks a well-formed admitted action")

        if self.identity is NonBorderSegment.ZERO_RUN:
            if self.witness is not None:
                raise ValueError("zero-run seam cannot carry a border witness")
            from number_compiler.arithmetic.fields.two_adic import v2_positive

            steps = v2_positive(self.source)
            if (
                self.source == 1
                or self.odd_symbols != 0
                or self.action != DyadicTerminalFieldAction.zero_run(steps)
                or self.endpoint != self.source >> steps
            ):
                raise ValueError("zero-run seam differs from its exact source guard")
            return

        if self.identity is NonBorderSegment.TERMINAL_POWER_OF_TWO:
            from number_compiler.sequences.collatz.terminal_preimage import (
                CollatzTerminalPower2Macro,
                validate_terminal_power2_macro,
            )

            if type(self.witness) is not CollatzTerminalPower2Macro:
                raise ValueError("terminal seam lacks its power-of-two witness")
            validate_terminal_power2_macro(self.witness)
            if (
                self.witness.source != self.source
                or self.witness.endpoint != self.endpoint
                or self.witness.fields != self.action
                or self.odd_symbols != self.witness.odd_symbols
            ):
                raise ValueError("terminal seam is detached from its witness")
            return

        from number_compiler.sequences.collatz.border_return_grammar import (
            BorderReturnMacro,
            validate_border_return_macro,
        )
        from number_compiler.sequences.collatz.boundary_macros import (
            CollatzBoundaryMacro,
            validate_boundary_macro,
        )

        if type(self.witness) is BorderReturnMacro:
            validate_border_return_macro(self.witness)
        elif type(self.witness) is CollatzBoundaryMacro:
            validate_boundary_macro(self.witness)
        else:
            raise ValueError("named Collatz seam lacks its source-guard witness")
        if (
            self.witness.identity != self.identity
            or self.witness.source != self.source
            or self.witness.endpoint != self.endpoint
            or self.witness.fields != self.action
            or self.witness.odd_symbols != self.odd_symbols
        ):
            raise ValueError("Collatz seam is detached from its selected witness")

    def observation(
        self,
        evaluator: GrowthArithmeticEvaluator,
        *,
        width: int,
        previous_odds: int,
        previous_halvings: int,
        next_identity: CollatzSegmentIdentity | None,
        difference_places: int = 0,
        include_walsh64: bool = False,
    ) -> dict[str, object]:
        """Join this selected low-digit transition with radial/high-bit output."""
        self.verify()
        require_integer(previous_odds, "preceding odd count", 0)
        require_integer(previous_halvings, "preceding division count", 0)
        if next_identity is not None and type(next_identity) not in (
            NonBorderSegment,
            CycleEntryPhase,
            GuardedBorderPath,
        ):
            raise ValueError("next selected segment has an unknown identity")
        if type(difference_places) is not int or not 0 <= difference_places <= 64:
            raise ValueError("difference-port demand must be within 0..64")
        if type(include_walsh64) is not bool:
            raise TypeError("Walsh64 demand must be Boolean")
        scale = HomogeneousGrowthScale(
            previous_odds + self.odd_symbols,
            previous_halvings + self.normalized_steps,
        )
        previous_scale = HomogeneousGrowthScale(previous_odds, previous_halvings)
        radial = RadialSturmianClock(scale).leading_binary(evaluator, width)
        order_increment = evaluator.radix_order(scale, 2) - evaluator.radix_order(
            previous_scale, 2
        )
        high = affine_high_digit_transport(
            self.endpoint, self.action.offset, self.action.steps, width
        )
        packet: dict[str, object] = {
            "identity": _identity_observation(self.identity),
            "source_digit": self.source % 10,
            "endpoint_digit": self.endpoint % 10,
            "source_residue20": self.source % 20,
            "endpoint_residue20": self.endpoint % 20,
            "next_admitted_identity": (
                _identity_observation(next_identity)
                if next_identity is not None
                else None
            ),
            "next_identity_authority": (
                "following source-validated seam"
                if next_identity is not None
                else "no following seam was selected"
            ),
            "physical_ticks": self.normalized_steps + self.odd_symbols,
            "normalized_steps": self.normalized_steps,
            "odd_symbols": self.odd_symbols,
            "cumulative_rotation": asdict(radial),
            "cumulative_radial_order_increment": order_increment,
            "high_digit_transport": asdict(high),
            "homogeneous_high_binary": high.homogeneous_high_binary,
            "endpoint_high_binary": high.endpoint_high_binary,
            "high_xor_binary": high.high_xor_binary,
        }
        if self.joint_source is not None and self.joint_endpoint is not None:
            previous, following = self.joint_source, self.joint_endpoint
            packet["joint_radix6_f5_source"] = {
                "source_radix6_cells": tuple(
                    previous.radix6_digit(j) for j in range(5)
                ),
                "endpoint_radix6_cells": tuple(
                    following.radix6_digit(j) for j in range(5)
                ),
                "source_mod5": previous.residue5,
                "endpoint_mod5": following.residue5,
                "source_two_adic_mod32": previous.low_binary,
                "endpoint_two_adic_mod32": following.low_binary,
                "endpoint_candidate": _identity_observation(following.candidate_family),
                "candidate_is_not_source_authority": True,
                "tripling_event_clock": following.tripling_events,
                "halving_event_clock": following.halving_events,
            }
            if difference_places or include_walsh64:
                requested: dict[str, object] = {}
                if following.tripling_events:
                    if difference_places:
                        requested.update(
                            {
                                str(base): following.demanded_difference_ports(
                                    base, difference_places
                                )
                                for base in (3, 6, 10)
                            }
                        )
                    if include_walsh64:
                        requested["64"] = following.demanded_difference_ports(
                            64, 64, walsh=True
                        )
                elif include_walsh64:
                    raise ValueError("Walsh64 requires an issued tripling event")
                packet["homogeneous_difference_ports"] = requested
        from number_compiler.sequences.collatz.border_return_grammar import (
            BorderReturnMacro,
        )

        if type(self.witness) is BorderReturnMacro:
            packet["return_exit_port"] = self.witness.exit_port.value
            packet["6305_return_transitions"] = (
                _border_return_high_transitions_admitted(
                    self.witness, evaluator=evaluator, width=width
                )
            )
        return packet


def _identity_observation(
    identity: CollatzSegmentIdentity | None,
) -> dict[str, object] | None:
    if identity is None:
        return None
    if isinstance(identity, NonBorderSegment):
        return {"kind": "segment", "value": identity.value}
    if isinstance(identity, CycleEntryPhase):
        return identity.observation()
    return identity.observation()


def border_return_high_transitions(
    macro: BorderReturnMacro,
    *,
    evaluator: GrowthArithmeticEvaluator,
    width: int = 8,
) -> tuple[dict[str, object], ...]:
    """Observe certified 6305 returns without replaying their zero tails."""
    from number_compiler.sequences.collatz.border_return_grammar import (
        BorderReturnMacro,
        validate_border_return_macro,
    )

    if type(evaluator) is not GrowthArithmeticEvaluator:
        raise TypeError("6305 high transitions require their growth evaluator")
    if type(macro) is not BorderReturnMacro:
        raise TypeError("6305 return observation needs its issued border action")
    validate_border_return_macro(macro)
    return _border_return_high_transitions_admitted(
        macro, evaluator=evaluator, width=width
    )


def _border_return_high_transitions_admitted(
    macro: BorderReturnMacro,
    *,
    evaluator: GrowthArithmeticEvaluator,
    width: int,
) -> tuple[dict[str, object], ...]:
    """Inspect returns after the seam owner has validated this macro once."""
    from number_compiler.arithmetic.fields.two_adic import v2_positive

    if type(evaluator) is not GrowthArithmeticEvaluator:
        raise TypeError("6305 high transitions require their growth evaluator")
    current = macro.source
    if macro.entry_port is BorderEntryPort.DIGIT_SIX:
        current //= 2
    elif macro.entry_port is BorderEntryPort.DIGIT_ZERO:
        current >>= v2_positive(current)
    if current % 10 == 5:
        current = (3 * current + 1) // 2

    transitions: list[dict[str, object]] = []
    for zero_tail in macro.zero_tails:
        if current % 10 != 3:
            raise ValueError("6305 return is detached from its 3 boundary")
        current_bits = current.bit_length()
        tail_bits = zero_tail + 2
        work_units = max(1, 4 * current_bits + tail_bits + width)
        operand_bits = 3 * current_bits + tail_bits + width
        storage_bits = 2 * current_bits + tail_bits + width + 32
        with evaluator._charge_work(
            work_units,
            0,
            operand_bits,
            storage_bits=storage_bits,
        ):
            upper_numerator = 3 * ((current - 3) // 10) + 1
            if v2_positive(upper_numerator) != zero_tail:
                raise ValueError("6305 zero tail differs from its upper valuation")
            upper_odd = upper_numerator >> zero_tail
            endpoint = (15 * upper_odd + 1) // 2
            correction = 2 if zero_tail == 0 else 1
            if ((9 * current) >> tail_bits) + correction != endpoint:
                raise AssertionError("6305 return carry disagrees with its endpoint")
            high = affine_high_digit_transport(
                endpoint, 3 + (1 << (zero_tail + 1)), tail_bits, width
            )
        transitions.append(
            {
                "from_digit": current % 10,
                "to_digit": endpoint % 10,
                "zero_tail": zero_tail,
                "normalized_steps": zero_tail + 2,
                "physical_ticks": zero_tail + 4,
                "upper_odd_mod4": upper_odd % 4,
                "upper_odd_mod8": upper_odd % 8,
                "next_border": "3_return" if endpoint % 10 == 3 else "8_exit",
                "high_digit_transport": asdict(high),
                "homogeneous_high_binary": high.homogeneous_high_binary,
                "endpoint_high_binary": high.endpoint_high_binary,
                "high_xor_binary": high.high_xor_binary,
            }
        )
        current = endpoint

    if current % 10 not in (3, 8):
        raise AssertionError("6305 return ended outside the admitted exit digits")
    if (
        macro.exit_port
        in (
            BorderExitPort.RETURN_TO_THREE,
            BorderExitPort.RETURN_AT_HORIZON,
        )
        and current != macro.endpoint
    ):
        raise AssertionError("6305 return endpoint differs from its issued action")
    if (
        macro.exit_port
        in (
            BorderExitPort.EIGHT_TO_FOUR,
            BorderExitPort.EIGHT_TO_NINE,
            BorderExitPort.EIGHT_TO_NINE_TO_EIGHT,
            BorderExitPort.EIGHT_TO_NINE_OPEN,
            BorderExitPort.EIGHT_TO_NINE_PENDING,
        )
        and current % 10 != 8
    ):
        raise AssertionError("6305 upper exit lacks its 8 precursor")
    return tuple(transitions)


__all__ = ["CollatzRadialBoundarySeam", "border_return_high_transitions"]
