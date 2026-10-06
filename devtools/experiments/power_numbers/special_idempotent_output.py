"""Factor-backed research for idempotent special-number output quotients.

This module answers the concrete question raised by the terminal source gap:
how much of a requested output can be emitted without deciding the unresolved
source theorem?

The production algebra lives in :mod:`number_compiler.arithmetic.fields.idempotent_output` and is
oracle-free.  The audits here may use known factors/CRT truth, exactly like the
other bounded special-number research controls.  They deliberately separate:

1. a global Boolean PASS/FAIL output guard;
2. the ring-valued support idempotent ``e=(1-b)/2``; and
3. a successor-closed machine state.

Those three objects coincide on simple ALL_PASS/ALL_FAIL controls but are not
interchangeable on mixed support or under temporal powering.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.experiments.power_numbers.special_germ_descent import (
    GermOrientationAudit,
    mersenne_m29_mixed_orientation_audit,
    prime_decision_orientation_truth_audit,
)
from devtools.experiments.power_numbers.terminal_etale_square import (
    bit_not_successor_closed_audit,
    etale_square_bit_truth_audit,
)
from number_compiler.arithmetic.fields.idempotent_output import (
    IdempotentModElement,
)
from number_compiler.arithmetic.fields.morphism_core import QuadraticPower
from number_compiler.projection.output_quotient import (
    BinaryOutputCoordinate,
    audit_binary_source_factor,
    minimize_projection_machine,
)
from number_compiler.sequences.power_numbers.idempotent_output import (
    IdempotentSpecialDigitBlock,
)
from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    MersenneNumberSpec,
)


def orientation_idempotent(row: GermOrientationAudit) -> int:
    """Return ``e=(1-b)/2`` from one exact factor-backed orientation row."""
    modulus = row.modulus
    if modulus % 2 == 0:
        raise ValueError(modulus)
    e = ((1 - row.crt_orientation) * pow(2, -1, modulus)) % modulus
    if (e * e - e) % modulus:
        raise AssertionError((row.crt_orientation, e, modulus))
    return e


@dataclass(frozen=True, slots=True)
class TerminalIdempotentControlAudit:
    family: str
    parameter: int
    status: str
    modulus: int
    orientation: int
    idempotent: int
    boolean_idempotent: bool
    expected_boolean: int | None
    exact_boolean_specialization: bool
    digit_derivatives: tuple[int, ...]
    length_endpoints: tuple[int, int]
    carry_endpoints: tuple[int, int]
    carry_at_actual_idempotent: int
    factor_enumeration: int
    candidate_derived: bool = False

    @property
    def idempotent_valid(self) -> bool:
        return pow(self.idempotent, 2, self.modulus) == self.idempotent


def terminal_idempotent_control_audit(
    family: str,
    parameter: int,
) -> TerminalIdempotentControlAudit:
    """Differential the rank-two coordinate against a bounded exact control."""
    row = prime_decision_orientation_truth_audit(str(family), int(parameter))
    e = orientation_idempotent(row)
    formal = IdempotentModElement.generator(row.modulus)
    block = IdempotentSpecialDigitBlock(row.family, row.parameter, formal)
    derivatives = tuple(
        block.endpoint_digit_pair(index)[1] - block.endpoint_digit_pair(index)[0]
        for index in range(block.width + 1)
    )
    lengths = block.endpoint_length_pair()
    carries = block.endpoint_square_boundary_carries()
    carry_actual = block.square_boundary_carry_at_idempotent(e)
    expected = (
        0
        if row.result.status == "ALL_PASS"
        else 1
        if row.result.status == "ALL_FAIL"
        else None
    )
    return TerminalIdempotentControlAudit(
        row.family,
        row.parameter,
        row.result.status,
        row.modulus,
        row.crt_orientation,
        e,
        e in (0, 1),
        expected,
        expected is not None and e == expected,
        derivatives,
        lengths,
        carries,
        carry_actual,
        row.factor_enumeration,
    )


@dataclass(frozen=True, slots=True)
class SplitEndpointCounterexampleAudit:
    family: str
    parameter: int
    status: str
    modulus: int
    local_orientations: tuple[int, ...]
    idempotent: int
    chosen_digit: int
    endpoint_digits: tuple[int, int]
    split_digit: int
    endpoint_lengths: tuple[int, int]
    split_length: int
    endpoint_carries: tuple[int, int]
    split_carry: int
    endpoint_digit_equality_unsound: bool
    endpoint_length_equality_unsound: bool
    endpoint_carry_equality_unsound: bool
    factor_enumeration: int
    candidate_derived: bool = False


def mixed_split_endpoint_counterexample_audit() -> SplitEndpointCounterexampleAudit:
    """Freeze M29's nontrivial CRT idempotent as a nonlinear-output guard.

    M29 has local orientations ``(-1,-1,+1)`` at the level-one control.  Its
    support idempotent is therefore neither 0 nor 1.  The formal element ``E``
    has equal endpoint values for every binary digit above bit zero and equal
    endpoint lengths, yet specialization to the exact CRT idempotent changes
    both.  The canonical Lucas--Lehmer end-around carry also changes.
    """
    row = mersenne_m29_mixed_orientation_audit()
    e = orientation_idempotent(row)
    if e in (0, 1):
        raise AssertionError(("expected-nontrivial-idempotent", e))
    formal = IdempotentModElement.generator(row.modulus)
    block = IdempotentSpecialDigitBlock("mersenne", 29, formal)

    # Pick a nonzero high bit of the actual idempotent.  Both Boolean endpoints
    # 0 and 1 have zero there by construction.
    chosen = e.bit_length() - 1
    endpoint_digits = block.endpoint_digit_pair(chosen)
    split_digit = block.digit_at_idempotent(chosen, e)
    endpoint_lengths = block.endpoint_length_pair()
    split_length = block.length_at_idempotent(e)
    endpoint_carries = block.endpoint_square_boundary_carries()
    split_carry = block.square_boundary_carry_at_idempotent(e)
    return SplitEndpointCounterexampleAudit(
        "mersenne",
        29,
        row.result.status,
        row.modulus,
        row.local_orientations,
        e,
        chosen,
        endpoint_digits,
        split_digit,
        endpoint_lengths,
        split_length,
        endpoint_carries,
        split_carry,
        endpoint_digits[0] == endpoint_digits[1] and split_digit != endpoint_digits[0],
        endpoint_lengths[0] == endpoint_lengths[1]
        and split_length != endpoint_lengths[0],
        endpoint_carries[0] == endpoint_carries[1]
        and split_carry != endpoint_carries[0],
        row.factor_enumeration,
    )


@dataclass(frozen=True, slots=True)
class BooleanOutputQuotientAudit:
    source_bits: tuple[bool, ...]
    outputs: tuple[int, ...]
    factors_through_bit: bool
    quotient_states: int | None
    mode: str | None
    derivative: int | None
    source_bit_recoverable: bool


def boolean_output_quotient_audit(
    source_bits: tuple[bool, ...],
    outputs: tuple[int, ...],
) -> BooleanOutputQuotientAudit:
    """Construct the requested Concrete/Guarded quotient only after proof."""
    audit = audit_binary_source_factor(source_bits, outputs)
    if not audit.coordinate_available:
        return BooleanOutputQuotientAudit(
            tuple(source_bits),
            tuple(outputs),
            audit.factors_through_source_bit,
            None,
            None,
            None,
            False,
        )
    coordinate = BinaryOutputCoordinate.from_factor_audit(audit)
    recoverable = False
    if coordinate.separates_source_bit:
        recoverable = (
            coordinate.recover_source_bit(coordinate.false_value) is False
            and coordinate.recover_source_bit(coordinate.true_value) is True
        )
    return BooleanOutputQuotientAudit(
        tuple(source_bits),
        tuple(outputs),
        True,
        coordinate.quotient_states,
        coordinate.mode.value,
        coordinate.derivative,
        recoverable,
    )


@dataclass(frozen=True, slots=True)
class OutputPartitionClosureAudit:
    same_current_bit: bool
    different_next_bit: bool
    output_fiber_states: int
    successor_closed_states: int
    refinements: int
    output_only_partition_is_closed: bool
    conclusion: str


def output_partition_successor_closure_audit() -> OutputPartitionClosureAudit:
    """Turn the existing F4/F5 witness into an executable partition-refinement test."""
    witness = bit_not_successor_closed_audit()
    f4_now = etale_square_bit_truth_audit("fermat", 4, 1).all_local_square
    f5_now = etale_square_bit_truth_audit("fermat", 5, 1).all_local_square
    f4_next = etale_square_bit_truth_audit("fermat", 4, 2).all_local_square
    f5_next = etale_square_bit_truth_audit("fermat", 5, 2).all_local_square

    # Four bounded truth states: current F4/F5 rows flow to their next-level
    # rows; the latter self-loop only to make a closed finite unary control.
    outputs = tuple(map(int, (f4_now, f5_now, f4_next, f5_next)))
    successors = (2, 3, 2, 3)
    quotient = minimize_projection_machine(outputs, successors)
    return OutputPartitionClosureAudit(
        witness.same_current_bit,
        witness.different_next_bit,
        quotient.initial_state_count,
        quotient.state_count,
        quotient.refinements,
        quotient.output_fibers_successor_closed,
        "output equivalence is an emission quotient; powered state requires successor refinement",
    )


@dataclass(frozen=True, slots=True)
class RawSpecialMaterializationAudit:
    family: str
    parameter: int
    raw_value: int
    zero_sheet_value: int
    one_sheet_value: int
    source_independent: bool
    output_quotient_states: int


def raw_special_materialization_audit(
    family: str, parameter: int
) -> RawSpecialMaterializationAudit:
    """Freeze that raw F_n/M_p construction never consumes the theorem bit."""
    family = str(family)
    parameter = int(parameter)
    value = (
        FermatNumberSpec(parameter).materialize()
        if family == "fermat"
        else MersenneNumberSpec(parameter).materialize()
        if family == "mersenne"
        else None
    )
    if value is None:
        raise ValueError(family)
    audit = audit_binary_source_factor((False, True), (value, value))
    coordinate = BinaryOutputCoordinate.from_factor_audit(audit)
    return RawSpecialMaterializationAudit(
        family,
        parameter,
        value,
        value,
        value,
        coordinate.mode.value == "Concrete",
        coordinate.quotient_states,
    )


@dataclass(frozen=True, slots=True)
class RankTwoPowerAudit:
    family: str
    parameter: int
    depth: int
    formal_zero: int
    formal_one: int
    reference_zero: int
    reference_one: int
    exact: bool


def rank_two_quadratic_power_audit(
    family: str, parameter: int, depth: int
) -> RankTwoPowerAudit:
    """Verify the shared ``QuadraticPower`` operates directly on rank-two state."""
    family = str(family)
    parameter = int(parameter)
    depth = int(depth)
    if depth < 0:
        raise ValueError(depth)
    modulus = (
        FermatNumberSpec(parameter).materialize()
        if family == "fermat"
        else MersenneNumberSpec(parameter).materialize()
        if family == "mersenne"
        else None
    )
    if modulus is None:
        raise ValueError(family)

    # Deliberately distinct sheets so this tests real branch propagation rather
    # than the trivial E generator fixed by squaring.
    formal = IdempotentModElement.from_sheets(modulus, 3, 5)
    power = QuadraticPower(depth)
    if family == "fermat":
        result = power.apply_iterated(formal, step=lambda item: item.square())
        ref0 = pow(3, 1 << depth, modulus)
        ref1 = pow(5, 1 << depth, modulus)
    else:
        result = power.apply_iterated(formal, step=lambda item: item.square().add(-2))
        ref0, ref1 = 3 % modulus, 5 % modulus
        for _ in range(depth):
            ref0 = (ref0 * ref0 - 2) % modulus
            ref1 = (ref1 * ref1 - 2) % modulus
    return RankTwoPowerAudit(
        family,
        parameter,
        depth,
        result.zero_sheet,
        result.one_sheet,
        ref0,
        ref1,
        result.sheets == (ref0, ref1),
    )


__all__ = [
    "BooleanOutputQuotientAudit",
    "OutputPartitionClosureAudit",
    "RankTwoPowerAudit",
    "RawSpecialMaterializationAudit",
    "SplitEndpointCounterexampleAudit",
    "TerminalIdempotentControlAudit",
    "boolean_output_quotient_audit",
    "mixed_split_endpoint_counterexample_audit",
    "orientation_idempotent",
    "output_partition_successor_closure_audit",
    "rank_two_quadratic_power_audit",
    "raw_special_materialization_audit",
    "terminal_idempotent_control_audit",
]
