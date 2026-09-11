from __future__ import annotations

from devtools.proofs.carry_action_quotient import (
    CarryActionQuotientArena,
    analyze_carry_action_quotient,
)
from number_compiler.arithmetic.carry.carry_itinerary import LiveCarryItinerary
from number_compiler.arithmetic.carry.carry_monoid import scan_carry_automaton
from number_compiler.arithmetic.carry.event_memory import (
    carry_field,
    event_memory_horizon,
    pair_step,
)
from number_compiler.arithmetic.fields.radix import digits_lsd


def _pair(value: int, base: int) -> tuple[int, ...]:
    digits = digits_lsd(value, base)
    return tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))


def test_reverse_add_carry_scan_is_exactly_the_existing_three_function_automaton() -> (
    None
):
    pair = _pair(196, 10)
    direct = carry_field(pair, base=10)
    result = scan_carry_automaton(pair, base=10)
    assert result.boundaries == direct
    assert 1 <= result.distinct_transition_functions <= 3


def test_live_carry_primary_cyclotomic_interface_is_semantic_and_self_advancing() -> (
    None
):
    base = 10
    horizon = event_memory_horizon(base)
    pair = _pair(196, base)
    rows = []
    for _ in range(horizon):
        rows.append(carry_field(pair, base=base))
        pair, _ = pair_step(pair, base)
    live = LiveCarryItinerary.seed(rows, base=base)
    arena = CarryActionQuotientArena()
    first = arena.intern_source(live)
    again = arena.intern_source(live)
    assert first is again
    assert first.width == len(live.pair)
    assert first.primary_jet
    assert tuple(m for m, _ in first.cyclotomic_valuations) == (1, 2, 4, 8)
    action = arena.intern_action(live)
    assert action.growth in (0, 1)
    next_live = live.advance()
    assert next_live.pair == pair_step(live.pair, base)[0]


def test_proposed_full_extensional_carry_key_is_fail_honest_on_196() -> None:
    metrics = analyze_carry_action_quotient(196, base=10, transitions=256)
    # This is the requested exact key.  It currently does not merge the 196
    # actions, so it must not be advertised as the missing powered quotient.
    assert metrics.unique_source_interfaces == metrics.transitions
    assert metrics.unique_nonlinear_actions == metrics.transitions
    assert metrics.nonlinear_action_reuses == 0
    assert metrics.live_rows_max <= 11


def test_extensional_carry_action_key_is_adaptive_across_radices() -> None:
    decimal = analyze_carry_action_quotient(196, base=10, transitions=128)
    octal = analyze_carry_action_quotient(196, base=8, transitions=128)
    assert decimal.nonlinear_action_reuses == 0
    # The exact threshold-word key merges before prefix compilation: equal <,=,>
    # signatures are a theorem of equal carry behavior, not an output hash.
    assert octal.unique_source_interfaces == 128
    assert octal.nonlinear_action_reuses == 47
    assert octal.carry_scan_evaluations == 0
    assert octal.unique_theorem_interfaces == 112


def test_threshold_signature_is_an_exact_pre_scan_action_key() -> None:
    from devtools.proofs.carry_action_quotient import CarryThresholdSignature
    from number_compiler.arithmetic.carry.carry_monoid import scan_carry_automaton

    base = 10
    pairs = ((0, 9, 18, 9, 4), (0, 9, 18, 9, 4), (1, 9, 17, 9, 5), (2, 8, 16, 9, 6))
    groups: dict[tuple[object, ...], tuple[int, ...]] = {}
    for pair in pairs:
        key = CarryThresholdSignature.from_pair(pair, base=base).canonical_key
        carry = scan_carry_automaton(pair, base=base).boundaries
        if key in groups:
            assert groups[key] == carry
        else:
            groups[key] = carry
    assert len(groups) < len(pairs)


def test_one_carry_row_is_not_a_temporal_automaton_state() -> None:
    # Same current carry vector, different next carry: the temporal automaton
    # needs the live suffix/theorem interface rather than one carry row.
    p = (4, 4)
    q = (5, 5)
    base = 10
    assert carry_field(p, base=base) == carry_field(q, base=base) == (0, 0, 0)
    pn, _ = pair_step(p, base)
    qn, _ = pair_step(q, base)
    assert carry_field(pn, base=base) == (0, 0, 0)
    assert carry_field(qn, base=base) == (0, 1, 1)


def test_reset_observer_synthesizes_full_carry_row_without_scan_execution_randomized() -> (
    None
):
    import random

    from devtools.proofs.carry_action_quotient import CarryResetSignature

    rng = random.Random(0x0B5E2E)
    for base in range(3, 17):
        for _ in range(40):
            width = rng.randint(1, 32)
            pair = tuple(rng.randrange(2 * base - 1) for _ in range(width))
            reset = CarryResetSignature.from_pair(pair, base=base)
            for incoming in (0, 1):
                direct = scan_carry_automaton(
                    pair, base=base, incoming=incoming
                ).boundaries
                assert reset.boundaries(incoming) == direct
                count, mask = reset.boundary_mask(incoming)
                assert count == width + 1
                assert tuple((mask >> i) & 1 for i in range(count)) == direct
                assert reset.final_carry(incoming) == direct[-1]
