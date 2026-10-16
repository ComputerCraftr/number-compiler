"""Finite border-safety ports; no unproved whole-196 macro repetition."""

from __future__ import annotations

from dataclasses import replace
from random import Random

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.border_carry_safety import (
    BorderTile,
    ConditionalBorderCycle,
    border_carry_port,
    conditional_return_from_trace,
    conditional_window_return_from_trace,
    enumerate_one_digit_cycles,
    reverse_k,
    universal_one_digit_states,
)
from number_compiler.sequences.reverse_add.q19_border_control import (
    BoundaryControlNotAuthorized,
)
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner


def _reverse(x: int) -> int:
    return int(str(x)[::-1])


def _tile(x: int, k: int) -> BorderTile:
    word = str(x)
    return BorderTile(k, int(word[:k]), int(word[-k:]))


def _carry_into_high_tile(x: int, k: int) -> int:
    digits = digits_lsd(x, 10)
    carry = 0
    for i in range(len(digits) - k):
        carry = int(digits[i] + digits[-i - 1] + carry >= 10)
    return carry


def _owner_at_196_generation_79() -> tuple[
    int, ResourceLedger, ReversePairQ19OutputOwner
]:
    source = 196
    for _ in range(79):
        source += _reverse(source)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(source, 10), base=10)
    return source, ledger, owner


def test_fixed_width_reversal_checks_the_shared_border_width_bound() -> None:
    assert reverse_k(1, 64) == 10**63
    assert BorderTile(64, 10**63, 0).k == 64
    for width in (True, 0, 65):
        with pytest.raises(ValueError):
            reverse_k(1, width)
        with pytest.raises(ValueError):
            BorderTile(width, 1, 0)
    with pytest.raises(ValueError):
        reverse_k(True, 1)


def test_all_26_one_digit_states_and_96_cycles_have_exact_carry_guards() -> None:
    states = universal_one_digit_states()
    assert len(states) == 26
    cycles = enumerate_one_digit_cycles()
    assert len(cycles) == 96
    assert sum(c.has_trailing_zero for c in cycles) == 83
    assert {min(c.steps for c in cycles), max(c.steps for c in cycles)} == {2, 24}
    assert all(c.needs_future_carry_certificate for c in cycles)
    assert all(not c.source_universal for c in cycles)
    for cycle in cycles:
        span, births, moment = cycle.conditional_repeat(10**18)
        assert span == cycle.steps * 10**18
        assert births == cycle.width_growth * 10**18
        assert moment >= 0
        assert cycle.conditional_repeat(0) == (0, 0, 0)
        for state, port, bit in zip(
            cycle.states, cycle.incoming, cycle.growth, strict=True
        ):
            assert bit in (0, 1)
            assert port in (0, 1, None)
            assert state in states
    forged = replace(cycles[0])
    object.__setattr__(forged, "source_universal", True)
    with pytest.raises(ValueError):
        replace(forged)
    with pytest.raises(ValueError):
        cycles[0].conditional_repeat(-1)


def test_k2_forces_leading_carry_safety_without_inventing_inner_port() -> None:
    for high, low, ingress, next_high in (
        (88, 88, 1, "17"),
        (91, 8, 0, "17"),
        (95, 58, 1, "18"),
    ):
        guard = border_carry_port(BorderTile(2, high, low))
        assert guard.forced_msd_ingress == ingress
        assert guard.forced_growth == 1
        assert guard.common_prefix == next_high
        assert tuple(edge.target.high for edge in guard.edges) == (
            int(next_high),
            int(next_high),
        )
        assert guard.require_growth(1) == (0, 1)
        assert guard.require_growth(0) == ()
    # Same high carry, but the lower high digit differs. Do not puncture it.
    exceptional = border_carry_port(BorderTile(2, 12, 2))
    assert exceptional.forced_msd_ingress == 0
    assert exceptional.forced_growth == 0
    assert exceptional.common_prefix == "3"
    assert exceptional.require_target(BorderTile(2, 32, 23)) == (0,)
    assert exceptional.require_target(BorderTile(2, 33, 23)) == (1,)


def test_every_known_border_tile_contains_the_actual_reverse_add_edge() -> None:
    rng = Random(19685)
    for _ in range(1500):
        w = rng.randrange(3, 80)
        x = rng.randrange(10 ** (w - 1), 10**w)
        k = rng.randrange(1, (w - 1) // 2 + 1)
        source = _tile(x, k)
        ingress = _carry_into_high_tile(x, k)
        truth = _tile(x + _reverse(x), k)
        port = border_carry_port(source)
        edge = next(edge for edge in port.edges if edge.carry_in == ingress)
        assert edge.target == truth
        assert edge.growth == int(len(str(x + _reverse(x))) > w)
        assert tuple(
            candidate.carry_in
            for candidate in border_carry_port(source, (ingress,)).edges
        ) == (ingress,)


def test_196_79_to_88_is_a_finite_conditional_return_not_a_global_repeat() -> None:
    x, ledger, owner = _owner_at_196_generation_79()
    try:
        short = owner.certify_border_growth(owner.initial, steps=9, window_digits=2)
        assert short.growth_word == (0, 1, 0, 0, 1, 0, 1, 0, 1)
        assert None in short.outer_pairs
        with pytest.raises(BoundaryControlNotAuthorized):
            short.conditional_outer_return()

        proved = owner.certify_border_growth(owner.initial, steps=9, window_digits=3)
        assert all(state is not None for state in proved.outer_pairs)
        assert proved.outer_pairs == (
            (1, 5),
            (7, 6),
            (1, 3),
            (4, 4),
            (9, 8),
            (1, 7),
            (8, 8),
            (1, 6),
            (8, 7),
            (1, 5),
        )
        assert proved.forced_leading_carry_ports() == (
            (1,),
            (0, 1),
            (0,),
            (1,),
            (0, 1),
            (0,),
            (0, 1),
            (1,),
            (0, 1),
        )
        cycle = proved.conditional_outer_return()
        assert isinstance(cycle, ConditionalBorderCycle)
        assert cycle.width_growth == 4
        assert cycle.conditional_repeat(2) == (18, 8, 62)
        assert cycle.needs_future_carry_certificate
        assert not cycle.source_universal
        x_test = x
        for i, bit in enumerate(proved.growth_word):
            y = x_test + _reverse(x_test)
            assert _tile(x_test, 1).high == proved.outer_pairs[i][0]
            assert _tile(x_test, 1).low == proved.outer_pairs[i][1]
            assert int(len(str(y)) > len(str(x_test))) == bit
            x_test = y
        assert proved.outer_pairs[-1] == (int(str(x_test)[0]), int(str(x_test)[-1]))
        # A certificate for one physical return does not authorize unlimited
        # repetition: the interior source root is different after nine steps.
        with pytest.raises(ValueError):
            conditional_return_from_trace(((1, 5), (7, 6)), (1,))
        assert ledger.counters.get("reverse_q19_punctured_t4_applications", 0) == 0
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_certified_border_return_issues_a_punctured_conditional_f5_action() -> None:
    from number_compiler.sequences.reverse_add.conditional_f5_macro import (
        SourceCertifiedF5Macro,
    )

    _, ledger, owner = _owner_at_196_generation_79()
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=9, window_digits=3
        )
        macro = certificate.conditional_f5_macro_action(z=4)
        assert type(macro) is SourceCertifiedF5Macro
        assert macro.duration == 9
        assert macro.cycle.growth == certificate.growth_word
        assert macro.homogeneous_multiplier == 0
        assert macro.forcing_weights == (0, 0, 0, 0, 0, 0, 0, 0, 1)
        assert macro.apply(None, (None,) * 8 + (3,)) == 3
        assert macro.apply(2, (None,) * 8 + (3,)) == 3
        assert macro.apply(2, (None,) * 9) is None

        known_forcing = tuple(range(9))
        ordinary = certificate.conditional_f5_macro_action(z=2)
        affine = ordinary.affine_action(known_forcing)
        assert affine is not None
        direct = 1
        for growth, correction in zip(
            certificate.growth_word, known_forcing, strict=True
        ):
            direct = ((3 if growth else 2) * direct + correction) % 5
        assert affine.apply(1) == direct
        assert ordinary.conditional_repeat(3, 1, known_forcing) == affine.repeat(
            3
        ).apply(1)
        # A non-returning or partially known trace cannot issue a temporal action.
        with pytest.raises(BoundaryControlNotAuthorized):
            certificate.conditional_f5_macro_action(start=1, steps=8, z=2)
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_same_k2_outer_return_may_exit_when_first_non9_port_changes() -> None:
    x = 12302
    seen = []
    for _ in range(5):
        seen.append(_tile(x, 2))
        x += _reverse(x)
    assert seen[:4] == [
        BorderTile(2, 12, 2),
        BorderTile(2, 32, 23),
        BorderTile(2, 65, 46),
        BorderTile(2, 12, 2),
    ]
    assert seen[4] == BorderTile(2, 33, 23)
    assert border_carry_port(seen[0]).require_target(seen[1]) == (0,)
    assert border_carry_port(seen[3]).require_target(seen[4]) == (1,)
    cycle = conditional_window_return_from_trace(tuple(seen[:4]), (0, 0, 1))
    assert cycle.incoming == (0, 1, 0)
    assert cycle.width_growth == 1
    assert cycle.needs_future_carry_certificate
    assert not cycle.source_universal
    assert cycle.conditional_repeat(10**18)[1] == 10**18
    with pytest.raises(ValueError):
        conditional_window_return_from_trace(tuple(seen[:4]), (0, 1, 1))


def test_later_source_first_non9_is_not_folded_from_previous_pair_root() -> None:
    rng = Random(1919)
    for _ in range(20):
        x = rng.randrange(10**19, 10**35)
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(x, 10), base=10)
        try:
            from number_compiler.sequences.reverse_add.q19_border_control import (
                _source_inner_carry,
            )

            issued = owner.apply_pair_step(owner.initial)
            successor = x + _reverse(x)
            emitted = successor + _reverse(successor)
            digits = digits_lsd(emitted, 10)
            incoming, inspections = _source_inner_carry(
                owner, issued, width=len(digits), k=3, max_states=300
            )
            assert inspections >= 1
            expected = 0
            for i in range(len(digits) - 3):
                expected = int(digits[i] + digits[-i - 1] + expected >= 10)
            assert incoming == expected
            # The first step of a later-root certificate is the transition
            # X_(n+1) -> X_(n+2), not the initial X_n -> X_(n+1).
            one = owner.certify_border_growth(issued, steps=1, window_digits=3)
            assert one.growth_word == (int(len(str(emitted)) > len(str(successor))),)
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0


def test_certified_gt_bank_consumes_same_leading_safety_trace() -> None:
    from tests.support.reverse_add_banks import source_guarded_periodic_banks

    with source_guarded_periodic_banks() as (ledger, owner, cert, bank, spatial):
        assert bank.control_certified
        assert spatial.control_certified
        for tick in range(8):
            assert (
                bank.leading_carry_ports(tick)
                == (cert.forced_leading_carry_ports()[tick])
            )
            assert spatial.leading_carry_ports(tick) == bank.leading_carry_ports(tick)
        conditional = owner.authorize_controlled_gt_bank(
            owner.initial,
            steps=8,
            coordinate=200,
            period_size=2,
            growth_control=cert.growth_word,
        )
        with pytest.raises(ValueError, match="live border certificate"):
            conditional.leading_carry_ports(0)
        saved = cert.outer_pairs
        object.__setattr__(cert, "outer_pairs", saved[:-1] + (None,))
        with pytest.raises(ValueError, match="changed|retained"):
            cert.validate(owner, owner.initial)
        object.__setattr__(cert, "outer_pairs", saved)
        cert.validate(owner, owner.initial)
        audit = ledger.audit_payload_contracts()
        assert audit.invalid == frozenset()
