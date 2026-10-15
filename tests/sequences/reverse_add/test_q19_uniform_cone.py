"""Source-authenticated homogeneous temporal cone and fail-closed macro guards."""

from __future__ import annotations

from dataclasses import replace
from random import Random

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.q19_uniform_cone import (
    CertifiedUniformCone,
    UniformConeNotAuthorized,
    _bulk_at,
    _same_symbol_range,
    authorize_uniform_cone,
)


def _rev(x: int) -> int:
    return int(str(x)[::-1])


def _pair_at(value: int, index: int) -> int:
    digits = str(value)[::-1]
    return int(digits[index]) + int(digits[-index - 1])


def _word_from_pairs(half: list[int], rng: Random) -> int:
    low, high = [], []
    for index, s in enumerate(half):
        lo = max(0, s - 9)
        hi = min(9, s)
        if index == 0:
            hi = min(hi, s - 1)
            if hi < lo:
                raise ValueError("outer pair cannot be canonical")
        a = rng.randint(lo, hi)
        low.append(a)
        high.append(s - a)
    return int("".join(map(str, high)) + "".join(map(str, reversed(low))))


def test_uniform_bulk_temporal_square_without_any_completed_child(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    start = int("1" * 600)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(start, 10), base=10)
    try:
        source = owner.initial

        def poisoned(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("a source-closed interior power replayed Q19")

        monkeypatch.setattr(owner, "apply_pair_step", poisoned)
        monkeypatch.setattr(owner, "apply_punctured_pair_block", poisoned)
        action = owner.authorize_temporal_cell(source, steps=32, coordinate=300)
        action = action.square(owner).square(owner)
        assert action.steps == 128
        assert action.source == source
        x = start
        for t in range(129):
            assert action.at(t) == _pair_at(x, 300), t
            x += _rev(x)
        assert action.five_band in ("lt_low", "lt_high", "eq", "gt_low", "gt_high")
        assert action.f5 == action.coefficient % 5
        assert ledger.counters.get("reverse_q19_primitive_pair_applications", 0) == 0
        assert ledger.counters.get("reverse_q19_punctured_t4_applications", 0) == 0
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_all_reset_pairs_and_uniform_eq_first_reset() -> None:
    for d in range(1, 10):
        start = int(str(d) * 500)
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(start, 10), base=10)
        try:
            power = owner.authorize_temporal_cell(
                owner.initial, steps=80, coordinate=250
            )
            x = start
            for t in range(81):
                assert power.at(t) == _pair_at(x, 250), (d, t)
                x += _rev(x)
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0

    start = int("4" * 250 + "5" * 250)  # all pair coefficients are 9
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(start, 10), base=10)
    try:
        power = owner.authorize_temporal_cell(owner.initial, steps=80, coordinate=250)
        assert power.source_symbol == 9 and power.source_ingress == 0
        assert power.at(1) == 18
        x = start
        for t in range(81):
            assert power.at(t) == _pair_at(x, 250)
            x += _rev(x)
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_random_protected_interior_and_all_growth_choices() -> None:
    rng = Random(1962026)
    checked = 0
    for _ in range(110):
        # An actual, completely arbitrary outer digit border surrounds a
        # homogeneous central core; growth is never supplied as an oracle.
        s = rng.randrange(19)
        half = [rng.randrange(1, 19)]
        half.extend(rng.randrange(19) for _ in range(48))
        half.extend([s] * 160)
        half.extend(rng.randrange(19) for _ in range(60))
        start = _word_from_pairs(half, rng)
        source_width = len(str(start))
        coord = 110
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(start, 10), base=10)
        try:
            try:
                power = owner.authorize_temporal_cell(
                    owner.initial, steps=20, coordinate=coord
                )
            except UniformConeNotAuthorized:
                # A nine-wire with asymmetric *actual* ingress is not closed.
                assert s == 9
                continue
            x = start
            for t in range(21):
                assert coord < len(str(x))
                assert power.at(t) == _pair_at(x, coord), (s, t, source_width)
                x += _rev(x)
            checked += 1
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0
    assert checked >= 95


def test_future_nongrowth_borrow_gate_matches_independent_digit_subtraction() -> None:
    for d in range(1, 10):
        start = int(str(d) * 300)
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(start, 10), base=10)
        try:
            action = owner.authorize_temporal_cell(
                owner.initial, steps=4, coordinate=150
            )
            x = start
            for t in range(4):
                y = x + _rev(x)
                z = y + _rev(y)
                if len(str(y)) == len(str(z)):
                    left = int(str(z)[150])
                    right = int(str(y)[150])
                    literal = tuple(int(left < right + b) for b in (0, 1))
                    assert action.next_quiet_borrow_response(t) == literal
                    carry = int(action.at(t + 1) > 9)
                    assert action.next_quiet_joint_xor_response(t) == tuple(
                        carry ^ b for b in literal
                    )
                x = y
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0


def test_guards_refuse_edge_overlap_and_mixed_core() -> None:
    start = int("1" * 401)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(start, 10), base=10)
    other_ledger = ResourceLedger()
    foreign = ReversePairQ19OutputOwner(other_ledger, digits_lsd(start, 10), base=10)
    try:
        with pytest.raises(UniformConeNotAuthorized, match="halo"):
            authorize_uniform_cone(owner, owner.initial, steps=10, coordinate=5)
        with pytest.raises(UniformConeNotAuthorized, match="halo"):
            authorize_uniform_cone(owner, owner.initial, steps=150, coordinate=200)
        with pytest.raises(ValueError):
            authorize_uniform_cone(foreign, owner.initial, steps=2, coordinate=200)
    finally:
        owner.dispose()
        foreign.dispose()
        assert ledger.entries == ledger.nodes == 0
        assert other_ledger.entries == other_ledger.nodes == 0

    start = int("1" * 100 + "2" * 100 + "1" * 100)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(start, 10), base=10)
    try:
        with pytest.raises(UniformConeNotAuthorized, match="not uniform"):
            owner.authorize_temporal_cell(owner.initial, steps=24, coordinate=90)
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_virtual_repeat_is_checked_once_and_never_claimed_reachable() -> None:
    # This only tests the spatial SLP guard on a symbolic repetition. It
    # deliberately never fabricates an issued temporal source occurrence.
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    try:
        long_word = owner.arena.repeat(owner.arena.terminal(6), 10**18)
        assert _same_symbol_range(owner, long_word, 1, 10**18 - 1, 6)
        assert not _same_symbol_range(owner, long_word, 1, 10**18 - 1, 8)
        assert _bulk_at(6, 0, 10**18) == _bulk_at(6, 0, 4 + (10**18 - 4) % 6)
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_asymmetric_eq_wire_and_unprotected_square_fail_closed() -> None:
    start = _word_from_pairs([2] + [9] * 150 + [18], Random(13))
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(start, 10), base=10)
    try:
        with pytest.raises(UniformConeNotAuthorized, match="asymmetric EQ"):
            owner.authorize_temporal_cell(owner.initial, steps=20, coordinate=80)
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_uniform_cell_records_are_live_owner_checked_observations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add import q19_uniform_cone

    start = int("1" * 400)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(start, 10), base=10)
    cert = owner.authorize_temporal_cell(owner.initial, steps=12, coordinate=200)
    assert cert.coefficient == _pair_at(start, 200)

    def no_rederivation(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("issued uniform observation re-derived its full halo")

    monkeypatch.setattr(q19_uniform_cone, "_derive_uniform_cone", no_rederivation)
    assert cert.coefficient == _pair_at(start, 200)
    with pytest.raises(ValueError, match="issued by a Q19 owner"):
        replace(cert, source_symbol=cert.source_symbol + 1)
    with pytest.raises(ValueError, match="issued by a Q19 owner"):
        CertifiedUniformCone(
            cert.source, owner, cert.coordinate, cert.steps, 0, 0, cert.halo
        )
    owner.dispose()
    assert ledger.entries == ledger.nodes == 0
    with pytest.raises(ValueError, match="disposed"):
        _ = cert.coefficient


def test_uniform_square_refuses_insufficient_remaining_halo() -> None:
    start = int("1" * 250)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(start, 10), base=10)
    try:
        action = owner.authorize_temporal_cell(owner.initial, steps=50, coordinate=125)
        with pytest.raises(UniformConeNotAuthorized, match="halo"):
            action.square(owner)
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_exhaustive_uniform_moore_closure() -> None:
    from number_compiler.sequences.reverse_add.q19_uniform_cone import (
        uniform_cone_moore_certificate,
    )

    proof = uniform_cone_moore_certificate()
    assert proof.admitted_entry_states == 20
    assert proof.distinct_future_states == 10
    assert proof.future_coefficients == tuple(range(0, 19, 2))
    assert set(proof.cycle_lengths) == {1, 2, 6}
    for initial in range(19):
        for c in range(2) if initial == 9 else (int(initial > 9),):
            target = _bulk_at(initial, c, 1)
            assert target in proof.future_coefficients
            assert _bulk_at(initial, c, 200) == (_bulk_at(target, int(target > 9), 199))
