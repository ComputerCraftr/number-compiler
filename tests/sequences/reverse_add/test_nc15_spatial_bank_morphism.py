"""Independent arithmetic / authorization gates for reverse/add's bank morphism."""

from __future__ import annotations

import json
import sys
from collections.abc import Callable
from typing import cast

import pytest

from number_compiler.api import cli
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.fields.walsh import walsh64_mod5
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.reverse_add.mixed_periodic_bank import (
    IncompleteMixedBorder,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.q19_spatial_bank_morphism import (
    SpatialBankProgram,
)
from number_compiler.sequences.reverse_add.q19_uniform_cone import (
    UniformConeNotAuthorized,
)
from tests.support.reverse_add_sources import periodic_reverse_add_source


def _rev(x: int) -> int:
    return int(str(x)[::-1])


def _trace(x: int, steps: int) -> tuple[list[int], tuple[int, ...]]:
    values = [x]
    bits: list[int] = []
    for _ in range(steps):
        nxt = x + _rev(x)
        bits.append(int(len(str(nxt)) > len(str(x))))
        values.append(nxt)
        x = nxt
    return values, tuple(bits)


def _pair(value: int, index: int) -> int:
    s = str(value)
    return int(s[-1 - index]) + int(s[index])


@pytest.mark.parametrize(
    "period",
    [(0, 11), (2, 14), (5, 16), (7, 14), (5, 16, 2)],
)
def test_morphisms_predict_all_protected_output_positions(
    period: tuple[int, ...], monkeypatch: pytest.MonkeyPatch
) -> None:
    seed = periodic_reverse_add_source(period, seed=9302 + sum(period))
    depth = 12
    values, bits = _trace(seed, depth)
    start = 200 - 200 % len(period)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        cert = owner.certify_border_growth(owner.initial, steps=depth, window_digits=6)
        assert cert.growth_word == bits

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("spatial output morphism executed physical Q19")

        monkeypatch.setattr(owner, "apply_pair_step", forbidden)
        monkeypatch.setattr(owner, "apply_punctured_pair_block", forbidden)
        action = owner.authorize_spatial_bank_morphism(
            owner.initial,
            steps=depth,
            start=start,
            count=64,
            period_size=len(period),
            growth_control=cert,
        )
        assert action.control_certified
        assert not action.complete_integer_certified
        assert action.final_width_if_certified == len(str(values[-1]))
        assert action.residue99().target_mod99 == values[-1] % 99
        expected = tuple(_pair(values[-1], start + i) for i in range(64))
        assert action.output_word("coefficient").slice(0, 64) == expected
        assert action.output_word("f5").slice(0, 64) == tuple(
            value % 5 for value in expected
        )
        assert (
            sum(
                action.counts(ch)
                for ch in ("lt_low", "lt_high", "eq", "gt_low", "gt_high")
            )
            == 64
        )
        predicates: tuple[tuple[str, Callable[[int], bool]], ...] = (
            ("lt_low", lambda s: s <= 4),
            ("lt_high", lambda s: 5 <= s <= 8),
            ("eq", lambda s: s == 9),
            ("gt_low", lambda s: 10 <= s <= 14),
            ("gt_high", lambda s: 15 <= s <= 18),
        )
        for channel, test in predicates:
            expected_bits = tuple(int(test(s)) for s in expected)
            word = action.output_word(channel)
            assert word.slice(0, 64) == expected_bits
            assert word.counts() == sum(expected_bits)
            assert action.walsh64_mod5(channel) == walsh64_mod5(
                sum(x << i for i, x in enumerate(expected_bits))
            )
        # Check the independent temporal prefix output from the SAME bank.
        for t in (0, 1, 2, 7, 12):
            word = action.output_word("coefficient", depth=t)
            assert word.slice(0, 20) == tuple(
                _pair(values[t], start + i) for i in range(20)
            )
        assert ledger.counters.get("reverse_q19_punctured_t4_applications", 0) == 0
        assert ledger.counters.get("reverse_q19_primitive_pair_applications", 0) == 0
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_no_growth_or_mod99_authority_forgery_for_nonperiodic_source() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    try:
        with pytest.raises((UniformConeNotAuthorized, ValueError)):
            owner.authorize_spatial_bank_morphism(
                owner.initial,
                steps=9,
                start=0,
                count=16,
                growth_control=(0, 1, 0, 0, 1, 0, 1, 0, 1),
                period_size=2,
            )
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0
    # Same residue and parity do not select the same GT bank or growth.
    values, growth = _trace(196, 10)
    assert values[3] % 99 == values[9] % 99 == 11
    assert growth[3] != growth[9]


def test_conditional_control_stays_conditional_and_refuses_false_period() -> None:
    seed = periodic_reverse_add_source((5, 16), seed=9323)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        values, bits = _trace(seed, 12)
        conditional = owner.authorize_spatial_bank_morphism(
            owner.initial,
            steps=12,
            start=200,
            count=64,
            growth_control=bits,
            period_size=2,
        )
        assert not conditional.control_certified
        assert conditional.final_width_if_certified is None
        assert conditional.residue99().target_mod99 == values[-1] % 99
        with pytest.raises((UniformConeNotAuthorized, IncompleteMixedBorder)):
            owner.authorize_spatial_bank_morphism(
                owner.initial,
                steps=12,
                start=200,
                count=64,
                growth_control=bits,
                period_size=3,
            )
        with pytest.raises(UniformConeNotAuthorized):
            owner.authorize_spatial_bank_morphism(
                owner.initial,
                steps=12,
                start=200,
                count=220,
                growth_control=bits,
                period_size=2,
            )
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_spatial_program_symbolically_repeats_and_bounds_walsh() -> None:
    p = SpatialBankProgram((0, 1, 1, 0, 1), 10**18 + 3)
    assert p.nodes <= 3
    assert p.counts() == 3 * (p.length // 5) + sum(p.suffix)
    assert p.at(10**18) == 0
    assert p.walsh64_mod5(1) == walsh64_mod5(sum(p.at(1 + i) << i for i in range(64)))
    with pytest.raises(IndexError):
        p.at(p.length)
    with pytest.raises(ValueError):
        SpatialBankProgram((0, 2), 64).walsh64_mod5(0)


def test_cli_spatial_bank_morphism_is_pointed_and_resource_safe(
    capsys: pytest.CaptureFixture[str],
) -> None:
    seed = periodic_reverse_add_source((5, 16), seed=9323)
    args = [
        "reverse-add",
        "--seed",
        str(seed),
        "--nth",
        "16",
        "--no-value",
        "--info",
        "spatial.bank-morphism",
        "--spatial-pair-bank-position",
        "200",
        "--spatial-bank-morphism-count",
        "48",
        "--temporal-grammar-period",
        "2",
        "--format",
        "json",
    ]
    assert cli.main(args) == 0
    data = json.loads(capsys.readouterr().out)
    packet = data["info"]["spatial.bank-morphism"]
    assert packet["control_certified"] is True
    assert packet["complete_integer_certified"] is False
    assert packet["pair_count"] == 48
    assert packet["mod99"] == _trace(seed, 16)[0][-1] % 99
    assert data["value"] is None


def test_morphism_rejects_tampered_halo_and_source_binding() -> None:
    seed = periodic_reverse_add_source((5, 16), seed=9323)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        bits = _trace(seed, 12)[1]
        morph = owner.authorize_spatial_bank_morphism(
            owner.initial,
            steps=12,
            start=200,
            count=64,
            period_size=2,
            growth_control=bits,
        )
        payload = audit_registered_payloads(ledger)
        assert (payload.unknown_payloads, payload.forbidden_future_payloads) == (
            0,
            0,
        )
        with pytest.raises(ValueError, match="issued halo"):
            type(morph)(morph.action, morph.start, morph.count, 0)
        object.__setattr__(morph, "count", 300)
        with pytest.raises(ValueError, match="was changed"):
            morph.output_word("gt_high")
        with pytest.raises(ValueError, match="was changed"):
            morph.residue99()

        # A forged object can copy the private seal and recompute its local
        # binding, but the owner registry only retains the exact issued window.
        forged = object.__new__(type(morph))
        for name in (
            "action",
            "start",
            "count",
            "halo",
            "_seal",
            "_registry_key",
        ):
            object.__setattr__(forged, name, getattr(morph, name))
        object.__setattr__(forged, "start", morph.start + 1)
        snapshot_method = cast(
            Callable[[], tuple[object, ...]],
            object.__getattribute__(forged, "_snapshot"),
        )
        object.__setattr__(forged, "_binding", snapshot_method())
        with pytest.raises(ValueError, match="not retained by this Q19 owner"):
            forged.output_word("coefficient")

        owner.dispose()
        with pytest.raises(ValueError, match="disposed Q19 pair output owner"):
            morph.output_word("coefficient")
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_failed_spatial_window_publication_releases_both_records(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = periodic_reverse_add_source((5, 16), seed=9323)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        bits = _trace(seed, 12)[1]

        def fail_after_retention(_window: object) -> None:
            raise RuntimeError("forced spatial window publication failure")

        monkeypatch.setattr(
            owner.audit_snapshot().issuance_registry,
            "validate_spatial_bank_window",
            fail_after_retention,
        )
        with pytest.raises(RuntimeError, match="forced spatial window"):
            owner.authorize_spatial_bank_morphism(
                owner.initial,
                steps=12,
                start=200,
                count=64,
                period_size=2,
                growth_control=bits,
            )
        snapshot = owner.audit_snapshot()
        assert not snapshot.spatial_bank_windows.payload_view
        assert snapshot.issuance_registry.spatial_bank_window_next == 0
        assert not snapshot.controlled_gt_banks.payload_view
        assert snapshot.issuance_registry.controlled_gt_bank_next == 0
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_twenty_coefficient_gt_bank_period_is_exact_not_mask_only() -> None:
    """Period 20 retains all F5 coefficient lifts, not just 20 GT-high bits."""
    previous = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(20000)
    try:
        period = (
            7,
            14,
            8,
            17,
            0,
            11,
            5,
            16,
            3,
            13,
            6,
            12,
            1,
            10,
            2,
            15,
            4,
            18,
            8,
            14,
        )
        seed = periodic_reverse_add_source(period, seed=2020)
        values, bits = _trace(seed, 8)
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
        try:
            cert = owner.certify_border_growth(owner.initial, steps=8, window_digits=6)
            assert cert.growth_word == bits
            morph = owner.authorize_spatial_bank_morphism(
                owner.initial,
                steps=8,
                start=400,
                count=64,
                period_size=20,
                growth_control=cert,
                max_states=512,
            )
            assert morph.output_word("coefficient").slice(0, 64) == tuple(
                _pair(values[-1], 400 + i) for i in range(64)
            )
            assert morph.control_certified
            assert morph.output_word("coefficient").nodes <= 3
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0
    finally:
        sys.set_int_max_str_digits(previous)


def test_later_issued_q19_root_authenticates_entire_spatial_region(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = periodic_reverse_add_source((5, 16), seed=9626)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        issued = owner.apply_pair_step(owner.initial)
        current = seed + _rev(seed)
        values, bits = _trace(current, 12)
        cert = owner.certify_border_growth(issued, steps=12, window_digits=6)
        assert cert.growth_word == bits

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("later-root bank executed a Q19 successor")

        monkeypatch.setattr(owner, "apply_pair_step", forbidden)
        monkeypatch.setattr(owner, "apply_punctured_pair_block", forbidden)
        morph = owner.authorize_spatial_bank_morphism(
            issued,
            steps=12,
            start=200,
            count=64,
            period_size=2,
            growth_control=cert,
        )
        assert morph.control_certified
        assert morph.output_word("coefficient").slice(0, 64) == tuple(
            _pair(values[-1], 200 + i) for i in range(64)
        )
        assert morph.residue99().target_mod99 == values[-1] % 99
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0
