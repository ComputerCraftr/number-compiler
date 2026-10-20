"""NC13: source-rooted border certificates and coupled GT/EQ/LT bank ports."""

from __future__ import annotations

import operator
from collections.abc import Callable, MutableMapping
from random import Random
from typing import cast

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.mixed_periodic_bank import (
    IncompleteMixedBorder,
    MixedPeriodicCore,
)
from number_compiler.sequences.reverse_add.q19_bank_boolean import (
    CoupledBooleanBankFrame,
)
from number_compiler.sequences.reverse_add.q19_border_control import (
    BoundaryControlNotAuthorized,
    CertifiedBorderGrowth,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.source_workspace import (
    ReverseSourceImageWorkspace,
)
from tests.support.reverse_add_sources import periodic_reverse_add_source


def _rev(x: int) -> int:
    return int(str(x)[::-1])


def _pair(number: int, index: int) -> int:
    digits = str(number)
    return int(digits[index]) + int(digits[-1 - index])


def _copied_border_with_word(
    record: CertifiedBorderGrowth, word: tuple[int, ...]
) -> CertifiedBorderGrowth:
    clone = object.__new__(CertifiedBorderGrowth)
    for attribute in (
        "owner",
        "source",
        "growth_word",
        "window_digits",
        "max_visited_states",
        "source_pair_inspections",
        "outer_pairs",
        "window_tiles",
        "physical_growth_certified",
        "full_integer_certified",
        "_seal",
    ):
        object.__setattr__(clone, attribute, getattr(record, attribute))
    object.__setattr__(clone, "growth_word", word)
    snapshot = cast(
        Callable[[], tuple[object, ...]], object.__getattribute__(clone, "_snapshot")
    )
    object.__setattr__(clone, "_binding", snapshot())
    return clone


def test_boolean_gt_eq_birth_and_f5_are_source_coupled() -> None:
    rng = Random(87011)
    checked = 0
    for _ in range(3000):
        period = tuple(rng.randrange(19) for _ in range(rng.randrange(1, 9)))
        try:
            core = MixedPeriodicCore(period)
            for growth in (0, 1):
                _, step = core.advance(growth)
                result = CoupledBooleanBankFrame.from_frame(period, step)
                with pytest.raises(TypeError):
                    operator.setitem(
                        cast(MutableMapping[str, tuple[int, ...]], result.target_bands),
                        "eq",
                        (),
                    )
                assert result.target == step.target
                assert result.carries == step.incoming
                assert result.reflected_xor == tuple(
                    left ^ right for left, right in step.incoming
                )
                assert result.pascal_parity == tuple(value % 2 for value in step.target)
                assert result.gt_high_birth == result.target_bands["gt_high"]
                assert result.eq_birth == result.target_bands["eq"]
                if growth:
                    assert result.shifted_growth_xor is not None
                    assert result.gt_high_from_lt_high is None
                    assert result.gt_high_from_eq is None
                else:
                    assert result.shifted_growth_xor is None
                    assert result.gt_high_from_lt_high is not None
                    assert result.gt_high_from_eq is not None
                for i, s in enumerate(step.target):
                    assert (
                        result.target_bands["lt_low"][i]
                        + result.target_bands["lt_high"][i]
                        + result.target_bands["eq"][i]
                        + result.target_bands["gt_low"][i]
                        + result.target_bands["gt_high"][i]
                        == 1
                    )
                    assert result.target_bands["f5"][i] == s % 5
                    eta = MixedPeriodicCore(step.target).ingresses()[i][1]
                    rho = int(s > 9 or (s == 9 and eta == 1))
                    expected = (
                        (0, 1) if step.borrow_identity_if_next_quiet[i] else (rho, rho)
                    )
                    assert result.borrow_transfer_if_next_quiet[i] == expected
                checked += 1
        except IncompleteMixedBorder:
            continue
    assert checked > 5000
    with pytest.raises(IncompleteMixedBorder):
        MixedPeriodicCore((9, 9, 9))


@pytest.mark.parametrize("period", [(5, 16), (0, 11), (5, 16, 2)])
def test_later_root_uses_authenticated_border_and_powered_boolean_bank(
    period: tuple[int, ...],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = periodic_reverse_add_source(period, seed=9610 + sum(period))
    width = len(period)
    coord = 201 - 201 % width
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        # The input to the bank is now an issued *later* S1, not owner.initial.
        source = owner.apply_pair_step(owner.initial)
        current = seed + _rev(seed)
        duration = 12
        growth: list[int] = []
        coefficients: list[int] = [_pair(current, coord)]
        for _ in range(duration):
            target = current + _rev(current)
            growth.append(int(len(str(target)) > len(str(current))))
            current = target
            coefficients.append(_pair(current, coord))

        def forbidden_pair_step(*args: object, **kwargs: object) -> object:
            raise AssertionError("composed border/bank observer ran Q19 again")

        with monkeypatch.context() as poison:
            poison.setattr(owner, "apply_pair_step", forbidden_pair_step)
            cert = owner.certify_border_growth(source, steps=duration, window_digits=6)
        assert cert.growth_word == tuple(growth)
        assert cert.final_width == len(str(current))
        assert (
            owner.audit_snapshot().issuance_registry.lookup_border(source, duration, 6)
            is cert
        )

        duplicate = owner.apply_pair_step(owner.initial)
        assert duplicate is source
        assert (
            owner.audit_snapshot().issuance_registry.lookup_border(
                duplicate, duration, 6
            )
            is cert
        )

        conflicting = type(source)(
            source.owner,
            source.root,
            source.temporal_steps,
            source.pair_width,
            source.output_width,
            source.growth,
            source.q19_domain,
            (source.q19_f9 + 1) % 9,
        )
        with pytest.raises(ValueError, match="different metadata"):
            owner.publish(conflicting)
        snapshot = owner.audit_snapshot()
        assert (
            snapshot.issued.payload_view.get((source.root, source.temporal_steps))
            is source
        )
        assert snapshot.issuance_registry.lookup_border(source, duration, 6) is cert

        monkeypatch.setattr(owner, "apply_pair_step", forbidden_pair_step)
        forged_word = (1 - cert.growth_word[0],) + cert.growth_word[1:]
        forged = _copied_border_with_word(cert, forged_word)
        with pytest.raises(ValueError, match="not retained"):
            forged.validate(owner, source)
        action = owner.authorize_controlled_gt_bank(
            source,
            steps=duration,
            coordinate=coord,
            period_size=width,
            growth_control=cert,
        )
        assert action.control_certified
        assert not action.full_integer_certified
        assert tuple(action.at(t) for t in range(duration + 1)) == tuple(coefficients)
        for tick in range(duration):
            packet = action.boolean_frame(tick)
            assert packet.target[coord % width] == coefficients[tick + 1]
            assert packet.target_bands["f5"][coord % width] == (
                coefficients[tick + 1] % 5
            )
        assert ledger.counters.get("reverse_q19_punctured_t4_applications", 0) == 0
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_width_published_from_border_without_physical_pair_steps(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = periodic_reverse_add_source((5, 16), seed=2001)
    final = seed
    for _ in range(16):
        final += _rev(final)
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, seed, 16)
    try:
        # The width producer must never request the completed Q19 image.
        def forbidden(*args: object, **kwargs: object) -> None:
            raise AssertionError("certified width incorrectly executed Q19")

        monkeypatch.setattr(workspace.adapter, "apply_composite", forbidden)
        assert workspace.width() == len(str(final))
        assert workspace.audit_snapshot().image is None
        assert ledger.counters["reverse_q19_border_width_publications"] == 1
        assert ledger.counters.get("reverse_q19_punctured_t4_applications", 0) == 0
    finally:
        workspace.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_196_long_border_refuses_unproved_128_step_growth_word() -> None:
    seed = 196
    for _ in range(79):
        seed += _rev(seed)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        with pytest.raises(BoundaryControlNotAuthorized):
            owner.certify_border_growth(
                owner.initial, steps=128, window_digits=4, max_states=4096
            )
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_warm_border_certificate_preserves_source_probe_budget() -> None:
    seed = 874321
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=2, window_digits=1, max_states=2
        )
        assert certificate.max_visited_states == 1
        assert certificate.source_pair_inspections == 2
        warm_inspections = ledger.counters[
            "reverse_q19_border_control_source_pair_inspections"
        ]
        with pytest.raises(BoundaryControlNotAuthorized):
            owner.certify_border_growth(
                owner.initial, steps=2, window_digits=1, max_states=1
            )
        assert (
            ledger.counters["reverse_q19_border_control_source_pair_inspections"]
            == warm_inspections
        )
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0

    cold_ledger = ResourceLedger()
    cold_owner = ReversePairQ19OutputOwner(cold_ledger, digits_lsd(seed, 10), base=10)
    try:
        with pytest.raises(BoundaryControlNotAuthorized):
            cold_owner.certify_border_growth(
                cold_owner.initial, steps=2, window_digits=1, max_states=1
            )
        assert (
            cold_ledger.counters["reverse_q19_border_control_source_pair_inspections"]
            == 1
        )
    finally:
        cold_owner.dispose()
        assert cold_ledger.entries == cold_ledger.nodes == 0


def test_border_certificate_rejects_mutated_nested_window_tile_fields() -> None:
    seed = 874321
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=2, window_digits=1, max_states=2
        )
        tile = next(tile for tile in certificate.window_tiles if tile is not None)
        mutations = (
            ("k", tile.k, tile.k + 1),
            ("high", tile.high, tile.high + 1),
            ("low", tile.low, (tile.low + 1) % (10**tile.k)),
        )
        for field, original, changed in mutations:
            object.__setattr__(tile, field, changed)
            try:
                with pytest.raises(
                    ValueError, match="border growth certificate was changed"
                ):
                    certificate.validate(owner, owner.initial)
            finally:
                object.__setattr__(tile, field, original)
        certificate.validate(owner, owner.initial)
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0
