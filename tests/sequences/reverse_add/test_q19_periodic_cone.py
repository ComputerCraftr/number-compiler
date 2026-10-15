"""Guarded mixed reset/GT/EQ periodic branch tests, never root authority."""

from __future__ import annotations

from dataclasses import replace
from random import Random

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.q19_periodic_cone import (
    CertifiedUniformizingCone,
    _match_region,
    _step,
    authorize_uniformizing_cone,
)
from number_compiler.sequences.reverse_add.q19_uniform_cone import (
    UniformConeNotAuthorized,
)


def _rev(value: int) -> int:
    return int(str(value)[::-1])


def _pair_at(value: int, index: int) -> int:
    word = str(value)
    return int(word[index]) + int(word[-index - 1])


def _from_half_sums(half: list[int], rng: Random) -> int:
    low, high = [], []
    for index, s in enumerate(half):
        lo, hi = max(0, s - 9), min(9, s)
        if index == 0:
            hi = min(hi, s - 1)
        a = rng.randint(lo, hi)
        low.append(a)
        high.append(s - a)
    return int("".join(map(str, high)) + "".join(map(str, reversed(low))))


def test_mixed_lt_gt_uniformizing_source_action_power_without_q19_kernels(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    rng = Random(20261014)
    for period in ((0, 11), (1, 12), (3, 14), (6, 17), (8, 8)):
        half = [rng.randrange(1, 19)]
        half += [rng.randrange(19) for _ in range(99)]
        half += list(period) * 400
        half += [rng.randrange(19) for _ in range(100)]
        x = _from_half_sums(half, rng)
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(x, 10), base=10)
        try:

            def poisoned(*_args: object, **_kwargs: object) -> None:
                raise AssertionError("mixed source authorization replayed Q19")

            monkeypatch.setattr(owner, "apply_pair_step", poisoned)
            monkeypatch.setattr(owner, "apply_punctured_pair_block", poisoned)
            cert = owner.authorize_mixed_temporal_cell(
                owner.initial, steps=40, coordinate=500
            ).square(owner)
            assert cert.steps == 80 and cert.period == period
            assert cert.uniform_successor == _step(period, 0)[0]
            for t in range(81):
                assert cert.at(t) == _pair_at(x, 500), (period, t)
                if t < 80:
                    x += _rev(x)
            assert ledger.counters.get("reverse_q19_punctured_t4_applications", 0) == 0
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0


def test_mixed_source_refuses_unclosed_growth_and_mismatched_period() -> None:
    rng = Random(32)
    for period in ((0, 10, 11), (0, 18)):
        half = [rng.randrange(1, 19)]
        half += [rng.randrange(19) for _ in range(99)]
        half += list(period) * 310
        half += [rng.randrange(19) for _ in range(70)]
        x = _from_half_sums(half, rng)
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(x, 10), base=10)
        try:
            with pytest.raises(UniformConeNotAuthorized):
                authorize_uniformizing_cone(
                    owner,
                    owner.initial,
                    steps=12,
                    coordinate=450,
                    period_size=len(period),
                )
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0


def test_periodic_match_exact_slp_pumping_and_corrupted_leaf() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    try:
        root = owner.arena.repeat(
            owner.arena.concat(owner.arena.terminal(0), owner.arena.terminal(11)),
            10**18,
        )
        assert _match_region(owner, root, 32, 2 * 10**18 - 32, (0, 11))
        assert not _match_region(owner, root, 32, 2 * 10**18 - 32, (11, 0))
        corrupt = owner.arena.concat(root, owner.arena.terminal(14))
        assert not _match_region(owner, corrupt, 0, 2 * 10**18 + 1, (0, 11))
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_mixed_cell_records_are_live_owner_checked_observations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add import q19_periodic_cone

    rng = Random(808)
    half = [rng.randrange(1, 19)]
    half += [rng.randrange(19) for _ in range(99)]
    half += [0, 11] * 400
    half += [rng.randrange(19) for _ in range(100)]
    source_value = _from_half_sums(half, rng)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(source_value, 10), base=10)
    cert = authorize_uniformizing_cone(
        owner, owner.initial, steps=20, coordinate=500, period_size=2
    )
    # This test checks owner binding and metadata forgery. Exact powered
    # trajectory values are checked by the preceding arithmetic regression.
    assert cert.period == (0, 11) and cert.uniform_successor == 2

    def no_rederivation(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("issued mixed observation re-derived its full halo")

    monkeypatch.setattr(q19_periodic_cone, "_derive_uniformizing_cone", no_rederivation)
    monkeypatch.setattr(q19_periodic_cone, "_match_region", no_rederivation)
    assert cert.at(20) == 4
    with pytest.raises(ValueError, match="issued by a Q19 owner"):
        replace(cert, uniform_successor=cert.uniform_successor ^ 2)
    with pytest.raises(ValueError, match="issued by a Q19 owner"):
        CertifiedUniformizingCone(
            cert.source,
            owner,
            cert.coordinate,
            cert.steps,
            cert.period,
            cert.uniform_successor + 1,
            cert.halo,
        )
    owner.dispose()
    assert ledger.entries == ledger.nodes == 0
    with pytest.raises(ValueError, match="disposed"):
        cert.at(1)
