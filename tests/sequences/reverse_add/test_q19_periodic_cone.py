"""Guarded mixed reset/GT/EQ periodic branch tests, never root authority."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace
from random import Random
from typing import cast

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add import q19_periodic_cone
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.q19_periodic_cone import (
    CertifiedUniformizingCone,
    authorize_uniformizing_cone,
)
from number_compiler.sequences.reverse_add.q19_uniform_cone import (
    UniformConeNotAuthorized,
)
from tests.support.private_attributes import private_test_attribute

match_region = cast(
    Callable[[ReversePairQ19OutputOwner, int, int, int, tuple[int, ...]], bool],
    private_test_attribute(q19_periodic_cone, "_match_region"),
)
periodic_step = cast(
    Callable[[tuple[int, ...], int], tuple[int, ...]],
    private_test_attribute(q19_periodic_cone, "_step"),
)


def _rev(value: int) -> int:
    return int(str(value)[::-1])


def _pair_at(value: int, index: int) -> int:
    word = str(value)
    return int(word[index]) + int(word[-index - 1])


def _from_half_sums(half: list[int], rng: Random) -> int:
    low: list[int] = []
    high: list[int] = []
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
            assert cert.uniform_successor == periodic_step(period, 0)[0]
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
        assert match_region(owner, root, 32, 2 * 10**18 - 32, (0, 11))
        assert not match_region(owner, root, 32, 2 * 10**18 - 32, (11, 0))
        corrupt = owner.arena.concat(root, owner.arena.terminal(14))
        assert not match_region(owner, corrupt, 0, 2 * 10**18 + 1, (0, 11))
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_periodic_guard_uses_primitive_motif_across_reflected_seam(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(123321, 10), base=10)
    original = match_region
    observed: list[int] = []

    def record_match(
        source_owner: ReversePairQ19OutputOwner,
        root: int,
        lo: int,
        hi: int,
        pattern: tuple[int, ...],
    ) -> bool:
        observed.append(len(pattern))
        return original(source_owner, root, lo, hi, pattern)

    try:
        monkeypatch.setattr(q19_periodic_cone, "_match_region", record_match)
        pattern = (2, 4, 6, 6, 4, 2)
        short = q19_periodic_cone.periodic_guard(owner, owner.initial, 0, 6, pattern)
        observed.clear()
        repeated = q19_periodic_cone.periodic_guard(
            owner, owner.initial, 0, 6, pattern * 10
        )
        assert short and repeated
        assert observed == [6, 6]
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_mixed_cell_records_are_live_owner_checked_observations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
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


def _periodic_source(repeats: int) -> tuple[int, ...]:
    half = (1, 2) * repeats + (1,)
    return half + half[-2::-1]


def test_rotated_reflected_period_shares_the_checked_source_fold() -> None:
    from number_compiler.resources.metric_keys import reverse_add as metric_keys

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, _periodic_source(96), base=10)
    key = metric_keys.REVERSE_Q19_PERIODIC_GUARD_SLP_NODE_VISITS
    try:
        width = owner.initial.pair_width
        half = (width + 1) // 2
        assert match_region(owner, owner.initial.root, 0, half, (2, 4))
        assert match_region(owner, owner.initial.root, 0, width - half, (2, 4))
        separate = ledger.counters[key]
        assert q19_periodic_cone.periodic_guard(
            owner, owner.initial, 0, width, (2, 4, 2, 4)
        )
        assert ledger.counters[key] - separate == separate // 2
        assert not q19_periodic_cone.periodic_guard(
            owner, owner.initial, 0, width, (4, 2)
        )
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize("cut", [0, 1, 2, 7, 15])
@pytest.mark.parametrize("pattern", [(2, 4), (4, 2), (2, 4, 2, 4), (2, 6)])
def test_reflected_period_guards_match_literal_at_each_entry_phase(
    cut: int, pattern: tuple[int, ...]
) -> None:
    digits = _periodic_source(8)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits, base=10)
    try:
        width = owner.initial.pair_width
        stop = width - cut
        pair_sums = tuple(digits[i] + digits[width - i - 1] for i in range(width))
        expected = all(
            pair_sums[i] == pattern[i % len(pattern)] for i in range(cut, stop)
        )
        assert (
            q19_periodic_cone.periodic_guard(owner, owner.initial, cut, stop, pattern)
            is expected
        )
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_rotated_guard_capacity_miss_keeps_exact_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from number_compiler.resources.metric_keys import reverse_add as metric_keys

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, _periodic_source(16), base=10)
    original = ResourceLedger.check_capacity

    def refuse_optional(
        candidate: ResourceLedger, *, entries: int = 0, nodes: int = 0
    ) -> None:
        if candidate is ledger and entries and nodes:
            raise BlockContextBudgetExceeded("optional rotated matcher capacity")
        original(candidate, entries=entries, nodes=nodes)

    try:
        monkeypatch.setattr(ResourceLedger, "check_capacity", refuse_optional)
        assert q19_periodic_cone.periodic_guard(
            owner, owner.initial, 0, owner.initial.pair_width, (2, 4)
        )
        visits = ledger.counters[metric_keys.REVERSE_Q19_PERIODIC_GUARD_SLP_NODE_VISITS]
        assert visits > 0 and visits % 2 == 0
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0
