"""Exact factored transport, cancellation, and nonmaterializing controls."""

from itertools import product
from typing import Never

import pytest

from devtools.proofs import exact_oracle
from number_compiler.arithmetic.automata import program_word as words
from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.exact_tree_context import (
    ExactTreeConstructionForbidden,
    source_reads_only,
)
from number_compiler.arithmetic.fields.radix import reverse_pair_sums
from number_compiler.sequences.reverse_add import factored_carrier as module
from number_compiler.sequences.reverse_add.factored_carrier import (
    FactoredReverseCarrier,
    OutputResidualID,
    TemporalCell,
)
from number_compiler.sequences.reverse_add.factored_power import FactoredTemporalPower


@pytest.mark.parametrize("seed", (1, 1111, 196))
def test_three_planes_agree_with_independent_successors(seed: int) -> None:
    carrier = FactoredReverseCarrier()
    with exact_oracle():
        field = reverse_pair_sums(seed, 10)
        cell = carrier.source(field)
        for _ in range(16):
            field, growth = pair_step(field, 10)
            cell, actual = carrier.successor(cell)
            assert actual == growth
            assert carrier.decode(cell) == field


@pytest.mark.parametrize("length", (1, 4, 1_000_000, 10**100))
def test_uniform_control_uses_only_small_coordinate_atoms(
    length: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    carrier = FactoredReverseCarrier()
    q = carrier.uniform(CarryFn.CONST0, 2, 0, length)
    run = words.run

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("successor materialized or decoded a digit/pair field")

    def bounded_run(symbol: int, count: int) -> words.CanonicalWord:
        assert 0 <= symbol < 5
        return run(symbol, count)

    monkeypatch.setattr(carrier, "source", forbidden)
    monkeypatch.setattr(carrier, "decode", forbidden)
    monkeypatch.setattr(carrier.planes, "from_values", forbidden)
    monkeypatch.setattr(module, "decimal_factored_value", forbidden)
    monkeypatch.setattr(words, "from_values", forbidden)
    monkeypatch.setattr(words, "run", bounded_run)
    for expected in ((0, 4, 0), (0, 3, 1), (2, 1, 1)):
        q, growth = carrier.successor(q)
        assert growth == 0
        assert (
            tuple(carrier.planes.atom(p, 0) for p in (q.domain, q.f5, q.half))
            == expected
        )
        assert all(
            carrier.planes.metrics(p)["nodes"] == 1 for p in (q.domain, q.f5, q.half)
        )
    q, growth = carrier.successor(q)
    assert growth == 1
    for i in (0, length):
        assert tuple(carrier.planes.atom(p, i) for p in (q.domain, q.f5, q.half)) == (
            0,
            2,
            1,
        )
    if length > 1:
        assert tuple(
            carrier.planes.atom(p, length // 2) for p in (q.domain, q.f5, q.half)
        ) == (2, 4, 0)
    assert all(
        carrier.planes.metrics(p)["nodes"] <= 4 for p in (q.domain, q.f5, q.half)
    )


def test_output_normal_form_can_merge_distinct_input_carriers() -> None:
    carrier = FactoredReverseCarrier()
    found: dict[OutputResidualID, tuple[int, ...]] = {}
    with exact_oracle():
        for a, b in product(range(19), repeat=2):
            source = (a, b, b, a)
            q = carrier.source(source)
            out, _ = carrier.successor(q)
            residual = carrier.residual(out)
            prior = found.get(residual)
            if prior is not None and prior != source:
                assert carrier.source(prior) != q
                assert pair_step(prior, 10)[0] == pair_step(source, 10)[0]
                return
            found[residual] = source
    pytest.fail("finite cancellation control found no output merge")


def test_temporal_squaring_matches_stepwise_execution() -> None:
    carrier = FactoredReverseCarrier()
    with exact_oracle():
        field = reverse_pair_sums(196, 10)
        source = carrier.source(field)
        power = FactoredTemporalPower(carrier)
        for event in range(1, 33):
            field, _ = pair_step(field, 10)
            if event in (1, 2, 4, 8, 16, 32):
                out = power.advance(source, event)
                assert carrier.decode(out) == field
        assert carrier.successor_evaluations == 32
        before = carrier.successor_evaluations
        assert power.advance(source, 32) == out
        assert carrier.successor_evaluations == before
        assert power.cache_hits > 0
        action = power.block(source, 32).action
        assert action.linear.growths == carrier.planes.resolve(out.f5).length - 3
        assert action.linear.growths > 5
        assert action.linear.frobenius_factors()


def test_invalid_or_foreign_channels_and_point_scope_are_rejected() -> None:
    carrier = FactoredReverseCarrier()
    q = carrier.uniform(CarryFn.CONST0, 2, 0, 4)
    other = FactoredReverseCarrier().uniform(CarryFn.CONST0, 2, 0, 4)
    for bad in (
        TemporalCell(q.domain, other.f5, q.half),
        TemporalCell(q.domain, q.half, q.f5),
    ):
        with pytest.raises(ValueError):
            carrier.successor(bad)
    bad = TemporalCell(carrier.planes.constant("domain", 1, 4), q.f5, q.half)
    with pytest.raises(ValueError, match="disagree"):
        carrier.successor(bad)
    with pytest.raises(ValueError, match="symmetric"):
        carrier.source((2, 4))
    with pytest.raises(ValueError, match="center"):
        carrier.source((1,))
    with pytest.raises(ExactTreeConstructionForbidden):
        source_reads_only(carrier.successor)(q)
    carrier.planes.max_work = 1
    with pytest.raises(BlockContextBudgetExceeded):
        carrier.successor(q)
    assert not carrier.planes._gates


def test_independent_observations_release_their_workspaces() -> None:
    carrier = FactoredReverseCarrier(max_work=12)
    q = carrier.uniform(CarryFn.CONST0, 2, 0, 4)
    for _ in range(30):
        assert carrier.decode(q) == (2, 2, 2, 2)
        assert carrier.residual(q).f5 == q.f5
        assert carrier.planes.work == 0
        assert not carrier.planes._gates


def test_checkpoint_preserves_separate_planes_without_reencoding() -> None:
    import json

    from devtools.proofs.reverse_plane_checkpoint import export_planes, import_planes

    carrier = FactoredReverseCarrier()
    cell = carrier.uniform(CarryFn.CONST0, 2, 0, 10**100)
    for _ in range(4):
        cell, _ = carrier.successor(cell)
    archive = json.loads(json.dumps(export_planes(carrier, cell)))
    restored = import_planes(carrier, archive)
    assert restored == cell
    assert len(archive["nodes"]) < 20
    archive["roots"][0] = len(archive["nodes"])
    with pytest.raises(ValueError, match="root"):
        import_planes(carrier, archive)


def test_stale_rope_memos_are_removed_without_invalidating_live_hits() -> None:
    import gc

    source = words.from_values((0, 1, 0, 2))
    source_id = source.node_id
    leaf = words.slice_runs(source, 0, 1)
    key = source_id, 0, 1
    words.prune_stale_program_word_memos()
    assert words._SLICE[key] is leaf
    del source
    gc.collect()
    words.prune_stale_program_word_memos()
    assert key not in words._SLICE
    assert leaf.symbol == 0
