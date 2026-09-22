"""Exact factored transport, cancellation, and nonmaterializing controls."""

from itertools import product
from typing import Never

import pytest

from devtools.experiments.reverse_add import factored_carrier as module
from devtools.experiments.reverse_add.factored_carrier import (
    FactoredReverseCarrier,
    OutputResidualID,
    TemporalCell,
)
from devtools.experiments.reverse_add.factored_power import FactoredTemporalPower
from devtools.experiments.reverse_add.factored_planes import PlaneAlgebra, PlaneGate
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


@pytest.mark.parametrize("seed", (1, 18, 196, 909))
def test_endpoint_demand_skips_historical_affine_composition_but_not_source_steps(
    seed: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    carrier = FactoredReverseCarrier()
    with exact_oracle():
        field = reverse_pair_sums(seed, 10)
        source = carrier.source(field)
        expected = field
        for _ in range(16):
            expected, _ = pair_step(expected, 10)
        power = FactoredTemporalPower(carrier)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("endpoint demand composed historical F5 forcing")

        with monkeypatch.context() as patch:
            patch.setattr(power, "_compose", forbidden)
            endpoint = power.advance(source, 16)
            assert carrier.decode(endpoint) == expected
            assert power.advance(source, 16) is endpoint
        assert power.compositions == 0
        assert not power._memo
        assert power._endpoint_memo
        assert carrier.successor_evaluations == 16

        # An endpoint-only cache hit cannot stand in for a complete action.
        complete = power.block(source, 16)
        assert complete.output == endpoint
        assert power.compositions > 0
        assert (
            complete.action.apply(
                power._pad(source.f5, carrier.planes.resolve(endpoint.f5).length),
                shift=carrier.planes.shift,
                add=carrier._add,
                scale=carrier._scale,
            )
            == endpoint.f5
        )
        power.clear()
        assert not power._memo and not power._endpoint_memo


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


def test_gate_bisimulation_returns_existing_projection_without_traversal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    planes = PlaneAlgebra()
    values = tuple(i % 5 for i in range(1024))
    source = planes.from_values("f5", values)
    noise = planes.from_values("bool", tuple(i % 2 for i in range(1024)))
    gate = PlaneGate.build("left", ("f5", "bool"), "f5", lambda x, _y: x)
    renamed = PlaneGate("another-name", gate.inputs, gate.output, gate.table)
    assert gate == renamed and hash(gate) == hash(renamed)

    def forbidden(*args: object) -> Never:
        raise AssertionError("projection rebuilt or decoded an existing subtree")

    with monkeypatch.context() as patch:
        patch.setattr(words, "concat", forbidden)
        patch.setattr(PlaneGate, "evaluate", forbidden)
        assert planes.apply(gate, source, noise) is source
        assert planes.apply(renamed, source, noise) is source
    assert planes.total_work <= 2
    before = planes.total_work
    with monkeypatch.context() as patch:
        patch.setattr(PlaneGate, "evaluate", forbidden)
        clipped = planes.slice(source, 7, 997)
    assert planes.total_work - before <= 12 * len(values).bit_length()
    assert tuple(planes.atom(clipped, i) for i in range(997)) == values[7:1004]


def test_diagonal_bisimulation_preserves_undefined_inputs_and_source_authority() -> (
    None
):
    planes = PlaneAlgebra()
    source = planes.from_values("f5", (0, 1, 2, 3, 4) * 100)
    gate = PlaneGate.build(
        "partial-equality", ("f5", "f5"), "bool", lambda a, b: 0 if a == b else None
    )
    result = planes.apply(gate, source, source)
    assert planes.resolve(result).symbol == 0
    assert planes.total_work <= 6
    other = planes.from_values("f5", (1, 2, 3, 4, 0) * 100)
    with pytest.raises(ValueError, match="undefined"):
        planes.apply(gate, source, other)
    foreign = PlaneAlgebra().from_values("f5", (0, 1, 2, 3, 4) * 100)
    with pytest.raises(ValueError, match="foreign"):
        planes.apply(gate, source, foreign)


def test_all_partial_boolean_tables_preserve_every_cofactor() -> None:
    planes = PlaneAlgebra(max_cofactors=2)
    inputs = ((0, 0, 0, 0), (1, 1, 1, 1), (0, 1, 0, 1), (0, 0, 1, 1))
    roots = [planes.from_values("bool", value) for value in inputs]
    for table in product((None, 0, 1), repeat=4):
        gate = PlaneGate("exhaustive-partial", ("bool", "bool"), "bool", table)
        for i, left in enumerate(inputs):
            for j, right in enumerate(inputs):
                expected = tuple(
                    table[2 * a + b] for a, b in zip(left, right, strict=True)
                )
                try:
                    if None in expected:
                        with pytest.raises(ValueError, match="undefined"):
                            planes.apply(gate, roots[i], roots[j])
                    else:
                        output = planes.apply(gate, roots[i], roots[j])
                        assert (
                            tuple(planes.atom(output, k) for k in range(4)) == expected
                        )
                finally:
                    planes.clear_work()
                assert len(planes._cofactors) <= 2
    assert planes.cofactor_evictions > 0
    assert planes.cofactor_cells > 0


def test_bisimulation_catalog_bypass_and_compile_budget() -> None:
    planes = PlaneAlgebra(max_cofactors=0)
    source = planes.from_values("f5", (0, 1, 2, 3))
    zero = planes.constant("f5", 0, 4)
    gate = PlaneGate.build("sum", ("f5", "f5"), "f5", lambda a, b: (a + b) % 5)
    assert planes.apply(gate, source, zero) is source
    assert not planes._cofactors
    assert planes.cofactor_cells == 5
    planes.clear_work()
    planes.max_work = 1
    with pytest.raises(BlockContextBudgetExceeded):
        planes.apply(gate, source, zero)
    assert planes.work == 1
    assert not planes._cofactors
    planes.clear_work()
    assert not planes._gates


def test_automatic_memo_cleanup_does_not_rescan_unchanged_tables() -> None:
    source = words.from_values((0, 1, 0, 2))
    observed = words.slice_runs(source, 0, 1)
    words.prune_stale_program_word_memos()
    assert (
        sum(words.prune_stale_program_word_memos(amortized=True) for _ in range(100))
        == 0
    )
    assert words._SLICE[source.node_id, 0, 1] is observed


def test_rope_cache_reset_starts_a_new_cleanup_epoch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = words.from_values((0, 1, 2, 3))
    monkeypatch.setattr(words, "_NEXT_PRUNE_SIZE", 10**9)
    words.clear_transient_program_word_caches()
    assert words._NEXT_PRUNE_SIZE == 256
    assert list(words.iter_runs(source)) == [(0, 1), (1, 1), (2, 1), (3, 1)]


def test_residual_reuse_is_bounded_and_clear_preserves_live_handles() -> None:
    planes = PlaneAlgebra(max_reuse_entries=2)
    gate = PlaneGate.build("increment", ("f5",), "f5", lambda a: (a + 1) % 5)
    source = planes.from_values("f5", (0, 1, 2, 3))
    result = planes.apply(gate, source)
    planes.clear_work()
    hits = planes.reuse_hits
    assert planes.apply(gate, source) is result
    assert planes.reuse_hits == hits + 1
    outputs = [result]
    for i in range(5):
        current = planes.from_values("f5", (i, (i + 1) % 5, i))
        outputs.append(planes.apply(gate, current))
        planes.clear_work()
        assert len(planes._reuse) <= 2
    assert planes.reuse_evictions > 0
    planes.clear_reuse()
    assert not planes._reuse and not planes._cofactors
    assert tuple(planes.atom(result, i) for i in range(4)) == (1, 2, 3, 4)
    assert planes.apply(gate, source) is result


def test_residual_reuse_does_not_keep_an_endpoint_word_alive() -> None:
    import gc
    import weakref

    planes = PlaneAlgebra()
    source = planes.from_values("f5", (0, 1, 2))
    gate = PlaneGate.build("increment", ("f5",), "f5", lambda a: (a + 1) % 5)
    output = planes.apply(gate, source)
    root = weakref.ref(planes.resolve(output))
    planes.clear_work()
    del output
    gc.collect()
    assert root() is None
