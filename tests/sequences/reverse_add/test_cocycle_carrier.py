"""Exact parity-cocycle carrier and nonmaterializing controls."""

import json
from pathlib import Path
from typing import Never

import pytest

from devtools.experiments.reverse_add import cocycle_carrier as module
from devtools.experiments.reverse_add.cocycle_carrier import (
    CocycleReverseCarrier,
)
from devtools.experiments.reverse_add.factored_planes import PlaneGate
from devtools.proofs import exact_oracle
from number_compiler.arithmetic.automata import program_word as words
from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.fields.radix import reverse_pair_sums


@pytest.mark.parametrize("seed", (1, 1111, 196))
def test_cocycle_planes_agree_with_independent_successors(seed: int) -> None:
    carrier = CocycleReverseCarrier()
    with exact_oracle():
        field = reverse_pair_sums(seed, 10)
        cell = carrier.source(field)
        for _ in range(16):
            field, growth = pair_step(field, 10)
            source = cell
            cell, actual, actions = carrier.successor_with_actions(cell)
            assert actual == growth
            assert carrier.decode(cell) == field
            width = carrier.planes.resolve(cell.f5).length
            if growth:
                source_f5 = carrier.planes.concat(
                    source.f5, carrier.planes.constant("f5", 0, 1)
                )
                source_epsilon = carrier.planes.concat(
                    source.epsilon, carrier.planes.constant("bool", 0, 1)
                )
            else:
                source_f5, source_epsilon = source.f5, source.epsilon
            assert carrier.planes.resolve(source_f5).length == width
            assert (
                actions.f5.apply(
                    source_f5,
                    shift=carrier.planes.shift,
                    add=carrier._factored._add,
                    scale=carrier._factored._scale,
                )
                == cell.f5
            )
            assert (
                actions.epsilon.apply(
                    source_epsilon,
                    shift=carrier.planes.shift,
                    add=carrier._bool_add,
                )
                == cell.epsilon
            )
    assert carrier.primitive_successors == 16
    assert carrier.nonlinear_gate_requests == 32


@pytest.mark.parametrize("length", (1, 4, 10**100))
def test_huge_uniform_control_never_imports_or_decodes_pair_values(
    length: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    carrier = CocycleReverseCarrier()
    cell = carrier.uniform(CarryFn.CONST0, 2, 0, length)
    run = words.run

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("successor imported or decoded a pair-value field")

    def bounded_run(symbol: int, count: int) -> words.CanonicalWord:
        assert 0 <= symbol < 5
        return run(symbol, count)

    monkeypatch.setattr(carrier, "source", forbidden)
    monkeypatch.setattr(carrier, "encode", forbidden)
    monkeypatch.setattr(carrier, "decode", forbidden)
    monkeypatch.setattr(carrier.planes, "from_values", forbidden)
    monkeypatch.setattr(module, "decimal_cocycle_value", forbidden)
    monkeypatch.setattr(words, "from_values", forbidden)
    monkeypatch.setattr(words, "run", bounded_run)

    for expected in ((0, 4, 0), (0, 3, 0), (2, 1, 0)):
        cell, growth = carrier.successor(cell)
        assert growth == 0
        assert (
            tuple(
                carrier.planes.atom(plane, 0)
                for plane in (cell.domain, cell.f5, cell.epsilon)
            )
            == expected
        )
        assert all(
            carrier.planes.metrics(plane)["nodes"] == 1
            for plane in (cell.domain, cell.f5, cell.epsilon)
        )

    cell, growth = carrier.successor(cell)
    assert growth == 1
    for position in (0, length):
        assert tuple(
            carrier.planes.atom(plane, position)
            for plane in (cell.domain, cell.f5, cell.epsilon)
        ) == (0, 2, 1)
    if length > 1:
        assert tuple(
            carrier.planes.atom(plane, length // 2)
            for plane in (cell.domain, cell.f5, cell.epsilon)
        ) == (2, 4, 0)
    assert all(
        carrier.planes.metrics(plane)["nodes"] <= 4
        for plane in (cell.domain, cell.f5, cell.epsilon)
    )


def test_partial_plane_gate_rejects_undefined_scalar_input() -> None:
    carrier = CocycleReverseCarrier()
    partial = PlaneGate.build(
        "partial-regression", ("bool",), "bool", lambda value: 0 if not value else None
    )
    undefined = carrier.planes.constant("bool", 1, 8)
    with pytest.raises(ValueError, match="undefined"):
        carrier.planes.apply(partial, undefined)


def test_cocycle_plane_checkpoint_round_trip() -> None:
    from devtools.proofs.reverse_plane_checkpoint import (
        export_plane_roots,
        import_plane_roots,
    )

    carrier = CocycleReverseCarrier()
    with exact_oracle():
        cell = carrier.source(reverse_pair_sums(196, 10))
        archive = json.loads(
            json.dumps(
                export_plane_roots(
                    carrier,
                    (cell.domain, cell.f5, cell.epsilon),
                )
            )
        )
        restored = module.CocycleCell(*import_plane_roots(carrier, archive))
        assert restored == cell
        assert carrier.validate(restored) == carrier.validate(cell)


def test_endpoint_resume_preserves_primitive_counts(tmp_path: Path) -> None:
    import json

    from devtools.proofs.reverse_cocycle_endpoint_probe import probe

    checkpoint = tmp_path / "checkpoint.json"
    with exact_oracle():
        first = probe(196, 16, chunk=8, checkpoint=checkpoint)
        second = probe(196, 16, chunk=8, resume=checkpoint, checkpoint=checkpoint)
        assert first["primitive_successors"] == 8
        assert second["primitive_successors"] == 16
        assert second["nonlinear_gate_requests"] == 32
        archive = json.loads(checkpoint.read_text())
        archive["primitive_successors"] = 1
        checkpoint.write_text(json.dumps(archive))
        with pytest.raises(ValueError, match="counters"):
            probe(196, 16, resume=checkpoint)
