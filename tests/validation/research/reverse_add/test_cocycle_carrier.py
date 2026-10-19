"""Exact parity-cocycle carrier and nonmaterializing controls."""

import json
from collections.abc import Callable
from pathlib import Path
from typing import Never

import pytest

from devtools.experiments.reverse_add import cocycle_carrier as module
from devtools.experiments.reverse_add.cocycle_carrier import (
    CocycleReverseCarrier,
)
from devtools.experiments.reverse_add.factored_planes import PlaneGate, PlaneID
from devtools.experiments.reverse_add.factored_power import FactoredTemporalPower
from devtools.verification import exact_oracle
from number_compiler.arithmetic.automata import program_word as words
from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.fields.radix import reverse_pair_sums
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_crt_digit,
)
from number_compiler.arithmetic.polynomials.f2_transport import F2SpatialTransport
from number_compiler.arithmetic.polynomials.f5_transport import F5AffineTransport


def test_cocycle_endpoint_demand_is_separate_from_complete_f5_action(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    carrier = CocycleReverseCarrier()
    with exact_oracle():
        field = reverse_pair_sums(196, 10)
        source = carrier.source(field)
        expected = field
        for _ in range(8):
            expected, _ = pair_step(expected, 10)
        power = FactoredTemporalPower(carrier)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("endpoint demand composed historical F5 forcing")

        with monkeypatch.context() as patch:
            patch.setattr(power, "_compose", forbidden)
            endpoint = power.advance(source, 8)
        assert carrier.decode(endpoint) == expected
        assert power.compositions == 0
        assert not power._memo
        assert carrier.primitive_successors == 8
        complete = power.block(source, 8)
        assert complete.output == endpoint
        assert complete.action.linear.growths == (
            carrier.planes.resolve(endpoint.f5).length
            - carrier.planes.resolve(source.f5).length
        )
        assert power.compositions > 0


@pytest.mark.parametrize("seed", (0, 1, 18, 196, 909, 1041, 1051, 1593))
def test_source_only_d4_squares_use_returned_cocycle_grammar(
    seed: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    from devtools.experiments.reverse_add import powered_f5f2_carrier as orbit

    def pair(value: int) -> tuple[int, ...]:
        digits = tuple(map(int, reversed(str(value))))
        return tuple(a + b for a, b in zip(digits, reversed(digits), strict=True))

    expected: dict[int, tuple[int, ...]] = {}
    expected_values: dict[int, int] = {}
    value = seed
    for count in range(1, 21):
        value += int(str(value)[::-1])
        if count in (4, 8, 16, 20):
            expected[count] = pair(value)
            expected_values[count] = value
    carrier = CocycleReverseCarrier()
    source = carrier.source(pair(seed))
    power = FactoredTemporalPower(carrier)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("macro requested an endpoint row or pair decoder")

    with monkeypatch.context() as patch:
        patch.setattr(orbit, "reverse_add_pair_orbit", forbidden)
        patch.setattr(orbit, "powered_block", forbidden)
        patch.setattr(module, "decimal_cocycle_value", forbidden)
        patch.setattr(carrier, "source", forbidden)
        patch.setattr(carrier, "decode", forbidden)
        patch.setattr(carrier.planes, "from_values", forbidden)
        patch.setattr(words, "from_values", forbidden)
        patch.setattr(F5AffineTransport, "apply", forbidden)
        left = power.block(source, 4)
        right = power.block(left.output, 4)
        squared = power.block(source, 8)
        assert squared.output == right.output
        assert squared.action == power._compose(source, left, right).action
        fourth = power.block(squared.output, 8)
        sixteen = power.block(source, 16)
        assert sixteen.output == fourth.output
        assert sixteen.action == power._compose(source, squared, fourth).action
        work = carrier.planes.total_work
        primitives = carrier.primitive_successors
        assert power.block(source, 16) is sixteen
        # Revalidate the source but do not reconstruct the macro on a memo hit.
        assert carrier.primitive_successors == primitives
        assert carrier.planes.total_work >= work > 0
        assert power.cache_hits > 0
        twenty = power.block(source, 20)
    for count, block in ((4, left), (8, squared), (16, sixteen), (20, twenty)):
        assert carrier.decode(block.output) == expected[count]
        assert block.action.linear.growths == len(expected[count]) - len(pair(seed))
        # The expensive independent equality check belongs here, not in every
        # internal temporal composition that already has its returned grammar.
        assert (
            block.action.apply(
                power._pad(source.f5, len(expected[count])),
                shift=carrier.planes.shift,
                add=carrier.add_planes,
                scale=carrier.scale_plane,
            )
            == block.output.f5
        )
        assert block.emission is not None
        alpha, epsilon = block.emission
        width = carrier.planes.resolve(alpha).length
        digits = tuple(
            decimal_crt_digit(
                carrier.planes.atom(alpha, i), carrier.planes.atom(epsilon, i)
            )
            for i in range(width)
        )
        assert (
            sum(digit * 10**i for i, digit in enumerate(digits))
            == expected_values[count]
        )
    # This is a complete finite constructor, not a sublinear temporal pump:
    # a cold D16 still executes sixteen native grammar advances.
    assert carrier.primitive_successors <= 20
    if seed == 196:
        assert carrier.primitive_successors == 20
        assert expected_values[20] == 70446464506


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
                    add=carrier._factored.add_planes,
                    scale=carrier._factored.scale_plane,
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


def test_existing_carrier_aliases_dead_f2_forcing_without_source_arithmetic(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = F2SpatialTransport.apply

    def live_only(
        self: F2SpatialTransport,
        source: PlaneID,
        *,
        shift: Callable[[PlaneID, int], PlaneID],
        add: Callable[[PlaneID, PlaneID], PlaneID],
    ) -> PlaneID:
        if self.annihilated:
            raise AssertionError("carrier re-evaluated its annihilated F2 source")
        return original(self, source, shift=shift, add=add)

    monkeypatch.setattr(F2SpatialTransport, "apply", live_only)
    carrier = CocycleReverseCarrier()
    no_growths = 0
    with exact_oracle():
        expected = reverse_pair_sums(196, 10)
        cell = carrier.source(expected)
        for _ in range(8):
            expected, growth = pair_step(expected, 10)
            cell, actual, action = carrier.successor_with_actions(cell)
            assert actual == growth
            assert carrier.decode(cell) == expected
            if not growth:
                no_growths += 1
                assert cell.epsilon is action.epsilon.forcing
    assert no_growths == 4


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
    from devtools.verification.reverse_plane_checkpoint import (
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

    from devtools.verification.reverse_cocycle_endpoint_probe import probe

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
