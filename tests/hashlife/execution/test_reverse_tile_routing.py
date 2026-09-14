"""Replacement coverage for the retired reverse concrete-port executor."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from devtools.proofs.oracles.reverse_publisher import (
    ReversePublisherProjection,
)
from tests.arithmetic.contracts.test_tile_kernel import _runtime, _tile
from tests.support.reverse_higher_interface import _direct_step


@pytest.mark.validation  # Six temporal scales and all output coordinates.
def test_tile_scheduler_fuses_t1_through_t32_without_higher_runtime(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = (7, 18, 7, 19, 19, 19, 19, 19)
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(10))
    expected: tuple[int, ...] = source
    expectations: dict[int, tuple[int, ...]] = {}
    for step in range(1, 33):
        expected = _direct_step(expected, 10)
        if step in (1, 2, 4, 8, 16, 32):
            expectations[step] = expected

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("tile scheduler entered higher/proof execution")

    monkeypatch.setattr(HigherSemanticArena, "evaluate", forbidden)
    monkeypatch.setattr(HigherBimachineRuntime, "point", forbidden)
    monkeypatch.setattr(HigherBimachineRuntime, "point_structural", forbidden)
    with _tile(tiles, adapter, primitive, source) as binding:
        for steps, expected_word in expectations.items():
            action = adapter.power(primitive, steps)
            with scheduler.application(
                action,
                binding.tile,
                adapter.initial_ports(action),
                adapter.wiring(action),
            ) as application:
                assert (
                    tuple(application.point(i) for i in range(len(source)))
                    == expected_word
                )
    assert ledger.counters["tile_causal_frames"] > 0
    assert not hasattr(scheduler, "_ports")
    assert not hasattr(scheduler, "_residuals")


@pytest.mark.parametrize("generation", (1, 2, 4, 8, 16))
def test_public_reverse_digits_use_canonical_reachable_images(
    monkeypatch: pytest.MonkeyPatch,
    generation: int,
) -> None:
    """The family-first digit path cannot fall back to the retired publisher."""
    import number_compiler.hashlife.execution.tile_temporal as temporal

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("public reverse execution entered the retired publisher")

    monkeypatch.setattr(ReversePublisherProjection, "__init__", forbidden)
    monkeypatch.setattr(HigherBimachineRuntime, "point", forbidden)
    monkeypatch.setattr(HigherBimachineRuntime, "point_structural", forbidden)
    value = 196
    for _ in range(generation):
        value += int(str(value)[::-1])
    expected = tuple(map(int, reversed(str(value))))

    term = ReverseAddPoweredTerm(196, generation)
    index = term._point_index()
    assert type(index._lazy_application) is LazyProjection
    with monkeypatch.context() as poison:
        poison.setattr(temporal, "complete_temporal", forbidden)
        assert tuple(term.digit(i) for i in range(len(expected))) == expected
        assert term.width() == len(expected)
    counters = term._ledger.counters
    assert counters["tile_projection_compilation_frames"] > 0
    assert counters["primitive_transition_evaluations"] > 0
    assert counters.get("higher_action_continuation_requests", 0) == 0
    assert counters.get("higher_concrete_operation_evaluations", 0) == 0
    assert counters.get("whole_word_sweeps", 0) == 0
    assert counters.get("whole_word_symbol_visits", 0) == 0
    assert term.metrics().exact_endpoint_nodes == 0


@pytest.mark.parametrize("sort", ("tile", "action", "interface"))
@pytest.mark.parametrize("alias", (True, 0.0, 1.0))
def test_reverse_tile_ids_reject_integer_aliases_before_mutation(
    sort: str,
    alias: object,
) -> None:
    ledger, tiles, adapter, primitive, _scheduler = _runtime(BaseBlockEffect(10))
    with _tile(tiles, adapter, primitive, (7,)) as binding:
        interface = adapter._compile_interface(
            primitive, binding.tile, adapter.wiring(primitive)
        )
        if sort == "tile":
            tile = TileID(binding.tile.owner, binding.tile.kind, binding.tile.local_id)
            object.__setattr__(tile, "local_id", alias)
            before = ledger.snapshot()
            with pytest.raises((TypeError, ValueError)):
                tiles.resolve(tile)
        elif sort == "action":
            action = FieldCellActionID(
                primitive.owner, primitive.kind, primitive.local_id
            )
            object.__setattr__(action, "local_id", alias)
            before = ledger.snapshot()
            with pytest.raises((TypeError, ValueError)):
                adapter.validate_action(action)
        else:
            local = LocalInterfaceID(
                interface.owner, interface.kind, interface.local_id
            )
            object.__setattr__(local, "local_id", alias)
            before = ledger.snapshot()
            with pytest.raises((TypeError, ValueError)):
                adapter.quotients.resolve(local)
        assert ledger.snapshot() == before
