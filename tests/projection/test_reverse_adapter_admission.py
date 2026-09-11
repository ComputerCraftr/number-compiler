"""Issued tile scopes validate before warm result and interface lookups."""

from collections.abc import Callable
from dataclasses import replace
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def test_reverse_adapter_rejects_foreign_inputs_before_warm_microblock() -> None:
    term = ReverseAddPoweredTerm(196, 8)
    expected = term.digit(0)
    projection = term._point_index()._lazy_application
    assert type(projection) is LazyProjection
    application = projection._open()
    scheduler = application.scheduler
    point_args = (
        application.action,
        application.source,
        application.ports,
        application.wiring,
        0,
    )
    assert scheduler.point(*point_args) == expected
    before = term._ledger.snapshot()
    attacks: tuple[tuple[Callable[..., object], tuple[object, ...]], ...] = (
        (scheduler.point, point_args),
        (scheduler.width, point_args[:4]),
    )
    for method, arguments in attacks:
        for position in (0, 1):
            original = arguments[position]
            assert isinstance(original, ArenaHandle)
            for altered in (
                replace(original, owner=ArenaToken("foreign-adapter")),
                replace(original, kind="wrong-kind"),
                replace(original, local_id=10**9),
            ):
                values = list(arguments)
                values[position] = altered
                with pytest.raises((TypeError, ValueError)):
                    method(*values)
        for altered in (
            replace(application.wiring.signature, owner=ArenaToken("foreign-port")),
            replace(application.wiring.signature, kind="wrong-kind"),
            replace(application.wiring.signature, local_id=10**9),
        ):
            values = list(arguments)
            values[3] = replace(application.wiring, signature=altered)
            with pytest.raises((TypeError, ValueError)):
                method(*values)
    for coordinate in (True, 0.0, -1, term.maximum_width):
        with pytest.raises((TypeError, IndexError)):
            projection.point(cast("int", coordinate))
        with pytest.raises((TypeError, IndexError)):
            term.digit(cast("int", coordinate))
    assert term._ledger.snapshot() == before


def test_prepared_reverse_output_uses_no_source_reads_or_leaf_recompilation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.interfaces.tile_interface_compilation as compilation
    from number_compiler.projection.microblock_cache import MicroblockCache
    from number_compiler.projection.point_response import PointResponseRegister

    monkeypatch.setattr(MicroblockCache, "get", lambda *_args, **_kw: None)
    monkeypatch.setattr(MicroblockCache, "put", lambda *_args, **_kw: None)
    monkeypatch.setattr(
        PointResponseRegister,
        "query",
        lambda _self, _program, coordinate, evaluate: evaluate(coordinate),
    )
    term = ReverseAddPoweredTerm(196, 32)
    expected = term.digit(0)
    index = term._point_index()
    projection = index._lazy_application
    assert type(projection) is LazyProjection
    before = term._ledger.snapshot()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("prepared reverse output rebuilt a source/leaf")

    monkeypatch.setattr(index._source_geometry, "read", forbidden)
    monkeypatch.setattr(compilation, "_tabulated", forbidden)
    monkeypatch.setattr(index._compiler, "compose", forbidden)
    assert term.digit(0) == expected
    after = term._ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert after.counters.get("source_leaf_reads", 0) == before.counters.get(
        "source_leaf_reads", 0
    )
    assert after.counters.get("completed_result_early_hits", 0) > before.counters.get(
        "completed_result_early_hits", 0
    )
