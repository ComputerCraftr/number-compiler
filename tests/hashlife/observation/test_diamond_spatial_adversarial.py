"""Primitive summary admission and public generic midpoint boundaries."""

from array import array
from dataclasses import replace
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    SpatialSummary,
)
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.diamond_runtime import build, oracle


def test_direct_spatial_compile_cannot_skip_source_and_action_admission() -> None:
    runtime, action = build(CollatzPhysicalBlockEffect(), (1,), 2, 1)
    other, other_action = build(CollatzPhysicalBlockEffect(), (1,), 2, 1)
    wrong_alphabet = runtime.actions.intern(
        runtime.actions.compiler.atom(BaseBlockEffect(3))
    )
    good = SpatialSummary(action, runtime.cells.source(0, 0), 0)
    for warm in (False, True):
        if warm:
            runtime.execute(good)
        for invalid in (
            replace(good, action=wrong_alphabet),
            replace(good, action=other_action),
            replace(good, cell=other.cells.source(0, 0)),
            replace(good, side=True),
        ):
            before = runtime.ledger.snapshot()
            generator = runtime.spatial.compile(invalid)
            try:
                with pytest.raises((TypeError, ValueError)):
                    next(generator)
            finally:
                generator.close()
            assert runtime.ledger.snapshot() == before


def test_foreign_or_wrong_port_summary_rejects_before_cold_or_warm_kernel_memo() -> (
    None
):
    runtime, action = build(CollatzPhysicalBlockEffect(), (1,), 2, 1)
    other, _ = build(CollatzPhysicalBlockEffect(), (1,), 2, 1)
    state = runtime.boundaries.literal(action, 0, 0)
    foreign = other.kernels.constant(6, 0)
    wrong_port = runtime.kernels.variable(
        6, PortVariable(0, 0, "another-input-port", 0)
    )
    wrong_domain = runtime.kernels.constant(3, 0)
    assert not runtime.primitive_ids
    for warm in (False, True):
        if warm:
            summary = runtime.execute(
                SpatialSummary(action, runtime.cells.source(0, 0), 0)
            )
            runtime.spatial.observe(action, 0, summary, state)
        for invalid in (foreign, wrong_port, wrong_domain):
            before = runtime.ledger.snapshot()
            with pytest.raises(ValueError):
                runtime.spatial.observe(action, 0, invalid, state)
            assert runtime.ledger.snapshot() == before


def test_public_custom_finite_composition_uses_diamonds_without_future_tiles(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    kernel = FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=2,
        right_count=2,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array(
            "H",
            [
                state ^ (symbol & 1) if symbol < 3 else state
                for state in range(2)
                for symbol in range(4)
            ],
        ),
        right_transitions=array(
            "H",
            [
                state ^ (symbol & 1) if symbol < 3 else state
                for state in range(2)
                for symbol in range(4)
            ],
        ),
        outputs=bytes(
            symbol ^ left ^ right if symbol < 3 else 3
            for left in range(2)
            for symbol in range(4)
            for right in range(2)
        ),
        kernel_name="custom-bilateral-parity",
        storage_bytes=48,
        uncompressed_bytes=48,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )
    values, length = (1, 0, 1), 8
    expected = oracle(kernel, values, length, 3)
    compiler = LazyCompiler(ResourceLedger())
    effect = compiler.power(kernel, 3).root
    assert effect is not None

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError(
            "generic point path fell back or allocated exact future geometry"
        )

    index = HashLifeBlockIndex(effect, values, logical_length=length)
    assert isinstance(index._lazy_application, LazyProjection)
    import number_compiler.arithmetic.fields.dyadic_tile as tiles

    monkeypatch.setattr(tiles, "leaf", forbidden)
    monkeypatch.setattr(tiles, "join", forbidden)
    before = tuple(index._source_geometry.nodes.items())
    assert [
        index.direct_powered_point(position) for position in range(length)
    ] == expected
    assert index.direct_active_width() == max(
        (index + 1 for index, value in enumerate(expected) if value != 3), default=0
    )
    assert tuple(index._source_geometry.nodes.items()) == before
