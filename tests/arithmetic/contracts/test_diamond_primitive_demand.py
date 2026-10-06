"""Demand pruning is a universal fixed-interface cofactor, never sampling."""

from __future__ import annotations

from functools import partial
from itertools import product
from typing import TYPE_CHECKING, Literal, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.execution.diamond_primitive_demand import (
    PrimitiveDemandCertificate,
    PrimitiveDemandKey,
    PrimitiveDemandOracle,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from number_compiler.sequences.collatz.tile_family_hooks import collatz_tile_hooks
from tests.support.arithmetic_fixtures import nonblank_demand
from tests.support.assertions import assert_rejected_atomically

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel


def _collatz_kernels() -> DiamondKernelArena:
    kernels = DiamondKernelArena()
    kernels.bind_family_hooks(collatz_tile_hooks())
    return kernels


def oracle(
    primitive: PrimitiveKernel,
    operation: str,
    side: int,
    values: tuple[int | None, ...],
) -> int | None:
    sizes = (
        (
            primitive.left_count if side == 0 else primitive.right_count,
            primitive.blank + 1,
        )
        if operation == "advance"
        else (primitive.left_count, primitive.blank + 1, primitive.right_count)
    )
    outputs = set()
    for arguments in product(
        *(
            range(size) if value is None else (value,)
            for value, size in zip(values, sizes, strict=True)
        )
    ):
        if operation == "advance":
            outputs.add(
                primitive.encode(
                    BoundarySide(side),
                    primitive.effect.advance(
                        BoundarySide(side),
                        primitive.decode(BoundarySide(side), arguments[0]),
                        arguments[1],
                    ),
                )
            )
        else:
            outputs.add(
                primitive.effect.emit(
                    primitive.left[arguments[0]],
                    arguments[1],
                    primitive.right[arguments[2]],
                )
            )
    return next(iter(outputs)) if len(outputs) == 1 else None


@pytest.mark.parametrize(
    "operation,side", [("advance", 0), ("advance", 1), ("emit", 0)]
)
def test_every_partial_collatz_primitive_pattern_matches_complete_oracle(
    operation: Literal["advance", "emit"], side: int
) -> None:
    kernels = _collatz_kernels()
    handle = kernels.intern(CollatzPhysicalBlockEffect())
    primitive = kernels.kernel(handle)
    demand = PrimitiveDemandOracle(kernels)
    sizes = (
        (
            primitive.left_count if side == 0 else primitive.right_count,
            primitive.blank + 1,
        )
        if operation == "advance"
        else (primitive.left_count, primitive.blank + 1, primitive.right_count)
    )
    for values in product(*((None, *range(size)) for size in sizes)):
        expected = oracle(primitive, operation, side, values)
        assert demand.constant(handle, operation, side, values) == expected
    assert demand.ledger.counters["primitive_demand_cursor_peak"] == len(sizes)
    assert all(row.accounting_delta == 0 for row in demand.ledger.inventory())


def test_absorbing_observer_certificate_drops_unknown_symbol_and_warm_work() -> None:
    kernels = _collatz_kernels()
    handle = kernels.intern(NonblankBlockEffect(2, 2))
    demand = PrimitiveDemandOracle(kernels)
    before = kernels.ledger.counters.get("primitive_transition_evaluations", 0)
    assert demand.constant(handle, "advance", 0, (1, None)) == 1
    assert kernels.ledger.counters["primitive_transition_evaluations"] - before == 3
    after = kernels.ledger.counters["primitive_transition_evaluations"]
    assert demand.constant(handle, "advance", 0, (1, None)) == 1
    assert kernels.ledger.counters["primitive_transition_evaluations"] == after
    assert demand.ledger.counters["primitive_demand_cache_hits"] == 1


def test_varying_pattern_stops_at_first_disagreeing_completion() -> None:
    kernels = DiamondKernelArena()
    handle = kernels.intern(NonblankBlockEffect(2, 2))
    demand = PrimitiveDemandOracle(kernels)
    assert demand.constant(handle, "advance", 0, (0, None)) is None
    assert demand.ledger.counters["primitive_demand_completion_tests"] == 3
    assert demand.ledger.counters["primitive_demand_early_variation_exits"] == 1
    before = demand.ledger.counters["primitive_demand_completion_tests"]
    assert demand.constant(handle, "advance", 0, (0, None)) is None
    assert demand.ledger.counters["primitive_demand_completion_tests"] == before


def test_foreign_domains_and_malformed_warm_patterns_do_not_mutate_ledger() -> None:
    kernels = _collatz_kernels()
    handle = kernels.intern(CollatzPhysicalBlockEffect())
    demand = PrimitiveDemandOracle(kernels)
    other = DiamondKernelArena(kernels.ledger)
    other.bind_family_hooks(collatz_tile_hooks())
    foreign = other.intern(CollatzPhysicalBlockEffect())
    demand.constant(handle, "advance", 1, (0, None))
    bad = (
        (foreign, "advance", 1, (0, None)),
        (
            ActionProgramID(handle.owner, "diamond-action", handle.local_id),
            "advance",
            1,
            (0, None),
        ),
        (handle, "advance", True, (0, None)),
        (handle, "emit", 1, (0, None, 0)),
        (handle, "advance", 0, (True, None)),
        (handle, "advance", 0, (1000, None)),
        (handle, "advance", 0, [0, None]),
        (handle, "emit", 0, (0, None)),
    )
    for kernel, operation, side, values in bad:
        assert_rejected_atomically(
            kernels.ledger,
            partial(
                demand.constant,
                kernel,
                cast("Literal['advance', 'emit']", operation),
                side,
                cast("tuple[int | None, ...]", values),
            ),
            (ValueError, TypeError),
        )


def test_eviction_recomputes_the_universal_certificate() -> None:
    ledger, _unused_kernels_binding, handle, demand = nonblank_demand()
    assert demand.constant(handle, "advance", 0, (1, None)) == 1
    before = ledger.counters["primitive_demand_completion_tests"]
    ledger.evict_query_memos()
    assert not demand.memo
    assert demand.constant(handle, "advance", 0, (1, None)) == 1
    assert ledger.counters["primitive_demand_completion_tests"] == before + 3


def test_demand_records_cannot_accept_future_word_payloads() -> None:
    kernels = _collatz_kernels()
    handle = kernels.intern(CollatzPhysicalBlockEffect())
    with pytest.raises(ValueError):
        PrimitiveDemandKey(handle, "emit", 0, (1 << 255, None, 0))
    with pytest.raises(ValueError):
        PrimitiveDemandCertificate(1 << 255)


def test_verified_four_step_kernel_blank_cofactor_checks_every_right_port() -> None:
    from number_compiler.sequences.collatz.physical_kernel import (
        PhysicalCollatzFourBlockEffect,
    )

    kernels = _collatz_kernels()
    handle = kernels.intern(PhysicalCollatzFourBlockEffect())
    primitive = kernels.kernel(handle)
    demand = PrimitiveDemandOracle(kernels)
    assert demand.constant(handle, "emit", 0, (0, 2, None)) == 2
    assert (
        demand.ledger.counters["primitive_demand_completion_tests"]
        == primitive.right_count
    )
    assert all(
        primitive.effect.emit(primitive.left[0], 2, state) == 2
        for state in primitive.right
    )


def test_collatz_odd_local_phase_does_not_demand_any_right_context() -> None:
    kernels = _collatz_kernels()
    handle = kernels.intern(CollatzPhysicalBlockEffect())
    primitive = kernels.kernel(handle)
    demand = PrimitiveDemandOracle(kernels)
    assert demand.constant(handle, "emit", 0, (0, 1, None)) == 0
    assert (
        demand.ledger.counters["primitive_demand_completion_tests"]
        == primitive.right_count
    )


def test_exhausted_cache_rejects_before_primitive_work_but_known_operation_needs_no_cache() -> (
    None
):
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    kernels = DiamondKernelArena()
    handle = kernels.intern(NonblankBlockEffect(2, 2))
    demand = PrimitiveDemandOracle(kernels)
    kernels.ledger.max_cache_entries = kernels.ledger.entries
    before = kernels.ledger.counters.get("primitive_transition_evaluations", 0)
    with pytest.raises(BlockContextBudgetExceeded):
        demand.constant(handle, "advance", 0, (1, None))
    assert kernels.ledger.counters.get("primitive_transition_evaluations", 0) == before
    assert not demand.memo
    entries = kernels.ledger.entries
    assert demand.constant(handle, "advance", 0, (1, 0)) == 1
    assert kernels.ledger.entries == entries
    assert not demand.memo
