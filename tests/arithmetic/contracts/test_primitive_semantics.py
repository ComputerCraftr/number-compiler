from __future__ import annotations

from array import array
from itertools import product
from typing import TYPE_CHECKING, Literal

import pytest

from number_compiler.arithmetic.automata.primitive_semantics import (
    PrimitiveSemanticsAdapter,
    division_witness,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BlockEffect,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
)
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.interfaces.diamond_kernel import (
    DiamondKernelArena,
    PrimitiveKernel,
)
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.assertions import assert_rejected_atomically

if TYPE_CHECKING:
    from number_compiler.arithmetic.automata.primitive_semantics import (
        PrimitiveSemantics,
    )
    from number_compiler.arithmetic.functions.finite_function_types import SemanticNode
    from number_compiler.resources.ledger import ResourceInventory


def adapter() -> PrimitiveSemanticsAdapter:
    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    return PrimitiveSemanticsAdapter(DiamondKernelArena(ledger), functions)


def identity(
    outputs: bytes = bytes(range(4)), name: str = "identity"
) -> FiniteBlockEffect:
    return FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=1,
        right_count=1,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", [0] * 4),
        right_transitions=array("I", [0] * 4),
        outputs=outputs,
        kernel_name=name,
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )


@pytest.mark.parametrize(
    "effect",
    (
        identity(),
        BaseBlockEffect(2),
        DigitNormalizeBlockEffect(2),
        NonblankBlockEffect(2, 2),
        CollatzPhysicalBlockEffect(),
        PhysicalCollatzFourBlockEffect(),
    ),
)
def test_primitive_functions_exhaust_every_admitted_state_and_symbol(
    effect: BlockEffect,
) -> None:
    compiled = adapter()
    record = compiled.compile(effect)
    primitive = compiled.kernels.kernel(record.kernel)
    for left, symbol, right in product(
        range(primitive.left_count),
        range(primitive.blank + 1),
        range(primitive.right_count),
    ):
        environment = dict(
            zip((p.variable for p in record.ports), (left, symbol, right))
        )
        expected = (
            primitive.advance(BoundarySide.LEFT, left, symbol),
            primitive.advance(BoundarySide.RIGHT, right, symbol),
            primitive.emit(left, symbol, right),
        )
        for function, value in zip(
            (record.advance_left, record.advance_right, record.emit), expected
        ):
            terminal = compiled.functions.evaluate(function, environment)
            assert terminal.kind == "atom" and terminal.value == value
    assert record.initial_left == primitive.initial(BoundarySide.LEFT)
    assert record.initial_right == primitive.initial(BoundarySide.RIGHT)
    # Invalid binary encodings are invalid even for a semantically unused port.
    for index, port in enumerate(record.ports):
        if port.cardinality == 1 << port.bits:
            continue
        values = [0, 0, 0]
        values[index] = port.cardinality
        environment = dict(zip((p.variable for p in record.ports), values))
        for function in (record.advance_left, record.advance_right, record.emit):
            assert compiled.functions.evaluate(function, environment).kind == "invalid"


def test_equal_definitions_alias_but_equal_carry_different_output_stays_distinct() -> (
    None
):
    compiled = adapter()
    first = compiled.compile(identity())
    alias = compiled.compile(identity(name="different-name"))
    other = compiled.compile(identity(bytes((1, 0, 2, 3))))
    assert first is alias
    assert first.advance_left == other.advance_left
    assert first.advance_right == other.advance_right
    assert first.emit != other.emit
    before = compiled.ledger.snapshot()
    assert compiled.compile(first.kernel) is first
    assert compiled.ledger.snapshot().entries == before.entries
    assert compiled.ledger.counters["primitive_semantics_compilations"] == 2


@pytest.mark.parametrize("radix", (3, 6, 12))
def test_division_primitive_outputs_complete_binary_quotient_and_remainder(
    radix: int,
) -> None:
    compiled = adapter()
    record = compiled.compile(division_witness(radix))
    left, symbol, right = (p.variable for p in record.ports)
    for value in range(128):
        carry = 0
        quotient = 0
        for bit in map(int, bin(value)[2:]):
            environment = {left: 0, symbol: bit, right: carry}
            emitted = compiled.functions.evaluate(record.emit, environment)
            carry_out = compiled.functions.evaluate(record.advance_right, environment)
            quotient = 2 * quotient + emitted.value
            carry = carry_out.value
        assert (quotient, carry) == divmod(value, radix)
    for carry in range(radix):
        environment = {left: 0, symbol: record.blank, right: carry}
        assert (
            compiled.functions.evaluate(record.emit, environment).value == record.blank
        )
        assert (
            compiled.functions.evaluate(record.advance_right, environment).value
            == carry
        )


@pytest.mark.parametrize("warm", (False, True))
def test_foreign_wrong_kind_and_numeric_alias_reject_before_mutation(
    warm: bool,
) -> None:
    compiled = adapter()
    local = compiled.kernels.intern(CollatzPhysicalBlockEffect())
    if warm:
        compiled.compile(local)
    other = adapter().kernels.intern(CollatzPhysicalBlockEffect())
    boolean = ActionProgramID(local.owner, local.kind, local.local_id)
    floating = ActionProgramID(local.owner, local.kind, local.local_id)
    object.__setattr__(boolean, "local_id", True)
    object.__setattr__(floating, "local_id", 1.0)
    invalid = (
        other,
        ActionProgramID(local.owner, "other", local.local_id),
        boolean,
        floating,
    )
    before = compiled.ledger.snapshot()
    for handle in invalid:
        with pytest.raises((TypeError, ValueError)):
            compiled.compile(handle)
        assert compiled.ledger.snapshot() == before


def test_record_budget_rejection_precedes_primitive_synthesis() -> None:
    compiled = adapter()
    handle = compiled.kernels.intern(CollatzPhysicalBlockEffect())
    compiled.ledger.max_cache_entries = compiled.ledger.entries
    assert_rejected_atomically(
        compiled.ledger, lambda: compiled.compile(handle), BlockContextBudgetExceeded
    )
    assert not compiled.records


def test_adapter_rejects_cross_ledger_arena_pair() -> None:
    with pytest.raises(ValueError):
        PrimitiveSemanticsAdapter(
            DiamondKernelArena(ResourceLedger()),
            SemanticFunctionArena(ResourceLedger()),
        )


@pytest.mark.parametrize(
    "effect,ticks",
    ((CollatzPhysicalBlockEffect(), 1), (PhysicalCollatzFourBlockEffect(), 4)),
)
def test_physical_functions_preserve_even_odd_and_cycle_phases(
    effect: CollatzPhysicalBlockEffect | PhysicalCollatzFourBlockEffect, ticks: int
) -> None:
    compiled = adapter()
    record = compiled.compile(effect)
    left_port, symbol_port, right_port = (port.variable for port in record.ports)
    for original in range(1, 65):
        symbols = (
            tuple((original >> i) & 1 for i in range(original.bit_length()))
            + (record.blank,) * 10
        )
        right_states = [record.initial_right] * len(symbols)
        right = record.initial_right
        for position in range(len(symbols) - 1, -1, -1):
            right_states[position] = right
            environment = {
                left_port: record.initial_left,
                symbol_port: symbols[position],
                right_port: right,
            }
            right = compiled.functions.evaluate(record.advance_right, environment).value
        left = record.initial_left
        observed = 0
        for position, symbol in enumerate(symbols):
            environment = {
                left_port: left,
                symbol_port: symbol,
                right_port: right_states[position],
            }
            emitted = compiled.functions.evaluate(record.emit, environment).value
            left = compiled.functions.evaluate(record.advance_left, environment).value
            if emitted != record.blank:
                assert emitted in (0, 1)
                observed |= emitted << position
        expected = original
        for _ in range(ticks):
            expected = 3 * expected + 1 if expected & 1 else expected // 2
        assert observed == expected


def _retained_snapshot(
    compiled: PrimitiveSemanticsAdapter,
) -> tuple[
    tuple[SemanticNode, ...],
    dict[SemanticNode, int],
    dict[ActionProgramID, PrimitiveSemantics],
    int,
    int,
    tuple[ResourceInventory, ...],
]:
    ledger = compiled.ledger.snapshot()
    return (
        tuple(compiled.functions.nodes),
        dict(compiled.functions.keys),
        dict(compiled.records),
        ledger.entries,
        ledger.nodes,
        ledger.inventory,
    )


def _construction_work_snapshot(
    compiled: PrimitiveSemanticsAdapter,
) -> tuple[int, int, int, int]:
    ledger = compiled.ledger.snapshot()
    return (
        ledger.peak_entries,
        ledger.peak_nodes,
        ledger.counters.get("semantic_function_workspace_allocated_entries", 0),
        ledger.counters.get("semantic_function_workspace_allocated_nodes", 0),
    )


@pytest.mark.parametrize("budget", ("entries", "nodes"))
def test_late_component_budget_failure_publishes_no_partial_functions(
    budget: str,
) -> None:
    calibration = adapter()
    handle = calibration.kernels.intern(CollatzPhysicalBlockEffect())
    before_entries, before_nodes = calibration.ledger.entries, calibration.ledger.nodes
    calibration.compile(handle)
    required_entries = calibration.ledger.entries - before_entries
    required_nodes = calibration.ledger.nodes - before_nodes
    assert required_nodes > 1
    assert required_entries == 2 * required_nodes + 1

    compiled = adapter()
    handle = compiled.kernels.intern(CollatzPhysicalBlockEffect())
    if budget == "entries":
        compiled.ledger.max_cache_entries = (
            compiled.ledger.entries + required_entries - 1
        )
    else:
        compiled.ledger.max_nodes = compiled.ledger.nodes + required_nodes - 1
    before = _retained_snapshot(compiled)
    before_work = _construction_work_snapshot(compiled)
    with pytest.raises(BlockContextBudgetExceeded):
        compiled.compile(handle)
    assert compiled.ledger.counters["primitive_semantics_admissible_evaluations"] > 0
    assert _retained_snapshot(compiled) == before
    _assert_failed_construction_work(compiled, before_work)
    compiled.ledger.max_cache_entries = None
    compiled.ledger.max_nodes = None
    record = compiled.compile(handle)
    assert record.kernel == handle
    assert compiled.ledger.entries == before[3] + required_entries
    assert compiled.ledger.nodes == before[4] + required_nodes


def test_exception_during_third_component_keeps_prior_semantic_arena_unchanged(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    compiled = adapter()
    compiled.compile(identity())
    handle = compiled.kernels.intern(CollatzPhysicalBlockEffect())
    before = _retained_snapshot(compiled)
    before_work = _construction_work_snapshot(compiled)
    build = compiled._build
    calls = []

    def fail_emit(
        transaction: _Transaction,
        kernel: PrimitiveKernel,
        ports: tuple[FinitePort, FinitePort, FinitePort],
        output: AtomSort,
        operation: Literal["left", "right", "emit"],
    ) -> int:
        calls.append(operation)
        if operation == "emit":
            raise ArithmeticError("injected primitive proof failure")
        return build(transaction, kernel, ports, output, operation)

    monkeypatch.setattr(compiled, "_build", fail_emit)
    with pytest.raises(ArithmeticError, match="injected"):
        compiled.compile(handle)
    assert calls == ["left", "right", "emit"]
    assert _retained_snapshot(compiled) == before
    _assert_failed_construction_work(compiled, before_work)


def test_full_budget_warm_record_needs_no_reservation_or_primitive_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    compiled = adapter()
    record = compiled.compile(CollatzPhysicalBlockEffect())
    compiled.ledger.max_cache_entries = compiled.ledger.entries
    compiled.ledger.max_nodes = compiled.ledger.nodes
    before = _retained_snapshot(compiled)
    before_work = _construction_work_snapshot(compiled)

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("warm primitive semantics attempted construction")

    monkeypatch.setattr(compiled, "_build", forbidden)
    assert compiled.compile(record.kernel) is record
    assert _retained_snapshot(compiled) == before
    assert _construction_work_snapshot(compiled) == before_work


def _assert_failed_construction_work(
    compiled: PrimitiveSemanticsAdapter,
    before_work: tuple[int, int, int, int],
) -> None:
    after_work = _construction_work_snapshot(compiled)
    assert all(after >= prior for after, prior in zip(after_work[:2], before_work[:2]))
    assert after_work[2] > before_work[2]
    assert after_work[3] > before_work[3]
