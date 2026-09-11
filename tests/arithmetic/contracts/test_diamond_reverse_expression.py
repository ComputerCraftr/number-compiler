"""Exhaustive original-kernel truth-function verification; no source tapes."""

from array import array
from itertools import product

import pytest

from number_compiler.arithmetic.contracts.block_kernel import (
    FiniteBlockEffect,
    _load_base10_t2_kernel,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena


@pytest.mark.validation  # Exhaustive comparison of all 2,710,060 T² outputs.
def test_factorized_function_matches_every_verified_t2_output() -> None:
    arena = DiamondKernelArena()
    handle = arena.intern(_load_base10_t2_kernel())
    arguments = tuple(
        arena.variable(domain, PortVariable(0, side, "complete-t2", 0))
        for side, domain in enumerate((757, 20, 179))
    )
    output = arena.emit_expression(handle, *arguments)
    # Uninstrumented traversal here is an independent read-only test oracle;
    # production uses arena.evaluate and reports its decision visits.
    nodes = arena.functions._nodes
    graph = []
    for node in nodes:
        if node.variable is None:
            graph.append((-1, 0, 0, 0))
        else:
            graph.append(
                (node.variable.side, 1 << node.variable.bit, node.low, node.high)
            )
    roots = tuple(bit.local_id for bit in arena.expression(output).bits)
    expected = _load_base10_t2_kernel().outputs
    # Resolve each repeated right-port function once in this independent
    # oracle. Immutable truth rows still cover every one of the 179 ports;
    # comparison below remains exhaustive over all 2,710,060 output entries.
    right_functions = {0: bytes(179), 1: bytes([1]) * 179}
    right_lanes: dict[int, int] = {}
    output_rows: dict[tuple[int, ...], bytes] = {}
    checked = 0
    for left, symbol in product(range(757), range(20)):
        residuals = []
        for root in roots:
            while root >= 2 and graph[root][0] < 2:
                side, mask, low, high = graph[root]
                root = high if (left if side == 0 else symbol) & mask else low
            residuals.append(root)
        key = tuple(residuals)
        row = output_rows.get(key)
        if row is None:
            pending = [(root, False) for root in residuals]
            while pending:
                root, ready = pending.pop()
                if root in right_functions:
                    continue
                side, mask, low, high = graph[root]
                assert side == 2
                if not ready:
                    pending.extend(((root, True), (low, False), (high, False)))
                    continue
                low_values, high_values = right_functions[low], right_functions[high]
                right_functions[root] = bytes(
                    high_values[right] if right & mask else low_values[right]
                    for right in range(179)
                )
            # Test-only byte lanes combine all right assignments at once.
            # There is no cross-lane carry: each component is Boolean and
            # the verified output alphabet occupies fewer than eight bits.
            assert len(residuals) <= 8
            lanes = 0
            for bit, root in enumerate(residuals):
                if root not in right_lanes:
                    right_lanes[root] = int.from_bytes(right_functions[root], "little")
                lanes |= right_lanes[root] << bit
            row = lanes.to_bytes(179, "little")
            output_rows[key] = row
        offset = (left * 20 + symbol) * 179
        assert row == expected[offset : offset + 179]
        checked += len(row)
    assert checked == 757 * 20 * 179
    assert arena.ledger.counters["decimal_t2_lookup_reads"] == 12418
    assert arena.ledger.counters["decimal_t2_lookup_templates"] == 4
    before = arena.ledger.snapshot()
    assert arena.emit_expression(handle, *arguments) == output
    assert (
        arena.ledger.counters["decimal_t2_lookup_reads"]
        == before.counters["decimal_t2_lookup_reads"]
    )
    for left, symbol, right in ((757, 0, 0), (0, 20, 0), (0, 0, 179), (1023, 31, 255)):
        values = (left, symbol, right)
        assignment = {
            PortVariable(0, side, "complete-t2", bit): bool(values[side] & (1 << bit))
            for side, width in enumerate((10, 5, 8))
            for bit in range(width)
        }
        assert arena.evaluate(output, assignment) == 0


def test_constant_arguments_and_foreign_ownership_precede_factor_publication() -> None:
    arena, other = DiamondKernelArena(), DiamondKernelArena()
    handle = arena.intern(_load_base10_t2_kernel())
    for left, symbol, right in ((0, 0, 0), (756, 19, 178), (231, 7, 33)):
        arguments = tuple(
            arena.constant(domain, value)
            for domain, value in zip((757, 20, 179), (left, symbol, right), strict=True)
        )
        result = arena.emit_expression(handle, *arguments)
        assert arena.evaluate(result, {}) == _load_base10_t2_kernel().emit(
            left, symbol, right
        )
    assert arena._reverse_emitter is None
    foreign = other.variable(757, PortVariable(0, 0, "foreign", 0))
    symbol_expression, right_expression = (
        arena.constant(20, 0),
        arena.variable(179, PortVariable(0, 2, "foreign", 0)),
    )
    before = arena.ledger.snapshot()
    with pytest.raises(ValueError):
        arena.emit_expression(handle, foreign, symbol_expression, right_expression)
    assert arena.ledger.snapshot() == before


def test_same_named_finite_kernel_does_not_gain_factorization_authority() -> None:
    arena = DiamondKernelArena()
    fake = FiniteBlockEffect(
        base=10,
        exponent=2,
        left_count=2,
        right_count=2,
        alphabet_size=20,
        initial_left=0,
        initial_right=0,
        left_transitions=array("H", [0] * 40),
        right_transitions=array("H", [0] * 40),
        outputs=bytes([3] * 80),
        kernel_name="base10_t2_minimized_757x179",
        storage_bytes=240,
        uncompressed_bytes=240,
        blank_left_tail=2,
        blank_right_tail=1,
        stable_blank_output=True,
    )
    kernel = arena.intern(fake)
    left = arena.variable(2, PortVariable(0, 0, "fake", 0))
    right = arena.variable(2, PortVariable(0, 2, "fake", 0))
    result = arena.emit_expression(kernel, left, arena.constant(20, 0), right)
    assert (
        arena.evaluate(
            result,
            {PortVariable(0, 0, "fake", 0): False, PortVariable(0, 2, "fake", 0): True},
        )
        == 3
    )
    assert arena._reverse_emitter is None
