"""Complete primitive closure and reduced output-complete finite expressions."""

from __future__ import annotations

from array import array
from itertools import product
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BlockEffect,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.diamond_kernel import (
    DiamondKernelArena,
    FiniteExpression,
)
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect


def finite_identity() -> FiniteBlockEffect:
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
        outputs=bytes(range(4)),
        kernel_name="identity",
        storage_bytes=36,
        uncompressed_bytes=36,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )


def assignment(
    port: PortVariable,
    value: int,
    domain: int,
) -> dict[PortVariable, bool]:
    return {
        PortVariable(port.time, port.side, port.role, port.bit + bit): bool(
            value & (1 << bit)
        )
        for bit in range((domain - 1).bit_length())
    }


@pytest.mark.parametrize(
    "effect",
    [
        BaseBlockEffect(3),
        DigitNormalizeBlockEffect(3),
        CollatzPhysicalBlockEffect(),
        finite_identity(),
    ],
)
def test_complete_primitive_scalar_interfaces_preserve_every_declared_state(
    effect: BlockEffect,
) -> None:
    arena = DiamondKernelArena()
    handle = arena.intern(effect)
    assert arena.intern(effect) == handle
    kernel = arena.kernel(handle)
    for side in BoundarySide:
        domain = kernel.domain(side)
        assert domain[kernel.initial(side)] == effect.initial(side)
        for state, symbol in product(range(len(domain)), range(effect.blank + 1)):
            assert domain[kernel.advance(side, state, symbol)] == effect.advance(
                side, domain[state], symbol
            )
    for left, symbol, right in product(
        range(kernel.left_count), range(kernel.blank + 1), range(kernel.right_count)
    ):
        assert kernel.emit(left, symbol, right) == effect.emit(
            kernel.left[left], symbol, kernel.right[right]
        )
    assert arena.ledger.counters["primitive_output_evaluations"] > 0
    assert all(row.accounting_delta == 0 for row in arena.ledger.inventory())


def test_parametric_collatz_functions_are_complete_and_preserve_blank_behavior() -> (
    None
):
    arena = DiamondKernelArena()
    handle = arena.intern(CollatzPhysicalBlockEffect())
    kernel = arena.kernel(handle)
    lp, sp, rp = (PortVariable(0, side, "kernel", 0) for side in range(3))
    left = arena.variable(kernel.left_count, lp)
    symbol = arena.variable(kernel.blank + 1, sp)
    right = arena.variable(kernel.right_count, rp)
    output = arena.emit_expression(handle, left, symbol, right)
    next_left = arena.advance_expression(handle, BoundarySide.LEFT, left, symbol)
    next_right = arena.advance_expression(handle, BoundarySide.RIGHT, right, symbol)
    for left_state, a, r in product(
        range(kernel.left_count), range(kernel.blank + 1), range(kernel.right_count)
    ):
        inputs = (
            assignment(lp, left_state, kernel.left_count)
            | assignment(sp, a, kernel.blank + 1)
            | assignment(rp, r, kernel.right_count)
        )
        assert arena.evaluate(output, inputs) == kernel.emit(left_state, a, r)
        assert arena.evaluate(next_left, inputs) == kernel.advance(
            BoundarySide.LEFT, left_state, a
        )
        assert arena.evaluate(next_right, inputs) == kernel.advance(
            BoundarySide.RIGHT, r, a
        )
    before = arena.ledger.snapshot()
    assert arena.emit_expression(handle, left, symbol, right) == output
    assert (
        arena.ledger.counters["primitive_output_evaluations"]
        == before.counters["primitive_output_evaluations"]
    )


def test_different_symbol_histories_alias_as_complete_transfer_ids() -> None:
    arena = DiamondKernelArena()
    kernel = arena.intern(DigitNormalizeBlockEffect(3))
    state = arena.variable(4, PortVariable(0, 0, "normalizer", 0))
    zero = arena.constant(6, 0)
    one = arena.constant(6, 1)
    a = arena.advance_expression(kernel, BoundarySide.LEFT, state, zero)
    b = arena.advance_expression(kernel, BoundarySide.LEFT, state, one)
    assert a == b  # both symbols reset carry while preserving blank/sink handling
    aa = arena.advance_expression(kernel, BoundarySide.LEFT, a, zero)
    assert aa == a
    assert all(type(node) is FiniteExpression for node in arena._expressions)


def test_simultaneous_substitution_preserves_parametric_function_identity() -> None:
    arena = DiamondKernelArena()
    port = PortVariable(0, 0, "bit", 0)
    value = arena.variable(2, port)
    negated = arena.functions.negate(arena.expression(value).bits[0])
    opposite = arena.substitute(value, {port: negated})
    assert arena.substitute(opposite, {port: negated}) == value
    assert arena.evaluate(opposite, {port: False}) == 1
    assert arena.evaluate(opposite, {port: True}) == 0
    arena.ledger.evict_query_memos()
    assert arena.substitute(opposite, {port: negated}) == value


def test_foreign_handles_and_invalid_domains_fail_before_warm_work() -> None:
    a, b = DiamondKernelArena(), DiamondKernelArena()
    ka, kb = (
        a.intern(CollatzPhysicalBlockEffect()),
        b.intern(CollatzPhysicalBlockEffect()),
    )
    state, symbol = a.constant(6, 0), a.constant(3, 0)
    a.advance_expression(ka, BoundarySide.LEFT, state, symbol)
    before = a.ledger.snapshot()
    with pytest.raises(ValueError):
        a.advance_expression(kb, BoundarySide.LEFT, state, symbol)
    with pytest.raises(ValueError):
        a.advance_expression(ka, BoundarySide.LEFT, b.constant(6, 0), symbol)
    with pytest.raises(TypeError):
        a.expression(
            cast(
                "TransferSummaryID",
                ActionProgramID(a.owner, "diamond-finite-expression", state.local_id),
            )
        )
    with pytest.raises(ValueError):
        a.kernel(ActionProgramID(a.owner, "diamond-kernel", 10000))
    with pytest.raises(TypeError):
        a.kernel(
            cast(
                "ActionProgramID",
                TransferSummaryID(a.owner, "diamond-kernel", ka.local_id),
            )
        )
    assert a.ledger.snapshot() == before


def test_zero_budget_and_nonprimitive_admission_publish_no_kernel() -> None:
    ledger = ResourceLedger(max_nodes=0)
    with pytest.raises(BlockContextBudgetExceeded):
        DiamondKernelArena(ledger)
    assert ledger.nodes == ledger.entries == 0
    arena = DiamondKernelArena()

    class Pretend:
        canonical_key = ("collatz-physical-block", 1)

    before = arena.ledger.snapshot()
    with pytest.raises(TypeError):
        arena.intern(cast("BlockEffect", Pretend()))
    assert arena.ledger.snapshot() == before


def test_nonblank_observer_is_complete_for_physical_and_pair_alphabets(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.observation.diamond_observers import (
        NonblankBlockEffect,
    )

    for base, blank in ((2, 2), (10, 19)):
        effect = NonblankBlockEffect(base, blank)
        arena = DiamondKernelArena()
        handle = arena.intern(effect)
        kernel = arena.kernel(handle)
        assert kernel.left_count == kernel.right_count == 2
        assert kernel.is_absorbing(BoundarySide.LEFT, 1)
        assert kernel.is_absorbing(BoundarySide.RIGHT, 1)
        assert not kernel.is_absorbing(BoundarySide.LEFT, 0)
        for left, symbol, right in product((0, 1), range(blank + 1), (0, 1)):
            assert kernel.emit(left, symbol, right) == symbol

        def forbidden(*args: object) -> Never:
            raise AssertionError("nonblank boundary query must not emit an output tape")

        with monkeypatch.context() as patch:
            patch.setattr(NonblankBlockEffect, "emit", forbidden)
            for side in BoundarySide:
                for word in ((blank,) * 8, (blank, 0, blank), (1, blank), ()):
                    state = kernel.initial(side)
                    for symbol in word:
                        state = kernel.advance(side, state, symbol)
                    assert state == int(any(symbol != blank for symbol in word))
        state_function = arena.variable(2, PortVariable(0, 0, "activity", 0))
        inactive = arena.advance_expression(
            handle, BoundarySide.LEFT, state_function, arena.constant(blank + 1, blank)
        )
        active = arena.advance_expression(
            handle, BoundarySide.LEFT, state_function, arena.constant(blank + 1, 0)
        )
        assert inactive == state_function
        assert active == arena.constant(2, 1)
        with pytest.raises((AttributeError, TypeError)):
            effect.__setattr__("blank", 0)


def test_absorber_classification_matches_complete_primitive_alphabet() -> None:
    arena = DiamondKernelArena()
    kernel = arena.kernel(arena.intern(CollatzPhysicalBlockEffect()))
    for side in BoundarySide:
        for state in range(len(kernel.domain(side))):
            expected = all(
                kernel.advance(side, state, symbol) == state
                for symbol in range(kernel.blank + 1)
            )
            assert kernel.is_absorbing(side, state) == expected
    before = arena.ledger.snapshot()
    with pytest.raises(ValueError):
        kernel.is_absorbing(BoundarySide.LEFT, -1)
    assert arena.ledger.snapshot() == before


def test_universal_primitive_templates_are_substituted_without_reenumeration() -> None:
    arena = DiamondKernelArena()
    kernel = arena.intern(CollatzPhysicalBlockEffect())

    def variables(
        time: int,
    ) -> tuple[TransferSummaryID, TransferSummaryID, TransferSummaryID]:
        return (
            arena.variable(6, PortVariable(time, 0, "q", 0)),
            arena.variable(3, PortVariable(time, 1, "a", 0)),
            arena.variable(3, PortVariable(time, 2, "r", 0)),
        )

    first = variables(0)
    arena.advance_expression(kernel, BoundarySide.LEFT, first[0], first[1])
    arena.emit_expression(kernel, *first)
    assert len(arena._templates) == 2
    before = arena.ledger.snapshot()
    second = variables(1)
    transition = arena.advance_expression(
        kernel, BoundarySide.LEFT, second[0], second[1]
    )
    output = arena.emit_expression(kernel, *second)
    assert (
        arena.ledger.counters["primitive_transition_evaluations"]
        == before.counters["primitive_transition_evaluations"]
    )
    assert (
        arena.ledger.counters["primitive_output_evaluations"]
        == before.counters["primitive_output_evaluations"]
    )
    assert arena.ledger.counters["diamond_kernel_template_evaluations"] == 2
    for state, symbol, right in product(range(6), range(3), range(3)):
        inputs = (
            assignment(PortVariable(1, 0, "q", 0), state, 6)
            | assignment(PortVariable(1, 1, "a", 0), symbol, 3)
            | assignment(PortVariable(1, 2, "r", 0), right, 3)
        )
        actual = arena.kernel(kernel)
        assert arena.evaluate(transition, inputs) == actual.advance(
            BoundarySide.LEFT, state, symbol
        )
        assert arena.evaluate(output, inputs) == actual.emit(state, symbol, right)
    arena.ledger.evict_query_memos()
    before = arena.ledger.snapshot()
    assert arena.emit_expression(kernel, *second) == output
    assert (
        arena.ledger.counters["primitive_output_evaluations"]
        == before.counters["primitive_output_evaluations"]
    )
    assert all(row.accounting_delta == 0 for row in arena.ledger.inventory())


def test_shannon_templates_keep_reduced_branches_and_bounded_primitive_workspace() -> (
    None
):
    arena = DiamondKernelArena()
    handle = arena.intern(BaseBlockEffect(10))
    kernel = arena.kernel(handle)
    domains = (kernel.left_count, kernel.blank + 1, kernel.right_count)
    ports = tuple(
        PortVariable(0, side, "complete-base-interface", 0) for side in range(3)
    )
    arguments = tuple(
        arena.variable(domain, port)
        for domain, port in zip(domains, ports, strict=True)
    )
    output = arena.emit_expression(handle, *arguments)
    counters = arena.ledger.counters
    assert (
        counters["diamond_kernel_shannon_leaf_evaluations"]
        == domains[0] * domains[1] * domains[2]
    )
    assert counters["diamond_kernel_shannon_peak_frames"] <= sum(
        (domain - 1).bit_length() for domain in domains
    )
    assert counters["diamond_kernel_invalid_subtrees"] > 0
    # Row-by-row truth accumulation retained over 90,000 partial Boolean
    # functions. Shannon construction retains only reduced subtree functions.
    assert len(arena.functions._nodes) < 2_000
    for left, symbol, right in product(*(range(domain) for domain in domains)):
        inputs = {}
        for port, value, domain in zip(
            ports, (left, symbol, right), domains, strict=True
        ):
            inputs.update(assignment(port, value, domain))
        assert arena.evaluate(output, inputs) == kernel.emit(left, symbol, right)
    # Unused input codes have the same explicit zero extension at every leaf.
    invalid = {}
    for port, domain in zip(ports, domains, strict=True):
        invalid.update(assignment(port, (1 << (domain - 1).bit_length()) - 1, domain))
    assert arena.evaluate(output, invalid) == 0


def test_fixed_primitive_symbol_specializes_before_truth_construction() -> None:
    arena = DiamondKernelArena()
    handle = arena.intern(BaseBlockEffect(10))
    kernel = arena.kernel(handle)
    left_port, right_port = (
        PortVariable(0, 0, "left", 0),
        PortVariable(0, 1, "right", 0),
    )
    left = arena.variable(kernel.left_count, left_port)
    right = arena.variable(kernel.right_count, right_port)
    fixed = arena.constant(kernel.blank + 1, 7)
    result = arena.emit_expression(handle, left, fixed, right)
    assert (
        arena.ledger.counters["diamond_kernel_shannon_leaf_evaluations"]
        == kernel.left_count * kernel.right_count
    )
    assert next(iter(arena._templates)).constants == (None, 7, None)
    for lstate, rstate in product(range(kernel.left_count), range(kernel.right_count)):
        inputs = assignment(left_port, lstate, kernel.left_count) | assignment(
            right_port, rstate, kernel.right_count
        )
        assert arena.evaluate(result, inputs) == kernel.emit(lstate, 7, rstate)
