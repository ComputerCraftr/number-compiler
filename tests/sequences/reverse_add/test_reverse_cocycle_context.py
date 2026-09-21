"""Whole bounded contexts retain growth and midpoint definedness under squaring."""

from itertools import product

import pytest

from devtools.experiments.reverse_add.cocycle_temporal import CocycleAction
from devtools.experiments.reverse_add.factored_carrier import DOMAINS
from devtools.proofs import exact_oracle
from devtools.proofs.reverse_cocycle_context import BoundedReverseCocycle
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_cocycle_value,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FunctionSignature,
)
from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID


def _check(
    context: BoundedReverseCocycle, action: CocycleAction, field: tuple[int, ...]
) -> None:
    binding = context.binding(field)
    expected = field
    with exact_oracle():
        for _ in range(action.events):
            expected, _ = pair_step(expected, 10)
    width = context.bits.evaluate(action.outputs[0], binding)
    if len(expected) > context.capacity:
        assert width is None
        assert all(context.bits.evaluate(f, binding) is None for f in action.outputs)
        return
    assert width == len(expected)
    for i, symbol in enumerate(expected):
        slot = min(i, width - 1 - i) if context.symmetric else i
        coords = [
            context.bits.evaluate(f, binding)
            for f in action.outputs[1 + 3 * slot : 4 + 3 * slot]
        ]
        assert all(c is not None for c in coords)
        domain, alpha, epsilon = (int(c) for c in coords if c is not None)
        assert decimal_cocycle_value(DOMAINS[domain], alpha, epsilon) == symbol


def _scalar_compose(
    context: BoundedReverseCocycle,
    before: CocycleAction,
    after: CocycleAction,
) -> CocycleAction:
    """Previous per-function construction, retained as a bounded oracle."""
    bits, cocycles = context.bits, context.cocycles
    mapping = dict(
        zip((port.variable for port in before.ports), before.outputs, strict=True)
    )

    def pull(function: FactoredFunctionID) -> FactoredFunctionID:
        inputs = bits.resolve(function).signature.inputs
        return bits.substitute(
            function,
            {port.variable: mapping[port.variable] for port in inputs},
        )

    false = bits.constant(FunctionSignature((), BOOL), 0)
    admitted = bits.select(before.admissible, pull(after.admissible), false)
    outputs = tuple(pull(function) for function in after.outputs)
    residuals = tuple(
        cocycles.compose_temporal(
            residual,
            mapping,
            before.cocycles[0],
        )
        for residual in after.cocycles
    )
    full = bits.constant(FunctionSignature(before.ports, BOOL), 1)
    admitted = bits.select(full, admitted, false)
    residual_functions = tuple(cocycles.resolve(value) for value in residuals)
    for function in (*outputs, *residual_functions):
        admitted = bits.select(
            admitted,
            bits.domain_predicate(function),
            false,
        )
    return CocycleAction(
        before.ports,
        tuple(bits.restrict(function, admitted) for function in outputs),
        tuple(cocycles.restrict(value, admitted) for value in residuals),
        admitted,
        before.events + after.events,
    )


@pytest.mark.parametrize("symmetric", (False, True))
def test_three_cell_primitive_all_symmetric_fields_and_reflected_growth(
    symmetric: bool,
) -> None:
    context = BoundedReverseCocycle(3, symmetric=symmetric)
    action = context.compile_primitive()
    for symbol in range(0, 19, 2):
        _check(context, action, (symbol,))
    for symbol in range(19):
        _check(context, action, (symbol, symbol))
    for edge, middle in product(range(19), range(0, 19, 2)):
        _check(context, action, (edge, middle, edge))
    assert context.temporal.primitive_successors == 1


@pytest.mark.parametrize("symmetric", (False, True))
def test_bounded_squaring_retains_intermediate_growth_without_primitive_replay(
    monkeypatch: pytest.MonkeyPatch,
    symmetric: bool,
) -> None:
    context = BoundedReverseCocycle(2, symmetric=symmetric)
    action = context.compile_primitive()
    with monkeypatch.context() as patched:

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError(
                "primitive execution or midpoint observation during squaring"
            )

        patched.setattr(context, "compile_primitive", forbidden)
        patched.setattr(context.temporal, "primitive", forbidden)
        patched.setattr(context.bits, "evaluate", forbidden)
        squared = context.temporal.compose(action, action)
    for symbol in range(0, 19, 2):
        _check(context, squared, (symbol,))
    for symbol in range(19):
        _check(context, squared, (symbol, symbol))
    assert context.temporal.primitive_successors == 1
    assert context.temporal.temporal_compositions == 1


@pytest.mark.parametrize("symmetric", (False, True))
def test_batch_temporal_composition_matches_scalar_complete_interface(
    symmetric: bool,
) -> None:
    context = BoundedReverseCocycle(3, symmetric=symmetric)
    primitive = context.compile_primitive()
    squared = context.temporal.compose(primitive, primitive)
    evaluations = context.bits.ledger.counters["semantic_bit_composition_evaluations"]
    hits = context.bits.ledger.counters.get("semantic_bit_composition_hits", 0)
    restrictions = context.bits.ledger.counters.get(
        "semantic_bit_batch_restriction_evaluations", 0
    )
    temporal_hits = context.temporal.temporal_composition_cache_hits
    assert context.temporal.compose(primitive, primitive) == squared
    assert (
        context.bits.ledger.counters["semantic_bit_composition_evaluations"]
        == evaluations
    )
    assert context.bits.ledger.counters.get("semantic_bit_composition_hits", 0) == hits
    assert (
        context.bits.ledger.counters.get(
            "semantic_bit_batch_restriction_evaluations", 0
        )
        == restrictions
    )
    assert context.temporal.temporal_composition_cache_hits == temporal_hits + 1
    assert squared == _scalar_compose(context, primitive, primitive)
    for field in ((0,), (18,), (1, 1), (18, 18), (2, 9, 2)):
        reflected = field == field[::-1]
        valid_center = len(field) % 2 == 0 or field[len(field) // 2] % 2 == 0
        if not symmetric or reflected and valid_center:
            _check(context, squared, field)


def test_complete_interface_batch_budget_failure_publishes_nothing() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    context = BoundedReverseCocycle(2)
    primitive = context.compile_primitive()
    mapping = dict(
        zip(
            (port.variable for port in primitive.ports),
            primitive.outputs,
            strict=True,
        )
    )
    functions = (
        primitive.admissible,
        *primitive.outputs,
        *(context.cocycles.resolve(value) for value in primitive.cocycles),
    )
    ledger = context.bits.ledger
    before = ledger.snapshot()
    lengths = (
        len(context.bits.functions.nodes),
        len(context.bits.functions.keys),
        len(context.bits.nodes),
        len(context.bits.keys),
        len(context.bits._compositions),
    )
    ledger.tighten_limits(
        max_nodes=ledger.nodes,
        max_cache_entries=ledger.entries,
    )
    with pytest.raises(BlockContextBudgetExceeded):
        context.bits.substitute_many(functions, mapping)
    after = ledger.snapshot()
    assert (after.nodes, after.entries, after.inventory) == (
        before.nodes,
        before.entries,
        before.inventory,
    )
    assert lengths == (
        len(context.bits.functions.nodes),
        len(context.bits.functions.keys),
        len(context.bits.nodes),
        len(context.bits.keys),
        len(context.bits._compositions),
    )


def test_orbit_binding_rejects_nonpair_contexts() -> None:
    context = BoundedReverseCocycle(3, symmetric=True)
    with pytest.raises(ValueError, match="reflected"):
        context.binding((2, 4))
    with pytest.raises(ValueError, match="even parity"):
        context.binding((2, 9, 2))
