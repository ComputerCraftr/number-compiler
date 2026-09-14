"""Whole bounded contexts retain growth and midpoint definedness under squaring."""

from itertools import product

import pytest

from devtools.proofs import exact_oracle
from devtools.proofs.reverse_cocycle_context import BoundedReverseCocycle
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_cocycle_value,
)
from number_compiler.sequences.reverse_add.cocycle_temporal import CocycleAction
from number_compiler.sequences.reverse_add.factored_carrier import DOMAINS


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


def test_orbit_binding_rejects_nonpair_contexts() -> None:
    context = BoundedReverseCocycle(3, symmetric=True)
    with pytest.raises(ValueError, match="reflected"):
        context.binding((2, 4))
    with pytest.raises(ValueError, match="even parity"):
        context.binding((2, 9, 2))
