"""Exact geometry controls and explicit limits of harmonic/structural identity."""

from itertools import product

import pytest

from devtools.experiments.reverse_add.cocycle_carrier import CocycleReverseCarrier
from devtools.verification.reverse_geometry_context import ReverseGeometryContext
from devtools.verification.reverse_threshold_geometry import ThresholdGeometry
from devtools.verification.threshold_expressions import ThresholdExpressions
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.radix import reverse_pair_sums
from number_compiler.arithmetic.formula.symmetry_frame import (
    FixedRealCyclotomicGerm,
    ReverseAddSymmetryProjection,
)
from number_compiler.arithmetic.functions.decision import MultiTerminalDecisionArena

pytestmark = pytest.mark.validation


def test_harmonic_kernel_collision_changes_threshold_geometry() -> None:
    left = (8,) * 9
    right = (9, 10, 10, 10, 10, 10, 10, 10, 9)
    germs = []
    for row in (left, right):
        views = {
            order: ReverseAddSymmetryProjection.from_coefficients(
                row, order=order, bits=5
            ).fixed_coordinates
            for order in (2, 4, 8)
        }
        germs.append(FixedRealCyclotomicGerm.from_fixed_views(views, bits=5))
    assert germs[0] == germs[1]
    assert pair_step(left, 10)[0] != pair_step(right, 10)[0]
    assert tuple((v > 9) - (v < 9) for v in left) != tuple(
        (v > 9) - (v < 9) for v in right
    )


def test_whole_cell_range_proof_merges_distinct_value_expressions(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    e = ThresholdExpressions()
    g = ThresholdGeometry(e)
    variable = e.variable(2, 0)
    left = e.table(variable, 10, (1, 2))
    right = e.table(variable, 10, (3, 4))
    other = e.table(variable, 10, (0, 1))

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("uniform range proof expanded a local comparator")

    monkeypatch.setattr(e, "affine", forbidden)
    a = g.uniform(left, right, 10**100)
    b = g.uniform(other, right, 10**100)
    assert a == b and a.word.symbol is not None
    assert e.resolve(e.handle(a.word.symbol)).data == (0,)
    assert g.visits == g.uniform_proofs == 2 and g.local_consumers == 0


def test_spatial_threshold_intervals_and_local_consumers_are_exact() -> None:
    e = ThresholdExpressions()
    g = ThresholdGeometry(e)
    variable = e.variable(10, 0)
    left = tuple(e.constant(10, v) for v in (0, 1, 4, 5, 8, 9))
    geometry = g.compare(left, (variable,) * len(left))
    roots = g.coordinates(geometry)
    for value in range(10):
        expected = tuple(
            0 if v + value < 9 else 1 if v + value == 9 else 2
            for v in (0, 1, 4, 5, 8, 9)
        )
        assert e.evaluate(roots, (value,)) == expected


def test_affine_substitution_preserves_correlation_and_finite_consumers() -> None:
    e = ThresholdExpressions()
    x, y = e.variable(5, 0), e.variable(5, 1)
    linear = e.affine(5, ((x, 2), (y, 3)), 4)
    assert e.affine(5, ((linear, 1), (x, 3), (y, 2)), 1) == e.constant(5, 0)
    consumer = e.table(linear, 2, (0, 0, 1, 1, 1))
    substituted = e.substitute((consumer,), {0: y, 1: x})
    for a, b in product(range(5), repeat=2):
        assert e.evaluate(substituted, (a, b)) == e.evaluate((consumer,), (b, a))
    with pytest.raises(ValueError, match="incomplete"):
        e.substitute((consumer,), {0: x})
    with pytest.raises(ValueError, match="foreign"):
        e.select(consumer, ThresholdExpressions().constant(5, 0), x)
    tiny = ThresholdExpressions(max_nodes=1)
    tiny.constant(2, 0)
    with pytest.raises(BlockContextBudgetExceeded):
        tiny.constant(2, 1)
    for invalid_charge in (-1, True):
        with pytest.raises(ValueError, match="work charges"):
            e.tick(invalid_charge)


@pytest.mark.parametrize("growth_quotient", (False, True))
def test_196_a16_without_primitive_bdd_or_midpoint_observation(
    monkeypatch: pytest.MonkeyPatch,
    growth_quotient: bool,
) -> None:
    context = ReverseGeometryContext(9, growth_quotient=growth_quotient)
    action = context.primitive()
    source = reverse_pair_sums(196, 10)
    binding = context.binding(source)
    with monkeypatch.context() as poison:

        def forbidden(*args: object, **kwargs: object) -> None:
            raise AssertionError("threshold powering expanded a primitive or BDD")

        poison.setattr(context, "primitive", forbidden)
        poison.setattr(context, "observe", forbidden)
        poison.setattr(context.expressions, "evaluate", forbidden)
        poison.setattr(MultiTerminalDecisionArena, "build_labeled_boxes", forbidden)
        poison.setattr(CocycleReverseCarrier, "successor", forbidden)
        for _ in range(4):
            action = context.compose(action, action)
    expected = source
    for _ in range(16):
        expected = pair_step(expected, 10)[0]
    assert context.observe(action, binding) == expected
    assert context.primitive_successors == 1 and context.temporal_compositions == 4
    assert context.metrics(action)["retained_expression_nodes"] < 30000
    # This deliberately prevents interpreting small construction counts as a
    # closed nonlinear quotient: observation still resolves many consumer gates.
    assert context.expressions.observed_tables > 16
    for other in ((0,) * 9, (2,) * 9, (16,) * 8):
        target: tuple[int, ...] = other
        for _ in range(16):
            target = pair_step(target, 10)[0]
        assert context.observe(action, context.binding(other)) == (
            target if len(target) <= 9 else None
        )


@pytest.mark.parametrize("growth_quotient", (False, True))
def test_small_complete_context_powers_and_overflow_are_exact(
    growth_quotient: bool,
) -> None:
    context = ReverseGeometryContext(4, growth_quotient=growth_quotient)
    actions = [context.primitive()]
    for _ in range(3):
        actions.append(context.compose(actions[-1], actions[-1]))
    for width in range(1, 4):
        for half in product(range(19), repeat=(width + 1) // 2):
            if width % 2 and half[-1] % 2:
                continue
            source = half + (half[:-1] if width % 2 else half)[::-1]
            binding = context.binding(source)
            expected = source
            previous = 0
            for action in actions:
                for _ in range(previous, action.events):
                    expected = pair_step(expected, 10)[0]
                previous = action.events
                assert context.observe(action, binding) == (
                    expected if len(expected) <= 4 else None
                )
    invalid = list(context.binding((2, 2)))
    invalid[1] = 1  # EQ cannot describe coefficient 2.
    assert context.observe(actions[-1], tuple(invalid)) is None
