"""Skew consumer exactness and absence of redundant persistent coordinates."""

from itertools import product

import pytest

from devtools.verification.reverse_geometry_context import ReverseGeometryContext
from devtools.verification.threshold_expressions import ThresholdExpressions
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.fields.radix import reverse_pair_sums
from number_compiler.arithmetic.formula.skew_residue_laws import (
    skew_normalized_digit,
    skew_pair_value,
)

pytestmark = pytest.mark.validation


def test_all_point_ports_and_two_operand_consumers() -> None:
    e = ThresholdExpressions()
    inputs = tuple(e.variable(size, slot) for slot, size in enumerate((3, 9, 2) * 2))
    output = e.skew_pair_domain(*inputs)
    for a, b, ca, cb in product(range(19), range(19), range(2), range(2)):
        da, db = (a > 9) + (a >= 9), (b > 9) + (b >= 9)
        # bool+bool above has integer result and gives LT0/EQ1/GT2.
        assert skew_pair_value(da, a % 9) == a
        assert skew_normalized_digit(da, a % 9, ca) == (a + ca) % 10
        total = (a + ca) % 10 + (b + cb) % 10
        assert e.evaluate((output,), (da, a % 9, ca, db, b % 9, cb)) == (
            (total > 9) + (total >= 9),
        )
    assert e.skew_pair_domain(*inputs[3:], *inputs[:3]) == output


@pytest.mark.parametrize(("capacity", "events"), ((9, 16), (16, 32)))
def test_mod9_power_replaces_value_planes_and_never_materializes(
    monkeypatch: pytest.MonkeyPatch,
    capacity: int,
    events: int,
) -> None:
    context = ReverseGeometryContext(capacity, value_quotient="mod9")

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("mod9 compilation materialized a legacy value view")

    with monkeypatch.context() as poison:
        poison.setattr(context, "_residue", forbidden)
        poison.setattr(context.expressions, "growth_symbol", forbidden)
        poison.setattr(context.expressions, "decimal_sum_domain", forbidden)
        action = context.primitive()
        poison.setattr(context, "primitive", forbidden)
        poison.setattr(context, "observe", forbidden)
        poison.setattr(context.expressions, "evaluate", forbidden)
        for _ in range(events.bit_length() - 1):
            action = context.compose(action, action)
    metrics = context.metrics(action)
    for name in (
        "reachable_residue10_nodes",
        "reachable_q_view_nodes",
        "independent_reset_nodes",
        "independent_carry_vector_nodes",
        "f5_nodes",
        "f2_nodes",
    ):
        assert metrics[name] == 0
    assert context.sizes == (capacity + 1, *((3, 9) * ((capacity + 1) // 2)))
    assert metrics["primitive_successors"] == 1
    for source in (reverse_pair_sums(196, 10), (0,) * 9, (2,) * 9, (16,) * 8):
        target = source
        for _ in range(events):
            target = pair_step(target, 10)[0]
        assert context.observe(action, context.binding(source)) == (
            target if len(target) <= capacity else None
        )


def test_mod9_small_powers_admission_and_growth_family() -> None:
    context = ReverseGeometryContext(4, value_quotient="mod9")
    actions = [context.primitive()]
    for _ in range(3):
        actions.append(context.compose(actions[-1], actions[-1]))
    for width in range(1, 4):
        for half in product(range(19), repeat=(width + 1) // 2):
            if width % 2 and half[-1] % 2:
                continue
            source = half + (half[:-1] if width % 2 else half)[::-1]
            expected = source
            previous = 0
            for action in actions:
                for _ in range(previous, action.events):
                    expected = pair_step(expected, 10)[0]
                previous = action.events
                assert context.observe(action, context.binding(source)) == (
                    expected if len(expected) <= 4 else None
                )
    invalid = list(context.binding((2, 2)))
    invalid[1] = 1
    assert context.observe(actions[0], tuple(invalid)) is None
    for length in (1, 2, 3, 8, 17):
        c = ReverseGeometryContext(length + 1, value_quotient="mod9")
        action = c.primitive()
        source = (2,) * length
        for coefficient in (4, 8, 16):
            observed = c.observe(action, c.binding(source))
            assert observed == (coefficient,) * length
            assert observed is not None
            source = observed
        assert c.observe(action, c.binding(source)) == (7,) + (14,) * (length - 1) + (
            7,
        )


def test_mod9_rejects_noncanonical_bindings() -> None:
    with pytest.raises(ValueError, match="EQ"):
        skew_pair_value(1, 1)
    with pytest.raises(ValueError, match="choose"):
        ReverseGeometryContext(4, growth_quotient=True, value_quotient="mod9")
    context = ReverseGeometryContext(4, value_quotient="mod9")
    for source in ((True, True), (19, 19), (3,), (1, 2)):
        with pytest.raises((ValueError, TypeError)):
            context.binding(source)
