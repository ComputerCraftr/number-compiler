"""Consumer programs may share storage while their bound outputs stay distinct."""

import pytest

from devtools.verification.reverse_consumer_audit import audit
from devtools.verification.reverse_geometry_context import ReverseGeometryContext
from devtools.verification.threshold_expressions import ThresholdExpressions
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded

pytestmark = pytest.mark.validation


def test_shared_schema_preserves_distinct_bindings_and_exact_composition() -> None:
    e = ThresholdExpressions()
    x, y = e.variable(10, 0), e.variable(10, 1)
    table = tuple(int(v >= 5) for v in range(10))
    left = e.table(x, 2, table)
    right = e.table(y, 2, tuple(table))
    assert left != right
    assert e.consumer_schema_id(left) == e.consumer_schema_id(right)
    assert e.consumer_program(left)[2] is e.consumer_program(right)[2]
    assert e.evaluate((left, right), (2, 8)) == (0, 1)
    complement = e.table(left, 2, (1, 0))
    direct = e.table(x, 2, tuple(1 - value for value in table))
    assert complement == direct
    for value in range(10):
        assert e.evaluate((complement,), (value,)) == (int(value < 5),)
    with pytest.raises(ValueError, match="foreign consumer schema"):
        ThresholdExpressions().resolve_schema(e.consumer_schema_id(left))
    with pytest.raises(ValueError, match="not a finite consumer"):
        e.consumer_schema_id(x)


def test_schema_storage_is_charged_and_constant_consumers_need_no_schema() -> None:
    e = ThresholdExpressions(max_nodes=3)
    x = e.variable(10, 0)
    e.table(x, 2, (0,) * 5 + (1,) * 5)
    assert len(e.nodes) + len(e.schemas) == 3
    with pytest.raises(BlockContextBudgetExceeded):
        e.table(x, 2, (1,) * 5 + (0,) * 5)
    assert len(e.nodes) + len(e.schemas) == 3
    folded = ThresholdExpressions()
    y = folded.variable(10, 0)
    assert folded.table(y, 2, (0,) * 10) == folded.constant(2, 0)
    assert not folded.schemas
    selection = ThresholdExpressions(max_work=100)
    condition = selection.variable(2, 0)
    yes, no = selection.variable(64, 1), selection.variable(64, 2)
    before = len(selection.nodes)
    with pytest.raises(BlockContextBudgetExceeded, match="work budget"):
        selection.select(condition, yes, no)
    assert len(selection.nodes) == before


def test_audit_separates_shared_programs_from_growing_bindings() -> None:
    context = ReverseGeometryContext(9)
    action = context.primitive()
    rows: list[dict[str, object]] = []
    for _ in range(3):
        action = context.compose(action, action)
        rows.append(audit(context, action))
    # Native domain-monoid operations replace redundant unary carry tests.
    assert {row["unique_consumer_schema_ids"] for row in rows} == {42}
    assert len({row["unique_binding_family_ids"] for row in rows}) == 3
    for row in rows:
        assert (
            row["physical_consumer_table_tuples"] == row["unique_consumer_schema_ids"]
        )
        assert (
            row["physical_consumer_table_entries"]
            == row["unique_consumer_program_entries"]
        )
        assert row["max_residual_hole_arity"] == 1
        assert row["max_binding_input_arity"] == 16
        assert row["successor_refinement_classes"] is None
        assert row["successor_conflicts"] is None
        assert row["independent_harmonic_factors_in_action"] == 0
        assert row["independent_carry_border_harmonic_inputs"] == 0
        assert row["source_input_roles"] == {
            "width": 1,
            "domain": 5,
            "f5": 5,
            "parity": 5,
        }
        carry_nodes = row["derived_carry_operation_nodes"]
        assert isinstance(carry_nodes, int) and carry_nodes > 0
