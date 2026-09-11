"""Demanded pullback, branch deadness, and failed-publication accounting."""

from unittest.mock import patch
from typing import cast

import pytest

from devtools.proofs.reverse_geometry_context import ReverseGeometryContext
from devtools.proofs.reverse_growth_attribution import attribute_growth
from devtools.proofs.reverse_successor_image_audit import _sources
from devtools.proofs.threshold_expressions import ThresholdExpressions
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded


def test_substitution_resolves_condition_before_rebuilding_unused_branch() -> None:
    e = ThresholdExpressions()
    condition = e.variable(2, 0)
    yes = e.table(e.variable(5, 1), 5, (1, 2, 3, 4, 0))
    no = e.variable(5, 2)
    root = e.select(condition, yes, no)
    replacement = e.variable(5, 3)
    false = e.constant(2, 0)
    count = len(e.nodes)
    with patch.object(e, "table", side_effect=AssertionError("rebuilt dead branch")):
        result = e.substitute((root,), {0: false, 2: replacement})
    assert result == (replacement,)
    assert len(e.nodes) == count
    assert e.substitution_select_branches_skipped == 1
    before_observed = e.observed_nodes
    assert e.evaluate((root,), (0, 2, 4)) == (4,)
    assert e.observed_nodes - before_observed == 3
    assert e.observed_tables == 0
    # Free selectors cannot discard either possible continuation.
    with pytest.raises(ValueError, match="incomplete temporal substitution"):
        e.substitute((root,), {0: condition, 2: replacement})


def test_pullback_matches_full_composition_without_primitive_or_evaluation() -> None:
    context = ReverseGeometryContext(4, value_quotient="mod9")
    primitive = context.primitive()
    domain = context.project(primitive, (1,))
    with (
        patch.object(context, "primitive", side_effect=AssertionError("primitive")),
        patch.object(
            context.expressions, "evaluate", side_effect=AssertionError("evaluation")
        ),
    ):
        pulled = context.pullback(primitive, domain)
        composed = context.compose(primitive, primitive)
    assert pulled == context.project(composed, (1,))
    assert context.primitive_successors == 1
    assert len(pulled.outputs) == 1
    assert len(composed.outputs) == len(context.sizes)


def test_consumer_pullback_associativity_on_complete_small_interface() -> None:
    context = ReverseGeometryContext(4, value_quotient="mod9")
    first = context.primitive()
    second = context.compose(first, first)
    consumer = context.project(first, (0, 1, 2))
    nested = context.pullback(first, context.pullback(second, consumer))
    direct = context.pullback(context.compose(first, second), consumer)
    e = context.expressions
    for width in range(1, 5):
        for source in _sources(width):
            binding = context.binding(source)
            left = e.evaluate((nested.admitted, *nested.outputs), binding)
            right = e.evaluate((direct.admitted, *direct.outputs), binding)
            assert left[0] == right[0]
            if left[0]:
                assert left == right


def test_failed_pullback_rolls_back_unpublished_ids_but_charges_work() -> None:
    context = ReverseGeometryContext(4, value_quotient="mod9")
    first = context.primitive()
    e = context.expressions
    nodes, schemas, keys, schema_keys = (
        list(e.nodes),
        list(e.schemas),
        dict(e.keys),
        dict(e._schema_keys),
    )
    e.max_nodes = len(nodes) + len(schemas) + e.auxiliary_nodes + 4
    with pytest.raises(BlockContextBudgetExceeded):
        context.compose(first, first)
    assert (e.nodes, e.schemas, e.keys, e._schema_keys) == (
        nodes,
        schemas,
        keys,
        schema_keys,
    )
    assert e.work > 0
    assert e.discarded_failed_nodes + e.discarded_failed_schemas > 0
    assert context.temporal_compositions == context.consumer_pullbacks == 0
    e.max_nodes = 30000
    second = context.compose(first, first)
    assert context.observe(second, context.binding((2,))) == (8,)


def test_growth_attribution_separates_free_action_and_bound_slice() -> None:
    context = ReverseGeometryContext(4, value_quotient="mod9")
    first = context.primitive()
    second = context.compose(first, first)
    result = attribute_growth(
        context, second, previous=first, binding=context.binding((2,))
    )
    metrics = context.metrics(second)
    assert result["raw_midpoint_ports_after_publish"] == 0
    assert cast(int, result["reachable_source_ports"]) <= cast(
        int, result["declared_source_ports"]
    )
    assert (
        sum(
            cast(int, result[name])
            for name in (
                "output_only_nodes",
                "admission_only_nodes",
                "shared_output_admission_nodes",
                "retained_unreachable_nodes",
            )
        )
        == metrics["retained_expression_nodes"]
    )
    trace = result["bound_oracle_slice"]
    assert isinstance(trace, dict) and trace["admitted"]
    assert trace["unchosen_consumers"] > 0
    assert trace["licenses_free_branch_pruning"] is False
    assert result["free_action_successor_conflicts"] is None
