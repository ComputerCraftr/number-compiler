"""Profile encodings preserve binder scope before admission or cache work."""

from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
    StructuredExpressionTask,
)
from number_compiler.hashlife.interfaces.semantic_structures import StructureArena
from number_compiler.sequences.collatz.physical_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from tests.support.assertions import assert_rejected_atomically
from tests.support.collatz_diamond_fixtures import build_collatz_diamond_application


def test_reachable_codec_namespace_cannot_capture_next_binder() -> None:
    app = build_collatz_diamond_application(
        PhysicalCollatzFourBlockEffect(), (0, 1), 16, 1
    )
    runtime, primitive = app.runtime, app.root
    pair = runtime.actions.compose(primitive, primitive)
    compiler = runtime.semantic_compiler
    profile = compiler.source_initial_profile(pair)
    compiler.structures = StructureArena(
        BitFunctionArena(runtime.ledger, runtime.semantic_functions)
    )
    expression = compiler.expressions.variable(
        compiler.expressions.state_sort(pair, 0), "free"
    )
    binding = compiler._binding(
        expression, PortVariable(0, 0, "semantic-lambda-00000000", 0), profile
    )
    task = StructuredExpressionTask(
        expression, ((expression, binding),), profile=profile
    )
    assert_rejected_atomically(
        runtime.ledger, lambda: compiler.probe_task(task), ValueError, match="capture"
    )
    assert not compiler.admissions


def test_profile_choice_is_explicit_and_foreign_rejects_before_warm_admission() -> None:
    app = build_collatz_diamond_application(
        PhysicalCollatzFourBlockEffect(), (0, 1), 16, 1
    )
    runtime, primitive = app.runtime, app.root
    compiler = runtime.semantic_compiler
    pair = runtime.actions.compose(primitive, primitive)
    profile = compiler.source_initial_profile(pair)
    variable = compiler.expressions.variable(
        compiler.expressions.state_sort(primitive, 0), "free"
    )
    compiler._admit(variable, (variable,), structured=True, profile=profile)
    compiler._admit(variable, (variable,), structured=True)
    assert {key.profile for key in compiler.admissions} == {None, profile}
    other = build_collatz_diamond_application(
        PhysicalCollatzFourBlockEffect(), (0, 1), 16, 1
    )
    foreign = other.runtime.semantic_compiler.source_initial_profile(
        other.runtime.actions.compose(other.root, other.root)
    )
    assert_rejected_atomically(
        runtime.ledger,
        lambda: compiler._admit(
            variable, (variable,), structured=True, profile=foreign
        ),
        ValueError,
    )
