"""The shared scheduler compiles a bounded arbitrary state input codec."""

from __future__ import annotations

from itertools import product
from typing import TYPE_CHECKING, Never, cast

import pytest

from devtools.verification.immutable_artifacts import ImmutableArtifactRegistry
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FunctionSignature,
    FunctionSort,
)
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    LowerFinite,
)
from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
    StructuredExpressionTask,
)
from number_compiler.hashlife.interfaces.semantic_structures import StructureArena
from number_compiler.resources.ledger import LedgerSnapshot
from tests.support.assertions import assert_rejected_atomically
from tests.support.c4_summary_artifact import (
    C4FourthInput,
    fresh_c4_fourth_right_summary,
)
from tests.support.diamond_continuation_reduction import literal
from tests.support.runtime_limits import deadline
from tests.support.semantic_state_codec import paired_tiny, tiny

if TYPE_CHECKING:
    import typing

    from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
    from number_compiler.hashlife.execution.continuations.diamond_context_program import (
        ContextObservation,
    )
    from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
        ResolveExpr,
    )
    from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
        HigherEmit,
        HigherInitial,
        HigherObserve,
        HigherStep,
        HigherSummary,
        HigherUnaryObserve,
        HigherUnarySummary,
    )
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        Evaluate,
        Initial,
        Output,
        OutputFunction,
        PairSummary,
        ResetTransfer,
        SpatialSummary,
        Substitute,
        Transfer,
    )
    from number_compiler.hashlife.execution.diamond_continuation_reduction import (
        CompilePrimitiveFunction,
        NormalizePrimitiveLambda,
    )
    from number_compiler.hashlife.interfaces.diamond_boundary import BoundaryStateID
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
    from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
    from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
        CompileStructuredExpression,
        StructuredExpressionTask,
    )
    from number_compiler.hashlife.interfaces.semantic_primitive_tasks import (
        PrimitiveMacroKey,
        PrimitiveMacroObservation,
    )
    from number_compiler.hashlife.interfaces.semantic_structures import StructureID


@pytest.mark.parametrize("side", [0, 1])
def test_unknown_paired_continuation_uses_every_original_component(side: int) -> None:
    runtime, primitive, arena, compiler, paired = paired_tiny()
    parameter = arena.variable(arena.state_sort(paired, side), "arbitrary-function")
    count = (
        runtime.kernel(primitive).right_count
        if side == 0
        else runtime.kernel(primitive).left_count
    )
    compiled = [
        compiler.compile_structured(
            arena.apply(
                arena.continuation(parameter), literal(runtime, primitive, 1 - side, q)
            ),
            (parameter,),
        )
        for q in range(count)
    ]
    assert compiler.codecs is not None
    codec = next(iter(compiler.codecs.records.values()))
    assert codec.continuation_cardinality is not None
    for values in product(range(codec.continuation_cardinality), repeat=count):
        inputs = {port.variable: 0 for port in codec.ports}
        inputs.update(
            (port.variable, value) for port, value in zip(codec.component_ports, values)
        )
        assert compiler.structures is not None
        assert (
            tuple(
                compiler.structures.evaluate_atom(result.structure, inputs)
                for result in compiled
            )
            == values
        )
    assert all(result.ports == codec.ports for result in compiled)


def test_lambda_over_a_paired_state_has_flat_codec_domain_and_exact_decoding() -> None:
    _unused_runtime_binding, _unused_primitive_binding, arena, compiler, paired = (
        paired_tiny()
    )
    variable = arena.variable(arena.state_sort(paired, 1), "input-pair")
    function = arena.lambda_(variable, arena.anchor(variable))
    compiled = compiler.compile_structured(function)
    structures = compiler.structures
    assert structures is not None
    signature = structures.resolve(compiled.structure).signature.output
    assert isinstance(signature, FunctionSort)
    assert tuple(port.cardinality for port in signature.inputs) == (4, 4, 4)
    for code in range(4):
        assert structures is not None
        arguments = {
            port.variable: structures.bits.constant(
                FunctionSignature((), AtomSort("storage", port.cardinality)), code
            )
            for port in signature.inputs
        }
        assert structures is not None
        result = structures.apply(compiled.structure, arguments)
        assert structures is not None
        assert structures.evaluate_atom(result, {}) == (code if code < 3 else 0)


def test_composed_lambda_keeps_independent_outer_dependency() -> None:
    _unused_runtime_binding, primitive, arena, compiler, paired = paired_tiny()
    outer = arena.variable(arena.state_sort(primitive, 1), "outer")
    argument = arena.variable(arena.state_sort(paired, 1), "bound")
    # Return outer: ignored paired inputs are still valid finite codec arguments.
    function = arena.lambda_(argument, outer)
    result = compiler.compile_structured(function, (outer,))
    structures = compiler.structures
    assert structures is not None
    signature = structures.resolve(result.structure).signature.output
    assert isinstance(signature, FunctionSort)
    assert len(signature.inputs) == 3
    assert structures is not None
    arguments = {
        port.variable: structures.bits.constant(
            FunctionSignature((), AtomSort("storage", port.cardinality)), 3
        )
        for port in signature.inputs
    }
    assert structures is not None
    selected = structures.apply(result.structure, arguments)
    for value in range(4):
        assert structures is not None
        assert structures.evaluate_atom(
            selected, {result.ports[0].variable: value}
        ) == (value if value < 3 else None)


def test_unsupported_higher_lambda_domain_rejects_without_registering_codec() -> None:
    runtime, primitive, arena, compiler, paired = paired_tiny()
    higher = runtime.actions.compose(paired, paired)
    variable = arena.variable(arena.state_sort(higher, 0), "unsupported-domain")
    function = arena.lambda_(variable, literal(runtime, primitive, 0, 0))
    assert_rejected_atomically(
        runtime.ledger,
        lambda: compiler.compile_structured(function),
        UnsupportedInterfaceError,
        match="composed function domain",
    )
    assert compiler.codecs is None and compiler.structures is None


def test_actual_c4_fourth_power_right_summary_accepts_its_paired_binder() -> None:
    with deadline(35, "C4 fourth-power RIGHT16 semantic compilation"):
        _check_actual_c4_fourth_power_right_summary()


def _check_actual_c4_fourth_power_right_summary() -> None:
    artifact = fresh_c4_fourth_right_summary()
    runtime = artifact.runtime
    closure = runtime.higher.expressions.closures.resolve(artifact.closure)
    assert closure.support == ()
    result = runtime.semantic_compiler.compile_structured(closure.body)
    structures = runtime.semantic_compiler.structures
    assert structures is not None
    assert structures.resolve(result.structure).kind == "product"
    assert result.ports == ()
    # Compare the first primitive anchor to the independent existing evaluator.
    assert structures is not None
    anchor = structures.component(structures.component(result.structure, 0), 0)
    expected = runtime.execute(
        LowerFinite(
            runtime.higher.expressions.anchor(
                runtime.higher.expressions.anchor(closure.body)
            )
        )
    )
    assert structures is not None
    assert structures.evaluate_atom(anchor, {}) == expected


def test_c4_summary_artifact_rebinds_into_fresh_scoped_arenas() -> None:
    from devtools.verification.immutable_artifacts import REGISTRY

    before = REGISTRY.stats().get("physical-c4-fourth-right-unary-summary")
    first = fresh_c4_fourth_right_summary()
    second = fresh_c4_fourth_right_summary()
    after = REGISTRY.stats()["physical-c4-fourth-right-unary-summary"]
    assert first.runtime is not second.runtime
    assert first.closure.owner is not second.closure.owner
    assert first.runtime.ledger.counters["proof_artifact_loading_work"] > 0
    assert second.runtime.ledger.counters["proof_artifact_loading_work"] > 0
    assert after.hits >= (0 if before is None else before.hits) + 1


def test_proof_registry_rejects_scoped_handles_and_records_uncached_reason() -> None:
    from dataclasses import dataclass

    from devtools.verification.immutable_artifacts import (
        ArtifactKey,
        ImmutableArtifactRegistry,
        UncachedBuild,
    )
    from number_compiler.arithmetic.contracts.scoped_handles import (
        ActionProgramID,
        ArenaToken,
    )

    registry = ImmutableArtifactRegistry()
    key = ArtifactKey("test-summary", "recipe-digest")
    with pytest.raises(TypeError, match="owner-free"):
        registry.obtain(key, lambda: ActionProgramID(ArenaToken("live"), "action", 0))
    assert registry.stats()["test-summary"].failed_builds == 1
    request = UncachedBuild("test node", "exercise cold construction")
    assert registry.obtain(key, lambda: ("frozen", 1), uncached=request) == (
        ("frozen", 1),
        False,
    )
    assert registry.obtain(key, lambda: ("frozen", 2), uncached=request) == (
        ("frozen", 2),
        False,
    )
    stats = registry.stats()["test-summary"]
    assert stats.uncached_builds == 2 and stats.hits == 0 and stats.retained_bytes == 0
    assert stats.uncached_requests == (request, request)
    none_key = ArtifactKey("nullable-summary", "other-recipe")
    assert registry.obtain(none_key, lambda: None) == (None, False)
    assert registry.obtain(none_key, lambda: pytest.fail("cached None rebuilt")) == (
        None,
        True,
    )
    failed_key = ArtifactKey("failed-summary", "failed-recipe")
    with pytest.raises(RuntimeError, match="proof failed"):
        registry.obtain(
            failed_key, lambda: (_ for _ in ()).throw(RuntimeError("proof failed"))
        )
    assert registry.stats()["failed-summary"].failed_builds == 1
    with pytest.raises(ValueError):
        ArtifactKey(cast(str, True), "aliased-kind")

    @dataclass(frozen=True, init=False)
    class HiddenSlot:
        __slots__ = ("hidden", "value")
        value: int

        def __init__(self) -> None:
            object.__setattr__(self, "value", 1)
            object.__setattr__(self, "hidden", [])

    with pytest.raises(TypeError, match="owner-free"):
        registry.obtain(ArtifactKey("hidden-slot", "hidden-recipe"), HiddenSlot)


def test_c4_artifact_budget_preflight_leaves_fresh_runtime_unchanged() -> None:
    from devtools.verification.c4_summary_artifact import c4_fourth_right_summary
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from tests.support.c4_summary_artifact import fresh_c4_fourth_input

    # Ensure the shared object exists before imposing the fresh runtime budget.
    fresh_c4_fourth_right_summary()
    value = fresh_c4_fourth_input()
    ledger = value.runtime.ledger
    ledger.max_nodes, ledger.max_cache_entries = ledger.nodes, ledger.entries
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        c4_fourth_right_summary(value.runtime, value.fourth, value.cell)
    after = ledger.snapshot()
    assert (after.entries, after.nodes, after.inventory) == (
        before.entries,
        before.nodes,
        before.inventory,
    )
    assert after.counters["proof_artifact_loading_failures"] == 1


def _refused_summary(
    value: C4FourthInput, registry: ImmutableArtifactRegistry
) -> tuple[LedgerSnapshot, LedgerSnapshot]:
    from devtools.verification.c4_summary_artifact import c4_fourth_right_summary
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    ledger = value.runtime.ledger
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        c4_fourth_right_summary(
            value.runtime, value.fourth, value.cell, registry=registry
        )
    return before, ledger.snapshot()


def test_cold_c4_artifact_rejects_exhausted_target_before_shared_build() -> None:
    from devtools.verification.immutable_artifacts import ImmutableArtifactRegistry
    from tests.support.c4_summary_artifact import fresh_c4_fourth_input

    registry = ImmutableArtifactRegistry()
    value = fresh_c4_fourth_input()
    ledger = value.runtime.ledger
    ledger.max_nodes, ledger.max_cache_entries = ledger.nodes, ledger.entries
    before, after = _refused_summary(value, registry)
    assert registry.stats() == {}
    assert (after.entries, after.nodes, after.inventory) == (
        before.entries,
        before.nodes,
        before.inventory,
    )
    assert after.counters["proof_artifact_loading_failures"] == 1


def test_c4_artifact_capacity_bound_rejects_intermediate_budgets_atomically() -> None:
    from devtools.verification.c4_summary_artifact import c4_fourth_right_summary
    from devtools.verification.immutable_artifacts import ImmutableArtifactRegistry
    from tests.support.c4_summary_artifact import fresh_c4_fourth_input

    registry = ImmutableArtifactRegistry()
    warm = fresh_c4_fourth_input()
    c4_fourth_right_summary(warm.runtime, warm.fourth, warm.cell, registry=registry)
    for allowance in (2, 100, 1_000):
        value = fresh_c4_fourth_input()
        ledger = value.runtime.ledger
        ledger.max_nodes = ledger.nodes + allowance
        ledger.max_cache_entries = ledger.entries + allowance
        before, after = _refused_summary(value, registry)
        assert (after.entries, after.nodes, after.inventory) == (
            before.entries,
            before.nodes,
            before.inventory,
        )


def test_malformed_artifact_parameters_reject_before_target_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from dataclasses import replace

    import devtools.verification.c4_summary_artifact as module
    from devtools.verification.immutable_artifacts import ImmutableArtifactRegistry
    from tests.support.c4_summary_artifact import fresh_c4_fourth_input

    value = fresh_c4_fourth_input()
    runtime = value.runtime
    digest = module._recipe(runtime, value.fourth, value.cell, 1)
    artifact = module._build_isolated(digest)
    parameter = artifact.root_parameters[0]
    expressions = list(artifact.expressions)
    expressions[parameter] = replace(expressions[parameter], kind="literal")
    malformed = (
        replace(artifact, root_parameters=()),
        replace(artifact, root_parameters=(parameter, parameter)),
        replace(artifact, expressions=tuple(expressions)),
    )

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("malformed proof reached target binding")

    monkeypatch.setattr(module, "_bind", forbidden)
    registry = ImmutableArtifactRegistry()
    for altered in malformed:
        monkeypatch.setattr(
            registry,
            "obtain",
            lambda *_args, altered=altered, **_kw: (altered, True),
        )
        before = runtime.ledger.snapshot()
        with pytest.raises(ValueError, match="parameter"):
            module.c4_fourth_right_summary(
                runtime, value.fourth, value.cell, registry=registry
            )
        after = runtime.ledger.snapshot()
        assert (after.entries, after.nodes, after.inventory) == (
            before.entries,
            before.nodes,
            before.inventory,
        )


def test_codec_environment_rejects_foreign_or_wrong_sort_before_work() -> None:
    from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
        StructuredExpressionTask,
    )

    runtime, _unused_primitive_binding, arena, compiler, paired = paired_tiny()
    variable = arena.variable(arena.state_sort(paired, 0), "local")
    compiler.compile_structured(variable, (variable,))
    assert compiler.codecs is not None
    local = next(iter(compiler.codecs.records.values()))
    other, other_primitive = tiny()
    other_pair = other.actions.compose(other_primitive, other_primitive)
    other_var = other.higher.expressions.variable(
        other.higher.expressions.state_sort(other_pair, 0), "foreign"
    )
    other.semantic_compiler.compile_structured(other_var, (other_var,))
    assert other.semantic_compiler.codecs is not None
    foreign = next(iter(other.semantic_compiler.codecs.records.values()))
    wrong_side = arena.variable(arena.state_sort(paired, 1), "wrong-side")
    before = runtime.ledger.snapshot()
    for task in (
        StructuredExpressionTask(variable, ((variable, foreign),)),
        StructuredExpressionTask(wrong_side, ((wrong_side, local),)),
    ):
        with pytest.raises(ValueError):
            compiler.probe_task(task)
    assert runtime.ledger.snapshot() == before


def test_equal_decoded_state_and_rebuilt_identity_continuation_share_complete_id() -> (
    None
):
    _unused_runtime_binding, primitive, arena, compiler, paired = paired_tiny()
    x = arena.variable(arena.state_sort(paired, 0), "arbitrary-state")
    q = arena.variable(arena.state_sort(primitive, 1), "opposite")
    applied = arena.apply(arena.continuation(x), q)
    # This fixed kernel's left transition is the identity for every symbol.
    same_value = arena.primitive_advance(
        primitive, 0, applied, arena.symbol(primitive, 0)
    )
    reconstructed = arena.pair(paired, 0, arena.anchor(x), arena.lambda_(q, same_value))
    assert reconstructed != x
    direct = compiler.compile_structured(x, (x,))
    rebuilt = compiler.compile_structured(reconstructed, (x,))
    assert direct.structure == rebuilt.structure


def test_projecting_opaque_pair_does_not_compile_its_unused_continuation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import FunctionSort

    runtime, primitive, arena, compiler, paired = paired_tiny()
    x = arena.variable(arena.state_sort(primitive, 0), "anchor-input")
    q = arena.variable(arena.state_sort(primitive, 1), "opposite-input")
    continuation = arena.lambda_(
        q, arena.primitive_advance(primitive, 0, x, arena.symbol(primitive, 1))
    )
    body = arena.pair(paired, 0, x, continuation)
    call = arena.call(arena.closures.intern((x,), body), (x,))
    projected = arena.anchor(call)
    assert arena.node(projected).kind == "anchor"
    original = compiler._structured_program

    def guarded(
        task: StructuredExpressionTask, structures: StructureArena
    ) -> typing.Generator[
        Initial
        | Transfer
        | ResetTransfer
        | Substitute
        | Evaluate
        | Output
        | OutputFunction
        | PairSummary
        | SpatialSummary
        | ContextObservation
        | HigherInitial
        | HigherStep
        | HigherEmit
        | HigherSummary
        | HigherUnarySummary
        | HigherObserve
        | HigherUnaryObserve
        | LowerFinite
        | ResolveExpr
        | CompilePrimitiveFunction
        | NormalizePrimitiveLambda
        | CompileStructuredExpression
        | StructuredExpressionTask
        | PrimitiveMacroKey
        | PrimitiveMacroObservation,
        BoundaryStateID
        | TransferSummaryID
        | ExprID
        | StructureID
        | LocalInterfaceID
        | int,
        BoundaryStateID
        | TransferSummaryID
        | ExprID
        | StructureID
        | LocalInterfaceID
        | int,
    ]:
        assert not isinstance(arena.node(task.expression).sort, FunctionSort), (
            "compiled discarded continuation"
        )
        return original(task, structures)

    monkeypatch.setattr(compiler, "_structured_program", guarded)
    result = compiler.compile_structured(projected, (x,))
    for value in range(2):
        assert compiler.structures is not None
        assert (
            compiler.structures.evaluate_atom(
                result.structure, {result.ports[0].variable: value}
            )
            == value
        )
    assert runtime.ledger.counters["semantic_expression_head_elisions"] >= 1


def test_constant_opaque_function_discards_argument_before_semantic_compilation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, primitive = tiny()
    arena, compiler = runtime.higher.expressions, runtime.semantic_compiler
    x = arena.variable(arena.state_sort(primitive, 0), "retained-outer")
    q = arena.variable(arena.state_sort(primitive, 1), "discarded-argument")
    function = arena.lambda_(q, x)
    opaque = arena.call(arena.closures.intern((x,), function), (x,))
    argument = arena.primitive_advance(primitive, 1, q, arena.symbol(primitive, 1))
    applied = arena.apply(opaque, argument)
    assert arena.node(applied).kind == "apply"
    original = compiler._structured_program

    def guarded(
        task: StructuredExpressionTask, structures: StructureArena
    ) -> typing.Generator[
        Initial
        | Transfer
        | ResetTransfer
        | Substitute
        | Evaluate
        | Output
        | OutputFunction
        | PairSummary
        | SpatialSummary
        | ContextObservation
        | HigherInitial
        | HigherStep
        | HigherEmit
        | HigherSummary
        | HigherUnarySummary
        | HigherObserve
        | HigherUnaryObserve
        | LowerFinite
        | ResolveExpr
        | CompilePrimitiveFunction
        | NormalizePrimitiveLambda
        | CompileStructuredExpression
        | StructuredExpressionTask
        | PrimitiveMacroKey
        | PrimitiveMacroObservation,
        BoundaryStateID
        | TransferSummaryID
        | ExprID
        | StructureID
        | LocalInterfaceID
        | int,
        BoundaryStateID
        | TransferSummaryID
        | ExprID
        | StructureID
        | LocalInterfaceID
        | int,
    ]:
        assert arena.node(task.expression).sort != arena.node(q).sort, (
            "compiled discarded primitive argument"
        )
        return original(task, structures)

    monkeypatch.setattr(compiler, "_structured_program", guarded)
    result = compiler.compile_structured(applied, (x, q))
    for left in range(2):
        for right in range(4):
            assert compiler.structures is not None
            assert compiler.structures.evaluate_atom(
                result.structure,
                {result.ports[0].variable: left, result.ports[1].variable: right},
            ) == (left if right < 3 else None)
