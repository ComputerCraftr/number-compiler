"""Portable C4 fourth-power unary summary used by proof/compiler tests.

The artifact contains topologically encoded expression and Boolean DAGs.  It
contains no arena tokens or handles and is rebound into every fresh runtime.
Semantic compilation itself is intentionally outside this cache.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from hashlib import sha256
from typing import TYPE_CHECKING, TypeAlias, cast

from devtools.verification.immutable_artifacts import (
    REGISTRY,
    ArtifactKey,
    ImmutableArtifactRegistry,
    UncachedBuild,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import (
    ExactSource,
    TransferSummaryID,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_expression_closures import (
    ClosureProgramID,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HigherUnarySummary,
)
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExprNode,
    ExpressionKind,
    ExpressionSort,
    ExprID,
    FunctionSort,
    StateSort,
    SymbolSort,
)
from number_compiler.hashlife.interfaces.diamond_kernel import FiniteExpression
from number_compiler.hashlife.interfaces.expression_transactions import (
    ExpressionTransaction,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.physical_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from number_compiler.sequences.collatz.physical_pair_certificate import (
    kernel_digest,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.actions.diamond_actions import CellID


_KIND = "physical-c4-fourth-right-unary-summary"
_RECIPE_SCHEMA = "c4-fourth-right-summary-recipe-v1"
PortableSort: TypeAlias = tuple[object, ...]


@dataclass(frozen=True, slots=True)
class PortableDecision:
    variable: PortVariable | None
    low: int
    high: int


@dataclass(frozen=True, slots=True)
class PortableFiniteExpression:
    domain: int
    bits: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class PortableExpression:
    kind: str
    sort: PortableSort
    children: tuple[int, ...]
    role: str
    bound: int
    value: int
    action_exponent: int
    side: int
    function: int
    closure: int
    binding_safe: bool


@dataclass(frozen=True, slots=True)
class PortableClosure:
    parameters: tuple[int, ...]
    body: int
    support: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class C4UnarySummaryArtifact:
    recipe_digest: str
    decisions: tuple[PortableDecision, ...]
    finite_expressions: tuple[PortableFiniteExpression, ...]
    expressions: tuple[PortableExpression, ...]
    closures: tuple[PortableClosure, ...]
    root_parameters: tuple[int, ...]
    root_body: int
    root_support: tuple[int, ...]


_KINDS = frozenset(
    (
        "port",
        "bound",
        "literal",
        "symbol",
        "pair",
        "anchor",
        "continuation",
        "lambda",
        "apply",
        "advance",
        "emit",
        "finite_apply",
        "finite_map",
        "call",
    )
)


def _valid_sort(value: object) -> bool:
    if type(value) is not tuple:
        return False
    parts = cast(tuple[object, ...], value)
    if not parts or type(parts[0]) is not str:
        return False
    if parts[0] == "state":
        return (
            len(parts) == 3
            and type(parts[1]) is int
            and 0 <= parts[1] <= 4
            and type(parts[2]) is int
            and parts[2] in (0, 1)
        )
    if parts[0] == "symbol":
        return (
            len(parts) == 3
            and type(parts[1]) is int
            and parts[1] == 2
            and type(parts[2]) is int
            and parts[2] == 2
        )
    if parts[0] == "function":
        return (
            len(parts) == 3
            and type(parts[1]) is tuple
            and type(parts[2]) is tuple
            and _valid_state_sort(cast(tuple[object, ...], parts[1]))
            and _valid_state_sort(cast(tuple[object, ...], parts[2]))
        )
    return False


def _valid_state_sort(value: tuple[object, ...]) -> bool:
    return (
        len(value) == 3
        and value[0] == "state"
        and type(value[1]) is int
        and 0 <= value[1] <= 4
        and type(value[2]) is int
        and value[2] in (0, 1)
    )


def _valid_port_variable(value: object) -> bool:
    return (
        type(value) is PortVariable
        and type(value.time) is int
        and value.time >= 0
        and type(value.side) is int
        and value.side >= 0
        and type(value.role) is str
        and bool(value.role)
        and type(value.bit) is int
        and value.bit >= 0
    )


def _validate_artifact(artifact: object, digest: str) -> C4UnarySummaryArtifact:
    if type(artifact) is not C4UnarySummaryArtifact or artifact.recipe_digest != digest:
        raise ValueError("C4 summary artifact recipe digest mismatch")
    if (
        type(artifact.decisions) is not tuple
        or len(artifact.decisions) < 2
        or type(artifact.finite_expressions) is not tuple
        or type(artifact.expressions) is not tuple
        or not artifact.expressions
        or type(artifact.closures) is not tuple
    ):
        raise ValueError("C4 summary artifact has malformed tables")
    for index, decision in enumerate(artifact.decisions):
        if (
            type(decision) is not PortableDecision
            or type(decision.low) is not int
            or type(decision.high) is not int
        ):
            raise ValueError("C4 summary artifact has malformed decisions")
        terminal = index < 2
        if (
            (decision.variable is None) != terminal
            or not terminal
            and not _valid_port_variable(decision.variable)
            or decision.low < 0
            or decision.high < 0
            or not terminal
            and (decision.low >= index or decision.high >= index)
        ):
            raise ValueError("C4 summary artifact decision graph is not topological")
    for finite in artifact.finite_expressions:
        if (
            type(finite) is not PortableFiniteExpression
            or type(finite.domain) is not int
            or not 1 <= finite.domain <= 1 << 64
            or type(finite.bits) is not tuple
            or any(
                type(bit) is not int or not 0 <= bit < len(artifact.decisions)
                for bit in finite.bits
            )
            or len(finite.bits) != (finite.domain - 1).bit_length()
        ):
            raise ValueError("C4 summary artifact has a malformed finite expression")
    for index, expression in enumerate(artifact.expressions):
        if (
            type(expression) is not PortableExpression
            or expression.kind not in _KINDS
            or not _valid_sort(expression.sort)
            or type(expression.children) is not tuple
            or any(
                type(child) is not int or not 0 <= child < index
                for child in expression.children
            )
            or type(expression.role) is not str
            or type(expression.bound) is not int
            or type(expression.value) is not int
            or type(expression.action_exponent) is not int
            or not -1 <= expression.action_exponent <= 4
            or type(expression.side) is not int
            or type(expression.function) is not int
            or not -1 <= expression.function < len(artifact.finite_expressions)
            or type(expression.closure) is not int
            or not -1 <= expression.closure < len(artifact.closures)
            or type(expression.binding_safe) is not bool
        ):
            raise ValueError("C4 summary artifact has a malformed expression")
    for closure in artifact.closures:
        if type(closure) is not PortableClosure:
            raise ValueError("C4 summary artifact has a malformed closure")
        if (
            type(closure.parameters) is not tuple
            or type(closure.body) is not int
            or type(closure.support) is not tuple
        ):
            raise ValueError("C4 summary artifact closure references are invalid")
        all_refs = closure.parameters + (closure.body,) + closure.support
        if any(
            type(item) is not int or not 0 <= item < len(artifact.expressions)
            for item in all_refs
        ) or any(item not in closure.parameters for item in closure.support):
            raise ValueError("C4 summary artifact closure references are invalid")
    if (
        type(artifact.root_parameters) is not tuple
        or type(artifact.root_body) is not int
        or type(artifact.root_support) is not tuple
    ):
        raise ValueError("C4 summary artifact root references are invalid")
    root_refs = artifact.root_parameters + (artifact.root_body,) + artifact.root_support
    if any(
        type(item) is not int or not 0 <= item < len(artifact.expressions)
        for item in root_refs
    ) or any(item not in artifact.root_parameters for item in artifact.root_support):
        raise ValueError("C4 summary artifact root references are invalid")
    # Parameter reconstruction uses (state sort, role) canonical identity.
    # Reject invalid or aliased parameters before any target arena publication.
    parameter_sets = (
        artifact.root_parameters,
        *(item.parameters for item in artifact.closures),
    )
    for parameters in parameter_sets:
        if not 1 <= len(parameters) <= 3 or len(set(parameters)) != len(parameters):
            raise ValueError("C4 summary artifact requires distinct state parameters")
        identities: set[tuple[PortableSort, str]] = set()
        for parameter in parameters:
            node = artifact.expressions[parameter]
            if node.kind != "port" or not _valid_state_sort(node.sort) or not node.role:
                raise ValueError(
                    "C4 summary artifact parameters must be named state ports"
                )
            identities.add((node.sort, node.role))
        if len(identities) != len(parameters):
            raise ValueError("C4 summary artifact parameters have aliased identities")
    # Every call in closure i may reference only an already bound closure.
    for closure_index, closure in enumerate(artifact.closures):
        pending = [closure.body]
        seen: set[int] = set()
        while pending:
            expression_index = pending.pop()
            if expression_index in seen:
                continue
            seen.add(expression_index)
            expression = artifact.expressions[expression_index]
            if expression.closure >= closure_index:
                raise ValueError("C4 summary artifact closure graph is not topological")
            pending.extend(expression.children)
    return artifact


def _preflight_bind(runtime: DiamondRuntime, artifact: C4UnarySummaryArtifact) -> None:
    # Conservative upper bound: each closure can rebuild the complete portable
    # expression DAG. Canonical hits make actual retention strictly smaller.
    nodes, entries = _bind_capacity(artifact)
    ledger = runtime.ledger
    if (
        ledger.max_nodes is not None
        and ledger.nodes + nodes > ledger.max_nodes
        or ledger.max_cache_entries is not None
        and ledger.entries + entries > ledger.max_cache_entries
    ):
        raise BlockContextBudgetExceeded(
            "proof artifact binding exceeds the fresh arena budget"
        )


def _bind_capacity(artifact: C4UnarySummaryArtifact) -> tuple[int, int]:
    """Upper bound every canonical publication performed by one fresh bind.

    Each decision, finite expression, action, expression, port, and closure can
    publish at most one node plus one interner entry. Each closure import can
    visit the complete expression table; this deliberately overcounts shared
    subgraphs. Binding performs no query-memo publication.
    """
    expression_objects = len(artifact.expressions) * (len(artifact.closures) + 1)
    parameter_objects = sum(len(item.parameters) for item in artifact.closures) + len(
        artifact.root_parameters
    )
    objects = (
        max(0, len(artifact.decisions) - 2)
        + len(artifact.finite_expressions)
        + expression_objects
        + parameter_objects
        + len(artifact.closures)
        + 4
    )
    return objects, 2 * objects


def _action_exponent(runtime: DiamondRuntime, action: ActionProgramID) -> int:
    node = runtime.actions.resolve(action)
    if node.kind == "identity":
        return 0
    if node.base != 2 or node.blank != 2 or node.exponent < 4 or node.exponent % 4:
        raise ValueError("C4 artifact contains an incompatible temporal action")
    return node.exponent // 4


def _sort(runtime: DiamondRuntime, value: object) -> PortableSort:
    if type(value) is StateSort:
        return ("state", _action_exponent(runtime, value.action), value.side)
    if type(value) is FunctionSort:
        return (
            "function",
            (
                "state",
                _action_exponent(runtime, value.domain.action),
                value.domain.side,
            ),
            (
                "state",
                _action_exponent(runtime, value.codomain.action),
                value.codomain.side,
            ),
        )
    if type(value) is SymbolSort:
        return ("symbol", value.base, value.blank)
    raise TypeError("C4 summary contains an unknown expression sort")


def c4_artifact_recipe(
    runtime: DiamondRuntime, action: ActionProgramID, cell: CellID, side: int
) -> str:
    temporal = runtime.actions.resolve(action)
    primitive, repetitions, action_digest = _action_recipe(runtime, action)
    source = runtime.cells.source_geometry.construction.source
    node = runtime.cells.require_original(cell)
    if (
        temporal.exponent != 16
        or repetitions != 4
        or side != 1
        or node.level != 4
        or node.source_start != 0
        or source.extent != 16
        or source.digits != (0, 1) * 8
        or source.base != 2
        or source.blank != 2
        or source.alphabet_size != 2
    ):
        raise ValueError("C4 summary artifact requires the certified RIGHT16 recipe")
    payload = {
        "schema": _RECIPE_SCHEMA,
        "kernel": _kernel_digest(runtime, primitive),
        "action": action_digest,
        "source": list(source.digits),
        "source_type": f"{type(source).__module__}.{type(source).__qualname__}",
        "source_base": source.base,
        "source_blank": source.blank,
        "source_alphabet_size": source.alphabet_size,
        "source_orbit": source.orbit,
        "extent": source.extent,
        "action_exponent": temporal.exponent,
        "cell_start": node.source_start,
        "cell_level": node.level,
        "cell_encoding": "original-source-dyadic-cell-v1",
        "side": side,
    }
    return sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def _kernel_digest(runtime: DiamondRuntime, primitive: ActionProgramID) -> str:
    effect = runtime.actions.primitive(primitive)
    if type(effect) is not PhysicalCollatzFourBlockEffect:
        raise ValueError("C4 summary artifact has another primitive kernel")
    return kernel_digest(effect)


def _action_recipe(
    runtime: DiamondRuntime, action: ActionProgramID
) -> tuple[ActionProgramID, int, str]:
    """Validate every temporal leaf and hash the normalized C4 action DAG."""
    pending = [action]
    leaves: list[ActionProgramID] = []
    records: list[tuple[str, int, int, int]] = []
    while pending:
        current = pending.pop()
        node = runtime.actions.resolve(current)
        if node.kind == "atom":
            if node.base != 2 or node.blank != 2 or node.exponent != 4:
                raise ValueError("C4 artifact action contains another primitive")
            effect = runtime.actions.primitive(current)
            if type(effect) is not PhysicalCollatzFourBlockEffect:
                raise ValueError("C4 artifact action contains another kernel family")
            digest = kernel_digest(effect)
            leaves.append(current)
            records.append((digest, 1, 0, 0))
            continue
        if node.kind != "compose":
            raise ValueError("C4 artifact action contains identity or unknown syntax")
        left = runtime.actions.reference(node.left)
        right = runtime.actions.reference(node.right)
        records.append(("compose", node.exponent, 0, 0))
        pending.extend((right, left))
    if not leaves or any(
        kernel_digest(
            cast(PhysicalCollatzFourBlockEffect, runtime.actions.primitive(leaf))
        )
        != kernel_digest(
            cast(PhysicalCollatzFourBlockEffect, runtime.actions.primitive(leaves[0]))
        )
        for leaf in leaves
    ):
        raise ValueError("C4 artifact action mixes primitive kernels")
    # The digest records the admitted DAG shape as well as all verified leaves.
    digest = sha256(repr(tuple(records)).encode()).hexdigest()
    return leaves[0], len(leaves), digest


def _freeze(
    runtime: DiamondRuntime,
    action: ActionProgramID,
    cell: CellID,
    side: int,
    recipe_digest: str,
) -> C4UnarySummaryArtifact:
    summary = runtime.execute(HigherUnarySummary(action, cell, side))
    if type(summary) is not TransferSummaryID:
        raise AssertionError("C4 unary summary returned another result sort")
    record = runtime.higher.unary(summary)
    root = runtime.higher.expressions.closures.resolve(record.body)
    arena = runtime.higher.expressions

    expression_ids: set[int] = set()
    closure_ids: set[int] = set()
    pending = [
        root.body.local_id,
        *(value.local_id for value in root.parameters + root.support),
    ]
    while pending:
        index = pending.pop()
        if index in expression_ids:
            continue
        expression_ids.add(index)
        node = arena.nodes[index]
        pending.extend(node.children)
        if node.closure is not None and node.closure.local_id not in closure_ids:
            closure_ids.add(node.closure.local_id)
            closure = arena.closures.nodes[node.closure.local_id]
            pending.extend(
                value.local_id
                for value in closure.parameters + (closure.body,) + closure.support
            )

    ordered_expressions = tuple(sorted(expression_ids))
    expression_map = {old: new for new, old in enumerate(ordered_expressions)}
    ordered_closures = tuple(sorted(closure_ids))
    closure_map = {old: new for new, old in enumerate(ordered_closures)}

    finite_handle_set: set[int] = set()
    for index in expression_ids:
        function = arena.nodes[index].function
        if function is not None:
            finite_handle_set.add(function.local_id)
    finite_handles = sorted(finite_handle_set)
    finite_map = {old: new for new, old in enumerate(finite_handles)}
    functions = runtime.kernels.functions
    decision_ids = {0, 1}
    finite_storage = runtime.kernels.audit_snapshot()
    finite_expressions = finite_storage.expressions
    functions = runtime.kernels.functions
    function_nodes = functions.audit_snapshot().nodes
    decision_pending = [
        bit.local_id for old in finite_handles for bit in finite_expressions[old].bits
    ]
    while decision_pending:
        index = decision_pending.pop()
        if index in decision_ids:
            continue
        decision_ids.add(index)
        decision = function_nodes[index]
        decision_pending.extend((decision.low, decision.high))
    ordered_decisions = (0, 1, *sorted(decision_ids - {0, 1}))
    decision_map = {old: new for new, old in enumerate(ordered_decisions)}

    decisions = tuple(
        PortableDecision(
            function_nodes[old].variable,
            decision_map[function_nodes[old].low],
            decision_map[function_nodes[old].high],
        )
        for old in ordered_decisions
    )
    finite = tuple(
        PortableFiniteExpression(
            finite_expressions[old].domain,
            tuple(decision_map[bit.local_id] for bit in finite_expressions[old].bits),
        )
        for old in finite_handles
    )
    expressions: list[PortableExpression] = []
    for old in ordered_expressions:
        node = arena.nodes[old]
        expressions.append(
            PortableExpression(
                node.kind,
                _sort(runtime, node.sort),
                tuple(expression_map[child] for child in node.children),
                node.role,
                node.bound,
                node.value,
                -1 if node.action is None else _action_exponent(runtime, node.action),
                node.side,
                -1 if node.function is None else finite_map[node.function.local_id],
                -1 if node.closure is None else closure_map[node.closure.local_id],
                node.binding_safe,
            )
        )
    closures = tuple(
        PortableClosure(
            tuple(expression_map[value.local_id] for value in closure.parameters),
            expression_map[closure.body.local_id],
            tuple(expression_map[value.local_id] for value in closure.support),
        )
        for old in ordered_closures
        for closure in (arena.closures.nodes[old],)
    )
    return C4UnarySummaryArtifact(
        recipe_digest,
        decisions,
        finite,
        tuple(expressions),
        closures,
        tuple(expression_map[value.local_id] for value in root.parameters),
        expression_map[root.body.local_id],
        tuple(expression_map[value.local_id] for value in root.support),
    )


def _restored_action(
    runtime: DiamondRuntime,
    primitive: ActionProgramID,
    exponent: int,
    actions: dict[int, ActionProgramID],
) -> ActionProgramID:
    runtime.ledger.bump("proof_artifact_loading_work")
    runtime.ledger.bump("proof_artifact_action_reference_loads")
    action = actions.get(exponent)
    if action is None:
        action = runtime.actions.power(primitive, exponent)
        actions[exponent] = action
    else:
        runtime.ledger.bump("proof_artifact_action_reference_hits")
    return action


def _restore_state(
    runtime: DiamondRuntime,
    primitive: ActionProgramID,
    value: object,
    actions: dict[int, ActionProgramID],
) -> StateSort:
    if type(value) is not tuple:
        raise ValueError("portable function sort has invalid state metadata")
    parts = cast(tuple[object, ...], value)
    if len(parts) != 3 or parts[0] != "state":
        raise ValueError("portable function sort has invalid state metadata")
    exponent, side = parts[1], parts[2]
    if type(exponent) is not int or type(side) is not int:
        raise ValueError("portable state sort has invalid metadata")
    return StateSort(_restored_action(runtime, primitive, exponent, actions), side)


def _restore_sort(
    runtime: DiamondRuntime,
    primitive: ActionProgramID,
    value: PortableSort,
    actions: dict[int, ActionProgramID],
    sorts: dict[PortableSort, ExpressionSort],
) -> ExpressionSort:
    runtime.ledger.bump("proof_artifact_loading_work")
    runtime.ledger.bump("proof_artifact_sort_loads")
    found = sorts.get(value)
    if found is not None:
        runtime.ledger.bump("proof_artifact_sort_hits")
        return found
    tag = value[0]
    if tag == "state":
        result: ExpressionSort = _restore_state(runtime, primitive, value, actions)
        sorts[value] = result
        return result
    if tag == "function":
        domain_value, codomain_value = value[1], value[2]
        if type(domain_value) is not tuple or type(codomain_value) is not tuple:
            raise ValueError("portable function sort has invalid metadata")
        domain = _restore_state(
            runtime, primitive, cast(tuple[object, ...], domain_value), actions
        )
        codomain = _restore_state(
            runtime, primitive, cast(tuple[object, ...], codomain_value), actions
        )
        result = FunctionSort(domain, codomain)
        sorts[value] = result
        return result
    if tag == "symbol":
        base, blank = value[1], value[2]
        if type(base) is not int or type(blank) is not int:
            raise ValueError("portable symbol sort has invalid metadata")
        result = SymbolSort(base, blank)
        sorts[value] = result
        return result
    raise ValueError("portable expression has an unknown sort")


def _bind(
    runtime: DiamondRuntime, action: ActionProgramID, artifact: C4UnarySummaryArtifact
) -> ClosureProgramID:
    primitive, repetitions, _ = _action_recipe(runtime, action)
    if repetitions != 4:
        raise ValueError("C4 summary binding requires four primitive actions")
    functions = runtime.kernels.functions
    action_cache = {0: runtime.actions.identity, 1: primitive}
    sort_cache: dict[PortableSort, ExpressionSort] = {}
    decision_ids = [0, 1]
    for index, decision in enumerate(artifact.decisions[2:], 2):
        if decision.variable is None:
            raise ValueError("nonterminal portable decision has no variable")
        runtime.ledger.bump("proof_artifact_loading_work")
        runtime.ledger.bump("proof_artifact_decision_loads")
        actual = functions.intern_record(
            decision.variable, decision_ids[decision.low], decision_ids[decision.high]
        )
        decision_ids.append(actual)
        if len(decision_ids) != index + 1:
            raise AssertionError("portable decision order was not topological")
    finite_results: list[TransferSummaryID] = []
    for finite in artifact.finite_expressions:
        runtime.ledger.bump("proof_artifact_loading_work")
        runtime.ledger.bump("proof_artifact_finite_expression_loads")
        finite_results.append(
            runtime.kernels.intern_expression(
                FiniteExpression(
                    finite.domain,
                    tuple(
                        functions.scoped_handle(decision_ids[bit])
                        for bit in finite.bits
                    ),
                )
            )
        )
    finite_ids = tuple(finite_results)

    arena = runtime.higher.expressions
    closures: dict[int, ClosureProgramID] = {}

    def port(index: int) -> ExprID:
        portable = artifact.expressions[index]
        if portable.kind != "port":
            raise ValueError("portable closure parameter is not a port")
        runtime.ledger.bump("proof_artifact_loading_work")
        runtime.ledger.bump("proof_artifact_expression_loads")
        return arena.variable(
            _restore_sort(runtime, primitive, portable.sort, action_cache, sort_cache),
            portable.role,
        )

    def expression(root: int, parameters: dict[int, ExprID]) -> ExprID:
        transaction = ExpressionTransaction(arena)
        resolved = {index: handle.local_id for index, handle in parameters.items()}
        pending = [(root, False)]
        while pending:
            index, ready = pending.pop()
            if index in resolved:
                continue
            portable = artifact.expressions[index]
            if not ready:
                pending.append((index, True))
                pending.extend(
                    (child, False)
                    for child in reversed(portable.children)
                    if child not in resolved
                )
                continue
            if any(child not in resolved for child in portable.children):
                raise ValueError("portable expression order is cyclic")
            if portable.closure >= 0 and portable.closure not in closures:
                raise ValueError("portable closure was not topologically available")
            action = (
                None
                if portable.action_exponent < 0
                else _restored_action(
                    runtime, primitive, portable.action_exponent, action_cache
                )
            )
            function = None if portable.function < 0 else finite_ids[portable.function]
            closure = None if portable.closure < 0 else closures[portable.closure]
            node = BoundaryExprNode(
                cast(ExpressionKind, portable.kind),
                _restore_sort(
                    runtime, primitive, portable.sort, action_cache, sort_cache
                ),
                tuple(resolved[child] for child in portable.children),
                role=portable.role,
                bound=portable.bound,
                value=portable.value,
                action=action,
                side=portable.side,
                function=function,
                closure=closure,
                binding_safe=portable.binding_safe,
            )
            runtime.ledger.bump("proof_artifact_loading_work")
            runtime.ledger.bump("proof_artifact_expression_loads")
            resolved[index] = transaction.intern(node)
        return transaction.publish(resolved[root])

    for index, record in enumerate(artifact.closures):
        parameters = tuple(port(item) for item in record.parameters)
        mapping = dict(zip(record.parameters, parameters, strict=True))
        body = expression(record.body, mapping)
        runtime.ledger.bump("proof_artifact_loading_work")
        runtime.ledger.bump("proof_artifact_closure_loads")
        closure = arena.closures.intern_canonical(parameters, body)
        expected = tuple(mapping[item] for item in record.support)
        if arena.closures.resolve(closure).support != expected:
            raise ValueError("portable closure support changed during binding")
        closures[index] = closure
    runtime.ledger.bump(
        "proof_artifact_loading_c4_summary_nodes", len(artifact.expressions)
    )
    parameters = tuple(port(item) for item in artifact.root_parameters)
    mapping = dict(zip(artifact.root_parameters, parameters, strict=True))
    runtime.ledger.bump("proof_artifact_loading_work")
    runtime.ledger.bump("proof_artifact_closure_loads")
    root = arena.closures.intern_canonical(
        parameters, expression(artifact.root_body, mapping)
    )
    if (
        tuple(mapping[item] for item in artifact.root_support)
        != arena.closures.resolve(root).support
    ):
        raise ValueError("portable root closure support changed during binding")
    return root


def build_isolated_c4_artifact(digest: str) -> C4UnarySummaryArtifact:
    """Build shared proof data without borrowing the requesting index."""
    effect = PhysicalCollatzFourBlockEffect()
    ledger = ResourceLedger()
    from number_compiler.sequences.collatz.tile_family_hooks import (
        collatz_compatibility_tile_hooks,
    )

    compiler = LazyCompiler(
        ledger, family_hooks=collatz_compatibility_tile_hooks(effect)
    )
    atom = compiler.atom(effect)
    source = ExactSource(
        (0, 1) * 8,
        effect.base,
        blank=effect.blank,
        extent=16,
        alphabet_size=effect.blank,
    )
    geometry = SourceGeometry(ledger, source)
    geometry.span(source.digits, source.blank, 16)
    runtime = DiamondRuntime(compiler, geometry)
    primitive = runtime.actions.intern(atom)
    runtime.kernel(primitive)
    pair = runtime.actions.compose(primitive, primitive)
    fourth = runtime.actions.compose(pair, pair)
    cell = runtime.cells.source(0, 4)
    if c4_artifact_recipe(runtime, fourth, cell, 1) != digest:
        raise ValueError("isolated C4 artifact recipe differs from its requester")
    return _freeze(runtime, fourth, cell, 1, digest)


def _preflight_first_target_reservation(runtime: DiamondRuntime) -> None:
    ledger = runtime.ledger
    if (
        ledger.max_nodes is not None
        and ledger.nodes + 1 > ledger.max_nodes
        or ledger.max_cache_entries is not None
        and ledger.entries + 2 > ledger.max_cache_entries
    ):
        raise BlockContextBudgetExceeded(
            "proof artifact target has no publication capacity"
        )


def c4_fourth_right_summary(
    runtime: DiamondRuntime,
    action: ActionProgramID,
    cell: CellID,
    *,
    uncached: UncachedBuild | None = None,
    registry: ImmutableArtifactRegistry = REGISTRY,
) -> ClosureProgramID:
    """Return a fresh-runtime closure from one immutable upstream proof artifact."""
    digest = c4_artifact_recipe(runtime, action, cell, 1)
    try:
        _preflight_first_target_reservation(runtime)
    except BaseException:
        runtime.ledger.bump("proof_artifact_loading_failures")
        runtime.ledger.bump("proof_artifact_c4_summary_loading_failures")
        raise
    if type(registry) is not ImmutableArtifactRegistry:
        raise TypeError("C4 summary requires an immutable proof registry")
    try:
        artifact, hit = registry.obtain(
            ArtifactKey(_KIND, digest),
            lambda: build_isolated_c4_artifact(digest),
            uncached=uncached,
        )
    except BaseException:
        runtime.ledger.bump("proof_artifact_build_failures")
        runtime.ledger.bump("proof_artifact_c4_summary_build_failures")
        raise
    try:
        artifact = _validate_artifact(artifact, digest)
        _preflight_bind(runtime, artifact)
    except BaseException:
        runtime.ledger.bump("proof_artifact_loading_failures")
        runtime.ledger.bump("proof_artifact_c4_summary_loading_failures")
        raise
    runtime.ledger.bump("proof_artifact_hits" if hit else "proof_artifact_builds")
    runtime.ledger.bump(
        "proof_artifact_c4_summary_hits" if hit else "proof_artifact_c4_summary_builds"
    )
    try:
        return _bind(runtime, action, artifact)
    except BaseException:
        runtime.ledger.bump("proof_artifact_loading_failures")
        runtime.ledger.bump("proof_artifact_c4_summary_loading_failures")
        raise


__all__ = ["C4UnarySummaryArtifact", "c4_fourth_right_summary"]
