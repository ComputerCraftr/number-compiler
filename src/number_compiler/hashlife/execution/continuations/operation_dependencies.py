"""Operation dependencies with one canonical implementation owner."""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_summaries import (
    ContextLeaf,
    ContextSpatial,
    HigherSummaryID,
    UnaryAffine,
    UnaryFinite,
    UnaryIdentity,
    UnaryLeaf,
    UnarySpatial,
    UnaryTemporal,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeActionFunction,
    RuntimeAtom,
    RuntimeContextState,
    RuntimeFunction,
    RuntimePair,
    RuntimeSummaryFunction,
    RuntimeTableFunction,
    RuntimeTransferredState,
    RuntimeValueID,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_operations import (
        OperationMachine,
        RuntimeFunctionRequest,
    )
    from number_compiler.hashlife.execution.continuations.higher_semantic import (
        HigherSemanticArena,
    )


def advance_operation(
    arena: HigherSemanticArena,
    machine: OperationMachine,
    supplied: RuntimeAtom | None = None,
) -> RuntimeAtom | RuntimeFunctionRequest:
    """Advance until completion or a syntax continuation must be evaluated."""
    from number_compiler.hashlife.execution.continuations.higher_operations import (
        MAX_EXTENSIONAL_TABLE_DOMAIN,
        RuntimeFunctionRequest,
        canonical_operation_task,
        constant_anchor,
        has_primitive_children,
        is_constant_function,
        operation_children,
        singleton_state,
    )

    values = arena.runtime_values
    tasks, results = machine.tasks, machine.results
    if supplied is not None:
        values.validate_atom(supplied)
        results.append(supplied)
    while tasks:
        task = tasks.pop()
        tag = cast(str, task[0])
        if tag == "force" and type(task[1]) is int:
            results.append(task[1])
            continue
        task = canonical_operation_task(arena, task)
        if tag in ("initial", "step", "emit", "apply", "force"):
            cached = values.operations.get(task)
            if cached is not None:
                arena.ledger.bump(_execution_keys.HIGHER_CONCRETE_OPERATION_HITS)
                results.append(cached)
                continue
            arena.ledger.bump(_execution_keys.HIGHER_CONCRETE_OPERATION_EVALUATIONS)
            arena.ledger.bump(f"higher_concrete_{tag}_evaluations")
            tasks.extend((("cache-operation", task), (tag + "-run", *task[1:])))
            continue
        if tag == "cache-operation":
            values.publish_operation(cast(tuple[object, ...], task[1]), results[-1])
            continue
        if tag == "push":
            value = cast(RuntimeAtom, task[1])
            values.validate_atom(value)
            results.append(value)
            continue
        if tag == "initial-run":
            current, current_side = cast(FieldCellActionID, task[1]), cast(int, task[2])
            children = operation_children(arena, machine, current)
            if children is None:
                results.append(arena.schema.initial(current, current_side))
                continue
            before, after = children
            tasks.extend(
                (
                    ("initial-done", current, current_side),
                    ("initial", after, current_side),
                    ("initial", before, current_side),
                )
            )
            continue
        if tag == "initial-done":
            current, current_side = cast(FieldCellActionID, task[1]), cast(int, task[2])
            after_value, before_value = results.pop(), results.pop()
            primitive_children = has_primitive_children(
                arena,
                machine,
                current,
            )
            domain = (
                arena.schema.state_count(primitive_children[0], 1 - current_side)
                if primitive_children is not None
                else 0
            )
            if (
                primitive_children is not None
                and domain <= MAX_EXTENSIONAL_TABLE_DOMAIN
                and type(after_value) is int
            ):
                continuation = values.table_function(
                    current,
                    current_side,
                    (after_value,) * domain,
                )
                arena.ledger.bump(_execution_keys.HIGHER_EXTENSIONAL_TABLE_PUBLICATIONS)
            else:
                continuation = values.action_function(
                    "constant",
                    current,
                    current_side,
                    after_value,
                    None,
                    -1,
                )
            results.append(values.pair(before_value, continuation))
            continue
        if tag == "step-run":
            current, current_side = cast(FieldCellActionID, task[1]), cast(int, task[2])
            state, symbol = cast(RuntimeAtom, task[3]), cast(RuntimeAtom, task[4])
            if type(symbol) is not int:
                raise ValueError("higher action step symbol is structured")
            state_record = (
                values.resolve(state) if type(state) is RuntimeValueID else None
            )
            if type(state_record) in (RuntimeTransferredState, RuntimeContextState):
                tasks.extend(
                    (
                        ("step-after-force", current, current_side, symbol),
                        ("force", state),
                    )
                )
                continue
            children = operation_children(arena, machine, current)
            if children is None:
                if type(state) is not int:
                    raise ValueError("primitive higher action state is structured")
                results.append(
                    state
                    if arena.schema.kind(current) == "identity"
                    else arena.primitive_tables.step(
                        current, current_side, state, symbol
                    )
                )
                continue
            pair = state_record
            if type(pair) is not RuntimePair:
                raise ValueError("composed higher action state is not a pair")
            # A bottom temporal diamond has a genuinely finite local port:
            # the anchor is one primitive boundary state and the continuation
            # is a complete table over the opposite primitive boundary.  Apply
            # that extensional carrier directly.  Sending it back through the
            # generic higher task machine used to rebuild the two primitive
            # halves for every source context, which made the lowest rung
            # dominate otherwise binary-powered observations.
            primitive_children = has_primitive_children(arena, machine, current)
            prior = values.resolve(pair.continuation)
            if (
                primitive_children is not None
                and type(pair.anchor) is int
                and type(prior) is RuntimeTableFunction
            ):
                before, after = primitive_children
                opposite = 1 - current_side
                domain = arena.schema.state_count(before, opposite)
                if len(prior.outputs) != domain:
                    raise ValueError("bounded continuation has another domain")
                direct_same = arena.primitive_tables.step(
                    before,
                    current_side,
                    pair.anchor,
                    symbol,
                )
                direct_outputs: list[int] = []
                for ordinal in range(domain):
                    primitive_stepped = arena.primitive_tables.step(
                        before,
                        opposite,
                        ordinal,
                        symbol,
                    )
                    primitive_incoming = prior.outputs[primitive_stepped]
                    primitive_left, primitive_right = (
                        (pair.anchor, ordinal)
                        if current_side == 0
                        else (ordinal, pair.anchor)
                    )
                    primitive_middle = arena.primitive_tables.emit(
                        before,
                        primitive_left,
                        symbol,
                        primitive_right,
                    )
                    direct_outputs.append(
                        arena.primitive_tables.step(
                            after,
                            current_side,
                            primitive_incoming,
                            primitive_middle,
                        )
                    )
                continuation = values.table_function(
                    current,
                    current_side,
                    tuple(direct_outputs),
                )
                arena.ledger.bump(_execution_keys.BOUNDED_LOCAL_INTERFACE_APPLICATIONS)
                results.append(values.pair(direct_same, continuation))
                continue
            tasks.extend(
                (
                    ("step-done", current, current_side, pair, symbol),
                    ("step", children[0], current_side, pair.anchor, symbol),
                )
            )
            continue
        if tag == "step-after-force":
            current, current_side, symbol = (
                cast(FieldCellActionID, task[1]),
                cast(int, task[2]),
                cast(int, task[3]),
            )
            tasks.append(("step-run", current, current_side, results.pop(), symbol))
            continue
        if tag == "step-done":
            current, current_side = cast(FieldCellActionID, task[1]), cast(int, task[2])
            pair, symbol = cast(RuntimePair, task[3]), cast(int, task[4])
            same = results.pop()
            children = operation_children(arena, machine, current)
            if children is None:
                raise AssertionError("composed step lost its child actions")
            if singleton_state(arena, machine, children[1], current_side):
                tasks.extend(
                    (
                        ("step-singleton-done", current, current_side, same),
                        ("initial", children[1], current_side),
                    )
                )
                continue
            continuation = values.action_function(
                "step",
                current,
                current_side,
                pair.anchor,
                pair.continuation,
                symbol,
            )
            results.append(values.pair(same, continuation))
            continue
        if tag == "step-singleton-done":
            current, current_side, same = (
                cast(FieldCellActionID, task[1]),
                cast(int, task[2]),
                cast(RuntimeAtom, task[3]),
            )
            singleton = results.pop()
            continuation = values.action_function(
                "constant",
                current,
                current_side,
                singleton,
                None,
                -1,
            )
            arena.ledger.bump(_execution_keys.HIGHER_SINGLETON_CONTINUATION_ELISIONS)
            results.append(values.pair(same, continuation))
            continue
        if tag == "emit-run":
            current = cast(FieldCellActionID, task[1])
            left = cast(RuntimeAtom, task[3])
            symbol = cast(RuntimeAtom, task[4])
            right = cast(RuntimeAtom, task[5])
            if type(symbol) is not int:
                raise ValueError("higher action emit symbol is structured")
            left_record = values.resolve(left) if type(left) is RuntimeValueID else None
            if type(left_record) in (RuntimeTransferredState, RuntimeContextState):
                tasks.extend(
                    (
                        ("emit-after-left-force", current, symbol, right),
                        ("force", left),
                    )
                )
                continue
            right_record = (
                values.resolve(right) if type(right) is RuntimeValueID else None
            )
            if type(right_record) in (RuntimeTransferredState, RuntimeContextState):
                tasks.extend(
                    (
                        ("emit-after-right-force", current, left, symbol),
                        ("force", right),
                    )
                )
                continue
            children = operation_children(arena, machine, current)
            if children is None:
                if not all(type(item) is int for item in (left, right)):
                    raise ValueError("primitive higher action boundary is structured")
                results.append(
                    symbol
                    if arena.schema.kind(current) == "identity"
                    else arena.primitive_tables.emit(
                        current, cast(int, left), symbol, cast(int, right)
                    )
                )
                continue
            left_pair = left_record
            right_pair = right_record
            if (
                type(left_pair) is not RuntimePair
                or type(right_pair) is not RuntimePair
            ):
                raise ValueError("composed higher emission requires pair boundaries")
            primitive_children = has_primitive_children(arena, machine, current)
            left_continuation = values.resolve(left_pair.continuation)
            right_continuation = values.resolve(right_pair.continuation)
            if (
                primitive_children is not None
                and type(left_pair.anchor) is int
                and type(right_pair.anchor) is int
                and type(left_continuation) is RuntimeTableFunction
                and type(right_continuation) is RuntimeTableFunction
            ):
                before, after = primitive_children
                left_domain = arena.schema.state_count(before, 1)
                right_domain = arena.schema.state_count(before, 0)
                if (
                    len(left_continuation.outputs) != left_domain
                    or len(right_continuation.outputs) != right_domain
                ):
                    raise ValueError("bounded emission continuation has another domain")
                direct_middle = arena.primitive_tables.emit(
                    before,
                    left_pair.anchor,
                    symbol,
                    right_pair.anchor,
                )
                left_argument = arena.primitive_tables.step(
                    before,
                    1,
                    right_pair.anchor,
                    symbol,
                )
                right_argument = arena.primitive_tables.step(
                    before,
                    0,
                    left_pair.anchor,
                    symbol,
                )
                direct_left_after = left_continuation.outputs[left_argument]
                direct_right_after = right_continuation.outputs[right_argument]
                results.append(
                    arena.primitive_tables.emit(
                        after,
                        direct_left_after,
                        direct_middle,
                        direct_right_after,
                    )
                )
                arena.ledger.bump(_execution_keys.BOUNDED_LOCAL_INTERFACE_APPLICATIONS)
                continue
            tasks.extend(
                (
                    (
                        "emit-after-first",
                        children[0],
                        children[1],
                        left_pair,
                        right_pair,
                        symbol,
                    ),
                    (
                        "emit",
                        children[0],
                        -1,
                        left_pair.anchor,
                        symbol,
                        right_pair.anchor,
                    ),
                )
            )
            continue
        if tag == "emit-after-left-force":
            current, symbol, right = (
                cast(FieldCellActionID, task[1]),
                cast(int, task[2]),
                cast(RuntimeAtom, task[3]),
            )
            tasks.append(("emit-run", current, -1, results.pop(), symbol, right))
            continue
        if tag == "emit-after-right-force":
            current, left, symbol = (
                cast(FieldCellActionID, task[1]),
                cast(RuntimeAtom, task[2]),
                cast(int, task[3]),
            )
            tasks.append(("emit-run", current, -1, left, symbol, results.pop()))
            continue
        if tag == "emit-after-first":
            before, after, left_pair, right_pair, symbol = (
                cast(FieldCellActionID, task[1]),
                cast(FieldCellActionID, task[2]),
                cast(RuntimePair, task[3]),
                cast(RuntimePair, task[4]),
                cast(int, task[5]),
            )
            middle = results.pop()
            left_constant = constant_anchor(arena, machine, left_pair.continuation)
            right_constant = constant_anchor(arena, machine, right_pair.continuation)
            left_tasks = (
                (("push", left_constant),)
                if left_constant is not None
                else (("apply", left_pair.continuation, right_pair.anchor),)
                if is_constant_function(arena, left_pair.continuation)
                else (
                    ("apply-after-step", left_pair.continuation),
                    ("step", before, 1, right_pair.anchor, symbol),
                )
            )
            right_tasks = (
                (("push", right_constant),)
                if right_constant is not None
                else (("apply", right_pair.continuation, left_pair.anchor),)
                if is_constant_function(arena, right_pair.continuation)
                else (
                    ("apply-after-step", right_pair.continuation),
                    ("step", before, 0, left_pair.anchor, symbol),
                )
            )
            arena.ledger.bump(
                _execution_keys.HIGHER_CONSTANT_ARGUMENT_ELISIONS,
                int(
                    left_constant is not None
                    or is_constant_function(arena, left_pair.continuation)
                )
                + int(
                    right_constant is not None
                    or is_constant_function(arena, right_pair.continuation)
                ),
            )
            tasks.extend((("emit-final", after, middle), *right_tasks, *left_tasks))
            continue
        if tag == "apply-after-step":
            stepped = results.pop()
            tasks.append(("apply", cast(RuntimeValueID, task[1]), stepped))
            continue
        if tag == "emit-final":
            after, middle = cast(FieldCellActionID, task[1]), cast(RuntimeAtom, task[2])
            right_after, left_after = results.pop(), results.pop()
            tasks.append(("emit", after, -1, left_after, middle, right_after))
            continue
        if tag == "apply-run":
            function_id, argument = (
                cast(RuntimeValueID, task[1]),
                cast(RuntimeAtom, task[2]),
            )
            function = values.resolve(function_id)
            argument_record = (
                values.resolve(argument) if type(argument) is RuntimeValueID else None
            )
            if type(argument_record) in (RuntimeTransferredState, RuntimeContextState):
                tasks.extend((("apply-after-force", function_id), ("force", argument)))
                continue
            if type(function) is RuntimeFunction:
                return RuntimeFunctionRequest(function, argument)
            if type(function) is RuntimeTableFunction:
                results.append(function.apply(argument))
                continue
            if type(function) is RuntimeSummaryFunction:
                summaries = arena.summary_runtime
                if summaries is None:
                    raise ValueError("summary continuation has no bound runtime")
                constant_input = constant_anchor(arena, machine, function.continuation)
                left, right = (
                    (function.anchor, argument)
                    if function.side == 0
                    else (argument, function.anchor)
                )
                tasks.append(
                    (
                        "apply-summary-context",
                        function.context,
                        left,
                        right,
                        function.side,
                    )
                )
                if constant_input is not None:
                    tasks.append(("push", constant_input))
                    arena.ledger.bump(_execution_keys.HIGHER_CONSTANT_ARGUMENT_ELISIONS)
                else:
                    opposite_value = summaries.transfer_value(
                        function.opposite,
                        argument,
                    )
                    tasks.append(("apply", function.continuation, opposite_value))
                continue
            if type(function) is not RuntimeActionFunction:
                raise ValueError("opaque action received a non-function")
            if function.kind == "constant":
                results.append(function.anchor)
                continue
            if function.continuation is None:
                raise AssertionError("step continuation lost its prior function")
            children = operation_children(arena, machine, function.action)
            if children is None:
                raise AssertionError("step continuation action is primitive")
            before, after = children
            incoming_constant = constant_anchor(arena, machine, function.continuation)
            if incoming_constant is not None:
                left, right = (
                    (function.anchor, argument)
                    if function.side == 0
                    else (argument, function.anchor)
                )
                tasks.extend(
                    (
                        ("apply-after-input", after, function.side),
                        ("emit", before, -1, left, function.symbol, right),
                        ("push", incoming_constant),
                    )
                )
                arena.ledger.bump(_execution_keys.HIGHER_CONSTANT_ARGUMENT_ELISIONS)
                continue
            if is_constant_function(arena, function.continuation):
                left, right = (
                    (function.anchor, argument)
                    if function.side == 0
                    else (argument, function.anchor)
                )
                tasks.extend(
                    (
                        ("apply-after-input", after, function.side),
                        ("emit", before, -1, left, function.symbol, right),
                        ("apply", function.continuation, argument),
                    )
                )
                arena.ledger.bump(_execution_keys.HIGHER_CONSTANT_ARGUMENT_ELISIONS)
                continue
            opposite = 1 - function.side
            tasks.extend(
                (
                    ("apply-after-opposite", after, function, argument),
                    ("step", before, opposite, argument, function.symbol),
                )
            )
            continue
        if tag == "apply-after-force":
            tasks.append(("apply-run", cast(RuntimeValueID, task[1]), results.pop()))
            continue
        if tag == "apply-summary-context":
            summary, left, right, current_side = (
                task[1],
                cast(RuntimeAtom, task[2]),
                cast(RuntimeAtom, task[3]),
                cast(int, task[4]),
            )
            summaries = arena.summary_runtime
            if summaries is None:
                raise ValueError("summary context has no bound runtime")
            incoming = results.pop()
            tasks.append(
                (
                    "force",
                    summaries.context_value(
                        cast(HigherSummaryID, summary),
                        left,
                        right,
                        incoming,
                        current_side,
                    ),
                )
            )
            continue
        if tag == "force-run":
            atom = cast(RuntimeAtom, task[1])
            values.validate_atom(atom)
            if type(atom) is int:
                results.append(atom)
                continue
            reference = cast(RuntimeValueID, atom)
            record = values.resolve(reference)
            summaries = arena.summary_runtime
            if summaries is None:
                raise ValueError("transferred state has no bound summary runtime")
            if type(record) is RuntimeTransferredState:
                summary = summaries.runtime_unary_record(record.summary)
                recipe = summary.recipe
                if type(recipe) is UnaryIdentity:
                    results.append(record.incoming)
                    continue
                if type(recipe) is UnaryAffine:
                    tasks.extend(
                        (("force-affine-transfer", recipe), ("force", record.incoming))
                    )
                    continue
                if type(recipe) is UnaryFinite:
                    tasks.extend(
                        (("force-finite-transfer", recipe), ("force", record.incoming))
                    )
                    continue
                if type(recipe) is UnaryLeaf:
                    tasks.append(
                        (
                            "step",
                            summary.action,
                            summary.side,
                            record.incoming,
                            recipe.symbol,
                        )
                    )
                    continue
                if type(recipe) is UnarySpatial:
                    tasks.extend(
                        (
                            ("force-spatial-after-first", recipe.second),
                            (
                                "force",
                                summaries.transfer_value(
                                    recipe.first,
                                    record.incoming,
                                ),
                            ),
                        )
                    )
                    continue
                if type(recipe) is not UnaryTemporal:
                    raise AssertionError("unknown unary summary recipe")
                tasks.extend(
                    (
                        (
                            "force-temporal-summary",
                            recipe,
                            summary.side,
                            summary.action,
                        ),
                        ("force", record.incoming),
                    )
                )
                continue
            if type(record) is RuntimeContextState:
                ports = record.left, record.right, record.incoming
                if any(
                    type(value) is RuntimeValueID
                    and type(values.resolve(value))
                    in (
                        RuntimeTransferredState,
                        RuntimeContextState,
                    )
                    for value in ports
                ):
                    tasks.append(("force-context-normalized", record))
                    tasks.extend(("force", value) for value in reversed(ports))
                    continue
                context = summaries.runtime_context_record(record.summary)
                context_recipe = context.recipe
                if type(context_recipe) is ContextLeaf:
                    tasks.extend(
                        (
                            (
                                "context-leaf-after-emit",
                                context.consumer,
                                record.side,
                                record.incoming,
                            ),
                            (
                                "emit",
                                context.provider,
                                -1,
                                record.left,
                                context_recipe.symbol,
                                record.right,
                            ),
                        )
                    )
                    continue
                if type(context_recipe) is not ContextSpatial:
                    raise AssertionError("unknown context summary recipe")
                middle_left = summaries.transfer_value(
                    context_recipe.low_forward, record.left
                )
                middle_right = summaries.transfer_value(
                    context_recipe.high_backward, record.right
                )
                if record.side == 0:
                    midpoint = summaries.context_value(
                        context_recipe.low,
                        record.left,
                        middle_right,
                        record.incoming,
                        0,
                    )
                    outer = summaries.context_value(
                        context_recipe.high,
                        middle_left,
                        record.right,
                        midpoint,
                        0,
                    )
                else:
                    midpoint = summaries.context_value(
                        context_recipe.high,
                        middle_left,
                        record.right,
                        record.incoming,
                        1,
                    )
                    outer = summaries.context_value(
                        context_recipe.low,
                        record.left,
                        middle_right,
                        midpoint,
                        1,
                    )
                tasks.append(("force", outer))
                continue
            results.append(reference)
            continue
        if tag == "force-context-normalized":
            context_state = cast(RuntimeContextState, task[1])
            incoming, right, left = results.pop(), results.pop(), results.pop()
            canonical = values.context_state(
                context_state.summary,
                left,
                right,
                incoming,
                context_state.side,
            )
            tasks.append(("force", canonical))
            continue
        if tag == "force-affine-transfer":
            affine = cast(UnaryAffine, task[1])
            incoming = results.pop()
            if type(incoming) is not int:
                raise ValueError("affine port input must be a finite scalar")
            results.append(affine.transfer.apply(incoming, arena.ledger))
            continue
        if tag == "force-finite-transfer":
            finite = cast(UnaryFinite, task[1])
            incoming = results.pop()
            if type(incoming) is not int or not 0 <= incoming < len(finite.outputs):
                raise ValueError("finite transfer input has another port sort")
            results.append(finite.outputs[incoming])
            continue
        if tag == "force-spatial-after-first":
            summaries = arena.summary_runtime
            if summaries is None:
                raise ValueError("spatial transfer has no bound summary runtime")
            middle = results.pop()
            tasks.append(
                (
                    "force",
                    summaries.transfer_value(
                        cast(HigherSummaryID, task[1]),
                        middle,
                    ),
                )
            )
            continue
        if tag == "force-temporal-summary":
            summaries = arena.summary_runtime
            if summaries is None:
                raise ValueError("temporal transfer has no bound summary runtime")
            recipe, current_side = cast(UnaryTemporal, task[1]), cast(int, task[2])
            incoming = results.pop()
            pair = values.resolve(cast(RuntimeValueID, incoming))
            if type(pair) is not RuntimePair:
                raise ValueError("temporal K summary input is not a pair")
            anchor = summaries.transfer_value(
                recipe.forward,
                pair.anchor,
            )
            continuation = values.summary_function(
                recipe.context,
                recipe.opposite,
                current_side,
                pair.anchor,
                pair.continuation,
            )
            action = cast(FieldCellActionID, task[3])
            primitive_children = has_primitive_children(arena, machine, action)
            domain = (
                arena.schema.state_count(primitive_children[0], 1 - current_side)
                if primitive_children is not None
                else 0
            )
            if (
                primitive_children is not None
                and domain <= MAX_EXTENSIONAL_TABLE_DOMAIN
            ):
                tasks.append(("force-temporal-table", action, current_side, domain))
                tasks.extend(
                    ("apply", continuation, state) for state in reversed(range(domain))
                )
                tasks.append(("force", anchor))
                arena.ledger.bump(
                    _execution_keys.HIGHER_FINITE_TRANSFER_STATE_VISITS,
                    domain,
                )
            else:
                results.append(values.pair(anchor, continuation))
            continue
        if tag == "force-temporal-table":
            from number_compiler.hashlife.execution.continuations.higher_operations import (
                publish_temporal_table,
            )

            publish_temporal_table(arena, machine, task)
            continue
        if tag == "context-leaf-after-emit":
            consumer, current_side, incoming = (
                cast(FieldCellActionID, task[1]),
                cast(int, task[2]),
                cast(RuntimeAtom, task[3]),
            )
            tasks.append(("step", consumer, current_side, incoming, results.pop()))
            continue
        if tag == "apply-after-opposite":
            after, function, argument = (
                cast(FieldCellActionID, task[1]),
                cast(RuntimeActionFunction, task[2]),
                cast(RuntimeAtom, task[3]),
            )
            opposite_after = results.pop()
            left, right = (
                (function.anchor, argument)
                if function.side == 0
                else (argument, function.anchor)
            )
            tasks.extend(
                (
                    ("apply-after-input", after, function.side),
                    (
                        "emit",
                        (
                            operation_children(arena, machine, function.action)
                            or (None,)
                        )[0],
                        -1,
                        left,
                        function.symbol,
                        right,
                    ),
                    ("apply", function.continuation, opposite_after),
                )
            )
            continue
        if tag == "apply-after-input":
            after, current_side = cast(FieldCellActionID, task[1]), cast(int, task[2])
            middle, incoming = results.pop(), results.pop()
            tasks.append(("step", after, current_side, incoming, middle))
            continue
        raise AssertionError(f"unknown opaque higher operation {tag}")
    if len(results) != 1:
        raise AssertionError("opaque higher operation produced another result arity")
    return results[0]
