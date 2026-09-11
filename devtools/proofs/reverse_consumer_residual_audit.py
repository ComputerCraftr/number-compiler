"""Complete small-interface audit of branch-restricted reverse consumers.

This is an exact bounded oracle over every symmetric source through capacity
four.  It evaluates the primitive mod-9 geometry DAG once per source, then
records each table/native-domain consumer only when the branch-selected trace
actually observes that node.  Expression IDs never enter response identity.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.proofs import exact_oracle
from devtools.proofs.reverse_geometry_context import ReverseGeometryContext
from devtools.proofs.reverse_successor_image_audit import _sources
from devtools.proofs.threshold_expressions import ConsumerSchema
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.finite_unary import (
    analyze_observer,
    minimize_unary_moore,
)
from number_compiler.arithmetic.carry.event_memory import pair_step

_NATIVE_CONSUMERS = frozenset(
    {
        "mirror_pair",
        "mirror_domain",
        "decimal_sum_domain",
        "growth_symbol",
        "growth_domain",
        "growth_value_plane",
        "skew_pair_domain",
    }
)


@dataclass(frozen=True, slots=True)
class ReverseConsumerResidualAudit:
    capacity: int
    context_rows: int
    action_admitted_rows: int
    overflow_rows: int
    structural_consumer_occurrences: int
    exact_response_classes: int
    unobserved_constant_occurrences: int
    branch_masked_occurrences: int
    response_cells: int
    reachable_nodes: int
    scan_work: int
    initial_action_classes: int
    initial_successor_conflicts: int
    horizon_1_classes: int
    horizon_2_classes: int
    horizon_4_classes: int
    pullback_classes: int
    pullback_rounds: int
    initial_successor_closed: bool
    refined_successor_conflicts: int
    refined_successor_closed: bool
    general_successor_closure_claimed: bool = False


def _context_count(capacity: int) -> int:
    return sum(
        (19 ** (width // 2)) * (10 if width % 2 else 1)
        for width in range(1, capacity + 1)
    )


def _class_ids(values: tuple[object, ...]) -> tuple[int, ...]:
    classes: dict[object, int] = {}
    return tuple(classes.setdefault(value, len(classes)) for value in values)


def _selected_trace(
    roots: tuple[int, ...], values: dict[int, int], context: ReverseGeometryContext
) -> set[int]:
    nodes = context.expressions.nodes
    reached: set[int] = set()
    pending = list(roots)
    while pending:
        index = pending.pop()
        if index in reached:
            continue
        reached.add(index)
        node = nodes[index]
        if node.kind == "select":
            condition, yes, no = node.args
            pending.append(condition)
            pending.append(yes if values[condition] else no)
        else:
            pending.extend(node.args)
    return reached


def _bounded_future_classes(
    initial: tuple[int, ...], successors: tuple[int, ...], horizon: int
) -> int:
    """Count exact response histories through ``horizon`` transitions.

    The overflow sink has its own response and is excluded from the reported
    source-class count.  This is a finite-interface measurement, not a claim
    about sources wider than ``capacity``.
    """
    rows: list[tuple[int, ...]] = []
    for source in range(len(successors) - 1):
        state = source
        response = [initial[state]]
        for _ in range(horizon):
            state = successors[state]
            response.append(initial[state])
        rows.append(tuple(response))
    return len(set(rows))


def audit_reverse_consumer_residuals(
    capacity: int,
    *,
    max_contexts: int = 1000,
    max_cells: int = 1_000_000,
) -> ReverseConsumerResidualAudit:
    """Audit free responses and bounded source-context continuation separately.

    ``ConsumerSchema`` values identify exact finite response functions over the
    complete context.  The horizon and Moore counts instead partition concrete
    source contexts by their bounded future responses; they are not free-action
    residual continuation IDs.
    """
    capacity, max_contexts, max_cells = int(capacity), int(max_contexts), int(max_cells)
    if not 1 <= capacity <= 4 or max_contexts < 1 or max_cells < 1:
        raise ValueError((capacity, max_contexts, max_cells))
    context_count = _context_count(capacity)
    if context_count > max_contexts:
        raise BlockContextBudgetExceeded("reverse consumer context budget exceeded")

    with exact_oracle():
        context = ReverseGeometryContext(capacity, value_quotient="mod9")
        action = context.primitive()
        e = context.expressions
        roots = (action.admitted, *action.outputs)
        reached = e.reachable(roots)
        ordered = tuple(sorted(reached))
        consumers = tuple(
            index
            for index in ordered
            if e.nodes[index].kind == "table"
            or e.nodes[index].kind in _NATIVE_CONSUMERS
        )
        response_cells = context_count * len(consumers)
        scan_work = context_count * len(ordered)
        if response_cells + scan_work > max_cells:
            raise BlockContextBudgetExceeded("reverse consumer cell budget exceeded")

        sources = tuple(
            source for width in range(1, capacity + 1) for source in _sources(width)
        )
        if len(sources) != context_count:
            raise AssertionError((len(sources), context_count))
        columns: list[list[int]] = [[] for _ in consumers]
        action_rows: list[object] = []
        admitted_count = overflow_count = masked_occurrences = 0
        for source in sources:
            binding = context.binding(source)
            evaluated = e.evaluate(tuple(e.handle(index) for index in ordered), binding)
            values = dict(zip(ordered, evaluated, strict=True))
            admitted = bool(values[action.admitted.index])
            admitted_count += int(admitted)
            overflow_count += int(not admitted)
            trace_roots = (
                tuple(output.index for output in action.outputs)
                + (action.admitted.index,)
                if admitted
                else (action.admitted.index,)
            )
            trace = _selected_trace(trace_roots, values, context)
            response: list[int] = []
            for column, index in zip(columns, consumers, strict=True):
                observed = index in trace
                encoded = 1 + values[index] if observed else 0
                column.append(encoded)
                response.append(encoded)
                masked_occurrences += int(not observed)
            action_rows.append((int(admitted), tuple(response)))

        schemas = tuple(
            ConsumerSchema(context_count, e.nodes[index].size + 1, tuple(column))
            for index, column in zip(consumers, columns, strict=True)
        )
        source_index = {source: index for index, source in enumerate(sources)}
        sink = len(sources)
        successors: list[int] = []
        for source in sources:
            output, _growth = pair_step(source, 10)
            successors.append(sink if len(output) > capacity else source_index[output])
        successors.append(sink)
        initial = _class_ids(tuple(action_rows) + (("overflow-sink",),))
        signatures: dict[int, int] = {}
        conflicts = 0
        for state, class_id in enumerate(initial):
            target = initial[successors[state]]
            previous = signatures.setdefault(class_id, target)
            conflicts += int(previous != target)
        minimized = minimize_unary_moore(
            tuple(successors),
            initial,
        )
        refined = analyze_observer(
            minimized.class_ids,
            tuple(minimized.class_ids[target] for target in successors),
        )
        return ReverseConsumerResidualAudit(
            capacity,
            context_count,
            admitted_count,
            overflow_count,
            len(consumers),
            len(set(schemas)),
            sum(
                len(set(schema.table)) == 1 and schema.table[0] == 0
                for schema in schemas
            ),
            masked_occurrences,
            response_cells,
            len(ordered),
            scan_work,
            len(set(initial)) - 1,
            conflicts,
            _bounded_future_classes(initial, tuple(successors), 1),
            _bounded_future_classes(initial, tuple(successors), 2),
            _bounded_future_classes(initial, tuple(successors), 4),
            minimized.classes - 1,
            minimized.rounds,
            conflicts == 0,
            refined.successor_conflicts,
            refined.next_closed,
            False,
        )


__all__ = ["ReverseConsumerResidualAudit", "audit_reverse_consumer_residuals"]
