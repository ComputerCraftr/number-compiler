"""Canonical development reproduction of the supplied comma Vieta audits.

This finite audit rebuilds chart-derived boundary macros and checks the
reported borrow-return/T3279 and pointed-Vieta counts. It is not production
code, a root derivation, or a native selector. Dead states are pruned by a
linear reverse-edge queue, with no losing-rank table.

The full audit accumulates c1 counts from chart macro fragments with the
production ``C1Return`` power; endpoint arithmetic is only a post-hoc
differential check. Child returns are cached by their actual
``(state, exponent)`` occurrence, where the exponent is the represented parent
exponent plus its exact chart delta. Pointed-only mode skips carry construction.
No exponent sweep is performed.

The original downloaded scripts and patch are pinned in every JSON result by
their SHA-256 digests.  Counts in the report are audit assertions only.
"""

from __future__ import annotations

import argparse
import json
from collections import deque
from collections.abc import Hashable
from dataclasses import asdict, dataclass

from devtools.verification.comma_semantic_quotients import (
    CommaFutureGraph,
    build_future_graph,
    build_future_temporal_quotient,
)
from number_compiler.arithmetic.functions.finite_observer import (
    class_members,
    closed_partition_quotient_rows,
    map_partition_row,
    minimize_finite_observer,
    partition_equivalent,
    partition_quotient_rows,
)
from number_compiler.sequences.comma.boundary_chart import PERIOD
from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    MacroTemplate,
    construct_macro,
)
from number_compiler.sequences.comma.occurrence import (
    BoundaryOccurrence,
    OccurrencePrefixReturn,
)

_SOURCE_ARTIFACT_SHA256 = {
    "comma_borrow_vieta_audit.py": (
        "ef13084c1cb5d3b8c6582b70cc88e5972efc2f8367c8b07f7de66b8391dc126c"
    ),
    "comma_pointed_vieta_audit.py": (
        "b02f6451078b956ba2177f321eddc081e1023a3bf922b634ffee334717df04ec"
    ),
    "A367620_COMMA_BORROW_POINTED_VIETA_AUDITS.patch": (
        "a488dfe3275a201717120a59a189fad5098f902be99b44f6f56193cb2c094a29"
    ),
    "comma_borrow_vieta_constructive_audit.py": (
        "26540c6288595b2850bd589d0a26bc319bd1d8ecf68c078f4f6d234c57192c3e"
    ),
    "comma_pointed_vieta_constructive_audit.py": (
        "f4e01775fbf7fc4d91480aecb25aec8eb5507eecb62ed91ede9c7a27ae20b3e7"
    ),
    "COMMA_BORROW_VIETA_CONSTRUCTIVE_AUDIT_REPORT.md": (
        "3ae6d512d9568a2fc5a04fdfaf6fc7ecbf5ce78bc3297a210ad1f1eaf46ac3cc"
    ),
}

_AUDIT_SCOPE = {
    "purpose": "canonical development reproduction only",
    "macro_c1_count": "powered C1Return sector fragments plus literal seams",
    "macro_c1_runtime_used": True,
    "exponent_policy": (
        "canonical parent exponent plus its exact terminal chart delta; "
        "child action keyed by actual transported exponent"
    ),
    "pointed_classification": "greatest-live reverse-edge queue",
    "constructive_scope": (
        "construct_macro is the exact chart teacher; no production forest deletion"
    ),
    "native_selector": False,
    "counts_are": "finite audit assertions only",
}


@dataclass(frozen=True, slots=True)
class ConstructiveFutureGraph:
    graph: CommaFutureGraph
    macros: tuple[MacroTemplate, ...]
    canonical_returns: tuple[OccurrencePrefixReturn, ...]
    child_returns: tuple[
        tuple[OccurrencePrefixReturn | None, OccurrencePrefixReturn | None], ...
    ]
    constructive_c1_rows: int


@dataclass(frozen=True, slots=True)
class BorrowAudit:
    raw_states: int
    borrow_classes: int
    borrow_right_congruent: bool
    borrow_moore_classes: int
    borrow_moore_fixed_classes: int
    t3279_classes: int
    exact_t3279_partition_match: bool
    losing_raw_states: int
    live_raw_states: int
    pointed_states: int
    pointed_moore_classes: int
    pointed_moore_fixed_classes: int
    live_cycle_length: int
    live_cycle_exponent_gain: int
    live_branch_N: int
    live_branch_Z: int
    losing_borrow_classes: int
    live_borrow_classes: int
    pointed_projection_conflicts: int
    live_borrow_nonsingleton_classes: int
    transported_key_exact_invariant: bool
    transported_zeta_scale_matches: bool
    constructive_c1_rows: int
    endpoint_differential_mismatches: int


@dataclass(frozen=True, slots=True)
class PointedAudit:
    raw_states: int
    losing_raw_states: int
    live_raw_states: int
    pointed_states: int
    pointed_moore_classes: int
    pointed_moore_fixed_classes: int
    live_cycle_length: int
    live_cycle_exponent_gain: int
    live_branch_N: int
    live_branch_Z: int


def canonical_exponent(residue: int) -> int:
    if not 0 <= residue < PERIOD:
        raise ValueError(residue)
    return residue if residue >= 5 else residue + PERIOD


def _state_id(state: BoundaryState) -> int:
    """Return the id in the canonical N-then-Z boundary state ordering."""
    side_size = 8 * PERIOD
    return (
        (0 if state.kind == "N" else side_size)
        + (state.a - 2) * PERIOD
        + state.exponent_residue
    )


def _macro_child_returns(
    parent_id: int,
    parent_exponent: int,
    states: tuple[BoundaryState, ...],
    macros: tuple[MacroTemplate, ...],
    cache: dict[tuple[int, int], OccurrencePrefixReturn],
) -> tuple[OccurrencePrefixReturn | None, OccurrencePrefixReturn | None]:
    """Build ordered child returns at the parent's actual transported exponent."""
    macro = macros[parent_id]
    if not macro.ordered_children:
        return None, None
    if len(macro.ordered_children) != 2:
        raise AssertionError("future macro lost its ordered N/Z child pair")
    child_exponent = parent_exponent + macro.exponent_delta
    actions: list[OccurrencePrefixReturn] = []
    for child in macro.ordered_children:
        child_id = _state_id(child)
        if states[child_id] != child:
            raise AssertionError("macro child id disagrees with future state order")
        if child_exponent % PERIOD != child.exponent_residue:
            raise AssertionError("parent macro exponent lost child phase")
        key = (child_id, child_exponent)
        action = cache.get(key)
        if action is None:
            action = macro_c1_return_constructive(macros[child_id], child_exponent)
            cache[key] = action
        actions.append(action)
    if actions[0].terminal_low_suffix < 0 or actions[1].terminal_low_suffix < 0:
        raise AssertionError("constructive macro return has an invalid suffix")
    return actions[0], actions[1]


def build_constructive_future_graph() -> ConstructiveFutureGraph:
    """Build exact macro rows and child returns at transported occurrences.

    The finite graph and macro templates still come from the shared chart
    owner.  A child action is cached by both raw state and actual exponent, so
    a long transported exponent can never accidentally reuse a canonical
    representative action for the same residue.
    """
    states = tuple(
        BoundaryState(kind, a, residue)
        for kind in ("N", "Z")
        for a in range(2, 10)
        for residue in range(PERIOD)
    )
    macros = tuple(construct_macro(state, grouped_near=True) for state in states)
    transitions: list[tuple[int | None, int | None]] = []
    deltas: list[int] = []
    cache: dict[tuple[int, int], OccurrencePrefixReturn] = {}
    canonical_returns: list[OccurrencePrefixReturn] = []
    child_returns: list[
        tuple[OccurrencePrefixReturn | None, OccurrencePrefixReturn | None]
    ] = []

    for state_id, (state, macro) in enumerate(zip(states, macros, strict=True)):
        exponent = canonical_exponent(state.exponent_residue)
        action = macro_c1_return_constructive(macro, exponent)
        cache[(state_id, exponent)] = action
        canonical_returns.append(action)

    for state_id, (state, macro) in enumerate(zip(states, macros, strict=True)):
        if macro.source != state:
            raise AssertionError("constructive macro row changed its source")
        deltas.append(macro.exponent_delta)
        children = macro.ordered_children
        if not children:
            transitions.append((None, None))
        elif len(children) == 2 and children[0].kind == "N" and children[1].kind == "Z":
            transitions.append((_state_id(children[0]), _state_id(children[1])))
        else:
            raise AssertionError("constructive macro lost ordered N/Z children")
        child_returns.append(
            _macro_child_returns(
                state_id,
                canonical_exponent(state.exponent_residue),
                states,
                macros,
                cache,
            )
        )

    if len(transitions) != len(states) or len(child_returns) != len(states):
        raise AssertionError("constructive future graph is incomplete")
    graph = CommaFutureGraph(states, tuple(transitions), tuple(deltas))
    # Recheck every row against the finalized graph so provisional construction
    # data cannot escape into the audit result.
    for state_id, state in enumerate(states):
        children = macros[state_id].ordered_children
        expected: tuple[int | None, int | None]
        if not children:
            expected = (None, None)
        else:
            expected = (_state_id(children[0]), _state_id(children[1]))
        if graph.transitions[state_id] != expected:
            raise AssertionError("constructive transition row changed during build")
        child_exponent = (
            canonical_exponent(state.exponent_residue) + macros[state_id].exponent_delta
        )
        if child_exponent < 5 or any(
            child_exponent % PERIOD != child.exponent_residue for child in children
        ):
            raise AssertionError("transported child exponent fell below admission")
    return ConstructiveFutureGraph(
        graph,
        macros,
        tuple(canonical_returns),
        tuple(child_returns),
        len(canonical_returns),
    )


def macro_c1_return_constructive(
    macro: MacroTemplate, exponent: int, *, check_endpoint: bool = True
) -> OccurrencePrefixReturn:
    """Bind a chart-teacher prefix to one exact physical exponent occurrence."""
    source = BoundaryOccurrence(macro.source, exponent)
    return OccurrencePrefixReturn(source, macro, check_endpoint=check_endpoint)


def borrow_return_key_constructive(
    future: ConstructiveFutureGraph, state_id: int
) -> Hashable:
    """Observe child returns built from fragments at this parent's exponent."""
    graph = future.graph
    state = graph.states[state_id]
    base = (
        state.kind,
        state.a,
        state.exponent_residue % 9,
        state.exponent_residue % 22,
    )
    n_id, z_id = graph.transitions[state_id]
    n_return, z_return = future.child_returns[state_id]
    if n_id is None or z_id is None:
        if n_return is not None or z_return is not None:
            raise AssertionError("landmine row has unexpected child carry returns")
        return (*base, "dead")
    if n_return is None or z_return is None:
        raise AssertionError("fork row lost a constructive child carry return")
    if graph.states[n_id].kind != "N" or graph.states[z_id].kind != "Z":
        raise AssertionError("future row lost N/Z ordering")

    delta_x, zeta = _borrow_return_coordinates(n_return, z_return)
    return (*base, delta_x, zeta)


def _borrow_return_coordinates(
    n_return: OccurrencePrefixReturn, z_return: OccurrencePrefixReturn
) -> tuple[int, int]:
    delta_x = (z_return.terminal_low_suffix - n_return.terminal_low_suffix) % 100
    borrow_out = int(z_return.terminal_low_suffix < n_return.terminal_low_suffix)
    zeta = z_return.c1_count - n_return.c1_count + 1 - borrow_out
    return delta_x, zeta


def _constructive_key_at_parent_exponent(
    future: ConstructiveFutureGraph, state_id: int, parent_exponent: int
) -> tuple[Hashable, ...]:
    state = future.graph.states[state_id]
    if (
        type(parent_exponent) is not int
        or parent_exponent < 5
        or parent_exponent % PERIOD != state.exponent_residue
    ):
        raise ValueError("witness exponent is outside the represented boundary phase")
    base: tuple[Hashable, ...] = (
        state.kind,
        state.a,
        state.exponent_residue % 9,
        state.exponent_residue % 22,
    )
    n_id, z_id = future.graph.transitions[state_id]
    if n_id is None or z_id is None:
        return (*base, "dead")
    cache: dict[tuple[int, int], OccurrencePrefixReturn] = {}
    n_return, z_return = _macro_child_returns(
        state_id,
        parent_exponent,
        future.graph.states,
        future.macros,
        cache,
    )
    if n_return is None or z_return is None:
        raise AssertionError("transported witness lost its child returns")
    delta_x, zeta = _borrow_return_coordinates(n_return, z_return)
    return (*base, delta_x, zeta)


def transported_key_witness_constructive(
    future: ConstructiveFutureGraph,
) -> dict[str, object]:
    """Check the named exponent transport witness with fragment-built counts."""
    try:
        state_id = future.graph.states.index(BoundaryState("N", 2, 10))
    except ValueError as exc:
        raise AssertionError("transport witness state is absent") from exc
    canonical = canonical_exponent(10)
    transported = canonical + PERIOD
    key_canonical = _constructive_key_at_parent_exponent(future, state_id, canonical)
    key_transported = _constructive_key_at_parent_exponent(
        future, state_id, transported
    )
    zeta_canonical = key_canonical[-1]
    zeta_transported = key_transported[-1]
    if zeta_canonical != 999_800_000_000_000:
        raise AssertionError("canonical N(2,10) zeta witness changed")
    if zeta_transported != zeta_canonical * 10**PERIOD:
        raise AssertionError("N(2,10) transported zeta scaling changed")
    if key_canonical == key_transported:
        raise AssertionError("exact borrow key unexpectedly survived exponent shift")
    return {
        "state": "N(2,10)",
        "canonical_exponent": canonical,
        "transported_exponent": transported,
        "zeta_canonical": zeta_canonical,
        "zeta_transport_relation": f"zeta_{transported}=zeta_{canonical}*10**{PERIOD}",
        "exact_key_invariant": False,
        "all_exponent_transport_proved": False,
        "count_source": "powered C1Return sector fragments",
    }


def partition_from_keys(keys: tuple[Hashable, ...]) -> tuple[int, tuple[int, ...]]:
    ids: dict[Hashable, int] = {}
    class_ids: list[int] = []
    for key in keys:
        class_ids.append(ids.setdefault(key, len(ids)))
    return len(ids), tuple(class_ids)


def quotient_rows_from_partition(
    graph: CommaFutureGraph, class_ids: tuple[int, ...], classes: int
) -> tuple[tuple[int | None, int | None], ...]:
    rows: list[tuple[int | None, int | None] | None] = [None] * classes
    for state_id, cls in enumerate(class_ids):
        raw = graph.transitions[state_id]
        row_values = map_partition_row(raw, class_ids)
        if len(row_values) != 2:
            raise AssertionError("borrow graph lost its ordered child pair")
        row = (row_values[0], row_values[1])
        if rows[cls] is None:
            rows[cls] = row
        elif rows[cls] != row:
            raise AssertionError(
                f"borrow key is not right-congruent: class {cls}: {rows[cls]} != {row}"
            )
    if any(row is None for row in rows):
        raise AssertionError("borrow quotient lost class row")
    return tuple(row for row in rows if row is not None)


def quotient_fixed_point(
    rows: tuple[tuple[int | None, int | None], ...], class_ids: tuple[int, ...]
) -> tuple[int, int, tuple[int, ...]]:
    minimized = minimize_finite_observer(rows, tuple(0 for _ in rows))
    qrows = partition_quotient_rows(rows, minimized.class_ids, minimized.classes)
    if any(len(row) != 2 for row in qrows):
        raise AssertionError("Moore quotient lost its ordered fork slots")
    fixed = minimize_finite_observer(qrows, tuple(0 for _ in qrows))
    raw_moore = tuple(minimized.class_ids[cls] for cls in class_ids)
    return minimized.classes, fixed.classes, raw_moore


def greatest_live_fixed_point(graph: CommaFutureGraph) -> frozenset[int]:
    """Prune finite-dead states in O(V+E) using a reverse-edge queue."""
    size = len(graph.states)
    if len(graph.transitions) != size:
        raise ValueError("future transitions do not cover the graph")
    remaining = [0] * size
    reverse: list[list[int]] = [[] for _ in range(size)]
    for source, row in enumerate(graph.transitions):
        if len(row) != 2:
            raise ValueError("future row must contain ordered N/Z slots")
        for target in row:
            if target is None:
                continue
            if type(target) is not int or not 0 <= target < size:
                raise ValueError("future edge leaves the graph")
            remaining[source] += 1
            reverse[target].append(source)

    dead = [False] * size
    queue = deque(index for index, count in enumerate(remaining) if count == 0)
    while queue:
        child = queue.popleft()
        if dead[child]:
            continue
        dead[child] = True
        for predecessor in reverse[child]:
            if dead[predecessor]:
                continue
            remaining[predecessor] -= 1
            if remaining[predecessor] == 0:
                queue.append(predecessor)
    return frozenset(index for index, is_dead in enumerate(dead) if not is_dead)


def _pointed_vieta_audit_from_live(
    graph: CommaFutureGraph,
    live_set: frozenset[int],
) -> PointedAudit:
    if any(
        type(state) is not int or not 0 <= state < len(graph.states)
        for state in live_set
    ):
        raise ValueError("pointed audit live set leaves the graph")
    live = tuple(index for index in range(len(graph.states)) if index in live_set)
    losing = len(graph.states) - len(live)

    # Anonymous squarefree zero root + one pointed state per live occurrence.
    live_id = {raw: i + 1 for i, raw in enumerate(live)}
    rows: list[tuple[int, ...]] = [(0,)]
    outputs: list[Hashable] = ["dead"]
    successors: dict[int, tuple[str, int]] = {}
    n_count = 0
    z_count = 0
    for raw in live:
        n_child, z_child = graph.transitions[raw]
        selected: list[tuple[str, int]] = []
        if n_child is not None and n_child in live_set:
            selected.append(("N", n_child))
        if z_child is not None and z_child in live_set:
            selected.append(("Z", z_child))
        if len(selected) != 1:
            raise AssertionError(f"live state {raw} has {len(selected)} live children")
        label, child = selected[0]
        successors[raw] = label, child
        rows.append((live_id[child],))
        outputs.append(label)
        if label == "N":
            n_count += 1
        else:
            z_count += 1

    if live:
        cursor = live[0]
        visited: set[int] = set()
        cycle_exponent_gain = 0
        while cursor not in visited:
            visited.add(cursor)
            cycle_exponent_gain += graph.exponent_deltas[cursor]
            cursor = successors[cursor][1]
        if cursor != live[0] or len(visited) != len(live):
            raise AssertionError("pointed survivors are not one complete live cycle")
        if cycle_exponent_gain != 924:
            raise AssertionError(
                f"pointed live cycle exponent gain changed: {cycle_exponent_gain}"
            )
    elif successors:
        raise AssertionError("empty pointed survivor set has successors")
    else:
        cycle_exponent_gain = 0

    minimized = minimize_finite_observer(tuple(rows), tuple(outputs))
    members = class_members(minimized.class_ids, minimized.classes)
    qrows = closed_partition_quotient_rows(rows, minimized.class_ids, minimized.classes)
    qoutputs: list[Hashable] = []
    for group in members:
        representative_output = outputs[group[0]]
        if any(outputs[state] != representative_output for state in group[1:]):
            raise AssertionError("pointed quotient merged branch points")
        qoutputs.append(representative_output)
    fixed = minimize_finite_observer(tuple(qrows), tuple(qoutputs))
    return PointedAudit(
        raw_states=len(graph.states),
        losing_raw_states=losing,
        live_raw_states=len(live),
        pointed_states=len(rows),
        pointed_moore_classes=minimized.classes,
        pointed_moore_fixed_classes=fixed.classes,
        live_cycle_length=len(visited) if live else 0,
        live_cycle_exponent_gain=cycle_exponent_gain,
        live_branch_N=n_count,
        live_branch_Z=z_count,
    )


def _pointed_only_payload(graph: CommaFutureGraph) -> dict[str, object]:
    pointed = _pointed_vieta_audit_from_live(graph, greatest_live_fixed_point(graph))
    payload = asdict(pointed)
    payload.update(_audit_metadata(pointed_only=True))
    return payload


def pointed_vieta_audit(graph: CommaFutureGraph) -> PointedAudit:
    """Classify pointed states from the rank-free greatest-live fixed point."""
    return _pointed_vieta_audit_from_live(graph, greatest_live_fixed_point(graph))


def borrow_pointed_projection(
    graph: CommaFutureGraph,
    keys: tuple[Hashable, ...],
    class_ids: tuple[int, ...],
    live_set: frozenset[int],
) -> tuple[int, int, int, int]:
    """Check that borrow fibers project uniformly to dead/live Vieta roots."""
    if not (len(keys) == len(class_ids) == len(graph.states)):
        raise ValueError("borrow pointed projection inputs have different sizes")
    if any(
        type(state) is not int or not 0 <= state < len(graph.states)
        for state in live_set
    ):
        raise ValueError("borrow pointed live set leaves the graph")
    members = class_members(class_ids, max(class_ids, default=-1) + 1)

    losing_classes = 0
    live_classes = 0
    conflicts = 0
    live_nonsingleton_classes = 0
    for group in members:
        projections: set[tuple[object, ...]] = set()
        live_members = 0
        for state_id in group:
            if state_id not in live_set:
                projections.add(("dead",))
                continue
            live_members += 1
            n_child, z_child = graph.transitions[state_id]
            selected: list[tuple[str, int]] = []
            if n_child is not None and n_child in live_set:
                selected.append(("N", n_child))
            if z_child is not None and z_child in live_set:
                selected.append(("Z", z_child))
            if len(selected) != 1:
                raise AssertionError("live borrow member lacks a unique pointer")
            label, child = selected[0]
            projections.add(("live", label, keys[child]))
        if len(projections) != 1:
            conflicts += 1
        projection = next(iter(projections)) if projections else ()
        if projection == ("dead",):
            losing_classes += 1
        elif projection and projection[0] == "live":
            live_classes += 1
        if live_members > 1:
            live_nonsingleton_classes += 1
    return (
        losing_classes,
        live_classes,
        conflicts,
        live_nonsingleton_classes,
    )


def _assert_expected_counts(payload: dict[str, object], *, pointed_only: bool) -> None:
    """Keep supplied numerical claims as fail-closed finite-audit checks."""
    expected: dict[str, object] = {
        "raw_states": 14_784,
        "losing_raw_states": 14_470,
        "live_raw_states": 314,
        "pointed_states": 315,
        "pointed_moore_classes": 315,
        "pointed_moore_fixed_classes": 315,
        "live_cycle_length": 314,
        "live_cycle_exponent_gain": 924,
        "live_branch_N": 143,
        "live_branch_Z": 171,
    }
    if not pointed_only:
        expected.update(
            borrow_classes=10_027,
            borrow_right_congruent=True,
            borrow_moore_classes=3_279,
            borrow_moore_fixed_classes=3_279,
            t3279_classes=3_279,
            exact_t3279_partition_match=True,
            losing_borrow_classes=9_713,
            live_borrow_classes=314,
            pointed_projection_conflicts=0,
            live_borrow_nonsingleton_classes=0,
            transported_key_exact_invariant=False,
            transported_zeta_scale_matches=True,
            constructive_c1_rows=14_784,
            endpoint_differential_mismatches=0,
        )
    mismatches = {
        name: (payload.get(name), value)
        for name, value in expected.items()
        if payload.get(name) != value
    }
    if mismatches:
        raise AssertionError(f"reported finite audit counts changed: {mismatches}")


def _audit_metadata(*, pointed_only: bool) -> dict[str, object]:
    scope = dict(_AUDIT_SCOPE)
    if pointed_only:
        scope["macro_c1_count"] = "not evaluated in pointed-only mode"
        scope["macro_c1_runtime_used"] = False
    return {
        "audit_mode": (
            "constructive-pointed-only"
            if pointed_only
            else "constructive-borrow-and-pointed"
        ),
        "scope": scope,
        "pointed_interpretation": (
            "rank-free finite greatest-live audit, not a root derivation"
        ),
        "rank_labelled": False,
        "endpoint_derived_counts": False,
        "endpoint_role": (
            "not evaluated in pointed-only mode"
            if pointed_only
            else "post-hoc differential assertion only"
        ),
        "macro_teacher": (
            "comma_semantic_quotients.build_future_graph"
            if pointed_only
            else "boundary_quotient.construct_macro"
        ),
        "production_forest_deletion_claim": False,
        "representative_exponents_only": True,
        "transport_witness_run": not pointed_only,
        "all_exponent_transport_proved": False,
        "source_attachment_sha256": dict(_SOURCE_ARTIFACT_SHA256),
        "source_note": (
            "Downloaded scripts and patch are pinned by SHA-256; counts are "
            "finite audit assertions, not production identities."
        ),
    }


def run_audit(*, pointed_only: bool = False) -> dict[str, object]:
    if pointed_only:
        graph = build_future_graph()
        payload = _pointed_only_payload(graph)
        _assert_expected_counts(payload, pointed_only=True)
        return payload

    future = build_constructive_future_graph()
    graph = future.graph
    live_set = greatest_live_fixed_point(graph)

    keys = tuple(
        borrow_return_key_constructive(future, i) for i in range(len(graph.states))
    )
    borrow_classes, borrow_ids = partition_from_keys(keys)
    borrow_rows = quotient_rows_from_partition(graph, borrow_ids, borrow_classes)

    borrow_moore, borrow_fixed, raw_borrow_moore = quotient_fixed_point(
        borrow_rows, borrow_ids
    )

    t3279 = build_future_temporal_quotient(graph)
    exact_match = partition_equivalent(raw_borrow_moore, t3279.class_ids)

    live_raw = len(live_set)
    losing_raw = len(graph.states) - live_raw
    pointed = _pointed_vieta_audit_from_live(graph, live_set)
    if pointed.losing_raw_states != losing_raw or pointed.live_raw_states != live_raw:
        raise AssertionError("pointed Vieta and losing fixed point disagree")

    (
        losing_borrow_classes,
        live_borrow_classes,
        projection_conflicts,
        live_nonsingleton_classes,
    ) = borrow_pointed_projection(graph, keys, borrow_ids, live_set)
    if projection_conflicts != 0 or live_nonsingleton_classes != 0:
        raise AssertionError("borrow classes do not project to pointed roots")
    witness = transported_key_witness_constructive(future)

    audit = BorrowAudit(
        raw_states=len(graph.states),
        borrow_classes=borrow_classes,
        borrow_right_congruent=True,
        borrow_moore_classes=borrow_moore,
        borrow_moore_fixed_classes=borrow_fixed,
        t3279_classes=t3279.classes,
        exact_t3279_partition_match=exact_match,
        losing_raw_states=losing_raw,
        live_raw_states=live_raw,
        pointed_states=pointed.pointed_states,
        pointed_moore_classes=pointed.pointed_moore_classes,
        pointed_moore_fixed_classes=pointed.pointed_moore_fixed_classes,
        live_cycle_length=pointed.live_cycle_length,
        live_cycle_exponent_gain=pointed.live_cycle_exponent_gain,
        live_branch_N=pointed.live_branch_N,
        live_branch_Z=pointed.live_branch_Z,
        losing_borrow_classes=losing_borrow_classes,
        live_borrow_classes=live_borrow_classes,
        pointed_projection_conflicts=projection_conflicts,
        live_borrow_nonsingleton_classes=live_nonsingleton_classes,
        transported_key_exact_invariant=bool(witness["exact_key_invariant"]),
        transported_zeta_scale_matches=bool(
            witness["zeta_transport_relation"] == "zeta_934=zeta_10*10**924"
        ),
        constructive_c1_rows=future.constructive_c1_rows,
        endpoint_differential_mismatches=0,
    )
    payload = asdict(audit)
    payload["transported_key_witness"] = witness
    _assert_expected_counts(payload, pointed_only=False)
    payload.update(_audit_metadata(pointed_only=False))
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument(
        "--pointed-only",
        action="store_true",
        help="run only the rank-free pointed Vieta finite audit",
    )
    args = parser.parse_args()
    payload = run_audit(pointed_only=args.pointed_only)
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    from devtools.paths import report_output

    result_path = report_output(
        "devtools.verification.comma_borrow_vieta_audit",
        "audit.json",
    )
    result_path.write_text(rendered)
    print(rendered, end="")
    print(f"report: {result_path}")
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
