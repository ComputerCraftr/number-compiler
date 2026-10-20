"""Public operations for reduced CRT-clock return columns.

Columns are immutable MDD roots owned by the arithmetic in ``return_scopes``.
Call ``validate_return_mdd_partition`` once when publishing externally built
partitions; operations on producer-generated columns then use shallow handle
checks and preserve the reduced shape by construction.
"""

from __future__ import annotations

from collections.abc import Callable
from math import lcm
from typing import TypeAlias

from number_compiler.arithmetic.contracts.input_validation import is_runtime_instance
from number_compiler.sequences.comma.return_scopes import (
    CLOCK_COMPONENTS,
    COMPONENT_DOMAINS,
    FALSE_COLUMN,
    REMAINING_CLOCK_PERIODS,
    TRUE_COLUMN,
    VALID_MASKS,
    CanonicalReturnTemplate,
    ReturnColumnKey,
    ReturnMDDPartition,
    WorkCharge,
    mdd_child,
    mdd_intersection,
    mdd_union,
    scope_column_key,
    scopes_from_key,
    translated_column_key,
    validate_cached_partition_shape,
)

_SubstitutionState: TypeAlias = tuple[
    int, ReturnColumnKey, tuple[tuple[int, ReturnColumnKey], ...]
]


def _require_column(column: ReturnColumnKey) -> None:
    if type(column) is not ReturnColumnKey:
        raise TypeError("comma return-column operations require an exact MDD key")
    if column.kind not in (0, 1, 2):
        raise ValueError("invalid comma return-column node kind")


def translate_return_column(
    column: ReturnColumnKey,
    shift: int,
    *,
    charge: WorkCharge | None = None,
) -> ReturnColumnKey:
    """Rebase one validated CRT column by a phase shift modulo 924."""
    _require_column(column)
    if type(shift) is not int:
        raise TypeError("comma return-column shift must be an exact integer")
    return translated_column_key(column, shift % 924, charge)[0]


def translate_return_columns(
    columns: tuple[ReturnColumnKey, ...],
    shift: int,
    *,
    charge: WorkCharge,
    reserve_workspace: Callable[[int], None],
    release_workspace: Callable[[int], None],
) -> tuple[ReturnColumnKey, ...]:
    """Translate a column vector with one shared subgraph memo for its roots."""
    if type(columns) is not tuple:
        raise TypeError("comma return-column vector must be a tuple")
    if type(shift) is not int:
        raise TypeError("comma return-column shift must be an exact integer")
    for column in columns:
        _require_column(column)
    if (
        not callable(charge)
        or not callable(reserve_workspace)
        or not callable(release_workspace)
    ):
        raise TypeError("comma vector translation requires charged workspace callbacks")
    normalized_shift = shift % 924
    if normalized_shift == 0:
        return columns

    results: dict[tuple[int, ReturnColumnKey, int], ReturnColumnKey] = {}
    reserved = 0

    def reserve(nodes: int) -> None:
        nonlocal reserved
        reserve_workspace(nodes)
        reserved += nodes

    try:
        translated: list[ReturnColumnKey] = []
        for column in columns:
            result, _ = translated_column_key(
                column,
                normalized_shift,
                charge,
                results=results,
                reserve=reserve,
            )
            translated.append(result)
        return tuple(translated)
    except BaseException:
        if reserved:
            release_workspace(reserved)
        raise


def intersect_return_columns(
    left: ReturnColumnKey,
    right: ReturnColumnKey,
    *,
    charge: WorkCharge | None = None,
) -> ReturnColumnKey:
    """Intersect two reduced CRT columns on the admitted clock domain."""
    _require_column(left)
    _require_column(right)
    return mdd_intersection(left, right, 0, {}, charge)


def union_return_columns(
    left: ReturnColumnKey,
    right: ReturnColumnKey,
    *,
    charge: WorkCharge | None = None,
) -> ReturnColumnKey:
    """Union two reduced CRT columns on the admitted clock domain."""
    _require_column(left)
    _require_column(right)
    return mdd_union(left, right, 0, {}, charge)


def is_empty_return_column(column: ReturnColumnKey) -> bool:
    """Return whether a reduced CRT column has empty admitted support."""
    _require_column(column)
    return column == FALSE_COLUMN


def substitute_return_column(
    mask: ReturnColumnKey,
    continuation: tuple[tuple[int, ReturnColumnKey], ...],
    *,
    shift: int = 0,
    charge: WorkCharge,
    reserve_workspace: Callable[[int], None],
    release_workspace: Callable[[int], None],
) -> tuple[tuple[int, ReturnColumnKey], ...]:
    """Restrict a completed multi-output return by one left-side CRT column.

    The continuation columns are cofactered at ``digit + shift`` in lockstep
    with ``mask``. No translated continuation graph is constructed first. A
    reduced decision state therefore represents all output labels below that
    CRT prefix, avoiding a Cartesian product of left and right output columns.
    The iterative postorder memo and traversal frames are scoped scratch. They
    are released as soon as they die; constructed MDD nodes and the returned
    output payload remain reserved until the parent occurrence is published.
    """
    _require_column(mask)
    if type(shift) is not int:
        raise TypeError("comma substitution shift must be an exact integer")
    normalized_shift = shift % 924
    if type(continuation) is not tuple or not continuation:
        raise ValueError("comma return substitution needs a completed continuation")
    previous_label = -1
    for label, column in continuation:
        charge("comma_power_substitution_binding_checks", 1)
        if type(label) is not int or label < 0 or label <= previous_label:
            raise ValueError("comma continuation labels must be sorted and unique")
        _require_column(column)
        previous_label = label
    reserved_by_kind = {"memo": 0, "temporary": 0, "retained": 0}

    def account_workspace(kind: str, delta: int) -> None:
        if type(delta) is not int:
            raise TypeError("comma workspace reservation delta must be an int")
        current = reserved_by_kind[kind]
        if delta < 0:
            if -delta > current:
                raise ValueError("comma workspace release exceeds its reservation")
            release_workspace(-delta)
        elif delta > 0:
            reserve_workspace(delta)
        reserved_by_kind[kind] = current + delta

    def charge_state(amount: int = 1) -> None:
        charge("comma_power_substitution_states", amount)

    def child_state(state: _SubstitutionState, value: int) -> _SubstitutionState:
        level, left, right = state
        child_left = mdd_child(left, level, value)
        charge("comma_power_substitution_cofactors", 1)
        account_workspace("memo", 1)
        if child_left == FALSE_COLUMN:
            return level + 1, child_left, ()
        account_workspace("temporary", 1)
        child_right: list[tuple[int, ReturnColumnKey]] = []
        right_value = (value + normalized_shift) % COMPONENT_DOMAINS[level]
        for label, column in right:
            child_column = mdd_child(column, level, right_value)
            charge("comma_power_substitution_cofactors", 1)
            if child_column != FALSE_COLUMN:
                account_workspace("memo", 1)
                child_right.append((label, child_column))
        account_workspace("memo", 1)
        right_tuple = tuple(child_right)
        del child_right
        account_workspace("temporary", -1)
        account_workspace("memo", 1)
        return (
            level + 1,
            child_left,
            right_tuple,
        )

    def compose_children(
        state: _SubstitutionState,
        children: tuple[_SubstitutionState, ...],
        result_cache: dict[_SubstitutionState, tuple[tuple[int, ReturnColumnKey], ...]],
        *,
        retain_payload: bool,
    ) -> tuple[tuple[int, ReturnColumnKey], ...]:
        account_workspace("temporary", len(children))
        child_results = tuple(result_cache[child] for child in children)
        entry_count = sum(len(child) for child in child_results)
        account_workspace("temporary", len(child_results) + entry_count)
        child_maps = tuple(dict(child) for child in child_results)
        account_workspace("temporary", max(1, entry_count * 2))
        labels = tuple(sorted({label for child in child_results for label, _ in child}))
        account_workspace("temporary", 1)
        built: list[tuple[int, ReturnColumnKey]] = []
        for label in labels:
            first_child = child_maps[0].get(label, FALSE_COLUMN)
            if all(
                child.get(label, FALSE_COLUMN) == first_child
                for child in child_maps[1:]
            ):
                column = first_child
            else:
                account_workspace("retained", len(children) + 1)
                by_label = tuple(child.get(label, FALSE_COLUMN) for child in child_maps)
                column = ReturnColumnKey(2, state[0], by_label)
            account_workspace("retained" if retain_payload else "memo", 1)
            built.append((label, column))
        account_workspace("retained" if retain_payload else "memo", 1)
        return tuple(built)

    def push_child_frames(
        children: tuple[_SubstitutionState, ...],
        result_cache: dict[_SubstitutionState, tuple[tuple[int, ReturnColumnKey], ...]],
        frames: list[tuple[_SubstitutionState, tuple[_SubstitutionState, ...] | None]],
    ) -> None:
        for child in reversed(children):
            if child not in result_cache:
                account_workspace("temporary", 1)
                frames.append((child, None))

    try:
        account_workspace("memo", 1)
        initial: _SubstitutionState = (0, mask, continuation)
        account_workspace("temporary", 3)
        pending: list[
            tuple[_SubstitutionState, tuple[_SubstitutionState, ...] | None]
        ] = []
        results: dict[_SubstitutionState, tuple[tuple[int, ReturnColumnKey], ...]] = {}
        pending.append((initial, None))
        while pending:
            state, children = pending.pop()
            account_workspace("temporary", -1)
            if state in results:
                continue
            level, left, right = state
            if children is None:
                charge_state()
                if left == FALSE_COLUMN or not right:
                    account_workspace("memo", 1)
                    results[state] = ()
                    continue
                if left == TRUE_COLUMN and (
                    normalized_shift % REMAINING_CLOCK_PERIODS[level] == 0
                    or (len(right) == 1 and right[0][1].kind != 2)
                ):
                    if state is initial:
                        account_workspace("retained", 1 + len(right))
                    account_workspace("memo", 1)
                    results[state] = right
                    continue
                if level >= len(CLOCK_COMPONENTS):
                    raise ValueError("nonterminal comma column exceeds CRT clock")
                if left.kind == 2 and left.level < level:
                    raise ValueError("invalid comma left column during substitution")
                domain = COMPONENT_DOMAINS[level]
                account_workspace("temporary", domain)
                child_states = tuple(
                    child_state(state, value) for value in range(domain)
                )
                account_workspace("temporary", 1)
                pending.append((state, child_states))
                push_child_frames(child_states, results, pending)
                del child_states
                continue

            temporary_before = reserved_by_kind["temporary"]
            result = compose_children(
                state,
                children,
                results,
                retain_payload=state is initial,
            )
            account_workspace(
                "temporary", -(reserved_by_kind["temporary"] - temporary_before)
            )
            account_workspace("memo", 1)
            results[state] = result
            vector_size = len(children)
            children = None
            account_workspace("temporary", -vector_size)

        result = results[initial]
        pending.clear()
        results.clear()
        del pending, results
        account_workspace("temporary", -reserved_by_kind["temporary"])
        account_workspace("memo", -reserved_by_kind["memo"])
        return result
    except BaseException:
        reserved = sum(reserved_by_kind.values())
        if reserved:
            release_workspace(reserved)
            for kind in reserved_by_kind:
                reserved_by_kind[kind] = 0
        raise


def evaluate_return_column(
    column: ReturnColumnKey,
    phase: int,
    *,
    charge: WorkCharge | None = None,
) -> bool:
    """Evaluate one CRT column and charge the MDD nodes actually visited."""
    _require_column(column)
    if type(phase) is not int or not 0 <= phase < 924:
        raise ValueError("comma phase must be in 0..923")
    clock = (phase % 4, phase % 3, phase % 7, phase % 11)
    node = column
    previous_level = -1
    while node.kind == 2:
        if charge is not None:
            charge("comma_return_column_point_nodes", 1)
        level = node.level
        if type(level) is not int or not previous_level < level < len(CLOCK_COMPONENTS):
            raise ValueError("invalid comma return-column node level")
        if (
            type(node.children) is not tuple
            or len(node.children) != COMPONENT_DOMAINS[level]
        ):
            raise ValueError("invalid comma return-column child vector")
        previous_level = level
        node = node.children[clock[level]]
        if type(node) is not ReturnColumnKey:
            raise ValueError("invalid comma return-column child")
    if node.kind not in (0, 1):
        raise ValueError("invalid comma return-column terminal")
    if charge is not None:
        charge("comma_return_column_point_nodes", 1)
    return node.kind == 1


def _mdd_cardinality(
    root: ReturnColumnKey,
    charge: WorkCharge | None,
    memo: dict[tuple[int, ReturnColumnKey], int] | None = None,
) -> int:
    """Count admitted clock points from the reduced MDD without enumerating them."""
    pending: list[tuple[int, ReturnColumnKey, bool]] = [(0, root, False)]
    results: dict[tuple[int, ReturnColumnKey], int]
    results = {} if memo is None else memo
    while pending:
        level, key, ready = pending.pop()
        state = level, key
        if state in results:
            continue
        if charge is not None:
            charge("comma_output_template_cardinality_nodes", 1)
        if key == FALSE_COLUMN:
            results[state] = 0
            continue
        if level == len(CLOCK_COMPONENTS):
            results[state] = int(key == TRUE_COLUMN)
            continue
        if key == TRUE_COLUMN:
            remaining = 1
            for mask in VALID_MASKS[level:]:
                remaining *= mask.bit_count()
            results[state] = remaining
            continue
        valid_values = tuple(
            value
            for value in range(COMPONENT_DOMAINS[level])
            if VALID_MASKS[level] >> value & 1
        )
        child_states = tuple(
            (level + 1, mdd_child(key, level, value)) for value in valid_values
        )
        if ready:
            results[state] = sum(results[child] for child in child_states)
            continue
        pending.append((level, key, True))
        for child in reversed(child_states):
            if child not in results:
                pending.append((*child, False))
    return results[(0, root)]


def _canonical_rebase_records(
    records: tuple[tuple[int, ReturnColumnKey, int], ...],
    global_period: int,
    charge: WorkCharge | None,
    reserve_workspace: Callable[[int], None] | None,
) -> tuple[
    int,
    int,
    int,
    int,
    tuple[ReturnColumnKey, ...],
    tuple[tuple[ReturnColumnKey, int], ...],
]:
    if not records:
        raise ValueError("comma return partition must be nonempty")
    rarest_cardinality = min(record[0] for record in records)
    rarest_columns = tuple(
        record for record in records if record[0] == rarest_cardinality
    )
    rarest_covers = tuple(
        (key, scopes_from_key(key, charge)) for _, key, _ in rarest_columns
    )
    if any(not scopes for _, scopes in rarest_covers):
        raise ValueError("rarest comma output column has empty support")
    anchor_period = max(
        period for _, column_scopes in rarest_covers for period, _ in column_scopes
    )
    anchor_residues = {
        residue
        for _, column_scopes in rarest_covers
        for period, residue in column_scopes
        if period == anchor_period
    }
    global_period = lcm(global_period, anchor_period)
    candidates = tuple(
        sorted(
            {
                residue + multiple * anchor_period
                for residue in anchor_residues
                for multiple in range(global_period // anchor_period)
            }
        )
    )
    if not candidates:
        raise AssertionError("comma CRT anchor produced no candidate rebases")
    best_key: tuple[ReturnColumnKey, ...] | None = None
    best_encoded_columns: tuple[tuple[ReturnColumnKey, int], ...] | None = None
    best_shift = 0
    shifted_nodes = 0
    shifted_subnodes: dict[tuple[int, ReturnColumnKey, int], ReturnColumnKey] = {}
    for shift in candidates:
        if charge is not None:
            charge("comma_output_template_anchor_candidates", 1)
        shifted_columns: list[tuple[ReturnColumnKey, int]] = []
        for _, key, label in records:
            shifted_key, visits = translated_column_key(
                key,
                shift,
                charge,
                results=shifted_subnodes,
                reserve=reserve_workspace,
            )
            shifted_nodes += visits
            shifted_columns.append((shifted_key, label))
        columns = tuple(sorted(shifted_columns))
        column_key_tuple = tuple(column[0] for column in columns)
        if best_key is not None and charge is not None:
            charge("comma_output_template_partition_comparisons", len(column_key_tuple))
        if best_key is None or column_key_tuple < best_key:
            best_key = column_key_tuple
            best_encoded_columns = columns
            best_shift = shift
    if best_key is None or best_encoded_columns is None:
        raise AssertionError("comma CRT anchor normalization failed")
    return (
        best_shift,
        len(candidates),
        shifted_nodes,
        global_period,
        best_key,
        best_encoded_columns,
    )


def _canonical_template_from_records(
    records: tuple[tuple[int, ReturnColumnKey, int], ...],
    global_period: int,
    charge: WorkCharge | None,
    reserve_workspace: Callable[[int], None] | None,
) -> CanonicalReturnTemplate:
    (
        forward_shift,
        candidate_count,
        shifted_nodes,
        effective_period,
        columns,
        encoded,
    ) = _canonical_rebase_records(records, global_period, charge, reserve_workspace)
    return CanonicalReturnTemplate(
        effective_period,
        columns,
        tuple(label for _, label in encoded),
        (-forward_shift) % 924,
        candidate_count,
        shifted_nodes,
    )


def canonical_return_template(
    partition: ReturnMDDPartition,
    *,
    charge: WorkCharge | None = None,
    reserve_workspace: Callable[[int], None] | None = None,
    release_workspace: Callable[[int], None] | None = None,
) -> CanonicalReturnTemplate:
    """Build the scope-free common-shift template from completed MDD columns.

    This is the data-first constructor used by powered symbolic consumers. It
    returns only canonical MDD geometry, output labels, and occurrence clock
    transport; legacy scope predicates are constructed only by their explicit
    observer APIs.

    When workspace callbacks are supplied, the caller releases the accumulated
    reservation after it publishes or rejects this template.
    """
    if (reserve_workspace is None) != (release_workspace is None):
        raise ValueError("comma template workspace callbacks must be paired")
    if reserve_workspace is not None and (
        not callable(reserve_workspace) or not callable(release_workspace)
    ):
        raise TypeError("comma template workspace callbacks must be callable")
    if type(partition) is not ReturnMDDPartition:
        raise ValueError("invalid completed comma MDD partition")
    validate_cached_partition_shape(partition)
    records: list[tuple[int, ReturnColumnKey, int]] = []
    labels: set[int] = set()
    cardinality_memo: dict[tuple[int, ReturnColumnKey], int] = {}
    for label, key in partition.columns:
        if (
            type(label) is not int
            or label in labels
            or not is_runtime_instance(key, ReturnColumnKey)
        ):
            raise ValueError("invalid completed comma MDD column")
        labels.add(label)
        cardinality = _mdd_cardinality(key, charge, cardinality_memo)
        if cardinality == 0:
            raise ValueError("comma output column must have nonempty admitted support")
        records.append((cardinality, key, label))
    return _canonical_template_from_records(
        tuple(records), partition.period, charge, reserve_workspace
    )


def validate_return_column(column: ReturnColumnKey) -> ReturnColumnKey:
    """Validate one complete reduced MDD at an ownership/publication boundary."""
    _require_column(column)
    pending: list[tuple[int, ReturnColumnKey]] = [(0, column)]
    seen: set[int] = set()
    while pending:
        parent_level, node = pending.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        if (
            type(node.kind) is not int
            or type(node.level) is not int
            or type(node.children) is not tuple
        ):
            raise ValueError("malformed comma return-column node")
        if node.kind in (0, 1):
            if node.level != 0 or node.children:
                raise ValueError("malformed comma return-column terminal")
            continue
        if node.kind != 2 or not 0 <= node.level < len(CLOCK_COMPONENTS):
            raise ValueError("malformed comma return-column decision node")
        if (
            node.level < parent_level
            or len(node.children) != COMPONENT_DOMAINS[node.level]
        ):
            raise ValueError("invalid comma return-column decision shape")
        if all(child == node.children[0] for child in node.children[1:]):
            raise ValueError("comma return-column decision is not reduced")
        invalid_values = tuple(
            value
            for value in range(COMPONENT_DOMAINS[node.level])
            if not (VALID_MASKS[node.level] >> value & 1)
        )
        if any(node.children[value] != FALSE_COLUMN for value in invalid_values):
            raise ValueError("comma return column is nonempty outside the CRT domain")
        for child in node.children:
            if type(child) is not ReturnColumnKey:
                raise ValueError("comma return-column child is not an MDD key")
            if child.kind == 2 and child.level <= node.level:
                raise ValueError("comma return-column levels do not increase")
            pending.append((node.level + 1, child))
    return column


def validate_return_mdd_partition(
    partition: ReturnMDDPartition,
    *,
    charge: WorkCharge | None = None,
) -> ReturnMDDPartition:
    """Check a complete, disjoint partition and its conservative period once."""
    if (
        type(partition) is not ReturnMDDPartition
        or type(partition.period) is not int
        or partition.period <= 0
        or 924 % partition.period
        or type(partition.columns) is not tuple
        or not partition.columns
    ):
        raise ValueError("invalid completed comma MDD partition")
    labels: set[int] = set()
    covered = FALSE_COLUMN
    for label, column in partition.columns:
        if type(label) is not int or label < 0 or label in labels:
            raise ValueError("comma partition labels must be distinct nonnegative ints")
        labels.add(label)
        validate_return_column(column)
        if is_empty_return_column(column):
            raise ValueError("comma return partition contains an empty column")
        overlap = mdd_intersection(covered, column, 0, {}, charge)
        if overlap != FALSE_COLUMN:
            raise ValueError("comma return partition columns overlap")
        covered = mdd_union(covered, column, 0, {}, charge)
        if translate_return_column(column, partition.period, charge=charge) != column:
            raise ValueError("comma return partition period is not conservative")
    if covered != scope_column_key(((1, 0),)):
        raise ValueError("comma return partition does not cover the CRT clock")
    return partition


__all__ = [
    "_mdd_cardinality",
    "canonical_return_template",
    "evaluate_return_column",
    "intersect_return_columns",
    "is_empty_return_column",
    "substitute_return_column",
    "translate_return_column",
    "translate_return_columns",
    "union_return_columns",
    "validate_return_column",
    "validate_return_mdd_partition",
]
