"""Exact CRT-cylinder returns for the comma continuation DAG.

The semantic continuation owner already stores local-period actions.  This
module composes those rows as congruence scopes; it never samples a 924-value
return row.  Output labels stay beside, and outside, the unlabeled geometry.
"""

from __future__ import annotations

from collections.abc import Callable, MutableMapping
from dataclasses import dataclass, field
from math import gcd, lcm, prod
from typing import TypeAlias

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
    is_object_tuple,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.sequences.comma.domain import canonical_offset_orbit
from number_compiler.sequences.comma.semantic_continuation import (
    ContinuationID,
    SemanticAction,
    SemanticContinuation,
)

ReturnScope: TypeAlias = tuple[int, int]
ReturnColumn: TypeAlias = tuple[int, tuple[ReturnScope, ...]]
WorkCharge: TypeAlias = Callable[[str, int], None]
_Cube: TypeAlias = tuple[int, ...]

CLOCK_COMPONENTS = (("r4", 4), ("r3", 3), ("r7", 7), ("r11", 11))
COMPONENT_DOMAINS = (4, 3, 7, 11)
VALID_MASKS = tuple((1 << domain) - 1 for domain in COMPONENT_DOMAINS)
_COMPONENT_MODULI = (4, 3, 7, 11)
REMAINING_CLOCK_PERIODS = tuple(
    prod(_COMPONENT_MODULI[level:]) for level in range(len(_COMPONENT_MODULI) + 1)
)


@dataclass(frozen=True, slots=True, order=True)
class ReturnColumnKey:
    """An ordered structural key for one reduced CRT decision node."""

    kind: int
    level: int = 0
    children: tuple[ReturnColumnKey, ...] = ()
    _cached_hash: int = field(init=False, repr=False, compare=False, hash=False)

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "_cached_hash",
            hash((self.kind, self.level, self.children)),
        )

    def __hash__(self) -> int:
        return self._cached_hash


FALSE_COLUMN = ReturnColumnKey(0)
TRUE_COLUMN = ReturnColumnKey(1)
_ALLOWED_CYLINDER_MASKS = (
    (0b1111, 0b0101, 0b1010, 0b0001, 0b0010, 0b0100, 0b1000),
    (0b111, 0b001, 0b010, 0b100),
    (0b1111111, *(1 << value for value in range(7))),
    (0b11111111111, *(1 << value for value in range(11))),
)


@dataclass(frozen=True, slots=True)
class ReturnMDDPartition:
    """Completed continuation outputs kept as reduced exact CRT columns."""

    period: int
    columns: tuple[tuple[int, ReturnColumnKey], ...]


@dataclass(frozen=True, slots=True)
class CanonicalReturnTemplate:
    """Scope-free quotient plus the occurrence data needed to reconstruct it.

    ``columns`` is the unlabeled, common-clock canonical geometry. ``labels``
    is the parallel output binding, and ``return_shift`` is the input-clock
    shift to apply to this canonical geometry for the original occurrence.
    No scope predicates or semantic-function nodes are constructed here.
    """

    period: int
    columns: tuple[ReturnColumnKey, ...]
    labels: tuple[int, ...]
    return_shift: int
    candidate_count: int
    shifted_nodes: int


_B1_PARTITION_SEAL = object()


@dataclass(frozen=True, slots=True, init=False)
class B1ReturnPartitionRecord:
    """Cache authority binding a completed B1 partition to its CID owner."""

    partition: ReturnMDDPartition
    owner: ArenaToken
    source_id: ContinuationID
    seal: object

    def __init__(
        self,
        partition: ReturnMDDPartition,
        owner: ArenaToken,
        source_id: ContinuationID,
        *,
        _authority: object,
    ) -> None:
        if _authority is not _B1_PARTITION_SEAL:
            raise ValueError("B1 return partition records are producer-owned")
        if (
            type(partition) is not ReturnMDDPartition
            or type(owner) is not ArenaToken
            or type(source_id) is not ContinuationID
            or source_id.owner is not owner
        ):
            raise ValueError("B1 partition publication has mismatched ownership")
        validate_cached_partition_shape(partition)
        object.__setattr__(self, "partition", partition)
        object.__setattr__(self, "owner", owner)
        object.__setattr__(self, "source_id", source_id)
        object.__setattr__(self, "seal", _B1_PARTITION_SEAL)


def _owned_b1_partition(
    partition: ReturnMDDPartition,
    owner: ArenaToken,
    source_id: ContinuationID,
) -> B1ReturnPartitionRecord:
    return B1ReturnPartitionRecord(
        partition,
        owner,
        source_id,
        _authority=_B1_PARTITION_SEAL,
    )


def _cached_b1_partition(
    source_view: SemanticContinuation,
    source_id: ContinuationID,
    value: object,
) -> ReturnMDDPartition:
    """Check cache provenance in constant time; producer owns shape validity."""
    if (
        type(value) is not B1ReturnPartitionRecord
        or value.seal is not _B1_PARTITION_SEAL
        or value.owner is not source_view.owner
        or value.source_id != source_id
        or type(value.partition) is not ReturnMDDPartition
    ):
        raise ValueError("comma return partition cache entry has foreign authority")
    validate_cached_partition_shape(value.partition)
    return value.partition


def return_code(action: SemanticAction) -> int:
    if action.kind == "stop" and action.stop_j is not None:
        return action.stop_j
    if action.kind == "live" and action.live_root is not None:
        return 9 + canonical_offset_orbit(action.live_root)
    raise ValueError("complete return partition requires terminal or Live actions")


def return_partition_node_cost(
    _identifier: object,
    value: ReturnMDDPartition | B1ReturnPartitionRecord,
) -> int:
    """Count logical container/MDD nodes, not bytes or scalar leaf payloads.

    ``OwnedMemo`` adds one node for its key-to-cost index. Integer labels,
    periods, handles, and Python object headers are payload fields rather than
    nodes in this ledger dimension; the process memory guard remains the byte
    limit authority.
    """
    if type(value) is B1ReturnPartitionRecord:
        partition = value.partition
        extra_records = 1
    elif type(value) is ReturnMDDPartition:
        partition = value
        extra_records = 0
    else:
        raise TypeError("comma partition memo requires a typed partition")
    pending: list[object] = [partition]
    seen: set[int] = set()
    while pending:
        current = pending.pop()
        if id(current) in seen:
            continue
        if isinstance(current, ReturnMDDPartition):
            seen.add(id(current))
            pending.append(current.columns)
        elif is_object_tuple(current):
            seen.add(id(current))
            pending.extend(current)
        elif isinstance(current, ReturnColumnKey):
            seen.add(id(current))
            pending.append(current.children)
    return len(seen) + extra_records


def return_template_node_cost(
    key: tuple[ReturnColumnKey, ...], _function: object
) -> int:
    """Count the key graph retained by the output-template interner."""
    pending: list[object] = [key]
    seen: set[int] = set()
    while pending:
        current = pending.pop()
        if id(current) in seen:
            continue
        if is_exact_object_tuple(current):
            seen.add(id(current))
            pending.extend(current)
        elif isinstance(current, ReturnColumnKey):
            seen.add(id(current))
            pending.append(current.children)
    return len(seen)


def crt_meet(left: ReturnScope, right: ReturnScope) -> ReturnScope | None:
    """Intersect two normalized congruence cylinders by the generalized CRT."""
    left_period, left_residue = _validate_scope(left)
    right_period, right_residue = _validate_scope(right)
    common = gcd(left_period, right_period)
    difference = right_residue - left_residue
    if difference % common:
        return None
    reduced_right = right_period // common
    multiplier = (
        0
        if reduced_right == 1
        else (difference // common)
        * pow(left_period // common, -1, reduced_right)
        % reduced_right
    )
    period = lcm(left_period, right_period)
    residue = (left_residue + left_period * multiplier) % period
    return period, residue


def _validate_scope(scope: ReturnScope) -> ReturnScope:
    if (
        type(scope) is not tuple
        or len(scope) != 2
        or type(scope[0]) is not int
        or type(scope[1]) is not int
        or scope[0] <= 0
        or 924 % scope[0]
        or not 0 <= scope[1] < scope[0]
    ):
        raise ValueError("comma return scope must be a normalized divisor of 924")
    return scope


def validate_scopes(scopes: tuple[ReturnScope, ...]) -> tuple[ReturnScope, ...]:
    if type(scopes) is not tuple:
        raise TypeError("comma scope union must be an immutable tuple")
    return tuple(_validate_scope(scope) for scope in scopes)


def _scope_cube(scope: ReturnScope) -> _Cube:
    _validate_scope(scope)
    period, residue = scope
    factors: list[int] = []
    if period % 4 == 0:
        factors.append(4)
    elif period % 2 == 0:
        factors.append(2)
    else:
        factors.append(1)
    for component_modulus in (3, 7, 11):
        factors.append(component_modulus if period % component_modulus == 0 else 1)
    masks: list[int] = []
    for factor, valid_mask, domain in zip(
        factors,
        VALID_MASKS,
        COMPONENT_DOMAINS,
        strict=True,
    ):
        if factor == 1:
            masks.append(valid_mask)
        else:
            target = residue % factor
            masks.append(
                sum(
                    1 << value
                    for value in range(domain)
                    if valid_mask >> value & 1 and value % factor == target
                )
            )
    return tuple(masks)


def _minimal_cubes(cubes: tuple[_Cube, ...]) -> tuple[_Cube, ...]:
    unique = tuple(sorted(set(cubes)))
    return tuple(
        cube
        for cube in unique
        if not any(
            other != cube
            and all(
                mask & parent == mask for mask, parent in zip(cube, other, strict=True)
            )
            for other in unique
        )
    )


def scope_column_key(
    scopes: tuple[ReturnScope, ...], *, charge: WorkCharge | None = None
) -> ReturnColumnKey:
    """Canonical reduced multiway decision key for one scope union."""
    scopes = validate_scopes(scopes)
    cubes = _minimal_cubes(tuple(_scope_cube(scope) for scope in scopes))
    pending: list[tuple[int, tuple[_Cube, ...], bool]] = [(0, cubes, False)]
    results: dict[tuple[int, tuple[_Cube, ...]], ReturnColumnKey] = {}
    while pending:
        level, active, ready = pending.pop()
        if charge is not None:
            charge("comma_output_template_mdd_nodes", 1)
        state = (level, active)
        if state in results:
            continue
        if not active:
            results[state] = FALSE_COLUMN
            continue
        if level == len(CLOCK_COMPONENTS):
            results[state] = TRUE_COLUMN
            continue
        domain = COMPONENT_DOMAINS[level]
        child_cubes = tuple(
            _minimal_cubes(tuple(cube[1:] for cube in active if cube[0] >> value & 1))
            for value in range(domain)
        )
        child_states = tuple((level + 1, item) for item in child_cubes)
        if ready:
            children = tuple(results[item] for item in child_states)
            results[state] = (
                children[0]
                if all(child == children[0] for child in children)
                else ReturnColumnKey(2, level, children)
            )
            continue
        pending.append((level, active, True))
        for child_level, child in reversed(child_states):
            if (child_level, child) not in results:
                pending.append((child_level, child, False))
    return results[(0, cubes)]


def mdd_child(key: ReturnColumnKey, level: int, value: int) -> ReturnColumnKey:
    if key.kind in (0, 1):
        return key
    if key.kind != 2:
        raise ValueError("invalid comma clock MDD node kind")
    node_level = key.level
    if not 0 <= node_level < len(CLOCK_COMPONENTS):
        raise ValueError("invalid comma clock MDD node")
    if node_level > level:
        return key
    if node_level < level:
        raise ValueError("comma clock MDD node precedes its cofactor level")
    children = key.children
    if not 0 <= value < len(children):
        raise ValueError("invalid comma clock MDD child vector")
    return children[value]


def translated_column_key(
    root: ReturnColumnKey,
    shift: int,
    charge: WorkCharge | None,
    *,
    results: MutableMapping[tuple[int, ReturnColumnKey, int], ReturnColumnKey]
    | None = None,
    reserve: Callable[[int], None] | None = None,
) -> tuple[ReturnColumnKey, int]:
    """Translate a column by shifting its CRT characters in the reduced MDD."""
    if reserve is not None:
        reserve(1)
    pending: list[tuple[int, ReturnColumnKey, bool]] = [(0, root, False)]
    memo: MutableMapping[tuple[int, ReturnColumnKey, int], ReturnColumnKey] = (
        {} if results is None else results
    )
    visits = 0
    while pending:
        level, key, ready = pending.pop()
        state = level, key, shift % REMAINING_CLOCK_PERIODS[level]
        if state in memo:
            if charge is not None:
                charge("comma_output_template_mdd_shift_cache_hits", 1)
            continue
        if charge is not None:
            charge("comma_output_template_mdd_shift_nodes", 1)
        if reserve is not None:
            reserve(1)
        visits += 1
        if key.kind in (0, 1) or level == len(CLOCK_COMPONENTS):
            memo[state] = key
            continue
        if key.kind != 2 or key.level < level:
            raise ValueError("invalid comma clock MDD during translation")
        if key.level > level:
            next_level = level + 1
            next_state = (
                next_level,
                key,
                shift % REMAINING_CLOCK_PERIODS[next_level],
            )
            if ready:
                memo[state] = memo[next_state]
            else:
                if reserve is not None:
                    reserve(1)
                pending.append((level, key, True))
                if next_state not in memo:
                    if reserve is not None:
                        reserve(1)
                    pending.append((next_level, key, False))
            continue

        modulus = _COMPONENT_MODULI[level]
        domain = COMPONENT_DOMAINS[level]
        valid_values = tuple(
            value for value in range(domain) if VALID_MASKS[level] >> value & 1
        )
        old_values = tuple((value + shift) % modulus for value in valid_values)
        if reserve is not None:
            reserve(len(valid_values))
        child_states = tuple(
            (
                level + 1,
                mdd_child(key, level, old_value),
                shift % REMAINING_CLOCK_PERIODS[level + 1],
            )
            for old_value in old_values
        )
        if ready:
            if reserve is not None:
                reserve(domain)
            translated_children = {
                new_value: memo[child_state]
                for new_value, child_state in zip(
                    valid_values, child_states, strict=True
                )
            }
            first_child = translated_children.get(0, FALSE_COLUMN)
            if all(
                translated_children.get(value, FALSE_COLUMN) == first_child
                for value in range(domain)
            ):
                memo[state] = first_child
            else:
                if reserve is not None:
                    reserve(1)
                children = tuple(
                    translated_children.get(value, FALSE_COLUMN)
                    for value in range(domain)
                )
                memo[state] = ReturnColumnKey(2, level, children)
            continue

        if reserve is not None:
            reserve(1)
        pending.append((level, key, True))
        for child_level, child_key, _child_shift in reversed(child_states):
            child_state = child_level, child_key, _child_shift
            if child_state not in memo:
                if reserve is not None:
                    reserve(1)
                pending.append((child_level, child_key, False))
    return memo[(0, root, shift % REMAINING_CLOCK_PERIODS[0])], visits


def _mdd_pair(
    left: ReturnColumnKey, right: ReturnColumnKey
) -> tuple[ReturnColumnKey, ReturnColumnKey]:
    """Order a commutative memo key without comparing whole trees normally."""
    a, b = hash(left), hash(right)
    return (left, right) if a < b or (a == b and left <= right) else (right, left)


def _mdd_boolean_combine(
    left: ReturnColumnKey,
    right: ReturnColumnKey,
    level: int,
    cache: dict[tuple[int, ReturnColumnKey, ReturnColumnKey], ReturnColumnKey],
    charge: Callable[[str, int], None] | None,
    *,
    union: bool,
) -> ReturnColumnKey:
    pending = [(level, left, right, False)]
    while pending:
        current_level, first, second, ready = pending.pop()
        first, second = _mdd_pair(first, second)
        state = current_level, first, second
        if state in cache:
            continue
        if charge is not None:
            operation = "union" if union else "intersection"
            charge(f"comma_output_template_mdd_{operation}_nodes", 1)
        if union:
            if first == TRUE_COLUMN or second == TRUE_COLUMN:
                cache[state] = TRUE_COLUMN
                continue
            if first == FALSE_COLUMN:
                cache[state] = second
                continue
            if second == FALSE_COLUMN:
                cache[state] = first
                continue
        else:
            if first == FALSE_COLUMN or second == FALSE_COLUMN:
                cache[state] = FALSE_COLUMN
                continue
            if first == TRUE_COLUMN:
                cache[state] = second
                continue
            if second == TRUE_COLUMN:
                cache[state] = first
                continue
        if first == second:
            cache[state] = first
            continue
        if current_level == len(CLOCK_COMPONENTS):
            cache[state] = TRUE_COLUMN if union else FALSE_COLUMN
            continue
        domain = COMPONENT_DOMAINS[current_level]
        child_pairs = tuple(
            (
                mdd_child(first, current_level, value),
                mdd_child(second, current_level, value),
            )
            for value in range(domain)
        )
        child_states = tuple(
            (current_level + 1, *_mdd_pair(a, b)) for a, b in child_pairs
        )
        if ready:
            children = tuple(cache[child] for child in child_states)
            cache[state] = (
                children[0]
                if all(child == children[0] for child in children)
                else ReturnColumnKey(2, current_level, children)
            )
            continue
        pending.append((current_level, first, second, True))
        for child_level, child_first, child_second in reversed(child_states):
            child_state = child_level, child_first, child_second
            if child_state not in cache:
                pending.append((child_level, child_first, child_second, False))
    normalized = (level, *_mdd_pair(left, right))
    return cache[normalized]


def mdd_intersection(
    left: ReturnColumnKey,
    right: ReturnColumnKey,
    level: int,
    cache: dict[tuple[int, ReturnColumnKey, ReturnColumnKey], ReturnColumnKey],
    charge: WorkCharge | None,
) -> ReturnColumnKey:
    return _mdd_boolean_combine(left, right, level, cache, charge, union=False)


def mdd_union(
    left: ReturnColumnKey,
    right: ReturnColumnKey,
    level: int,
    cache: dict[tuple[int, ReturnColumnKey, ReturnColumnKey], ReturnColumnKey],
    charge: WorkCharge | None,
) -> ReturnColumnKey:
    return _mdd_boolean_combine(left, right, level, cache, charge, union=True)


def validate_cached_partition_shape(partition: ReturnMDDPartition) -> None:
    """Check constant-size period metadata on a sealed B1 cache hit."""
    if (
        type(partition.period) is not int
        or partition.period <= 0
        or 924 % partition.period
        or type(partition.columns) is not tuple
        or not partition.columns
    ):
        raise ValueError("invalid sealed comma return partition shape")


def _scope_mdd_key(
    scope: ReturnScope,
    cache: dict[ReturnScope, ReturnColumnKey],
    charge: WorkCharge | None,
) -> ReturnColumnKey:
    found = cache.get(scope)
    if found is not None:
        if charge is not None:
            charge("comma_return_partition_selector_cache_hits", 1)
        return found
    cube = _scope_cube(scope)
    key = TRUE_COLUMN
    for level in reversed(range(len(CLOCK_COMPONENTS))):
        children = tuple(
            key if cube[level] >> value & 1 else FALSE_COLUMN
            for value in range(COMPONENT_DOMAINS[level])
        )
        key = (
            children[0]
            if all(child == children[0] for child in children)
            else ReturnColumnKey(2, level, children)
        )
        if charge is not None:
            charge("comma_return_partition_selector_nodes", 1)
    cache[scope] = key
    return key


def _maximal_cylinder_cubes(
    root: ReturnColumnKey,
    charge: WorkCharge | None,
) -> tuple[_Cube, ...]:
    """Extract maximal subgroup-coset product cubes from an extensional MDD."""
    intersection_cache: dict[
        tuple[int, ReturnColumnKey, ReturnColumnKey], ReturnColumnKey
    ] = {}
    pending: list[tuple[int, ReturnColumnKey, bool]] = [(0, root, False)]
    options_by_state: dict[
        tuple[int, ReturnColumnKey], tuple[tuple[int, ReturnColumnKey], ...]
    ] = {}
    results: dict[tuple[int, ReturnColumnKey], tuple[_Cube, ...]] = {}
    while pending:
        level, function, ready = pending.pop()
        state = level, function
        if state in results:
            continue
        if level == len(CLOCK_COMPONENTS):
            results[state] = ((),) if function == TRUE_COLUMN else ()
            continue
        if ready:
            candidates = tuple(
                (mask, *suffix)
                for mask, child in options_by_state[state]
                for suffix in results[(level + 1, child)]
            )
            unique = set(candidates)
            maximal_cubes: list[_Cube] = []
            comparisons = 0
            for cube in sorted(unique):
                contained = False
                for other in unique:
                    comparisons += 1
                    if cube != other and all(
                        mask & parent == mask
                        for mask, parent in zip(cube, other, strict=True)
                    ):
                        contained = True
                        break
                if not contained:
                    maximal_cubes.append(cube)
            if charge is not None:
                charge("comma_output_template_cylinder_dominance_checks", comparisons)
            results[state] = tuple(maximal_cubes)
            continue
        choices: list[tuple[int, ReturnColumnKey]] = []
        domain = COMPONENT_DOMAINS[level]
        for mask in _ALLOWED_CYLINDER_MASKS[level]:
            common = TRUE_COLUMN
            for value in range(domain):
                if mask >> value & 1:
                    common = mdd_intersection(
                        common,
                        mdd_child(function, level, value),
                        level + 1,
                        intersection_cache,
                        charge,
                    )
                    if common == FALSE_COLUMN:
                        break
            if common != FALSE_COLUMN:
                choices.append((mask, common))
        options = tuple(choices)
        options_by_state[state] = options
        pending.append((level, function, True))
        for child in reversed(tuple((level + 1, key) for _, key in options)):
            if child not in results:
                pending.append((*child, False))
    return results[(0, root)]


def _cube_scope(cube: _Cube) -> ReturnScope:
    factors: list[tuple[int, int]] = []
    for level, (mask, valid_mask, domain, modulus) in enumerate(
        zip(
            cube,
            VALID_MASKS,
            COMPONENT_DOMAINS,
            (4, 3, 7, 11),
            strict=True,
        )
    ):
        if mask == valid_mask:
            factors.append((1, 0))
        elif level == 0 and mask in (0b0101, 0b1010):
            factors.append((2, 0 if mask == 0b0101 else 1))
        else:
            values = tuple(value for value in range(domain) if mask >> value & 1)
            if len(values) != 1:
                raise ValueError("comma maximal cylinder has an unsupported axis mask")
            factors.append((modulus, values[0]))
    scope = (1, 0)
    for factor in factors:
        merged = crt_meet(scope, factor)
        if merged is None:
            raise AssertionError("comma cylinder factor intersection is empty")
        scope = merged
    return scope


def scopes_from_key(
    key: ReturnColumnKey, charge: WorkCharge | None
) -> tuple[ReturnScope, ...]:
    cubes = _maximal_cylinder_cubes(key, charge)
    if charge is not None:
        charge("comma_output_template_scope_reconstruction", len(cubes))
    return tuple(sorted({_cube_scope(cube) for cube in cubes}))


def continuation_return_partition(
    source_view: SemanticContinuation,
    identifier: ContinuationID,
    cache: MutableMapping[ContinuationID, B1ReturnPartitionRecord],
    *,
    charge: WorkCharge | None = None,
) -> ReturnMDDPartition:
    """Compose one complete return directly in the reduced CRT-MDD algebra."""
    if charge is not None:
        charge("comma_return_partition_lookups", 1)
    source_view.validate_id(identifier)
    found = cache.get(identifier)
    if found is not None:
        if charge is not None:
            charge("comma_return_partition_cache_hits", 1)
        return _cached_b1_partition(source_view, identifier, found)
    if charge is not None:
        charge("comma_return_partition_cache_misses", 1)
    pending: list[tuple[ContinuationID, bool]] = [(identifier, False)]
    active: set[ContinuationID] = set()
    while pending:
        current, ready = pending.pop()
        if charge is not None:
            charge("comma_return_partition_worklist_visits", 1)
        if current in cache:
            _cached_b1_partition(source_view, current, cache[current])
            active.discard(current)
            continue
        rows = source_view.actions_by_id.get(source_view.validate_id(current))
        if rows is None or not rows:
            raise ValueError("comma continuation has no local action row")
        if ready:
            by_label: dict[int, ReturnColumnKey] = {}
            selector_cache: dict[ReturnScope, ReturnColumnKey] = {}
            intersection_cache: dict[
                tuple[int, ReturnColumnKey, ReturnColumnKey], ReturnColumnKey
            ] = {}
            union_cache: dict[
                tuple[int, ReturnColumnKey, ReturnColumnKey], ReturnColumnKey
            ] = {}
            row_period = len(rows)
            if 924 % row_period:
                raise ValueError("comma local action period does not divide 924")
            result_period = row_period
            for residue, action in enumerate(rows):
                if charge is not None:
                    charge("comma_return_partition_action_visits", 1)
                local_scope = (row_period, residue)
                selector = _scope_mdd_key(local_scope, selector_cache, charge)
                if action.kind == "goto":
                    if action.target is None:
                        raise ValueError("comma Goto omits its child ID")
                    target = source_view.validate_id(action.target)
                    child_entry = cache.get(target)
                    if child_entry is None:
                        raise AssertionError("comma child partition was not completed")
                    child = _cached_b1_partition(source_view, target, child_entry)
                    result_period = lcm(result_period, child.period)
                    for label, child_key in child.columns:
                        if charge is not None:
                            charge("comma_return_partition_mdd_meets", 1)
                        overlap = mdd_intersection(
                            selector,
                            child_key,
                            0,
                            intersection_cache,
                            charge,
                        )
                        if overlap != FALSE_COLUMN:
                            previous = by_label.get(label, FALSE_COLUMN)
                            by_label[label] = mdd_union(
                                previous,
                                overlap,
                                0,
                                union_cache,
                                charge,
                            )
                else:
                    label = return_code(action)
                    previous = by_label.get(label, FALSE_COLUMN)
                    by_label[label] = mdd_union(
                        previous,
                        selector,
                        0,
                        union_cache,
                        charge,
                    )
            result = ReturnMDDPartition(
                result_period,
                tuple(sorted(by_label.items())),
            )
            cache[current] = _owned_b1_partition(
                result,
                source_view.owner,
                current,
            )
            active.discard(current)
            continue
        if current in active:
            raise ValueError("comma continuation graph contains a cycle")
        active.add(current)
        pending.append((current, True))
        targets = tuple(
            source_view.validate_id(action.target)
            for action in rows
            if action.kind == "goto" and action.target is not None
        )
        for target in reversed(targets):
            if target in active:
                raise ValueError("comma continuation graph contains a cycle")
            if target not in cache:
                pending.append((target, False))
    published = cache.get(identifier)
    if published is None:
        raise AssertionError("comma continuation partition was not published")
    return _cached_b1_partition(source_view, identifier, published)


__all__ = [
    "B1ReturnPartitionRecord",
    "CanonicalReturnTemplate",
    "ReturnColumn",
    "ReturnColumnKey",
    "ReturnMDDPartition",
    "ReturnScope",
    "continuation_return_partition",
    "crt_meet",
    "return_code",
    "return_partition_node_cost",
    "return_template_node_cost",
    "scope_column_key",
]
