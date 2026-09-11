"""Shared symmetry-aware finite-action and binary-power machinery.

The engine is intentionally family-neutral.  A directed digit/carry kernel is
specified by its finite state transition and (optionally) an involutive state /
symbol conjugacy.  Word actions retain both scan orientations, so geometric
reflection is represented by swapping the two directions rather than by
pretending a one-way carry became bidirectional.

Canonical action IDs are assigned *after* quotienting by every proved
transformation.  The same canonical references can therefore be used directly
in memo keys.  The binary-lift cache is likewise generic and iterative; it
powers any deterministic canonical state transition without Python recursion.
"""

from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass
from enum import IntFlag
from hashlib import sha256
from typing import Callable, Generic, Hashable, Iterable, TypeVar

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
    TransferSummaryID,
)


class ActionTransform(IntFlag):
    IDENTITY = 0
    MIRROR = 1
    CONJUGATE = 2

    @property
    def inverse(self) -> "ActionTransform":
        # Both generators are involutions and commute on oriented actions.
        return self


@dataclass(frozen=True, slots=True, init=False, eq=False)
class FiniteKernel:
    """An immutable, exhaustively captured finite transition definition.

    The constructor consumes the callback exactly once for each input pair.
    Execution and equality subsequently use only the frozen table. A digest is
    an inequality shortcut; equal digests still require exact definition equality.
    """

    state_count: int
    alphabet_size: int
    transition_table: tuple[tuple[int, ...], ...]
    state_conjugate: tuple[int, ...] | None
    symbol_conjugate: tuple[int, ...] | None
    name: str
    semantic_digest: str

    def __init_subclass__(cls, **kwargs: object) -> None:
        raise TypeError("finite kernel definitions cannot override their frozen table")

    def __init__(
        self,
        state_count: int,
        alphabet_size: int,
        transition: Callable[[int, int], int],
        state_conjugate: tuple[int, ...] | None = None,
        symbol_conjugate: tuple[int, ...] | None = None,
        name: str = "finite-kernel",
    ) -> None:
        if type(state_count) is not int or type(alphabet_size) is not int:
            raise TypeError("finite kernel dimensions require exact integers")
        states, alphabet = state_count, alphabet_size
        if states <= 0 or alphabet <= 0:
            raise ValueError((states, alphabet))
        object.__setattr__(self, "state_count", states)
        object.__setattr__(self, "alphabet_size", alphabet)
        if type(name) is not str or not name:
            raise TypeError("finite kernel name must be a nonempty string")
        object.__setattr__(self, "name", name)
        object.__setattr__(self, "state_conjugate", None)
        object.__setattr__(self, "symbol_conjugate", None)
        if (state_conjugate is None) != (symbol_conjugate is None):
            raise ValueError("state and symbol conjugacies must be supplied together")
        if state_conjugate is not None:
            if (
                type(state_conjugate) is not tuple
                or type(symbol_conjugate) is not tuple
            ):
                raise TypeError(
                    "finite kernel conjugacies require immutable integer tuples"
                )
            if any(
                type(value) is not int for value in state_conjugate + symbol_conjugate
            ):
                raise TypeError("finite kernel conjugacies require exact integers")
            sc = state_conjugate
            sy = symbol_conjugate
            if len(sc) != states or sorted(sc) != list(range(states)):
                raise ValueError(("state-conjugate", sc))
            if len(sy) != alphabet or sorted(sy) != list(range(alphabet)):
                raise ValueError(("symbol-conjugate", sy))
            if any(sc[sc[i]] != i for i in range(states)):
                raise ValueError("state conjugacy is not involutive")
            if any(sy[sy[i]] != i for i in range(alphabet)):
                raise ValueError("symbol conjugacy is not involutive")
            object.__setattr__(self, "state_conjugate", sc)
            object.__setattr__(self, "symbol_conjugate", sy)
        rows: list[tuple[int, ...]] = []
        for state in range(states):
            row = tuple(transition(state, symbol) for symbol in range(alphabet))
            if any(
                type(target) is not int or not 0 <= target < states for target in row
            ):
                raise ValueError(("transition outside finite state domain", state, row))
            rows.append(row)
        object.__setattr__(self, "transition_table", tuple(rows))
        object.__setattr__(
            self,
            "semantic_digest",
            sha256(repr(self.semantic_key).encode("utf-8")).hexdigest(),
        )

    @property
    def semantic_key(self) -> tuple[object, ...]:
        return (
            self.state_count,
            self.alphabet_size,
            self.transition_table,
            self.state_conjugate,
            self.symbol_conjugate,
        )

    def __eq__(self, other: object) -> bool:
        return (
            isinstance(other, FiniteKernel)
            and self.semantic_digest == other.semantic_digest
            and self.semantic_key == other.semantic_key
        )

    def __hash__(self) -> int:
        return hash(self.semantic_digest)

    def transition(self, state: int, symbol: int) -> int:
        if (
            type(state) is not int
            or type(symbol) is not int
            or not 0 <= state < self.state_count
            or not 0 <= symbol < self.alphabet_size
        ):
            raise ValueError((state, symbol))
        return self.transition_table[state][symbol]

    def verify_conjugacy(self) -> None:
        """Exhaustively prove ``K(T(q,a)) == T(Kq,Ka)`` on the local kernel."""
        if self.state_conjugate is None:
            return
        sc = self.state_conjugate
        sy = self.symbol_conjugate
        if sy is None:
            raise AssertionError("missing symbol conjugacy")
        for state in range(self.state_count):
            for symbol in range(self.alphabet_size):
                lhs = sc[int(self.transition(state, symbol))]
                rhs = int(self.transition(sc[state], sy[symbol]))
                if lhs != rhs:
                    raise ValueError((self.name, state, symbol, lhs, rhs))


@dataclass(frozen=True, slots=True)
class OrientedActionRef(ActionProgramID):
    transform: ActionTransform = ActionTransform.IDENTITY

    def __post_init__(self) -> None:
        super(OrientedActionRef, self).__post_init__()
        if not isinstance(self.transform, ActionTransform) or int(self.transform) & ~3:
            raise ValueError("invalid oriented action transform")

    @property
    def action_id(self) -> int:
        return self.local_id


@dataclass(frozen=True, slots=True)
class OrientedActionMetrics:
    mapping_count: int
    action_count: int
    action_alias_hits: int
    mirror_alias_hits: int
    conjugate_alias_hits: int
    compose_hits: int


class OrientedFiniteActionArena:
    """Intern exact word actions modulo mirror and a proved conjugacy.

    A raw oriented action is ``(forward, reverse)`` where each member is a
    function on the finite carry/boundary state set.  Reflection swaps the two
    functions.  Conjugacy transforms each function extensionally.  Only the
    lexicographically minimal orbit representative receives an action ID.
    """

    __slots__ = (
        "_kernel",
        "_owner",
        "_mapping_ids",
        "_mappings",
        "_compose",
        "_conjugates",
        "_action_ids",
        "_actions",
        "_leaf_refs",
        "action_alias_hits",
        "mirror_alias_hits",
        "conjugate_alias_hits",
        "compose_hits",
        "compose_cache_limit",
    )

    def __init__(
        self, kernel: FiniteKernel, *, compose_cache_limit: int = 4096
    ) -> None:
        if type(kernel) is not FiniteKernel:
            raise TypeError("oriented actions require an exact frozen finite kernel")
        if type(compose_cache_limit) is not int:
            raise TypeError("composition cache limit requires an exact integer")
        if compose_cache_limit < 0:
            raise ValueError("composition cache limit must be nonnegative")
        kernel.verify_conjugacy()
        self._kernel = kernel
        self._owner = ArenaToken("oriented-finite-actions")
        self._mapping_ids: dict[tuple[int, ...], int] = {}
        self._mappings: list[tuple[int, ...]] = []
        self._compose: OrderedDict[tuple[int, int], int] = OrderedDict()
        self._conjugates: dict[int, int] = {}
        self._action_ids: dict[tuple[int, int], int] = {}
        self._actions: list[tuple[int, int]] = []
        self._leaf_refs: dict[int, OrientedActionRef] = {}
        self.action_alias_hits = 0
        self.mirror_alias_hits = 0
        self.conjugate_alias_hits = 0
        self.compose_hits = 0
        self.compose_cache_limit = compose_cache_limit

    @property
    def kernel(self) -> FiniteKernel:
        return self._kernel

    def _intern_mapping(self, mapping: Iterable[int]) -> int:
        value = tuple(mapping)
        if any(type(target) is not int for target in value):
            raise TypeError("finite mappings require exact integer targets")
        if len(value) != self.kernel.state_count:
            raise ValueError((len(value), self.kernel.state_count))
        if any(not 0 <= target < self.kernel.state_count for target in value):
            raise ValueError(
                "finite mapping target lies outside the kernel state domain"
            )
        found = self._mapping_ids.get(value)
        if found is not None:
            return found
        out = len(self._mappings)
        self._mapping_ids[value] = out
        self._mappings.append(value)
        return out

    def _mapping_handle(self, local_id: int) -> TransferSummaryID:
        return TransferSummaryID(self._owner, "finite-mapping", local_id)

    def _validate_mapping(self, reference: TransferSummaryID) -> int:
        if type(reference) is not TransferSummaryID:
            raise TypeError("finite mapping requires a scoped transfer ID")
        return reference.validate(
            self._owner, "finite-mapping", size=len(self._mappings)
        ).local_id

    def _validate_action(self, reference: OrientedActionRef) -> int:
        if type(reference) is not OrientedActionRef:
            raise TypeError("oriented action requires a scoped oriented reference")
        reference.validate(self._owner, "oriented-action", size=len(self._actions))
        if (
            type(reference.transform) is not ActionTransform
            or int(reference.transform) & ~3
        ):
            raise ValueError("invalid oriented action transform")
        if (
            reference.transform & ActionTransform.CONJUGATE
            and self.kernel.state_conjugate is None
        ):
            raise ValueError("kernel has no proved conjugacy")
        return reference.local_id

    def mapping(self, reference: TransferSummaryID) -> tuple[int, ...]:
        return self._mappings[self._validate_mapping(reference)]

    def compose_mapping(
        self, before: TransferSummaryID, after: TransferSummaryID
    ) -> TransferSummaryID:
        first, second = self._validate_mapping(before), self._validate_mapping(after)
        return self._mapping_handle(self._compose_mapping(first, second))

    def conjugate_mapping(self, reference: TransferSummaryID) -> TransferSummaryID:
        local_id = self._validate_mapping(reference)
        if self.kernel.state_conjugate is None:
            raise ValueError("kernel has no proved conjugacy")
        return self._mapping_handle(self._conjugate_mapping(local_id))

    def intern_oriented(
        self, forward: TransferSummaryID, reverse: TransferSummaryID
    ) -> OrientedActionRef:
        first, second = self._validate_mapping(forward), self._validate_mapping(reverse)
        return self._intern_oriented(first, second)

    def raw_action(
        self, reference: OrientedActionRef
    ) -> tuple[TransferSummaryID, TransferSummaryID]:
        first, second = self._raw_action(self._validate_action(reference))
        return self._mapping_handle(first), self._mapping_handle(second)

    def oriented_pair(
        self, reference: OrientedActionRef
    ) -> tuple[TransferSummaryID, TransferSummaryID]:
        first, second = self._oriented_pair(reference)
        return self._mapping_handle(first), self._mapping_handle(second)

    def _compose_mapping(self, before_id: int, after_id: int) -> int:
        """Return the mapping for scanning ``before`` then ``after``."""
        key = (int(before_id), int(after_id))
        found = self._compose.get(key)
        if found is not None:
            self.compose_hits += 1
            self._compose.move_to_end(key)
            return found
        before = self._mappings[key[0]]
        after = self._mappings[key[1]]
        out = self._intern_mapping(
            after[before[state]] for state in range(self.kernel.state_count)
        )
        if self.compose_cache_limit:
            self._compose[key] = out
            self._compose.move_to_end(key)
            while len(self._compose) > self.compose_cache_limit:
                self._compose.popitem(last=False)
        return out

    def _conjugate_mapping(self, mapping_id: int) -> int:
        mapping_id = int(mapping_id)
        if self.kernel.state_conjugate is None:
            return mapping_id
        found = self._conjugates.get(mapping_id)
        if found is not None:
            return found
        sc = self.kernel.state_conjugate
        if sc is None:
            raise AssertionError("missing state conjugacy")
        mapping = self._mappings[mapping_id]
        # K o f o K; K is an involution.
        out = self._intern_mapping(
            sc[mapping[sc[state]]] for state in range(self.kernel.state_count)
        )
        self._conjugates[mapping_id] = out
        self._conjugates[out] = mapping_id
        return out

    @staticmethod
    def _apply_transform_pair(
        pair: tuple[int, int],
        transform: ActionTransform,
        conjugate: Callable[[int], int],
    ) -> tuple[int, int]:
        forward, reverse = pair
        if transform & ActionTransform.CONJUGATE:
            forward, reverse = conjugate(forward), conjugate(reverse)
        if transform & ActionTransform.MIRROR:
            forward, reverse = reverse, forward
        return forward, reverse

    def _canonicalize_pair(
        self, pair: tuple[int, int]
    ) -> tuple[tuple[int, int], ActionTransform]:
        candidates = [(pair, ActionTransform.IDENTITY)]
        candidates.append(((pair[1], pair[0]), ActionTransform.MIRROR))
        if self.kernel.state_conjugate is not None:
            cpair = (self._conjugate_mapping(pair[0]), self._conjugate_mapping(pair[1]))
            candidates.append((cpair, ActionTransform.CONJUGATE))
            candidates.append(
                (
                    (cpair[1], cpair[0]),
                    ActionTransform.MIRROR | ActionTransform.CONJUGATE,
                )
            )
        representative, transform = min(
            candidates, key=lambda item: (item[0], int(item[1]))
        )
        return representative, transform

    def _intern_oriented(self, forward_id: int, reverse_id: int) -> OrientedActionRef:
        raw = (int(forward_id), int(reverse_id))
        representative, transform = self._canonicalize_pair(raw)
        found = self._action_ids.get(representative)
        if found is None:
            found = len(self._actions)
            self._actions.append(representative)
            self._action_ids[representative] = found
        else:
            self.action_alias_hits += 1
        if transform & ActionTransform.MIRROR:
            self.mirror_alias_hits += 1
        if transform & ActionTransform.CONJUGATE:
            self.conjugate_alias_hits += 1
        return OrientedActionRef(self._owner, "oriented-action", found, transform)

    def _raw_action(self, action_id: int) -> tuple[int, int]:
        return self._actions[int(action_id)]

    def _oriented_pair(self, ref: OrientedActionRef) -> tuple[int, int]:
        pair = self._raw_action(self._validate_action(ref))
        return self._apply_transform_pair(
            pair, ref.transform.inverse, self._conjugate_mapping
        )

    def leaf(self, symbol: int) -> OrientedActionRef:
        if type(symbol) is not int or not 0 <= symbol < self.kernel.alphabet_size:
            raise ValueError(symbol)
        found = self._leaf_refs.get(symbol)
        if found is not None:
            return found
        if not 0 <= symbol < self.kernel.alphabet_size:
            raise ValueError(symbol)
        mapping = self._intern_mapping(
            self.kernel.transition(state, symbol)
            for state in range(self.kernel.state_count)
        )
        out = self._intern_oriented(mapping, mapping)
        self._leaf_refs[symbol] = out
        return out

    def compose(
        self, left: OrientedActionRef, right: OrientedActionRef
    ) -> OrientedActionRef:
        self._validate_action(left)
        self._validate_action(right)
        lf, lr = self._oriented_pair(left)
        rf, rr = self._oriented_pair(right)
        forward = self._compose_mapping(lf, rf)
        reverse = self._compose_mapping(rr, lr)
        return self._intern_oriented(forward, reverse)

    def apply(
        self, ref: OrientedActionRef, state: int, *, reverse: bool = False
    ) -> int:
        self._validate_action(ref)
        if (
            type(state) is not int
            or not 0 <= state < self.kernel.state_count
            or type(reverse) is not bool
        ):
            raise ValueError(state)
        forward_id, reverse_id = self._oriented_pair(ref)
        mapping = self._mappings[reverse_id if reverse else forward_id]
        return int(mapping[int(state)])

    def transformed(
        self, ref: OrientedActionRef, transform: ActionTransform
    ) -> OrientedActionRef:
        self._validate_action(ref)
        if not isinstance(transform, ActionTransform) or int(transform) & ~3:
            raise ValueError("invalid oriented action transform")
        if (
            transform & ActionTransform.CONJUGATE
            and self.kernel.state_conjugate is None
        ):
            raise ValueError("kernel has no proved conjugacy")
        pair = self._oriented_pair(ref)
        transformed = self._apply_transform_pair(
            pair, transform, self._conjugate_mapping
        )
        return self._intern_oriented(*transformed)

    @property
    def retained_entries(self) -> int:
        return (
            len(self._mapping_ids)
            + len(self._mappings)
            + len(self._compose)
            + len(self._conjugates)
            + len(self._action_ids)
            + len(self._actions)
            + len(self._leaf_refs)
        )

    def metrics(self) -> OrientedActionMetrics:
        return OrientedActionMetrics(
            len(self._mappings),
            len(self._actions),
            self.action_alias_hits,
            self.mirror_alias_hits,
            self.conjugate_alias_hits,
            self.compose_hits,
        )


S = TypeVar("S")
W = TypeVar("W")


@dataclass(frozen=True, slots=True)
class BinaryLiftMetrics:
    step_evaluations: int
    jump_requests: int
    jump_hits: int
    jump_entries: int
    jump_evictions: int = 0


@dataclass(frozen=True, slots=True)
class FiniteQuotientLiftMetrics:
    """Accounting for a completely enumerated successor-closed quotient."""

    states: int
    primitive_step_evaluations: int
    built_levels: int
    table_entries: int
    squaring_operations: int
    advance_queries: int


class FiniteQuotientLiftEngine(Generic[S, W]):
    """Binary lifting over a *proved complete finite* semantic quotient.

    This class deliberately differs from :class:`BinaryLiftEngine`.  The latter
    discovers state-specific jumps lazily and can therefore evaluate a linear
    successor chain on first use when semantic states do not repeat.  Here the
    caller supplies the complete finite carrier.  Construction evaluates one
    primitive transition for every quotient state and rejects any target whose
    canonical key is outside that carrier.  Higher levels square the *entire*
    transition table extensionally.

    Consequently, after an adapter has proved a bounded quotient ``Q -> Q'``,
    an ``n``-step query performs at most ``bit_length(n)`` table applications.
    The charged table-building cost is ``O(|Q| log n)`` and cannot hide an
    unbounded source trajectory in memo entries.
    """

    __slots__ = (
        "states",
        "key",
        "identity_weight",
        "combine_weight",
        "_index",
        "_targets",
        "_weights",
        "primitive_step_evaluations",
        "squaring_operations",
        "advance_queries",
    )

    def __init__(
        self,
        *,
        states: Iterable[S],
        step: Callable[[S], tuple[S, W]],
        key: Callable[[S], Hashable],
        identity_weight: W,
        combine_weight: Callable[[W, W], W],
    ) -> None:
        carrier = tuple(states)
        if not carrier:
            raise ValueError("finite quotient carrier must be nonempty")
        index: dict[Hashable, int] = {}
        for state_index, state in enumerate(carrier):
            state_key = key(state)
            if state_key in index:
                raise ValueError(("duplicate quotient key", state_key))
            index[state_key] = state_index

        targets: list[int] = []
        weights: list[W] = []
        for state in carrier:
            target, weight = step(state)
            target_key = key(target)
            target_index = index.get(target_key)
            if target_index is None:
                raise ValueError(("successor outside finite quotient", target_key))
            targets.append(target_index)
            weights.append(weight)

        self.states = carrier
        self.key = key
        self.identity_weight = identity_weight
        self.combine_weight = combine_weight
        self._index = index
        self._targets: list[tuple[int, ...]] = [tuple(targets)]
        self._weights: list[tuple[W, ...]] = [tuple(weights)]
        self.primitive_step_evaluations = len(carrier)
        self.squaring_operations = 0
        self.advance_queries = 0

    def _ensure_level(self, level: int) -> None:
        if type(level) is not int:
            raise TypeError("finite quotient level must be an exact integer")
        if level < 0:
            raise ValueError(level)
        while len(self._targets) <= level:
            previous_targets = self._targets[-1]
            previous_weights = self._weights[-1]
            next_targets: list[int] = []
            next_weights: list[W] = []
            for state_index, middle in enumerate(previous_targets):
                next_targets.append(previous_targets[middle])
                next_weights.append(
                    self.combine_weight(
                        previous_weights[state_index],
                        previous_weights[middle],
                    )
                )
                self.squaring_operations += 1
            self._targets.append(tuple(next_targets))
            self._weights.append(tuple(next_weights))

    def advance(self, state: S, steps: int) -> tuple[S, W]:
        if type(steps) is not int:
            raise TypeError("finite quotient step count must be an exact integer")
        if steps < 0:
            raise ValueError(steps)
        state_key = self.key(state)
        state_index = self._index.get(state_key)
        if state_index is None:
            raise ValueError(("state outside finite quotient", state_key))
        self.advance_queries += 1
        weight = self.identity_weight
        level = 0
        remaining = steps
        while remaining:
            if remaining & 1:
                self._ensure_level(level)
                delta = self._weights[level][state_index]
                state_index = self._targets[level][state_index]
                weight = self.combine_weight(weight, delta)
            remaining >>= 1
            level += 1
        return self.states[state_index], weight

    def metrics(self) -> FiniteQuotientLiftMetrics:
        states = len(self.states)
        levels = len(self._targets)
        return FiniteQuotientLiftMetrics(
            states=states,
            primitive_step_evaluations=self.primitive_step_evaluations,
            built_levels=levels,
            table_entries=states * levels,
            squaring_operations=self.squaring_operations,
            advance_queries=self.advance_queries,
        )


@dataclass(frozen=True, slots=True)
class _LiftEval(Generic[S]):
    state: S
    level: int


@dataclass(frozen=True, slots=True)
class _LiftAfterFirst:
    level: int
    key: tuple[int, Hashable]


@dataclass(frozen=True, slots=True)
class _LiftAfterSecond(Generic[W]):
    key: tuple[int, Hashable]
    weight: W


class BinaryLiftEngine(Generic[S, W]):
    """Iterative memoized binary lifting for an exact deterministic transition.

    The engine does not assume that memoization makes an arbitrary state system
    small.  It reports step and jump counts so callers cannot mistake a compact
    exponent syntax for compact semantic closure.
    """

    __slots__ = (
        "step",
        "key",
        "identity_weight",
        "combine_weight",
        "_jumps",
        "step_evaluations",
        "jump_requests",
        "jump_hits",
        "jump_evictions",
        "jump_cache_limit",
    )

    def __init__(
        self,
        *,
        step: Callable[[S], tuple[S, W]],
        key: Callable[[S], Hashable],
        identity_weight: W,
        combine_weight: Callable[[W, W], W],
        jump_cache_limit: int = 16384,
    ) -> None:
        if type(jump_cache_limit) is not int:
            raise TypeError("binary lift cache limit must be an exact integer")
        if jump_cache_limit < 0:
            raise ValueError("binary lift cache limit must be nonnegative")
        self.step = step
        self.key = key
        self.identity_weight = identity_weight
        self.combine_weight = combine_weight
        self.jump_cache_limit = jump_cache_limit
        self._jumps: OrderedDict[tuple[int, Hashable], tuple[S, W]] = OrderedDict()
        self.step_evaluations = 0
        self.jump_requests = 0
        self.jump_hits = 0
        self.jump_evictions = 0

    def _cache_get(self, cache_key: tuple[int, Hashable]) -> tuple[S, W] | None:
        found = self._jumps.get(cache_key)
        if found is not None:
            self.jump_hits += 1
            self._jumps.move_to_end(cache_key)
        return found

    def _cache_put(self, cache_key: tuple[int, Hashable], value: tuple[S, W]) -> None:
        if not self.jump_cache_limit:
            return
        self._jumps[cache_key] = value
        self._jumps.move_to_end(cache_key)
        while len(self._jumps) > self.jump_cache_limit:
            self._jumps.popitem(last=False)
            self.jump_evictions += 1

    def _jump(self, state: S, level: int) -> tuple[S, W]:
        if type(level) is not int:
            raise TypeError("binary lift level must be an exact integer")
        if level < 0:
            raise ValueError(level)
        root_key = (level, self.key(state))
        self.jump_requests += 1
        found = self._cache_get(root_key)
        if found is not None:
            return found

        results: list[tuple[S, W]] = []
        tasks: list[_LiftEval[S] | _LiftAfterFirst | _LiftAfterSecond[W]] = [
            _LiftEval(state, level)
        ]
        while tasks:
            frame = tasks.pop()
            if isinstance(frame, _LiftEval):
                current, current_level = frame.state, frame.level
                cache_key = (current_level, self.key(current))
                self.jump_requests += 1
                cached = self._cache_get(cache_key)
                if cached is not None:
                    results.append(cached)
                    continue
                if current_level == 0:
                    out = self.step(current)
                    self.step_evaluations += 1
                    self._cache_put(cache_key, out)
                    results.append(out)
                    continue
                tasks.append(_LiftAfterFirst(current_level, cache_key))
                tasks.append(_LiftEval(current, current_level - 1))
                continue
            if isinstance(frame, _LiftAfterFirst):
                middle, first_weight = results.pop()
                tasks.append(_LiftAfterSecond(frame.key, first_weight))
                tasks.append(_LiftEval(middle, frame.level - 1))
                continue
            target, second_weight = results.pop()
            out = (target, self.combine_weight(frame.weight, second_weight))
            self._cache_put(frame.key, out)
            results.append(out)
        if len(results) != 1:
            raise AssertionError(len(results))
        return results[0]

    def advance(self, state: S, steps: int) -> tuple[S, W]:
        if type(steps) is not int:
            raise TypeError("binary lift step count must be an exact integer")
        if steps < 0:
            raise ValueError(steps)
        out = state
        weight = self.identity_weight
        level = 0
        remaining = steps
        while remaining:
            if remaining & 1:
                out, delta = self._jump(out, level)
                weight = self.combine_weight(weight, delta)
            remaining >>= 1
            level += 1
        return out, weight

    def metrics(self) -> BinaryLiftMetrics:
        return BinaryLiftMetrics(
            self.step_evaluations,
            self.jump_requests,
            self.jump_hits,
            len(self._jumps),
            self.jump_evictions,
        )


__all__ = [
    "ActionTransform",
    "FiniteKernel",
    "OrientedActionRef",
    "OrientedActionMetrics",
    "OrientedFiniteActionArena",
    "FiniteQuotientLiftMetrics",
    "FiniteQuotientLiftEngine",
    "BinaryLiftMetrics",
    "BinaryLiftEngine",
]
