"""Exact partial affine monoid for finite Collatz branch programs.

This module deliberately separates two questions:

* a *known finite branch program* has a tiny exact algebraic summary; and
* the full Collatz map still has to discover which branch program applies.

For one branch program the exact action is

    x |-> (multiplier*x + offset) / 2**shift

on either an empty domain or one residue class ``x == residue (mod 2**domain_bits)``.
The representation is closed under composition.  It therefore provides a genuine
powered monoid for branch programs without pretending that the exponentially many
possible parity domains of a source-independent ``T**N`` have disappeared.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable, MutableMapping, MutableSequence
from dataclasses import dataclass
from typing import Literal, TypeVar, cast

from number_compiler.arithmetic.fields.morphism_core import (
    DyadicAffineCocycle,
    InternedEffectNode,
    LazyLoweringCache,
    binary_power,
)
from number_compiler.arithmetic.functions.word_concatenation import concatenate_words
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger

Branch = Literal["E", "O"]


@dataclass(frozen=True, slots=True)
class CollatzAffineBranch:
    """Canonical exact partial function for one finite Collatz branch program."""

    steps: int
    odd_steps: int
    multiplier: int
    offset: int
    shift: int
    domain_bits: int
    residue: int
    empty: bool = False

    def __post_init__(self) -> None:
        if (
            self.steps < 0
            or self.odd_steps < 0
            or self.shift < 0
            or self.domain_bits < 0
        ):
            raise ValueError(self)
        if self.odd_steps > self.steps or self.shift > self.steps:
            raise ValueError(self)
        if self.empty:
            return
        if self.multiplier <= 0 or (self.multiplier & 1) == 0:
            raise ValueError("Collatz affine multiplier must be positive and odd")
        modulus = 1 << self.domain_bits
        if not 0 <= self.residue < modulus:
            raise ValueError((self.residue, self.domain_bits))

    @classmethod
    def identity(cls) -> CollatzAffineBranch:
        return cls(0, 0, 1, 0, 0, 0, 0, False)

    @classmethod
    def zero(cls, *, steps: int = 0) -> CollatzAffineBranch:
        return cls(int(steps), 0, 1, 0, 0, 0, 0, True)

    @classmethod
    def atom(cls, branch: Branch) -> CollatzAffineBranch:
        if branch == "E":
            return cls(1, 0, 1, 0, 1, 1, 0, False)
        if branch == "O":
            return cls(1, 1, 3, 1, 0, 1, 1, False)
        raise ValueError(branch)

    @property
    def cocycle(self) -> DyadicAffineCocycle:
        if self.empty:
            raise ValueError("empty Collatz branch has no affine cocycle")
        return DyadicAffineCocycle(self.multiplier, self.offset, self.shift)

    @property
    def modulus(self) -> int:
        return 1 << self.domain_bits

    def accepts(self, value: int) -> bool:
        if self.empty:
            return False
        value = int(value)
        return value >= 0 and (value & (self.modulus - 1)) == self.residue

    def apply(self, value: int) -> int:
        value = int(value)
        if not self.accepts(value):
            raise ValueError(
                f"value {value} is outside Collatz branch domain "
                f"{self.residue} mod 2^{self.domain_bits}"
            )
        numerator = self.multiplier * value + self.offset
        divisor = 1 << self.shift
        if numerator % divisor:
            raise AssertionError((self, value, numerator))
        return numerator // divisor

    def semantic_key(self) -> tuple[object, ...]:
        if self.empty:
            return (self.steps, True)
        return (
            self.steps,
            self.odd_steps,
            self.multiplier,
            self.offset,
            self.shift,
            self.domain_bits,
            self.residue,
            False,
        )

    def description_bits(self) -> int:
        """Charge the actual integer parameters, not merely the object count."""
        if self.empty:
            return max(1, self.steps.bit_length()) + 1
        vals = (
            self.steps,
            self.odd_steps,
            self.multiplier,
            self.offset,
            self.shift,
            self.domain_bits,
            self.residue,
        )
        return sum(max(1, int(v).bit_length()) for v in vals) + 1


def _intersection_residue(
    *, first: CollatzAffineBranch, second: CollatzAffineBranch
) -> tuple[int, int] | None:
    """Pull ``second``'s dyadic input domain back through ``first`` exactly."""
    d1 = first.domain_bits
    d2_pull = first.shift + second.domain_bits
    if d2_pull == 0:
        candidate = 0
    else:
        modulus = 1 << d2_pull
        inv = pow(first.multiplier, -1, modulus)
        candidate = (inv * ((second.residue << first.shift) - first.offset)) % modulus

    if d1 >= d2_pull:
        # The first domain is stronger.  Verify it implies the pulled-back one.
        if d2_pull and (first.residue & ((1 << d2_pull) - 1)) != candidate:
            return None
        return first.residue, d1

    # The pulled-back second domain is stronger.  It must refine the first.
    if d1 and (candidate & ((1 << d1) - 1)) != first.residue:
        return None
    return candidate, d2_pull


def compose_collatz_branches(
    first: CollatzAffineBranch, second: CollatzAffineBranch
) -> CollatzAffineBranch:
    """Return ``second o first`` as one canonical partial affine action."""
    if first.empty or second.empty:
        return CollatzAffineBranch.zero(steps=first.steps + second.steps)

    domain = _intersection_residue(first=first, second=second)
    if domain is None:
        return CollatzAffineBranch.zero(steps=first.steps + second.steps)
    residue, domain_bits = domain

    cocycle = first.cocycle.then(second.cocycle)
    return CollatzAffineBranch(
        steps=first.steps + second.steps,
        odd_steps=first.odd_steps + second.odd_steps,
        multiplier=cocycle.multiplier,
        offset=cocycle.addend,
        shift=cocycle.shift,
        domain_bits=domain_bits,
        residue=residue,
        empty=False,
    )


_NodeT = TypeVar("_NodeT")


def _balanced_accumulate(
    nodes: Iterable[_NodeT],
    *,
    identity: _NodeT,
    concat: Callable[[_NodeT, _NodeT], _NodeT],
) -> _NodeT:
    """Binary-counter accumulation with logarithmic temporary stack depth."""
    levels: list[_NodeT | None] = []
    count = 0
    for initial in nodes:
        node = initial
        count += 1
        level = 0
        while True:
            if level == len(levels):
                levels.append(node)
                break
            prior = levels[level]
            if prior is None:
                levels[level] = node
                break
            levels[level] = None
            node = concat(prior, node)
            level += 1
    if count == 0:
        return identity
    result: _NodeT | None = None
    for remaining in reversed(levels):
        if remaining is None:
            continue
        result = remaining if result is None else concat(result, remaining)
    if result is None:
        raise AssertionError("nonempty event sequence lost")
    return result


CollatzPowerNode = InternedEffectNode[CollatzAffineBranch]


class CollatzPowerArena:
    """Early-canonical interner for Collatz branch-program effects.

    Construction history is intentionally *not* retained.  The affine action
    plus dyadic admissible domain is the complete behavior of a finite branch
    program, so keeping child pointers would duplicate provenance after the
    quotient.  Cache/context size and the final operator description are
    reported separately.
    """

    __slots__ = (
        "_atoms",
        "_by_key",
        "_identity",
        "_nodes",
        "composition_operations",
        "intern_hits",
        "intern_misses",
    )

    def __init__(self) -> None:
        self._nodes: list[CollatzPowerNode] = []
        self._by_key: dict[tuple[object, ...], CollatzPowerNode] = {}
        self.composition_operations = 0
        self.intern_hits = 0
        self.intern_misses = 0
        self._identity = self._intern(CollatzAffineBranch.identity())
        self._atoms = {
            "E": self._intern(CollatzAffineBranch.atom("E")),
            "O": self._intern(CollatzAffineBranch.atom("O")),
        }

    def _intern(self, effect: CollatzAffineBranch) -> CollatzPowerNode:
        key = effect.semantic_key()
        old = self._by_key.get(key)
        if old is not None:
            self.intern_hits += 1
            return old
        node = CollatzPowerNode(node_id=len(self._nodes) + 1, effect=effect)
        self._nodes.append(node)
        self._by_key[key] = node
        self.intern_misses += 1
        return node

    @property
    def identity(self) -> CollatzPowerNode:
        return self._identity

    def atom(self, branch: Branch) -> CollatzPowerNode:
        try:
            return self._atoms[branch]
        except KeyError as exc:
            raise ValueError(branch) from exc

    def concat(
        self, first: CollatzPowerNode, second: CollatzPowerNode
    ) -> CollatzPowerNode:
        self.composition_operations += 1
        return self._intern(compose_collatz_branches(first.effect, second.effect))

    def from_branches(self, branches: Iterable[Branch]) -> CollatzPowerNode:
        return _balanced_accumulate(
            (self.atom(branch) for branch in branches),
            identity=self.identity,
            concat=self.concat,
        )

    def power(self, node: CollatzPowerNode, exponent: int) -> CollatzPowerNode:
        powered = binary_power(
            node,
            exponent,
            identity=self.identity,
            compose=self.concat,
        )
        return powered.value

    @property
    def node_count(self) -> int:
        return len(self._nodes)

    def metrics(self, root: CollatzPowerNode) -> dict[str, int]:
        return {
            "operator_nodes": 1,
            "operator_description_bits": root.effect.description_bits(),
            "arena_nodes": len(self._nodes),
            "composition_operations": self.composition_operations,
            "intern_hits": self.intern_hits,
            "intern_misses": self.intern_misses,
            "steps": root.effect.steps,
            "domain_bits": root.effect.domain_bits,
        }


@dataclass(frozen=True, slots=True)
class CollatzEventTransport:
    """Compact summary of an already-proved accelerated-event block.

    Only additive counters are composed eagerly.  The potentially huge affine
    offset of a multi-event block is deliberately absent; it is lowered from
    the canonical event DAG only when requested.
    """

    events: int
    physical_steps: int
    shift: int

    def __post_init__(self) -> None:
        if min(map(int, (self.events, self.physical_steps, self.shift))) < 0:
            raise ValueError(self)
        object.__setattr__(self, "events", int(self.events))
        object.__setattr__(self, "physical_steps", int(self.physical_steps))
        object.__setattr__(self, "shift", int(self.shift))

    @classmethod
    def identity(cls) -> CollatzEventTransport:
        return cls(0, 0, 0)

    @classmethod
    def valuation_atom(cls, valuation: int) -> CollatzEventTransport:
        k = int(valuation)
        if k <= 0:
            raise ValueError(valuation)
        return cls(1, k + 1, k)

    def then(self, other: CollatzEventTransport) -> CollatzEventTransport:
        return CollatzEventTransport(
            self.events + other.events,
            self.physical_steps + other.physical_steps,
            self.shift + other.shift,
        )

    @property
    def description_bits(self) -> int:
        return sum(
            max(1, value.bit_length())
            for value in (self.events, self.physical_steps, self.shift)
        )


@dataclass(frozen=True, slots=True)
class CollatzEventNode:
    node_id: int
    effect: CollatzEventTransport
    kind: str
    valuation: int | None = None
    left: CollatzEventNode | None = None
    right: CollatzEventNode | None = None

    def __post_init__(self) -> None:
        if self.kind not in {"identity", "event", "concat"}:
            raise ValueError(self.kind)
        if self.kind == "identity":
            if (
                self.valuation is not None
                or self.left is not None
                or self.right is not None
            ):
                raise ValueError(self)
        elif self.kind == "event":
            if (
                self.valuation is None
                or self.valuation <= 0
                or self.left is not None
                or self.right is not None
            ):
                raise ValueError(self)
        elif self.left is None or self.right is None or self.valuation is not None:
            raise ValueError(self)


class CollatzEventArena:
    """Lazy canonical consumer for already-extracted Collatz valuations.

    ``event(k)`` stores only ``k``.  Concatenation stores two interned child
    morphisms and additive counters; it does not create the affine offset or a
    dyadic source-domain residue.  Concrete transport can be executed directly
    through event leaves or lowered to a cocycle explicitly.
    """

    __slots__ = (
        "__weakref__",
        "_by_key",
        "_cocycle_cache",
        "_cocycle_owner",
        "_concat_cache",
        "_concat_owner",
        "_event_owner",
        "_events",
        "_identity",
        "_key_owner",
        "_ledger",
        "_node_owner",
        "_nodes",
        "_uniform",
        "_uniform_owner",
        "composition_operations",
        "intern_hits",
        "intern_misses",
    )

    def __init__(self, *, ledger: ResourceLedger | None = None) -> None:
        ledger = ledger if ledger is not None else ResourceLedger()
        self._ledger = ledger
        prefix = f"collatz-event-{len(ledger.inventory())}"
        self._node_owner = ledger.register(prefix + "-nodes", "action_program")
        self._key_owner = ledger.register(prefix + "-keys", "field_transfer_interner")
        self._event_owner = ledger.register(
            prefix + "-atoms", "runtime_query_state_memo"
        )
        self._concat_owner = ledger.register(
            prefix + "-concats", "runtime_query_state_memo"
        )
        self._uniform_owner = ledger.register(
            prefix + "-uniform", "runtime_query_state_memo"
        )
        self._cocycle_owner = ledger.register(prefix + "-cocycles", "observation_memo")
        self._nodes: MutableSequence[CollatzEventNode] = ledger.make_list(
            self._node_owner
        )
        self._by_key: MutableMapping[tuple[object, ...], CollatzEventNode] = (
            ledger.make_dict(self._key_owner)
        )
        self._events: MutableMapping[int, CollatzEventNode] = ledger.make_dict(
            self._event_owner
        )
        self._concat_cache: MutableMapping[tuple[int, int], CollatzEventNode] = (
            ledger.make_dict(self._concat_owner)
        )
        self._uniform: MutableMapping[int, int | None] = ledger.make_dict(
            self._uniform_owner
        )
        self._cocycle_cache: LazyLoweringCache[int, DyadicAffineCocycle] = (
            LazyLoweringCache()
        )
        self._cocycle_cache._values = cast(
            dict[int, DyadicAffineCocycle], OwnedMemo(ledger, self._cocycle_owner)
        )
        self.composition_operations = 0
        self.intern_hits = 0
        self.intern_misses = 0
        self._identity = self._intern(
            ("identity",),
            CollatzEventTransport.identity(),
            "identity",
        )
        ledger.register_execution_root(self)

    def _intern(
        self,
        key: tuple[object, ...],
        effect: CollatzEventTransport,
        kind: str,
        *,
        valuation: int | None = None,
        left: CollatzEventNode | None = None,
        right: CollatzEventNode | None = None,
        reserved: bool = False,
    ) -> CollatzEventNode:
        old = self._by_key.get(key)
        if old is not None:
            self.intern_hits += 1
            return old
        if self._ledger is not None and not reserved:
            assert self._node_owner is not None and self._key_owner is not None
            self._ledger.reserve_many(
                ((self._node_owner, 1, 1), (self._key_owner, 1, 0))
            )
        node = CollatzEventNode(
            len(self._nodes) + 1,
            effect,
            kind,
            valuation,
            left,
            right,
        )
        self._nodes.append(node)
        self._by_key[key] = node
        self.intern_misses += 1
        return node

    @property
    def identity(self) -> CollatzEventNode:
        return self._identity

    def validate_node(self, node: CollatzEventNode) -> None:
        if (
            type(node) is not CollatzEventNode
            or node.node_id < 1
            or node.node_id > len(self._nodes)
            or self._nodes[node.node_id - 1] is not node
        ):
            raise ValueError("event node belongs to another arena")
        node.__post_init__()
        if node.kind == "identity":
            key: tuple[object, ...] = ("identity",)
            expected = CollatzEventTransport.identity()
        elif node.kind == "event":
            assert node.valuation is not None
            key = ("event", node.valuation)
            expected = CollatzEventTransport.valuation_atom(node.valuation)
            if self._events.get(node.valuation) is not node:
                raise ValueError("event atom lost its canonical arena binding")
        else:
            assert node.left is not None and node.right is not None
            for child in (node.left, node.right):
                if (
                    type(child) is not CollatzEventNode
                    or not 0 < child.node_id < node.node_id
                    or self._nodes[child.node_id - 1] is not child
                ):
                    raise ValueError("event child belongs to another arena")
            key = ("concat", node.left.node_id, node.right.node_id)
            expected = node.left.effect.then(node.right.effect)
        if self._by_key.get(key) is not node or node.effect != expected:
            raise ValueError("event node has forged canonical semantics")

    def event(self, valuation: int) -> CollatzEventNode:
        k = int(valuation)
        if k <= 0:
            raise ValueError(valuation)
        old = self._events.get(k)
        if old is not None:
            self.intern_hits += 1
            return old
        reserved = self._ledger is not None
        if reserved:
            assert self._ledger is not None
            assert None not in (
                self._node_owner,
                self._key_owner,
                self._event_owner,
                self._uniform_owner,
            )
            self._ledger.reserve_many(
                (
                    (self._node_owner, 1, 1),
                    (self._key_owner, 1, 0),
                    (self._event_owner, 1, 0),
                    (self._uniform_owner, 1, 0),
                )
            )
        node = self._intern(
            ("event", k),
            CollatzEventTransport.valuation_atom(k),
            "event",
            valuation=k,
            reserved=reserved,
        )
        self._uniform[node.node_id] = k
        self._events[k] = node
        return node

    def _join(
        self, first: CollatzEventNode, second: CollatzEventNode
    ) -> CollatzEventNode:
        self.composition_operations += 1
        key = ("concat", first.node_id, second.node_id)
        reserved = self._ledger is not None and key not in self._by_key
        if reserved:
            assert self._ledger is not None
            assert None not in (self._node_owner, self._key_owner, self._uniform_owner)
            self._ledger.reserve_many(
                (
                    (self._node_owner, 1, 1),
                    (self._key_owner, 1, 0),
                    (self._uniform_owner, 1, 0),
                )
            )
        node = self._intern(
            key,
            first.effect.then(second.effect),
            "concat",
            left=first,
            right=second,
            reserved=reserved,
        )
        a, b = self._uniform.get(first.node_id), self._uniform.get(second.node_id)
        self._uniform[node.node_id] = a if a == b else None
        return node

    def _uniform_word(self, valuation: int, count: int) -> CollatzEventNode:
        """Construct the canonical shape of one run, with logarithmic nodes."""
        if count == 0:
            return self.identity
        block = self.event(valuation)
        selected = []
        while count:
            if count & 1:
                selected.append(block)
            count >>= 1
            if count:
                block = self._join(block, block)
        result = selected[0]
        for block in selected[1:]:
            result = self._join(block, result)
        return result

    def concat(
        self, first: CollatzEventNode, second: CollatzEventNode
    ) -> CollatzEventNode:
        """Unique largest-dyadic-prefix association of an event word.

        Pending joins are evaluated iteratively and memoized by input nodes.
        Shared subwords stay shared; no exact affine value or sampled hash is
        used to decide equality. This quotients association, not distinct words.
        """
        self.validate_node(first)
        self.validate_node(second)
        reservations = 0
        previous = len(self._concat_cache)

        def reserve() -> None:
            nonlocal reservations
            if self._ledger is not None:
                assert self._concat_owner is not None
                self._ledger.reserve(self._concat_owner, entries=1)
                reservations += 1

        try:
            return concatenate_words(
                first,
                second,
                key_of=lambda node: node.node_id,
                length=lambda node: node.effect.events,
                children=lambda node: (
                    cast(CollatzEventNode, node.left),
                    cast(CollatzEventNode, node.right),
                ),
                uniform=lambda node: self._uniform.get(node.node_id),
                run=self._uniform_word,
                join=self._join,
                cache=self._concat_cache,
                reserve=reserve,
            )
        finally:
            excess = reservations - (len(self._concat_cache) - previous)
            if self._ledger is not None and excess:
                assert self._ledger is not None and self._concat_owner is not None
                self._ledger.release(self._concat_owner, entries=excess)

    def from_valuations(self, valuations: Iterable[int]) -> CollatzEventNode:
        return _balanced_accumulate(
            (self.event(k) for k in valuations),
            identity=self.identity,
            concat=self.concat,
        )

    def power(self, node: CollatzEventNode, exponent: int) -> CollatzEventNode:
        self.validate_node(node)
        exponent = int(exponent)
        if exponent < 0:
            raise ValueError(exponent)
        uniform = self._uniform.get(node.node_id)
        if uniform is not None:
            return self._uniform_word(uniform, node.effect.events * exponent)
        return binary_power(
            node,
            int(exponent),
            identity=self.identity,
            compose=self.concat,
        ).value

    def apply_exact(self, node: CollatzEventNode, value: int) -> int:
        """Execute the proven events directly, without lowering a huge offset."""
        value = int(value)
        stack = [node]
        while stack:
            current = stack.pop()
            if current.kind == "identity":
                continue
            if current.kind == "event":
                if current.valuation is None:
                    raise AssertionError(current)
                numerator = 3 * value + 1
                divisor = 1 << current.valuation
                if numerator % divisor:
                    raise ValueError(
                        "event valuation is incompatible with concrete source"
                    )
                value = numerator // divisor
                if not value & 1:
                    raise ValueError("event valuation is not exact for concrete source")
                continue
            if current.left is None or current.right is None:
                raise AssertionError(current)
            # Concatenation semantics are left then right.
            stack.append(current.right)
            stack.append(current.left)
        return value

    def materialize_cocycle(self, node: CollatzEventNode) -> DyadicAffineCocycle:
        """Explicit lowering boundary for callers that genuinely need coefficients."""
        local: dict[int, DyadicAffineCocycle] = {}
        stack: list[tuple[CollatzEventNode, bool]] = [(node, False)]
        while stack:
            current, ready = stack.pop()
            if current.node_id in local:
                continue
            if current.kind == "identity":
                candidate = DyadicAffineCocycle.identity()
            elif current.kind == "event":
                if current.valuation is None:
                    raise AssertionError(current)
                candidate = DyadicAffineCocycle(3, 1, current.valuation)
            else:
                if current.left is None or current.right is None:
                    raise AssertionError(current)
                if not ready:
                    stack.append((current, True))
                    if current.right.node_id not in local:
                        stack.append((current.right, False))
                    if current.left.node_id not in local:
                        stack.append((current.left, False))
                    continue
                candidate = local[current.left.node_id].then(
                    local[current.right.node_id]
                )

            def lower_candidate(
                bound: DyadicAffineCocycle = candidate,
            ) -> DyadicAffineCocycle:
                return bound

            local[current.node_id] = self._cocycle_cache.get_or_lower(
                current.node_id,
                lower_candidate,
            )
        return local[node.node_id]

    @property
    def cocycle_materializations(self) -> int:
        return self._cocycle_cache.misses

    @property
    def node_count(self) -> int:
        return len(self._nodes)

    def _reachable_nodes(self, root: CollatzEventNode) -> int:
        seen: set[int] = set()
        stack = [root]
        while stack:
            node = stack.pop()
            if node.node_id in seen:
                continue
            seen.add(node.node_id)
            if node.left is not None:
                stack.append(node.left)
            if node.right is not None:
                stack.append(node.right)
        return len(seen)

    def metrics(self, root: CollatzEventNode) -> dict[str, int]:
        return {
            "operator_nodes": self._reachable_nodes(root),
            "operator_description_bits": root.effect.description_bits,
            "arena_nodes": self.node_count,
            "composition_operations": self.composition_operations,
            "intern_hits": self.intern_hits,
            "intern_misses": self.intern_misses,
            "events": root.effect.events,
            "physical_steps": root.effect.physical_steps,
            "shift": root.effect.shift,
            "cocycle_materializations": self._cocycle_cache.misses,
        }


def collatz_branch_word(seed: int, steps: int) -> tuple[Branch, ...]:
    """Reference-only concrete branch trace used by tests and benchmarks."""
    seed, steps = int(seed), int(steps)
    if seed <= 0 or steps < 0:
        raise ValueError((seed, steps))
    value = seed
    out: list[Branch] = []
    for _ in range(steps):
        if value & 1:
            out.append("O")
            value = 3 * value + 1
        else:
            out.append("E")
            value //= 2
    return tuple(out)


def collatz_apply_word(seed: int, branches: Iterable[Branch]) -> int:
    """Independent direct executor for differential tests."""
    value = int(seed)
    for branch in branches:
        if branch == "E":
            if value & 1:
                raise ValueError("even branch on odd input")
            value //= 2
        elif branch == "O":
            if not value & 1:
                raise ValueError("odd branch on even input")
            value = 3 * value + 1
        else:
            raise ValueError(branch)
    return value


__all__ = [
    "Branch",
    "CollatzAffineBranch",
    "CollatzEventArena",
    "CollatzEventNode",
    "CollatzEventTransport",
    "CollatzPowerArena",
    "CollatzPowerNode",
    "collatz_apply_word",
    "collatz_branch_word",
    "compose_collatz_branches",
]
