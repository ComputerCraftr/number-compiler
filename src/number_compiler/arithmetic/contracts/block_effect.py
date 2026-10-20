"""Immutable block-effect interfaces and compatibility construction budgets.

Production indexes compile these definitions into scoped temporal actions and
recursive field images under their own ResourceLedger. The exact composed
boundary machines remain in proof tooling. Compact operator syntax alone does
not certify logarithmic point-query execution; runtime observations account
for the concrete interface work separately.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import IntEnum
from itertools import count
from typing import Protocol, TypeAlias

from number_compiler.arithmetic.contracts.input_validation import require_integer


def _carry_out(pair_value: int, carry_in: int, base: int) -> int:
    return (pair_value + carry_in) // base


def normalized_digit(pair_value: int, carry_in: int, base: int) -> int:
    carry = _carry_out(pair_value, carry_in, base)
    return pair_value + carry_in - base * carry


def _state_key(state: object) -> object:
    """Typed canonical cache key for a boundary value.

    Earlier releases returned a bare ``node_id`` for hash-consed contexts and a
    bare integer for finite-kernel states.  Those are distinct identifier
    namespaces and can numerically collide.  Type-tag every local handle so no
    cache can alias semantically different state kinds.
    """
    if isinstance(state, bool):
        return ("bool", int(state))
    if isinstance(state, int):
        return ("finite_state", int(state))
    semantic_key = getattr(state, "canonical_state_key", None)
    if semantic_key is not None:
        value = semantic_key() if callable(semantic_key) else semantic_key
        return (
            "semantic_state",
            type(state).__module__,
            type(state).__qualname__,
            value,
        )
    node_id = getattr(state, "node_id", None)
    if node_id is not None:
        cls = type(state)
        return ("context_state", cls.__module__, cls.__qualname__, int(node_id))
    return ("value_state", type(state).__module__, type(state).__qualname__, state)


def _cache_state_key(state: object) -> object:
    """Canonical *runtime-cache* identity for a boundary state.

    Persistent HashLife/runtime memos should retain the canonical state object,
    not serialize a construction ``node_id`` into another key namespace.  Exact
    finite integer states stay type-tagged; canonical object carriers are pinned
    by their owning interners/budget or by the cache key itself. Canonical object
    identities are final before a parent HashLife action may retain them; there
    is no post-hoc representative rewrite.
    """
    if isinstance(state, bool):
        return ("bool", int(state))
    if isinstance(state, int):
        return ("finite_state", int(state))
    canonical = getattr(state, "canonical_cache_state", None)
    if canonical is not None:
        state = canonical() if callable(canonical) else canonical
    try:
        hash(state)
    except TypeError:
        return _state_key(state)
    return state


def _effect_key(effect: object) -> object:
    """Semantic operator key; never use construction-order ``node_id`` as identity."""
    key = getattr(effect, "canonical_key", None)
    if key is not None:
        return key() if callable(key) else key
    return (
        "effect",
        type(effect).__module__,
        type(effect).__qualname__,
        int(getattr(effect, "base", -1)),
        int(getattr(effect, "exponent", -1)),
    )


class BlockContextBudgetExceeded(RuntimeError):
    pass


@dataclass
class BlockContextBudget:
    max_nodes: int | None = None
    max_cache_entries: int | None = None
    created_nodes: int = 0
    cache_entries: int = 0

    def __setattr__(self, name: str, value: object) -> None:
        if name in ("max_nodes", "max_cache_entries"):
            if value is not None:
                require_integer(value, name, 0)
        elif name in ("created_nodes", "cache_entries"):
            require_integer(value, name, 0)
        object.__setattr__(self, name, value)

    def consume_node(self, count_value: int = 1) -> None:
        require_integer(count_value, "node count", 0)
        if (
            self.max_nodes is not None
            and self.created_nodes + count_value > self.max_nodes
        ):
            raise BlockContextBudgetExceeded(
                f"block-effect execution context exceeded {self.max_nodes} retained nodes"
            )
        self.created_nodes += count_value

    def check_spacetime_nodes(self, spacetime_nodes: int) -> None:
        require_integer(spacetime_nodes, "spacetime nodes", 0)
        if (
            self.max_nodes is not None
            and self.created_nodes + spacetime_nodes > self.max_nodes
        ):
            raise BlockContextBudgetExceeded(
                f"block-effect execution context exceeded {self.max_nodes} retained nodes"
            )

    def consume_cache(self, count_value: int = 1) -> None:
        require_integer(count_value, "cache count", 0)
        if (
            self.max_cache_entries is not None
            and self.cache_entries + count_value > self.max_cache_entries
        ):
            raise BlockContextBudgetExceeded(
                f"block-effect memoization exceeded {self.max_cache_entries} retained entries"
            )
        self.cache_entries += count_value


BoundaryState: TypeAlias = object


class BoundarySide(IntEnum):
    LEFT = 0
    RIGHT = 1


class BlockEffect(Protocol):
    """Canonical executable algebra element for a powered pair block.

    A block effect owns one boundary-transition operation parameterized by
    direction rather than two duplicated left/right APIs.  ``compose`` and
    ``power`` return the same semantic type.
    """

    @property
    def base(self) -> int:
        raise NotImplementedError

    @property
    def blank(self) -> int:
        raise NotImplementedError

    @property
    def exponent(self) -> int:
        raise NotImplementedError

    @property
    def node_id(self) -> int:
        raise NotImplementedError

    @property
    def blank_left_tail(self) -> int:
        raise NotImplementedError

    @property
    def blank_right_tail(self) -> int:
        raise NotImplementedError

    @property
    def stable_blank_output(self) -> bool:
        raise NotImplementedError

    @property
    def supports_predecessor_trace(self) -> bool:
        raise NotImplementedError

    def boundary_universe(
        self, side: BoundarySide
    ) -> tuple[BoundaryState, ...] | None: ...
    def initial(self, side: BoundarySide) -> BoundaryState: ...
    def advance(
        self, side: BoundarySide, state: BoundaryState, symbol: int
    ) -> BoundaryState: ...
    def emit(self, left: BoundaryState, symbol: int, right: BoundaryState) -> int: ...
    def predecessor(
        self, side: BoundarySide, state: BoundaryState
    ) -> BoundaryState | None: ...
    def operator_nodes(self) -> int: ...
    def runtime_stats(self) -> dict[str, int]: ...


class BlockEffectAdmissionAdapter(Protocol):
    """Explicit family-owned admission for one exact immutable effect type."""

    @property
    def effect_type(self) -> type[BlockEffect]: ...

    @property
    def compatibility_type(self) -> type[BlockEffect] | None: ...

    def owns_effect(self, effect: BlockEffect) -> bool: ...

    def clone(self, effect: BlockEffect) -> BlockEffect: ...

    def owns_compatibility(self, effect: BlockEffect) -> bool: ...

    def validate_compatibility(self, effect: BlockEffect) -> None: ...


_OPERATOR_IDS = count(1)
_CONTEXT_IDS = count(1)


def next_context_id() -> int:
    """Allocate a context identity while retaining ownership of the counter."""
    return next(_CONTEXT_IDS)


def next_operator_id() -> int:
    """Allocate a compatibility/display node ID from the shared sequence."""
    return next(_OPERATOR_IDS)


__all__ = [
    "BlockContextBudget",
    "BlockContextBudgetExceeded",
    "BlockEffect",
    "BlockEffectAdmissionAdapter",
    "BoundarySide",
    "BoundaryState",
    "_cache_state_key",
    "_effect_key",
    "_state_key",
    "next_operator_id",
]
