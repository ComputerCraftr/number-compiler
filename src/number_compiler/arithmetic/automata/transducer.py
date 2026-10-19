"""Exact finite-state pair-half transducer used by powered operator compilation.

This module is operator metadata, not semantic state.  It encodes one exact
reverse/add step on a symmetric pair half as a bimachine whose size is
independent of the represented digit width.
"""

from __future__ import annotations

from collections import deque
from collections.abc import Callable, MutableMapping, Sequence
from dataclasses import dataclass, field
from typing import (
    TYPE_CHECKING,
    Generic,
    Literal,
    TypeVar,
)

from number_compiler.arithmetic.carry.carry_labels import (
    IDENTITY as I,
)
from number_compiler.arithmetic.carry.carry_labels import (
    RESET_ONE as R1,
)
from number_compiler.arithmetic.carry.carry_labels import (
    RESET_ZERO as R0,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.decision import CanonicalOutputRelation


_MetricsT = TypeVar("_MetricsT")
_StateT = TypeVar("_StateT")


def _intern_dfa_state(
    data: _StateT, states: list[_StateT], identifiers: dict[_StateT, int]
) -> int:
    previous = identifiers.get(data)
    if previous is not None:
        return previous
    identifier = len(states)
    identifiers[data] = identifier
    states.append(data)
    return identifier


def dfa_word(
    step: Callable[[int, int], int | None],
    state: int,
    word: Sequence[int],
    *,
    right: bool = False,
) -> int | None:
    symbols = reversed(tuple(word)) if right else word
    current = int(state)
    for symbol in symbols:
        successor = step(current, int(symbol))
        if successor is None:
            return None
        current = successor
    return current


def _lab(s: int, base: int) -> int:
    t = base - 1
    return R0 if s < t else (I if s == t else R1)


def pair_half_coefficient(
    parity: int,
    first_pre: int,
    last_pre: int,
    prev: int,
    seen_value: int,
    center: int,
    first_excl: int,
    a: int,
    b: int,
) -> int | None:
    """Canonical bounded coefficient law for one paired bimachine context."""
    m = _lab(a, b)
    last_after = m if m != I else last_pre
    first_all = first_excl if first_excl != I else (center if seen_value else I)
    glob = first_pre if first_pre != I else (m if m != I else first_all)
    growth = int(glob == R1)
    li = _carry(last_pre)
    li1 = _carry(last_after)
    if parity == 0:
        rip1_lab = first_all if first_all != I else last_after
        ri_lab = m if m != I else (first_all if first_all != I else last_pre)
    else:
        if first_excl != I:
            rip1_lab = first_excl
        elif seen_value:
            rip1_lab = center if center != I else last_after
        else:
            rip1_lab = last_pre
        if m != I:
            ri_lab = m
        elif first_excl != I:
            ri_lab = first_excl
        elif seen_value and center != I:
            ri_lab = center
        else:
            ri_lab = last_pre
    ri = _carry(ri_lab)
    rip1 = _carry(rip1_lab)
    if not growth:
        y = 2 * a + li + rip1 - b * (li1 + ri)
    elif prev == -1:
        y = a + 1 - b * li1
    else:
        rim1 = 0 if prev < b - 1 else (ri if prev == b - 1 else 1)
        y = a + prev + li + ri - b * (li1 + rim1)
    return y if 0 <= y <= 2 * (b - 1) else None


def pair_left_context(
    parity: int, first: int, last: int, symbol: int, base: int
) -> tuple[str, int, int, int, int]:
    label = _lab(symbol, base)
    leading = first if first != I else label
    trailing = label if label != I else last
    return "V", parity, leading, trailing, symbol


def _carry(m: int) -> int:
    return int(m == R1)


def parity_tag(parity: int, base: int) -> int:
    return 2 * base - 1 + int(parity)


def end_tag(base: int) -> int:
    return 2 * base + 1


@dataclass(frozen=True, slots=True)
class DFA:
    alphabet: tuple[int, ...]
    start: int
    trans: dict[tuple[int, int], int]
    states: tuple[int, ...]
    right: bool = False

    def step(self, state: int, symbol: int) -> int | None:
        return self.trans.get((int(state), int(symbol)))

    def word(self, state: int, word: Sequence[int]) -> int | None:
        return dfa_word(self.step, state, word, right=self.right)


def bimachine_output(
    word: Sequence[int],
    left_start: int,
    left_step: Callable[[int, int], int | None],
    right_start: int,
    right_step: Callable[[int, int], int | None],
    emit: Callable[[int, int, int], tuple[int, ...] | None],
) -> tuple[int, ...]:
    """Evaluate canonical left/right context paths and emitted symbols once."""
    w = tuple(map(int, word))
    n = len(w)
    left = [left_start]
    for symbol in w:
        q = left_step(left[-1], symbol)
        if q is None:
            raise ValueError(("left reject", left[-1], symbol))
        left.append(q)
    right = [0] * (n + 1)
    right[n] = right_start
    for i in range(n - 1, -1, -1):
        q = right_step(right[i + 1], w[i])
        if q is None:
            raise ValueError(("right reject", right[i + 1], w[i]))
        right[i] = q
    out: list[int] = []
    for i, symbol in enumerate(w):
        z = emit(left[i], symbol, right[i + 1])
        if z is None:
            raise ValueError(("undefined output", left[i], symbol, right[i + 1]))
        out.extend(z)
    return tuple(out)


@dataclass(slots=True)
class LazyBimachine:
    base: int
    alphabet: tuple[int, ...]
    left: DFA
    right: DFA
    resolver: Callable[[int, int, int], tuple[int, ...] | None]
    cache_enabled: bool = True
    canonical_output: CanonicalOutputRelation | None = None

    def __post_init__(self) -> None:
        self._cache: dict[tuple[int, int, int], tuple[int, ...] | None] = {}

    # dataclass(slots=True) does not include post-init dynamic fields, so declare
    # it as a class annotation to make the slot.
    _cache: dict[tuple[int, int, int], tuple[int, ...] | None] = field(
        default_factory=dict, init=False
    )

    def emit(self, left: int, symbol: int, right: int) -> tuple[int, ...] | None:
        key = (int(left), int(symbol), int(right))
        relation = self.canonical_output
        if relation is not None:
            # Canonical semantic relation is authoritative.  Do not recreate a
            # parallel late tuple cache after quotienting/minimization.
            return relation.emit(*key)
        if self.cache_enabled and key in self._cache:
            return self._cache[key]
        out = self.resolver(*key)
        if self.cache_enabled:
            self._cache[key] = out
        return out

    def install_canonical_output(self, relation: CanonicalOutputRelation) -> None:
        """Install the exact canonical output relation and drop tuple-cache debt."""
        self.canonical_output = relation
        self._cache.clear()
        # Prevent future repopulation of a structurally duplicate context cache.
        self.cache_enabled = False

    @property
    def has_canonical_output(self) -> bool:
        return self.canonical_output is not None

    def clear_output_cache(self) -> None:
        self._cache.clear()

    @property
    def cached_outputs(self) -> int:
        return len(self._cache)

    def output(self, word: Sequence[int]) -> tuple[int, ...]:
        return bimachine_output(
            word,
            self.left.start,
            self.left.step,
            self.right.start,
            self.right.step,
            self.emit,
        )


@dataclass(slots=True)
class BimachineTransformResult(Generic[_MetricsT]):
    """Shared result wrapper for one bimachine transformation pass."""

    machine: LazyBimachine
    metrics: _MetricsT


class _BimachineBuilder:
    def __init__(self, base: int) -> None:
        self.base = int(base)
        if self.base < 2:
            raise ValueError(base)

    def build(self) -> LazyBimachine:
        from collections import deque

        b = self.base
        vals = tuple(range(2 * b - 1))
        p0, p1, end = parity_tag(0, b), parity_tag(1, b), end_tag(b)
        alphabet = vals + (p0, p1, end)

        # Left DFA data is kept only while constructing the output resolver.
        ldata: list[tuple[str, int, int, int, int]] = []
        lid: dict[tuple[str, int, int, int, int], int] = {}
        lt: dict[tuple[int, int], int] = {}

        def L(data: tuple[str, int, int, int, int]) -> int:
            return _intern_dfa_state(data, ldata, lid)

        start_l = L(("S", 0, 0, 0, 0))
        done_l = L(("D", 0, 0, 0, 0))
        todo = deque([start_l])
        seen: set[int] = set()
        while todo:
            q = todo.popleft()
            if q in seen:
                continue
            seen.add(q)
            data = ldata[q]
            if data[0] == "S":
                enqueue_pair_parity_transitions(L, lt, todo, q, p0, p1)
            elif data[0] == "V":
                _, parity, first, last, _prev = data
                for s in vals:
                    z = L(pair_left_context(parity, first, last, s, b))
                    lt[q, s] = z
                    todo.append(z)
                lt[q, end] = done_l
        left = DFA(alphabet, start_l, lt, tuple(range(len(ldata))), False)

        rdata: list[tuple[str, int, int, int]] = []
        rid: dict[tuple[str, int, int, int], int] = {}
        rt: dict[tuple[int, int], int] = {}

        def R(data: tuple[str, int, int, int]) -> int:
            return _intern_dfa_state(data, rdata, rid)

        start_r = R(("S", 0, 0, 0))
        after = R(("A", 0, I, I))
        done_r = R(("D", 0, 0, 0))
        rt[start_r, end] = after
        todo = deque([after])
        seen.clear()
        while todo:
            q = todo.popleft()
            if q in seen:
                continue
            seen.add(q)
            _, seen_value, center, first_excl = rdata[q]
            for s in vals:
                m = _lab(s, b)
                right_data = (
                    ("A", 1, m, I)
                    if not seen_value
                    else ("A", 1, center, m if m != I else first_excl)
                )
                z = R(right_data)
                rt[q, s] = z
                todo.append(z)
            rt[q, p0] = done_r
            rt[q, p1] = done_r
        right = DFA(alphabet, start_r, rt, tuple(range(len(rdata))), True)

        # The resolver outlives construction. Retain only immutable finite law
        # data, rather than the mutable worklists used to discover its states.
        left_data = tuple(ldata)
        frozen_right_data = tuple(rdata)

        def emit(left_state: int, a: int, r: int) -> tuple[int, ...] | None:
            ld = left_data[left_state]
            rd = frozen_right_data[r]
            if left_state == start_l and a in (p0, p1) and rd[0] == "A" and rd[1]:
                parity = a - (2 * b - 1)
                _, _, center, first_excl = rd
                fa = first_excl if first_excl != I else center
                return (parity_tag(parity ^ int(fa == R1), b),)
            if ld[0] == "V" and a in vals and rd[0] == "A":
                _, parity, first_pre, last_pre, prev = ld
                _, seen_value, center, first_excl = rd
                output = pair_half_coefficient(
                    parity,
                    first_pre,
                    last_pre,
                    prev,
                    seen_value,
                    center,
                    first_excl,
                    a,
                    b,
                )
                return None if output is None else (output,)
            if a == end and r == start_r and ld[0] == "V" and ld[4] != -1:
                _, parity, first, last, prev = ld
                growth = int(first == R1)
                extra: list[int] = []
                if parity == 0 and growth:
                    lh = _carry(last)
                    next_carry = 0 if prev < b - 1 else (lh if prev == b - 1 else 1)
                    center = 2 * prev + 2 * lh - 2 * b * next_carry
                    if not 0 <= center <= 2 * (b - 1):
                        return None
                    extra.append(center)
                return tuple(extra + [end])
            return None

        return LazyBimachine(b, alphabet, left, right, emit, cache_enabled=True)


def build_pair_step_bimachine(base: int = 10) -> LazyBimachine:
    return _BimachineBuilder(base).build()


def encode_pair_half(
    parity: int, half: Sequence[int], base: int = 10
) -> tuple[int, ...]:
    return (parity_tag(parity, base),) + tuple(map(int, half)) + (end_tag(base),)


def decode_pair_half(
    word: Sequence[int], base: int = 10
) -> tuple[int, tuple[int, ...]]:
    w = tuple(map(int, word))
    if not w or w[-1] != end_tag(base):
        raise ValueError("invalid pair-half encoding")
    parity = w[0] - (2 * base - 1)
    if parity not in (0, 1):
        raise ValueError("invalid parity tag")
    return parity, tuple(w[1:-1])


__all__ = [
    "DFA",
    "BimachineTransformResult",
    "LazyBimachine",
    "build_pair_step_bimachine",
    "decode_pair_half",
    "encode_pair_half",
    "end_tag",
    "parity_tag",
]


def enqueue_dfa_transition(
    transitions: MutableMapping[tuple[int, int], int],
    queue: deque[int],
    state: int,
    symbol: int,
    target: int,
) -> None:
    """Publish an admitted transition and schedule its destination for traversal."""
    transitions[state, symbol] = target
    queue.append(target)


def transduction_midpoints(
    forward: Callable[[int, int], int | None],
    reverse: Callable[[int, int], int | None],
    left: int,
    right: int,
    left_context: int,
    right_context: int,
) -> tuple[int, int]:
    """Resolve both midpoint contexts in chronological order before child output."""
    left_mid = forward(left, left_context)
    right_mid = reverse(right, right_context)
    if left_mid is None or right_mid is None:
        raise ValueError("context reject")
    return left_mid, right_mid


def enqueue_pair_parity_transitions(
    intern: Callable[[tuple[Literal["V"], int, int, int, int]], int],
    transitions: MutableMapping[tuple[int, int], int],
    queue: deque[int],
    state: int,
    parity_zero: int,
    parity_one: int,
) -> None:
    """Introduce the two tagged pair contexts with identity carry boundaries."""
    for parity, tag in ((0, parity_zero), (1, parity_one)):
        target = intern(("V", parity, I, I, -1))
        enqueue_dfa_transition(transitions, queue, state, tag, target)
