"""Exact subsequential radix-word transducers for accelerated Collatz.

In radix four the 2-adic residue ``-1/3`` is the infinite LSF word ``111...``.
An accelerated odd step therefore skips a run of input digit ``1`` and then
uses only one of two bounded arithmetic modes:

* first non-1 digit 0 or 2: ``3*m+1``;
* first non-1 digit 3: ``(3*m+1)/2``.

Outputs may be empty while the sentinel run is skipped, so the natural object
is a deterministic *subsequential* transducer rather than a synchronous Mealy
machine.  Such transducers compose exactly: an output word of the first machine
is fed immediately through the second machine.  This module lets the powered
research path test the automaton closure directly without materializing Collatz
carry vectors or parity runs.
"""

from __future__ import annotations

from collections import deque
from collections.abc import Callable, Hashable, Mapping, Sequence
from dataclasses import dataclass
from typing import Literal, TypeVar

from number_compiler.arithmetic.fields.digit_formula import synthesize_multiply_add
from number_compiler.arithmetic.fields.radix import bit_width, digits_lsd

StateT = TypeVar("StateT", bound=Hashable)
CollatzState = (
    tuple[Literal["S"]] | tuple[Literal["M"], int] | tuple[Literal["H"], int, int]
)

Word = tuple[int, ...]


@dataclass(frozen=True, slots=True)
class SubsequentialDigitTransducer:
    base: int
    states: tuple[int, ...]
    start_state: int
    transition: Mapping[tuple[int, int], tuple[int, Word]]
    final_output: Mapping[int, Word]
    name: str = "subsequential"

    def __post_init__(self) -> None:
        if self.base < 2 or self.start_state not in self.states:
            raise ValueError((self.base, self.start_state))
        state_set = set(self.states)
        for q in self.states:
            if q not in self.final_output:
                raise ValueError(("missing final output", q))
            for d in range(self.base):
                if (q, d) not in self.transition:
                    raise ValueError(("missing transition", q, d))
                nq, out = self.transition[q, d]
                if nq not in state_set or any(not 0 <= x < self.base for x in out):
                    raise ValueError((q, d, nq, out))
            if any(not 0 <= x < self.base for x in self.final_output[q]):
                raise ValueError((q, self.final_output[q]))

    def run_from(self, state: int, word: Sequence[int]) -> tuple[int, Word]:
        q = int(state)
        out: list[int] = []
        for digit in word:
            q, emitted = self.transition[q, int(digit)]
            out.extend(emitted)
        return q, tuple(out)

    def apply_digits(self, digits: Sequence[int]) -> Word:
        q, out = self.run_from(self.start_state, digits)
        result = list(out)
        result.extend(self.final_output[q])
        while len(result) > 1 and result[-1] == 0:
            result.pop()
        return tuple(result)

    def description_bits(self) -> int:
        sid = bit_width(len(self.states))
        digit = bit_width(self.base - 1)
        total = bit_width(self.base) + bit_width(len(self.states))
        for q in self.states:
            final = self.final_output[q]
            total += bit_width(len(final)) + len(final) * digit
            for d in range(self.base):
                _nq, out = self.transition[q, d]
                total += sid + bit_width(len(out)) + len(out) * digit
        return total


def _canonicalize(
    base: int,
    start_label: StateT,
    step: Callable[[StateT, int], tuple[StateT, Word]],
    finish: Callable[[StateT], Word],
    *,
    name: str,
) -> SubsequentialDigitTransducer:
    labels = [start_label]
    ids = {start_label: 0}
    queue = deque([start_label])
    raw_trans: dict[tuple[StateT, int], tuple[StateT, Word]] = {}
    while queue:
        q = queue.popleft()
        for digit in range(base):
            nq, out = step(q, digit)
            raw_trans[q, digit] = nq, tuple(map(int, out))
            if nq not in ids:
                ids[nq] = len(labels)
                labels.append(nq)
                queue.append(nq)
    trans: dict[tuple[int, int], tuple[int, Word]] = {}
    finals: dict[int, Word] = {}
    for label in labels:
        local_id = ids[label]
        finals[local_id] = tuple(map(int, finish(label)))
        for digit in range(base):
            nq, out = raw_trans[label, digit]
            trans[local_id, digit] = ids[nq], out
    return SubsequentialDigitTransducer(
        base, tuple(range(len(labels))), 0, trans, finals, name
    )


def collatz_accelerated_radix4_transducer() -> SubsequentialDigitTransducer:
    """Exact accelerated Collatz map on positive odd canonical radix-4 words."""
    mul = synthesize_multiply_add(4, 3, 1)

    # labels: ('S',) skip sentinel 1s; ('M',carry) 3*m+1; ('H',carry,prev)
    # (3*m+1)/2 with one normalized product digit delayed.
    start: CollatzState = ("S",)

    def step(state: CollatzState, digit: int) -> tuple[CollatzState, Word]:
        if state[0] == "S":
            if digit == 1:
                return state, ()
            carry, product_digit = mul.transition[mul.start_state, digit]
            if digit in (0, 2):
                return ("M", int(carry)), (int(product_digit),)
            if digit == 3:
                return ("H", int(carry), int(product_digit)), ()
            raise AssertionError(digit)
        if state[0] == "M":
            carry = int(state[1])
            nxt, product_digit = mul.transition[carry, digit]
            return ("M", int(nxt)), (int(product_digit),)
        if state[0] == "H":
            carry, previous = int(state[1]), int(state[2])
            nxt, product_digit = mul.transition[carry, digit]
            quotient_digit = previous // 2 + 2 * (int(product_digit) & 1)
            return ("H", int(nxt), int(product_digit)), (quotient_digit,)
        raise AssertionError(state)

    def finish(state: CollatzState) -> Word:
        if state[0] == "S":
            # Finite input all 1s: n=(4**q-1)/3 -> accelerated target 1.
            return (1,)
        if state[0] == "M":
            carry = int(state[1])
            return () if carry == 0 else (carry,)
        if state[0] == "H":
            carry, previous = int(state[1]), int(state[2])
            high = carry  # carry is already one canonical radix-4 product digit.
            low_q = previous // 2 + 2 * (high & 1)
            high_q = high // 2
            if high_q:
                return (low_q, high_q)
            return (low_q,)
        raise AssertionError(state)

    return _canonicalize(4, start, step, finish, name="collatz_accel_radix4")


def compose_subsequential(
    first: SubsequentialDigitTransducer,
    second: SubsequentialDigitTransducer,
    *,
    name: str | None = None,
) -> SubsequentialDigitTransducer:
    """Return ``second o first`` by exact deterministic word feeding."""
    if first.base != second.base:
        raise ValueError((first.base, second.base))
    base = first.base
    start = (first.start_state, second.start_state)

    def feed_second(state: int, word: Word) -> tuple[int, Word]:
        return second.run_from(state, word)

    def step(state: tuple[int, int], digit: int) -> tuple[tuple[int, int], Word]:
        q1, q2 = map(int, state)
        n1, out1 = first.transition[q1, digit]
        n2, out2 = feed_second(q2, out1)
        return (int(n1), int(n2)), out2

    def finish(state: tuple[int, int]) -> Word:
        q1, q2 = map(int, state)
        q2_after, out = feed_second(q2, first.final_output[q1])
        return tuple(out) + tuple(second.final_output[q2_after])

    return _canonicalize(
        base,
        start,
        step,
        finish,
        name=name or f"({second.name})o({first.name})",
    )


def power_subsequential(
    transducer: SubsequentialDigitTransducer, exponent: int
) -> SubsequentialDigitTransducer:
    """Binary-compose a positive power of a subsequential transducer."""
    exponent = int(exponent)
    if exponent <= 0:
        raise ValueError("positive powers only")
    result: SubsequentialDigitTransducer | None = None
    base = transducer
    n = exponent
    while n:
        if n & 1:
            result = base if result is None else compose_subsequential(result, base)
        n >>= 1
        if n:
            base = compose_subsequential(base, base)
    if result is None:
        raise AssertionError(exponent)
    return result


def apply_accelerated_reference(value: int, steps: int) -> int:
    value, steps = int(value), int(steps)
    if value <= 0 or not (value & 1) or steps < 0:
        raise ValueError((value, steps))
    for _ in range(steps):
        if value == 1:
            return 1
        m = 3 * value + 1
        value = m >> ((m & -m).bit_length() - 1)
    return value


def apply_transducer_value(transducer: SubsequentialDigitTransducer, value: int) -> int:
    digits = transducer.apply_digits(digits_lsd(int(value), transducer.base))
    return sum(d * transducer.base**i for i, d in enumerate(digits))


__all__ = [
    "SubsequentialDigitTransducer",
    "apply_accelerated_reference",
    "apply_transducer_value",
    "collatz_accelerated_radix4_transducer",
    "compose_subsequential",
    "power_subsequential",
]


def minimize_aligned_subsequential(
    transducer: SubsequentialDigitTransducer,
) -> SubsequentialDigitTransducer:
    """Exact Moore-style quotient for output-aligned subsequential states.

    States are merged only when they have identical final output and, for every
    digit, identical immediate output and equivalent successor.  This is a
    fail-safe behavioral quotient: it never uses sampled continuation words or
    output-delay identities.
    """
    states = tuple(transducer.states)
    cls = {q: 0 for q in states}
    while True:
        keys: dict[tuple[Word, tuple[tuple[Word, int], ...]], int] = {}
        next_cls = {}
        for q in states:
            key = (
                tuple(transducer.final_output[q]),
                tuple(
                    (
                        tuple(transducer.transition[q, d][1]),
                        cls[transducer.transition[q, d][0]],
                    )
                    for d in range(transducer.base)
                ),
            )
            cid = keys.setdefault(key, len(keys))
            next_cls[q] = cid
        if all(next_cls[q] == cls[q] for q in states) and len(
            set(next_cls.values())
        ) == len(set(cls.values())):
            cls = next_cls
            break
        # Class numbers can permute, so compare pairwise equivalence instead.
        stable = all(
            (cls[a] == cls[b]) == (next_cls[a] == next_cls[b])
            for a in states
            for b in states
        )
        cls = next_cls
        if stable:
            break

    classes: dict[int, list[int]] = {}
    for q, c in cls.items():
        classes.setdefault(c, []).append(q)
    start_class = cls[transducer.start_state]
    # Canonical BFS over quotient classes.
    labels = [start_class]
    ids = {start_class: 0}
    queue = deque([start_class])
    transition: dict[tuple[int, int], tuple[int, Word]] = {}
    finals: dict[int, Word] = {}
    while queue:
        c = queue.popleft()
        rep = min(classes[c])
        qid = ids[c]
        finals[qid] = tuple(transducer.final_output[rep])
        for d in range(transducer.base):
            nq, out = transducer.transition[rep, d]
            nc = cls[nq]
            if nc not in ids:
                ids[nc] = len(labels)
                labels.append(nc)
                queue.append(nc)
            transition[qid, d] = ids[nc], tuple(out)
    return SubsequentialDigitTransducer(
        transducer.base,
        tuple(range(len(labels))),
        0,
        transition,
        finals,
        transducer.name + "_aligned_min",
    )


__all__.append("minimize_aligned_subsequential")
