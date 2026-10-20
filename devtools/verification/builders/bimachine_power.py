"""Direct classical-bimachine powering experiment for reverse/add pair halves.

Implements the direct composition construction of Mihov/Schulz §6.4 for a
small exact pair-half bimachine.  Research-only until state-growth measurements
justify promotion into the guarded full-J backend.
"""

from __future__ import annotations

import random
import time
from collections import deque
from collections.abc import Callable, Hashable, Iterable, Mapping, Sequence
from collections.abc import Set as AbstractSet
from dataclasses import dataclass
from functools import partial
from typing import Generic, Literal, Protocol, TypeVar, cast

from devtools.verification.partition_refinement import (
    partition_representatives,
    stable_partition,
)
from devtools.verification.random_inputs import random_half
from devtools.verification.reverse_pair_reference import reference_pair_half
from devtools.verification.transducer_graph import DenseInterner, determinize_subsets
from number_compiler.arithmetic.automata.transducer import (
    enqueue_pair_parity_transitions,
    pair_half_coefficient,
    pair_left_context,
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

State_co = TypeVar("State_co", covariant=True)
StateT = TypeVar("StateT")

LeftState = tuple[Literal["S", "D"]] | tuple[Literal["V"], int, int, int, int]

RightState = tuple[Literal["S", "D"]] | tuple[Literal["A"], int, int, int]


def scan_word(
    q: int | None,
    word: Sequence[int],
    right: bool,
    step: Callable[[int, int], int | None],
) -> int | None:
    sequence = reversed(tuple(word)) if right else word
    for symbol in sequence:
        if q is None:
            return None
        q = step(q, symbol)
        if q is None:
            return None
    return q


def lab(s: int, b: int) -> int:
    t = b - 1
    return R0 if s < t else (I if s == t else R1)


def carry_label(m: int) -> int:
    return int(m == R1)


def compose_label(a: int, b: int) -> int:
    return b if b != I else a


def ptag(p: int, b: int) -> int:
    return 2 * b - 1 + p


def endtag(b: int) -> int:
    return 2 * b + 1


def first_nonI(*xs: int) -> int:
    for x in xs:
        if x != I:
            return x
    return I


@dataclass
class DFA(Generic[State_co]):
    alphabet: tuple[int, ...]
    start: int
    trans: dict[tuple[int, int], int]
    states: tuple[int, ...]
    data: Mapping[int, State_co]
    right: bool = False

    def step(self, q: int, a: int) -> int | None:
        return self.trans.get((q, a))

    def word(self, q: int | None, w: Sequence[int]) -> int | None:
        return scan_word(q, w, self.right, self.step)


@dataclass
class Bimachine:
    base: int
    alphabet: tuple[int, ...]
    left: DFA[object]
    right: DFA[object]
    out: dict[tuple[int, int, int], tuple[int, ...]]

    def output(self, word: Sequence[int]) -> tuple[int, ...]:
        w = tuple(word)
        n = len(w)
        ls = [self.left.start]
        for a in w:
            q = self.left.step(ls[-1], a)
            if q is None:
                raise ValueError(("left reject", a, ls[-1]))
            ls.append(q)
        rs = [0] * (n + 1)
        rs[n] = self.right.start
        for i in range(n - 1, -1, -1):
            q = self.right.step(rs[i + 1], w[i])
            if q is None:
                raise ValueError(("right reject", w[i], rs[i + 1]))
            rs[i] = q
        z: list[int] = []
        for i, a in enumerate(w):
            o = self.out.get((ls[i], a, rs[i + 1]))
            if o is None:
                raise ValueError(
                    (
                        "undefined output",
                        self.left.data[ls[i]],
                        a,
                        self.right.data[rs[i + 1]],
                    )
                )
            z.extend(o)
        return tuple(z)


def build_step(base: int = 10) -> Bimachine:
    b = base
    vals = tuple(range(2 * b - 1))
    P0, P1 = ptag(0, b), ptag(1, b)
    E = endtag(b)
    alphabet = vals + (P0, P1, E)
    # LEFT DFA. data: ('S',) ; ('V',p,first,last,prev) ; ('D',)
    left_interner = _StateInterner[LeftState]()
    ldata = left_interner.data
    lt: dict[tuple[int, int], int] = {}

    L = left_interner.intern

    sL = L(("S",))
    done = L(("D",))
    dq = deque([sL])
    seen: set[int] = set()
    while dq:
        q = dq.popleft()
        if q in seen:
            continue
        seen.add(q)
        d: LeftState | RightState = ldata[q]
        if d[0] == "S":
            enqueue_pair_parity_transitions(L, lt, dq, q, P0, P1)
        elif d[0] == "V":
            _, p, first, last, prev = d
            for s in vals:
                z = L(cast(LeftState, pair_left_context(p, first, last, s, b)))
                lt[q, s] = z
                dq.append(z)
            lt[q, E] = done
    left = DFA(
        alphabet, sL, lt, tuple(range(len(ldata))), {i: d for i, d in enumerate(ldata)}
    )

    # RIGHT DFA scans from END backwards. data:
    # ('S',) empty suffix after whole word; ('A',seen,center,first_excl);
    # ('D',) after parity.
    right_interner = _StateInterner[RightState]()
    rdata = right_interner.data
    rt: dict[tuple[int, int], int] = {}

    R = right_interner.intern

    sR = R(("S",))
    after = R(("A", 0, I, I))
    rdone = R(("D",))
    rt[sR, E] = after
    dq = deque([after])
    seen = set()
    while dq:
        q = dq.popleft()
        if q in seen:
            continue
        seen.add(q)
        current = rdata[q]
        assert current[0] == "A"
        _, seenval, center, firstex = current
        for s in vals:
            m = lab(s, b)
            if not seenval:
                nd: RightState = ("A", 1, m, I)
            else:
                nd = ("A", 1, center, m if m != I else firstex)
            z = R(nd)
            rt[q, s] = z
            dq.append(z)
        # Once all values have been scanned, the parity tag is consumed.
        rt[q, P0] = rdone
        rt[q, P1] = rdone
    right = DFA(
        alphabet,
        sR,
        rt,
        tuple(range(len(rdata))),
        {i: d for i, d in enumerate(rdata)},
        right=True,
    )

    out: dict[tuple[int, int, int], tuple[int, ...]] = {}
    # Output parity tag using entire suffix summary in right state.
    for p, a in ((0, P0), (1, P1)):
        for r in right.states:
            d = right.data[r]
            if d[0] != "A" or not d[1]:
                continue
            _, _, center, firstex = d
            fa = firstex if firstex != I else center
            g = int(fa == R1)
            out[sL, a, r] = (ptag(p ^ g, b),)
    # Value outputs.
    for states_left_state in left.states:
        ld = left.data[states_left_state]
        if ld[0] != "V":
            continue
        _, p, firstpre, lastpre, prev = ld
        for s in vals:
            for r in right.states:
                rd = right.data[r]
                if rd[0] != "A":
                    continue
                _, seenval, center, firstex = rd
                y = pair_half_coefficient(
                    p, firstpre, lastpre, prev, seenval, center, firstex, s, b
                )
                if y is not None:
                    out[states_left_state, s, r] = (y,)
    # END output. r_after END is the right start state.
    for states_left_state in left.states:
        ld = left.data[states_left_state]
        if ld[0] != "V" or ld[4] == -1:
            continue
        _, p, first, last, prev = ld
        g = int(first == R1)
        extra: list[int] = []
        if p == 0 and g:
            Lh = carry_label(last)
            nextc = 0 if prev < b - 1 else (Lh if prev == b - 1 else 1)
            center = 2 * prev + 2 * Lh - 2 * b * nextc
            if not 0 <= center <= 2 * (b - 1):
                continue
            extra.append(center)
        out[states_left_state, E, sR] = tuple(extra + [E])
    return Bimachine(b, alphabet, left, right, out)


def ref(
    parity: int, half: list[int] | tuple[int, ...] | tuple[int, int], b: int = 10
) -> tuple[int, tuple[int, ...]]:
    return reference_pair_half(
        parity,
        half,
        b,
        lambda symbol, incoming, threshold: (
            0 if symbol < threshold else incoming if symbol == threshold else 1
        ),
    )


def encode(p: int, h: Sequence[int], b: int = 10) -> tuple[int, ...]:
    return (ptag(p, b),) + tuple(h) + (endtag(b),)


def decode(w: Sequence[int], b: int = 10) -> tuple[int, tuple[int, ...]]:
    assert w[-1] == endtag(b)
    return w[0] - (2 * b - 1), tuple(w[1:-1])


# Determinize an NFA over triples. NFA transitions are represented by adjacency
# mapping (state,a)->set(next). Only reachable subsets are kept.
def determinize(
    alphabet: tuple[int, ...],
    startset: Iterable[int],
    nfa_trans: Mapping[tuple[int, int], AbstractSet[int]],
    data: Sequence[object],
    right: bool = False,
) -> DFA[frozenset[int]]:
    start, trans, subsets = determinize_subsets(alphabet, startset, nfa_trans)
    return DFA(
        alphabet,
        start,
        trans,
        tuple(range(len(subsets))),
        {i: subsets[i] for i in range(len(subsets))},
        right=right,
    )


def reachable_nfa(
    starts: Iterable[int],
    successors: Callable[[int], Iterable[tuple[int, int]]],
) -> dict[tuple[int, int], set[int]]:
    """Collect reachable labelled NFA edges from a finite start set."""
    transitions: dict[tuple[int, int], set[int]] = {}
    queue = deque(starts)
    seen: set[int] = set()
    while queue:
        state = queue.popleft()
        if state in seen:
            continue
        seen.add(state)
        for symbol, target in successors(state):
            transitions.setdefault((state, symbol), set()).add(target)
            if target not in seen:
                queue.append(target)
    return transitions


def predecessor_index(
    states: Iterable[int],
    alphabet: Iterable[int],
    step: Callable[[int, int], int | None],
) -> dict[int, dict[int, list[int]]]:
    """Index finite automaton predecessors by symbol and target state."""
    result: dict[int, dict[int, list[int]]] = {symbol: {} for symbol in alphabet}
    for state in states:
        for symbol, targets in result.items():
            target = step(state, symbol)
            if target is not None:
                targets.setdefault(target, []).append(state)
    return result


TripleInterner = DenseInterner


class _StateInterner(Generic[StateT]):
    def __init__(self) -> None:
        self.data: list[StateT] = []
        self.ids: dict[StateT, int] = {}

    def intern(self, state: StateT) -> int:
        old = self.ids.get(state)
        if old is not None:
            return old
        result = len(self.data)
        self.ids[state] = result
        self.data.append(state)
        return result


def _intern_composed_transition(
    symbol: int,
    state: tuple[int, int, int] | None,
    intern: Callable[[tuple[int, int, int]], int],
) -> tuple[int, int] | None:
    if state is None:
        return None
    return symbol, intern(state)


def _compose_successors(
    triple: tuple[int, int, int],
    alphabet: Iterable[int],
    predecessor: Mapping[int, Mapping[int, Iterable[int]]],
    step: Callable[[int, int], int | None],
    emit_candidate: Callable[[int, int, int], Sequence[int] | None],
    consume: Callable[[int, Sequence[int]], int | None],
    intern: Callable[[tuple[int, int, int]], int],
    decode: Callable[[tuple[int, int, int]], tuple[int, int, int]],
    encode: Callable[[int, int, int, int], tuple[int, int, int]],
) -> Iterable[tuple[int, int]]:
    base, key, downstream = decode(triple)
    for symbol in alphabet:
        next_base = step(base, symbol)
        if next_base is None:
            continue
        for candidate in predecessor.get(symbol, {}).get(key, ()):
            word = emit_candidate(base, symbol, candidate)
            if word is None:
                continue
            next_downstream = consume(downstream, word)
            transition = _intern_composed_transition(
                symbol,
                None
                if next_downstream is None
                else encode(next_base, candidate, next_downstream, base),
                intern,
            )
            if transition is not None:
                yield transition


def composed_left_successors(
    qi: int,
    triples: Sequence[tuple[int, int, int]],
    alphabet: Iterable[int],
    left_step: Callable[[int, int], int | None],
    right_predecessors: Mapping[int, Mapping[int, Iterable[int]]],
    emit: Callable[[int, int, int], Sequence[int] | None],
    consume: Callable[[int, Sequence[int]], int | None],
    intern: Callable[[tuple[int, int, int]], int],
) -> Iterable[tuple[int, int]]:
    """Yield left NFA composition edges for eager and lazy bimachines."""
    yield from _compose_successors(
        triples[qi],
        alphabet,
        right_predecessors,
        left_step,
        emit,
        consume,
        intern,
        lambda triple: (triple[0], triple[1], triple[2]),
        lambda next_base, candidate, downstream, _base: (
            next_base,
            candidate,
            downstream,
        ),
    )


def composed_right_successors(
    qi: int,
    triples: Sequence[tuple[int, int, int]],
    alphabet: Iterable[int],
    left_predecessors: Mapping[int, Mapping[int, Iterable[int]]],
    right_step: Callable[[int, int], int | None],
    emit: Callable[[int, int, int], Sequence[int] | None],
    consume: Callable[[int, Sequence[int]], int | None],
    intern: Callable[[tuple[int, int, int]], int],
) -> Iterable[tuple[int, int]]:
    """Yield right NFA composition edges for eager and lazy bimachines."""
    yield from _compose_successors(
        triples[qi],
        alphabet,
        left_predecessors,
        right_step,
        lambda base, symbol, candidate: emit(candidate, symbol, base),
        consume,
        intern,
        lambda triple: (triple[1], triple[0], triple[2]),
        lambda next_base, candidate, downstream, _base: (
            candidate,
            next_base,
            downstream,
        ),
    )


def compose_contexts(
    alphabet: Sequence[int],
    first_left_states: Sequence[int],
    first_right_states: Sequence[int],
    first_left_start: int,
    first_right_start: int,
    second_left_start: int,
    second_right_start: int,
    first_left_step: Callable[[int, int], int | None],
    first_right_step: Callable[[int, int], int | None],
    second_left_word: Callable[[int, Sequence[int]], int | None],
    second_right_word: Callable[[int, Sequence[int]], int | None],
    emit: Callable[[int, int, int], Sequence[int] | None],
) -> tuple[
    DFA[frozenset[int]],
    DFA[frozenset[int]],
    list[tuple[int, int, int]],
    list[tuple[int, int, int]],
]:
    """Build both finite context automata for eager and lazy composers."""
    alphabet_tuple = tuple(alphabet)
    left_triples: DenseInterner[tuple[int, int, int]] = TripleInterner()
    left_values = left_triples.values
    left_id = left_triples.intern
    left_start_set = {
        left_id((first_left_start, right, second_left_start))
        for right in first_right_states
    }
    right_predecessors = predecessor_index(
        first_right_states, alphabet_tuple, first_right_step
    )
    left_successors = partial(
        composed_left_successors,
        triples=left_values,
        alphabet=alphabet_tuple,
        left_step=first_left_step,
        right_predecessors=right_predecessors,
        emit=emit,
        consume=second_left_word,
        intern=left_id,
    )
    left_nfa = reachable_nfa(left_start_set, left_successors)
    left = determinize(
        alphabet_tuple, left_start_set, left_nfa, left_values, right=False
    )

    right_triples: DenseInterner[tuple[int, int, int]] = TripleInterner()
    right_values = right_triples.values
    right_id = right_triples.intern
    right_start_set = {
        right_id((left, first_right_start, second_right_start))
        for left in first_left_states
    }
    left_predecessors = predecessor_index(
        first_left_states, alphabet_tuple, first_left_step
    )
    right_successors = partial(
        composed_right_successors,
        triples=right_values,
        alphabet=alphabet_tuple,
        left_predecessors=left_predecessors,
        right_step=first_right_step,
        emit=emit,
        consume=second_right_word,
        intern=right_id,
    )
    right_nfa = reachable_nfa(right_start_set, right_successors)
    right = determinize(
        alphabet_tuple, right_start_set, right_nfa, right_values, right=True
    )
    return left, right, left_values, right_values


def compose_bimachine(B1: Bimachine, B2: Bimachine) -> Bimachine:
    assert B1.alphabet == B2.alphabet
    A = B1.alphabet
    left, right, LT, RT = compose_contexts(
        A,
        B1.left.states,
        B1.right.states,
        B1.left.start,
        B1.right.start,
        B2.left.start,
        B2.right.start,
        B1.left.step,
        B1.right.step,
        B2.left.word,
        B2.right.word,
        lambda left_state, a, r: B1.out.get((left_state, a, r)),
    )

    # Output function. Search compatible witnesses; theorem guarantees uniqueness.
    out: dict[tuple[int, int, int], tuple[int, ...]] = {}
    for Ls in left.states:
        LA = left.data[Ls]
        for a in A:
            Lnext = left.step(Ls, a)
            if Lnext is None:
                continue
            for Rs in right.states:
                RB = right.data[Rs]  # right state after current symbol
                candidates: set[tuple[int, ...]] = set()
                for xid in LA:
                    l1, r1, l2 = LT[xid]
                    l1n = B1.left.step(l1, a)
                    if l1n is None:
                        continue
                    for yid in RB:
                        l1b, r1b, r2b = RT[yid]
                        if l1b != l1n:
                            continue
                        # RB tuple is (l1_after, r1_after, r2_after)
                        r1_after = r1b
                        if B1.right.step(r1_after, a) != r1:
                            continue
                        v = B1.out.get((l1, a, r1_after))
                        if v is None:
                            continue
                        # l2 before output is in LA; r2 after output is r2b
                        w = eval_bimachine_fragment(
                            cast(FragmentMachine, B2), l2, v, r2b
                        )
                        if w is not None:
                            candidates.add(w)
                if len(candidates) > 1:
                    raise AssertionError(
                        ("ambiguous composed output", len(candidates), a, Ls, Rs)
                    )
                if candidates:
                    out[Ls, a, Rs] = next(iter(candidates))
    C = Bimachine(B1.base, A, left, right, out)
    return pseudo_minimize(C)


class _FragmentAutomaton(Protocol):
    def step(self, q: int, a: int) -> int | None: ...


class FragmentMachine(Protocol):
    left: _FragmentAutomaton
    right: _FragmentAutomaton
    out: Mapping[tuple[int, int, int], tuple[int, ...]]


def fragment_states(
    B: FragmentMachine, left_state: int, word: Sequence[int], r_after: int
) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
    w = tuple(word)
    ls = [left_state]
    for a in w:
        q = B.left.step(ls[-1], a)
        if q is None:
            return None
        ls.append(q)
    rs = [0] * (len(w) + 1)
    rs[len(w)] = r_after
    for i in range(len(w) - 1, -1, -1):
        q = B.right.step(rs[i + 1], w[i])
        if q is None:
            return None
        rs[i] = q
    return tuple(ls), tuple(rs)


def eval_bimachine_fragment(
    B: FragmentMachine, left_state: int, word: Sequence[int], r_after: int
) -> tuple[int, ...] | None:
    w = tuple(word)
    states = fragment_states(B, left_state, w, r_after)
    if states is None:
        return None
    ls, rs = states
    z: list[int] = []
    for i, a in enumerate(w):
        o = B.out.get((ls[i], a, rs[i + 1]))
        if o is None:
            return None
        z.extend(o)
    return tuple(z)


def minimize_colored(
    dfa: DFA[object], color: Callable[[int], Hashable]
) -> tuple[DFA[tuple[int, ...]], dict[int, int]]:
    qs = list(dfa.states)
    alphabet = dfa.alphabet

    def signature(q: int, previous: Mapping[int, int]) -> tuple[object, ...]:
        transitions: list[int] = []
        for a in alphabet:
            target = dfa.step(q, a)
            transitions.append(-1 if target is None else previous.get(target, -1))
        return color(q), tuple(transitions)

    part = stable_partition(
        qs,
        color,
        signature,
    )
    reps, cmap = partition_representatives(part)
    trans: dict[tuple[int, int], int] = {}
    for c, q in reps.items():
        nq = cmap[c]
        for a in alphabet:
            z = dfa.step(q, a)
            if z is not None:
                trans[nq, a] = cmap[part[z]]
    start = cmap[part[dfa.start]]
    data = {cmap[c]: tuple(q for q in qs if part[q] == c) for c in reps}
    return DFA(
        alphabet, start, trans, tuple(range(len(reps))), data, right=dfa.right
    ), {q: part[q] for q in qs}


def pseudo_minimize(machine: Bimachine) -> Bimachine:
    # Alternate coloured minimization to a fixed point. Colors encode the entire
    # currently fixed opposite-side output row/column, preserving the function.
    changed = True
    while changed:
        changed = False
        Rstates = machine.right.states

        def lc(
            left_state: int,
            machine: Bimachine = machine,
            Rstates: tuple[int, ...] = Rstates,
        ) -> tuple[tuple[int, ...] | None, ...]:
            return tuple(
                machine.out.get((left_state, a, r), None)
                for a in machine.alphabet
                for r in Rstates
            )

        Lnew, _lpart = minimize_colored(machine.left, lc)
        if len(Lnew.states) < len(machine.left.states):
            # representative old state per new class
            rep = {new: members[0] for new, members in Lnew.data.items()}
            out = {
                (nl, a, r): machine.out[(old, a, r)]
                for nl, old in rep.items()
                for a in machine.alphabet
                for r in Rstates
                if (old, a, r) in machine.out
            }
            machine = Bimachine(
                machine.base, machine.alphabet, Lnew, machine.right, out
            )
            changed = True
        Lstates = machine.left.states

        def rc(
            r: int, machine: Bimachine = machine, Lstates: tuple[int, ...] = Lstates
        ) -> tuple[tuple[int, ...] | None, ...]:
            return tuple(
                machine.out.get((left_state, a, r), None)
                for left_state in Lstates
                for a in machine.alphabet
            )

        Rnew, _rpart = minimize_colored(machine.right, rc)
        if len(Rnew.states) < len(machine.right.states):
            rep = {new: members[0] for new, members in Rnew.data.items()}
            out = {
                (left_state, a, nr): machine.out[(left_state, a, old)]
                for nr, old in rep.items()
                for left_state in Lstates
                for a in machine.alphabet
                if (left_state, a, old) in machine.out
            }
            machine = Bimachine(machine.base, machine.alphabet, machine.left, Rnew, out)
            changed = True
    return machine


def selftest() -> None:
    b = 10
    machine = build_step(b)
    print(
        "B1 L/R/out",
        len(machine.left.states),
        len(machine.right.states),
        len(machine.out),
        flush=True,
    )
    rng = random.Random(196)
    for _ in range(1000):
        p = rng.randrange(2)
        h = random_half(rng, 7)
        got = decode(machine.output(encode(p, h, b)), b)
        exp = ref(p, h, b)
        assert got == exp, (p, h, got, exp)
    powered = machine
    for e in range(1, 5):
        t = time.perf_counter()
        powered = compose_bimachine(powered, powered)
        dt = time.perf_counter() - t
        print(
            "pow",
            2**e,
            "L/R/out",
            len(powered.left.states),
            len(powered.right.states),
            len(powered.out),
            "sec",
            dt,
            flush=True,
        )
        for _ in range(100):
            p = rng.randrange(2)
            h = random_half(rng, 4)
            pp, hh = p, tuple(h)
            for __ in range(2**e):
                pp, hh = ref(pp, hh, b)
            got = decode(powered.output(encode(p, h, b)), b)
            assert got == (pp, hh), (e, p, h, got, (pp, hh))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(selftest))
