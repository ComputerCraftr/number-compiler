"""Lazy-output direct bimachine powering experiment.

Avoids materializing the cartesian output table of composed bimachines.  This is
research-only: it measures width-independent powered operator state growth.
"""

from __future__ import annotations

import random
import time
from collections import defaultdict
from collections.abc import Callable, Generator, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, Protocol, cast

# Reuse exact one-step construction/helpers from the verified experiment.
from devtools.verification.builders.bimachine_power import (
    _FragmentMachine,
    build_step,
    compose_contexts,
    decode,
    encode,
    fragment_states,
    ref,
)

if TYPE_CHECKING:
    from devtools.verification.builders.bimachine_power import Bimachine


class ScanAutomaton(Protocol):
    """Finite scan contract, independent of a proof state's concrete carrier."""

    @property
    def alphabet(self) -> tuple[int, ...]: ...
    @property
    def start(self) -> int: ...
    @property
    def states(self) -> tuple[int, ...]: ...
    def step(self, q: int, a: int) -> int | None: ...
    def word(self, q: int | None, w: Sequence[int]) -> int | None: ...


Word = tuple[int, ...]


@dataclass(frozen=True)
class EmissionRequest:
    machine: LazyBimachine
    left: int
    symbol: int
    right: int

    @property
    def key(self) -> tuple[int, int, int]:
        return self.left, self.symbol, self.right


EmissionSteps = Generator[EmissionRequest, Word | None, Word | None]


@dataclass
class LazyBimachine:
    base: int
    alphabet: tuple[int, ...]
    left: ScanAutomaton
    right: ScanAutomaton
    resolver: Callable[[int, int, int], Word | None | EmissionSteps]
    _cache: dict[tuple[int, int, int], tuple[int, ...] | None]

    def emit(self, left_state: int, a: int, r: int) -> tuple[int, ...] | None:
        root = EmissionRequest(self, left_state, a, r)
        stack = [_EmissionFrame(root)]
        active = {(id(self), root.key)}
        while stack:
            frame = stack[-1]
            request = frame.request
            machine, key = request.machine, request.key
            if key in machine._cache:
                stack.pop()
                active.remove((id(machine), key))
                continue
            if frame.steps is None:
                response = machine.resolver(*key)
                if not isinstance(response, Generator):
                    machine._cache[key] = response
                    continue
                frame.steps = response
            try:
                dependency = (
                    next(frame.steps)
                    if frame.dependency is None
                    else frame.steps.send(
                        frame.dependency.machine._cache[frame.dependency.key]
                    )
                )
            except StopIteration as done:
                machine._cache[key] = cast("Word | None", done.value)
                continue
            frame.dependency = dependency
            identity = id(dependency.machine), dependency.key
            if dependency.key in dependency.machine._cache:
                continue
            if identity in active:
                raise ValueError("cyclic proof emission dependency")
            active.add(identity)
            stack.append(_EmissionFrame(dependency))
        return self._cache[root.key]

    def output(self, word: Sequence[int]) -> tuple[int, ...]:
        w = tuple(word)
        n = len(w)
        ls = [self.left.start]
        for a in w:
            q = self.left.step(ls[-1], a)
            if q is None:
                raise ValueError(("left reject", ls[-1], a))
            ls.append(q)
        rs = [0] * (n + 1)
        rs[n] = self.right.start
        for i in range(n - 1, -1, -1):
            q = self.right.step(rs[i + 1], w[i])
            if q is None:
                raise ValueError(("right reject", rs[i + 1], w[i]))
            rs[i] = q
        out: list[int] = []
        for i, a in enumerate(w):
            z = self.emit(ls[i], a, rs[i + 1])
            if z is None:
                raise ValueError(("undefined output", ls[i], a, rs[i + 1]))
            out.extend(z)
        return tuple(out)


@dataclass
class _EmissionFrame:
    request: EmissionRequest
    steps: EmissionSteps | None = None
    dependency: EmissionRequest | None = None


def lazy_from_eager(
    B: Bimachine,
) -> LazyBimachine:
    return LazyBimachine(
        B.base,
        B.alphabet,
        B.left,
        B.right,
        lambda left_state, a, r: B.out.get((left_state, a, r)),
        {},
    )


def fragment_steps(
    B: LazyBimachine, left_state: int, word: Sequence[int], r_after: int
) -> EmissionSteps:
    w = tuple(word)
    states = fragment_states(cast(_FragmentMachine, B), left_state, w, r_after)
    if states is None:
        return None
    ls, rs = states
    z: list[int] = []
    for i, a in enumerate(w):
        o = yield EmissionRequest(B, ls[i], a, rs[i + 1])
        if o is None:
            return None
        z.extend(o)
    return tuple(z)


def compose(
    B1: LazyBimachine, B2: LazyBimachine, verbose: bool = True
) -> LazyBimachine:
    assert B1.alphabet == B2.alphabet
    A = B1.alphabet
    t0 = time.perf_counter()
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
        B1.emit,
    )
    if verbose:
        print(
            " left+right NFA/DFA (combined)",
            len(LT),
            len(left.states),
            len(RT),
            len(right.states),
            "sec",
            time.perf_counter() - t0,
            flush=True,
        )

    # Index each determinized right subset by the two compatibility fields used
    # by the output witness search, separately for every input symbol.
    rindex: dict[tuple[int, int], dict[tuple[int, int], list[tuple[int, int]]]] = {}

    def get_rindex(Rs: int, a: int) -> dict[tuple[int, int], list[tuple[int, int]]]:
        key = (Rs, a)
        z = rindex.get(key)
        if z is not None:
            return z
        idx: defaultdict[tuple[int, int], list[tuple[int, int]]] = defaultdict(list)
        for yid in right.data[Rs]:
            l1_after, r1_after, r2_after = RT[yid]
            r1_before = B1.right.step(r1_after, a)
            if r1_before is not None:
                idx[(l1_after, r1_before)].append((r1_after, r2_after))
        rindex[key] = idx
        return idx

    def resolver(Ls: int, a: int, Rs: int) -> EmissionSteps:
        idx = get_rindex(Rs, a)
        candidate = None
        for xid in left.data[Ls]:
            l1, r1, l2 = LT[xid]
            l1n = B1.left.step(l1, a)
            if l1n is None:
                continue
            for r1_after, r2_after in idx.get((l1n, r1), ()):
                v = yield EmissionRequest(B1, l1, a, r1_after)
                if v is None:
                    continue
                w = yield from fragment_steps(B2, l2, v, r2_after)
                if w is None:
                    continue
                if candidate is None:
                    candidate = w
                elif candidate != w:
                    raise AssertionError(("ambiguous", Ls, a, Rs, candidate, w))
        return candidate

    C = LazyBimachine(B1.base, A, left, right, resolver, {})
    if verbose:
        print(
            " composed lazy L/R",
            len(left.states),
            len(right.states),
            "total sec",
            time.perf_counter() - t0,
            flush=True,
        )
    return C


def check_power(
    B: LazyBimachine, power: int, tests: int = 200, seed: int = 196
) -> None:
    rng = random.Random(seed + power)
    for _ in range(tests):
        p = rng.randrange(2)
        h = [rng.randrange(19) for _ in range(rng.randrange(1, 6))]
        h[0] = h[0] or 1
        pp, hh = p, tuple(h)
        for __ in range(power):
            pp, hh = ref(pp, hh, 10)
        got = decode(B.output(encode(p, h, 10)), 10)
        assert got == (pp, hh), (power, p, h, got, (pp, hh))


def main() -> None:
    B = lazy_from_eager(build_step(10))
    check_power(B, 1, 500)
    print(
        "B1",
        len(B.left.states),
        len(B.right.states),
        "cache",
        len(B._cache),
        flush=True,
    )
    P = B
    power = 1
    for _ in range(3):
        P = compose(P, P)
        power *= 2
        print(
            "P",
            power,
            "L/R",
            len(P.left.states),
            len(P.right.states),
            "cache",
            len(P._cache),
            flush=True,
        )
        check_power(P, power, 100)
        print(" after check cache", len(P._cache), flush=True)


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
