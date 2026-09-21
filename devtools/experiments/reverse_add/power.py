"""Research quotient-first composition and repeated squaring of pair bimachines.

This reference composer builds an exact finite bipartite witness system and
quotients that system by a strong
Myhill--Nerode/bisimulation congruence over both transitions and output behavior,
then determinizes the canonical witness classes. It is not an installed
source-bound temporal constructor.

Likewise the composed output function is built from labeled Cartesian generator
regions and reduced directly to a canonical MTDD.  There is no
``left x alphabet x right`` output table and no per-context lazy resolver cache.
"""

from __future__ import annotations

from collections import defaultdict, deque
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass
from time import perf_counter

from number_compiler.arithmetic.automata.transducer import (
    DFA,
    BimachineTransformResult,
    LazyBimachine,
)
from number_compiler.arithmetic.functions.decision import (
    CanonicalOutputRelation,
    MultiTerminalDecisionArena,
)
from number_compiler.arithmetic.functions.residual import minimize_bimachine

_NFA = dict[tuple[int, int], set[int]]
_PrimitiveTriples = list[tuple[int, int, int]]
_OutputEdges = list[list[list[tuple[int, int]]]]
_OutputClasses = dict[tuple[int, int, int], int]
_Observation = tuple[tuple[int, int], ...]
_Observations = dict[tuple[int, int], _Observation]


class PowerConstructionLimit(RuntimeError):
    pass


@dataclass(frozen=True, slots=True)
class CompositionMetrics:
    left_nfa_states: int
    left_dfa_states: int
    right_nfa_states: int
    right_dfa_states: int
    seconds: float
    primitive_left_classes: int = 0
    primitive_right_classes: int = 0
    primitive_refinement_rounds: int = 0
    primitive_output_probes: int = 0
    semantic_generator_boxes: int = 0
    semantic_regions: int = 0
    semantic_decision_nodes: int = 0
    raw_left_dfa_states: int = 0
    raw_right_dfa_states: int = 0
    deterministic_refinement_rounds: int = 0


ComposedBimachine = BimachineTransformResult[CompositionMetrics]


def _determinize(
    alphabet: Sequence[int], startset: Iterable[int], nfa: _NFA, *, right: bool
) -> tuple[DFA, tuple[frozenset[int], ...]]:
    subsets: list[frozenset[int]] = []
    sid: dict[frozenset[int], int] = {}

    def intern(states: Iterable[int]) -> int:
        fs = frozenset(states)
        old = sid.get(fs)
        if old is not None:
            return old
        q = len(subsets)
        sid[fs] = q
        subsets.append(fs)
        return q

    start = intern(startset)
    trans: dict[tuple[int, int], int] = {}
    todo = deque([start])
    seen = set()
    while todo:
        q = todo.popleft()
        if q in seen:
            continue
        seen.add(q)
        subset = subsets[q]
        for symbol in alphabet:
            out: set[int] = set()
            for state in subset:
                out.update(nfa.get((state, symbol), ()))
            if not out:
                continue
            z = intern(out)
            trans[q, symbol] = z
            if z not in seen:
                todo.append(z)
    return DFA(tuple(alphabet), start, trans, tuple(range(len(subsets))), right), tuple(
        subsets
    )


def _fragment(
    machine: LazyBimachine, left: int, word: Sequence[int], right_after: int
) -> tuple[int, ...] | None:
    word = tuple(word)
    left_states = [left]
    for symbol in word:
        q = machine.left.step(left_states[-1], symbol)
        if q is None:
            return None
        left_states.append(q)
    right_states = [0] * (len(word) + 1)
    right_states[-1] = right_after
    for i in range(len(word) - 1, -1, -1):
        q = machine.right.step(right_states[i + 1], word[i])
        if q is None:
            return None
        right_states[i] = q
    output: list[int] = []
    for i, symbol in enumerate(word):
        value = machine.emit(left_states[i], symbol, right_states[i + 1])
        if value is None:
            return None
        output.extend(value)
    return tuple(output)


def _same_partition(old: Sequence[int], new: Sequence[int]) -> bool:
    forward: dict[int, int] = {}
    reverse: dict[int, int] = {}
    for a, b in zip(old, new):
        x = forward.get(a)
        if x is not None and x != b:
            return False
        y = reverse.get(b)
        if y is not None and y != a:
            return False
        forward[a] = b
        reverse[b] = a
    return True


class _WordInterner:
    __slots__ = ("ids", "words")

    def __init__(self) -> None:
        self.ids: dict[tuple[int, ...], int] = {}
        self.words: list[tuple[int, ...]] = []

    def intern(self, word: Sequence[int]) -> int:
        value = tuple(map(int, word))
        old = self.ids.get(value)
        if old is not None:
            return old
        q = len(self.words)
        self.ids[value] = q
        self.words.append(value)
        return q


def _build_primitive_left(
    first: LazyBimachine,
    second: LazyBimachine,
    alphabet: Sequence[int],
    check_limit: Callable[[int], None],
) -> tuple[_PrimitiveTriples, set[int], _NFA]:
    triples: list[tuple[int, int, int]] = []
    ids: dict[tuple[int, int, int], int] = {}

    def intern(value: tuple[int, int, int]) -> int:
        old = ids.get(value)
        if old is not None:
            return old
        q = len(triples)
        ids[value] = q
        triples.append(value)
        check_limit(len(triples))
        return q

    start = {
        intern((first.left.start, r, second.left.start)) for r in first.right.states
    }
    predecessor_right: dict[int, defaultdict[int, list[int]]] = {
        symbol: defaultdict(list) for symbol in alphabet
    }
    for right_after in first.right.states:
        for symbol in alphabet:
            right_before = first.right.step(right_after, symbol)
            if right_before is not None:
                predecessor_right[symbol][right_before].append(right_after)

    nfa: dict[tuple[int, int], set[int]] = {}
    todo = deque(start)
    seen = set()
    while todo:
        check_limit(len(triples))
        q = todo.popleft()
        if q in seen:
            continue
        seen.add(q)
        left_before, right_before, second_left_before = triples[q]
        for symbol in alphabet:
            left_after = first.left.step(left_before, symbol)
            if left_after is None:
                continue
            for right_after in predecessor_right[symbol].get(right_before, ()):
                middle = first.emit(left_before, symbol, right_after)
                if middle is None:
                    continue
                second_left_after = second.left.word(second_left_before, middle)
                if second_left_after is None:
                    continue
                z = intern((left_after, right_after, second_left_after))
                nfa.setdefault((q, symbol), set()).add(z)
                if z not in seen:
                    todo.append(z)
    return triples, start, nfa


def _build_primitive_right(
    first: LazyBimachine,
    second: LazyBimachine,
    alphabet: Sequence[int],
    check_limit: Callable[[int], None],
    left_count: int,
) -> tuple[_PrimitiveTriples, set[int], _NFA]:
    triples: list[tuple[int, int, int]] = []
    ids: dict[tuple[int, int, int], int] = {}

    def intern(value: tuple[int, int, int]) -> int:
        old = ids.get(value)
        if old is not None:
            return old
        q = len(triples)
        ids[value] = q
        triples.append(value)
        check_limit(left_count + len(triples))
        return q

    start = {
        intern((left_state, first.right.start, second.right.start))
        for left_state in first.left.states
    }
    predecessor_left: dict[int, defaultdict[int, list[int]]] = {
        symbol: defaultdict(list) for symbol in alphabet
    }
    for left_before in first.left.states:
        for symbol in alphabet:
            left_after = first.left.step(left_before, symbol)
            if left_after is not None:
                predecessor_left[symbol][left_after].append(left_before)

    nfa: dict[tuple[int, int], set[int]] = {}
    todo = deque(start)
    seen = set()
    while todo:
        check_limit(left_count + len(triples))
        q = todo.popleft()
        if q in seen:
            continue
        seen.add(q)
        left_after, right_after, second_right_after = triples[q]
        for symbol in alphabet:
            right_before = first.right.step(right_after, symbol)
            if right_before is None:
                continue
            for left_before in predecessor_left[symbol].get(left_after, ()):
                middle = first.emit(left_before, symbol, right_after)
                if middle is None:
                    continue
                second_right_before = second.right.word(second_right_after, middle)
                if second_right_before is None:
                    continue
                z = intern((left_before, right_before, second_right_before))
                nfa.setdefault((q, symbol), set()).add(z)
                if z not in seen:
                    todo.append(z)
    return triples, start, nfa


def _primitive_output_relation(
    first: LazyBimachine,
    second: LazyBimachine,
    alphabet: Sequence[int],
    triples_l: _PrimitiveTriples,
    triples_r: _PrimitiveTriples,
    check_limit: Callable[[int], None],
) -> tuple[_OutputEdges, _OutputEdges, _WordInterner, int]:
    """Exact bipartite primitive witness/output relation, indexed before subsets."""
    right_index: dict[tuple[int, int, int], list[tuple[int, int, int]]] = defaultdict(
        list
    )
    for yid, (left_after, right_after, second_right_after) in enumerate(triples_r):
        for ai, symbol in enumerate(alphabet):
            right_before = first.right.step(right_after, symbol)
            if right_before is not None:
                right_index[ai, left_after, right_before].append(
                    (yid, right_after, second_right_after)
                )

    words = _WordInterner()
    left_output: list[list[list[tuple[int, int]]]] = [
        [[] for _ in alphabet] for _ in triples_l
    ]
    right_output: list[list[list[tuple[int, int]]]] = [
        [[] for _ in alphabet] for _ in triples_r
    ]
    probes = 0
    for xid, (left_before, right_before, second_left_before) in enumerate(triples_l):
        for ai, symbol in enumerate(alphabet):
            next_left = first.left.step(left_before, symbol)
            if next_left is None:
                continue
            for yid, right_after, second_right_after in right_index.get(
                (ai, next_left, right_before), ()
            ):
                probes += 1
                check_limit(len(triples_l) + len(triples_r))
                middle = first.emit(left_before, symbol, right_after)
                if middle is None:
                    continue
                output = _fragment(
                    second, second_left_before, middle, second_right_after
                )
                if output is None:
                    continue
                wid = words.intern(output)
                left_output[xid][ai].append((yid, wid))
                right_output[yid][ai].append((xid, wid))
    return left_output, right_output, words, probes


def _primitive_semantic_partition(
    alphabet: Sequence[int],
    lnfa: _NFA,
    rnfa: _NFA,
    left_output: _OutputEdges,
    right_output: _OutputEdges,
) -> tuple[list[int], list[int], int]:
    """Coarsest strong transition/output congruence on primitive witnesses.

    This is deliberately stronger than general NFA language equivalence, hence
    every early merge is exact.  It is sufficient to move the powered T^2
    Myhill--Nerode merges in front of determinization on the pair operator.
    """
    left_part = [0] * len(left_output)
    right_part = [0] * len(right_output)
    rounds = 0
    while True:
        rounds += 1
        left_ids: dict[tuple[object, ...], int] = {}
        new_left: list[int] = []
        for q in range(len(left_output)):
            transition = tuple(
                tuple(sorted({left_part[z] for z in lnfa.get((q, symbol), ())}))
                for symbol in alphabet
            )
            outputs = tuple(
                tuple(sorted({(right_part[r], wid) for r, wid in left_output[q][ai]}))
                for ai in range(len(alphabet))
            )
            signature = transition, outputs
            new_left.append(left_ids.setdefault(signature, len(left_ids)))

        right_ids: dict[tuple[object, ...], int] = {}
        new_right: list[int] = []
        for q in range(len(right_output)):
            transition = tuple(
                tuple(sorted({right_part[z] for z in rnfa.get((q, symbol), ())}))
                for symbol in alphabet
            )
            outputs = tuple(
                tuple(
                    sorted(
                        {
                            (new_left[left_state], wid)
                            for left_state, wid in right_output[q][ai]
                        }
                    )
                )
                for ai in range(len(alphabet))
            )
            signature = transition, outputs
            new_right.append(right_ids.setdefault(signature, len(right_ids)))

        if _same_partition(left_part, new_left) and _same_partition(
            right_part, new_right
        ):
            return new_left, new_right, rounds
        left_part, right_part = new_left, new_right


def _quotient_nfa(
    alphabet: Sequence[int],
    nstates: int,
    nfa: _NFA,
    start: Iterable[int],
    part: Sequence[int],
) -> tuple[set[int], _NFA, int]:
    nclasses = max(part, default=-1) + 1
    representative: list[int | None] = [None] * nclasses
    for q, cls in enumerate(part):
        if representative[cls] is None:
            representative[cls] = q
    trans: dict[tuple[int, int], set[int]] = {}
    for cls, rep in enumerate(representative):
        assert rep is not None
        for symbol in alphabet:
            expected = {part[z] for z in nfa.get((rep, symbol), ())}
            if expected:
                trans[cls, symbol] = expected
    # The partition signature guarantees every member has the same class targets.
    for q in range(nstates):
        cls = part[q]
        for symbol in alphabet:
            actual = {part[z] for z in nfa.get((q, symbol), ())}
            if actual != trans.get((cls, symbol), set()):
                raise AssertionError("primitive quotient is not transition-congruent")
    return {part[q] for q in start}, trans, nclasses


def _class_output_map(
    left_output: _OutputEdges,
    left_part: Sequence[int],
    right_part: Sequence[int],
    words: _WordInterner,
) -> _OutputClasses:
    result: dict[tuple[int, int, int], int] = {}
    for left_primitive, by_symbol in enumerate(left_output):
        lc = left_part[left_primitive]
        for ai, entries in enumerate(by_symbol):
            for right_primitive, wid in entries:
                key = lc, ai, right_part[right_primitive]
                old = result.get(key)
                if old is not None and old != wid:
                    raise AssertionError(
                        "primitive semantic quotient merged unequal outputs"
                    )
                result[key] = wid
    return result


def _class_membership(subsets: Sequence[frozenset[int]], nclasses: int) -> list[int]:
    membership = [0] * int(nclasses)
    for state, subset in enumerate(subsets):
        bit = 1 << state
        for cls in subset:
            membership[cls] |= bit
    return membership


def _deterministic_observations(
    alphabet: Sequence[int],
    left_subsets: Sequence[frozenset[int]],
    right_subsets: Sequence[frozenset[int]],
    nleft_classes: int,
    nright_classes: int,
    class_output: _OutputClasses,
) -> tuple[_Observations, _Observations]:
    """Canonical exact output residuals without a Cartesian state product.

    A left observation is represented by output-word ids -> selector masks of
    right DFA states; undefined output is implicit in the complement.  Right
    observations are symmetric.  These are the exact functions used by
    Myhill--Nerode, but constructed from semantic class membership rather than
    by evaluating every left/right context pair.
    """
    left_membership = _class_membership(left_subsets, nleft_classes)
    right_membership = _class_membership(right_subsets, nright_classes)
    by_left: dict[tuple[int, int], list[tuple[int, int]]] = defaultdict(list)
    by_right: dict[tuple[int, int], list[tuple[int, int]]] = defaultdict(list)
    for (lc, ai, rc), wid in class_output.items():
        by_left[lc, ai].append((rc, wid))
        by_right[rc, ai].append((lc, wid))

    def canonical_groups(
        entries: Sequence[tuple[int, int]], opposite_membership: Sequence[int]
    ) -> _Observation:
        groups: dict[int, int] = {}
        for opposite_class, wid in entries:
            mask = opposite_membership[opposite_class]
            if not mask:
                continue
            groups[wid] = groups.get(wid, 0) | mask
        # Functional transduction requires different output labels to be disjoint.
        used = 0
        for wid, mask in groups.items():
            if used & mask:
                raise AssertionError(
                    "semantic class output selectors overlap with different words"
                )
            used |= mask
        return tuple(sorted((wid, mask) for wid, mask in groups.items()))

    left_obs: _Observations = {}
    for state, subset in enumerate(left_subsets):
        for ai in range(len(alphabet)):
            entries: list[tuple[int, int]] = []
            for lc in subset:
                entries.extend(by_left.get((lc, ai), ()))
            left_obs[state, alphabet[ai]] = canonical_groups(entries, right_membership)

    right_obs: _Observations = {}
    for state, subset in enumerate(right_subsets):
        for ai in range(len(alphabet)):
            entries = []
            for rc in subset:
                entries.extend(by_right.get((rc, ai), ()))
            right_obs[state, alphabet[ai]] = canonical_groups(entries, left_membership)
    return left_obs, right_obs


def _deterministic_partition(
    dfa: DFA, observation: _Observations
) -> tuple[dict[int, int], int]:
    states, alphabet = dfa.states, dfa.alphabet
    seed_ids: dict[tuple[object, ...], int] = {}
    part: dict[int, int] = {}
    for q in states:
        row = tuple(observation[q, a] for a in alphabet)
        part[q] = seed_ids.setdefault(row, len(seed_ids))
    rounds = 0
    while True:
        rounds += 1
        ids: dict[tuple[object, ...], int] = {}
        new: dict[int, int] = {}
        for q in states:
            signature = tuple(
                (
                    (
                        part.get(target, -1)
                        if (target := dfa.step(q, a)) is not None
                        else -1
                    ),
                    observation[q, a],
                )
                for a in alphabet
            )
            new[q] = ids.setdefault(signature, len(ids))
        if _same_partition(
            tuple(part[q] for q in states), tuple(new[q] for q in states)
        ):
            return new, rounds
        part = new


def _quotient_dfa_exact(dfa: DFA, part: dict[int, int]) -> tuple[DFA, dict[int, int]]:
    classes = sorted(set(part.values()))
    reps = {cls: min(q for q in dfa.states if part[q] == cls) for cls in classes}
    cmap = {cls: i for i, cls in enumerate(classes)}
    old_to_new = {q: cmap[part[q]] for q in dfa.states}
    trans = {}
    for cls, old in reps.items():
        q = cmap[cls]
        for symbol in dfa.alphabet:
            z = dfa.step(old, symbol)
            if z is not None:
                trans[q, symbol] = old_to_new[z]
    out = DFA(
        dfa.alphabet,
        old_to_new[dfa.start],
        trans,
        tuple(range(len(classes))),
        dfa.right,
    )
    new_to_old = {cmap[cls]: reps[cls] for cls in classes}
    return out, new_to_old


def _canonical_output_from_classes(
    alphabet: Sequence[int],
    left: DFA,
    left_subsets: Sequence[frozenset[int]],
    right: DFA,
    right_subsets: Sequence[frozenset[int]],
    nleft_classes: int,
    nright_classes: int,
    class_output: _OutputClasses,
    words: _WordInterner,
    exact_probes: int,
) -> CanonicalOutputRelation:
    left_membership = _class_membership(left_subsets, nleft_classes)
    right_membership = _class_membership(right_subsets, nright_classes)

    boxes: list[tuple[object, tuple[int, int, int]]] = []
    for (lc, ai, rc), wid in class_output.items():
        lm, rm = left_membership[lc], right_membership[rc]
        if lm and rm:
            boxes.append((words.words[wid], (lm, 1 << ai, rm)))

    # Quotient-first experiments show symbol -> right -> left minimizes the exact
    # decision description for the pair-field power while keeping symbol singleton.
    arena = MultiTerminalDecisionArena(
        (len(left.states), len(alphabet), len(right.states)), order=(1, 2, 0)
    )
    root = arena.build_labeled_boxes(boxes, default=None, exact_probes=exact_probes)
    return CanonicalOutputRelation(
        arena, root, left.states, tuple(alphabet), right.states
    )


def compose_bimachines(
    first: LazyBimachine,
    second: LazyBimachine,
    *,
    state_cap: int | None = None,
    time_cap: float | None = None,
    cache_outputs: bool = False,
) -> ComposedBimachine:
    """Exact quotient-first composition ``second(first(word))``.

    The returned context DFAs are already determinized from canonical primitive
    semantic classes.  A downstream exact minimizer is retained as a release
    assertion, not as the normal place where duplicate powered states are found.
    """
    if first.alphabet != second.alphabet:
        raise ValueError("alphabet mismatch")
    alphabet = first.alphabet
    t0 = perf_counter()

    def check_limit(n: int) -> None:
        if state_cap is not None and n > state_cap:
            raise PowerConstructionLimit(f"state cap {state_cap} exceeded")
        if time_cap is not None and perf_counter() - t0 > time_cap:
            raise PowerConstructionLimit(f"time cap {time_cap}s exceeded")

    triples_l, lstart, lnfa = _build_primitive_left(
        first, second, alphabet, check_limit
    )
    triples_r, rstart, rnfa = _build_primitive_right(
        first, second, alphabet, check_limit, len(triples_l)
    )
    left_output, right_output, words, primitive_probes = _primitive_output_relation(
        first, second, alphabet, triples_l, triples_r, check_limit
    )
    lpart, rpart, rounds = _primitive_semantic_partition(
        alphabet, lnfa, rnfa, left_output, right_output
    )

    qlstart, qlnfa, nleft_classes = _quotient_nfa(
        alphabet, len(triples_l), lnfa, lstart, lpart
    )
    qrstart, qrnfa, nright_classes = _quotient_nfa(
        alphabet, len(triples_r), rnfa, rstart, rpart
    )
    raw_left, raw_left_subsets = _determinize(alphabet, qlstart, qlnfa, right=False)
    raw_right, raw_right_subsets = _determinize(alphabet, qrstart, qrnfa, right=True)
    check_limit(
        len(triples_l) + len(triples_r) + len(raw_left.states) + len(raw_right.states)
    )

    class_output = _class_output_map(left_output, lpart, rpart, words)
    left_obs, right_obs = _deterministic_observations(
        alphabet,
        raw_left_subsets,
        raw_right_subsets,
        nleft_classes,
        nright_classes,
        class_output,
    )
    left_part, left_rounds = _deterministic_partition(raw_left, left_obs)
    right_part, right_rounds = _deterministic_partition(raw_right, right_obs)
    left, left_rep = _quotient_dfa_exact(raw_left, left_part)
    right, right_rep = _quotient_dfa_exact(raw_right, right_part)
    # Output construction needs only one raw semantic representative per final
    # Nerode class; no late minimizer or Cartesian output row is involved.
    left_subsets = tuple(raw_left_subsets[left_rep[q]] for q in left.states)
    right_subsets = tuple(raw_right_subsets[right_rep[q]] for q in right.states)
    relation = _canonical_output_from_classes(
        alphabet,
        left,
        left_subsets,
        right,
        right_subsets,
        nleft_classes,
        nright_classes,
        class_output,
        words,
        primitive_probes,
    )
    machine = LazyBimachine(
        first.base,
        tuple(alphabet),
        left,
        right,
        relation.emit,
        cache_enabled=cache_outputs,
        canonical_output=relation,
    )
    dm = relation.arena.metrics()
    return ComposedBimachine(
        machine,
        CompositionMetrics(
            len(triples_l),
            len(left.states),
            len(triples_r),
            len(right.states),
            perf_counter() - t0,
            nleft_classes,
            nright_classes,
            rounds,
            primitive_probes,
            dm.generator_boxes,
            dm.normalized_boxes,
            dm.internal_nodes,
            len(raw_left.states),
            len(raw_right.states),
            left_rounds + right_rounds,
        ),
    )


@dataclass(frozen=True, slots=True)
class PowerLevelMetrics:
    exponent: int
    left_states: int
    right_states: int
    output_probes: int
    decision_description_bytes: int
    compose_seconds: float
    canonical_generator_boxes: int = 0
    canonical_regions: int = 0
    late_left_merges: int = 0
    late_right_merges: int = 0


class ResidualPowerTable:
    """Universal-machine research table, not the decimal production owner.

    Source-ray powering must construct its admitted semantic effects before
    composition. Minimizing this table's context machines does not provide it.
    """

    __slots__ = ("levels", "metrics", "state_cap", "time_cap")

    def __init__(
        self,
        base: LazyBimachine,
        *,
        state_cap: int | None = None,
        time_cap: float | None = None,
    ):
        q = minimize_bimachine(base, cache_outputs=False)
        self.levels = [q.machine]
        self.metrics = [
            PowerLevelMetrics(
                1,
                len(q.machine.left.states),
                len(q.machine.right.states),
                q.metrics.exact_output_probes,
                q.metrics.decision_description_bytes,
                0.0,
                q.metrics.canonical_generator_boxes,
                q.metrics.canonical_regions,
                q.metrics.left_before - q.metrics.left_after,
                q.metrics.right_before - q.metrics.right_after,
            )
        ]
        self.state_cap = state_cap
        self.time_cap = time_cap

    def ensure(self, bit: int) -> LazyBimachine:
        bit = int(bit)
        if bit < 0:
            raise ValueError(bit)
        while len(self.levels) <= bit:
            prev = self.levels[-1]
            exponent = 1 << len(self.levels)
            if exponent <= 2:
                comp = compose_bimachines(
                    prev,
                    prev,
                    state_cap=self.state_cap,
                    time_cap=self.time_cap,
                    cache_outputs=False,
                )
                # compose_bimachines() performs primitive and deterministic
                # semantic quotienting before the canonical MTDD is constructed.
                machine = comp.machine
                relation = machine.canonical_output
                assert relation is not None
                dm = relation.arena.metrics()
                self.levels.append(machine)
                self.metrics.append(
                    PowerLevelMetrics(
                        exponent,
                        len(machine.left.states),
                        len(machine.right.states),
                        dm.exact_probes,
                        (dm.description_bits + 7) // 8,
                        comp.metrics.seconds,
                        dm.generator_boxes,
                        dm.normalized_boxes,
                        0,
                        0,
                    )
                )
                continue

            # Beyond T^2, raw Cartesian witness triples are a prohibited
            # regression.  Explore only the canonical grouped dependency
            # relation.  An incomplete cascade is a hard construction limit;
            # there is deliberately no fallback to compose_bimachines().
            from devtools.experiments.reverse_add.cascade_power import (
                compose_bimachines_cascade,
            )

            cc = compose_bimachines_cascade(
                prev,
                prev,
                state_cap=self.state_cap,
                time_cap=self.time_cap,
                cache_outputs=False,
            )
            lm, rm = cc.left.metrics(), cc.right.metrics()
            if not cc.complete or cc.machine is None:
                raise PowerConstructionLimit(
                    "canonical dependency cascade did not close for "
                    f"T^{exponent}: left={lm.states} states/{lm.dependency_groups} groups, "
                    f"right={rm.states} states/{rm.dependency_groups} groups; "
                    "raw primitive-triple fallback is forbidden"
                )
            # A complete context cascade still needs an authoritative canonical
            # output MTDD before it can become a release power level.  Do not
            # reintroduce a per-context resolver/cache as a shortcut.
            if not cc.machine.has_canonical_output:
                raise PowerConstructionLimit(
                    f"T^{exponent} context cascade closed but canonical output relation "
                    "is not installed; tuple-resolver promotion is forbidden"
                )
        return self.levels[bit]


__all__ = [
    "ComposedBimachine",
    "CompositionMetrics",
    "PowerConstructionLimit",
    "PowerLevelMetrics",
    "ResidualPowerTable",
    "compose_bimachines",
]
