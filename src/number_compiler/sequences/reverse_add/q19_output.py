"""Ledger-owned decimal pair output grammar and Q19 summaries.

This owner contains spatial pair-step work only.  Temporal powers are still
driven by ``TileScheduler`` through source-image primitive and composition
callbacks; a published occurrence is the completed SLP root plus its exact
Q19/width metadata.
"""

from __future__ import annotations

from collections.abc import Callable, Generator, Iterator, MutableMapping
from contextlib import closing
from dataclasses import dataclass
from functools import cache
from typing import TypeVar

from number_compiler.arithmetic.automata.guard import record_slp_metrics
from number_compiler.arithmetic.automata.slp import (
    BimachineSLPProjector,
    SLPArena,
    SLPNode,
)
from number_compiler.arithmetic.automata.transducer import (
    build_pair_step_bimachine,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.stores import LedgerList

_NEUTRAL = 0
_LOWER = -1
_UPPER = 1
_K = TypeVar("_K")


@dataclass(frozen=True, slots=True)
class _FrozenPairDFA:
    alphabet: tuple[int, ...]
    start: int
    trans: tuple[tuple[int | None, ...], ...]
    states: tuple[int, ...]
    right: bool

    def step(self, state: int, symbol: int) -> int | None:
        if not 0 <= state < len(self.trans) or not 0 <= symbol < len(self.alphabet):
            return None
        return self.trans[state][symbol]


@dataclass(frozen=True, slots=True)
class _FrozenPairStepLaw:
    base: int
    alphabet: tuple[int, ...]
    left: _FrozenPairDFA
    right: _FrozenPairDFA
    resolver: Callable[[int, int, int], tuple[int, ...] | None]

    def emit(self, left: int, symbol: int, right: int) -> tuple[int, ...] | None:
        return self.resolver(int(left), int(symbol), int(right))


@cache
def _pair_step_law() -> _FrozenPairStepLaw:
    """One immutable finite decimal law shared by request-local output owners."""
    machine = build_pair_step_bimachine(10)
    machine.cache_enabled = False
    machine.clear_output_cache()
    left = _FrozenPairDFA(
        machine.left.alphabet,
        machine.left.start,
        tuple(
            tuple(machine.left.step(state, symbol) for symbol in machine.alphabet)
            for state in machine.left.states
        ),
        tuple(machine.left.states),
        machine.left.right,
    )
    right = _FrozenPairDFA(
        machine.right.alphabet,
        machine.right.start,
        tuple(
            tuple(machine.right.step(state, symbol) for symbol in machine.alphabet)
            for state in machine.right.states
        ),
        tuple(machine.right.states),
        machine.right.right,
    )
    return _FrozenPairStepLaw(
        machine.base,
        tuple(machine.alphabet),
        left,
        right,
        machine.resolver,
    )


@dataclass(frozen=True, slots=True)
class _Q19:
    length: int
    domain: int
    f9: int

    @classmethod
    def identity(cls) -> _Q19:
        return cls(0, _NEUTRAL, 0)

    @classmethod
    def atom(cls, value: int) -> _Q19:
        if type(value) is not int or not 0 <= value <= 18:
            raise ValueError("decimal pair symbols must lie in 0..18")
        defect = value - 9
        return cls(1, _LOWER if defect < 0 else _UPPER if defect > 0 else 0, defect % 9)

    def then(self, right: _Q19) -> _Q19:
        if type(right) is not _Q19:
            raise TypeError("Q19 composition requires another summary")
        if right.length == 0:
            return self
        if self.length == 0:
            return right
        domain = right.domain if right.domain != _NEUTRAL else self.domain
        phase = (self.f9 + pow(2, self.length, 9) * right.f9) % 9
        return _Q19(self.length + right.length, domain, phase)

    def repeat(self, count: int) -> _Q19:
        if type(count) is not int or count < 0:
            raise ValueError("Q19 repetition count must be nonnegative")
        result = _Q19.identity()
        power = self
        while count:
            if count & 1:
                result = result.then(power)
            count >>= 1
            if count:
                power = power.then(power)
        return result

    def validate_symmetric(self) -> None:
        if self.length < 1:
            raise ValueError("pair output must be nonempty")
        if self.length & 1:
            if self.domain == _NEUTRAL:
                raise ValueError("odd symmetric pair output has a neutral center")
        elif self.f9 % 3:
            raise ValueError("even symmetric pair output has an invalid F9 phase")


@dataclass(frozen=True, slots=True)
class _WordSummary:
    symbols: int
    forward: _Q19
    reverse: _Q19
    prefix_forward: _Q19
    prefix_reverse: _Q19


@dataclass(frozen=True, slots=True)
class ReversePairOutputOccurrence:
    """Exact target pair grammar issued by one request-local output owner."""

    owner: ArenaToken
    root: int
    temporal_steps: int
    pair_width: int
    output_width: int
    growth: int
    q19_domain: int
    q19_f9: int

    def __post_init__(self) -> None:
        if type(self.owner) is not ArenaToken:
            raise TypeError("pair output occurrence needs a scoped owner")
        if any(
            type(value) is not int
            for value in (
                self.root,
                self.temporal_steps,
                self.pair_width,
                self.output_width,
                self.growth,
                self.q19_domain,
                self.q19_f9,
            )
        ):
            raise TypeError("pair output metadata must use exact integers")
        if (
            self.root < 0
            or self.temporal_steps < 1
            or self.pair_width < 1
            or self.output_width < self.pair_width
            or self.growth < 0
            or self.q19_domain not in (_LOWER, _NEUTRAL, _UPPER)
            or not 0 <= self.q19_f9 < 9
        ):
            raise ValueError("invalid pair output occurrence metadata")


class _LedgerSLPArena(SLPArena):
    """The existing SLP implementation backed by one request ledger."""

    __slots__ = ("ledger", "owners")

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        self.ledger = ledger
        self.owners = (
            ledger.register(prefix + "-slp-nodes", "reverse_pair_output_grammar"),
            ledger.register(prefix + "-slp-terminals", "reverse_pair_output_interner"),
            ledger.register(prefix + "-slp-concats", "reverse_pair_output_interner"),
            ledger.register(prefix + "-slp-repeats", "reverse_pair_output_interner"),
        )
        self.nodes: LedgerList[SLPNode] = ledger.make_list(
            self.owners[0], nodes_per_entry=1
        )
        self._term = OwnedMemo(ledger, self.owners[1])
        self._cat = OwnedMemo(ledger, self.owners[2])
        self._rep = OwnedMemo(ledger, self.owners[3])
        self.empty_id = self._add("EMPTY", 0)

    def _add(self, kind: str, length: int, **kw: int) -> int:
        node_id = len(self.nodes)
        owner = self.owners[0]
        self.ledger.reserve(owner, entries=1, nodes=1)
        try:
            self.nodes.append(SLPNode(node_id, kind, int(length), **kw))
        except BaseException:
            if len(self.nodes) > node_id:
                self.nodes._rollback_unpublished(node_id)
            self.ledger.release(owner, entries=1, nodes=1)
            raise
        record_slp_metrics(nodes=1)
        return node_id

    def _add_interned(
        self,
        kind: str,
        length: int,
        table: MutableMapping[_K, int],
        key: _K,
        **kw: int,
    ) -> int:
        node_owner = self.owners[0]
        self.ledger.reserve(node_owner, entries=1, nodes=1)
        node_id = len(self.nodes)
        try:
            self.nodes.append(SLPNode(node_id, kind, int(length), **kw))
            table[key] = node_id
        except BaseException:
            if len(self.nodes) > node_id:
                self.nodes._rollback_unpublished(node_id)
            self.ledger.release(node_owner, entries=1, nodes=1)
            raise
        record_slp_metrics(nodes=1)
        return node_id


class ReversePairQ19OutputOwner:
    """One exact decimal pair transducer owned by a source-image adapter."""

    def __init__(
        self,
        ledger: ResourceLedger,
        digits_lsd: tuple[int, ...],
        *,
        base: int,
    ) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("Q19 output owner requires a resource ledger")
        if type(digits_lsd) is not tuple or not digits_lsd:
            raise ValueError("Q19 output owner requires original source digits")
        if type(base) is not int or base != 10:
            raise ValueError("the Q19 pair transducer is decimal-only")
        if any(type(value) is not int or not 0 <= value < base for value in digits_lsd):
            raise ValueError("Q19 source contains a digit outside its radix")
        self.ledger = ledger
        self.base = base
        self._digits = digits_lsd
        self._authority = ArenaToken("reverse-pair-q19-output")
        prefix = f"reverse-pair-q19-{ledger.owner_count}"
        self.arena = _LedgerSLPArena(ledger, prefix)
        self.machine = _pair_step_law()
        self.projector = BimachineSLPProjector(self.machine, self.arena)
        self._projector_owners = tuple(
            ledger.register(
                prefix + f"-projector-{name}", "reverse_pair_projector_memo"
            )
            for name in (
                "forward",
                "reverse",
                "block",
                "forward-power",
                "reverse-power",
            )
        )
        forward: OwnedMemo[tuple[int, int], int | None] = OwnedMemo(
            ledger, self._projector_owners[0], nodes_per_entry=1
        )
        backward: OwnedMemo[tuple[int, int], int | None] = OwnedMemo(
            ledger, self._projector_owners[1], nodes_per_entry=1
        )
        block: OwnedMemo[tuple[int, int, int], int] = OwnedMemo(
            ledger, self._projector_owners[2], nodes_per_entry=1
        )
        forward_power: OwnedMemo[tuple[int, int, int], int | None] = OwnedMemo(
            ledger, self._projector_owners[3], nodes_per_entry=1
        )
        backward_power: OwnedMemo[tuple[int, int, int], int | None] = OwnedMemo(
            ledger, self._projector_owners[4], nodes_per_entry=1
        )
        self._projector_memos = (
            forward,
            backward,
            block,
            forward_power,
            backward_power,
        )
        (
            self.projector._fwd,
            self.projector._rev,
            self.projector._block,
            self.projector._fwd_power,
            self.projector._rev_power,
        ) = self._projector_memos
        self._summary_owner = ledger.register(
            prefix + "-q19-summaries", "reverse_pair_q19_summary"
        )
        self._summaries: OwnedMemo[int, _WordSummary] = OwnedMemo(
            ledger, self._summary_owner, nodes_per_entry=1
        )
        self._issued_owner = ledger.register(
            prefix + "-issued-occurrences", "reverse_pair_output_occurrence"
        )
        self._issued: OwnedMemo[tuple[int, int], ReversePairOutputOccurrence] = (
            OwnedMemo(ledger, self._issued_owner, nodes_per_entry=1)
        )
        self._scratch_owner = ledger.register(
            prefix + "-workspace", "reverse_pair_output_workspace"
        )
        self._disposed = False
        self._binding = (
            ledger,
            digits_lsd,
            base,
            self._authority,
            self.arena,
            self.projector,
            self.machine,
        )
        ledger.register_execution_root(self)
        try:
            self.initial = self._make_initial()
        except BaseException:
            self.dispose()
            raise

    def _check_open(self) -> None:
        if self._disposed:
            raise ValueError("disposed Q19 pair output owner")
        if self.base != 10 or type(self._digits) is not tuple or not self._digits:
            raise ValueError("Q19 pair output source binding changed")
        current = (
            self.ledger,
            self._digits,
            self.base,
            self._authority,
            self.arena,
            self.projector,
            self.machine,
        )
        if len(self._binding) != len(current) or any(
            original is not bound
            for original, bound in zip(self._binding, current, strict=True)
        ):
            raise ValueError("Q19 output owner or finite law binding changed")

    def _append_word_symbol(self, blocks: list[tuple[int, int]], symbol: int) -> None:
        node = self.arena.terminal(symbol)
        level = 0
        while blocks and blocks[-1][0] == level:
            left = blocks.pop()[1]
            node = self.arena.concat(left, node)
            level += 1
        blocks.append((level, node))

    def _word(self, symbols: Iterator[int]) -> int:
        blocks: list[tuple[int, int]] = []
        for symbol in symbols:
            self._append_word_symbol(blocks, symbol)
        root = self.arena.empty()
        for _level, block in blocks:
            root = self.arena.concat(root, block)
        return root

    def _make_initial(self) -> ReversePairOutputOccurrence:
        width = len(self._digits)
        parity = width & 1
        half_width = (width + 1) // 2

        def encoded() -> Iterator[int]:
            yield 2 * self.base - 1 + parity
            for index in range(half_width):
                yield self._digits[index] + self._digits[width - 1 - index]
            yield 2 * self.base + 1

        with self.ledger.reservation(
            self._scratch_owner, nodes=8 * (width.bit_length() + 1)
        ):
            root = self._word(encoded())
        summary = self._full_summary(root)
        if summary.length != width:
            raise AssertionError("initial Q19 grammar changed pair-field width")
        return self._issue(root, 1)

    def _symbol_at(self, root: int, index: int) -> int:
        if type(index) is not int or not 0 <= index < self.arena.nodes[root].length:
            raise IndexError(index)
        node_id = root
        offset = index
        while True:
            node = self.arena.nodes[node_id]
            if node.kind == "TERM":
                return node.symbol
            if node.kind == "CONCAT":
                left_length = self.arena.nodes[node.left].length
                if offset < left_length:
                    node_id = node.left
                else:
                    offset -= left_length
                    node_id = node.right
                continue
            if node.kind == "REPEAT":
                child_length = self.arena.nodes[node.child].length
                if child_length == 0:
                    raise IndexError(index)
                offset %= child_length
                node_id = node.child
                continue
            raise ValueError("pair output grammar contains an empty symbol")

    def _word_summary(self, root: int) -> _WordSummary:
        found = self._summaries.get(root)
        if found is not None:
            return found
        with self.ledger.reservation(
            self._scratch_owner, nodes=8 * (self.arena.nodes[root].length + 1)
        ):
            return self._build_word_summary(root)

    def _build_word_summary(self, root: int) -> _WordSummary:
        found = self._summaries.get(root)
        if found is not None:
            self.ledger.bump("reverse_pair_q19_summary_cache_hits")
            return found
        self.ledger.bump("reverse_pair_q19_summary_cache_misses")
        stack: list[tuple[int, bool]] = [(root, False)]
        identity = _Q19.identity()
        while stack:
            node_id, expanded = stack.pop()
            if self._summaries.get(node_id) is not None:
                continue
            node = self.arena.nodes[node_id]
            if node.kind == "EMPTY":
                value = _WordSummary(0, identity, identity, identity, identity)
            elif node.kind == "TERM":
                if 0 <= node.symbol <= 18:
                    atom = _Q19.atom(node.symbol)
                    value = _WordSummary(1, atom, atom, identity, identity)
                else:
                    value = _WordSummary(0, identity, identity, identity, identity)
            elif node.kind == "CONCAT":
                if not expanded:
                    stack.append((node_id, True))
                    stack.append((node.right, False))
                    stack.append((node.left, False))
                    continue
                left = self._summaries[node.left]
                right = self._summaries[node.right]
                if right.symbols:
                    prefix_forward = left.forward.then(right.prefix_forward)
                    prefix_reverse = right.prefix_reverse.then(left.reverse)
                else:
                    prefix_forward, prefix_reverse = (
                        left.prefix_forward,
                        left.prefix_reverse,
                    )
                value = _WordSummary(
                    left.symbols + right.symbols,
                    left.forward.then(right.forward),
                    right.reverse.then(left.reverse),
                    prefix_forward,
                    prefix_reverse,
                )
            elif node.kind == "REPEAT":
                if not expanded:
                    stack.append((node_id, True))
                    stack.append((node.child, False))
                    continue
                child = self._summaries[node.child]
                if not child.symbols:
                    value = _WordSummary(0, identity, identity, identity, identity)
                else:
                    whole_forward = child.forward.repeat(node.count)
                    whole_reverse = child.reverse.repeat(node.count)
                    if node.count == 1:
                        prefix_forward = child.prefix_forward
                        prefix_reverse = child.prefix_reverse
                    else:
                        prefix_forward = child.forward.repeat(node.count - 1).then(
                            child.prefix_forward
                        )
                        prefix_reverse = child.prefix_reverse.then(
                            child.reverse.repeat(node.count - 1)
                        )
                    value = _WordSummary(
                        child.symbols * node.count,
                        whole_forward,
                        whole_reverse,
                        prefix_forward,
                        prefix_reverse,
                    )
            else:  # pragma: no cover - guarded by SLPArena
                raise AssertionError(node.kind)
            self._summaries[node_id] = value
        result = self._summaries.get(root)
        if result is None:
            raise AssertionError("Q19 summary construction lost its root")
        return result

    def _full_summary(self, root: int) -> _Q19:
        encoded_summary = self._word_summary(root)
        first = self._symbol_at(root, 0)
        parity = first - (2 * self.base - 1)
        if parity not in (0, 1):
            raise ValueError("pair output grammar has an invalid parity tag")
        half = encoded_summary.forward
        mirror = encoded_summary.prefix_reverse if parity else encoded_summary.reverse
        result = half.then(mirror)
        expected = 2 * encoded_summary.symbols - parity
        if result.length != expected:
            raise AssertionError("Q19 full-field fold lost its symmetric extent")
        result.validate_symmetric()
        return result

    def _issue(self, root: int, temporal_steps: int) -> ReversePairOutputOccurrence:
        self._check_open()
        summary = self._full_summary(root)
        pair_width = summary.length
        output_width = pair_width + int(summary.domain == _UPPER)
        growth = output_width - len(self._digits)
        if growth < 0 or growth > temporal_steps:
            raise AssertionError("Q19 width growth escaped the one-cell-per-step bound")
        occurrence = ReversePairOutputOccurrence(
            self._authority,
            root,
            temporal_steps,
            pair_width,
            output_width,
            growth,
            summary.domain,
            summary.f9,
        )
        self._issued[(root, temporal_steps)] = occurrence
        return occurrence

    def validate(self, occurrence: ReversePairOutputOccurrence) -> None:
        self._check_open()
        if type(occurrence) is not ReversePairOutputOccurrence:
            raise TypeError("expected an exact Q19 output occurrence")
        occurrence.__post_init__()
        if occurrence.owner is not self._authority:
            raise ValueError("Q19 output occurrence belongs to another request")
        if not 0 <= occurrence.root < len(self.arena.nodes):
            raise ValueError("Q19 output root is outside its grammar")
        if self._issued.get((occurrence.root, occurrence.temporal_steps)) != occurrence:
            raise ValueError("Q19 output occurrence was not issued by this owner")
        summary = self._full_summary(occurrence.root)
        if (
            summary.length != occurrence.pair_width
            or summary.domain != occurrence.q19_domain
            or summary.f9 != occurrence.q19_f9
            or occurrence.output_width != summary.length + int(summary.domain == _UPPER)
            or occurrence.growth != occurrence.output_width - len(self._digits)
        ):
            raise ValueError("Q19 output metadata disagrees with its grammar")

    def apply_pair_step(
        self, occurrence: ReversePairOutputOccurrence
    ) -> ReversePairOutputOccurrence:
        self.validate(occurrence)
        before = self.projector.section_calls
        with self.ledger.reservation(
            self._scratch_owner,
            nodes=64 * (self.arena.nodes[occurrence.root].length + 1),
        ):
            target = self.projector.apply(occurrence.root)
        result = self._issue(target, occurrence.temporal_steps + 1)
        step_growth = result.output_width - occurrence.output_width
        if step_growth not in (0, 1):
            raise AssertionError("one reverse/add step changed width by more than one")
        self.ledger.bump("reverse_q19_primitive_pair_applications")
        self.ledger.bump(
            "reverse_q19_pair_output_nodes_visited",
            self.projector.section_calls - before,
        )
        return result

    def _pair_value_at(
        self, occurrence: ReversePairOutputOccurrence, index: int
    ) -> int:
        self.validate(occurrence)
        if type(index) is not int or not 0 <= index < occurrence.pair_width:
            raise IndexError(index)
        parity_tag_value = self._symbol_at(occurrence.root, 0)
        parity = parity_tag_value - (2 * self.base - 1)
        half_width = (occurrence.pair_width + parity) // 2
        half_index = index if index < half_width else occurrence.pair_width - 1 - index
        return self._symbol_at(occurrence.root, half_index + 1)

    def _range_summary(
        self, root: int, begin: int, end: int, *, reverse: bool = False
    ) -> _Q19:
        """Fold a pair-symbol interval through cached regions, excluding tags."""
        result = _Q19.identity()
        tasks = [(root, begin, end, 1)]
        while tasks:
            node_id, lo, hi, copies = tasks.pop()
            if lo == hi:
                continue
            summary = self._summaries[node_id]
            self.ledger.bump("reverse_q19_point_region_visits")
            if not 0 <= lo < hi <= summary.symbols:
                raise ValueError("pair summary interval escaped its region")
            if lo == 0 and hi == summary.symbols:
                part = summary.reverse if reverse else summary.forward
                result = result.then(part.repeat(copies))
                continue
            node = self.arena.nodes[node_id]
            pieces: list[tuple[int, int, int, int]] = []
            if node.kind == "CONCAT":
                middle = self._summaries[node.left].symbols
                if lo < middle:
                    pieces.append((node.left, lo, min(hi, middle), 1))
                if hi > middle:
                    pieces.append((node.right, max(lo - middle, 0), hi - middle, 1))
            elif node.kind == "REPEAT":
                width = self._summaries[node.child].symbols
                first, offset = divmod(lo, width)
                last, tail = divmod(hi, width)
                if first == last:
                    pieces.append((node.child, offset, tail, 1))
                else:
                    if offset:
                        pieces.append((node.child, offset, width, 1))
                        first += 1
                    if last > first:
                        pieces.append((node.child, 0, width, last - first))
                    if tail:
                        pieces.append((node.child, 0, tail, 1))
            else:
                raise ValueError("partial pair region is not a composite")
            tasks.extend(pieces if reverse else reversed(pieces))
        return result

    def digit(self, occurrence: ReversePairOutputOccurrence, position: int) -> int:
        self.validate(occurrence)
        if type(position) is not int or not 0 <= position < occurrence.output_width:
            raise IndexError(position)
        if position == occurrence.pair_width:
            return 1
        root = occurrence.root
        half = self._summaries[root].symbols
        with self.ledger.reservation(
            self._scratch_owner, nodes=16 * (self.arena.nodes[root].length + 1)
        ):
            prefix = self._range_summary(root, 0, min(position, half))
            if position > half:
                prefix = prefix.then(
                    self._range_summary(
                        root,
                        occurrence.pair_width - position,
                        occurrence.pair_width - half,
                        reverse=True,
                    )
                )
            value = self._pair_value_at(occurrence, position)
            return (value + int(prefix.domain == _UPPER)) % self.base

    def _iter_symbols(self, root: int, *, reverse: bool = False) -> Iterator[int]:
        tasks: list[tuple[str, int, bool, int]] = [("NODE", root, reverse, 1)]
        while tasks:
            tag, node_id, backwards, remaining = tasks.pop()
            self._check_open()
            self.ledger.bump("recursive_output_stream_node_visits")
            node = self.arena.nodes[node_id]
            if tag == "REPEAT_REST":
                if remaining > 0:
                    tasks.append(("REPEAT_REST", node_id, backwards, remaining - 1))
                    tasks.append(("NODE", node.child, backwards, 1))
                continue
            if node.kind == "EMPTY":
                continue
            if node.kind == "TERM":
                yield node.symbol
            elif node.kind == "CONCAT":
                first, second = (
                    (node.left, node.right) if backwards else (node.right, node.left)
                )
                tasks.append(("NODE", first, backwards, 1))
                tasks.append(("NODE", second, backwards, 1))
            elif node.kind == "REPEAT":
                if node.count:
                    tasks.append(("REPEAT_REST", node_id, backwards, node.count - 1))
                    tasks.append(("NODE", node.child, backwards, 1))
            else:  # pragma: no cover
                raise AssertionError(node.kind)

    def iter_pair_values(
        self, occurrence: ReversePairOutputOccurrence
    ) -> Generator[int, None, None]:
        self.validate(occurrence)
        with self.ledger.reservation(
            self._scratch_owner,
            nodes=16 * (self.arena.nodes[occurrence.root].length + 1),
        ):
            yield from self._stream_pair_values(occurrence)

    def _stream_pair_values(
        self, occurrence: ReversePairOutputOccurrence
    ) -> Iterator[int]:
        self.validate(occurrence)
        encoded_length = self.arena.nodes[occurrence.root].length
        parity = self._symbol_at(occurrence.root, 0) - (2 * self.base - 1)
        if parity not in (0, 1):
            raise ValueError("pair output grammar has an invalid parity tag")
        emitted = 0
        for index, symbol in enumerate(self._iter_symbols(occurrence.root)):
            if 0 < index < encoded_length - 1:
                emitted += 1
                yield symbol
        reverse_seen = 0
        for index, symbol in enumerate(
            self._iter_symbols(occurrence.root, reverse=True)
        ):
            if not 0 < index < encoded_length - 1:
                continue
            if parity and reverse_seen == 0:
                reverse_seen += 1
                continue
            reverse_seen += 1
            emitted += 1
            yield symbol
        if emitted != occurrence.pair_width:
            raise AssertionError("Q19 output grammar stream changed its pair width")

    def iter_digits(self, occurrence: ReversePairOutputOccurrence) -> Iterator[int]:
        self.validate(occurrence)
        carry = 0
        emitted = 0
        with closing(self.iter_pair_values(occurrence)) as pairs:
            for pair in pairs:
                total = pair + carry
                carry, digit = divmod(total, self.base)
                emitted += 1
                self.ledger.bump("recursive_output_stream_emitted_digits")
                yield digit
        if carry:
            emitted += 1
            self.ledger.bump("recursive_output_stream_emitted_digits")
            yield carry
        if emitted != occurrence.output_width:
            raise AssertionError("Q19 output stream disagrees with exact width")

    def dispose(self) -> None:
        if self._disposed:
            return
        self._disposed = True
        self._issued.dispose()
        self._summaries.dispose()
        for memo in self._projector_memos:
            memo.dispose()
        for interner in (self.arena._rep, self.arena._cat, self.arena._term):
            if type(interner) is not OwnedMemo:
                raise TypeError("pair grammar interner lost its ledger owner")
            interner.dispose()
        nodes = self.arena.nodes
        if type(nodes) is not LedgerList:
            raise TypeError("pair grammar lost its ledger node store")
        count = len(nodes)
        nodes._rollback_unpublished(0)
        self.ledger.release(self.arena.owners[0], entries=count, nodes=count)
        self.ledger.mark_disposed(self.arena.owners[0])


__all__ = ["ReversePairOutputOccurrence", "ReversePairQ19OutputOwner"]
