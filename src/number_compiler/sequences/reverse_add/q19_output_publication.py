"""Owner mixin for publishing exact occurrences in the Q19 output grammar."""

from __future__ import annotations

from collections.abc import Iterator

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import BimachineSLPProjector
from number_compiler.arithmetic.automata.slp_walks import symbol_at as slp_symbol_at
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.sequences.reverse_add.q19_occurrence import (
    ReversePairOutputOccurrence,
    occurrence_publication_snapshot,
)
from number_compiler.sequences.reverse_add.q19_summary_builder import (
    build_word_summary,
)
from number_compiler.sequences.reverse_add.q19_word_summary import (
    Q19_UPPER,
    Q19Summary,
    WordSummary,
)


class Q19OutputPublicationMixin:
    """Build, validate, and publish exact Q19 grammar occurrences."""

    __slots__ = ()

    ledger: ResourceLedger
    base: int
    _digits: tuple[int, ...]
    _authority: ArenaToken
    arena: LedgerSLPArena
    projector: BimachineSLPProjector
    _summaries: OwnedMemo[int, WordSummary]
    _issued: OwnedMemo[tuple[int, int], ReversePairOutputOccurrence]
    _scratch_owner: int

    def validate_open(self) -> None:
        raise NotImplementedError

    def discard_published_word_summary(self, root: int) -> None:
        raise NotImplementedError

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

    def symbol_at(self, root: int, index: int) -> int:
        return slp_symbol_at(self.arena, root, index)

    def word_summary(self, root: int) -> WordSummary:
        found = self._summaries.get(root)
        if found is not None:
            return found
        with self.ledger.reservation(
            self._scratch_owner, nodes=8 * (len(self.arena.nodes) + 1)
        ):
            return self._build_word_summary(root)

    def _build_word_summary(self, root: int) -> WordSummary:
        return build_word_summary(self.arena, self._summaries, self.ledger, root)

    def _full_summary(self, root: int) -> Q19Summary:
        encoded_summary = self.word_summary(root)
        first = self.symbol_at(root, 0)
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

    def candidate(self, root: int, temporal_steps: int) -> ReversePairOutputOccurrence:
        self.validate_open()
        summary = self._full_summary(root)
        pair_width = summary.length
        output_width = pair_width + int(summary.domain == Q19_UPPER)
        growth = output_width - len(self._digits)
        if growth < 0 or growth > temporal_steps:
            raise AssertionError("Q19 width growth escaped the one-cell-per-step bound")
        return ReversePairOutputOccurrence(
            self._authority,
            root,
            temporal_steps,
            pair_width,
            output_width,
            growth,
            summary.domain,
            summary.f9,
        )

    def publish(
        self, occurrence: ReversePairOutputOccurrence
    ) -> ReversePairOutputOccurrence:
        self.validate_open()
        occurrence.__post_init__()
        key = occurrence.root, occurrence.temporal_steps
        binding = occurrence_publication_snapshot(occurrence)
        published_binding = occurrence.publication_binding
        if published_binding is not None and published_binding != binding:
            raise ValueError("published Q19 occurrence metadata was altered")
        existing = self._issued.get(key)
        if existing is not None:
            # SLP interning can make repeated application of the same source
            # land on one key. Validate the first owner-issued handle before reuse.
            self.validate(existing)
            if occurrence_publication_snapshot(existing) != binding:
                raise ValueError("Q19 occurrence key collides with different metadata")
            return existing
        if published_binding is None:
            occurrence.bind_publication(binding)
        self._issued[key] = occurrence
        return occurrence

    def _issue(self, root: int, temporal_steps: int) -> ReversePairOutputOccurrence:
        return self.publish(self.candidate(root, temporal_steps))

    def issued_occurrence(
        self, key: tuple[int, int]
    ) -> ReversePairOutputOccurrence | None:
        """Read one owner-issued handle without exposing the mutable issue memo."""
        return self._issued.get(key)

    def rollback_punctured_application(
        self,
        first_new_node: int,
        published: ReversePairOutputOccurrence | None,
        previous_publication: ReversePairOutputOccurrence | None,
    ) -> None:
        """Restore one failed punctured publication and its unpublished SLP suffix."""
        if published is not None:
            issue_key = published.root, published.temporal_steps
            if self._issued.get(issue_key) == published:
                if previous_publication is None:
                    del self._issued[issue_key]
                else:
                    self._issued[issue_key] = previous_publication
        self.arena.rollback_unpublished_suffix(
            first_new_node, before_remove=self.discard_published_word_summary
        )

    def validate_occurrence(self, occurrence: ReversePairOutputOccurrence) -> None:
        self.validate_open()
        if type(occurrence) is not ReversePairOutputOccurrence:
            raise TypeError("expected an exact Q19 output occurrence")
        occurrence.__post_init__()
        if occurrence.owner is not self._authority:
            raise ValueError("Q19 output occurrence belongs to another request")
        if not 0 <= occurrence.root < len(self.arena.nodes):
            raise ValueError("Q19 output root is outside its grammar")
        if (
            self._issued.get((occurrence.root, occurrence.temporal_steps))
            is not occurrence
        ):
            raise ValueError("Q19 output occurrence was not issued by this owner")
        if occurrence.publication_binding != occurrence_publication_snapshot(
            occurrence
        ):
            raise ValueError("published Q19 occurrence metadata was altered")

    def validate(self, occurrence: ReversePairOutputOccurrence) -> None:
        self.validate_occurrence(occurrence)
        summary = self._full_summary(occurrence.root)
        if (
            summary.length != occurrence.pair_width
            or summary.domain != occurrence.q19_domain
            or summary.f9 != occurrence.q19_f9
            or occurrence.output_width
            != summary.length + int(summary.domain == Q19_UPPER)
            or occurrence.growth != occurrence.output_width - len(self._digits)
        ):
            raise ValueError("Q19 output metadata disagrees with its grammar")

    def validate_issued_occurrence(
        self, occurrence: ReversePairOutputOccurrence
    ) -> None:
        """Check an immutable handle without re-folding its SLP."""
        self.validate_occurrence(occurrence)

    def apply_pair_step(
        self, occurrence: ReversePairOutputOccurrence
    ) -> ReversePairOutputOccurrence:
        self.validate(occurrence)
        before = self.projector.section_calls
        with self.ledger.reservation(
            self._scratch_owner,
            nodes=64 * (len(self.arena.nodes) + 1),
        ):
            target = self.projector.apply(occurrence.root)
        candidate = self.candidate(target, occurrence.temporal_steps + 1)
        step_growth = candidate.output_width - occurrence.output_width
        if step_growth not in (0, 1):
            raise AssertionError("one reverse/add step changed width by more than one")
        result = self.publish(candidate)
        self.ledger.bump(_reverse_add_keys.REVERSE_Q19_PRIMITIVE_PAIR_APPLICATIONS)
        self.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PAIR_OUTPUT_NODES_VISITED,
            self.projector.section_calls - before,
        )
        return result


__all__ = ["Q19OutputPublicationMixin"]
