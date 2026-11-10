"""Owner mixin for publishing exact occurrences in the Q19 output grammar."""

from __future__ import annotations

from collections.abc import Iterator
from contextlib import AbstractContextManager

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import BimachineSLPProjector, SLPNode
from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag
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
    Q19CarryPhi6Summary,
    Q19CarryPhi6WordSummary,
    Q19Summary,
    WordSummary,
)


class Q19OutputPublicationMixin:
    """Build, validate, and publish exact Q19 grammar occurrences."""

    __slots__ = ("_broadword_last",)

    ledger: ResourceLedger
    base: int
    _digits: tuple[int, ...]
    _authority: ArenaToken
    arena: LedgerSLPArena
    projector: BimachineSLPProjector
    _summaries: OwnedMemo[int, WordSummary]
    _issued: OwnedMemo[tuple[int, int], ReversePairOutputOccurrence]
    _scratch_owner: int
    _broadword_last: tuple[int, int] | None

    def validate_open(self) -> None:
        raise NotImplementedError

    def discard_published_word_summary(self, root: int) -> None:
        raise NotImplementedError

    def _active_scratch_use(self) -> AbstractContextManager[None]:
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

    def publish_broadword_source(
        self, temporal_steps: int
    ) -> ReversePairOutputOccurrence:
        """Issue one exact growing-width endpoint from packed pair sums.

        Symmetric pair sums and the optional center form a successor-closed
        spatial state. The method still applies every requested transition;
        it does not infer a temporal period or skip source steps.
        """
        from number_compiler.resources.lifecycle import cleanup_on_error
        from number_compiler.sequences.reverse_add.q19_broadword_publisher import (
            PackedQ19,
        )

        self.validate_open()
        if type(temporal_steps) is not int or temporal_steps < 1:
            raise ValueError("physical Q19 endpoint requires positive duration")

        hint = self._broadword_last
        if hint is not None and hint[0] == temporal_steps:
            existing = self.issued_occurrence((hint[1], temporal_steps))
            if existing is not None:
                self.validate_issued_occurrence(existing)
                return existing

        width_bound = len(self._digits) + temporal_steps - 1
        scratch_nodes = 16 * (width_bound + 3)
        first_new_node = len(self.arena.nodes)
        rollback_publication: ReversePairOutputOccurrence | None = None
        previous_publication: ReversePairOutputOccurrence | None = None

        def rollback() -> None:
            self.rollback_punctured_application(
                first_new_node, rollback_publication, previous_publication
            )

        with cleanup_on_error(rollback):
            # Reserve before constructing the packed temporal state or its
            # terminal SLP. The reservation scales with the largest possible
            # width, while each live packed state is replaced in place.
            with self.ledger.reservation(
                self._scratch_owner,
                entries=4 * (width_bound + 3),
                nodes=scratch_nodes,
            ):
                frame = PackedQ19.from_digits(self._digits)

                def record_step_work(count: int, rounds: int) -> None:
                    # Count each requested recurrence before running it so an
                    # exception later in construction does not erase work.
                    self.ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_BROADWORD_SEMANTIC_STEPS
                    )
                    self.ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_BROADWORD_PREFIX_ROUNDS,
                        2 * rounds,
                    )
                    # This is a documented logical-bit estimate: ten fixed
                    # lane-width passes plus four prefix-network passes per
                    # doubling round. It is not an allocation or op counter.
                    logical_operand_bits = 6 * count * (10 + 4 * rounds)
                    self.ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_BROADWORD_OPERAND_BITS,
                        logical_operand_bits,
                    )

                frame = frame.advance_repeated(
                    temporal_steps - 1, before_step=record_step_work
                )

                # The ordinary Q19 source-to-output grammar represents the
                # source frame before its final addition. The terminal result
                # is therefore issued at temporal_steps from frame X_(n-1).
                def symbols() -> Iterator[int]:
                    yield 19 + (frame.width & 1)
                    for index in range(frame.count):
                        yield (frame.pairs >> (6 * index)) & 63
                    if frame.center is not None:
                        yield 2 * frame.center
                    yield 21

                root = self._word(symbols())
                issue_key = (root, temporal_steps)
                previous_publication = self.issued_occurrence(issue_key)
                published = self._issue(*issue_key)
                rollback_publication = published
                self.ledger.bump(
                    _reverse_add_keys.REVERSE_Q19_BROADWORD_ENDPOINT_PUBLICATIONS
                )
                self._broadword_last = (temporal_steps, published.root)
                return published

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
            # land on one key. Check the issued handle without re-folding the
            # full SLP; the incoming candidate already carries its exact fold.
            self.validate_issued_occurrence(existing)
            if occurrence_publication_snapshot(existing) != binding:
                raise ValueError("Q19 occurrence key collides with different metadata")
            return existing
        if published_binding is None:
            occurrence.bind_publication(binding)
        self._issued[key] = occurrence
        return occurrence

    def _issue(self, root: int, temporal_steps: int) -> ReversePairOutputOccurrence:
        # The target root is already known. Reuse an exact owner-issued
        # occurrence before rebuilding its whole-field summary.
        self.validate_open()
        existing = self._issued.get((root, temporal_steps))
        if existing is not None:
            self.validate_issued_occurrence(existing)
            return existing
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

    def _validated_full_summary(
        self, occurrence: ReversePairOutputOccurrence
    ) -> Q19Summary:
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
        return summary

    def validate(self, occurrence: ReversePairOutputOccurrence) -> None:
        self._validated_full_summary(occurrence)

    def _demanded_carry_phi6_summary(
        self, occurrence: ReversePairOutputOccurrence
    ) -> Q19CarryPhi6Summary:
        """Fold only the requested sidecar over the already issued SLP DAG.

        The ordinary Q19 summary remains cached unchanged. This extra pass is
        charged to the existing scratch owner and checks each visited interner
        binding, so a mutated descendant cannot acquire source authority.
        """
        encoded = self._summaries.get(occurrence.root)
        if type(encoded) is not WordSummary:
            raise ValueError("issued Q19 source lost its cached base summary")
        node_bound = len(self.arena.nodes)
        empty = Q19CarryPhi6WordSummary.identity()

        def checked_pending(node: SLPNode) -> None:
            self.validate_open()
            self.ledger.bump(_reverse_add_keys.REVERSE_Q19_NUMERIC_PORT_NODE_VISITS)
            self.validate_open()
            if type(node) is not SLPNode or not 0 <= node.id < node_bound:
                raise ValueError("Q19 fold encountered a foreign node")
            if self.arena.nodes[node.id] is not node:
                raise ValueError("Q19 fold node identity changed")
            if node.kind == "EMPTY":
                if node.id != self.arena.empty_id or node.length != 0:
                    raise ValueError("Q19 empty node binding changed")
            elif node.kind == "TERM":
                if (
                    self.arena.existing_terminal(node.symbol) != node.id
                    or node.length != 1
                ):
                    raise ValueError("Q19 terminal binding changed")
            elif node.kind == "CONCAT":
                if (
                    not (0 <= node.left < node.id and 0 <= node.right < node.id)
                    or self.arena.existing_concat(node.left, node.right) != node.id
                    or node.length
                    != self.arena.nodes[node.left].length
                    + self.arena.nodes[node.right].length
                ):
                    raise ValueError("Q19 concatenation binding changed")
            elif node.kind == "REPEAT":
                if (
                    not 0 <= node.child < node.id
                    or self.arena.existing_repeat_entry((node.child, node.count))
                    != node.id
                    or node.length != self.arena.nodes[node.child].length * node.count
                ):
                    raise ValueError("Q19 repetition binding changed")
            else:
                raise ValueError("Q19 grammar contains an unknown node")
            self.validate_open()

        def terminal(symbol: int) -> Q19CarryPhi6WordSummary:
            if not 0 <= symbol <= 18:
                return empty
            atom = Q19CarryPhi6Summary.atom(symbol)
            zero = Q19CarryPhi6Summary.identity()
            return Q19CarryPhi6WordSummary(atom, atom, zero, zero)

        def concatenate(
            left: Q19CarryPhi6WordSummary, right: Q19CarryPhi6WordSummary
        ) -> Q19CarryPhi6WordSummary:
            if right.forward.length:
                prefix_forward = left.forward.then(
                    right.prefix_forward, ledger=self.ledger
                )
                prefix_reverse = right.prefix_reverse.then(
                    left.reverse, ledger=self.ledger
                )
            else:
                prefix_forward = left.prefix_forward
                prefix_reverse = left.prefix_reverse
            return Q19CarryPhi6WordSummary(
                left.forward.then(right.forward, ledger=self.ledger),
                right.reverse.then(left.reverse, ledger=self.ledger),
                prefix_forward,
                prefix_reverse,
            )

        def repeat(
            child: Q19CarryPhi6WordSummary, count: int
        ) -> Q19CarryPhi6WordSummary:
            if not child.forward.length:
                return empty
            prefix_forward = (
                child.prefix_forward
                if count == 1
                else child.forward.repeat(count - 1, ledger=self.ledger).then(
                    child.prefix_forward, ledger=self.ledger
                )
            )
            prefix_reverse = (
                child.prefix_reverse
                if count == 1
                else child.prefix_reverse.then(
                    child.reverse.repeat(count - 1, ledger=self.ledger),
                    ledger=self.ledger,
                )
            )
            return Q19CarryPhi6WordSummary(
                child.forward.repeat(count, ledger=self.ledger),
                child.reverse.repeat(count, ledger=self.ledger),
                prefix_forward,
                prefix_reverse,
            )

        with (
            self._active_scratch_use(),
            self.ledger.reservation(
                self._scratch_owner,
                entries=4 * (node_bound + 1),
                nodes=8 * (node_bound + 1),
            ),
        ):
            values: dict[int, Q19CarryPhi6WordSummary] = {}
            try:
                values = fold_slp_dag(
                    self.arena,
                    occurrence.root,
                    empty_value=empty,
                    terminal_value=terminal,
                    concatenate=concatenate,
                    repeat=repeat,
                    on_pending=checked_pending,
                )
                self.validate_open()
                half = values[occurrence.root]
                first = self.symbol_at(occurrence.root, 0)
                parity = first - (2 * self.base - 1)
                if parity not in (0, 1):
                    raise ValueError("pair output grammar has an invalid parity tag")
                mirror = half.prefix_reverse if parity else half.reverse
                result = half.forward.then(mirror, ledger=self.ledger)
                self.validate_open()
                if result.length != encoded.forward.length * 2 - parity:
                    raise ValueError("Q19 Phi6 sidecar has a different pair width")
                self.ledger.bump(
                    _reverse_add_keys.REVERSE_Q19_NUMERIC_MODULAR_PROJECTIONS
                )
                return result
            finally:
                values.clear()

    def validate_issued_occurrence(
        self, occurrence: ReversePairOutputOccurrence
    ) -> None:
        """Check an immutable handle without re-folding its SLP."""
        self.validate_occurrence(occurrence)

    def apply_pair_step(
        self, occurrence: ReversePairOutputOccurrence
    ) -> ReversePairOutputOccurrence:
        self.validate_issued_occurrence(occurrence)
        before = self.projector.section_calls
        with self.ledger.reservation(
            self._scratch_owner,
            nodes=64 * (len(self.arena.nodes) + 1),
        ):
            target = self.projector.apply(occurrence.root)
        issue_key = (target, occurrence.temporal_steps + 1)
        existing = self.issued_occurrence(issue_key)
        if existing is None:
            candidate = self.candidate(*issue_key)
            step_growth = candidate.output_width - occurrence.output_width
            if step_growth not in (0, 1):
                raise AssertionError(
                    "one reverse/add step changed width by more than one"
                )
            result = self.publish(candidate)
        else:
            self.validate_issued_occurrence(existing)
            result = existing
            step_growth = result.output_width - occurrence.output_width
            if step_growth not in (0, 1):
                raise AssertionError(
                    "one reverse/add step changed width by more than one"
                )
        self.ledger.bump(_reverse_add_keys.REVERSE_Q19_PRIMITIVE_PAIR_APPLICATIONS)
        self.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PAIR_OUTPUT_NODES_VISITED,
            self.projector.section_calls - before,
        )
        return result


__all__ = ["Q19OutputPublicationMixin"]
