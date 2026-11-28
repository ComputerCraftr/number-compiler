"""Owner mixin for publishing exact occurrences in the Q19 output grammar."""

from __future__ import annotations

from collections.abc import Iterator
from contextlib import AbstractContextManager, closing
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import BimachineSLPProjector, SLPNode
from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag
from number_compiler.arithmetic.automata.slp_walks import iter_symbols
from number_compiler.arithmetic.automata.slp_walks import symbol_at as slp_symbol_at
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
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

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.q19_broadword_publisher import PackedQ19


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
    _frontiers: OwnedMemo[int, tuple[int, bool]]

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
        return self._publish_broadword_source(temporal_steps, carry_window=False)

    def publish_carry_window_continuation(
        self, temporal_steps: int, *, shared_cache: bool = False
    ) -> ReversePairOutputOccurrence:
        """Issue a physical endpoint through the source's twelve-row forcing image."""
        from number_compiler.sequences.reverse_add.q19_carry_window import (
            DECIMAL_CARRY_WINDOW,
        )

        if type(temporal_steps) is not int or temporal_steps <= DECIMAL_CARRY_WINDOW:
            raise ValueError(
                "a carry-window endpoint needs twelve source steps and an output tick"
            )
        return self._publish_broadword_source(
            temporal_steps, carry_window=True, shared_cache=shared_cache
        )

    def _resume_owned_broadword_frame(
        self, occurrence: ReversePairOutputOccurrence
    ) -> PackedQ19:
        """Decode the complete pair state from one authenticated endpoint."""
        from number_compiler.sequences.reverse_add.q19_broadword_publisher import (
            PackedQ19,
            pack_q19_pair_lanes,
        )

        self.validate_issued_occurrence(occurrence)
        if occurrence.pair_width >= 256:
            from .q19_periodic_packing import (
                has_nearby_repeat,
                recover_repeated_word,
            )

            if has_nearby_repeat(self.arena, occurrence.root):
                try:
                    return recover_repeated_word(
                        self.arena,
                        occurrence.root,
                        occurrence.pair_width,
                        self.ledger,
                        self._scratch_owner,
                    )
                except BlockContextBudgetExceeded:
                    # A bounded algebraic fold is optional. Its reservation
                    # has closed, so retry the exact streaming decoder.
                    pass
        count = occurrence.pair_width // 2
        odd = bool(occurrence.pair_width & 1)
        with closing(
            iter_symbols(
                self.arena,
                occurrence.root,
                ledger=self.ledger,
                owner=self._scratch_owner,
            )
        ) as symbols:
            if next(symbols, None) != 19 + int(odd):
                raise ValueError("issued Q19 frontier has another width or parity")

            def checked_pairs() -> Iterator[int]:
                for _ in range(count):
                    coefficient = next(symbols, None)
                    if type(coefficient) is not int or not 0 <= coefficient <= 18:
                        raise ValueError(
                            "issued Q19 frontier has an invalid coefficient"
                        )
                    yield coefficient

            pairs = pack_q19_pair_lanes(checked_pairs())
            center = None
            if odd:
                middle = next(symbols, None)
                if type(middle) is not int or middle % 2 or not 0 <= middle <= 18:
                    raise ValueError("issued Q19 frontier has an invalid center")
                center = middle // 2
            if next(symbols, None) != 21 or next(symbols, None) is not None:
                raise ValueError("issued Q19 frontier has an invalid terminal")
        return PackedQ19.from_record((pairs, count, center))

    def _publish_broadword_source(
        self, temporal_steps: int, *, carry_window: bool, shared_cache: bool = False
    ) -> ReversePairOutputOccurrence:
        from number_compiler.resources.lifecycle import cleanup_all, cleanup_on_error
        from number_compiler.sequences.reverse_add.q19_broadword_publisher import (
            PackedQ19,
        )

        self.validate_open()
        if type(temporal_steps) is not int or temporal_steps < 1:
            raise ValueError("physical Q19 endpoint requires positive duration")

        from number_compiler.sequences.reverse_add.q19_carry_window import (
            completed_continuation,
        )

        hint: tuple[int, int] | None = None
        for age in sorted(self._frontiers, reverse=True):
            if age > temporal_steps:
                continue
            entry = self._frontiers.get(age)
            if entry is None:
                continue
            root_hint, guarded = entry
            if carry_window and not guarded:
                continue
            known = self.issued_occurrence((root_hint, age))
            if known is not None:
                self.validate_issued_occurrence(known)
                hint = (age, root_hint)
                break
        if hint is not None and hint[0] == temporal_steps:
            existing = self.issued_occurrence((hint[1], temporal_steps))
            if existing is not None:
                self.validate_issued_occurrence(existing)
                return existing

        # The authenticated zero source never grows; do not reserve a
        # horizon-sized image or prefix ledger for its absorbing action.
        width_bound = (
            1 if self._digits == (0,) else len(self._digits) + temporal_steps - 1
        )
        scratch_nodes = 16 * (width_bound + 3)
        first_new_node = len(self.arena.nodes)
        rollback_publication: ReversePairOutputOccurrence | None = None
        previous_publication: ReversePairOutputOccurrence | None = None

        inserted_frontier = False
        replaced_frontier: tuple[int, bool] | None = None
        evicted_frontier: tuple[int, tuple[int, bool]] | None = None

        def rollback() -> None:
            def remove_inserted() -> None:
                if inserted_frontier and temporal_steps in self._frontiers:
                    del self._frontiers[temporal_steps]

            def restore_evicted() -> None:
                if evicted_frontier is not None:
                    self._frontiers[evicted_frontier[0]] = evicted_frontier[1]

            def restore_replaced() -> None:
                if replaced_frontier is not None:
                    self._frontiers[temporal_steps] = replaced_frontier

            cleanup_all(
                (
                    remove_inserted,
                    restore_evicted,
                    restore_replaced,
                    lambda: self.rollback_punctured_application(
                        first_new_node, rollback_publication, previous_publication
                    ),
                )
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
                resumed_age = 1
                previous = None
                if hint is not None and hint[0] < temporal_steps:
                    previous = self.issued_occurrence((hint[1], hint[0]))
                if previous is None:
                    frame = PackedQ19.from_digits(self._digits)
                else:
                    frame = self._resume_owned_broadword_frame(previous)
                    assert hint is not None
                    resumed_age = hint[0]

                def record_step_work(count: int, rounds: int) -> None:
                    # Logical recurrence accounting, including the bounded
                    # homogeneous prefix; its carry-round charge is zero.
                    self.ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_BROADWORD_SEMANTIC_STEPS
                    )
                    self.ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_BROADWORD_PREFIX_ROUNDS,
                        rounds,
                    )
                    # This is a documented logical-bit estimate: ten fixed
                    # lane-width passes plus two prefix-network passes per
                    # doubling round. It is not an allocation or op counter.
                    logical_operand_bits = 6 * count * (10 + 2 * rounds)
                    self.ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_BROADWORD_OPERAND_BITS,
                        logical_operand_bits,
                    )

                remaining = temporal_steps - resumed_age
                with completed_continuation(
                    frame,
                    remaining,
                    carry_window=carry_window and previous is None,
                    shared_cache=shared_cache,
                    before_step=record_step_work,
                    ledger=self.ledger,
                    scratch_owner=self._scratch_owner,
                ) as (target, reused):
                    reused_prefix = resumed_age - 1 + reused
                    if reused_prefix:
                        self.ledger.bump(
                            _reverse_add_keys.REVERSE_Q19_REUSED_CONTINUATION_STEPS,
                            reused_prefix,
                        )

                    # The ordinary Q19 source-to-output grammar represents the
                    # source frame before its final addition. The terminal result
                    # is therefore issued at temporal_steps from frame X_(n-1).
                    def symbols() -> Iterator[int]:
                        yield 19 + (target.width & 1)
                        for index in range(target.count):
                            yield (target.pairs >> (6 * index)) & 63
                        if target.center is not None:
                            yield 2 * target.center
                        yield 21

                    root = None
                    if target.count >= 128:
                        from .q19_periodic_packing import publish_packed_word

                        root = publish_packed_word(self.arena, target)
                    if root is None:
                        root = self._word(symbols())
                    issue_key = (root, temporal_steps)
                    previous_publication = self.issued_occurrence(issue_key)
                    published = self._issue(*issue_key)
                    rollback_publication = published
                    self.ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_BROADWORD_ENDPOINT_PUBLICATIONS
                    )
                    current_frontier = self._frontiers.get(temporal_steps)
                    if (
                        carry_window
                        and current_frontier is not None
                        and not current_frontier[1]
                    ):
                        replaced_frontier = current_frontier
                        self._frontiers[temporal_steps] = (published.root, True)
                    elif current_frontier is None:
                        self._frontiers[temporal_steps] = (published.root, carry_window)
                        inserted_frontier = True
                        if len(self._frontiers) > 64:
                            oldest = min(self._frontiers)
                            old_root = self._frontiers[oldest]
                            if oldest != temporal_steps:
                                evicted_frontier = (oldest, old_root)
                            del self._frontiers[oldest]
                            if oldest == temporal_steps:
                                inserted_frontier = False
                    return published

    def symbol_at(self, root: int, index: int) -> int:
        return slp_symbol_at(self.arena, root, index)

    def root_width_parity(self, root: int) -> int:
        parity = self.symbol_at(root, 0) - (2 * self.base - 1)
        if parity not in (0, 1):
            raise ValueError("pair output grammar has an invalid parity tag")
        return parity

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
        parity = self.root_width_parity(root)
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
                parity = self.root_width_parity(occurrence.root)
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
