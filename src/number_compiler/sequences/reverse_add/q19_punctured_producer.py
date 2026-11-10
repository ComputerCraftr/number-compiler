"""Transactional publisher for finite group-ring/carry Q19 macros."""

from __future__ import annotations

from typing import TYPE_CHECKING, Protocol

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import BimachineSLPProjector
from number_compiler.arithmetic.fields.run_pairing import append_run
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.lifecycle import cleanup_on_error
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.sequences.reverse_add.punctured_temporal import (
    MAX_PUNCTURED_TEMPORAL_STEPS,
    PuncturedTemporalWork,
    punctured_pair_runs,
)
from number_compiler.sequences.reverse_add.temporal_port_quotient import (
    MAX_EXACT_DECIMAL_BLOCK_WIDTH,
)

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.q19_occurrence import (
        ReversePairOutputOccurrence,
    )
    from number_compiler.sequences.reverse_add.q19_word_summary import (
        FrozenPairStepLaw,
        WordSummary,
    )


def admits_punctured_scheduler_block(steps: int, source_width: int) -> bool:
    """Bound finite attempts, including the scheduler's authenticated T3 tail.

    Oversized native requests remain available through smaller exact children.
    This predicate selects an attempt; the issuer still authenticates its source.
    """
    return (steps in (2, 3, 4) or 16 <= steps <= MAX_PUNCTURED_TEMPORAL_STEPS) and (
        steps <= 32 or source_width + steps <= MAX_EXACT_DECIMAL_BLOCK_WIDTH
    )


class _OutputOwner(Protocol):
    ledger: ResourceLedger
    arena: LedgerSLPArena
    machine: FrozenPairStepLaw
    projector: BimachineSLPProjector

    def validate(self, occurrence: ReversePairOutputOccurrence) -> None: ...

    def validate_issued_occurrence(
        self, occurrence: ReversePairOutputOccurrence
    ) -> None: ...

    def word_summary(self, root: int) -> WordSummary: ...

    @property
    def scratch_owner(self) -> int: ...

    def published_word_summary(self, root: int) -> WordSummary: ...

    def discard_published_word_summary(self, root: int) -> None: ...

    def candidate(
        self, root: int, temporal_steps: int
    ) -> ReversePairOutputOccurrence: ...

    def publish(
        self, occurrence: ReversePairOutputOccurrence
    ) -> ReversePairOutputOccurrence: ...

    def issued_occurrence(
        self, key: tuple[int, int]
    ) -> ReversePairOutputOccurrence | None: ...

    def rollback_punctured_application(
        self,
        first_new_node: int,
        published: ReversePairOutputOccurrence | None,
        previous_publication: ReversePairOutputOccurrence | None,
    ) -> None: ...


class PuncturedPairProducer:
    """Apply a bounded finite Q19 action and publish only its endpoint."""

    def __init__(self, owner: _OutputOwner) -> None:
        self._owner = owner

    def apply(
        self, occurrence: ReversePairOutputOccurrence, *, steps: int
    ) -> ReversePairOutputOccurrence:
        owner = self._owner
        owner.validate(occurrence)
        if type(steps) is not int or not (
            steps in (2, 4) or 16 <= steps <= MAX_PUNCTURED_TEMPORAL_STEPS
        ):
            raise ValueError("punctured Q19 producer exceeds its finite bound")

        first_new_node = len(owner.arena.nodes)
        emitted_nodes = 0
        work = PuncturedTemporalWork()
        published: ReversePairOutputOccurrence | None = None
        previous_publication: ReversePairOutputOccurrence | None = None
        recording_started = False
        symbolic_projector_used = False

        def rollback() -> None:
            nonlocal emitted_nodes
            emitted_nodes = len(owner.arena.nodes) - first_new_node
            self._rollback(first_new_node, published, previous_publication)

        try:
            with cleanup_on_error(rollback):
                source_summary = owner.word_summary(occurrence.root)
                # Nonuniform spatial repeats stay compressed for every admitted
                # horizon. The projector still executes each physical tick;
                # spatial repetition does not authorize temporal repetition.
                symbolic = self._has_pumped_nonuniform_band(occurrence.root)
                if symbolic:
                    # Match the existing one-step projector's scratch envelope,
                    # composed over this bounded physical action.
                    scratch = 64 * steps * (len(owner.arena.nodes) + 1)
                elif (
                    steps >= 16
                    and occurrence.output_width + steps <= MAX_EXACT_DECIMAL_BLOCK_WIDTH
                ):
                    scratch = 2 * (occurrence.output_width + steps) + 32 * (
                        source_summary.runs + 1
                    )
                else:
                    scratch = 512 * steps * (source_summary.runs + 1)
                with owner.ledger.reservation(
                    owner.scratch_owner, entries=scratch, nodes=scratch
                ):
                    if symbolic:
                        # Reuse the owner's ledger-backed SLP projector. If
                        # later publication fails, its cache must be cleared
                        # before rolled-back node IDs can be observed again.
                        projector = owner.projector
                        symbolic_projector_used = True
                        sections_before = projector.section_calls
                        try:
                            target_root = occurrence.root
                            for completed in range(1, steps + 1):
                                target_root = projector.apply(target_root)
                                work.spatial_projector_steps += 1
                                work.half_tape_tick_transitions += 1
                                if completed % 2 == 0:
                                    work.two_step_actions += 1
                        finally:
                            work.spatial_projector_sections += (
                                projector.section_calls - sections_before
                            )
                    else:
                        source_runs = self._coefficient_runs(occurrence.root)
                        output_runs, output_width = punctured_pair_runs(
                            source_runs,
                            odd=bool(occurrence.pair_width & 1),
                            steps=steps,
                            work=work,
                        )
                        target_root = self._run_word(output_runs, output_width, work)
                    issue_key = (
                        target_root,
                        occurrence.temporal_steps + steps,
                    )
                    previous_publication = owner.issued_occurrence(issue_key)
                    if previous_publication is not None:
                        # This exact owner-issued root is the only warm key.
                        # Authenticate it without repeating the full-field fold.
                        owner.validate_issued_occurrence(previous_publication)
                        published = previous_publication
                    else:
                        candidate = owner.candidate(*issue_key)
                        published = owner.publish(candidate)
                    width_change = published.output_width - occurrence.output_width
                    if not 0 <= width_change <= steps:
                        raise AssertionError(
                            "punctured reverse/add block escaped its per-step width bound"
                        )
                emitted_nodes = len(owner.arena.nodes) - first_new_node
                recording_started = True
                self._record_work(work, emitted_nodes=emitted_nodes, steps=steps)
            return published
        except BaseException:
            if symbolic_projector_used:
                owner.projector.clear_caches()
            if recording_started:
                owner.ledger.bump(
                    _reverse_add_keys.REVERSE_Q19_PUNCTURED_FAILED_APPLICATIONS
                )
            else:
                self._record_work(
                    work, emitted_nodes=emitted_nodes, steps=steps, failed=True
                )
            raise

    def _record_work(
        self,
        work: PuncturedTemporalWork,
        *,
        emitted_nodes: int,
        steps: int,
        failed: bool = False,
    ) -> None:
        ledger = self._owner.ledger
        ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PUNCTURED_PREFIX_RUN_VISITS,
            work.run_records_visited,
        )
        ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PUNCTURED_PREFIX_QUERIES,
            work.prefix_queries,
        )
        ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PUNCTURED_EVENT_REGIONS, work.event_regions
        )
        ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PUNCTURED_OUTPUT_RUNS, work.output_runs
        )
        ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PUNCTURED_PHYSICAL_T2_ACTIONS,
            work.two_step_actions,
        )
        ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PUNCTURED_HALF_TAPE_TICK_TRANSITIONS,
            work.half_tape_tick_transitions,
        )
        ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PUNCTURED_NATIVE_DECIMAL_TICKS,
            work.native_decimal_ticks,
        )
        ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PUNCTURED_NATIVE_DECIMAL_DIGIT_VISITS,
            work.native_decimal_digit_visits,
        )
        ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PUNCTURED_SPATIAL_PROJECTOR_STEPS,
            work.spatial_projector_steps,
        )
        ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PUNCTURED_SPATIAL_PROJECTOR_SECTIONS,
            work.spatial_projector_sections,
        )
        ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PUNCTURED_EMITTED_GRAMMAR_NODES,
            emitted_nodes,
        )
        if failed:
            ledger.bump(_reverse_add_keys.REVERSE_Q19_PUNCTURED_FAILED_APPLICATIONS)
        else:
            application_key = {
                2: _reverse_add_keys.REVERSE_Q19_PUNCTURED_T2_APPLICATIONS,
                4: _reverse_add_keys.REVERSE_Q19_PUNCTURED_T4_APPLICATIONS,
                16: _reverse_add_keys.REVERSE_Q19_PUNCTURED_T16_APPLICATIONS,
                32: _reverse_add_keys.REVERSE_Q19_PUNCTURED_T32_APPLICATIONS,
            }.get(steps, _reverse_add_keys.REVERSE_Q19_PUNCTURED_WIDE_APPLICATIONS)
            ledger.bump(application_key)

    def _has_pumped_nonuniform_band(self, root: int) -> bool:
        """Inspect the reachable SLP DAG without visiting represented copies."""
        owner = self._owner
        # Reserve the reachable-worklist upper bound before allocating it. The
        # guard visits DAG nodes, never copies represented by a REPEAT exponent.
        with owner.ledger.reservation(
            owner.scratch_owner,
            entries=3 * len(owner.arena.nodes) + 1,
            nodes=3 * len(owner.arena.nodes) + 1,
        ):
            todo = [root]
            seen: set[int] = set()
            try:
                while todo:
                    node_id = todo.pop()
                    if node_id in seen:
                        continue
                    seen.add(node_id)
                    owner.ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_PUNCTURED_REPEAT_GUARD_NODE_VISITS
                    )
                    node = owner.arena.nodes[node_id]
                    if node.kind == "REPEAT":
                        if node.count > 1:
                            summary = owner.published_word_summary(node.child)
                            if summary.runs > 1:
                                return True
                        todo.append(node.child)
                    elif node.kind == "CONCAT":
                        todo.extend((node.left, node.right))
                return False
            finally:
                todo.clear()
                seen.clear()

    def _coefficient_runs(self, root: int) -> tuple[tuple[int, int], ...]:
        owner = self._owner
        summary = owner.word_summary(root)
        runs: list[tuple[int, int]] = []
        symbol_count = 0
        tasks = [root]
        while tasks:
            node_id = tasks.pop()
            owner.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_PUNCTURED_INPUT_GRAMMAR_NODES_VISITED
            )
            node = owner.arena.nodes[node_id]
            if node.kind == "TERM":
                if 0 <= node.symbol <= 18:
                    append_run(runs, node.symbol, 1)
                    symbol_count += 1
            elif node.kind == "CONCAT":
                tasks.append(node.right)
                tasks.append(node.left)
            elif node.kind == "REPEAT":
                child_summary = owner.published_word_summary(node.child)
                if child_summary.symbols == 0:
                    continue
                if child_summary.runs == 1:
                    symbol = child_summary.first_symbol
                    if symbol is None:
                        raise AssertionError("nonempty run summary lost its symbol")
                    append_run(runs, symbol, child_summary.symbols * node.count)
                    symbol_count += child_summary.symbols * node.count
                elif node.count == 1:
                    tasks.append(node.child)
                elif node.count:
                    raise AssertionError(
                        "nonuniform repeated grammar requires the spatial projector"
                    )
            elif node.kind != "EMPTY":
                raise AssertionError(node.kind)
        if symbol_count != summary.symbols:
            raise AssertionError("punctured source runs changed pair-half extent")
        if len(runs) != summary.runs:
            raise AssertionError("punctured source runs changed canonical run count")
        owner.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_PUNCTURED_RUN_RECORDS_VISITED, len(runs)
        )
        return tuple(runs)

    def _run_word(
        self,
        half_runs: tuple[tuple[int, int], ...],
        width: int,
        work: PuncturedTemporalWork,
    ) -> int:
        owner = self._owner
        if not half_runs or type(width) is not int or width < 1:
            raise ValueError("punctured output requires a positive pair field")
        parts = [owner.arena.terminal(19 + (width & 1))]
        half_width = 0
        for symbol, count in half_runs:
            work.run_records_visited += 1
            if type(symbol) is not int or not 0 <= symbol <= 18:
                raise ValueError("punctured output coefficient is outside Q19")
            if type(count) is not int or count < 1:
                raise ValueError("punctured output run length must be positive")
            half_width += count
            parts.append(owner.arena.repeat(owner.arena.terminal(symbol), count))
        if 2 * half_width - (width & 1) != width:
            raise ValueError("punctured output runs disagree with center parity")
        parts.append(owner.arena.terminal(21))
        return owner.arena.concat_many(parts)

    def _rollback(
        self,
        first_new_node: int,
        published: ReversePairOutputOccurrence | None,
        previous_publication: ReversePairOutputOccurrence | None,
    ) -> None:
        owner = self._owner
        owner.rollback_punctured_application(
            first_new_node, published, previous_publication
        )


__all__ = ["PuncturedPairProducer"]
