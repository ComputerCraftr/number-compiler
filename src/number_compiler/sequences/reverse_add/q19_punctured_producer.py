"""Transactional publisher for fixed-depth punctured Q19 actions."""

from __future__ import annotations

from typing import TYPE_CHECKING, Protocol

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_on_error
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.sequences.reverse_add.punctured_temporal import (
    PuncturedTemporalWork,
    append_run,
    punctured_pair_runs,
)

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.q19_occurrence import (
        ReversePairOutputOccurrence,
    )
    from number_compiler.sequences.reverse_add.q19_word_summary import _WordSummary


class _OutputOwner(Protocol):
    ledger: ResourceLedger
    arena: LedgerSLPArena
    _digits: tuple[int, ...]
    _scratch_owner: int
    _summaries: OwnedMemo[int, _WordSummary]
    _issued: OwnedMemo[tuple[int, int], ReversePairOutputOccurrence]

    def _check_open(self) -> None: ...

    def validate(self, occurrence: ReversePairOutputOccurrence) -> None: ...

    def _word_summary(self, root: int) -> _WordSummary: ...

    def _candidate(
        self, root: int, temporal_steps: int
    ) -> ReversePairOutputOccurrence: ...

    def _publish(
        self, occurrence: ReversePairOutputOccurrence
    ) -> ReversePairOutputOccurrence: ...


class PuncturedPairProducer:
    """Apply a bounded T2/T4 pullback and publish it transactionally."""

    def __init__(self, owner: _OutputOwner) -> None:
        self._owner = owner

    def apply(
        self, occurrence: ReversePairOutputOccurrence, *, steps: int
    ) -> ReversePairOutputOccurrence:
        owner = self._owner
        owner.validate(occurrence)
        if type(steps) is not int or steps not in (2, 4):
            raise ValueError("punctured Q19 producer admits exact T2 or T4 blocks")

        first_new_node = len(owner.arena.nodes)
        emitted_nodes = 0
        work = PuncturedTemporalWork()
        published: ReversePairOutputOccurrence | None = None
        previous_publication: ReversePairOutputOccurrence | None = None
        recording_started = False

        def rollback() -> None:
            nonlocal emitted_nodes
            emitted_nodes = len(owner.arena.nodes) - first_new_node
            self._rollback(first_new_node, published, previous_publication)

        try:
            with cleanup_on_error(rollback):
                source_summary = owner._word_summary(occurrence.root)
                # T4 keeps one more bounded pullback's run partitions live.
                scratch_per_run = 512 if steps == 2 else 1024
                scratch = scratch_per_run * (source_summary.runs + 1)
                with owner.ledger.reservation(
                    owner._scratch_owner, entries=scratch, nodes=scratch
                ):
                    source_runs = self._coefficient_runs(occurrence.root)
                    output_runs, output_width = punctured_pair_runs(
                        source_runs,
                        odd=bool(occurrence.pair_width & 1),
                        steps=steps,
                        work=work,
                    )
                    target_root = self._run_word(output_runs, output_width, work)
                    candidate = owner._candidate(
                        target_root, occurrence.temporal_steps + steps
                    )
                    width_change = candidate.output_width - occurrence.output_width
                    if not 0 <= width_change <= steps:
                        raise AssertionError(
                            "punctured reverse/add block escaped its per-step width bound"
                        )
                    issue_key = candidate.root, candidate.temporal_steps
                    previous_publication = owner._issued.get(issue_key)
                    published = owner._publish(candidate)
                emitted_nodes = len(owner.arena.nodes) - first_new_node
                recording_started = True
                self._record_work(work, emitted_nodes=emitted_nodes, steps=steps)
            return published
        except BaseException:
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
            _reverse_add_keys.REVERSE_Q19_PUNCTURED_EMITTED_GRAMMAR_NODES,
            emitted_nodes,
        )
        if failed:
            ledger.bump(_reverse_add_keys.REVERSE_Q19_PUNCTURED_FAILED_APPLICATIONS)
        else:
            application_key = (
                _reverse_add_keys.REVERSE_Q19_PUNCTURED_T2_APPLICATIONS
                if steps == 2
                else _reverse_add_keys.REVERSE_Q19_PUNCTURED_T4_APPLICATIONS
            )
            ledger.bump(application_key)

    def _coefficient_runs(self, root: int) -> tuple[tuple[int, int], ...]:
        owner = self._owner
        summary = owner._word_summary(root)
        runs: list[tuple[int, int]] = []
        symbol_count = 0
        tasks: list[tuple[str, int, int]] = [("NODE", root, 1)]
        while tasks:
            kind, node_id, remaining = tasks.pop()
            owner.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_PUNCTURED_INPUT_GRAMMAR_NODES_VISITED
            )
            if kind == "REPEAT_REST":
                if remaining:
                    tasks.append((kind, node_id, remaining - 1))
                    tasks.append(("NODE", node_id, 1))
                continue
            node = owner.arena.nodes[node_id]
            if node.kind == "TERM":
                if 0 <= node.symbol <= 18:
                    append_run(runs, node.symbol, 1)
                    symbol_count += 1
            elif node.kind == "CONCAT":
                tasks.append(("NODE", node.right, 1))
                tasks.append(("NODE", node.left, 1))
            elif node.kind == "REPEAT":
                child_summary = owner._summaries[node.child]
                if child_summary.symbols == 0:
                    continue
                if child_summary.runs == 1:
                    symbol = child_summary.first_symbol
                    if symbol is None:
                        raise AssertionError("nonempty run summary lost its symbol")
                    append_run(runs, symbol, child_summary.symbols * node.count)
                    symbol_count += child_summary.symbols * node.count
                elif node.count:
                    tasks.append(("REPEAT_REST", node.child, node.count - 1))
                    tasks.append(("NODE", node.child, 1))
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
        if published is not None:
            issued_key = published.root, published.temporal_steps
            if owner._issued.get(issued_key) == published:
                if previous_publication is None:
                    del owner._issued[issued_key]
                else:
                    owner._issued[issued_key] = previous_publication
        if type(first_new_node) is not int or not 1 <= first_new_node <= len(
            owner.arena.nodes
        ):
            raise ValueError("invalid Q19 arena transaction boundary")
        while len(owner.arena.nodes) > first_new_node:
            node_id = len(owner.arena.nodes) - 1
            node = owner.arena.nodes[node_id]
            if node_id in owner._summaries:
                del owner._summaries[node_id]
            if node.kind == "TERM":
                if owner.arena._term.get(node.symbol) == node_id:
                    del owner.arena._term[node.symbol]
            elif node.kind == "CONCAT":
                key = node.left, node.right
                if owner.arena._cat.get(key) == node_id:
                    del owner.arena._cat[key]
            elif node.kind == "REPEAT":
                key = node.child, node.count
                if owner.arena._rep.get(key) == node_id:
                    del owner.arena._rep[key]
            else:
                raise AssertionError("cannot roll back the Q19 empty node")
            # _add_interned can append a node before a mapping assignment fails.
            # Only erase an interner entry when it still names this exact node.
            owner.arena._nodes_store._rollback_unpublished(node_id)
            owner.ledger.release(owner.arena.owners[0], entries=1, nodes=1)


__all__ = ["PuncturedPairProducer"]
