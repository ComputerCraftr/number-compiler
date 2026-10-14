"""Balanced composition of demanded normalized Collatz carry fields.

The source cylinder authenticates the parity block. The chronological sum is
an affine action over that cylinder; absolute history stays in the occurrence
context and never enters the cached semantic action.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Self

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.sequences.collatz.joint_cylinder_cache import (
    JointCertifiedMacroCache,
)

_MAX_JOINT_COEFFICIENT_BITS = 1_000_000
_D8_BATCH_VALIDATION_ISSUER = object()
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
        CollatzDyadicOccurrence,
    )
    from number_compiler.sequences.collatz.tape_width import CollatzTapeWidthSummary


@dataclass(frozen=True, slots=True)
class CollatzJointRunAction:
    """Source-bound completed joint action for one normalized run result."""

    source: int
    endpoint: int
    normalized_endpoint: int
    physical_ticks: int
    normalized_steps: int
    odd_symbols: int
    phase: int
    fields: DyadicTerminalFieldAction

    def __post_init__(self) -> None:
        integers = (
            self.source,
            self.endpoint,
            self.normalized_endpoint,
            self.physical_ticks,
            self.normalized_steps,
            self.odd_symbols,
            self.phase,
        )
        if any(type(value) is not int for value in integers):
            raise TypeError("joint run occurrence requires exact integer coordinates")
        if type(self.fields) is not DyadicTerminalFieldAction:
            raise TypeError("joint run occurrence requires its canonical field action")
        if not self.fields.producer_issued:
            raise ValueError("joint run occurrence needs a producer-issued action")
        if (
            self.source <= 0
            or self.endpoint <= 0
            or self.normalized_endpoint <= 0
            or self.physical_ticks < 0
            or self.normalized_steps < 0
            or self.odd_symbols < 0
            or self.phase not in (0, 1)
        ):
            raise ValueError("joint run occurrence has an invalid extent")
        if (
            self.fields.steps != self.normalized_steps
            or self.normalized_steps + self.odd_symbols + self.phase
            != self.physical_ticks
        ):
            raise ValueError("joint run clocks do not compose")
        if self.fields.endpoint(self.source) != self.normalized_endpoint:
            raise ValueError("joint affine action differs from its source endpoint")
        expected_endpoint = (
            self.normalized_endpoint
            if self.phase == 0
            else 3 * self.normalized_endpoint + 1
        )
        if self.endpoint != expected_endpoint:
            raise ValueError("joint normalized endpoint differs from physical endpoint")

    def normalized_accumulator_residue(self, modulus: int) -> int:
        """Sum the source and normalized successors, excluding odd half-steps."""
        modulus = require_integer(modulus, "accumulator modulus", 2)
        if self.normalized_steps == 0:
            return self.source % modulus
        return (
            self.source % modulus + self.fields.sum_mod(self.source, modulus)
        ) % modulus

    def accumulator_observation(self, modulus: int) -> CollatzAccumulatorObservation:
        return CollatzAccumulatorObservation(
            modulus,
            self.normalized_accumulator_residue(modulus),
            True,
            self.physical_ticks,
            self.normalized_steps,
            self.phase,
        )

    def root_port_payload(self) -> tuple[int, ...]:
        """Return the complete primitive wire payload for a root image port."""
        if not self.fields.producer_issued:
            raise ValueError("joint root port requires a producer-issued action")
        return (
            self.source,
            self.endpoint,
            self.normalized_endpoint,
            self.physical_ticks,
            self.normalized_steps,
            self.odd_symbols,
            self.phase,
            self.fields.gain,
            self.fields.offset,
            self.fields.sum_gain,
            self.fields.sum_offset,
            self.fields.previous_gain,
            self.fields.previous_offset,
        )

    @classmethod
    def _from_admitted_root_payload(cls, payload: object) -> CollatzJointRunAction:
        """Rehydrate only after a root-image owner has authenticated the tuple."""
        if (
            type(payload) is not tuple
            or len(payload) != 13
            or any(type(value) is not int for value in payload)
        ):
            raise ValueError("admitted Collatz root joint payload is malformed")
        source, endpoint, normalized_endpoint, physical, normalized, odd, phase = (
            payload[:7]
        )
        fields = DyadicTerminalFieldAction._restore_issued(normalized, payload[7:])
        return cls(
            source,
            endpoint,
            normalized_endpoint,
            physical,
            normalized,
            odd,
            phase,
            fields,
        )


@dataclass(frozen=True, slots=True)
class CollatzAccumulatorObservation:
    """Typed residue of the source plus normalized successor states."""

    modulus: int
    normalized_accumulator_residue: int
    source_included: bool
    physical_ticks: int
    normalized_symbols: int
    phase: int

    def __post_init__(self) -> None:
        values = (
            self.modulus,
            self.normalized_accumulator_residue,
            self.physical_ticks,
            self.normalized_symbols,
            self.phase,
        )
        if any(type(value) is not int for value in values):
            raise TypeError("Collatz accumulator observation needs exact integers")
        if type(self.source_included) is not bool or not self.source_included:
            raise ValueError("Collatz accumulator always includes its source")
        if (
            self.modulus < 2
            or not 0 <= self.normalized_accumulator_residue < self.modulus
            or self.physical_ticks < 0
            or self.normalized_symbols < 0
            or self.normalized_symbols > self.physical_ticks
            or self.phase not in (0, 1)
        ):
            raise ValueError("Collatz accumulator observation has invalid metadata")


class JointTemporalSpine:
    """Online binary frontier; retains logarithmically many action blocks."""

    __slots__ = (
        "_cursor_source",
        "_ledger",
        "_levels",
        "_root_source",
        "_scratch",
        "requested",
    )

    def __init__(
        self,
        ledger: ResourceLedger,
        scratch: RunArithmeticWorkspace,
        root_source: int,
        *,
        requested: bool,
    ) -> None:
        if (
            type(ledger) is not ResourceLedger
            or type(scratch) is not RunArithmeticWorkspace
            or scratch.ledger is not ledger
            or type(root_source) is not int
            or root_source <= 0
            or type(requested) is not bool
        ):
            raise TypeError("joint spine requires its ledger and Boolean demand")
        self._ledger = ledger
        self._scratch = scratch
        self.requested = requested
        self._cursor_source = root_source
        owner = ledger.register(
            f"collatz-joint-spine-{ledger.owner_count}", "query_memo"
        )
        self._levels: OwnedMemo[int, tuple[DyadicTerminalFieldAction, int]] = OwnedMemo(
            ledger,
            owner,
            node_cost=lambda _rank, item: self._action_nodes(item[0]),
            evictable=False,
        )
        self._root_source = root_source

    def append(
        self,
        action: DyadicTerminalFieldAction,
        source: int,
        odd_symbols: int,
    ) -> None:
        if not self.requested:
            return
        if type(action) is not DyadicTerminalFieldAction:
            raise TypeError("joint spine accepts only canonical field actions")
        if not action.producer_issued:
            raise ValueError("joint spine accepts only producer-issued actions")
        source = require_integer(source, "joint spine block source", 1)
        if source != self._cursor_source:
            raise ValueError("joint spine block is not chronological at its source")
        if type(odd_symbols) is not int or not 0 <= odd_symbols <= action.steps:
            raise ValueError("joint spine odd count differs from block extent")
        if not action.certifies(source):
            raise ValueError("joint block source is outside its parity cylinder")
        if action.steps == 0:
            if odd_symbols:
                raise ValueError("identity joint block cannot contain odd symbols")
            return
        self._append_frontier(action, odd_symbols)
        self._cursor_source = action.endpoint(source)

    def _append_checked_d8_batch(
        self,
        action: DyadicTerminalFieldAction,
        source: int,
        odd_symbols: int,
        endpoint: int,
        *,
        issuer: object,
    ) -> None:
        if issuer is not _D8_BATCH_VALIDATION_ISSUER:
            raise ValueError("D8 batch endpoint lacks its checked frame authority")
        if (
            type(action) is not DyadicTerminalFieldAction
            or not action.producer_issued
            or source != self._cursor_source
            or not action.certifies(source)
            or type(odd_symbols) is not int
            or not 0 <= odd_symbols <= action.steps
            or type(endpoint) is not int
            or endpoint <= 0
        ):
            raise ValueError("checked D8 batch differs from its joint spine")
        self._append_frontier(action, odd_symbols)
        self._cursor_source = endpoint

    def _append_frontier(
        self, action: DyadicTerminalFieldAction, odd_symbols: int
    ) -> None:
        rank = 0
        while rank in self._levels:
            left, left_ones = self._levels[rank]
            del self._levels[rank]
            action = self._compose(left, action)
            odd_symbols += left_ones
            rank += 1
        self._levels[rank] = (action, odd_symbols)

    @staticmethod
    def _action_nodes(action: DyadicTerminalFieldAction) -> int:
        return 8 + sum(
            (max(1, value.bit_length()) + 63) // 64
            for value in (
                action.gain,
                action.offset,
                action.sum_gain,
                action.sum_offset,
                action.previous_gain,
                action.previous_offset,
            )
        )

    def finish_fields(self, source: int) -> tuple[DyadicTerminalFieldAction, int]:
        """Consume the balanced frontier and return its exact composed action."""
        if not self.requested:
            return DyadicTerminalFieldAction.identity(), 0
        if self._root_source != source:
            raise ValueError("joint spine belongs to another root source")
        fields = DyadicTerminalFieldAction.identity()
        counted_ones = 0
        try:
            for rank in sorted(self._levels, reverse=True):
                action, ones = self._levels[rank]
                fields = action if fields.steps == 0 else self._compose(fields, action)
                counted_ones += ones
            return fields, counted_ones
        finally:
            self._levels.clear()

    def finish(
        self,
        source: int,
        endpoint: int,
        normalized_endpoint: int,
        physical_ticks: int,
        normalized_steps: int,
        odd_symbols: int,
        phase: int,
    ) -> CollatzJointRunAction | None:
        if not self.requested:
            return None
        fields, counted_ones = self.finish_fields(source)
        if fields.steps != normalized_steps or counted_ones != odd_symbols:
            raise ValueError("joint spine extent differs from physical run clocks")
        return CollatzJointRunAction(
            source,
            endpoint,
            normalized_endpoint,
            physical_ticks,
            normalized_steps,
            odd_symbols,
            phase,
            fields,
        )

    def _compose(
        self,
        before: DyadicTerminalFieldAction,
        after: DyadicTerminalFieldAction,
    ) -> DyadicTerminalFieldAction:
        required_bits = (
            sum(
                max(1, value.bit_length())
                for value in (
                    before.gain,
                    before.offset,
                    before.sum_gain,
                    before.sum_offset,
                    before.previous_gain,
                    before.previous_offset,
                    after.gain,
                    after.offset,
                    after.sum_gain,
                    after.sum_offset,
                    after.previous_gain,
                    after.previous_offset,
                )
            )
            + 2 * (before.steps + after.steps)
            + 64
        )
        self._scratch.require_bits(8 * required_bits)
        result = before.then(after)
        self._ledger.bump("collatz_hashlife_joint_parent_joins")
        self._ledger.bump(
            "collatz_hashlife_joint_operand_bits",
            sum(
                max(1, abs(value).bit_length())
                for value in (
                    before.gain,
                    before.offset,
                    before.sum_gain,
                    before.sum_offset,
                    after.gain,
                    after.offset,
                    after.sum_gain,
                    after.sum_offset,
                )
            ),
        )
        return result

    def close(self) -> None:
        self._levels.dispose()


class CollatzJointTemporalBuilder:
    """Demand-scoped publisher for one source's complete joint field action."""

    __slots__ = (
        "_closed",
        "_context_entered",
        "_d8_batch_levels",
        "_d8_batch_odd",
        "_d8_batch_source",
        "_d8_batch_steps",
        "cache",
        "ledger",
        "requested",
        "scratch",
        "source",
        "spine",
    )

    def __init__(
        self,
        ledger: ResourceLedger,
        scratch: RunArithmeticWorkspace,
        source: int,
        *,
        requested: bool,
        shared_cache: bool,
    ) -> None:
        self.ledger = ledger
        self.scratch = scratch
        self.source = source
        self.requested = requested
        self._d8_batch_levels: (
            OwnedMemo[int, tuple[DyadicTerminalFieldAction, int]] | None
        ) = None
        self._d8_batch_odd = 0
        self._d8_batch_source: int | None = None
        self._d8_batch_steps = 0
        self._context_entered = False
        self._closed = False
        self.spine: JointTemporalSpine | None = None
        self.cache: JointCertifiedMacroCache | None = None
        try:
            if requested:
                batch_owner = ledger.register(
                    f"collatz-joint-d8-batch-{ledger.owner_count}",
                    "execution_stack",
                )
                self._d8_batch_levels = OwnedMemo(
                    ledger,
                    batch_owner,
                    node_cost=lambda _rank, item: JointTemporalSpine._action_nodes(
                        item[0]
                    ),
                    evictable=False,
                )
                self.spine = JointTemporalSpine(ledger, scratch, source, requested=True)
                self.cache = JointCertifiedMacroCache(ledger, shared_cache=shared_cache)
        except BaseException:
            try:
                if self.cache is not None:
                    self.cache.__exit__(None, None, None)
            finally:
                try:
                    if self._d8_batch_levels is not None:
                        self._d8_batch_levels.dispose()
                finally:
                    if self.spine is not None:
                        self.spine.close()
            raise

    def __enter__(self) -> Self:
        if self._closed:
            raise RuntimeError("joint temporal builder is closed")
        if self._context_entered:
            raise RuntimeError("joint temporal builder cannot be entered twice")
        try:
            if self.cache is not None:
                self.cache.__enter__()
        except BaseException as enter_error:
            try:
                self._close(None, None, None)
            except BaseException as cleanup_error:
                raise cleanup_error from enter_error
            raise
        self._context_entered = True
        return self

    def __exit__(self, *_args: object) -> None:
        self._close(*_args)

    def _close(self, *args: object) -> None:
        if self._closed:
            return
        self._closed = True
        try:
            if self._d8_batch_levels is not None:
                self._d8_batch_levels.dispose()
        finally:
            try:
                if self.spine is not None:
                    self.spine.close()
            finally:
                if self.cache is not None:
                    self.cache.__exit__(*args)

    def require_steps(self, source: int, steps: int) -> None:
        if not self.requested:
            return
        estimated = source.bit_length() + 2 * steps + 128
        if estimated > _MAX_JOINT_COEFFICIENT_BITS:
            raise BlockContextBudgetExceeded(
                "optional exact Collatz joint action exceeds its coefficient bound"
            )
        self.scratch.require_bits(8 * estimated)

    def append(
        self,
        action: DyadicTerminalFieldAction,
        source: int,
        odd_symbols: int,
        endpoint: int,
        *,
        cache: bool = True,
    ) -> None:
        if not self.requested:
            return
        if not action.producer_issued or action.endpoint(source) != endpoint:
            raise ValueError("joint action differs from its source producer")
        if self.spine is None:
            raise RuntimeError("joint spine was not requested")
        self.spine.append(action, source, odd_symbols)
        if self.cache is not None and cache:
            self.cache.observe(
                source, action, odd_symbols, endpoint, anchor=self.source
            )

    def begin_d8_batch(self, source: int) -> None:
        levels = self._d8_batch_levels
        if not self.requested or self.spine is None or levels is None:
            raise RuntimeError("joint D8 batch was not requested")
        if self._d8_batch_source is not None or source != self.spine._cursor_source:
            raise ValueError("joint D8 batch does not begin at the current source")
        # D8 frame publication bypasses the observed dyadic frontier.  A
        # prior composite return or cached macro may leave a shorter pending
        # block there; it must not be joined across this unobserved frame.
        if self.cache is not None:
            self.cache.frontier.clear()
        self._d8_batch_source = source
        self._d8_batch_steps = 0
        self._d8_batch_odd = 0
        levels.clear()

    def append_d8_transition(
        self,
        action: DyadicTerminalFieldAction,
        odd_symbols: int,
        source_residue: int,
    ) -> None:
        """Accumulate an issued D8 action using only its eight-bit germ."""
        levels = self._d8_batch_levels
        spine = self.spine
        if self._d8_batch_source is None or levels is None or spine is None:
            raise ValueError("joint D8 action has no active frame batch")
        if (
            type(action) is not DyadicTerminalFieldAction
            or not action.producer_issued
            or action.steps != 8
            or type(odd_symbols) is not int
            or not 0 <= odd_symbols <= 8
            or type(source_residue) is not int
            or not 0 <= source_residue < 256
            or action.source_residue != source_residue
            or action.gain != 3**odd_symbols
        ):
            raise ValueError("joint D8 action differs from its selected frame row")
        self._d8_batch_steps += 8
        self._d8_batch_odd += odd_symbols
        rank = 0
        while rank in levels:
            before, before_odd = levels.pop(rank)
            action = spine._compose(before, action)
            odd_symbols += before_odd
            rank += 1
        levels[rank] = (action, odd_symbols)

    def finish_d8_batch(
        self,
        macros: CollatzDyadicMacros | None,
        frame: object,
    ) -> int:
        """Authenticate a balanced frame batch and use one exact endpoint."""
        from number_compiler.sequences.collatz.temporal_dyadic import D8CylinderFrame

        source = self._d8_batch_source
        levels = self._d8_batch_levels
        spine = self.spine
        if (
            source is None
            or levels is None
            or type(frame) is not D8CylinderFrame
            or frame.source != source
            or frame.consumed != self._d8_batch_steps
            or not levels
            or spine is None
        ):
            raise ValueError("joint D8 batch frame differs from its selected actions")
        action = DyadicTerminalFieldAction.identity()
        composed_odd = 0
        for rank in sorted(levels, reverse=True):
            part, part_odd = levels[rank]
            action = part if action.steps == 0 else spine._compose(action, part)
            composed_odd += part_odd
        steps = self._d8_batch_steps
        denominator = 1 << steps
        residue = source & (denominator - 1)
        if (
            action.steps != steps
            or composed_odd != self._d8_batch_odd
            or action.gain != frame.gain
            or action.offset != denominator * frame.origin - frame.gain * residue
            or not action.certifies(source)
        ):
            raise ValueError("composed joint D8 action differs from its frame")
        odd_count = self._d8_batch_odd
        # The exact endpoint comes from the frame only after the composed
        # producer action has been checked against its source and affine
        # coordinates. Callers cannot inject an unrelated cached integer.
        endpoint = frame.materialize()
        self.ledger.bump("collatz_physical_temporal_d8_frame_materializations")
        self.ledger.bump("collatz_physical_temporal_d8_endpoint_evaluations")
        self.ledger.bump(
            "collatz_physical_temporal_run_operand_bits",
            source.bit_length() + frame.gain.bit_length() + endpoint.bit_length(),
        )
        spine._append_checked_d8_batch(
            action,
            source,
            odd_count,
            endpoint,
            issuer=_D8_BATCH_VALIDATION_ISSUER,
        )
        self._d8_batch_source = None
        self._d8_batch_steps = 0
        self._d8_batch_odd = 0
        levels.clear()
        if (
            source == self.source
            and steps >= 16
            and steps & (steps - 1) == 0
            and endpoint > 2
        ):
            if self.cache is not None:
                self.cache.remember(source, action, odd_count)
            if macros is not None:
                macros.remember(source, steps, odd_count, endpoint)
        self.ledger.bump(
            "collatz_hashlife_joint_d8_batches",
        )
        return endpoint

    def append_run(self, source: int, length: int, *, odd: bool) -> None:
        if not self.requested:
            return
        self.require_steps(source, length)
        action = (
            DyadicTerminalFieldAction.one_run(length)
            if odd
            else DyadicTerminalFieldAction.zero_run(length)
        )
        endpoint = action.endpoint(source)
        self.append(
            action,
            source,
            length if odd else 0,
            endpoint,
            cache=False,
        )
        if self.cache is None:
            return
        remaining = length
        chunk_source = source
        while remaining:
            chunk = 1 << (remaining.bit_length() - 1)
            self.require_steps(chunk_source, chunk)
            part = (
                action
                if chunk == length
                else (
                    DyadicTerminalFieldAction.one_run(chunk)
                    if odd
                    else DyadicTerminalFieldAction.zero_run(chunk)
                )
            )
            part_endpoint = part.endpoint(chunk_source)
            self.cache.observe(
                chunk_source,
                part,
                chunk if odd else 0,
                part_endpoint,
                anchor=self.source,
            )
            chunk_source = part_endpoint
            remaining -= chunk

    def append_cycle(self, source: int, repetitions: int) -> None:
        if not self.requested:
            return
        steps = 2 * repetitions
        self.require_steps(source, steps)
        motif = DyadicTerminalFieldAction.one_run(1).then(
            DyadicTerminalFieldAction.zero_run(1)
        )
        action = motif.power(repetitions)
        self.append(action, source, repetitions, action.endpoint(source))

    def applied_cached_macro(self) -> None:
        if self.cache is None:
            raise RuntimeError("joint macro cache was not requested")
        self.cache.applied()

    def lookup_largest_macro(
        self,
        macros: CollatzDyadicMacros,
        source: int,
        width: int,
        physical_ticks: int,
        *,
        include_width: bool,
    ) -> (
        tuple[
            CollatzDyadicOccurrence,
            tuple[DyadicTerminalFieldAction, int],
            CollatzTapeWidthSummary | None,
            int,
        ]
        | None
    ):
        """Find the largest endpoint macro with its matching joint action."""
        if self.cache is None:
            raise RuntimeError("joint macro lookup was not requested")
        if type(include_width) is not bool:
            raise TypeError("joint macro width demand must be Boolean")
        width = min(width, JointCertifiedMacroCache.MAX_WIDTH)
        cell = macros.lookup_largest(source, width, physical_ticks)
        while cell is not None:
            record = self.cache.lookup(source, cell.width)
            if record is not None:
                action, odd_symbols = record
                endpoint = cell.apply(source)
                if (
                    action.steps != cell.width
                    or odd_symbols != cell.odd_symbols
                    or action.gain != cell.multiplier
                    or action.endpoint(source) != endpoint
                ):
                    raise ValueError(
                        "joint macro differs from admitted endpoint occurrence"
                    )
                self.ledger.bump(
                    "collatz_hashlife_joint_endpoint_crosscheck_operand_bits",
                    source.bit_length()
                    + endpoint.bit_length()
                    + action.gain.bit_length()
                    + action.offset.bit_length(),
                )
                summary = (
                    macros.lookup_width_summary(source, cell.width)
                    if include_width
                    else None
                )
                if summary is not None and (
                    summary.source_width != source.bit_length()
                    or summary.normalized_symbols != cell.width
                    or summary.odd_steps != cell.odd_symbols
                    or summary.physical_ticks != cell.width + cell.odd_symbols
                    or summary.target_width != endpoint.bit_length()
                ):
                    raise ValueError("joint macro width differs from its endpoint")
                return cell, record, summary, endpoint
            cell = macros.lookup_largest(source, cell.width // 2, physical_ticks)
        return None

    def finish(
        self,
        source: int,
        endpoint: int,
        normalized_endpoint: int,
        physical_ticks: int,
        normalized_steps: int,
        odd_symbols: int,
        phase: int,
    ) -> CollatzJointRunAction | None:
        if not self.requested:
            return None
        if self.spine is None:
            raise RuntimeError("joint spine was not requested")
        return self.spine.finish(
            source,
            endpoint,
            normalized_endpoint,
            physical_ticks,
            normalized_steps,
            odd_symbols,
            phase,
        )


__all__ = [
    "CollatzAccumulatorObservation",
    "CollatzJointRunAction",
    "CollatzJointTemporalBuilder",
    "JointTemporalSpine",
]
