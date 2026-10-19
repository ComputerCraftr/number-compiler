"""Persistent, source-bound Mahler odd-event compiler; not a TM scheduler.

Only *proved* repeated parity words are powered.  The result retains a
compressed list of authentic fragments, separate ledger and fractional
predicates, and an optional demanded joint carry/borrow harmonic projection.
Ordinary Antihydra physical execution never constructs these port packets.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.antihydra.mahler_odd_macro import MahlerOddToOddAction
from number_compiler.sequences.antihydra.mahler_odd_source_transfer import (
    select_source_certified_odd_macro,
    summarize_mahler_odd_event,
)
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MAX_MAHLER_SOURCE_EXTENT,
)


@dataclass(frozen=True, slots=True)
class MahlerOddProgramFragment:
    source: int
    destination: int
    motif: tuple[int, ...]
    repetitions: int
    source_modulus: int
    source_residue: int
    index_before: int
    clock_before: int
    balance_before: int
    index_after: int
    clock_after: int
    balance_after: int
    ledger_prefix_minimum: int
    fractional_guard_empty: bool
    carry_harmonics: dict[str, object] | None
    # Keep source-authenticated coefficients with their fragment so later
    # queries do not recompose the same motif and powered action.
    motif_action: MahlerOddToOddAction | None = None
    powered_action: MahlerOddToOddAction | None = None


@dataclass(frozen=True, slots=True)
class MahlerOddSourceProgram:
    source: int
    index: int
    clock: int
    balance: int
    fragments: tuple[MahlerOddProgramFragment, ...]
    endpoint: int
    ending_index: int
    ending_clock: int
    ending_balance: int
    stop_reason: str
    source_certified: bool
    fractional_safety_claim: bool = False
    physical_scheduler_replaced: bool = False

    @property
    def emitted_events(self) -> int:
        return self.ending_index - self.index

    @property
    def avoided_scalar_event_issues(self) -> int:
        return self.emitted_events - len(self.fragments)

    @staticmethod
    def _fragment_motif_action(
        fragment: MahlerOddProgramFragment,
    ) -> MahlerOddToOddAction:
        motif = fragment.motif_action
        if motif is None:
            motif = MahlerOddToOddAction.identity()
            for exponent in fragment.motif:
                motif = motif.then(MahlerOddToOddAction.run(exponent))
        if (
            type(motif) is not MahlerOddToOddAction
            or motif.odd_events != len(fragment.motif)
            or motif.extent != sum(fragment.motif)
        ):
            raise ValueError("stored odd motif action does not match its source word")
        return motif

    @classmethod
    def _source_after_events(
        cls, fragment: MahlerOddProgramFragment, event_count: int
    ) -> int:
        copies, partial = divmod(event_count, len(fragment.motif))
        if not 0 <= copies <= fragment.repetitions:
            raise ValueError("event request exceeds the issued Mahler fragment")
        motif = cls._fragment_motif_action(fragment)
        current = motif.power(copies).advance(fragment.source, 0)[0]
        if partial:
            prefix = MahlerOddToOddAction.identity()
            for exponent in fragment.motif[:partial]:
                prefix = prefix.then(MahlerOddToOddAction.run(exponent))
            current = prefix.advance(current, 0)[0]
        if event_count == len(fragment.motif) * fragment.repetitions:
            powered = fragment.powered_action
            if powered is not None and (
                type(powered) is not MahlerOddToOddAction
                or not powered.integer_admits(fragment.source)
                or powered.advance(fragment.source, fragment.balance_before)
                != (fragment.destination, fragment.balance_after)
            ):
                raise ValueError(
                    "stored powered Mahler action is detached from its source"
                )
            if current != fragment.destination:
                raise ArithmeticError(
                    "powered motif endpoint changed its issued source"
                )
        return current

    @staticmethod
    def _source_during_odd_event(source: int, exponent: int, elapsed: int) -> int:
        if not 1 <= elapsed <= exponent:
            raise ValueError("intra-event tick must lie within its odd run")
        numerator: int = 3**elapsed * source + 3 ** (elapsed - 1)
        endpoint: int
        remainder: int
        endpoint, remainder = divmod(numerator, 1 << elapsed)
        if remainder:
            raise ArithmeticError("issued odd-run source is not divisible at this tick")
        return endpoint

    def source_at_tick(self, tick: int) -> int:
        """Return an exact source only within this compiled finite program."""
        if type(tick) is not int or not self.clock <= tick <= self.ending_clock:
            raise ValueError("tick exceeds the authenticated Mahler source program")
        if tick == self.clock:
            return self.source
        for fragment in self.fragments:
            if not fragment.clock_before < tick <= fragment.clock_after:
                continue
            if (
                fragment.clock_after - fragment.clock_before
                != sum(fragment.motif) * fragment.repetitions
            ):
                raise ValueError("Mahler fragment clock does not match its issued word")
            elapsed = tick - fragment.clock_before
            motif_extent = sum(fragment.motif)
            copies, within_motif = divmod(elapsed, motif_extent)
            if copies > fragment.repetitions:
                raise ValueError("tick exceeds the fragment's certified motif copies")
            current = self._source_after_events(fragment, copies * len(fragment.motif))
            if within_motif == 0:
                return current
            for exponent in fragment.motif:
                if within_motif <= exponent:
                    return self._source_during_odd_event(
                        current, exponent, within_motif
                    )
                current = MahlerOddToOddAction.run(exponent).advance(current, 0)[0]
                within_motif -= exponent
            raise ArithmeticError("Mahler fragment has a missing physical tick")
        if tick == self.ending_clock:
            return self.endpoint
        raise ArithmeticError("Mahler source program has a missing temporal fragment")

    def center_transfer_at_tick(
        self,
        tick: int,
        *,
        steps: int = 4,
        initial_ledger: int | None = None,
        include_rows: bool = False,
        trace: bool = False,
    ) -> dict[str, object]:
        """Demand a finite center transfer within this program's recorded horizon."""
        if type(include_rows) is not bool:
            raise TypeError("center matrix row demand must be Boolean")
        if type(trace) is not bool:
            raise TypeError("center matrix trace demand must be Boolean")
        from number_compiler.sequences.antihydra.mahler_center_depth_matrix import (
            MahlerCertifiedCenterDepthTransfer,
        )

        certificate = MahlerCertifiedCenterDepthTransfer.from_program(
            self, tick, steps, initial_ledger=initial_ledger
        )
        return {
            **certificate.packet(include_rows=include_rows, trace=trace),
            "origin_tick": tick,
        }


def compile_mahler_odd_program(
    source: int,
    *,
    index: int = 0,
    clock: int = 0,
    balance: int = 0,
    max_events: int = 64,
    max_extent: int = MAX_MAHLER_SOURCE_EXTENT,
    max_motif_events: int = 4,
    include_carry_harmonics: bool = False,
    source_gate_bits: int = 96,
) -> MahlerOddSourceProgram:
    """Compile a bounded ledger-safe source program, with guarded macro squaring.

    Input `(source,index,clock,balance)` must be a witnessed pointed odd
    seam. Stops *before* any ledger-invalid event, and never infers a
    fractional Mahler witness or an Antihydra Turing-machine transition.
    """
    if type(source) is not int or source <= 0 or source % 2 != 1:
        raise ValueError("Mahler program must begin at a positive odd pointed source")
    if any(
        type(value) is not int or value < 0
        for value in (
            index,
            clock,
            max_events,
            max_extent,
            max_motif_events,
            source_gate_bits,
        )
    ):
        raise ValueError(
            "Mahler program clocks and budgets must be nonnegative integers"
        )
    if source.bit_length() > 65_536:
        raise BlockContextBudgetExceeded("Mahler program source exceeds bit budget")
    if type(balance) is not int or balance != 3 * index - clock:
        raise ValueError("Mahler pointed ledger/clock provenance is inconsistent")
    if (
        not 1 <= max_motif_events <= 8
        or not 1 <= max_extent <= MAX_MAHLER_SOURCE_EXTENT
        or source_gate_bits > 65_536
    ):
        raise ValueError("Mahler macro discovery requires positive finite budgets")
    if type(include_carry_harmonics) is not bool:
        raise TypeError("Mahler carry harmonic request must be Boolean")
    start_source, start_index, start_clock, start_balance = (
        source,
        index,
        clock,
        balance,
    )
    fragments: list[MahlerOddProgramFragment] = []
    steps_consumed = 0
    stop_reason = "event_horizon_exhausted"
    while index - start_index < max_events:
        remaining_events = max_events - (index - start_index)
        remaining_steps = max_extent - steps_consumed
        if remaining_steps < 1:
            stop_reason = "normalized_step_budget_exhausted"
            break
        selection = None
        ring = None
        copies = 1
        if remaining_events >= 2 and source.bit_length() >= source_gate_bits:
            # Cheap exact source lookahead selects a motif first.  The full
            # action is constructed only after two copies have been seen.
            try:
                selection = select_source_certified_odd_macro(
                    source,
                    remaining_steps=remaining_steps,
                    max_events=min(8, 2 * max_motif_events, remaining_events),
                    max_extent=min(remaining_steps, MAX_MAHLER_SOURCE_EXTENT),
                )
            except BlockContextBudgetExceeded:
                selection = None
            if selection is not None:
                ring = selection.ring
                copies = min(
                    selection.repetitions,
                    remaining_events // len(ring.exponents),
                    remaining_steps // ring.extent,
                )
                if copies < 2:
                    selection = None
                    ring = None
                    copies = 1
        if ring is not None:
            # Compute the repeated ledger prefix before constructing its
            # powered affine action. A complete motif may be unsafe even
            # when its first event is safe; in that case the exact scalar
            # issuer below preserves that proper prefix.
            safe_copies = ring.ledger_safe_copies(balance, copies)
            if safe_copies == 0:
                ring = None
                copies = 1
            else:
                copies = safe_copies
        motif: tuple[int, ...]
        if ring is None:
            try:
                event = summarize_mahler_odd_event(
                    source,
                    max_extent=min(remaining_steps, MAX_MAHLER_SOURCE_EXTENT),
                )
            except BlockContextBudgetExceeded:
                stop_reason = "normalized_step_budget_exhausted"
                break
            exponent = event.exponent
            action = MahlerOddToOddAction.run(exponent)
            motif = (exponent,)
            next_source, next_balance = action.advance(source, balance)
            if next_source != event.endpoint:
                raise ArithmeticError("odd event summary changed its source endpoint")
            if balance + action.minimum < 0:
                stop_reason = "ledger_barrier_before_next_event"
                break
            radix_packet = None
        else:
            action = ring.power(copies)
            motif = ring.exponents
            next_source, next_balance = action.advance(source, balance)
            if next_source != ring.endpoint(copies):
                raise ArithmeticError(
                    "source-bound powered macro disagrees with centered defect"
                )
            radix_packet = (
                ring.observation(
                    repetitions=copies,
                    clock=clock,
                    places=2,
                    walsh64=copies * len(motif) >= 64,
                )
                if include_carry_harmonics
                else None
            )
        if not action.integer_admits(source) or balance + action.minimum < 0:
            raise ArithmeticError(
                "compiled Mahler macro lost a required source or prefix guard"
            )
        old_source, old_index, old_clock, old_balance = source, index, clock, balance
        index += len(motif) * copies
        clock += action.extent
        steps_consumed += action.extent
        balance = next_balance
        if balance != 3 * index - clock:
            raise ArithmeticError(
                "compiled odd-event ledger detached from normalized return clock"
            )
        source = next_source
        fragments.append(
            MahlerOddProgramFragment(
                old_source,
                source,
                motif,
                copies,
                action.source_modulus,
                action.source_residue,
                old_index,
                old_clock,
                old_balance,
                index,
                clock,
                balance,
                action.minimum,
                action.joint.guard.empty,
                radix_packet,
                ring.action if ring is not None else action,
                action,
            )
        )
    return MahlerOddSourceProgram(
        start_source,
        start_index,
        start_clock,
        start_balance,
        tuple(fragments),
        source,
        index,
        clock,
        balance,
        stop_reason,
        True,
    )


__all__ = (
    "MahlerOddProgramFragment",
    "MahlerOddSourceProgram",
    "compile_mahler_odd_program",
)
