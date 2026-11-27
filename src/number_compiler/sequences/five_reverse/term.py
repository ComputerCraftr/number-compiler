"""Budgeted exact owner for ``x[n+1] = 5 * reverse10(x[n])``.

The owner deliberately separates the exact bounded recurrence from the
source-certified four-stage carry macro.  A finite source window is exact but
does not grant an unbounded temporal cycle.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator
from contextlib import ExitStack
from dataclasses import dataclass
from threading import RLock
from typing import Self

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.ordered_output import (
    OrderedBandChannel,
    OrderedBandOutput,
    OrderedPhaseCoordinate,
    OrderedSourceCoverage,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.fields.ordered_band import (
    ordered_band_scratch_cost,
)
from number_compiler.arithmetic.fields.ordered_matrix import (
    Matrix2,
    OrderedCovector,
    ordered_decimal_continuant,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageID,
    SourceImageView,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.ledger_records import ResourceScope
from number_compiler.resources.lifecycle import cleanup_all, cleanup_on_error
from number_compiler.resources.metric_keys import five_reverse as _keys
from number_compiler.resources.owned_memo import LedgerReservation

from .ports import (
    MAX_FIVE_REVERSE_MATRIX_STEPS,
    MAX_FIVE_REVERSE_TRACE_STEPS,
    FiveBorderPort,
    FiveCarryPort,
    FivePortTransition,
    FiveSourceTransfer,
    source_residue45,
)
from .source_adapter import (
    FiveReverseAction,
    FiveReverseSource,
    FiveReverseSourceAdapter,
)
from .source_window import (
    SEED196_SOURCE_WINDOW,
    FiveFiniteSourceWindow,
    validates_seed196_source_window,
)

_GUARDED_WINDOW_ENTRIES = 1
_GUARDED_WINDOW_NODES = 8
# The bounded bitplane candidate is held until its physical consumer proof and
# measured dispatch gate pass. Benchmark fixtures can select it explicitly.
_BITPLANE_MIN_STEPS: int | None = None


@dataclass(frozen=True, slots=True)
class _GuardedWindow:
    certificate: FiveFiniteSourceWindow
    source: FiveReverseSource
    seed: int
    generation: int
    stage: int
    head3: int
    tail3: int
    remaining_inlets: tuple[int, ...]
    incoming_growth: int | None = None


class FiveReverseTerm:
    """Source-bound, resource-limited exact term for the five-reversal map."""

    __slots__ = (
        "__weakref__",
        "_binding",
        "_closed",
        "_cleanup_complete",
        "_dispose_resources_complete",
        "_adapter",
        "_endpoint",
        "_guarded_window",
        "_guarded_window_reserved",
        "_image",
        "_issuer",
        "_lock",
        "_scheduler",
        "_scratch_owner",
        "_source",
        "generation",
        "max_state_bits",
        "max_steps",
        "resource_ledger",
        "seed",
    )

    def __init__(
        self,
        seed: int,
        generation: int,
        *,
        max_steps: int = 4096,
        max_state_bits: int = 4096,
        max_context_nodes: int | None = None,
        max_cache_entries: int | None = None,
    ) -> None:
        self.seed = require_integer(seed, "five-reversal seed", 0)
        self.generation = require_integer(generation, "five-reversal generation", 0)
        self.max_steps = require_integer(max_steps, "maximum steps", 0)
        self.max_state_bits = require_integer(max_state_bits, "maximum state bits", 1)
        if self.generation > self.max_steps:
            raise BlockContextBudgetExceeded(
                "five-reversal generation exceeds its step budget"
            )
        if self.seed.bit_length() > self.max_state_bits:
            raise BlockContextBudgetExceeded(
                "five-reversal source exceeds its admitted state-bit budget"
            )
        self.resource_ledger = ResourceLedger(max_context_nodes, max_cache_entries)
        self._scratch_owner = self.resource_ledger.register(
            "five-reversal-scratch", "temporary_work", ResourceScope.INDEX_OWNED
        )
        self._binding = (
            self.seed,
            self.generation,
            self.max_steps,
            self.max_state_bits,
        )
        self._endpoint: int | None = None
        self._guarded_window: _GuardedWindow | None = None
        self._guarded_window_reserved = False
        self._closed = False
        self._cleanup_complete = False
        self._dispose_resources_complete = False
        self._lock = RLock()
        with ExitStack() as rollback:
            rollback.enter_context(
                cleanup_on_error(
                    lambda: self.resource_ledger.mark_disposed(self._scratch_owner)
                )
            )
            self._issuer = ArenaToken("five-reversal-source")
            self._source = FiveReverseSource(self._issuer, self.seed)
            self._adapter = FiveReverseSourceAdapter(
                self, self.resource_ledger, self._source, self._issuer
            )
            scheduler = TileScheduler.source_only(self.resource_ledger)
            self._scheduler = scheduler
            rollback.enter_context(cleanup_on_error(scheduler.dispose_source_images))
            scheduler.register_source_image_adapter(self._adapter)
            self._image: SourceImageID | None = None
            self.resource_ledger.register_execution_root(self)

    @property
    def is_usable(self) -> bool:
        return not self._closed

    @property
    def maximum_width(self) -> int:
        self.check_open()
        return self._decimal_width(self.seed) + self.generation

    @property
    def estimated_bit_length(self) -> int:
        return max(1, 4 * self.maximum_width + 3)

    def check_open(self) -> None:
        if self._closed:
            raise ValueError("disposed five-reversal term")
        current = (self.seed, self.generation, self.max_steps, self.max_state_bits)
        if (
            type(self._binding) is not tuple
            or len(self._binding) != 4
            or any(type(value) is not int for value in self._binding)
            or any(type(value) is not int for value in current)
            or self._binding != current
        ):
            raise ValueError("five-reversal source/action binding changed")

    @staticmethod
    def _decimal_width(value: int) -> int:
        if value == 0:
            return 1
        width = 0
        while value:
            value //= 10
            width += 1
        return width

    def _next(self, value: int) -> int:
        self.resource_ledger.bump(_keys.FIVE_REVERSE_EXACT_STEPS)
        width_bound = max(1, (value.bit_length() * 30103 + 99999) // 100000)
        if (
            self.resource_ledger.max_nodes is not None
            or self.resource_ledger.max_cache_entries is not None
        ):
            # A loose decimal-width bound could reject an allocation that
            # fits an explicitly limited ledger under the original contract.
            width_bound = self._decimal_width(value)
        scratch = 2 * width_bound + 2
        try:
            # Account for the decimal buffers and both integer accumulators
            # before attempting conversion or the exact digit fallback.
            with self.resource_ledger.reservation(
                self._scratch_owner, entries=scratch, nodes=scratch
            ):
                try:
                    decimal = str(value)
                    reversed_value = int(decimal[::-1])
                except ValueError:
                    # Python can impose a decimal-conversion limit. Keep the
                    # exact arithmetic fallback without changing that limit.
                    width = self._decimal_width(value)
                    digits = digits_lsd(value, 10)
                    reversed_value = 0
                    for digit in digits:
                        reversed_value = reversed_value * 10 + digit
                else:
                    width = len(decimal)
                following = 5 * reversed_value
                if following.bit_length() > self.max_state_bits:
                    raise BlockContextBudgetExceeded(
                        "five-reversal next state exceeds its admitted bit budget"
                    )
                self.resource_ledger.bump(_keys.FIVE_REVERSE_DIGIT_READS, width)
                return following
        except BaseException as error:
            try:
                self.resource_ledger.bump(_keys.FIVE_REVERSE_FAILED_STEPS)
            except BaseException as accounting_error:
                raise accounting_error from error
            raise

    def step_value(self, value: int) -> int:
        """Apply one exact recurrence step for the registered image adapter."""
        self.check_open()
        value = require_integer(value, "five-reversal input", 0)
        if value.bit_length() > self.max_state_bits:
            raise BlockContextBudgetExceeded(
                "five-reversal input exceeds its admitted state-bit budget"
            )
        return self._next(value)

    def packed_value(self, value: int, steps: int) -> int:
        """Evaluate a bounded value with the packed recurrence candidate."""
        from .packed_two_step import PackedFiveWork, execute_packed_five

        self.check_open()
        value = require_integer(value, "five-reversal input", 0)
        if value.bit_length() > self.max_state_bits:
            raise BlockContextBudgetExceeded(
                "five-reversal input exceeds its admitted state-bit budget"
            )
        steps = require_integer(steps, "packed physical steps", 0)
        if steps > self.max_steps:
            raise BlockContextBudgetExceeded("packed action exceeds its step budget")
        work = PackedFiveWork()
        execute = execute_packed_five
        if (
            _BITPLANE_MIN_STEPS is not None
            and steps >= _BITPLANE_MIN_STEPS
            and value != 0
            and self.resource_ledger.max_nodes is None
            and self.resource_ledger.max_cache_entries is None
        ):
            from .bitplane_two_step import execute_bitplane_five

            execute = execute_bitplane_five
        held = 0
        try:
            with LedgerReservation(
                self.resource_ledger, self._scratch_owner
            ) as reserve:

                def reserve_capacity(capacity: int) -> None:
                    nonlocal held
                    required = 6 * (capacity + 4)
                    if required > held:
                        amount = required - held
                        reserve.reserve(entries=amount, nodes=amount)
                        held = required

                try:
                    return execute(
                        value,
                        steps,
                        self.max_state_bits,
                        work,
                        reserve_capacity=reserve_capacity,
                    )
                finally:
                    accounting: tuple[Callable[[], None], ...] = (
                        lambda: self.resource_ledger.bump(
                            _keys.FIVE_REVERSE_EXACT_STEPS, work.attempted
                        ),
                        lambda: self.resource_ledger.bump(
                            _keys.FIVE_REVERSE_PACKED_LOGICAL_DIGIT_READS,
                            work.digit_reads,
                        ),
                        lambda: self.resource_ledger.bump(
                            _keys.FIVE_REVERSE_PACKED_EXECUTED_PAIRS,
                            work.executed_pairs,
                        ),
                    )
                    if work.bitplane_pairs:
                        accounting += (
                            lambda: self.resource_ledger.bump(
                                _keys.FIVE_REVERSE_BITPLANE_PAIRS, work.bitplane_pairs
                            ),
                        )
                    cleanup_all(accounting)
        except BaseException as error:
            try:
                self.resource_ledger.bump(_keys.FIVE_REVERSE_FAILED_STEPS)
            except BaseException as accounting_error:
                raise accounting_error from error
            raise

    def padded_source_value(self, steps: int) -> int:
        """Compile an exact padded candidate from this term's bound source."""
        from number_compiler.arithmetic.carry.reflected_h_power import padded_h_endpoint

        self.check_open()
        self._adapter.validate_source(self._source)
        steps = require_integer(steps, "padded physical steps", 0)
        if steps > self.max_steps:
            raise BlockContextBudgetExceeded("padded action exceeds its step budget")
        return padded_h_endpoint(
            self.seed,
            steps,
            5,
            ledger=self.resource_ledger,
            scratch_owner=self._scratch_owner,
            max_state_bits=self.max_state_bits,
        )

    def publish_padded_source(self, arena: LedgerSLPArena, steps: int) -> int:
        """Publish this source's padded endpoint into a same-ledger arena."""
        from number_compiler.arithmetic.carry.reflected_h_power import padded_h_publish

        self.check_open()
        self._adapter.validate_source(self._source)
        steps = require_integer(steps, "padded physical steps", 0)
        if steps > self.max_steps:
            raise BlockContextBudgetExceeded("padded action exceeds its step budget")
        if (
            type(arena) is not LedgerSLPArena
            or arena.ledger is not self.resource_ledger
        ):
            raise ValueError("padded output arena belongs to another source ledger")
        arena.empty()
        return padded_h_publish(
            self.seed,
            steps,
            5,
            arena=arena,
            scratch_owner=self._scratch_owner,
            max_state_bits=self.max_state_bits,
        )

    def source_port(self, value: int) -> FiveBorderPort:
        """Return the exact bounded source port used by this term's adapter."""
        self.check_open()
        value = require_integer(value, "five-reversal port input", 0)
        if value.bit_length() > self.max_state_bits:
            raise BlockContextBudgetExceeded(
                "five-reversal port input exceeds its admitted state-bit budget"
            )
        return self._port(value)

    def require_issued_view(self, view: SourceImageView) -> None:
        """Reject forged or stale source-image views through the issuing scheduler."""
        self.check_open()
        if (
            type(view) is not SourceImageView
            or type(view.identity) is not SourceImageID
        ):
            raise TypeError("five-reversal view needs its exact scheduler identity")
        issued = self._scheduler.source_image_view(self._adapter, view.identity)
        if issued != view:
            raise ValueError("five-reversal source-image view is stale or forged")

    def issued_endpoint_view(self) -> SourceImageView:
        """Return the checked read-only view of this term's exact endpoint."""
        self._endpoint_value()
        with self._lock:
            self.check_open()
            image = self._image
            if image is None:
                raise ValueError("five-reversal endpoint image was not published")
            view = self._scheduler.source_image_view(self._adapter, image)
            self.require_issued_view(view)
            return view

    def _endpoint_value(self) -> int:
        self.check_open()
        with self._lock:
            cached = self._endpoint
            if cached is not None:
                return cached
            image = self._scheduler.source_image(
                self._adapter,
                self._source,
                FiveReverseAction(self.generation),
            )
            view = self._scheduler.source_image_view(self._adapter, image)
            if type(view) is not SourceImageView or type(view.payload) is not int:
                raise TypeError("five-reversal scheduler published a foreign endpoint")
            if (
                view.binding.source is not self._source
                or view.binding.action != FiveReverseAction(self.generation)
                or view.binding.semantic_version != self._adapter.semantic_version
            ):
                raise ValueError(
                    "five-reversal endpoint has another source/action binding"
                )
            value = view.payload
            self.resource_ledger.bump(_keys.FIVE_REVERSE_ENDPOINT_PUBLICATIONS)
            self._endpoint = value
            self._image = image
            return value

    def materialize(self, *, max_bits: int) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        value = self._endpoint_value()
        if value.bit_length() > max_bits:
            raise ValueError((value.bit_length(), max_bits))
        return value

    def _port(self, value: int) -> FiveBorderPort:
        width = self._decimal_width(value)
        digits = min(3, width)
        scratch = max(1, 2 * width + 2)
        with self.resource_ledger.reservation(
            self._scratch_owner, entries=scratch, nodes=scratch
        ):
            high_value = value // (10 ** (width - digits))
            low_value = value % (10**digits)
            high = tuple(reversed(digits_lsd(high_value, 10)))
            low = digits_lsd(low_value, 10)
        return FiveBorderPort(width, high, low, value % 45)

    @staticmethod
    def _reverse_fixed_three(value: int) -> int:
        return (value % 10) * 100 + (value // 10 % 10) * 10 + value // 100

    @classmethod
    def _advance_guarded_border(
        cls, head3: int, tail3: int, inlet: int
    ) -> tuple[int, int, int]:
        if not 100 <= head3 <= 999 or not 0 <= tail3 <= 999 or not 0 <= inlet <= 4:
            raise ValueError("guarded five-reversal border is outside its exact domain")
        raw = 5 * cls._reverse_fixed_three(tail3) + inlet
        if raw < 100:
            raise ValueError("five-reversal guarded border exits through width loss")
        growth = int(raw >= 1000)
        next_head = raw // 10 if growth else raw
        next_tail = 5 * cls._reverse_fixed_three(head3) % 1000
        return next_head, next_tail, growth

    def _source_guarded_window(
        self, *, through_generation: int
    ) -> _GuardedWindow | None:
        """Select a finite source window only within its bound and horizon."""
        with self._lock:
            self.check_open()
            certificate = SEED196_SOURCE_WINDOW
            if not validates_seed196_source_window(certificate):
                raise ValueError(
                    "five-reversal source window failed its authority seal"
                )
            if not certificate.supports(self.seed, self.generation, through_generation):
                self._release_guarded_window()
                return None
            if self.max_state_bits < certificate.state_bits_bound_through(
                through_generation
            ):
                self._release_guarded_window()
                return None
            found = self._guarded_window
            if found is not None:
                self._validate_guarded_window(found)
                if (
                    found.certificate is not certificate
                    or found.generation != self.generation
                    or found.seed != self.seed
                    or found.source is not self._source
                ):
                    raise ValueError("five-reversal guarded window binding changed")
                return found
            if self._guarded_window_reserved:
                # A prior construction may have failed while releasing its
                # reservation. Retry that cleanup before acquiring another one.
                self._release_guarded_window()
            try:
                self.resource_ledger.reserve(
                    self._scratch_owner,
                    entries=_GUARDED_WINDOW_ENTRIES,
                    nodes=_GUARDED_WINDOW_NODES,
                )
            except BlockContextBudgetExceeded:
                return None
            self._guarded_window_reserved = True
            try:
                border = certificate.initial_border
                inlets = certificate.inlets
                stage = self.generation - certificate.start_generation
                incoming_growth: int | None = None
                for prior_stage, inlet in enumerate(inlets[:stage]):
                    next_head, next_tail, border_growth = self._advance_guarded_border(
                        *border, inlet
                    )
                    if (next_head, next_tail) != certificate.borders[prior_stage + 1]:
                        raise ValueError(
                            "five-reversal border diverges from its finite certificate"
                        )
                    incoming_growth = border_growth
                    border = (next_head, next_tail)
                window = _GuardedWindow(
                    certificate,
                    self._source,
                    self.seed,
                    self.generation,
                    stage,
                    border[0],
                    border[1],
                    inlets[stage:],
                    incoming_growth,
                )
                self._validate_guarded_window(window)
                self._guarded_window = window
                return window
            except BaseException as error:
                self._guarded_window = None
                try:
                    self.resource_ledger.release(
                        self._scratch_owner,
                        entries=_GUARDED_WINDOW_ENTRIES,
                        nodes=_GUARDED_WINDOW_NODES,
                    )
                except BaseException as release_error:
                    raise release_error from error
                self._guarded_window_reserved = False
                raise

    @staticmethod
    def _packed_prefix(head3: int, places: int) -> int:
        digits = tuple(reversed(digits_lsd(head3, 10)))
        value = 0
        power = 1
        for digit in digits[:places]:
            value += (digit // 2) * power
            power *= 5
        return value

    def _validate_guarded_window(self, window: _GuardedWindow) -> None:
        self.check_open()
        if type(window) is not _GuardedWindow:
            raise TypeError("five-reversal guarded cursor has the wrong type")
        if (
            any(
                type(value) is not int
                for value in (
                    window.seed,
                    window.generation,
                    window.stage,
                    window.head3,
                    window.tail3,
                )
            )
            or (
                window.incoming_growth is not None
                and type(window.incoming_growth) is not int
            )
            or type(window.remaining_inlets) is not tuple
            or any(type(inlet) is not int for inlet in window.remaining_inlets)
        ):
            raise ValueError("five-reversal guarded cursor has malformed fields")
        certificate = window.certificate
        if not validates_seed196_source_window(certificate):
            raise ValueError("five-reversal guarded cursor has an invalid certificate")
        if (
            not 0
            <= window.stage
            <= (certificate.terminal_generation - certificate.start_generation)
        ):
            raise ValueError("five-reversal guarded cursor is outside its stage range")
        remaining_count = (
            certificate.terminal_generation
            - certificate.start_generation
            - window.stage
        )
        expected_growth: int | None = None
        if window.stage > 0:
            previous_head, previous_tail = certificate.borders[window.stage - 1]
            next_head, next_tail, expected_growth = self._advance_guarded_border(
                previous_head,
                previous_tail,
                certificate.inlets[window.stage - 1],
            )
            if (next_head, next_tail) != certificate.borders[window.stage]:
                raise ValueError("five-reversal certificate predecessor is invalid")
        if (
            window.certificate is not SEED196_SOURCE_WINDOW
            or window.source is not self._source
            or window.seed != self.seed
            or window.generation != certificate.start_generation + window.stage
            or len(window.remaining_inlets) != remaining_count
            or (window.head3, window.tail3) != certificate.borders[window.stage]
            or window.remaining_inlets != certificate.inlets[window.stage :]
            or window.incoming_growth != expected_growth
        ):
            raise ValueError("five-reversal guarded cursor is stale or foreign")

    def _guarded_port(self, window: _GuardedWindow) -> FiveCarryPort:
        self._validate_guarded_window(window)
        return FiveCarryPort(
            window.stage,
            window.head3,
            window.tail3,
            self._packed_prefix(window.head3, 2),
            self._packed_prefix(window.head3, 3),
            window.head3 % 2,
            window.tail3 % 2,
            window.incoming_growth,
        )

    def _advance_guarded_window(
        self, window: _GuardedWindow
    ) -> tuple[_GuardedWindow, int]:
        self._validate_guarded_window(window)
        if not window.remaining_inlets:
            raise ValueError("five-reversal guarded source window is exhausted")
        inlet = window.remaining_inlets[0]
        next_head, next_tail, border_growth = self._advance_guarded_border(
            window.head3, window.tail3, inlet
        )
        if (next_head, next_tail) != window.certificate.borders[window.stage + 1]:
            raise ValueError(
                "five-reversal transition diverges from its finite certificate"
            )
        next_window = _GuardedWindow(
            window.certificate,
            window.source,
            window.seed,
            window.generation + 1,
            window.stage + 1,
            next_head,
            next_tail,
            window.remaining_inlets[1:],
            border_growth,
        )
        return next_window, border_growth

    def source_transfer(self, steps: int, *, trace: bool = False) -> FiveSourceTransfer:
        """Publish an exact finite port relation from this term's endpoint."""
        steps = require_integer(
            steps, "physical transfer ticks", 0, MAX_FIVE_REVERSE_MATRIX_STEPS
        )
        if self.generation + steps > self.max_steps:
            raise BlockContextBudgetExceeded(
                "five-reversal transfer exceeds the remaining step budget"
            )
        if type(trace) is not bool:
            raise TypeError("source-transfer trace demand must be Boolean")
        if trace and steps > MAX_FIVE_REVERSE_TRACE_STEPS:
            raise ValueError("five-reversal trace exceeds 128 physical ticks")
        # A terminal-only demand retains two ports, not one source row per
        # tick. Reserve occurrence-sized history only for an explicit trace.
        entries = 1 + (steps if trace else 0)
        nodes = 4 + (5 * steps if trace else 0)
        with self._lock:
            self.check_open()
            with self.resource_ledger.reservation(
                self._scratch_owner, entries=entries, nodes=nodes
            ):
                return self._source_transfer_reserved(steps, trace)

    def _source_transfer_reserved(self, steps: int, trace: bool) -> FiveSourceTransfer:
        guarded = self._source_guarded_window(
            through_generation=self.generation + steps
        )
        transitions: list[FivePortTransition] = []
        if guarded is not None and steps <= len(guarded.remaining_inlets):
            initial: FiveBorderPort | FiveCarryPort = self._guarded_port(guarded)
            if not trace:
                # Project the sealed finite source action at its target stage.
                # Revalidate only the incoming boundary seam; the immutable
                # certificate already authenticates every intermediate row.
                stage = guarded.stage + steps
                if stage == guarded.stage:
                    terminal_cursor = guarded
                else:
                    certificate = guarded.certificate
                    prior_head, prior_tail = certificate.borders[stage - 1]
                    head, tail, growth = self._advance_guarded_border(
                        prior_head, prior_tail, certificate.inlets[stage - 1]
                    )
                    if (head, tail) != certificate.borders[stage]:
                        raise ValueError("guarded terminal border seam is invalid")
                    terminal_cursor = _GuardedWindow(
                        certificate,
                        guarded.source,
                        guarded.seed,
                        guarded.generation + steps,
                        stage,
                        head,
                        tail,
                        certificate.inlets[stage:],
                        growth,
                    )
                terminal: FiveBorderPort | FiveCarryPort = self._guarded_port(
                    terminal_cursor
                )
            else:
                cursor = guarded
                for offset in range(steps):
                    source_port = self._guarded_port(cursor)
                    cursor, _growth = self._advance_guarded_window(cursor)
                    transitions.append(
                        FivePortTransition(
                            self.generation + offset,
                            source_port,
                            self._guarded_port(cursor),
                        )
                    )
                terminal = self._guarded_port(cursor)
            self.resource_ledger.bump(_keys.FIVE_REVERSE_SOURCE_TRANSFER_TICKS, steps)
            return FiveSourceTransfer(
                self.generation,
                steps,
                source_residue45(self.seed, self.generation),
                source_residue45(self.seed, self.generation + steps),
                initial,
                terminal,
                tuple(transitions),
                source_coverage=OrderedSourceCoverage.FIVE_GUARDED_WINDOW,
            )
        value = self._endpoint_value()
        initial = self._port(value)
        if not trace:
            # One source-bound endpoint action is sufficient for a terminal
            # port. Replaying a second independent chronological observer
            # discarded the already-admitted packed/H production executor.
            # The adapter still checks every intermediate state-bit bound.
            terminal_value = self._adapter.apply_steps(value, steps)
            terminal = initial if steps == 0 else self._port(terminal_value)
        else:
            start_generation = self.generation
            for offset in range(steps):
                previous = value
                value = self._next(previous)
                transitions.append(
                    FivePortTransition(
                        start_generation + offset,
                        self._port(previous),
                        self._port(value),
                    )
                )
            terminal = initial if steps == 0 else self._port(value)
        self.resource_ledger.bump(_keys.FIVE_REVERSE_SOURCE_TRANSFER_TICKS, steps)
        return FiveSourceTransfer(
            self.generation,
            steps,
            source_residue45(self.seed, self.generation),
            source_residue45(self.seed, self.generation + steps),
            initial,
            terminal,
            tuple(transitions),
        )

    def _ordered_output(
        self,
        steps: int,
        digit_width: int,
        modulus: int,
        coefficients: tuple[int, ...] | None,
        *,
        trace: bool = False,
    ) -> OrderedBandOutput:
        steps = require_integer(
            steps, "ordered physical ticks", 1, MAX_FIVE_REVERSE_MATRIX_STEPS
        )
        digit_width = require_integer(
            digit_width, "five-reversal digit-band width", 1, 90
        )
        modulus = require_integer(modulus, "ordered matrix modulus", 2)
        if self.generation + steps > self.max_steps:
            raise BlockContextBudgetExceeded(
                "five-reversal ordered action exceeds the remaining step budget"
            )
        entries, nodes = ordered_band_scratch_cost(
            steps,
            digit_width,
            modulus,
            coefficients,
            trace=trace,
            matrix_channels=1,
        )
        with self._lock:
            self.check_open()
            with self.resource_ledger.reservation(
                self._scratch_owner, entries=entries, nodes=nodes
            ):
                return self._ordered_output_reserved(
                    steps,
                    digit_width,
                    modulus,
                    coefficients,
                    trace=trace,
                )

    def _ordered_output_reserved(
        self,
        steps: int,
        digit_width: int,
        modulus: int,
        coefficients: tuple[int, ...] | None,
        *,
        trace: bool,
    ) -> OrderedBandOutput:
        matrix = Matrix2.identity(modulus)
        source_letters = 0
        guarded = self._source_guarded_window(
            through_generation=self.generation + steps
        )
        use_guarded = (
            guarded is not None
            and steps <= len(guarded.remaining_inlets)
            and digit_width <= 3
        )
        current = None if use_guarded else self._endpoint_value()
        cursor = guarded if use_guarded else None
        trace_rows: list[tuple[Matrix2, ...]] = []
        for _ in range(steps):
            if cursor is not None:
                low = 5 * self._reverse_fixed_three(cursor.head3) % 1000
                following = None
                cursor, _growth = self._advance_guarded_window(cursor)
            else:
                if current is None:
                    raise AssertionError("exact five-reversal cursor is missing")
                following = self._next(current)
                low = following
            digits: list[int] = []
            for _digit in range(digit_width):
                low, digit = divmod(low, 10)
                digits.append(digit)
            # This family reads its physical word LSD first. The shared
            # continuant right product therefore consumes the reverse word.
            step_matrix = ordered_decimal_continuant(reversed(digits), modulus)
            matrix = matrix.then(step_matrix)
            source_letters += digit_width
            self.resource_ledger.bump(
                _keys.FIVE_REVERSE_ORDERED_MATRIX_PRODUCTS, digit_width + 1
            )
            if trace:
                trace_rows.append((step_matrix,))
            if following is not None:
                current = following
        covectors: tuple[OrderedCovector, ...] = ()
        if coefficients is not None:
            covectors = (OrderedCovector(coefficients, modulus).pullback(matrix),)
        channel = OrderedBandChannel.LOWER_DIGITS
        return OrderedBandOutput(
            source_index=self.generation,
            physical_ticks=steps,
            start_phase=source_residue45(self.seed, self.generation),
            terminal_phase=source_residue45(self.seed, self.generation + steps),
            channels=(channel,),
            matrices=(matrix,),
            covectors=covectors,
            source_coverage=(
                OrderedSourceCoverage.FIVE_GUARDED_WINDOW
                if use_guarded
                else OrderedSourceCoverage.EXACT_BOUNDED_WINDOW
            ),
            matrix_multiplications=source_letters + steps,
            source_letters_read=source_letters,
            trace=tuple(trace_rows),
            phase_coordinate=OrderedPhaseCoordinate.SOURCE_MOD45,
        )

    def digit_band(
        self,
        steps: int,
        width: int,
        modulus: int,
        *,
        coefficients: tuple[int, ...] | None = None,
        trace: bool = False,
    ) -> OrderedBandOutput:
        width = require_integer(width, "five-reversal digit-band width", 1, 90)
        return self._ordered_output(steps, width, modulus, coefficients, trace=trace)

    def iter_digits(self) -> Iterator[int]:
        value = self._endpoint_value()
        while True:
            self.check_open()
            value, digit = divmod(value, 10)
            yield digit
            if value == 0:
                return

    def digit(self, index: int) -> int:
        index = require_integer(index, "digit coordinate", 0)
        value = self._endpoint_value()
        for _ in range(index):
            value //= 10
            if value == 0:
                return 0
        return value % 10

    def dispose(self) -> None:
        with self._lock:
            if self._cleanup_complete:
                return
            self._closed = True
            if not self._dispose_resources_complete:
                cleanup_all(
                    (
                        self._scheduler.dispose_source_images,
                        self._release_guarded_window,
                        lambda: self.resource_ledger.mark_disposed(self._scratch_owner),
                    )
                )
                self._dispose_resources_complete = True
            self._endpoint = None
            self._image = None
            self._cleanup_complete = True

    def _release_guarded_window(self) -> None:
        if self._guarded_window_reserved:
            self.resource_ledger.release(
                self._scratch_owner,
                entries=_GUARDED_WINDOW_ENTRIES,
                nodes=_GUARDED_WINDOW_NODES,
            )
            self._guarded_window_reserved = False
        self._guarded_window = None

    def __enter__(self) -> Self:
        self.check_open()
        return self

    def __exit__(self, *_exc: object) -> None:
        self.dispose()
