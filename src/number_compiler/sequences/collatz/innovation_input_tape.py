"""Source-authenticated parity programs and global innovation port observers.

The parity program is a temporary grammar retained only while a demanded
observer is compiled.  Its finite Moore IDs describe signed output futures;
they never identify or authorize an arithmetic endpoint.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from typing import Self

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_0563,
    ENTRY_89_AT_NINE,
    ENTRY_421,
    ENTRY_4721,
    PATH_305,
    PATH_630,
)
from number_compiler.sequences.collatz.boundary_macros import (
    boundary_macro_26847_phase,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)

_UNISSUED = object()
_PROGRAM_ISSUER = object()
_D8_WORD_ISSUER = object()


@dataclass(frozen=True, slots=True)
class ParityFactor:
    """One exact Boolean motif repeated a positive number of times."""

    motif: tuple[int, ...]
    repetitions: int

    def __post_init__(self) -> None:
        if (
            type(self.motif) is not tuple
            or not self.motif
            or any(type(bit) is not int or bit not in (0, 1) for bit in self.motif)
            or type(self.repetitions) is not int
            or self.repetitions <= 0
        ):
            raise ValueError("parity factor needs a nonempty Boolean motif and power")

    @property
    def steps(self) -> int:
        return len(self.motif) * self.repetitions

    @property
    def ones(self) -> int:
        return sum(self.motif) * self.repetitions


@dataclass(frozen=True, slots=True)
class NormalizedParityProgram:
    """Compact source/endpoint-bound grammar for one normalized prefix."""

    source: int
    endpoint: int
    steps: int
    one_symbols: int
    factors: tuple[ParityFactor, ...]
    _authority: object = field(default=_UNISSUED, init=False, repr=False, compare=False)
    _seal: tuple[object, ...] = field(default=(), init=False, repr=False, compare=False)

    @property
    def producer_issued(self) -> bool:
        return self._authority is _PROGRAM_ISSUER and self._seal == (
            self.source,
            self.endpoint,
            self.steps,
            self.one_symbols,
            id(self.factors),
            tuple(
                (id(factor), factor.motif, factor.repetitions)
                for factor in self.factors
            )
            if type(self.factors) is tuple
            else None,
        )

    @property
    def description_units(self) -> int:
        return sum(
            3 + len(factor.motif) + factor.repetitions.bit_length()
            for factor in self.factors
        )


def _issue_program(builder: ParityProgramBuilder) -> NormalizedParityProgram:
    """Issue only from a builder whose exact action seams were checked."""
    if (
        type(builder) is not ParityProgramBuilder
        or builder._closed
        or builder._program is not None
        or builder._d8_frame is not None
        or builder._source_is_local
    ):
        raise ValueError("parity program issuer requires a completed exact builder")
    source = builder._start
    endpoint = builder._source
    steps = builder._steps
    one_symbols = builder._one_symbols
    factors = tuple(builder._factors)
    program = object.__new__(NormalizedParityProgram)
    for name, value in (
        ("source", source),
        ("endpoint", endpoint),
        ("steps", steps),
        ("one_symbols", one_symbols),
        ("factors", factors),
        ("_authority", _PROGRAM_ISSUER),
    ):
        object.__setattr__(program, name, value)
    if (
        type(source) is not int
        or source <= 0
        or type(endpoint) is not int
        or endpoint <= 0
        or type(steps) is not int
        or steps < 0
        or type(one_symbols) is not int
        or not 0 <= one_symbols <= steps
        or type(factors) is not tuple
        or any(type(factor) is not ParityFactor for factor in factors)
        or sum(factor.steps for factor in factors) != steps
        or sum(factor.ones for factor in factors) != one_symbols
        or (steps == 0) != (not factors)
        or (steps and factors[0].motif[0] != source & 1)
    ):
        raise ValueError("normalized parity program does not match its source action")
    object.__setattr__(
        program,
        "_seal",
        (
            source,
            endpoint,
            steps,
            one_symbols,
            id(factors),
            tuple((id(factor), factor.motif, factor.repetitions) for factor in factors),
        ),
    )
    return program


@dataclass(frozen=True, slots=True, init=False)
class _D8ParityTransition:
    """A D8 word and action issued together by the exact residue-table owner."""

    source_local: int
    endpoint_local: int
    odd_mask: int
    action: DyadicTerminalFieldAction
    source_frame: object
    advanced_frame: object
    _authority: object = field(default=_UNISSUED, init=False, repr=False, compare=False)
    _seal: tuple[object, ...] = field(default=(), init=False, repr=False, compare=False)

    def __init__(self) -> None:
        raise TypeError("D8 parity transitions are issued by the D8 table")

    @classmethod
    def _issue(
        cls,
        source_local: int,
        endpoint_local: int,
        odd_mask: int,
        action: DyadicTerminalFieldAction,
        source_frame: object,
        advanced_frame: object,
    ) -> _D8ParityTransition:
        from number_compiler.sequences.collatz.temporal_dyadic import D8CylinderFrame

        transition = object.__new__(cls)
        for name, value in (
            ("source_local", source_local),
            ("endpoint_local", endpoint_local),
            ("odd_mask", odd_mask),
            ("action", action),
            ("source_frame", source_frame),
            ("advanced_frame", advanced_frame),
            ("_authority", _D8_WORD_ISSUER),
        ):
            object.__setattr__(transition, name, value)
        if type(source_local) is not int or source_local < 0:
            raise ValueError("D8 parity transition has a negative local source")
        expected_mask = 0
        expected_endpoint = source_local
        for position in range(8):
            if expected_endpoint & 1:
                expected_mask |= 1 << position
                expected_endpoint = (3 * expected_endpoint + 1) >> 1
            else:
                expected_endpoint >>= 1
        certified_source = source_local if source_local > 0 else 256
        if (
            type(endpoint_local) is not int
            or endpoint_local < 0
            or type(odd_mask) is not int
            or not 0 <= odd_mask < 256
            or type(action) is not DyadicTerminalFieldAction
            or not action.producer_issued
            or type(source_frame) is not D8CylinderFrame
            or type(advanced_frame) is not D8CylinderFrame
        ):
            raise ValueError("D8 parity transition fields are malformed")
        local_numerator = action.gain * source_local + action.offset
        local_endpoint, local_remainder = divmod(local_numerator, 1 << 8)
        if (
            odd_mask != expected_mask
            or action.steps != 8
            or action.source_residue != source_local % 256
            or action.gain != 3 ** expected_mask.bit_count()
            or advanced_frame.source != source_frame.source
            or advanced_frame.consumed != source_frame.consumed + 8
            or advanced_frame.gain != action.gain * source_frame.gain
            or source_frame.local_word() != source_local
            or local_remainder != 0
            or local_endpoint != advanced_frame.origin
            or expected_endpoint != advanced_frame.origin
            or not action.certifies(certified_source)
            or action.endpoint(certified_source)
            != expected_endpoint + action.gain * int(source_local == 0)
            or advanced_frame.local_word() != endpoint_local
        ):
            raise ValueError("D8 parity transition differs from its exact action")
        object.__setattr__(
            transition,
            "_seal",
            (
                source_local,
                endpoint_local,
                odd_mask,
                id(action),
                id(source_frame),
                id(advanced_frame),
            ),
        )
        return transition

    @property
    def producer_issued(self) -> bool:
        from number_compiler.sequences.collatz.temporal_dyadic import (
            D8CylinderFrame,
        )

        if (
            self._authority is not _D8_WORD_ISSUER
            or type(self.source_local) is not int
            or self.source_local < 0
            or type(self.endpoint_local) is not int
            or self.endpoint_local < 0
            or type(self.odd_mask) is not int
            or type(self.action) is not DyadicTerminalFieldAction
            or type(self.source_frame) is not D8CylinderFrame
            or type(self.advanced_frame) is not D8CylinderFrame
        ):
            return False
        certified_source = self.source_local if self.source_local > 0 else 256
        local_numerator = self.action.gain * self.source_local + self.action.offset
        local_endpoint, local_remainder = divmod(local_numerator, 1 << 8)
        return (
            self.source_frame is not self.advanced_frame
            and self.source_frame.source == self.advanced_frame.source
            and self.advanced_frame.consumed == self.source_frame.consumed + 8
            and self.advanced_frame.gain == self.action.gain * self.source_frame.gain
            and local_remainder == 0
            and local_endpoint == self.advanced_frame.origin
            and self.advanced_frame.local_word() == self.endpoint_local
            and self.action.producer_issued
            and self.action.steps == 8
            and self.action.source_residue == self.source_local % 256
            and self.action.certifies(certified_source)
            and self.action.endpoint(certified_source)
            == self.advanced_frame.origin
            + self.action.gain * int(self.source_local == 0)
            and self._seal
            == (
                self.source_local,
                self.endpoint_local,
                self.odd_mask,
                id(self.action),
                id(self.source_frame),
                id(self.advanced_frame),
            )
        )


class ParityProgramBuilder:
    """Collect producer-selected compact factors with exact action seams."""

    @property
    def resource_ledger(self) -> ResourceLedger:
        """Read the resource owner, including for closed-state inspection."""
        return self._ledger

    __slots__ = (
        "_base_nodes",
        "_closed",
        "_d8_frame",
        "_entries",
        "_factor_nodes",
        "_factors",
        "_ledger",
        "_one_symbols",
        "_owner",
        "_program",
        "_program_nodes",
        "_source",
        "_source_is_local",
        "_start",
        "_steps",
    )

    def __init__(self, source: int, ledger: ResourceLedger) -> None:
        if type(source) is not int or source <= 0:
            raise ValueError("parity program needs a positive source")
        if type(ledger) is not ResourceLedger:
            raise TypeError("parity program needs its query ledger")
        self._start = source
        self._source = source
        self._source_is_local = False
        self._d8_frame: object | None = None
        self._steps = 0
        self._one_symbols = 0
        self._ledger = ledger
        self._owner = ledger.register(
            f"collatz-parity-program-{ledger.owner_count}", "temporary_workspace"
        )
        self._base_nodes = 1
        try:
            self._ledger.reserve(self._owner, nodes=self._base_nodes)
        except BaseException:
            self._ledger.mark_disposed(self._owner)
            raise
        try:
            self._factors: LedgerList[ParityFactor] = self._ledger.make_list(
                self._owner, nodes_per_entry=0, append_only=False
            )
        except BaseException:
            self._ledger.release(self._owner, nodes=self._base_nodes)
            self._ledger.mark_disposed(self._owner)
            raise
        self._entries = 0
        self._factor_nodes = 0
        self._program: NormalizedParityProgram | None = None
        self._program_nodes = 0
        self._closed = False

    @property
    def source(self) -> int:
        return self._source

    def __enter__(self) -> Self:
        if self._closed:
            raise RuntimeError("parity program builder is closed")
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()

    @staticmethod
    def _factor_cost(motif: tuple[int, ...], repetitions: int) -> int:
        return 3 + len(motif) + max(1, (repetitions.bit_length() + 63) // 64)

    def _append_admitted(
        self,
        source: int,
        endpoint: int,
        specs: tuple[tuple[tuple[int, ...], int], ...],
        *,
        odd_symbols: int,
        local_source: bool = False,
    ) -> None:
        if self._closed:
            raise RuntimeError("parity program builder is closed")
        if self._program is not None:
            raise RuntimeError("parity program builder has already published")
        if (
            type(source) is not int
            or source < 0
            or type(endpoint) is not int
            or endpoint < 0
            or type(local_source) is not bool
            or (not local_source and (source == 0 or endpoint == 0))
            or type(specs) is not tuple
            or any(
                type(spec) is not tuple
                or len(spec) != 2
                or type(spec[0]) is not tuple
                or any(type(bit) is not int or bit not in (0, 1) for bit in spec[0])
                or not spec[0]
                or type(spec[1]) is not int
                or spec[1] <= 0
                for spec in specs
            )
            or type(odd_symbols) is not int
        ):
            raise ValueError("parity fragment is malformed")
        steps = sum(len(motif) * count for motif, count in specs)
        ones = sum(sum(motif) * count for motif, count in specs)
        if steps <= 0 or ones != odd_symbols or not 0 <= odd_symbols <= steps:
            raise ValueError("parity factors disagree with the admitted action")
        if specs and specs[0][0][0] != source & 1:
            raise ValueError(
                "parity grammar does not start in the admitted source phase"
            )
        if local_source:
            if self._d8_frame is None:
                raise ValueError("D8 parity fragment is outside its frame batch")
        elif self._d8_frame is not None or self._source_is_local:
            raise ValueError("exact parity fragment bypasses its D8 frame batch")
        elif source != self._source:
            raise ValueError("parity fragment does not continue its exact source seam")

        original_length = len(self._factors)
        original_last = self._factors[-1] if original_length else None
        original_entries = self._entries
        reserved_entries = reserved_nodes = 0
        try:
            for motif, repetitions in specs:
                previous = (
                    self._factors[-1]
                    if self._factors and self._factors[-1].motif == motif
                    else None
                )
                merged_repetitions = repetitions + (
                    0 if previous is None else previous.repetitions
                )
                nodes = self._factor_cost(motif, merged_repetitions)
                previous_nodes = (
                    self._factor_cost(motif, previous.repetitions)
                    if previous is not None
                    else 0
                )
                entries = int(previous is None)
                node_delta = nodes - previous_nodes
                self._ledger.reserve(self._owner, entries=entries, nodes=node_delta)
                reserved_entries += entries
                reserved_nodes += node_delta
                factor = ParityFactor(motif, merged_repetitions)
                if previous is not None:
                    self._factors[-1] = factor
                else:
                    self._factors.append(factor)
                self._entries += entries
        except BaseException:
            self._factors.rollback_unpublished(original_length)
            if original_length and original_last is not None:
                self._factors[original_length - 1] = original_last
            self._entries = original_entries
            if reserved_entries or reserved_nodes:
                self._ledger.release(
                    self._owner, entries=reserved_entries, nodes=reserved_nodes
                )
            raise

        self._source = endpoint
        self._source_is_local = local_source
        self._steps += steps
        self._one_symbols += odd_symbols
        self._factor_nodes += reserved_nodes

    def append_zero_run(self, source: int, length: int) -> int:
        if (
            type(source) is not int
            or source <= 0
            or type(length) is not int
            or length <= 0
            or source % (1 << length)
        ):
            raise ValueError("zero-run source does not carry its exact valuation")
        endpoint = source >> length
        self._append_admitted(
            source,
            endpoint,
            (((0,), length),),
            odd_symbols=0,
        )
        return endpoint

    def append_one_run(self, source: int, length: int) -> tuple[int, int]:
        if (
            type(source) is not int
            or source <= 0
            or type(length) is not int
            or length <= 0
            or source & 1 == 0
            or (source + 1) % (1 << length) != 0
        ):
            raise ValueError("one-run source does not have odd parity")
        gain = 3**length
        endpoint = gain * ((source + 1) >> length) - 1
        if endpoint <= 0:
            raise ValueError("one-run endpoint must remain positive")
        self._append_admitted(
            source,
            endpoint,
            (((1,), length),),
            odd_symbols=length,
        )
        return endpoint, gain

    def append_cycle(self, repetitions: int) -> None:
        if (
            type(repetitions) is not int
            or repetitions <= 0
            or self._source != 1
            or self._source_is_local
        ):
            raise ValueError("cycle grammar requires the admitted singleton cycle")
        self._append_admitted(
            1,
            1,
            (((1, 0), repetitions),),
            odd_symbols=repetitions,
        )

    def append_boundary_macro(self, macro: object) -> None:
        from number_compiler.sequences.collatz.boundary_macros import (
            CollatzBoundaryMacro,
            validate_boundary_macro,
        )

        if type(macro) is not CollatzBoundaryMacro:
            raise TypeError("boundary grammar needs its exact producer action")
        validate_boundary_macro(macro)
        specs = boundary_macro_specs(macro)
        self._append_admitted(
            macro.source,
            macro.endpoint,
            specs,
            odd_symbols=macro.odd_symbols,
        )

    def append_border_return_macro(self, macro: object) -> None:
        """Append certified 6305 return/exit words as a compact parity SLP."""
        from number_compiler.sequences.collatz.border_return_grammar import (
            BorderReturnMacro,
            validate_border_return_macro,
        )

        if type(macro) is not BorderReturnMacro:
            raise TypeError("border return needs its exact producer action")
        validate_border_return_macro(macro)
        specs = tuple(((bit,), length) for bit, length in macro.parts)
        self._append_admitted(
            macro.source, macro.endpoint, specs, odd_symbols=macro.odd_symbols
        )

    def append_unified_skew_chain(self, chain: object) -> None:
        """Commit one joined border/helix grammar, with all seams.

        No intermediate parity word is materialized. The composed producer
        guards and its quadratic skew transfer must agree before publication.
        """
        from number_compiler.sequences.collatz.unified_skew_chain import (
            UnifiedSkewChain,
        )

        if type(chain) is not UnifiedSkewChain:
            raise TypeError("unified skew grammar needs its issued action")
        chain.verify()
        self._append_admitted(
            chain.source,
            chain.endpoint,
            chain.factors,
            odd_symbols=chain.odd_symbols,
        )

    def append_guarded_skew_repetitions(
        self,
        chain: object,
        power: object,
        endpoint: int,
        *,
        preflight: Callable[[int], None],
    ) -> None:
        """Retain the exact repeated word under its source-issued cylinder."""
        from number_compiler.sequences.collatz.skew_cylinder_repeat import (
            GuardedSkewCylinderPower,
        )
        from number_compiler.sequences.collatz.unified_skew_chain import (
            UnifiedSkewChain,
        )

        if (
            type(chain) is not UnifiedSkewChain
            or type(power) is not GuardedSkewCylinderPower
            or type(endpoint) is not int
        ):
            raise TypeError("repeated skew grammar needs issued source authority")
        chain.verify()
        power.verify()
        if (
            power.source != chain.source
            or power.action is not chain.fields
            or power.repetitions <= 1
            or not power.cylinder.admits(power.repetitions)
        ):
            raise ValueError("repeated parity grammar differs from its source cylinder")
        current = chain.source
        for _ in range(power.repetitions):
            preflight(
                current.bit_length()
                + chain.fields.gain.bit_length()
                + 2 * chain.fields.steps
                + 16
            )
            following = chain.fields.endpoint(current)
            self._append_admitted(
                current,
                following,
                chain.factors,
                odd_symbols=chain.odd_symbols,
            )
            current = following
        if current != endpoint:
            raise ValueError("repeated parity grammar endpoint differs from its power")

    def append_terminal_power2_macro(self, macro: object) -> None:
        from number_compiler.sequences.collatz.terminal_preimage import (
            CollatzTerminalPower2Macro,
            validate_terminal_power2_macro,
        )

        if type(macro) is not CollatzTerminalPower2Macro:
            raise TypeError("terminal grammar needs its exact producer action")
        validate_terminal_power2_macro(macro)
        self._append_admitted(
            macro.source,
            macro.endpoint,
            (((1,), 1), ((0,), macro.exponent - 1)),
            odd_symbols=1,
        )

    def append_mixed_clock_macro(self, macro: object) -> None:
        from number_compiler.sequences.collatz.mixed_clock_macros import (
            MixedClockMacro,
            validate_mixed_clock_macro,
        )

        if type(macro) is not MixedClockMacro:
            raise TypeError("mixed parity grammar needs its exact producer action")
        validate_mixed_clock_macro(macro)
        specs = ((macro.motif, macro.repetitions),)
        self._append_admitted(
            macro.source,
            macro.endpoint,
            specs,
            odd_symbols=macro.odd_symbols,
        )

    def append_d8_transition(self, transition: _D8ParityTransition) -> None:
        if (
            type(transition) is not _D8ParityTransition
            or not transition.producer_issued
            or self._d8_frame is not transition.source_frame
        ):
            raise ValueError("D8 parity word needs its exact table-issued transition")
        if self._source_is_local:
            if transition.source_local != self._source:
                raise ValueError("D8 parity word does not continue its local seam")
        elif transition.source_local != self._source & 255:
            raise ValueError("D8 parity word does not match the exact source low port")
        specs = ((tuple((transition.odd_mask >> bit) & 1 for bit in range(8)), 1),)
        self._append_admitted(
            transition.source_local,
            transition.endpoint_local,
            specs,
            odd_symbols=transition.odd_mask.bit_count(),
            local_source=True,
        )
        self._d8_frame = transition.advanced_frame

    def begin_d8_batch(self, source: int, frame: object) -> None:
        from number_compiler.sequences.collatz.temporal_dyadic import D8CylinderFrame

        if (
            self._closed
            or self._program is not None
            or self._d8_frame is not None
            or type(frame) is not D8CylinderFrame
            or type(source) is not int
            or source <= 0
            or self._source_is_local
            or source != self._source
            or frame.source != source
            or frame.consumed != 0
            or frame.origin != 0
            or frame.gain != 1
        ):
            raise ValueError("D8 parity batch does not start at its exact source")
        self._d8_frame = frame

    def finish_d8_batch(self, endpoint: int, frame: object) -> None:
        from number_compiler.sequences.collatz.temporal_dyadic import D8CylinderFrame

        if (
            self._d8_frame is None
            or type(frame) is not D8CylinderFrame
            or self._d8_frame is not frame
            or not self._source_is_local
            or self._source != frame.local_word()
            or type(endpoint) is not int
            or endpoint <= 0
            or frame.materialize() != endpoint
        ):
            raise ValueError("D8 parity batch endpoint differs from its exact frame")
        self._source = endpoint
        self._source_is_local = False
        self._d8_frame = None

    def finish(
        self, endpoint: int, *, steps: int, one_symbols: int
    ) -> NormalizedParityProgram:
        if (
            self._closed
            or self._d8_frame is not None
            or self._program is not None
            or type(endpoint) is not int
            or endpoint <= 0
            or type(steps) is not int
            or type(one_symbols) is not int
            or steps != self._steps
            or one_symbols != self._one_symbols
            or endpoint != self._source
        ):
            raise ValueError(
                "parity grammar does not match the completed normalized action"
            )
        self._program_nodes = 3 * len(self._factors) + 2
        self._ledger.reserve(self._owner, entries=1, nodes=self._program_nodes)
        try:
            program = _issue_program(self)
        except BaseException:
            self._ledger.release(self._owner, entries=1, nodes=self._program_nodes)
            self._program_nodes = 0
            raise
        self._program = program
        return program

    def close(self) -> None:
        if self._closed:
            return
        if self._program is not None:
            object.__setattr__(self._program, "_authority", _UNISSUED)
            self._program = None
        self._factors.clear()
        if self._entries or self._program_nodes or self._base_nodes:
            self._ledger.release(
                self._owner,
                entries=self._entries + int(self._program_nodes > 0),
                nodes=self._factor_nodes + self._program_nodes + self._base_nodes,
            )
            self._entries = 0
            self._factor_nodes = 0
            self._program_nodes = 0
            self._base_nodes = 0
        self._ledger.mark_disposed(self._owner)
        self._closed = True


def boundary_macro_specs(
    macro: object,
) -> tuple[tuple[tuple[int, ...], int], ...]:
    """Return the producer-admitted compact runs before factor allocation."""
    identity = getattr(macro, "identity", None)
    repetitions = getattr(macro, "repetitions", None)
    if identity is None or type(repetitions) is not int or repetitions <= 0:
        raise ValueError("boundary macro repetitions are malformed")
    if identity == ENTRY_421:
        specs: list[tuple[tuple[int, ...], int]] = [((0,), 2)]
        if repetitions > 1:
            specs.append(((1, 0), repetitions - 1))
        specs.append(((1,), 1))
        return tuple(specs)
    if identity == ENTRY_4721:
        return (((0,), 1), ((1,), 2 * repetitions))
    if identity == ENTRY_0563:
        return (((0,), 1), ((1,), 2 * repetitions))
    if (phase := boundary_macro_26847_phase(identity)) is not None:
        specs = []
        if phase < 4:
            specs.append(((0,), 4 - phase))
        if repetitions > 1:
            specs.append(((1, 0, 0, 0), repetitions - 1))
        specs.append(((1,), 1))
        return tuple(specs)
    if identity == PATH_630:
        return (((0,), 1), ((1,), 1), ((0,), repetitions))
    if identity == PATH_305:
        return (((1,), 1), ((0,), repetitions))
    if identity == ENTRY_89_AT_NINE:
        return (((1,), repetitions),)
    raise ValueError("unknown admitted Collatz boundary family")


__all__ = [
    "NormalizedParityProgram",
    "ParityFactor",
    "ParityProgramBuilder",
    "boundary_macro_specs",
]
