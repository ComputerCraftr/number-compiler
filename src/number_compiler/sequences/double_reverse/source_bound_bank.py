"""Owner-scoped pointed bank producers over an authenticated source prefix."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)
from number_compiler.sequences.double_reverse._temporal_bank_authority import (
    issue_source_record,
)
from number_compiler.sequences.double_reverse.protected_temporal_bank import (
    MAX_PROTECTED_PERIOD,
    ExactTemporalPairPort,
    protected_periodic_bank,
)
from number_compiler.sequences.double_reverse.source_adapter import (
    _DoubleReverseSource,
    _DoubleReverseSourceAdapter,
)
from number_compiler.sequences.double_reverse.temporal_bank_output_morphism import (
    CertifiedSpatialBankMorphism,
    ExactPointedBankWindow,
    certified_spatial_bank_morphism,
    frame_from_digits,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    DoubleReverseTemporalHashlife,
    growth_ports,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    DoubleReverseSourcePrefix,
    UncertifiedPointedStencilError,
)
from number_compiler.sequences.double_reverse.temporal_residue_quotient import (
    CertifiedResidueTemporalAction,
    certified_residue_action,
    decimal_residues_from_slp,
    source_residue_quotient,
)


@dataclass(frozen=True, slots=True)
class PointedBankSource:
    """Typed, already-certified source and temporal coordinates for bank work."""

    arena: LedgerSLPArena
    engine: DoubleReverseTemporalHashlife
    ledger: ResourceLedger
    scratch_owner: int
    physical_prefix: int
    root: int
    phase: int
    f_steps: int
    width_out: int
    max_steps: int
    max_state_bits: int
    width_bits: Callable[[int], int]

    @property
    def width_in(self) -> int:
        return self.arena.nodes[self.root].length


def exact_temporal_pair_digits(
    source: PointedBankSource, final_pair_position: int
) -> tuple[tuple[int, int], bool]:
    """Read a final pair, preferring a source-relative periodic producer."""
    if type(final_pair_position) is not int or final_pair_position < 0:
        raise ValueError("pair position must be nonnegative")
    if 2 * final_pair_position >= source.width_out - 1:
        raise IndexError(final_pair_position)
    if type(source.f_steps) is not int or source.f_steps < 0:
        raise ValueError("pointed source requires a nonnegative T-squared horizon")
    if source.f_steps == 0:
        right_position = source.width_in - 1 - final_pair_position
        return (
            (
                symbol_at(source.arena, source.root, final_pair_position),
                symbol_at(source.arena, source.root, right_position),
            ),
            False,
        )
    left_births, _right_births = growth_ports(source.phase, source.f_steps)
    source_position = final_pair_position - left_births
    right_position = source.width_in - 1 - source_position
    final_pair: tuple[int, int] | None = None
    used_periodic_bank = False
    if (
        source_position >= 0
        and source.f_steps <= source_position
        and source_position + source.f_steps + 2 <= source.width_in
        and right_position + source.f_steps + 2 <= source.width_in
        and symbol_at(source.arena, source.root, source_position)
        == symbol_at(source.arena, source.root, source_position + 2)
        and symbol_at(source.arena, source.root, right_position)
        == symbol_at(source.arena, source.root, right_position + 2)
    ):
        try:
            bank = protected_periodic_bank(
                source.arena,
                source.root,
                source.phase,
                source_position,
                source.f_steps,
                2,
                physical_prefix=source.physical_prefix,
                ledger=source.ledger,
                scratch_owner=source.scratch_owner,
            )
        except ValueError:
            pass
        else:
            final_pair = bank.at(source.f_steps - 1).next_digits
            used_periodic_bank = True
    if final_pair is None:
        final_pair = (
            source.engine.pointed_stencil(
                source.root, source.f_steps, source.phase, final_pair_position
            ).digit,
            source.engine.pointed_stencil(
                source.root,
                source.f_steps,
                source.phase,
                source.width_out - 1 - final_pair_position,
            ).digit,
        )
    return final_pair, used_periodic_bank


def exact_temporal_bank_window(
    source: PointedBankSource, final_pair_start: int, pair_count: int
) -> ExactPointedBankWindow:
    """Produce a bounded, unpumped output interval and its next-frame ports."""
    final_pair_start = _coordinate(final_pair_start, "final pair start")
    pair_count = _coordinate(pair_count, "pair count", minimum=1)
    if pair_count > 64:
        raise UncertifiedPointedStencilError(
            "exact bank windows are limited to 64 output pairs"
        )
    if 2 * (final_pair_start + pair_count - 1) >= source.width_out - 1:
        raise IndexError("bank pair window exceeds the final symmetric half")
    if source.max_steps < source.physical_prefix + 2 * (source.f_steps + 1):
        raise UncertifiedPointedStencilError(
            "conditional borrow window exceeds the admitted physical-step budget"
        )
    next_left, next_right = growth_ports(source.phase, source.f_steps + 1)
    current_left, current_right = growth_ports(source.phase, source.f_steps)
    birth_left = next_left - current_left
    birth_right = next_right - current_right
    next_width = source.width_out + birth_left + birth_right
    if 2 * (final_pair_start + pair_count - 1 + birth_left) >= next_width - 1:
        raise IndexError("next-frame bank ray crosses the symmetric half")
    if source.width_bits(next_width) > source.max_state_bits:
        raise UncertifiedPointedStencilError(
            "pointed bank next-frame borrow exceeds the admitted bit budget"
        )
    frames = []
    for offset in range(pair_count):
        coordinate = final_pair_start + offset
        following = coordinate + birth_left
        current_pair = (
            source.engine.pointed_stencil(
                source.root, source.f_steps, source.phase, coordinate
            ).digit,
            source.engine.pointed_stencil(
                source.root,
                source.f_steps,
                source.phase,
                source.width_out - 1 - coordinate,
            ).digit,
        )
        next_pair = (
            source.engine.pointed_stencil(
                source.root, source.f_steps + 1, source.phase, following
            ).digit,
            source.engine.pointed_stencil(
                source.root,
                source.f_steps + 1,
                source.phase,
                next_width - 1 - following,
            ).digit,
        )
        frames.append(
            frame_from_digits(current_pair, next_pair, birth_left, birth_right)
        )
    source_mod99, source_mod198 = decimal_residues_from_slp(
        source.arena,
        source.root,
        ledger=source.ledger,
        scratch_owner=source.scratch_owner,
    )
    residue_action = certified_residue_action(
        phase=source.phase,
        width=source.width_in,
        duration=2 * source.f_steps,
        source_mod99=source_mod99,
        source_mod198=source_mod198,
    )
    issue_source_record(
        residue_action,
        source.arena,
        source.root,
        source_generation=source.physical_prefix,
    )
    if residue_action.width_out != source.width_out:
        raise AssertionError("pointed bank output width disagrees with its clock")
    packet = ExactPointedBankWindow(
        source.physical_prefix,
        source.f_steps,
        source.phase,
        source.width_in,
        source.width_out,
        final_pair_start,
        tuple(frames),
        residue_action,
    )
    return issue_source_record(
        packet,
        source.arena,
        source.root,
        source_generation=source.physical_prefix,
    )


def temporal_bank_output_morphism(
    source: PointedBankSource,
    final_pair_start: int,
    pair_count: int,
    *,
    period: int,
) -> CertifiedSpatialBankMorphism:
    """Translate a final-word interval back to a guarded entry-word interval."""
    final_pair_start = _coordinate(final_pair_start, "final pair start")
    pair_count = _coordinate(pair_count, "pair count", minimum=1)
    period = _coordinate(period, "bank period", minimum=1)
    if period > MAX_PROTECTED_PERIOD:
        raise ValueError("protected bank period exceeds its source guard bound")
    if 2 * (final_pair_start + pair_count - 1) >= source.width_out - 1:
        raise IndexError("bank interval exceeds the final symmetric half")
    left_births, _right_births = growth_ports(source.phase, source.f_steps)
    source_pair_start = final_pair_start - left_births
    if source_pair_start < 0:
        raise UncertifiedPointedStencilError(
            "final pair interval begins before the source-relative halo"
        )
    return certified_spatial_bank_morphism(
        source.arena,
        source.root,
        source.phase,
        source_pair_start,
        pair_count,
        source.f_steps,
        period,
        physical_prefix=source.physical_prefix,
        ledger=source.ledger,
        scratch_owner=source.scratch_owner,
    )


def _coordinate(value: int, label: str, *, minimum: int = 0) -> int:
    if type(value) is not int or value < minimum:
        raise ValueError(f"{label} must be an integer at least {minimum}")
    return value


class DoubleReverseBankMixin:
    """Source-bound bank producers shared by the public term owner.

    The mixin keeps temporal port and source-coordinate policy beside the
    SLP-backed bank owner while its host supplies the already-issued prefix
    and Hashlife shape operations.
    """

    __slots__ = ()

    _adapter: _DoubleReverseSourceAdapter
    _arena: LedgerSLPArena
    _ledger: ResourceLedger
    _scratch_owner: int
    _source: _DoubleReverseSource
    generation: int
    max_steps: int
    max_state_bits: int

    def _check_open(self) -> None:
        raise NotImplementedError

    def _certified_prefix_entry(
        self, *, max_prefix: int, require_even_remainder: bool
    ) -> DoubleReverseSourcePrefix:
        raise NotImplementedError

    def _pointed_shape(
        self, entry: DoubleReverseSourcePrefix
    ) -> tuple[int, int, int, int]:
        raise NotImplementedError

    def _pointed_bank_source(
        self,
        entry: DoubleReverseSourcePrefix,
        root: int,
        phase: int,
        f_steps: int,
        width_out: int,
    ) -> PointedBankSource:
        return PointedBankSource(
            self._arena,
            self._adapter.temporal_hashlife,
            self._ledger,
            self._scratch_owner,
            entry.physical_steps,
            root,
            phase,
            f_steps,
            width_out,
            self.max_steps,
            self.max_state_bits,
            self._adapter._width_bits,
        )

    def _prepare_bank_source(
        self, *, max_prefix: int
    ) -> tuple[DoubleReverseSourcePrefix, PointedBankSource]:
        entry = self._certified_prefix_entry(
            max_prefix=max_prefix,
            require_even_remainder=True,
        )
        root, phase, steps, width = self._pointed_shape(entry)
        return entry, self._pointed_bank_source(entry, root, phase, steps, width)

    def exact_temporal_pair(self, pair_position: int) -> ExactTemporalPairPort:
        """Read an exact final pair, preferring its authenticated source bank."""
        self._check_open()
        pair_position = require_integer(pair_position, "pair position", 0)
        if self.generation < 2:
            raise UncertifiedPointedStencilError(
                "pointed pair requires at least two physical generations"
            )
        entry, source = self._prepare_bank_source(
            max_prefix=min(32, self.generation - 2)
        )
        width = source.width_out
        steps = source.f_steps
        final_pair, used_bank = exact_temporal_pair_digits(source, pair_position)
        if used_bank:
            self._ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_POINTED_REUSE
            )
        result = ExactTemporalPairPort.from_digits(
            pair_position,
            width,
            entry.physical_steps,
            steps,
            *final_pair,
        )
        self._ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_EXACT_PAIR_PUBLICATIONS
        )
        return result

    def exact_temporal_bank_window(
        self, final_pair_start: int, pair_count: int
    ) -> ExactPointedBankWindow:
        """Emit a bounded exact nonperiodic bank window from powered cones."""
        self._check_open()
        final_pair_start = require_integer(final_pair_start, "final pair start", 0)
        pair_count = require_integer(pair_count, "pair count", 1)
        if pair_count > 64:
            raise UncertifiedPointedStencilError(
                "exact bank windows are limited to 64 pairs"
            )
        if self.generation < 2:
            raise UncertifiedPointedStencilError(
                "pointed bank window requires a two-step temporal suffix"
            )
        _entry, source = self._prepare_bank_source(
            max_prefix=min(32, self.generation - 2)
        )
        try:
            return exact_temporal_bank_window(source, final_pair_start, pair_count)
        except ValueError as exc:
            raise UncertifiedPointedStencilError(str(exc)) from exc

    def temporal_bank_output_morphism(
        self, final_pair_start: int, pair_count: int, *, period: int = 2
    ) -> CertifiedSpatialBankMorphism:
        """Emit source-certified spatial output at the requested final time."""
        self._check_open()
        final_pair_start = require_integer(final_pair_start, "final pair start", 0)
        pair_count = require_integer(pair_count, "pair count", 1)
        period = require_integer(period, "bank period", 1, MAX_PROTECTED_PERIOD)
        if self.generation < 2:
            raise UncertifiedPointedStencilError(
                "spatial bank morphism requires a two-step temporal suffix"
            )
        _entry, source = self._prepare_bank_source(
            max_prefix=min(32, self.generation - 2)
        )
        try:
            return temporal_bank_output_morphism(
                source, final_pair_start, pair_count, period=period
            )
        except ValueError as exc:
            raise UncertifiedPointedStencilError(str(exc)) from exc

    def temporal_residue_quotient(
        self,
    ) -> tuple[int, CertifiedResidueTemporalAction]:
        """Predict source-bound residues modulo 99 and 198."""
        self._check_open()
        return source_residue_quotient(
            self._arena,
            self._adapter.temporal_hashlife,
            self._source.root,
            self.generation,
            self._certified_prefix_entry,
            ledger=self._ledger,
            scratch_owner=self._scratch_owner,
        )
