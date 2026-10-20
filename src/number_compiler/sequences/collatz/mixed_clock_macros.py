"""Bounded low-bit discovery of repeated, exactly guarded parity actions.

The preview proposes a word; only its full powered 2-adic cylinder admits it.
Finite innovation observations cannot authorize this substitution.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from typing import Final, cast

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.resources.process_cache import CacheLease
from number_compiler.sequences.collatz.border_identity import MixedParityMotif
from number_compiler.sequences.collatz.boundary_macros import BoundaryActionTemplateMemo
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.temporal_dyadic import (
    D8CylinderFrame,
    D8TemporalTable,
)

_ISSUER = object()
_MIXED_ACTION_CACHE_ISSUER = object()
MIXED_ACTION_CACHE_NAMESPACE: Final[str] = "collatz-mixed-action-index"
MIXED_ACTION_CACHE_VERSION: Final[str] = "collatz-complete-mixed-action-v2"
MIXED_ACTION_CACHE_INDEX_BITS = 16
_PREVIEW_BITS = (32, 64, 96)
_MAX_MOTIF = 64
MAX_MIXED_ACTION_SYMBOLS = 4096


@dataclass(frozen=True, slots=True, init=False)
class MixedClockMacro:
    source: int
    motif: tuple[int, ...]
    repetitions: int
    fields: DyadicTerminalFieldAction
    endpoint: int
    width_blank: BlankLedger | None
    _issuer: object = field(repr=False, compare=False)
    _binding: tuple[object, ...] = field(repr=False, compare=False)

    def __init__(self) -> None:
        raise TypeError("mixed clock macros require exact cylinder admission")

    @property
    def normalized_symbols(self) -> int:
        return self.fields.steps

    @property
    def odd_symbols(self) -> int:
        return sum(self.motif) * self.repetitions

    @property
    def physical_ticks(self) -> int:
        return self.normalized_symbols + self.odd_symbols

    def validate_issued(self) -> None:
        """Check this macro's issuer seal and unchanged payload in its owner."""
        if (
            type(self) is not MixedClockMacro
            or getattr(self, "_issuer", None) is not _ISSUER
        ):
            raise ValueError("mixed clock macro has no producer authority")
        if (
            self._binding
            != (
                self.source,
                self.motif,
                self.repetitions,
                self.fields,
                self.endpoint,
                self.width_blank,
            )
            or not self.fields.producer_issued
            or (
                self.width_blank is not None
                and type(self.width_blank) is not BlankLedger
            )
        ):
            raise ValueError("mixed clock macro payload changed after admission")


def validate_mixed_clock_macro(macro: MixedClockMacro) -> None:
    """Check the producer seal and unchanged complete payload, without replay."""
    macro.validate_issued()


def read_mixed_action_cache_bucket(lease: CacheLease) -> object:
    """Read this owner's exact process-cache bucket through its issuer seal."""
    if type(lease) is not CacheLease:
        raise TypeError("mixed action cache lookup needs an exact cache lease")
    return lease.get_issued(("macro",), _MIXED_ACTION_CACHE_ISSUER)


def update_mixed_action_cache_bucket(
    lease: CacheLease,
    update: Callable[[object], tuple[object, str]],
) -> tuple[bool | None, str | None]:
    """Atomically update this owner's bucket without exposing its issuer seal."""
    if type(lease) is not CacheLease:
        raise TypeError("mixed action cache publication needs an exact cache lease")
    return lease.update_issued(("macro",), _MIXED_ACTION_CACHE_ISSUER, update)


def _issue_macro(
    source: int,
    motif: tuple[int, ...],
    repetitions: int,
    action: DyadicTerminalFieldAction,
    endpoint: int,
    width: BlankLedger | None,
) -> MixedClockMacro:
    """Issue one guarded macro from an exact producer or cache record."""
    macro = object.__new__(MixedClockMacro)
    values = (source, motif, repetitions, action, endpoint, width)
    for name, value in zip(
        ("source", "motif", "repetitions", "fields", "endpoint", "width_blank"),
        values,
        strict=True,
    ):
        object.__setattr__(macro, name, value)
    object.__setattr__(macro, "_issuer", _ISSUER)
    object.__setattr__(macro, "_binding", values)
    return macro


def mixed_cache_payload(macro: MixedClockMacro) -> tuple[int, ...]:
    """Encode complete joint action fields and the compact parity descriptor."""
    validate_mixed_clock_macro(macro)
    if macro.width_blank is None:
        raise ValueError("mixed cache publication needs the cold width summary")
    fields = macro.fields
    motif_code = sum(bit << index for index, bit in enumerate(macro.motif))
    # The macro is already bound to this exact source and the publication
    # validator checks that source against the action.  Its canonical cylinder
    # residue can therefore be read from the admitted occurrence directly;
    # asking ``fields.source_residue`` would invert the gain modulo 2**steps,
    # repeating substantial arithmetic which admission has already settled.
    source_residue = macro.source & ((1 << fields.steps) - 1)
    return (
        fields.steps,
        source_residue,
        fields.gain,
        fields.offset,
        fields.sum_gain,
        fields.sum_offset,
        fields.previous_gain,
        fields.previous_offset,
        macro.odd_symbols,
        len(macro.motif),
        motif_code,
        macro.repetitions,
        macro.source,
        macro.endpoint,
        *macro.width_blank.as_tuple(),
    )


def validate_mixed_cache_publication(macro: MixedClockMacro) -> int:
    """Check the exact action once before its immutable record is issued."""
    validate_mixed_clock_macro(macro)
    if macro.width_blank is None:
        raise ValueError("mixed cache publication needs its exact width summary")
    expected_gain = _expected_mixed_gain(macro.odd_symbols)
    if (
        macro.fields.steps != len(macro.motif) * macro.repetitions
        or macro.fields.gain != expected_gain
        or not macro.fields.certifies(macro.source)
        or macro.fields.endpoint(macro.source) != macro.endpoint
        or macro.width_blank.delta
        != macro.endpoint.bit_length() - macro.source.bit_length()
        or macro.width_blank.minimum > 0
        or macro.width_blank.maximum < 0
    ):
        raise ValueError("mixed cache action is not an exact issued source action")
    return macro.odd_symbols + expected_gain.bit_length()


def restore_mixed_cache_payload(
    source: int,
    payload: object,
    *,
    include_width: bool,
    cache_lease: CacheLease | None = None,
) -> MixedClockMacro | None:
    """Rehydrate a complete cached action only when its full cylinder agrees."""
    if (
        type(source) is not int
        or source <= 0
        or type(include_width) is not bool
        or not is_exact_object_tuple(payload)
        or len(payload) != 17
        or any(type(value) is not int for value in payload)
    ):
        raise ValueError("mixed action cache payload is malformed")
    record = cast(tuple[int, ...], payload)
    (
        steps,
        residue,
        gain,
        offset,
        sum_gain,
        sum_offset,
        previous_gain,
        previous_offset,
        odd_symbols,
        motif_length,
        motif_code,
        repetitions,
        publisher_source,
        publisher_endpoint,
        width_delta,
        width_minimum,
        width_maximum,
    ) = record
    trusted_cache_record = cache_lease is not None
    if trusted_cache_record:
        expected_qualification = (
            MIXED_ACTION_CACHE_NAMESPACE,
            MIXED_ACTION_CACHE_VERSION,
            (publisher_source & ((1 << MIXED_ACTION_CACHE_INDEX_BITS) - 1),),
        )
        if type(cache_lease) is not CacheLease:
            raise ValueError("mixed cache payload has a foreign cache lease")
        if cache_lease.source_qualification != expected_qualification:
            raise ValueError("mixed cache payload has a foreign cache lease")
        issued_bucket = read_mixed_action_cache_bucket(cache_lease)
        if type(issued_bucket) is not tuple:
            raise ValueError("mixed cache payload has a foreign cache issuer")
        issued_records = cast(tuple[object, ...], issued_bucket)
        if record not in issued_records:
            raise ValueError("mixed cache payload has a foreign cache issuer")
    if (
        not 16 <= steps <= MAX_MIXED_ACTION_SYMBOLS
        or not 0 <= residue < 1 << steps
        or not 2 <= motif_length <= _MAX_MOTIF
        or not 0 <= motif_code < 1 << motif_length
        or repetitions < 2
        or steps != motif_length * repetitions
        or publisher_source <= 0
        or publisher_source % (1 << steps) != residue
    ):
        raise ValueError("mixed action cache descriptor is malformed")
    if source % (1 << steps) != residue:
        return None
    motif = tuple((motif_code >> index) & 1 for index in range(motif_length))
    if not 0 < sum(motif) < motif_length or sum(motif) * repetitions != odd_symbols:
        raise ValueError("mixed action cache parity descriptor is inconsistent")
    action = DyadicTerminalFieldAction.restore_cache_payload(
        steps,
        (gain, offset, sum_gain, sum_offset, previous_gain, previous_offset),
    )
    if (
        (not trusted_cache_record and action.gain != _expected_mixed_gain(odd_symbols))
        or not action.certifies(source)
        or not action.certifies(publisher_source)
    ):
        raise ValueError("mixed action cache cylinder differs from its action")
    endpoint = action.endpoint(source)
    if action.endpoint(publisher_source) != publisher_endpoint:
        raise ValueError("mixed action cache endpoint differs from its publisher")
    width: BlankLedger | None = None
    if include_width:
        if source != publisher_source:
            return None
        width = BlankLedger(width_delta, width_minimum, width_maximum)
        if (
            width.delta != endpoint.bit_length() - source.bit_length()
            or width.minimum > 0
            or width.maximum < 0
        ):
            raise ValueError("mixed action cache width summary is detached")
    return _issue_macro(source, motif, repetitions, action, endpoint, width)


def _expected_mixed_gain(odd_symbols: int) -> int:
    """Construct the normalized affine gain for strict unissued validation."""
    return cast(int, 3**odd_symbols)


def _scalar_preview(
    source: int, bits: int, templates: BoundaryActionTemplateMemo
) -> tuple[int, ...]:
    """Small stand-alone fallback for tests without a D8 execution owner."""
    if type(bits) is not int or bits < 16:
        raise ValueError("mixed clock preview needs at least 16 bits")
    value = source & ((1 << bits) - 1)
    result: list[int] = []
    operand_bits = source.bit_length()
    for _ in range(bits):
        operand_bits += value.bit_length()
        bit = value & 1
        result.append(bit)
        value = (3 * value + 1) // 2 if bit else value // 2
    templates.ledger.bump(_collatz_keys.COLLATZ_MIXED_CLOCK_CLASSIFICATIONS, bits)
    templates.ledger.bump(_collatz_keys.COLLATZ_MIXED_CLOCK_OPERAND_BITS, operand_bits)
    return tuple(result)


def _extend_d8_preview(
    frame: D8CylinderFrame,
    symbols: list[int],
    target_bits: int,
    table: D8TemporalTable,
    templates: BoundaryActionTemplateMemo,
) -> D8CylinderFrame:
    """Extend one exact preview through cached, authenticated D8 cells."""
    target_bits -= target_bits % 8
    if target_bits < len(symbols) or target_bits % 8:
        raise ValueError("mixed clock D8 preview extent is not monotone")
    while len(symbols) < target_bits:
        advanced, _ones, _residue, _origin, _width, word = (
            table.transition_with_parity_word(frame)
        )
        symbols.extend((word.odd_mask >> index) & 1 for index in range(8))
        frame = advanced
        templates.ledger.bump(_collatz_keys.COLLATZ_MIXED_CLOCK_CLASSIFICATIONS, 8)
    return frame


def _candidate_motifs(
    preview: tuple[int, ...], available_physical_ticks: int
) -> tuple[tuple[int, ...], ...]:
    """Propose periods using only symbols inside each candidate's horizon.

    The exact powered cylinder check remains authoritative.  Discovery must
    not demand symbols after the requested action: a valid finite repeated
    prefix can end immediately before the source leaves that period.
    """
    candidates: list[tuple[int, ...]] = []
    for length in range(
        2, min(_MAX_MOTIF, len(preview), available_physical_ticks // 2) + 1
    ):
        motif = preview[:length]
        if not 0 < sum(motif) < length:
            continue
        ticks_per_copy = length + sum(motif)
        repeats = min(
            available_physical_ticks // ticks_per_copy,
            MAX_MIXED_ACTION_SYMBOLS // length,
        )
        span = length * repeats
        if repeats < 2 or span < 16:
            continue
        comparisons = min(16, span - length, len(preview) - length)
        if any(
            preview[length + index] != motif[index % length]
            for index in range(comparisons)
        ):
            continue
        if any(
            length % divisor == 0 and motif == motif[:divisor] * (length // divisor)
            for divisor in range(1, length)
        ):
            continue
        candidates.append(motif)
    return tuple(candidates)


def _longest_repeat(
    source: int,
    motif: tuple[int, ...],
    limit: int,
    templates: BoundaryActionTemplateMemo,
) -> int:
    identity = MixedParityMotif(motif)

    def admitted(repeats: int) -> bool:
        action = templates.get(identity, repeats)[0]
        templates.ledger.bump(_collatz_keys.COLLATZ_MIXED_CLOCK_CYLINDER_CHECKS)
        templates.ledger.bump(
            _collatz_keys.COLLATZ_MIXED_CLOCK_OPERAND_BITS,
            source.bit_length() + action.steps,
        )
        return action.certifies(source)

    if limit < 2 or not admitted(2):
        return 0
    low, high = 2, min(4, limit)
    while high > low and admitted(high):
        low = high
        high = min(2 * high, limit)
    while high - low > 1:
        middle = (low + high) // 2
        if admitted(middle):
            low = middle
        else:
            high = middle
    return low


def _width_summary(
    source: int,
    endpoint: int,
    motif: tuple[int, ...],
    templates: BoundaryActionTemplateMemo,
) -> BlankLedger:
    # A positive affine motif has a monotone orbit. Each physical prefix is
    # also increasing in its entry, so extrema occur in the first/last copy.
    base = templates.get(MixedParityMotif(motif), 1)[0]
    last, remainder = divmod((endpoint << len(motif)) - base.offset, base.gain)
    if remainder:
        raise AssertionError("admitted mixed motif has a nonintegral predecessor")
    lower = upper = source.bit_length()
    for start in (source, last):
        value = start
        for bit in motif:
            if value & 1 != bit:
                raise AssertionError("mixed motif width boundary lost its source guard")
            if bit:
                value = 3 * value + 1
                upper = max(upper, value.bit_length())
            value //= 2
            lower = min(lower, value.bit_length())
            upper = max(upper, value.bit_length())
            templates.ledger.bump(_collatz_keys.COLLATZ_MIXED_CLOCK_WIDTH_PREFIXES)
            templates.ledger.bump(
                _collatz_keys.COLLATZ_MIXED_CLOCK_OPERAND_BITS, value.bit_length()
            )
    width = source.bit_length()
    return BlankLedger(endpoint.bit_length() - width, lower - width, upper - width)


def select_mixed_clock_macro(
    source: int,
    available_physical_ticks: int,
    *,
    templates: BoundaryActionTemplateMemo,
    d8_table: D8TemporalTable | None = None,
    max_preview_bits: int = 96,
) -> MixedClockMacro | None:
    """Select a repeated mixed word using bounded discovery and powered guards."""
    if type(source) is not int or source <= 0:
        raise ValueError("mixed clock source must be a positive exact integer")
    if type(available_physical_ticks) is not int or available_physical_ticks < 0:
        raise ValueError("mixed clock extent must be a nonnegative exact integer")
    if type(max_preview_bits) is not int or max_preview_bits not in _PREVIEW_BITS:
        raise ValueError("mixed clock preview must end at a bounded discovery stage")
    if available_physical_ticks < 16 or source <= 2:
        return None
    if d8_table is not None and (
        type(d8_table) is not D8TemporalTable or d8_table.ledger is not templates.ledger
    ):
        raise ValueError("mixed clock preview D8 table has another ledger")
    with templates.scratch(nodes=512 + (source.bit_length() + 63) // 64):
        best: tuple[tuple[int, ...], int] | None = None
        best_ticks = 0
        tested: set[tuple[int, ...]] = set()
        preview_symbols: list[int] = []
        preview_frame = D8CylinderFrame(source) if d8_table is not None else None
        for bits in _PREVIEW_BITS:
            if bits > max_preview_bits:
                break
            target = min(bits, available_physical_ticks)
            if d8_table is None:
                if target < 16:
                    continue
                preview = _scalar_preview(source, target, templates)
            else:
                if preview_frame is None:
                    raise AssertionError("D8 preview lost its source frame")
                preview_frame = _extend_d8_preview(
                    preview_frame,
                    preview_symbols,
                    target,
                    d8_table,
                    templates,
                )
                preview = tuple(preview_symbols)
            for motif in _candidate_motifs(preview, available_physical_ticks):
                if motif in tested:
                    continue
                tested.add(motif)
                length = len(motif)
                ticks = length + sum(motif)
                limit = min(
                    available_physical_ticks // ticks,
                    MAX_MIXED_ACTION_SYMBOLS // length,
                )
                repetitions = _longest_repeat(source, motif, limit, templates)
                if length * repetitions < 16 or ticks * repetitions <= best_ticks:
                    continue
                best = motif, repetitions
                best_ticks = ticks * repetitions
                if best_ticks == available_physical_ticks:
                    break
            if best_ticks == available_physical_ticks:
                # The full guarded action is already known. No longer
                # preview or alternative period can cover more of this query.
                break
        if best is None:
            return None
        motif, repetitions = best
        action = templates.get(MixedParityMotif(motif), repetitions)[0]
        endpoint = action.endpoint(source)
        width = _width_summary(source, endpoint, motif, templates)
        macro = _issue_macro(source, motif, repetitions, action, endpoint, width)
        templates.ledger.bump(_collatz_keys.COLLATZ_MIXED_CLOCK_ADMITTED_MACROS)
        return macro
