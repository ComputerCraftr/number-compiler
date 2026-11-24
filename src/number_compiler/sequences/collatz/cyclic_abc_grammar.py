"""Source-certified mixed Collatz row actions, independent of named borders.

The normalized shortcut H0(x)=x/2, H1(x)=(3*x+1)/2 has
    H_word(x)=(3**odds*x + J)/2**steps.
The word's physical clock is steps+odds.  For a periodic row, the
2-adic fixed-point defect (3**odds-2**steps)*x+J certifies exactly
v2(defect) matching normalized symbols (or unboundedly when it vanishes).
No historical parity tape is needed to issue that finite prefix.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from functools import lru_cache
from typing import Final

from number_compiler.arithmetic.automata.affine_port_action import AffinePortAction
from number_compiler.sequences.collatz.cyclic_diagonal import (
    CyclicDefectGuard,
    CyclicDiagonalState,
    CyclicLaurentAction,
)

_MOTIF_PHASE_KIND: Final[str] = "collatz-abc-motif-phase-v2"
_CYCLIC_ISSUER = object()


@dataclass(frozen=True, slots=True)
class ShortcutAffine:
    """Ordered normalized affine word, without an occurrence history."""

    steps: int
    odds: int
    offset: int

    def __post_init__(self) -> None:
        if (
            type(self.steps) is not int
            or type(self.odds) is not int
            or type(self.offset) is not int
            or self.steps < 0
            or not 0 <= self.odds <= self.steps
            or self.offset < 0
            or (self.steps == 0 and self.offset != 0)
        ):
            raise ValueError("invalid normalized Collatz action")

    @property
    def gain(self) -> int:
        gain: int = 3**self.odds
        return gain

    @classmethod
    def identity(cls) -> ShortcutAffine:
        return cls(0, 0, 0)

    @classmethod
    def from_word(cls, word: str) -> ShortcutAffine:
        if type(word) is not str or any(bit not in "01" for bit in word):
            raise ValueError("shortcut word must be binary")
        offset = 0
        for index, bit in enumerate(word):
            if bit == "1":
                offset = 3 * offset + (1 << index)
        return cls(len(word), word.count("1"), offset)

    def then(self, after: ShortcutAffine) -> ShortcutAffine:
        if type(after) is not ShortcutAffine:
            raise TypeError("shortcut composition needs another affine action")
        return ShortcutAffine(
            self.steps + after.steps,
            self.odds + after.odds,
            after.gain * self.offset + (after.offset << self.steps),
        )

    def power(self, repetitions: int) -> ShortcutAffine:
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("shortcut repetitions must be nonnegative")
        result = ShortcutAffine.identity()
        factor = self
        while repetitions:
            if repetitions & 1:
                result = result.then(factor)
            repetitions >>= 1
            if repetitions:
                factor = factor.then(factor)
        return result

    @property
    def source_residue(self) -> int:
        if not self.steps:
            return 0
        modulus = 1 << self.steps
        return -self.offset * pow(self.gain, -1, modulus) % modulus

    def certifies(self, source: int) -> bool:
        return (
            type(source) is int
            and source > 0
            and (self.gain * source + self.offset) % (1 << self.steps) == 0
        )

    def endpoint(self, source: int) -> int:
        if not self.certifies(source):
            raise ValueError("source is outside the guarded shortcut word")
        return (self.gain * source + self.offset) >> self.steps


@dataclass(frozen=True, slots=True)
class ParameterizedABC:
    """The A^a B^b C^c ordered grammar: no letter expansion for powering."""

    words: tuple[str, str, str]
    counts: tuple[int, int, int]

    def __post_init__(self) -> None:
        if (
            type(self.words) is not tuple
            or len(self.words) != 3
            or type(self.counts) is not tuple
            or len(self.counts) != 3
            or any(
                type(word) is not str
                or not word
                or any(bit not in "01" for bit in word)
                for word in self.words
            )
            or any(type(count) is not int or count < 0 for count in self.counts)
        ):
            raise ValueError("invalid parameterized abc grammar")

    @classmethod
    def from_motif(cls, word: str) -> ParameterizedABC:
        """Factor a bounded motif as three powered words, not occurrences.

        A and B are its first two maximal constant runs. C is the remaining
        suffix, itself a word, or an unused third symbol if no suffix exists.
        """
        if type(word) is not str or not word or any(b not in "01" for b in word):
            raise ValueError("motif must be a nonempty shortcut word")
        first = len(word) - len(word.lstrip(word[0]))
        if first == len(word):
            return cls((word[0], "0", "1"), (first, 0, 0))
        second_bit = word[first]
        second = len(word[first:]) - len(word[first:].lstrip(second_bit))
        suffix = word[first + second :]
        return cls(
            (word[0], second_bit, suffix or "0"), (first, second, int(bool(suffix)))
        )

    @property
    def action(self) -> ShortcutAffine:
        result = ShortcutAffine.identity()
        for word, count in zip(self.words, self.counts, strict=True):
            if count:
                result = result.then(ShortcutAffine.from_word(word).power(count))
        return result

    def short_word(self, *, limit: int = 256) -> str:
        if (
            sum(len(word) * n for word, n in zip(self.words, self.counts, strict=True))
            > limit
        ):
            raise ValueError("cyclic rotation requires an explicitly bounded motif")
        return "".join(
            word * n for word, n in zip(self.words, self.counts, strict=True)
        )


@dataclass(frozen=True, slots=True)
class CyclicGuardedRow:
    """A periodic source row, with phase as part of the guarded action key."""

    word: str

    def __post_init__(self) -> None:
        if (
            type(self.word) is not str
            or not self.word
            or any(bit not in "01" for bit in self.word)
        ):
            raise ValueError("cyclic row requires a nonempty binary motif")

    @property
    def abc(self) -> ParameterizedABC:
        return ParameterizedABC.from_motif(self.word)

    @property
    def motif(self) -> ShortcutAffine:
        return self.abc.action

    @property
    def motif_phase_id(self) -> tuple[str, str, int]:
        """Motif/rotation key only: NOT a complete guarded future state."""
        canonical, entry_phase = self.canonical_phase
        return (_MOTIF_PHASE_KIND, canonical, entry_phase)

    @property
    def canonical_phase(self) -> tuple[str, int]:
        action = self.laurent_action
        return action.necklace.word, action.phase

    @property
    def laurent_action(self) -> CyclicLaurentAction:
        return CyclicLaurentAction.from_word(self.word)

    def rotated(self, phase: int) -> CyclicGuardedRow:
        if type(phase) is not int:
            raise ValueError("cyclic phase must be an integer")
        phase %= len(self.word)
        return CyclicGuardedRow(self.word[phase:] + self.word[:phase])

    def advance_entry_phase(self, source: int) -> tuple[CyclicGuardedRow, int]:
        """Exact cyclic defect transport, with no repeated-word decoding.

        For the first source bit b, the rotated defect is 3**b/2 times
        the old defect.  The division is exact on an authenticated inlet.
        """
        if not self.motif.certifies(source):
            raise ValueError("rotation requires this row's exact dyadic source guard")
        bit = int(self.word[0])
        following = (3 * source + 1) >> 1 if bit else source >> 1
        rotated = self.rotated(1)
        numerator = (3 if bit else 1) * self.defect(source)
        if numerator & 1 or rotated.defect(following) != (numerator >> 1):
            raise AssertionError("cyclic row defect did not transport by 3**b/2")
        return rotated, following

    def defect(self, source: int) -> int:
        if type(source) is not int or source <= 0:
            raise ValueError("defect requires a positive physical source")
        word_action = self.motif
        return (
            word_action.gain - (1 << word_action.steps)
        ) * source + word_action.offset

    def matched_steps(self, source: int) -> int | None:
        """Exact number of matching periodic symbols; None means infinite."""
        return CyclicDefectGuard(self.laurent_action, source).first_mismatch

    def prefix_odds(self, length: int) -> int:
        if type(length) is not int or length < 0:
            raise ValueError("prefix length must be nonnegative")
        copies, tail = divmod(length, len(self.word))
        return copies * self.word.count("1") + self.word[:tail].count("1")

    def prefix_ticks(self, length: int) -> int:
        return length + self.prefix_odds(length)

    def prefix_action(self, length: int) -> ShortcutAffine:
        if type(length) is not int or length < 0:
            raise ValueError("prefix length must be nonnegative")
        law = self.laurent_action
        odds = law.odds(length)
        return ShortcutAffine(length, odds, law.prefix_offset(length, 3**odds))

    def admitted_prefix(
        self,
        source: int,
        remaining_ticks: int,
        *,
        maximum_steps: int = 8192,
        minimum_steps: int = 1,
        reserve_bits: Callable[[int], None] | None = None,
    ) -> CyclicRowAdmission | None:
        if (
            type(remaining_ticks) is not int
            or remaining_ticks < 0
            or type(maximum_steps) is not int
            or maximum_steps < 0
            or type(minimum_steps) is not int
            or minimum_steps < 1
        ):
            raise ValueError("invalid physical clock or power limit")
        guard = CyclicDefectGuard(self.laurent_action, source)
        matched = guard.first_mismatch
        if matched is not None and matched < minimum_steps:
            return None
        steps = min(
            guard.action.steps_for_ticks(remaining_ticks),
            maximum_steps,
            matched if matched is not None else remaining_ticks,
        )
        if steps < minimum_steps:
            return None
        if reserve_bits is not None:
            reserve_bits(steps)
        return _issue_cyclic_row(self, guard, steps)


@dataclass(frozen=True, slots=True)
class CyclicRowAdmission:
    row: CyclicGuardedRow
    source: int
    action: ShortcutAffine
    physical_ticks: int
    maximum_match: int | None
    _authority: object = field(default=None, init=False, repr=False, compare=False)
    _endpoint: int | None = field(default=None, init=False, repr=False, compare=False)
    _guard: CyclicDefectGuard | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _seal: tuple[object, ...] = field(default=(), init=False, repr=False, compare=False)

    def require_issued(self) -> None:
        if self._authority is not _CYCLIC_ISSUER or self._seal != _admission_seal(
            self, self._endpoint, self._guard
        ):
            raise ValueError("cyclic action lacks its source issuer")

    @property
    def guard(self) -> CyclicDefectGuard:
        self.require_issued()
        assert self._guard is not None
        return self._guard

    def _require_projection(self, steps: int) -> CyclicDefectGuard:
        guard = self.guard
        if type(steps) is not int or not 0 <= steps <= self.action.steps:
            raise ValueError("cyclic projection exceeds certified admission")
        return guard

    def point_at(self, steps: int, *, reserve_bits: Callable[[int], None]) -> int:
        guard = self._require_projection(steps)
        if not callable(reserve_bits):
            raise TypeError("cyclic projection requires a scratch owner")
        reserve_bits(8 * (self.source.bit_length() + 4 * steps + 128))
        if steps == self.action.steps:
            return self.endpoint
        return guard.point(steps, 3 ** guard.action.odds(steps))[0]

    def diagonal_state(
        self,
        steps: int,
        radix: int,
        precision: int,
        *,
        reserve_bits: Callable[[int], None],
    ) -> CyclicDiagonalState:
        guard = self._require_projection(steps)
        if (
            not callable(reserve_bits)
            or type(precision) is not int
            or precision < 0
            or type(radix) is not int
            or radix not in (2, 10)
        ):
            raise ValueError(
                "diagonal projection requires radix, precision and scratch owner"
            )
        reserve_bits(
            16
            * (self.source.bit_length() + 4 * precision + len(guard.action.word) + 128)
        )
        return guard.state(steps, radix, precision)

    def projected_upper_action(
        self,
        steps: int,
        radix: int,
        cut: int,
        width: int,
        *,
        reserve_bits: Callable[[int], None],
    ) -> AffinePortAction:
        guard = self._require_projection(steps)
        if (
            not callable(reserve_bits)
            or type(cut) is not int
            or cut < steps
            or type(width) is not int
            or width < 1
            or type(radix) is not int
            or radix not in (2, 10)
        ):
            raise ValueError("moving cut requires a guarded seam and precision owner")
        reserve_bits(
            16
            * (
                4 * self.source.bit_length()
                + 4 * (cut - steps + width)
                + 4 * len(guard.action.necklace.word)
                + 128
            )
        )
        return guard.upper_response(steps, radix, cut, width)

    @property
    def endpoint(self) -> int:
        self.require_issued()
        assert self._endpoint is not None
        return self._endpoint

    @property
    def suffix_phase(self) -> int:
        self.require_issued()
        return self.action.steps % len(self.guard.action.necklace.word)

    @property
    def canonical_action_id(self) -> tuple[str, str, int]:
        """Identify the ordered motif and phase independently of its inlet."""
        self.require_issued()
        return self.row.motif_phase_id

    def advance(
        self, normalized_steps: int, *, reserve_bits: Callable[[int], None]
    ) -> CyclicRowAdmission | None:
        """Transport an admitted prefix to its exact source-bound suffix."""
        self.require_issued()
        if (
            type(normalized_steps) is not int
            or not 0 <= normalized_steps <= self.action.steps
        ):
            raise ValueError("cyclic advance exceeds certified future")
        if not callable(reserve_bits):
            raise TypeError("symbolic advance requires a scratch owner")
        if normalized_steps == 0:
            return self
        if normalized_steps == self.action.steps:
            return None
        reserve_bits(8 * (self.source.bit_length() + 4 * self.action.steps + 128))
        guard = self.guard
        following, transported = guard.point(
            normalized_steps, 3 ** guard.action.odds(normalized_steps)
        )
        rotated = self.row.rotated(normalized_steps)
        next_guard = CyclicDefectGuard(
            guard.action.rotated(normalized_steps), following
        )
        if next_guard.defect != transported:
            raise AssertionError("cyclic successor lost its Laurent defect transport")
        issued = _issue_cyclic_row(
            rotated, next_guard, self.action.steps - normalized_steps
        )
        if issued.endpoint != self.endpoint:
            raise AssertionError("symbolic cyclic advancement changed endpoint")
        return issued

    def moving_cut(
        self, cut: int, *, reserve_bits: Callable[[int], None]
    ) -> MixedUpperBand:
        """Project an admitted lower source to its moving upper response."""
        self.require_issued()
        if type(cut) is not int or cut < self.action.steps:
            raise ValueError("moving cut would discard a source-guarded low bit")
        if not callable(reserve_bits):
            raise TypeError("moving cut requires its scratch owner")
        reserve_bits(8 * (cut + self.source.bit_length() + 4 * self.action.steps + 128))
        port, lower = self.guard.exact_lower_response(
            self.action.steps, cut, self.action.gain
        )
        return MixedUpperBand(
            self.action,
            cut,
            self.source & ((1 << cut) - 1),
            port.gain,
            port.carry,
            lower,
        )


def _admission_seal(
    admission: CyclicRowAdmission, endpoint: int | None, guard: CyclicDefectGuard | None
) -> tuple[object, ...]:
    action = admission.action
    binding = None
    if guard is not None:
        law = guard.action
        binding = (
            guard.source,
            guard.defect,
            guard.first_mismatch,
            law.phase,
            law.necklace.word,
            law.delta,
            law.necklace.offsets,
            law.necklace.odd_prefix,
        )
    return (
        admission.row.word,
        admission.source,
        (action.steps, action.odds, action.offset),
        admission.physical_ticks,
        admission.maximum_match,
        endpoint,
        binding,
    )


def _issue_cyclic_row(
    row: CyclicGuardedRow, guard: CyclicDefectGuard, steps: int
) -> CyclicRowAdmission:
    if (
        type(row) is not CyclicGuardedRow
        or type(guard) is not CyclicDefectGuard
        or guard.action != row.laurent_action
        or type(steps) is not int
        or steps <= 0
    ):
        raise ValueError("cyclic source guard cannot issue this future action")
    guard.require_steps(steps)
    odds = guard.action.odds(steps)
    gain = 3**odds
    action = ShortcutAffine(steps, odds, guard.action.prefix_offset(steps, gain))
    port, lower = guard.exact_lower_response(steps, steps, gain)
    if lower:
        raise ArithmeticError("terminal moving cut retained a nonempty lower band")
    endpoint = port.apply(guard.source >> steps)
    if endpoint <= 0:
        raise ValueError("cyclic endpoint is not a positive physical value")
    out = CyclicRowAdmission(
        row, guard.source, action, steps + odds, guard.first_mismatch
    )
    object.__setattr__(out, "_authority", _CYCLIC_ISSUER)
    object.__setattr__(out, "_endpoint", endpoint)
    object.__setattr__(out, "_guard", guard)
    object.__setattr__(out, "_seal", _admission_seal(out, endpoint, guard))
    return out


@dataclass(frozen=True, slots=True)
class MixedUpperBand:
    """Moving-cut upper response; lower source and safety remain guarded."""

    action: ShortcutAffine
    cut: int
    low_source: int
    upper_gain: int
    carry: int
    lower_endpoint: int

    @classmethod
    def from_lower(
        cls, action: ShortcutAffine, cut: int, low_source: int
    ) -> MixedUpperBand:
        if (
            type(action) is not ShortcutAffine
            or type(cut) is not int
            or type(low_source) is not int
            or cut < action.steps
            or not 0 <= low_source < (1 << cut)
            or (action.gain * low_source + action.offset) % (1 << action.steps)
        ):
            raise ValueError("lower band does not authenticate this shortcut action")
        numerator = action.gain * low_source + action.offset
        carry = numerator >> cut
        lower = (numerator >> action.steps) % (1 << (cut - action.steps))
        return cls(action, cut, low_source, action.gain, carry, lower)

    def projected_action_id(self, output_bits: int) -> tuple[int, int, int]:
        """Canonical upper response; lower guard is deliberately separate.

        Identical IDs have identical response for every upper input modulo
        2**output_bits, even when their source residue/physical history differs.
        """
        if type(output_bits) is not int or output_bits < 1:
            raise ValueError("upper output demand must have positive precision")
        response = self.projected_response(output_bits)
        return (output_bits, response.gain, response.carry)

    def projected_response(self, output_bits: int) -> AffinePortAction:
        if type(output_bits) is not int or output_bits < 1:
            raise ValueError("upper output demand must have positive precision")
        return AffinePortAction.reduced(1 << output_bits, self.upper_gain, self.carry)

    def upper_endpoint(self, upper_source: int) -> int:
        if type(upper_source) is not int or upper_source < 0:
            raise ValueError("upper source must be nonnegative")
        return self.upper_gain * upper_source + self.carry

    def then(self, following: MixedUpperBand) -> MixedUpperBand:
        """Join using gain_B*carry_A+carry_B, never 3**(n_A+n_B)."""
        if (
            type(following) is not MixedUpperBand
            or following.cut != self.cut - self.action.steps
            or following.low_source != self.lower_endpoint
        ):
            raise ValueError("mixed bands require the exact transported lower seam")
        action = self.action.then(following.action)
        return MixedUpperBand(
            action,
            self.cut,
            self.low_source,
            self.upper_gain * following.upper_gain,
            following.upper_gain * self.carry + following.carry,
            following.lower_endpoint,
        )


@lru_cache(maxsize=4)
def _small_period_words(period: int) -> tuple[str, ...]:
    """Small, fixed spatial phase LUT; no physical source history is retained."""
    if period not in (4, 8):
        raise ValueError("scalar source grammar supports periods 4 and 8")
    table: list[str] = []
    for residue in range(1 << period):
        x = residue
        word: list[str] = []
        for _ in range(period):
            bit = x & 1
            word.append(str(bit))
            x = (3 * x + 1) >> 1 if bit else x >> 1
        table.append("".join(word))
    return tuple(table)


def issue_cyclic_row(
    source: int,
    remaining_ticks: int,
    *,
    minimum_steps: int = 8,
    maximum_steps: int = 8192,
    reserve_bits: Callable[[int], None] | None = None,
) -> CyclicRowAdmission | None:
    """Issue a non-border mixed row without per-shortcut successor classification."""
    if (
        type(source) is not int
        or source <= 2
        or type(remaining_ticks) is not int
        or remaining_ticks < 0
    ):
        return None
    if remaining_ticks < minimum_steps + 2:
        return None
    for period in (4, 8):
        word = _small_period_words(period)[source % (1 << period)]
        if not ("0" in word and "1" in word):
            continue
        row = CyclicGuardedRow(word)
        admitted = row.admitted_prefix(
            source,
            remaining_ticks,
            maximum_steps=maximum_steps,
            minimum_steps=max(minimum_steps, 2 * period),
            reserve_bits=reserve_bits,
        )
        if admitted is not None and admitted.action.steps >= max(
            minimum_steps, 2 * period
        ):
            return admitted
    return None


__all__ = [
    "ShortcutAffine",
    "ParameterizedABC",
    "CyclicGuardedRow",
    "CyclicRowAdmission",
    "MixedUpperBand",
    "issue_cyclic_row",
]
