"""Issued Fermat 3X border-macro registry and jointly clocked port guards.

The owner is the existing, producer-authenticated bilateral three-power source.
A named clock is emitted only after its exact residue is checked.  Physical
tripling time is NOT the dyadic level.  High radial and dyadic XOR guards are
bound to the root, never assumed to hold at an arbitrary physical successor.
This module issues source actions, NOT Fermat primality certificates.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from math import gcd
from typing import cast

from number_compiler.sequences.power_numbers._harmonic_authority import (
    harmonic_verified,
    issue_harmonic,
    new_harmonic_issuer,
)
from number_compiler.sequences.power_numbers.three_dyadic_pivot_moore import (
    MAX_PIVOT_PRECISION,
    moving_unit_innovation_window,
)
from number_compiler.sequences.power_numbers.three_power_outer_inner_cyclotomic import (
    FermatOuterCyclotomicClock,
)
from number_compiler.sequences.power_numbers.three_power_signed_border_action import (
    SourceWeightedTriplingAction,
)


class FermatClockLaw(Enum):
    EULER_TRIPLING = "euler-tripling-residue"
    SOURCE_CYCLOTOMIC = "source-cyclotomic-residue"


class FermatClockId(Enum):
    """Closed typed identities for the two distinct Fermat clock laws."""

    _value_: tuple[FermatClockLaw, int, int | None, str]

    DECIMAL_2_DIGITS = (FermatClockLaw.EULER_TRIPLING, 100, 40, "D10-C4")
    DECIMAL_3_DIGITS = (FermatClockLaw.EULER_TRIPLING, 1000, 400, "D10-C20")
    DECIMAL_4_DIGITS = (FermatClockLaw.EULER_TRIPLING, 10000, 4000, "D10-C100")
    QUINARY_CUBED = (FermatClockLaw.EULER_TRIPLING, 125, 100, "Q5-125")
    SEPTENARY_SQUARED = (FermatClockLaw.EULER_TRIPLING, 49, 42, "Q7-49")
    MOD_99 = (FermatClockLaw.SOURCE_CYCLOTOMIC, 99, None, "D10-99")
    MOD_198 = (FermatClockLaw.SOURCE_CYCLOTOMIC, 198, None, "D10-198")
    MOD_9900 = (FermatClockLaw.SOURCE_CYCLOTOMIC, 9900, None, "D10-9900")

    @property
    def law(self) -> FermatClockLaw:
        return self._value_[0]

    @property
    def modulus(self) -> int:
        return self._value_[1]

    @property
    def exponent_period(self) -> int | None:
        return self._value_[2]

    @property
    def display_label(self) -> str:
        return self._value_[3]


_LEADING_PREFIXES = ((1, 3, 9), (1, 3), (1, 4), (1, 5), (2, 6), (2, 7), (2, 8))


class FermatRadialMode(Enum):
    EXACT_SMALL_ROOT = "exact-small-root"
    LEADING_PREFIX = "leading-prefix"
    SOURCE_ROOT = "source-root"
    UNRESOLVED = "unresolved"


class FermatSourceKind(Enum):
    """Authenticated source constructor class for macro payload snapshots."""

    SIGNED_TRIPLING_ACTION = "signed-tripling-action"
    ALGEBRAIC_ROOT = "algebraic-root"


def _digits(value: int) -> tuple[int, ...]:
    return tuple(int(char) for char in str(value))


def _totient_prime_power_base(base: int, places: int) -> int:
    """Certified Euler period bound for the supported coprime 3X radices."""
    if type(places) is not int or not 1 <= places <= 257:
        raise ValueError("macro clock depth outside admitted range")
    if base == 2:
        return 1 << (places - 1)
    if base == 5:
        return cast(int, 4 * 5 ** (places - 1))
    if base == 7:
        return cast(int, 6 * 7 ** (places - 1))
    if base == 10:
        return cast(int, 4 * 10 ** (places - 1))
    raise ValueError("unsupported Fermat macro clock base")


def exact_three_power_residue(level: int, modulus: int, period: int) -> int:
    """3**(2**level) mod m, with certified 3**period=1 mod m."""
    if (
        type(level) is not int
        or level < 0
        or level > 65535
        or type(modulus) is not int
        or modulus < 2
        or type(period) is not int
        or period < 1
        or gcd(3, modulus) != 1
        or pow(3, period, modulus) != 1
    ):
        raise ValueError("unproved or invalid modular source clock")
    return pow(3, pow(2, level, period), modulus)


@dataclass(frozen=True, slots=True, weakref_slot=True)
class FermatAlgebraicRoot:
    """Exact exponent-circuit source when a radial proof exceeds its budget.

    A low modular state derived from this root is exact even when the
    high-boundary source language cannot be constructed. This is NOT an
    invented source cylinder or a proof of upper carry ingress.
    """

    index: int
    level: int
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def issuer_payload(self) -> tuple[object, ...]:
        return (self.index, self.level)

    @property
    def producer_verified(self) -> bool:
        return harmonic_verified(self, self.issuer_payload(), issuer=_ROOT_ISSUER)


_ROOT_ISSUER = new_harmonic_issuer(FermatAlgebraicRoot)


def issue_algebraic_root(index: int, level: int) -> FermatAlgebraicRoot:
    if (
        type(index) is not int
        or not 0 <= index <= 16
        or type(level) is not int
        or level != (1 << index) - 1
    ):
        raise ValueError("Fermat symbolic low root belongs to another candidate")
    root = FermatAlgebraicRoot(index, level)
    issue_harmonic(root, root.issuer_payload(), issuer=_ROOT_ISSUER)
    return root


@dataclass(frozen=True, slots=True)
class NamedFermatClock:
    identity: FermatClockId
    source_residue: int

    @property
    def name(self) -> str:
        """Human-readable label; never participates in a clock identity."""
        return self.identity.display_label

    @property
    def modulus(self) -> int:
        return self.identity.modulus

    @property
    def exponent_period(self) -> int | None:
        return self.identity.exponent_period

    def issuer_payload(self) -> tuple[object, ...]:
        return self.identity, self.source_residue

    def at(self, offset: int) -> int:
        if type(offset) is not int or offset < 0:
            raise ValueError("physical offset must be nonnegative")
        return self.source_residue * pow(3, offset, self.modulus) % self.modulus


@dataclass(frozen=True, slots=True)
class FermatRadialPort:
    """A guaranteed leading-word cylinder after a physical tripling offset.

    An unknown interior remains an interval of decimal integers.  A radial
    word is published only when BOTH extremal prefixes agree.  The interval
    method never evaluates the giant original 3**(2**level) integer.
    """

    tick: int
    exact_width: int | None
    guaranteed_word: str | None
    guaranteed_places: int
    family_prefix: tuple[int, ...] | None

    @property
    def named_family(self) -> str | None:
        return (
            None
            if self.family_prefix is None
            else "".join(str(digit) for digit in self.family_prefix)
        )


@dataclass(frozen=True, slots=True, weakref_slot=True)
class FermatBorderMacro:
    """One root-guarded macro program with exact low and guarded high ports.

    Low modular clocks advance at arbitrary physical offsets; the high radial
    word and dyadic pivot remain assertions about the *source root only*.
    """

    source: SourceWeightedTriplingAction | FermatAlgebraicRoot = field(repr=False)
    clocks: tuple[NamedFermatClock, ...]
    root_radial_prefix: int | None
    root_radial_places: int
    radial_guard: tuple[int, int, tuple[int, ...]]
    binary_gap: int
    binary_lte_verified: bool
    radial_mode: FermatRadialMode
    pivot_xor: tuple[int, int, tuple[tuple[int, int, int], ...]] | None
    root_residue9900: int
    radial_guard_verified: bool
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def issuer_payload(self) -> tuple[object, ...]:
        if type(self.source) is SourceWeightedTriplingAction:
            source_kind = FermatSourceKind.SIGNED_TRIPLING_ACTION
        elif type(self.source) is FermatAlgebraicRoot:
            source_kind = FermatSourceKind.ALGEBRAIC_ROOT
        else:
            raise TypeError("macro payload has an unsupported source owner")
        return (
            # Bind the complete signed source authority, not just its public
            # exponent/index. A same-index algebraic root has different radial
            # semantics and cannot inherit this macro's guards.
            source_kind,
            self.source.issuer_payload(),
            tuple(clock.issuer_payload() for clock in self.clocks),
            self.root_radial_prefix,
            self.root_radial_places,
            self.radial_guard,
            self.binary_gap,
            self.binary_lte_verified,
            self.radial_mode,
            self.pivot_xor,
            self.root_residue9900,
            self.radial_guard_verified,
        )

    @property
    def root_radial_word(self) -> str | None:
        """Decimal rendering of an issued root prefix, for packets only."""
        return None if self.root_radial_prefix is None else str(self.root_radial_prefix)

    @property
    def names(self) -> tuple[str, ...]:
        """Display labels derived from typed clocks and root guard metadata."""
        labels = [clock.name for clock in self.clocks]
        if self.binary_lte_verified:
            labels.insert(0, "B2-LTE")
        labels.append(
            {
                FermatRadialMode.EXACT_SMALL_ROOT: "R3-EXACT-SMALL-ROOT",
                FermatRadialMode.LEADING_PREFIX: "R3-LEAD",
                FermatRadialMode.SOURCE_ROOT: "R3-SOURCE-GUARD",
                FermatRadialMode.UNRESOLVED: "R3-UNRESOLVED",
            }[self.radial_mode]
        )
        if self.pivot_xor is not None:
            labels.append("PIVOT-XOR")
        return tuple(labels)

    @property
    def producer_verified(self) -> bool:
        return self.source.producer_verified and harmonic_verified(
            self, self.issuer_payload(), issuer=_MACRO_ISSUER
        )

    def clock(self, identity: FermatClockId) -> NamedFermatClock:
        if not self.producer_verified:
            raise ValueError("unissued Fermat border macro")
        if type(identity) is not FermatClockId:
            raise TypeError("Fermat clock lookup requires its typed identity")
        for item in self.clocks:
            if item.identity == identity:
                return item
        raise KeyError(identity)

    def radial_at(self, offset: int) -> FermatRadialPort:
        """Conservatively transport a certified high border through 3**offset.

        If the source has leading P of h places and U unknown lower places,
        then P*10**U <= X < (P+1)*10**U, so

            P*3**t <= (3**t*X)/10**U < (P+1)*3**t.

        Width and each emitted leading digit must agree at BOTH interval
        endpoints.  This propagates future radial guards without inventing
        the missing middle, digitizing the huge source, or treating a
        dyadic-periodic suffix as a physical-periodic leading word.
        """
        if (
            not self.producer_verified
            or type(offset) is not int
            or not 0 <= offset <= 4096
        ):
            raise ValueError("unissued or unbounded radial source offset")
        if not self.radial_guard_verified:
            return FermatRadialPort(offset, None, None, 0, None)
        if type(self.source) is SourceWeightedTriplingAction:
            source = self.source
            cylinder = source.origin.bilateral.decimal
            root_prefix = cylinder.source_top
            root_places = cylinder.high_places
            root_width = cylinder.source_digits
            exact = False
        else:
            if self.root_radial_prefix is None:
                raise ArithmeticError("exact root radial value was not published")
            root_prefix = self.root_radial_prefix
            root_places = self.root_radial_places
            root_width = root_places
            exact = True
        if offset == 0:
            word, width = str(root_prefix), root_width
        else:
            scale = pow(3, offset)
            left = str(root_prefix * scale)
            right = str((root_prefix if exact else root_prefix + 1) * scale)
            if len(left) != len(right):
                return FermatRadialPort(offset, None, None, 0, None)
            width = root_width - root_places + len(left)
            candidate: str | None = None
            for digits in range(root_places, 0, -1):
                if left[:digits] == right[:digits]:
                    candidate = left[:digits]
                    break
            if candidate is None:
                return FermatRadialPort(offset, width, None, 0, None)
            word = candidate
        family = next(
            (
                prefix
                for prefix in sorted(_LEADING_PREFIXES, key=len, reverse=True)
                if tuple(int(char) for char in word[: len(prefix)]) == prefix
            ),
            None,
        )
        return FermatRadialPort(offset, width, word, len(word), family)

    def puncture(self, offset: int) -> tuple[tuple[FermatClockId, int], ...]:
        """All modular source residues at ONE physical port, from one root."""
        if not self.producer_verified:
            raise ValueError("unissued Fermat border macro")
        physical = (
            FermatOuterCyclotomicClock.from_level(self.source.level, offset)
            if self.source.level >= 1
            else None
        )
        output = tuple((clock.identity, clock.at(offset)) for clock in self.clocks)
        checked = dict(output)
        if (
            (
                physical is not None
                and (
                    checked[FermatClockId.DECIMAL_2_DIGITS] != physical.residue100
                    or checked[FermatClockId.MOD_99] != physical.residue99
                    or checked[FermatClockId.MOD_198] != physical.residue198
                    or checked[FermatClockId.MOD_9900] != physical.residue9900
                )
            )
            or checked[FermatClockId.MOD_9900] % FermatClockId.DECIMAL_2_DIGITS.modulus
            != checked[FermatClockId.DECIMAL_2_DIGITS]
            or checked[FermatClockId.MOD_9900] % FermatClockId.MOD_99.modulus
            != checked[FermatClockId.MOD_99]
            or checked[FermatClockId.MOD_9900] % FermatClockId.MOD_198.modulus
            != checked[FermatClockId.MOD_198]
            or checked[FermatClockId.MOD_198] % FermatClockId.MOD_99.modulus
            != checked[FermatClockId.MOD_99]
            or checked[FermatClockId.DECIMAL_3_DIGITS]
            % FermatClockId.QUINARY_CUBED.modulus
            != checked[FermatClockId.QUINARY_CUBED]
            or checked[FermatClockId.DECIMAL_4_DIGITS]
            % FermatClockId.DECIMAL_3_DIGITS.modulus
            != checked[FermatClockId.DECIMAL_3_DIGITS]
            or checked[FermatClockId.DECIMAL_4_DIGITS]
            % FermatClockId.DECIMAL_2_DIGITS.modulus
            != checked[FermatClockId.DECIMAL_2_DIGITS]
        ):
            raise ArithmeticError("physical clock / modular port join failed")
        return output


_MACRO_ISSUER = new_harmonic_issuer(FermatBorderMacro)


def issue_fermat_border_macro(
    source: SourceWeightedTriplingAction | FermatAlgebraicRoot,
) -> FermatBorderMacro:
    """Select all locally provable families BEFORE compiling a temporal matrix.

    If a radial source exceeds its construction budget, an independently
    issued algebraic source keeps low constraints but marks the high guard
    unresolved. The 5-adic clock is checked against the decimal bank whenever
    that bank is available.
    Q7 is an additional exact small-modulus source constraint, not an inference
    from the mod-99/100 observation. Unknown high and signed middle branches
    are never replaced with a sampled digit.
    """
    if (
        type(source) not in (SourceWeightedTriplingAction, FermatAlgebraicRoot)
        or not source.producer_verified
    ):
        raise TypeError("macro registry requires an issued Fermat root")
    signed_source = source if type(source) is SourceWeightedTriplingAction else None
    signed = signed_source is not None
    bank = (
        signed_source.origin.decimal_phase_bank if signed_source is not None else None
    )
    binary = (
        signed_source.origin.binary_phase_bank if signed_source is not None else None
    )
    if signed_source is not None and (bank is None or binary is None or bank.depth < 1):
        raise ValueError("signed macro registry needs joint phase banks")
    level = source.level
    physical = FermatOuterCyclotomicClock.from_level(level) if level >= 1 else None
    clocks: list[NamedFermatClock] = []
    for identity in FermatClockId:
        modulus = identity.modulus
        # The 9-primary part is nonunit for 3. Use the physical source
        # clock, which retains the transient and provides the 198 odd lift.
        if identity.law is FermatClockLaw.SOURCE_CYCLOTOMIC:
            if physical is None:
                value = pow(3, 1 << level, modulus)
            else:
                value = {
                    FermatClockId.MOD_99: physical.residue99,
                    FermatClockId.MOD_198: physical.residue198,
                    FermatClockId.MOD_9900: physical.residue9900,
                }[identity]
            clocks.append(NamedFermatClock(identity, value))
            continue
        if identity.law is not FermatClockLaw.EULER_TRIPLING:
            raise ArithmeticError("unrecognized Fermat clock law")
        period = identity.exponent_period
        if period is None:
            raise ArithmeticError("Euler clock has no certified exponent period")
        value = exact_three_power_residue(level, modulus, period)
        clocks.append(NamedFermatClock(identity, value))
    index = {clock.identity: clock.source_residue for clock in clocks}
    if signed_source is not None:
        assert bank is not None and binary is not None
        if (
            (
                physical is not None
                and (
                    index[FermatClockId.DECIMAL_2_DIGITS] != physical.residue100
                    or index[FermatClockId.MOD_99] != physical.residue99
                    or index[FermatClockId.MOD_198] != physical.residue198
                    or index[FermatClockId.MOD_9900] != physical.residue9900
                )
            )
            or index[FermatClockId.DECIMAL_4_DIGITS] % (10 ** min(4, bank.depth))
            != bank.source_prefix % (10 ** min(4, bank.depth))
            or index[FermatClockId.QUINARY_CUBED] % (5 ** min(3, bank.depth))
            != bank.source_prefix % (5 ** min(3, bank.depth))
        ):
            raise ArithmeticError("source-issued modular clocks disagree")
        if binary.depth >= level + 3:
            mask = (1 << (level + 3)) - 1
            if binary.source_prefix & mask != 1 + (1 << (level + 2)):
                raise ArithmeticError("LTE low binary pivot contradicts source bank")
        elif binary.source_prefix != 1 and binary.depth <= level + 2:
            raise ArithmeticError("2-adic root prefix contradicts source bank")
        decimal_border = signed_source.origin.bilateral.decimal
        leading = str(decimal_border.source_top)
        high = (
            decimal_border.source_top,
            decimal_border.high_places,
            tuple(signed_source.origin.decimal_middle.possible_high_ingress),
        )
        if not high[2]:
            raise ArithmeticError("radial guard has no admitted high carry ingress")
    elif level <= 1:
        leading = str(pow(3, 1 << level))
        high = (int(leading), len(leading), (0,))
    else:
        leading = None
        high = (0, 0, (0, 1, 2))
    root_prefix: int | None
    root_places: int
    if not signed and level <= 1:
        if leading is None:
            raise ArithmeticError("small exact Fermat root lost its decimal digits")
        root_prefix = int(leading)
        root_places = len(leading)
        radial_mode = FermatRadialMode.EXACT_SMALL_ROOT
    elif (
        signed_source is not None
        and leading is not None
        and any(
            _digits(int(leading))[: len(prefix)] == prefix
            for prefix in _LEADING_PREFIXES
        )
    ):
        root_prefix = high[0]
        root_places = high[1]
        radial_mode = FermatRadialMode.LEADING_PREFIX
    elif signed_source is not None:
        root_prefix = high[0]
        root_places = high[1]
        radial_mode = FermatRadialMode.SOURCE_ROOT
    else:
        root_prefix = None
        root_places = 0
        radial_mode = FermatRadialMode.UNRESOLVED
    pivot = None
    if level >= 1 and 2 * level + 11 <= MAX_PIVOT_PRECISION:
        window = moving_unit_innovation_window(level, 8)
        # Port puncture at the moving 2-adic pivot: independently recover
        # the actual 3**(2**level) low word from its modular exponent, and
        # insist that the theorem-derived unit bits describe that word.
        precision = 2 * level + 11
        source_prefix = exact_three_power_residue(
            level, 1 << precision, 1 << (precision - 1)
        )
        source_unit = (source_prefix - 1) >> (level + 2)
        if ((source_unit >> window.unit_offset) & 255) != window.current_bits:
            raise ArithmeticError("dyadic XOR source pivot is not a root port")
        pivot = (
            window.unit_offset,
            window.xor_mask,
            tuple((r.unit_start, r.length, r.expected_bit) for r in window.runs),
        )
    macro = FermatBorderMacro(
        source=source,
        clocks=tuple(clocks),
        root_radial_prefix=root_prefix,
        root_radial_places=root_places,
        radial_guard=high,
        binary_gap=level + 2,
        binary_lte_verified=level >= 1,
        radial_mode=radial_mode,
        pivot_xor=pivot,
        root_residue9900=(
            physical.residue9900
            if physical is not None
            else pow(3, 1 << level, FermatClockId.MOD_9900.modulus)
        ),
        radial_guard_verified=signed or level <= 1,
    )
    issue_harmonic(macro, macro.issuer_payload(), issuer=_MACRO_ISSUER)
    if (
        not macro.producer_verified
        or dict(macro.puncture(0))[FermatClockId.DECIMAL_4_DIGITS]
        != index[FermatClockId.DECIMAL_4_DIGITS]
    ):
        raise ArithmeticError("Fermat registry could not certify source ports")
    return macro


__all__ = (
    "FermatAlgebraicRoot",
    "FermatBorderMacro",
    "FermatClockId",
    "FermatClockLaw",
    "FermatRadialMode",
    "FermatRadialPort",
    "NamedFermatClock",
    "_totient_prime_power_base",
    "exact_three_power_residue",
    "issue_algebraic_root",
    "issue_fermat_border_macro",
)
