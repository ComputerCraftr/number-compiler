"""Predictive temporal quotient of decimal reverse-double modulo 99/198.

Unlike digit or Walsh projections made after the endpoint, this quotient acts
on the authenticated *source*.  Reversal is an anti-automorphism of decimal
words and 10**2 = 1 (mod 99).  Consequently, for canonical width w,

    T(x) = 2*reverse10(x) = 2*10**(w-1)*x  (mod 99).

On the certified four-phase noncontracting cylinder the physical width-growth
word has period four.  Its skew moments compose exactly, providing a finite
state action on (width mod 2, X mod 99).  This says nothing about the complete
integer or GT/EQ/LT interior.  There is NO binary-to-decimal carry correction.

The modulo-198 projection follows because doubling annihilates the factor
of two in 2*(reverse10(x) - 10**(w-1)*x), which is divisible by 198.
"""

from __future__ import annotations

from contextlib import nullcontext
from dataclasses import dataclass
from typing import Protocol, cast

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)
from number_compiler.sequences.double_reverse._temporal_bank_authority import (
    _SourceAuthorizedRecord,
    issue_source_record,
    validate_source_record,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    DoubleReverseTemporalHashlife,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    DoubleReverseSourcePrefix,
    UncertifiedPointedStencilError,
)

# One is a physical generation, not a T**2 frame.  These four letters follow
# from the *certified* 1144/2288 edge signatures and growth_ports(), not from
# an independently guessed interior carry.
PHYSICAL_GROWTH_CYCLES: tuple[tuple[int, int, int, int], ...] = (
    (1, 0, 0, 1),
    (0, 0, 1, 1),
    (0, 1, 1, 0),
    (1, 1, 0, 0),
)


@dataclass(frozen=True, slots=True)
class WidthMoments:
    """(duration, width increments, weighted increments) under concatenation."""

    steps: int = 0
    growth: int = 0
    skew: int = 0

    def __post_init__(self) -> None:
        if (
            type(self.steps) is not int
            or type(self.growth) is not int
            or type(self.skew) is not int
            or self.steps < 0
            or self.growth < 0
            or self.skew < 0
        ):
            raise ValueError("invalid physical width-moment action")

    def then(self, later: WidthMoments) -> WidthMoments:
        if not isinstance(later, WidthMoments):
            raise TypeError("width actions must compose with width actions")
        return WidthMoments(
            self.steps + later.steps,
            self.growth + later.growth,
            self.skew + later.skew + later.steps * self.growth,
        )

    def power(self, repeats: int) -> WidthMoments:
        if type(repeats) is not int or repeats < 0:
            raise ValueError("repeat count must be nonnegative")
        return binary_power(
            self,
            repeats,
            identity=WidthMoments(),
            compose=lambda first, second: first.then(second),
        ).value

    @classmethod
    def from_growth(cls, word: tuple[int, ...]) -> WidthMoments:
        if any(type(g) is not int or g not in (0, 1) for g in word):
            raise ValueError("physical growth letters must be bits")
        n = len(word)
        return cls(n, sum(word), sum((n - i - 1) * g for i, g in enumerate(word)))


def certified_width_moments(phase: int, steps: int) -> WidthMoments:
    """Binary-powered growth and quadratic skew for a certified border phase."""
    if type(phase) is not int or phase not in range(4):
        raise ValueError("an authenticated edge phase is required")
    if type(steps) is not int or steps < 0:
        raise ValueError("temporal duration must be nonnegative")
    word = PHYSICAL_GROWTH_CYCLES[phase]
    repeat, remainder = divmod(steps, 4)
    return (
        WidthMoments.from_growth(word)
        .power(repeat)
        .then(WidthMoments.from_growth(word[:remainder]))
    )


@dataclass(frozen=True, slots=True)
class _SLPResidues:
    """A concatenation monoid with two numerical residues, no digit expansion."""

    length: int
    modulo99: int
    modulo198: int

    def then(self, later: _SLPResidues) -> _SLPResidues:
        return _SLPResidues(
            self.length + later.length,
            (self.modulo99 * pow(10, later.length, 99) + later.modulo99) % 99,
            (self.modulo198 * pow(10, later.length, 198) + later.modulo198) % 198,
        )

    def power(self, times: int) -> _SLPResidues:
        if type(times) is not int or times < 0:
            raise ValueError("negative SLP repeat count")
        return binary_power(
            self,
            times,
            identity=_SLPResidues(0, 0, 0),
            compose=lambda first, second: first.then(second),
        ).value


def decimal_residues_from_slp(
    arena: SLPArena,
    root: int,
    *,
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
) -> tuple[int, int]:
    """Source-only O(SLP DAG size + log repeat count) mod-99/mod-198 fold."""
    if (ledger is None) != (scratch_owner is None):
        raise ValueError("residue fold resource handles are incomplete")
    bound = len(arena.nodes)
    workspace = (
        nullcontext()
        if ledger is None
        else ledger.reservation(
            cast(int, scratch_owner), entries=4 * (bound + 1), nodes=12 * (bound + 1)
        )
    )
    with workspace:
        values = fold_slp_dag(
            arena,
            root,
            empty_value=_SLPResidues(0, 0, 0),
            terminal_value=lambda d: _SLPResidues(1, d % 99, d % 198),
            concatenate=lambda a, b: a.then(b),
            repeat=lambda a, count: a.power(count),
            on_reduce=(
                None
                if ledger is None
                else lambda _node: ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_GUARD_NODES
                )
            ),
        )
        result = (values[root].modulo99, values[root].modulo198)
        del values
    return result


class _SourcePrefixFinder(Protocol):
    def __call__(
        self, *, max_prefix: int, require_even_remainder: bool
    ) -> DoubleReverseSourcePrefix: ...


def source_residue_quotient(
    arena: SLPArena,
    engine: DoubleReverseTemporalHashlife,
    source_root: int,
    generation: int,
    find_prefix: _SourcePrefixFinder,
    *,
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
) -> tuple[int, CertifiedResidueTemporalAction]:
    """Authenticate a source prefix and power only its certified suffix."""
    phase = engine.certify(source_root)
    prefix = 0
    root = source_root
    if phase is None:
        if type(generation) is not int or generation <= 0:
            raise UncertifiedPointedStencilError(
                "no certified 2rev10 residue width clock is available at generation zero"
            )
        entry = find_prefix(
            max_prefix=min(32, generation), require_even_remainder=False
        )
        phase = entry.certified_phase
        if phase is None or entry.physical_steps > generation:
            raise UncertifiedPointedStencilError(
                "no source-authorized certified residue prefix was found"
            )
        prefix = entry.physical_steps
        root = engine.root_of(entry.target)
    source_mod99, source_mod198 = decimal_residues_from_slp(
        arena, root, ledger=ledger, scratch_owner=scratch_owner
    )
    action = certified_residue_action(
        phase=phase,
        width=arena.nodes[root].length,
        duration=generation - prefix,
        source_mod99=source_mod99,
        source_mod198=source_mod198,
    )
    return prefix, issue_source_record(action, arena, root, source_generation=prefix)


@dataclass(frozen=True, slots=True)
class CertifiedResidueTemporalAction(_SourceAuthorizedRecord):
    """Closed predictive modulus-99/198 action, NOT a whole-integer closed form."""

    phase: int
    width_in: int
    duration: int
    growth: int
    skew: int
    width_out: int
    multiplier_mod99: int
    multiplier_mod198: int
    source_mod99: int
    source_mod198: int
    target_mod99: int
    target_mod198: int

    @property
    def four_step_return(self) -> bool:
        return self.duration % 4 == 0

    def validate_source_authority(self) -> None:
        """Reject a forged or mutated source residue packet before readout."""
        validate_source_record(self)


def certified_residue_action(
    *,
    phase: int,
    width: int,
    duration: int,
    source_mod99: int,
    source_mod198: int,
) -> CertifiedResidueTemporalAction:
    """Power only the finite four-phase width clock and modular reversal action.

    The caller must authenticate the actual source as belonging to the
    noncontracting 2rev10 cylinder.  Otherwise the supplied phase is not
    authority to predict its width tape.
    """
    if type(width) is not int or width < 1:
        raise ValueError("source width must be positive")
    if (
        type(source_mod99) is not int
        or type(source_mod198) is not int
        or not 0 <= source_mod99 < 99
        or not 0 <= source_mod198 < 198
        or source_mod198 % 99 != source_mod99
    ):
        raise ValueError("incompatible source residue ports")
    moments = certified_width_moments(phase, duration)
    exponent = moments.steps * (width - 1) + moments.skew
    # This is the exact width-dependent temporal action, not an endpoint
    # arithmetic check.  10**2 = 1 modulo 99; the modulo-198 formula retains
    # the doubled reversal congruence for all positive durations.
    mul99 = pow(2, duration, 99) * pow(10, exponent, 99) % 99
    mul198 = pow(2, duration, 198) * pow(10, exponent, 198) % 198
    return CertifiedResidueTemporalAction(
        phase,
        width,
        duration,
        moments.growth,
        moments.skew,
        width + moments.growth,
        mul99,
        mul198,
        source_mod99,
        source_mod198,
        source_mod99 * mul99 % 99,
        source_mod198 * mul198 % 198,
    )


def residue_clock_class_count(modulus: int = 99) -> int:
    """Return the exact minimized state count from the closed-form quotient.

    The observable is the current residue, so distinct residues never merge.
    Within one residue, the eight phase/parity clocks merge exactly when the
    residue is divisible by 11; otherwise they remain distinct.
    """
    if type(modulus) is not int or modulus not in (99, 198):
        raise ValueError("only the proved 99/198 scalar quotients are supported")
    multiples = modulus // 11
    return multiples + 8 * (modulus - multiples)


def residue_clock_class_of(
    phase: int, width_parity: int, residue: int, modulus: int = 99
) -> int:
    """Closed-form minimized class ID without constructing/refining the graph."""
    if type(modulus) is not int or modulus not in (99, 198):
        raise ValueError("only the proved 99/198 scalar quotients are supported")
    if (
        type(phase) is not int
        or phase not in range(4)
        or type(width_parity) is not int
        or width_parity not in (0, 1)
        or type(residue) is not int
        or not 0 <= residue < modulus
    ):
        raise ValueError("invalid residue-clock Moore state")
    multiples_below = residue // 11
    if residue % 11 == 0:
        return 8 * residue - 7 * multiples_below
    return 8 * residue - 7 * (multiples_below + 1) + 2 * phase + width_parity


def advance_residue_clock(
    phase: int, width_parity: int, residue: int, modulus: int = 99
) -> tuple[int, int, int]:
    """One physical-step quotient transition, independent of the digit SLP."""
    if modulus not in (99, 198):
        raise ValueError("source-closed scalar quotient is modulo 99 or 198")
    if (
        type(phase) is not int
        or phase not in range(4)
        or type(width_parity) is not int
        or width_parity not in (0, 1)
        or type(residue) is not int
        or not 0 <= residue < modulus
    ):
        raise ValueError("invalid source-issued residue-clock state")
    return (
        (phase + 1) % 4,
        (width_parity + PHYSICAL_GROWTH_CYCLES[0][phase]) % 2,
        (residue * (2 if width_parity else 20)) % modulus,
    )
