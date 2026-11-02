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

from collections.abc import Callable
from contextlib import AbstractContextManager, nullcontext
from dataclasses import dataclass
from typing import Literal, Protocol, cast

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.skew_moments import SkewMoment
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    arithmetic_fields as _arithmetic_field_keys,
)
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)
from number_compiler.sequences.double_reverse._temporal_bank_authority import (
    SourceAuthorizedRecord,
    issue_source_record,
    require_source_arena,
    validate_source_record,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    PHYSICAL_GROWTH_CYCLES,
    DoubleReverseTemporalHashlife,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    DoubleReverseSourcePrefix,
    UncertifiedPointedStencilError,
)

# One is a physical generation, not a T**2 frame.  These four letters follow
# from the *certified* 1144/2288 edge signatures and growth_ports(), not from
# an independently guessed interior carry.
_PHYSICAL_RETURN_TICKS = 4


def _growth_moment(word: tuple[int, ...]) -> SkewMoment:
    """Convert an admitted physical growth word into the shared skew monoid."""
    if any(type(growth) is not int or growth not in (0, 1) for growth in word):
        raise ValueError("physical growth letters must be bits")
    steps = len(word)
    return SkewMoment(
        steps,
        sum(word),
        sum((steps - index - 1) * growth for index, growth in enumerate(word)),
    )


def certified_width_moments(phase: int, steps: int) -> SkewMoment:
    """Binary-powered growth and quadratic skew for a certified border phase."""
    if type(phase) is not int or phase not in range(4):
        raise ValueError("an authenticated edge phase is required")
    if type(steps) is not int or steps < 0:
        raise ValueError("temporal duration must be nonnegative")
    word = PHYSICAL_GROWTH_CYCLES[phase]
    repeat, remainder = divmod(steps, _PHYSICAL_RETURN_TICKS)
    return (
        _growth_moment(word).power_formal(repeat).then(_growth_moment(word[:remainder]))
    )


@dataclass(frozen=True, slots=True)
class SLPResidues:
    """A concatenation monoid with two numerical residues, no digit expansion."""

    length: int
    modulo99: int
    modulo198: int

    def then(self, later: SLPResidues) -> SLPResidues:
        return SLPResidues(
            self.length + later.length,
            (self.modulo99 * pow(10, later.length, 99) + later.modulo99) % 99,
            (self.modulo198 * pow(10, later.length, 198) + later.modulo198) % 198,
        )

    def power(self, times: int) -> SLPResidues:
        if type(times) is not int or times < 0:
            raise ValueError("negative SLP repeat count")
        return binary_power(
            self,
            times,
            identity=SLPResidues(0, 0, 0),
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
            empty_value=SLPResidues(0, 0, 0),
            terminal_value=lambda d: SLPResidues(1, d % 99, d % 198),
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
            max_prefix=min(engine.prefix_limit, generation),
            require_even_remainder=False,
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
        ledger=ledger,
    )
    return prefix, issue_source_record(action, arena, root, source_generation=prefix)


@dataclass(frozen=True, slots=True)
class CertifiedResidueTemporalAction(SourceAuthorizedRecord):
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


@dataclass(frozen=True, slots=True)
class ResidueReturnOrbit:
    """Exact lasso for one residue projection sampled every four T steps."""

    modulus: int
    initial_residue: int
    multiplier_per_return: int
    transient_returns: int
    period_returns: int
    transient_ticks_upper_bound: int
    period_ticks: int
    width_drift_over_period: int


ResiduePeriodScope = Literal["certified border phase and mod-99/mod-198 residues only"]
_RESIDUE_PERIOD_SCOPE: ResiduePeriodScope = (
    "certified border phase and mod-99/mod-198 residues only"
)


@dataclass(frozen=True, slots=True)
class ProjectedResidueTemporalQuotient(SourceAuthorizedRecord):
    """Source-bound projected return; it never claims width or digit periodicity."""

    source_action: CertifiedResidueTemporalAction
    source_generation: int
    target_generation: int
    target_phase: int
    target_width: int
    width_growth_per_four_ticks: int
    modulo99: ResidueReturnOrbit
    modulo198: ResidueReturnOrbit
    return_states_visited: int
    scope: ResiduePeriodScope

    def validate_source_authority(self) -> None:
        """Validate this descriptor and the exact source action it projects."""
        authority = validate_source_record(self)
        self.source_action.validate_source_authority()
        action_authority = validate_source_record(self.source_action)
        if (
            authority.arena is not action_authority.arena
            or authority.root != action_authority.root
            or authority.source_generation != action_authority.source_generation
            or self.source_generation != authority.source_generation
            or self.target_generation
            != self.source_generation + self.source_action.duration
            or self.target_phase
            != (self.source_action.phase + self.source_action.duration) % 4
            or self.target_width != self.source_action.width_out
            or self.scope != _RESIDUE_PERIOD_SCOPE
        ):
            raise ValueError("projected residue return authority is inconsistent")

    def packet(self) -> dict[str, object]:
        """Return only the finite border/residue projection and affine width drift."""
        self.validate_source_authority()
        return {
            "scope": self.scope,
            "source_generation": self.source_generation,
            "target_generation": self.target_generation,
            "target_phase": self.target_phase,
            "target_width": self.target_width,
            "physical_ticks_per_return": _PHYSICAL_RETURN_TICKS,
            "width_growth_per_four_ticks": self.width_growth_per_four_ticks,
            "width_is_periodic": False,
            "modulo99": {
                **_residue_return_packet(self.modulo99),
                "cycle_width_drift": self.modulo99.width_drift_over_period,
            },
            "modulo198": {
                **_residue_return_packet(self.modulo198),
                "cycle_width_drift": self.modulo198.width_drift_over_period,
            },
            "return_states_visited": self.return_states_visited,
            "full_digit_word_authority": False,
        }


def _residue_return_packet(orbit: ResidueReturnOrbit) -> dict[str, int]:
    return {
        "initial_residue": orbit.initial_residue,
        "multiplier_per_return": orbit.multiplier_per_return,
        "transient_returns": orbit.transient_returns,
        "period_returns": orbit.period_returns,
        "transient_ticks_upper_bound": orbit.transient_ticks_upper_bound,
        "period_ticks": orbit.period_ticks,
    }


def projected_residue_return_lassos(
    initial_mod198: int,
    multiplier_mod99: int,
    multiplier_mod198: int,
    *,
    on_state_visit: Callable[[int], None] | None = None,
) -> tuple[ResidueReturnOrbit, ResidueReturnOrbit, int]:
    """Find exact mod-99/mod-198 lassos in one at-most-198-state walk.

    The callback runs before each state is inspected or its successor is
    computed, so ledger work accounting includes partial walks on failure.
    """
    if (
        type(initial_mod198) is not int
        or not 0 <= initial_mod198 < 198
        or type(multiplier_mod99) is not int
        or not 0 <= multiplier_mod99 < 99
        or type(multiplier_mod198) is not int
        or not 0 <= multiplier_mod198 < 198
        or multiplier_mod198 % 99 != multiplier_mod99
    ):
        raise ValueError("projected residue return has incompatible modular ports")

    first_mod198 = [-1] * 198
    mod99_lasso: tuple[int, int] | None = None
    state = initial_mod198
    visits = 0
    while first_mod198[state] < 0:
        if on_state_visit is not None:
            on_state_visit(state)
        first_mod198[state] = visits
        projected99 = state % 99
        opposite_mod198 = projected99 + 99 if state == projected99 else projected99
        opposite_first = first_mod198[opposite_mod198]
        if opposite_first >= 0 and mod99_lasso is None:
            mod99_lasso = (opposite_first, visits - opposite_first)
        visits += 1
        state = state * multiplier_mod198 % 198

    transient198 = first_mod198[state]
    period198 = visits - transient198
    if mod99_lasso is None:
        mod99_lasso = (transient198, period198)
    transient99, period99 = mod99_lasso
    mod99 = ResidueReturnOrbit(
        99,
        initial_mod198 % 99,
        multiplier_mod99,
        transient99,
        period99,
        _PHYSICAL_RETURN_TICKS * transient99,
        _PHYSICAL_RETURN_TICKS * period99,
        2 * period99,
    )
    mod198 = ResidueReturnOrbit(
        198,
        initial_mod198,
        multiplier_mod198,
        transient198,
        period198,
        _PHYSICAL_RETURN_TICKS * transient198,
        _PHYSICAL_RETURN_TICKS * period198,
        2 * period198,
    )
    return mod99, mod198, visits


def projected_residue_temporal_quotient(
    action: CertifiedResidueTemporalAction,
    *,
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
) -> ProjectedResidueTemporalQuotient:
    """Power the certified border/residue projection, never the full integer.

    A four-physical-step return has a source-phase-derived width increment of
    two. Its modular multiplier is evaluated by ``certified_residue_action``.
    Since each partial return's exponent is positive, adding two to its width
    shifts that exponent by an even number; powers of ten repeat every two
    positive exponents modulo 99 and 198. The return lasso is scoped to border
    phase and residues. Width keeps its affine drift and the interior digit
    word remains unspecified.
    """
    if type(action) is not CertifiedResidueTemporalAction:
        raise TypeError("projected residue return needs its exact action record")
    action.validate_source_authority()
    if (ledger is None) != (scratch_owner is None):
        raise ValueError("projected return resource handles are incomplete")
    authority = validate_source_record(action)
    arena = require_source_arena(authority)
    target_phase = (action.phase + action.duration) % 4
    target_width = action.width_out
    workspace: AbstractContextManager[None]
    if ledger is None:
        if scratch_owner is not None:
            raise ValueError("projected return scratch owner has no ledger")
        workspace = nullcontext()
    else:
        if scratch_owner is None:
            raise ValueError("projected return needs its ledger scratch owner")
        workspace = ledger.reservation(scratch_owner, entries=198, nodes=198)

    with workspace:
        if ledger is not None:
            _charge_residue_arithmetic(ledger, (target_phase, _PHYSICAL_RETURN_TICKS))
        moments = certified_width_moments(target_phase, _PHYSICAL_RETURN_TICKS)
        if (
            moments.duration != _PHYSICAL_RETURN_TICKS
            or moments.U != 2
            or target_width < 5
        ):
            raise AssertionError("certified four-step width return changed")

        if action.target_mod198 % 99 != action.target_mod99:
            raise AssertionError("residue action lost its mod-99 projection")
        block = certified_residue_action(
            phase=target_phase,
            width=target_width,
            duration=_PHYSICAL_RETURN_TICKS,
            source_mod99=action.target_mod99,
            source_mod198=action.target_mod198,
            ledger=ledger,
        )
        on_visit: Callable[[int], None] | None
        if ledger is None:
            on_visit = None
        else:

            def charge_visit(state: int) -> None:
                _charge_residue_arithmetic(
                    ledger,
                    (state, 99, state, block.multiplier_mod198, 198),
                )

            on_visit = charge_visit

        modulo99, modulo198, visits = projected_residue_return_lassos(
            action.target_mod198,
            block.multiplier_mod99,
            block.multiplier_mod198,
            on_state_visit=on_visit,
        )
    record = ProjectedResidueTemporalQuotient(
        action,
        authority.source_generation,
        authority.source_generation + action.duration,
        target_phase,
        target_width,
        moments.U,
        modulo99,
        modulo198,
        visits,
        _RESIDUE_PERIOD_SCOPE,
    )
    issue_source_record(
        record,
        arena,
        authority.root,
        parent=authority,
        source_generation=authority.source_generation,
    )
    record.validate_source_authority()
    return record


def certified_residue_action(
    *,
    phase: int,
    width: int,
    duration: int,
    source_mod99: int,
    source_mod198: int,
    ledger: ResourceLedger | None = None,
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
    if ledger is not None:
        _charge_residue_arithmetic(ledger, (phase, duration))
    moments = certified_width_moments(phase, duration)
    if ledger is not None:
        _charge_residue_arithmetic(ledger, (duration, width, moments.V))
    exponent = moments.duration * (width - 1) + moments.V
    # This is the exact width-dependent temporal action, not an endpoint
    # arithmetic check.  10**2 = 1 modulo 99; the modulo-198 formula retains
    # the doubled reversal congruence for all positive durations.
    power2_99 = _residue_power(2, duration, 99, ledger)
    power10_99 = _residue_power(10, exponent, 99, ledger)
    mul99 = _residue_product_mod(power2_99, power10_99, 99, ledger)
    power2_198 = _residue_power(2, duration, 198, ledger)
    power10_198 = _residue_power(10, exponent, 198, ledger)
    mul198 = _residue_product_mod(power2_198, power10_198, 198, ledger)
    target_mod99 = _residue_product_mod(source_mod99, mul99, 99, ledger)
    target_mod198 = _residue_product_mod(source_mod198, mul198, 198, ledger)
    return CertifiedResidueTemporalAction(
        phase,
        width,
        duration,
        moments.U,
        moments.V,
        width + moments.U,
        mul99,
        mul198,
        source_mod99,
        source_mod198,
        target_mod99,
        target_mod198,
    )


def _charge_residue_arithmetic(
    ledger: ResourceLedger, operands: tuple[int, ...]
) -> None:
    """Charge one exact modular arithmetic unit before it is performed."""
    ledger.bump(_arithmetic_field_keys.GROWTH_ARITHMETIC_WORK)
    ledger.bump(
        _arithmetic_field_keys.GROWTH_ARITHMETIC_OPERAND_BITS,
        sum(value.bit_length() for value in operands),
    )


def _residue_power(
    base: int, exponent: int, modulus: int, ledger: ResourceLedger | None
) -> int:
    if ledger is not None:
        _charge_residue_arithmetic(ledger, (base, exponent, modulus))
    return pow(base, exponent, modulus)


def _residue_product_mod(
    first: int, second: int, modulus: int, ledger: ResourceLedger | None
) -> int:
    if ledger is not None:
        _charge_residue_arithmetic(ledger, (first, second, modulus))
    return first * second % modulus


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
