"""Source-conditioned, exactly powered mod-198 Laurent accumulator quotient.

This is the *normalised* alternating frame of T(x)=2*reverse10(x):
    u[2j+1]=R(2*R(u[2j])), u[2j+2]=2*u[2j+1].
For the user-defined telescoping sums A (even increments), B (odd increments),
A+B=u, a certified four-physical-generation border cylinder gives

    (u, A, B, 1)' = M_g (u, A, B, 1)  (mod 198)

    M_1 = [[160,0,0,0],[100,1,0,99],[59,0,1,99],[0,0,0,1]]
    M_0 = [[160,0,0,0],[82, 1,0,99],[77,0,1,99],[0,0,0,1]].

The 99 terms come from the parity of the *same* reflected Laurent carry
polynomial. On the source-certified border, if the first mirrored step grows,
C(X) is odd while C(F(X))/10 is even; in the reverse phase C(X)/10 is
even and C(F(X)) is odd. The latter's complete integer value is not assumed
periodic and remains owned by the exact source-word Hashlife engine.

The matrix and its period are unconditional for this *projected* return after
the source's certified entry, not for full digit words or higher-depth jets.
There is no occurrence-derived semantic ID and no repeated endpoint SLP.
"""

from __future__ import annotations

from contextlib import closing
from dataclasses import dataclass
from math import gcd, lcm
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.slp_walks import iter_symbols
from number_compiler.arithmetic.fields.radix import reverse_radix_integer

from ._temporal_bank_authority import validate_source_record
from .source_adapter import decimal_digits_lsd
from .temporal_hashlife import PHYSICAL_GROWTH_CYCLES, edge_phase_of_integer
from .temporal_residue_quotient import (
    CertifiedResidueTemporalAction,
    certified_residue_action,
)

if TYPE_CHECKING:
    from .power import DoubleReverseTerm
    from .temporal_seed_morphism import CertifiedSeedOrbitMorphism

MODULUS = 198
FIRST_JET_MODULUS = 1980
MULTIPLIER = 160


def _primitive_order_160_mod99(residue: int) -> int:
    """Source-independent Moore period: ord of 160 on a mod-99 ideal.

    160 is a unit modulo 99 and 160**30 == 1 (mod 99); these eight
    divisors are the only possible primitive scalar periods.
    """
    modulus = 99 // gcd(99, residue % 99)
    for period in (1, 2, 3, 5, 6, 10, 15, 30):
        if modulus == 1 or pow(MULTIPLIER, period, modulus) == 1:
            return period
    raise AssertionError("mod-99 primitive order exceeded its proven bound 30")


def _geometric_160(repetitions: int, modulus: int) -> int:
    """Exact geometric sum of 160**j, evaluated modulo any given modulus.

    Since 160 = 1 (mod 159), its residue modulo 159*modulus is 1;
    subtraction and integer division by 159 are lossless, even when 159
    is not invertible modulo the requested ring.
    """
    if (
        type(repetitions) is not int
        or repetitions < 0
        or type(modulus) is not int
        or modulus < 1
    ):
        raise ValueError("invalid geometric carry-power ring")
    return ((pow(160, repetitions, 159 * modulus) - 1) // 159) % modulus


def _reverse(value: int) -> int:
    # Only the finitely many initial source-admission steps require this
    # scalar oracle. Powers beyond admission use only the matrix. Radix
    # iteration avoids Python's decimal string conversion digit ceiling.
    return reverse_radix_integer(value, 10)


def _decimal_width(value: int) -> int:
    """Count exact decimal digits without integer-to-string conversion."""
    return sum(1 for _ in decimal_digits_lsd(value))


def physical_carry_field_borrow_projection(
    *, target_phase: int, physical_mod198: int, seed_mod9: int
) -> dict[str, object]:
    """Factor mod-90 carry and the low borrow from one authenticated clock."""
    if type(target_phase) is not int or target_phase not in range(4):
        raise ValueError("physical carry field needs an authenticated border phase")
    if type(physical_mod198) is not int or not 0 <= physical_mod198 < 198:
        raise ValueError("physical carry field needs an issued mod-198 residue")
    if type(seed_mod9) is not int or not 0 <= seed_mod9 < 9:
        raise ValueError("physical carry field needs an authenticated seed modulo 9")
    last_digit = 8 if target_phase in (0, 3) else 2
    next_last_digit = 2 if target_phase in (0, 1) else 8
    physical_mod990 = physical_mod198 + 198 * (2 * (last_digit - physical_mod198) % 5)
    carry_field_mod90 = 2 * physical_mod990 % 90

    def fixes_seed_residue(period: int) -> bool:
        multiplier: int = pow(2, period, 9)
        return (multiplier - 1) * seed_mod9 % 9 == 0

    period9 = next(period for period in (1, 2, 6) if fixes_seed_residue(period))
    if (
        carry_field_mod90 % 9 != 2 * physical_mod198 % 9
        or carry_field_mod90 % 10 != 2 * last_digit % 10
    ):
        raise ArithmeticError("physical carry field lost its CRT source")
    return {
        "scope": "source-certified physical border cylinder",
        "target_phase": target_phase,
        "physical_target_mod990": physical_mod990,
        "carry_field_mod90": carry_field_mod90,
        "carry_field_primitive_period_physical_steps": lcm(4, period9),
        "physical_subtraction_borrow_low_digit": int(next_last_digit < last_digit),
        "physical_subtraction_borrow_low_digit_period": 4,
        "full_borrow_mask_period_certified": False,
        "derivation": "Q(x)=concat(str(2*d)); Q(x)=2*x (mod 90); "
        "borrow bit=[T(x)%10 < x%10]",
    }


@dataclass(frozen=True, slots=True)
class LaurentAccumulatorReturn:
    """Exact affine action of k source-guarded four-physical-step macros.

    Form: x'=m*x, A'=A+a*x+c, B'=B+b*x+c (mod 198).
    'g' is the mirrored growth bit of the first step in EACH macro.
    """

    first_growth: int
    macros: int
    multiplier: int
    a_coefficient: int
    b_coefficient: int
    constant: int

    def __post_init__(self) -> None:
        if (
            type(self.first_growth) is not int
            or self.first_growth not in (0, 1)
            or type(self.macros) is not int
            or self.macros < 0
            or any(
                type(value) is not int or not 0 <= value < MODULUS
                for value in (
                    self.multiplier,
                    self.a_coefficient,
                    self.b_coefficient,
                    self.constant,
                )
            )
        ):
            raise ValueError("malformed canonical Laurent accumulator action")
        sigma = _geometric_160(self.macros, MODULUS)
        alpha = 100 if self.first_growth else 82
        if (
            self.multiplier != pow(MULTIPLIER, self.macros, MODULUS)
            or self.a_coefficient != alpha * sigma % MODULUS
            or self.b_coefficient != (159 - alpha) * sigma % MODULUS
            or self.constant != 99 * self.macros % MODULUS
        ):
            raise ValueError(
                "Laurent accumulator action is not the canonical semantic power"
            )

    @staticmethod
    def identity(first_growth: int) -> LaurentAccumulatorReturn:
        if type(first_growth) is not int or first_growth not in (0, 1):
            raise ValueError("certified mirrored-growth phase must be a bit")
        return LaurentAccumulatorReturn(first_growth, 0, 1, 0, 0, 0)

    @staticmethod
    def generator(first_growth: int) -> LaurentAccumulatorReturn:
        alpha = 100 if first_growth else 82
        beta = 159 - alpha
        return LaurentAccumulatorReturn(first_growth, 1, 160, alpha, beta, 99)

    def then(self, later: LaurentAccumulatorReturn) -> LaurentAccumulatorReturn:
        """Order-preserving composition, without expanding a source word."""
        if (
            type(later) is not LaurentAccumulatorReturn
            or self.first_growth != later.first_growth
        ):
            raise ValueError("incompatible Laurent border phases")
        return LaurentAccumulatorReturn(
            self.first_growth,
            self.macros + later.macros,
            later.multiplier * self.multiplier % MODULUS,
            (self.a_coefficient + later.a_coefficient * self.multiplier) % MODULUS,
            (self.b_coefficient + later.b_coefficient * self.multiplier) % MODULUS,
            (self.constant + later.constant) % MODULUS,
        )

    def power(self, times: int) -> LaurentAccumulatorReturn:
        """Exact geometric closed-form power in O(log(repetitions)) arithmetic.

        The canonical semantic action is a known power of one guarded macro.
        Multiplying its exponent is equivalent to binary matrix squaring but
        avoids constructing and revalidating intermediate matrices.
        """
        if type(times) is not int or times < 0:
            raise ValueError("nonnegative integer repetition count required")
        repeats = self.macros * times
        sigma = _geometric_160(repeats, MODULUS)
        alpha = 100 if self.first_growth else 82
        return LaurentAccumulatorReturn(
            self.first_growth,
            repeats,
            pow(MULTIPLIER, repeats, MODULUS),
            alpha * sigma % MODULUS,
            (159 - alpha) * sigma % MODULUS,
            99 * repeats % MODULUS,
        )

    def apply(self, x: int, a: int, b: int) -> tuple[int, int, int]:
        if any(type(v) is not int for v in (x, a, b)):
            raise TypeError("a Laurent projection takes three integer residues")
        return (
            self.multiplier * x % MODULUS,
            (a + self.a_coefficient * x + self.constant) % MODULUS,
            (b + self.b_coefficient * x + self.constant) % MODULUS,
        )

    @property
    def matrix(self) -> tuple[tuple[int, ...], ...]:
        """Displayed row-major matrix for (x,A,B,1), already reduced mod198."""
        return (
            (self.multiplier, 0, 0, 0),
            (self.a_coefficient, 1, 0, self.constant),
            (self.b_coefficient, 0, 1, self.constant),
            (0, 0, 0, 1),
        )


@dataclass(frozen=True, slots=True)
class LaurentFirstJetReturn:
    """Exact first Laurent inward-jet lift, modulo 198 * 10.

    The observed border pairs *prove*, without a third-digit assumption,
    J mod10 = 4 when the first H grows and J mod10 = 1 otherwise. Hence
    X' = 160*X -198*(4 or 1) (mod 1980). The full higher mask is still
    needed beyond this precision.
    """

    first_growth: int
    macros: int
    multiplier: int
    constant: int

    def __post_init__(self) -> None:
        if (
            type(self.first_growth) is not int
            or self.first_growth not in (0, 1)
            or type(self.macros) is not int
            or self.macros < 0
            or type(self.multiplier) is not int
            or not 0 <= self.multiplier < FIRST_JET_MODULUS
            or type(self.constant) is not int
            or not 0 <= self.constant < FIRST_JET_MODULUS
        ):
            raise ValueError("malformed canonical Laurent first-jet action")
        expected = (
            (-198 * (4 if self.first_growth else 1))
            * _geometric_160(self.macros, FIRST_JET_MODULUS)
            % FIRST_JET_MODULUS
        )
        if (
            self.multiplier != pow(MULTIPLIER, self.macros, FIRST_JET_MODULUS)
            or self.constant != expected
        ):
            raise ValueError(
                "Laurent first-jet action is not a canonical source-independent power"
            )

    @classmethod
    def identity(cls, first_growth: int) -> LaurentFirstJetReturn:
        if type(first_growth) is not int or first_growth not in (0, 1):
            raise ValueError("a certified growth phase bit is required")
        return cls(first_growth, 0, 1, 0)

    @classmethod
    def generator(cls, first_growth: int) -> LaurentFirstJetReturn:
        cls.identity(first_growth)
        return cls(
            first_growth,
            1,
            MULTIPLIER,
            (-198 * (4 if first_growth else 1)) % FIRST_JET_MODULUS,
        )

    def then(self, later: LaurentFirstJetReturn) -> LaurentFirstJetReturn:
        if (
            type(later) is not LaurentFirstJetReturn
            or self.first_growth != later.first_growth
        ):
            raise ValueError("mismatched Laurent first-jet phase")
        return LaurentFirstJetReturn(
            self.first_growth,
            self.macros + later.macros,
            (later.multiplier * self.multiplier) % FIRST_JET_MODULUS,
            (later.multiplier * self.constant + later.constant) % FIRST_JET_MODULUS,
        )

    def power(self, times: int) -> LaurentFirstJetReturn:
        """Source-independent exact geometric power; no temporal tape."""
        if type(times) is not int or times < 0:
            raise ValueError("a nonnegative return exponent is required")
        repeats = self.macros * times
        sigma = _geometric_160(repeats, FIRST_JET_MODULUS)
        c = -198 * (4 if self.first_growth else 1)
        return LaurentFirstJetReturn(
            self.first_growth,
            repeats,
            pow(MULTIPLIER, repeats, FIRST_JET_MODULUS),
            c * sigma % FIRST_JET_MODULUS,
        )

    def apply(self, source: int) -> int:
        if type(source) is not int:
            raise TypeError("first Laurent jet needs an integer residue")
        return (self.multiplier * source + self.constant) % FIRST_JET_MODULUS

    def exact_period(self, source: int) -> dict[str, int]:
        """Closed-form CRT lasso, without a second 1980-state orbit scan.

        1980=20*99; 160 is divisible by 20 and invertible modulo 99.
        Therefore the mod-20 component becomes constant after at most one
        macro and the mod-99 component has primitive multiplicative order.
        """
        if type(source) is not int:
            raise TypeError("the first jet source must be an integer residue")
        if self.macros == 0:
            transient, period = 0, 1
        else:
            transient = int(source % 20 != self.constant % 20)
            base_order = _primitive_order_160_mod99(source)
            period = base_order // gcd(base_order, self.macros)
        return {
            "transient_macros": transient,
            "primitive_period_macros": period,
            "primitive_period_physical_generations": 4 * period,
            "states_visited": transient + period,
        }


def projected_period_from_state(x: int, first_growth: int) -> dict[str, int]:
    """Primitive all-future return period on the canonical 198-state factor.

    The scalar cycle is finite. Along a primitive scalar cycle of length p,
    the affine differences (delta_A,delta_B) are independent of A/B; the
    additive order of that displacement gives the *primitive* joint period.
    No scanning of the full (x,A,B) state graph or source word is required.
    """
    if type(x) is not int:
        raise TypeError("source residue must be an integer")
    generator = LaurentAccumulatorReturn.generator(first_growth)
    # Quotient FIRST: 160 is even and invertible modulo 99. Any odd source
    # residue enters the 99-element even ideal after exactly one step.
    # Thereafter write x=2*y mod 198, so y' =160*y mod99.
    # The primitive orbit order is ord_{99/gcd(y,99)}(160), dividing 30;
    # this replaces an unnecessary second 198-state chronological lasso walk.
    transient = int(x % MODULUS % 2 != 0)
    entering = generator.power(transient).apply(x, 0, 0)[0]
    p = _primitive_order_160_mod99(entering // 2)
    states = transient + p
    _, da, db = generator.power(p).apply(entering, 0, 0)
    additive_order = lcm(MODULUS // gcd(MODULUS, da), MODULUS // gcd(MODULUS, db))
    return {
        "transient_macros": transient,
        "primitive_residue_macros": p,
        "period_displacement_norm_mod198": da,
        "period_displacement_rev_mod198": db,
        "additive_order": additive_order,
        "primitive_joint_macros": p * additive_order,
        "primitive_joint_physical_generations": 4 * p * additive_order,
        "scalar_states_visited": states,
    }


def _prefix_accumulators(
    seed: int, physical_generation: int, *, checkpoint: int
) -> tuple[int, int, int, int]:
    """Finite *source-admission prefix* only; never the requested orbit tail.

    This reproduces the user's exact accumulator definitions at the certified
    anchor, and is checked against the separately issued source SLP residue.
    """
    if (
        type(seed) is not int
        or seed <= 0
        or type(physical_generation) is not int
        or physical_generation < 0
    ):
        raise ValueError(
            "positive source and nonnegative admission generation required"
        )
    if physical_generation > 513 or not 0 <= checkpoint <= physical_generation:
        raise ValueError("source entry exceeded the admissible finite prefix")
    x = seed
    physical_checkpoint = seed
    previous = seed
    norm = seed % MODULUS
    rev = 0
    for n in range(1, physical_generation + 1):
        x = 2 * _reverse(x)
        if n == checkpoint:
            physical_checkpoint = x
        u = x if n % 2 == 0 else _reverse(x)
        if n % 2:
            rev = (rev + u - previous) % MODULUS
        else:
            norm = (norm + u - previous) % MODULUS
        previous = u
    return x, norm, rev, physical_checkpoint


def _partial_macro(
    x: int,
    a: int,
    b: int,
    first_growth: int,
    physical_remainder: int,
) -> tuple[int, int, int]:
    """Project the remaining 0..3 steps by the SAME Laurent carry port.

    The parity of the carry masks is known from the certified two-digit
    boundary: H_1(x) = 20x-99 (mod198), H_0(x)=2x (mod198).
    """
    if physical_remainder not in (0, 1, 2, 3):
        raise ValueError("partial macro must have 0..3 physical steps")
    x %= MODULUS
    a %= MODULUS
    b %= MODULUS
    if physical_remainder == 0:
        return x, a, b
    h = (20 * x - 99) % MODULUS if first_growth else (2 * x) % MODULUS
    b = (b + h - x) % MODULUS
    if physical_remainder == 1:
        return h, a, b
    z = (2 * h) % MODULUS
    a = (a + z - h) % MODULUS
    if physical_remainder == 2:
        return z, a, b
    second_growth = 1 - first_growth
    hh = (20 * z - 99) % MODULUS if second_growth else (2 * z) % MODULUS
    b = (b + hh - z) % MODULUS
    return hh, a, b


def source_laurent_accumulator_packet(
    owner: DoubleReverseTerm,
    prefix: int,
    action: CertifiedResidueTemporalAction,
    *,
    authenticated_morphism: CertifiedSeedOrbitMorphism | None = None,
) -> dict[str, object]:
    """One authenticated source action, powered to any target generation.

    Authentication belongs to temporal_residue_quotient. Only the finite
    prefix through the first even certified source state is evaluated with
    integers, to anchor the user's sums. No requested future numeric word is
    constructed here. The live term owner, exact issued prefix cursor and
    every finite prefix digit are checked; a matching width or residue cannot
    authorize a jump.
    """
    from .power import DoubleReverseTerm

    if type(owner) is not DoubleReverseTerm:
        raise TypeError("a live source-bound DoubleReverseTerm owner is required")
    if type(action) is not CertifiedResidueTemporalAction:
        raise TypeError("a source-certified modular action is required")
    if type(prefix) is not int or prefix < 0:
        raise ValueError("source prefix must be a nonnegative integer")
    owner.validate_source_binding()
    if authenticated_morphism is None:
        action.validate_source_authority()
        authority = validate_source_record(action)
        if authority.source_generation != prefix:
            raise ValueError("source prefix does not match the issued action")
    else:
        # Reuse the *same* residue and full-word source morphism when the
        # Hashlife CLI has already issued it. Do not fold another source SLP.
        from .temporal_seed_morphism import CertifiedSeedOrbitMorphism

        if type(authenticated_morphism) is not CertifiedSeedOrbitMorphism:
            raise TypeError(
                "only a real source-issued full-word morphism can authenticate this projection"
            )
        authority = authenticated_morphism.validate_source_authority()
        if (
            authenticated_morphism.residue_action is not action
            or authority.source_generation != prefix
            or authenticated_morphism.physical_prefix != prefix
            or authenticated_morphism.start_f_steps != 0
            or authenticated_morphism.source_root != authority.root
            or authenticated_morphism.first.root != authority.root
            or authenticated_morphism.source_phase != action.phase
            or authenticated_morphism.steps * 2 != action.duration
            or authenticated_morphism.first.width != action.width_in
            or authenticated_morphism.first.residue198 != action.source_mod198
            or authenticated_morphism.first.residue99 != action.source_mod99
            or authenticated_morphism.last.width != action.width_out
            or authenticated_morphism.last.residue198 != action.target_mod198
            or authenticated_morphism.last.residue99 != action.target_mod99
        ):
            raise ValueError(
                "Laurent projection does not belong to the source-issued complete-word morphism"
            )
    engine = owner.temporal_engine
    if (
        authority.arena is not owner.source_arena
        or engine.arena is not owner.source_arena
        or engine.source_root != owner.source_root
        or owner.generation != prefix + action.duration
    ):
        raise ValueError(
            "Laurent action belongs to a different source owner or horizon"
        )
    if prefix == 0:
        if (
            authority.root != owner.source_root
            or engine.certify(owner.source_root) != action.phase
        ):
            raise ValueError(
                "zero-prefix Laurent action does not name the owner source"
            )
    else:
        cursor = engine.source_prefix()
        if (
            cursor is None
            or cursor.physical_steps != prefix
            or cursor.certified_phase != action.phase
            or engine.root_of(cursor.source) != owner.source_root
            or engine.root_of(cursor.target) != authority.root
        ):
            raise ValueError(
                "Laurent action has no matching issued source-prefix cursor"
            )
    completed_endpoint = (
        owner.issued_completed_endpoint_root()
        if authenticated_morphism is not None
        else None
    )
    if (
        authenticated_morphism is not None
        and completed_endpoint is not None
        and authenticated_morphism.last.root != completed_endpoint
    ):
        raise ValueError(
            "full-word morphism differs from the issued scheduler endpoint"
        )
    target = prefix + action.duration
    anchor = prefix + (prefix % 2)
    if anchor > target:
        return {
            "status": "unavailable",
            "reason": "the target precedes the first even source-certified normalization anchor",
            "all_depth_digit_period_certified": False,
        }
    seed = owner.seed
    if type(seed) is not int or seed <= 0:
        raise ValueError("a positive physical 2rev10 seed is required")
    x, a, b, physical_prefix = _prefix_accumulators(seed, anchor, checkpoint=prefix)
    source_width = owner.source_arena.nodes[authority.root].length
    if _decimal_width(physical_prefix) != source_width:
        raise ValueError(
            "finite Laurent prefix width differs from the issued source word"
        )
    with closing(
        iter_symbols(
            owner.source_arena,
            authority.root,
            reverse=True,
            reserve_task=lambda: owner.resource_ledger.reserve(
                owner.scratch_owner, entries=1, nodes=1
            ),
            release_tasks=lambda count: owner.resource_ledger.release(
                owner.scratch_owner, entries=count, nodes=count
            ),
            check_open=owner.check_open,
        )
    ) as source_digits:
        for expected, actual in zip(
            decimal_digits_lsd(physical_prefix), source_digits, strict=True
        ):
            if expected != actual:
                raise ValueError(
                    "finite Laurent source digits differ from the issued SLP word"
                )
    if (
        source_width != action.width_in
        or physical_prefix % MODULUS != action.source_mod198
    ):
        raise AssertionError(
            "exact Laurent source word disagrees with its residue action"
        )
    delta = anchor - prefix
    anchor_action = certified_residue_action(
        phase=action.phase,
        width=action.width_in,
        duration=delta,
        source_mod99=action.source_mod99,
        source_mod198=action.source_mod198,
    )
    if (
        _decimal_width(x) != anchor_action.width_out
        or x % MODULUS != anchor_action.target_mod198
    ):
        raise AssertionError(
            "Laurent normalization failed authenticated source transport"
        )
    phase = (action.phase + delta) % 4
    if edge_phase_of_integer(x) != phase:
        raise AssertionError("normalization anchor lost its certified border guard")
    growth = PHYSICAL_GROWTH_CYCLES[phase]
    if growth[0] + growth[2] != 1:
        raise AssertionError("the normalized Laurent macro has no paired growth clock")
    first_growth = growth[0]
    macros, remainder = divmod(target - anchor, 4)
    powered_action = LaurentAccumulatorReturn.generator(first_growth).power(macros)
    radial_jet = LaurentFirstJetReturn.generator(first_growth).power(macros)
    radial_target = radial_jet.apply(x)
    x_final, a_final, b_final = powered_action.apply(x, a, b)
    if radial_target % MODULUS != x_final:
        raise AssertionError(
            "the first Laurent jet failed its mod-198 factor projection"
        )
    normalized_target, a_final, b_final = _partial_macro(
        x_final, a_final, b_final, first_growth, remainder
    )
    if (a_final + b_final - normalized_target) % MODULUS:
        raise AssertionError("the exact normalized sum failed the Laurent seam")
    expected_width = anchor_action.width_out + 2 * macros + sum(growth[:remainder])
    if action.width_out != expected_width:
        raise AssertionError("growth-clock width disagrees with the Laurent return")
    if target % 2 == 0:
        if normalized_target != action.target_mod198:
            raise AssertionError(
                "Laurent projected endpoint disagrees with authenticated mod-198 source"
            )
    elif (
        normalized_target % 99
        != (action.target_mod99 * pow(10, action.width_out - 1, 99)) % 99
    ):
        raise AssertionError("Laurent reversal projection disagrees with source mod-99")
    period = projected_period_from_state(x % MODULUS, first_growth)
    return {
        "status": "available",
        "scope": "seed-certified mod-198 normalized (X,norm_sum,rev_sum) quotient only",
        "source_generation": prefix,
        "normalization_anchor_generation": anchor,
        "anchor_phase": phase,
        "first_mirrored_growth": first_growth,
        "anchor_width": anchor_action.width_out,
        "anchor_state_mod198": [x % MODULUS, a, b],
        "target_generation": target,
        "powered_macros": macros,
        "partial_physical_steps": remainder,
        "powered_matrix_mod198": [list(row) for row in powered_action.matrix],
        "first_laurent_jet": {
            "modulus": FIRST_JET_MODULUS,
            "scope": "certified four-generation even-anchor return only",
            "source_residue": x % FIRST_JET_MODULUS,
            "multiplier": radial_jet.multiplier,
            "constant": radial_jet.constant,
            "target_residue": radial_target,
            "primitive_period": LaurentFirstJetReturn.generator(
                first_growth
            ).exact_period(x),
            "higher_decimal_digits_certified": False,
        },
        "target_normalized_mod198": normalized_target,
        "target_norm_sum_mod198": a_final,
        "target_rev_sum_mod198": b_final,
        "physical_carry_field_borrow_clock": physical_carry_field_borrow_projection(
            target_phase=(action.phase + action.duration) % 4,
            physical_mod198=action.target_mod198,
            seed_mod9=seed % 9,
        ),
        "primitive_period": period,
        "certified_growth_and_mod198_all_future": True,
        "all_depth_digit_period_certified": False,
        "full_source_word_power_is_owned_by_seed_morphism": True,
    }


__all__ = [
    "LaurentAccumulatorReturn",
    "LaurentFirstJetReturn",
    "physical_carry_field_borrow_projection",
    "projected_period_from_state",
    "source_laurent_accumulator_packet",
]
