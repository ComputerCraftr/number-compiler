"""Demanded low-radix ports of source-bounded Fermat/Mersenne recurrences.

Only the explicitly requested small digit modulus is factored.  Fermat source
residues use CRT across the 3-primary and coprime parts; Mersenne source
residues use the norm-one trace of a matrix in ``SL_2(Z/m)``.  The separate
source guard proves that the raw source square has not reached the candidate
modulus seam before these unreduced residues are exposed as candidate digits.

This module observes exact source carries, borrows, and digits.  These ports do
not decide primality and are never consumed implicitly by a theorem query.
"""

from __future__ import annotations

from dataclasses import dataclass
from dataclasses import field as dataclass_field
from weakref import ReferenceType, ref

from number_compiler.arithmetic.fields.digit_formula import (
    FunctionMonoid,
    synthesize_function_monoid,
    synthesize_multiply_add,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power, modular_power
from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent
from number_compiler.hashlife.execution.source_image_seals import _typed_equal

MAX_DIGIT_MODULUS = 1_000_000
MAX_SOURCE_LEVEL_BITS = 4_096
MAX_SPARSE_DIGIT_POSITIONS = 19
PORT_BOUNDARIES = (1, 2, 3, 5, 6)
MULTIRADIX_BASES = (2, 3, 5, 7, 10, 11, 13, 27)
MAX_MULTIRADIX_PLACES = 19


def _validate_source(family: str, parameter: int, level: int) -> None:
    if family not in ("fermat", "mersenne"):
        raise ValueError(family)
    if type(parameter) is not int or parameter < 0:
        raise ValueError((family, parameter))
    if family == "mersenne" and parameter < 2:
        raise ValueError((family, parameter))
    if type(level) is not int or level < 0:
        raise ValueError(level)
    if level.bit_length() > MAX_SOURCE_LEVEL_BITS:
        raise ValueError(
            (
                "source-level-work-budget-exceeded",
                level.bit_length(),
                MAX_SOURCE_LEVEL_BITS,
            )
        )


def source_no_wrap_guard(family: str, parameter: int, level: int) -> bool:
    """Whether the requested raw square is proved below the candidate seam.

    For Fermat, the source width is ``2**parameter`` bits and the test reduces
    to ``level + 2 <= parameter``.  For Mersenne, the width is ``parameter``
    bits, so the exact inequality ``2**(level+2) <= parameter`` is checked by
    its bit length.  No family candidate or source integer is constructed.
    """
    _validate_source(family, parameter, level)
    if family == "fermat":
        return parameter >= 3 and level + 2 <= parameter
    return parameter >= 7 and level + 2 <= parameter.bit_length() - 1


def require_source_no_wrap(family: str, parameter: int, level: int) -> None:
    if not source_no_wrap_guard(family, parameter, level):
        raise ValueError(
            ("inner-squared-source-wrap-not-excluded", family, parameter, level)
        )


def _check_digit_modulus(modulus: int) -> None:
    if type(modulus) is not int or not 2 <= modulus <= MAX_DIGIT_MODULUS:
        raise ValueError(("digit-modulus-budget-exceeded", modulus, MAX_DIGIT_MODULUS))


def _bounded_radix_power(base: int, exponent: int) -> int:
    """Multiply only while the requested radix modulus remains admitted."""
    if type(base) is not int or not 2 <= base <= MAX_DIGIT_MODULUS:
        raise ValueError(("digit-modulus-budget-exceeded", base, MAX_DIGIT_MODULUS))
    if type(exponent) is not int or exponent < 0:
        raise ValueError(("invalid-radix-exponent", exponent))
    value = 1
    for _ in range(exponent):
        if value > MAX_DIGIT_MODULUS // base:
            raise ValueError(("digit-modulus-budget-exceeded", base, exponent))
        value *= base
    _check_digit_modulus(value)
    return value


def _distinct_prime_factors(value: int) -> tuple[tuple[int, ...], int]:
    """Factor one admitted small modulus, returning factors and trial count."""
    if type(value) is not int or value < 1:
        raise ValueError(value)
    factors: list[int] = []
    trials = 0
    candidate = 2
    remaining = value
    while candidate * candidate <= remaining:
        trials += 1
        if remaining % candidate == 0:
            factors.append(candidate)
            while remaining % candidate == 0:
                remaining //= candidate
        candidate = 3 if candidate == 2 else candidate + 2
    if remaining > 1:
        factors.append(remaining)
    return tuple(factors), trials


def _euler_phi(value: int) -> tuple[int, int]:
    if value == 1:
        return 1, 0
    factors, trials = _distinct_prime_factors(value)
    result = value
    for prime in factors:
        result = result // prime * (prime - 1)
    return result, trials


def _sl2_group_order(modulus: int) -> tuple[int, int]:
    factors, trials = _distinct_prime_factors(modulus)
    order = modulus**3
    for prime in factors:
        order = order // (prime * prime) * (prime * prime - 1)
    return order, trials


Matrix2 = tuple[int, int, int, int]


def _matrix_multiply(first: Matrix2, second: Matrix2, modulus: int) -> Matrix2:
    a, b, c, d = first
    e, f, g, h = second
    return (
        (a * e + b * g) % modulus,
        (a * f + b * h) % modulus,
        (c * e + d * g) % modulus,
        (c * f + d * h) % modulus,
    )


def _mersenne_source_residue(level: int, modulus: int) -> tuple[int, int, int, int]:
    order, factor_trials = _sl2_group_order(modulus)
    exponent_power = modular_power(2, level, order)
    exponent = exponent_power.value
    matrix: Matrix2 = (4 % modulus, (-1) % modulus, 1 % modulus, 0)
    identity: Matrix2 = (1 % modulus, 0, 0, 1 % modulus)
    matrix_power = binary_power(
        matrix,
        exponent,
        identity=identity,
        compose=lambda left, right: _matrix_multiply(left, right, modulus),
    )
    result = (matrix_power.value[0] + matrix_power.value[3]) % modulus
    return result, factor_trials, exponent_power.compositions, matrix_power.compositions


def _fermat_source_residue(level: int, modulus: int) -> tuple[int, int, int, int]:
    power_of_three = 1
    coprime = modulus
    while coprime % 3 == 0:
        power_of_three *= 3
        coprime //= 3

    factor_trials = 0
    scalar_compositions = 0
    if coprime == 1:
        coprime_residue = 0
    else:
        phi, trials = _euler_phi(coprime)
        factor_trials += trials
        if phi > 1:
            exponent_power = modular_power(2, level, phi)
            exponent = exponent_power.value
            scalar_compositions += exponent_power.compositions
        else:
            exponent = 0
        coprime_power = modular_power(3, exponent, coprime)
        coprime_residue = coprime_power.value
        scalar_compositions += coprime_power.compositions

    if power_of_three == 1:
        return coprime_residue, factor_trials, scalar_compositions, 0

    valuation = 0
    temp = power_of_three
    while temp > 1:
        temp //= 3
        valuation += 1
    if level >= (valuation - 1).bit_length():
        # 2**level >= v_3(modulus), so the residue is zero.  Do this check
        # before lowering 2**level: the requested source level can be huge.
        three_residue = 0
    else:
        three_residue = pow(3, 1 << level, power_of_three)

    if coprime == 1:
        return three_residue, factor_trials, scalar_compositions, 0
    lift = (
        (coprime_residue - three_residue) * pow(power_of_three, -1, coprime)
    ) % coprime
    return (
        three_residue + power_of_three * lift,
        factor_trials,
        scalar_compositions + 1,
        0,
    )


@dataclass(frozen=True, slots=True)
class SmallModulusWork:
    """Exact bounded work counters for one demanded source residue."""

    modulus: int
    factor_trial_candidates: int
    scalar_power_compositions: int
    matrix_power_compositions: int

    def __post_init__(self) -> None:
        _check_digit_modulus(self.modulus)
        counters = (
            self.factor_trial_candidates,
            self.scalar_power_compositions,
            self.matrix_power_compositions,
        )
        if any(type(counter) is not int or counter < 0 for counter in counters):
            raise ValueError(self)
        if self.factor_trial_candidates > 500:
            raise ValueError("small-modulus factor work exceeded its trial bound")


def _source_residue(
    family: str, level: int, modulus: int
) -> tuple[int, SmallModulusWork]:
    _check_digit_modulus(modulus)
    if family == "fermat":
        residue, trials, scalar, matrix = _fermat_source_residue(level, modulus)
    elif family == "mersenne":
        residue, trials, scalar, matrix = _mersenne_source_residue(level, modulus)
    else:
        raise ValueError(family)
    return residue, SmallModulusWork(modulus, trials, scalar, matrix)


def _prefix_multiplier_carries(
    source: int, base: int, places: int, multiplier: int
) -> tuple[tuple[int, ...], int]:
    """Use the shared finite transition monoid for demanded radix carries."""
    transducer = synthesize_multiply_add(base, multiplier, 0)
    monoid: FunctionMonoid = synthesize_function_monoid(transducer)
    state_zero = transducer.state_index[0]
    action = monoid.identity
    carries: list[int] = []
    remaining = source
    for _ in range(places):
        digit = remaining % base
        remaining //= base
        digit_action = monoid.digit_function[digit]
        action = monoid.composition[digit_action][action]
        state = monoid.functions[action][state_zero]
        carries.append(transducer.states[state])
    return tuple(carries), monoid.size


@dataclass(frozen=True, slots=True)
class ThreePowerRadixBoundary:
    """Exact demanded carry/borrow fields at one low-radix boundary.

    ``tripling_carry`` is the full 0/1/2 carry of multiplying the source by
    three. ``tripling_add_carry`` is the distinct Boolean carry of ``X+2X``;
    it equals the borrow of ``3X-X``. Temporal innovation fields compare
    adjacent dyadic source levels and are separate projections.
    """

    places: int
    source_remainder: int
    tripling_carry: int
    doubling_carry: int
    tripling_add_carry: int
    tripling_sub_borrow: int
    innovation_carry: int
    innovation_borrow: int
    successive_innovation_borrow: int

    def __post_init__(self) -> None:
        exact = (
            self.places,
            self.source_remainder,
            self.tripling_carry,
            self.doubling_carry,
            self.tripling_add_carry,
            self.tripling_sub_borrow,
            self.innovation_carry,
            self.innovation_borrow,
            self.successive_innovation_borrow,
        )
        if any(type(value) is not int for value in exact):
            raise TypeError("multiradix boundary values must be exact integers")
        if self.places < 1:
            raise ValueError(self.places)
        if not 0 <= self.tripling_carry <= 2 or not 0 <= self.doubling_carry <= 1:
            raise ValueError("multiplication carries are outside their trit/bit ranges")
        for field in (
            self.tripling_add_carry,
            self.tripling_sub_borrow,
            self.innovation_carry,
            self.innovation_borrow,
            self.successive_innovation_borrow,
        ):
            if field not in (0, 1):
                raise ValueError("multiradix borrow/carry fields must be Boolean")


_MULTIRADIX_ISSUER = object()


@dataclass(frozen=True, slots=True)
class _MultiradixProvenance:
    issuer: object
    record: ReferenceType[object]
    snapshot: tuple[object, ...]


@dataclass(frozen=True, slots=True, weakref_slot=True)
class FermatMultiradixPort:
    """Bounded source-only multiradix observations for ``3**(2**level)``."""

    index: int
    level: int
    base: int
    places: int
    modulus: int
    source_residue: int
    previous_residue: int
    next_residue: int
    boundaries: tuple[ThreePowerRadixBoundary, ...]
    carry_transition_steps: int
    carry_monoid_sizes: tuple[int, int]
    work: tuple[SmallModulusWork, SmallModulusWork, SmallModulusWork]
    # This is producer authority, not mathematical content.  Keeping it out
    # of construction and comparison preserves the public equality API while
    # preventing a structural copy from inheriting the producer's identity.
    _issuer: object = dataclass_field(
        default=None, init=False, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        if (
            type(self.index) is not int
            or self.index < 1
            or self.index.bit_length() > MAX_SOURCE_LEVEL_BITS
        ):
            raise ValueError(("Fermat index", self.index))
        if type(self.level) is not int or self.level < 1:
            raise ValueError(("dyadic level", self.level))
        if self.level.bit_length() > MAX_SOURCE_LEVEL_BITS:
            raise ValueError(("source-level-work-budget-exceeded", self.level))
        if not DyadicExtent(self.index).contains_index(self.level):
            raise ValueError(("level-exceeds-Fermat-source", self.index, self.level))
        if type(self.base) is not int or self.base not in MULTIRADIX_BASES:
            raise ValueError(("unsupported-multiradix-base", self.base))
        if (
            type(self.places) is not int
            or not 1 <= self.places <= MAX_MULTIRADIX_PLACES
        ):
            raise ValueError(("multiradix-place-budget-exceeded", self.places))
        expected_modulus = _bounded_radix_power(self.base, self.places)
        if type(self.modulus) is not int or self.modulus != expected_modulus:
            raise ValueError("multiradix modulus does not match its admitted request")
        for residue in (self.source_residue, self.previous_residue, self.next_residue):
            if type(residue) is not int or not 0 <= residue < self.modulus:
                raise ValueError("source residue is outside the admitted modulus")
        if type(self.boundaries) is not tuple or len(self.boundaries) != self.places:
            raise ValueError("multiradix boundary vector is incomplete")
        if any(type(port) is not ThreePowerRadixBoundary for port in self.boundaries):
            raise TypeError("multiradix boundaries require exact port records")
        if (
            type(self.work) is not tuple
            or len(self.work) != 3
            or any(
                type(item) is not SmallModulusWork or item.modulus != self.modulus
                for item in self.work
            )
        ):
            raise TypeError("multiradix demand requires three bounded work records")
        if type(self.carry_transition_steps) is not int or (
            self.carry_transition_steps != 2 * self.places
        ):
            raise ValueError("multiradix carry transition work is not exact")
        if (
            type(self.carry_monoid_sizes) is not tuple
            or len(self.carry_monoid_sizes) != 2
            or any(
                type(size) is not int or not 1 <= size <= 27
                for size in self.carry_monoid_sizes
            )
        ):
            raise ValueError("multiradix carry monoid work is outside the trit bound")
        place_modulus = 1
        for port in self.boundaries:
            place_modulus *= self.base
            current = self.source_residue % place_modulus
            before = self.previous_residue % place_modulus
            after = self.next_residue % place_modulus
            innovation = (after - current) % place_modulus
            previous_innovation = (current - before) % place_modulus
            if (
                port.places > self.places
                or port.source_remainder != current
                or port.tripling_carry != (3 * current) // place_modulus
                or port.doubling_carry != (2 * current) // place_modulus
                or port.tripling_add_carry != port.tripling_carry - port.doubling_carry
                or port.tripling_sub_borrow
                != int((3 * current) % place_modulus < current)
                or port.tripling_add_carry != port.tripling_sub_borrow
                or port.innovation_carry != int(current + innovation >= place_modulus)
                or port.innovation_borrow != int(after < current)
                or port.innovation_carry != port.innovation_borrow
                or port.successive_innovation_borrow
                != int(innovation < previous_innovation)
            ):
                raise ValueError("multiradix fields do not match their source residues")
        if tuple(port.places for port in self.boundaries) != tuple(
            range(1, self.places + 1)
        ):
            raise ValueError("multiradix boundary positions are not consecutive")

    @property
    def producer_verified(self) -> bool:
        issuer = self._issuer
        return (
            type(issuer) is _MultiradixProvenance
            and issuer.issuer is _MULTIRADIX_ISSUER
            and issuer.record() is self
            and _typed_equal(issuer.snapshot, _multiradix_snapshot(self))
        )


def _multiradix_snapshot(port: FermatMultiradixPort) -> tuple[object, ...]:
    """Capture the mathematical port fields protected by producer authority."""
    return (
        port.index,
        port.level,
        port.base,
        port.places,
        port.modulus,
        port.source_residue,
        port.previous_residue,
        port.next_residue,
        tuple(
            (
                item.places,
                item.source_remainder,
                item.tripling_carry,
                item.doubling_carry,
                item.tripling_add_carry,
                item.tripling_sub_borrow,
                item.innovation_carry,
                item.innovation_borrow,
                item.successive_innovation_borrow,
            )
            for item in port.boundaries
        ),
        port.carry_transition_steps,
        port.carry_monoid_sizes,
        tuple(
            (
                item.modulus,
                item.factor_trial_candidates,
                item.scalar_power_compositions,
                item.matrix_power_compositions,
            )
            for item in port.work
        ),
    )


def _seal_multiradix_port(port: FermatMultiradixPort) -> None:
    object.__setattr__(
        port,
        "_issuer",
        _MultiradixProvenance(
            _MULTIRADIX_ISSUER, ref(port), _multiradix_snapshot(port)
        ),
    )


def demand_three_power_multiradix_port(
    index: int, level: int, base: int, places: int
) -> FermatMultiradixPort:
    """Demand source trits and innovation borrows without candidate reduction.

    This is a low-radix source observation, so it deliberately has no
    Fermat no-wrap requirement. Every actual modulus is checked against the
    existing small-modulus work cap before any source powers are evaluated.
    """
    if type(index) is not int or index < 1:
        raise ValueError(("Fermat index", index))
    if index.bit_length() > MAX_SOURCE_LEVEL_BITS:
        raise ValueError(("Fermat-index-work-budget-exceeded", index))
    if type(level) is not int or level < 1:
        raise ValueError(("dyadic level", level))
    if level.bit_length() > MAX_SOURCE_LEVEL_BITS or (level + 1).bit_length() > (
        MAX_SOURCE_LEVEL_BITS
    ):
        raise ValueError(("source-level-work-budget-exceeded", level))
    if not DyadicExtent(index).contains_index(level):
        raise ValueError(("level-exceeds-Fermat-source", index, level))
    if type(base) is not int or base not in MULTIRADIX_BASES:
        raise ValueError(("unsupported-multiradix-base", base))
    # Reject huge place requests before a power or a loop is formed.
    if type(places) is not int or not 1 <= places <= MAX_MULTIRADIX_PLACES:
        raise ValueError(("multiradix-place-budget-exceeded", places))
    modulus = _bounded_radix_power(base, places)

    # Recover the preceding source once. The two adjacent levels are exact
    # squarings in this admitted small radix modulus, never in the Fermat
    # candidate ring. All carry/borrow projections therefore share one
    # authenticated source owner.
    previous, previous_work = _source_residue("fermat", level - 1, modulus)
    source = (previous * previous) % modulus
    following = (source * source) % modulus
    source_work = SmallModulusWork(modulus, 0, 1, 0)
    following_work = SmallModulusWork(modulus, 0, 1, 0)
    tripling, tripling_monoid_size = _prefix_multiplier_carries(source, base, places, 3)
    doubling, doubling_monoid_size = _prefix_multiplier_carries(source, base, places, 2)
    boundaries: list[ThreePowerRadixBoundary] = []
    place_modulus = 1
    for position in range(1, places + 1):
        place_modulus *= base
        current = source % place_modulus
        before = previous % place_modulus
        after = following % place_modulus
        c3 = tripling[position - 1]
        c2 = doubling[position - 1]
        add_carry = c3 - c2
        next_innovation = (after - current) % place_modulus
        previous_innovation = (current - before) % place_modulus
        innovation_carry = int(current + next_innovation >= place_modulus)
        innovation_borrow = int(after < current)
        difference_borrow = int(next_innovation < previous_innovation)
        if add_carry != int((3 * current) % place_modulus < current):
            raise ArithmeticError("tripling addition carry/3X-X borrow identity failed")
        if innovation_carry != innovation_borrow:
            raise ArithmeticError("source innovation carry/borrow identity failed")
        boundaries.append(
            ThreePowerRadixBoundary(
                position,
                current,
                c3,
                c2,
                add_carry,
                int((3 * current) % place_modulus < current),
                innovation_carry,
                innovation_borrow,
                difference_borrow,
            )
        )
    port = FermatMultiradixPort(
        index,
        level,
        base,
        places,
        modulus,
        source,
        previous,
        following,
        tuple(boundaries),
        2 * places,
        (tripling_monoid_size, doubling_monoid_size),
        (source_work, previous_work, following_work),
    )
    _seal_multiradix_port(port)
    return port


@dataclass(frozen=True, slots=True)
class UnwrappedInnerDigitStencil:
    """Exact sparse demanded digits of a no-wrap inner source square."""

    family: str
    parameter: int
    level: int
    base: int
    positions: tuple[int, ...]
    digits: tuple[int, ...]
    work: SmallModulusWork

    def __post_init__(self) -> None:
        require_source_no_wrap(self.family, self.parameter, self.level)
        if type(self.base) is not int or not 2 <= self.base <= MAX_DIGIT_MODULUS:
            raise ValueError(
                ("digit-modulus-budget-exceeded", self.base, MAX_DIGIT_MODULUS)
            )
        if type(self.positions) is not tuple or type(self.digits) is not tuple:
            raise TypeError("sparse digit coordinates and values must be exact tuples")
        if len(self.positions) > MAX_SPARSE_DIGIT_POSITIONS:
            raise ValueError(
                (
                    "sparse-digit-request-budget-exceeded",
                    len(self.positions),
                    MAX_SPARSE_DIGIT_POSITIONS,
                )
            )
        if type(self.work) is not SmallModulusWork:
            raise TypeError("sparse digit demand requires a bounded work record")
        if len(self.positions) != len(self.digits):
            raise ValueError("sparse digit coordinates and values differ in length")
        if any(
            type(position) is not int or position < 0 for position in self.positions
        ):
            raise ValueError(("invalid-digit-position", self.positions))
        if len(set(self.positions)) != len(self.positions):
            raise ValueError(("duplicate-digit-position", self.positions))
        if any(
            type(digit) is not int or not 0 <= digit < self.base
            for digit in self.digits
        ):
            raise ValueError(("invalid-digit-value", self.digits, self.base))
        if self.positions:
            exponent = max(self.positions) + 1
            if exponent > 19:
                raise ValueError(("digit-modulus-budget-exceeded", self.base, exponent))
            expected_modulus = _bounded_radix_power(self.base, exponent)
            if self.work.modulus != expected_modulus:
                raise ValueError("stencil work modulus does not match sparse demand")
        elif self.work != SmallModulusWork(2, 0, 0, 0):
            raise ValueError("empty sparse demand must carry an empty work record")

    @property
    def coordinate_values(self) -> tuple[tuple[int, int], ...]:
        return tuple(zip(self.positions, self.digits, strict=True))


def demand_unwrapped_inner_digit_stencil(
    family: str,
    parameter: int,
    level: int,
    base: int,
    positions: tuple[int, ...],
) -> UnwrappedInnerDigitStencil:
    """Compute only requested normalized digits, within a fixed modulus cap."""
    require_source_no_wrap(family, parameter, level)
    if type(base) is not int or base < 2 or base > MAX_DIGIT_MODULUS:
        raise ValueError(("digit-modulus-budget-exceeded", base, MAX_DIGIT_MODULUS))
    if type(positions) is not tuple:
        raise TypeError("positions must be an exact tuple")
    if len(positions) > MAX_SPARSE_DIGIT_POSITIONS:
        raise ValueError(
            (
                "sparse-digit-request-budget-exceeded",
                len(positions),
                MAX_SPARSE_DIGIT_POSITIONS,
            )
        )
    if any(type(position) is not int or position < 0 for position in positions):
        raise ValueError(("invalid-digit-position", positions))
    if len(set(positions)) != len(positions):
        raise ValueError(("duplicate-digit-position", positions))
    if not positions:
        return UnwrappedInnerDigitStencil(
            family, parameter, level, base, (), (), SmallModulusWork(2, 0, 0, 0)
        )
    exponent = max(positions) + 1
    # With base <= 10**6 and exponent <= 19 this power has at most 114 decimal
    # digits, so the rejection happens before a demand can allocate a large m.
    if exponent > 19 or base > MAX_DIGIT_MODULUS:
        raise ValueError(("digit-modulus-budget-exceeded", base, exponent))
    modulus = _bounded_radix_power(base, exponent)
    source, work = _source_residue(family, level, modulus)
    target = (source * source - (2 if family == "mersenne" else 0)) % modulus
    digits = tuple((target // (base**position)) % base for position in positions)
    return UnwrappedInnerDigitStencil(
        family, parameter, level, base, positions, digits, work
    )


@dataclass(frozen=True, slots=True)
class UnwrappedInnerRadixPort:
    family: str
    parameter: int
    level: int
    base: int
    boundaries: tuple[int, ...]
    modulus: int
    source_prefix: int
    target_prefix: int
    carry: tuple[int, ...]
    borrow: tuple[int, ...]
    xor: tuple[int, ...]
    work: SmallModulusWork

    def __post_init__(self) -> None:
        require_source_no_wrap(self.family, self.parameter, self.level)
        # Validate the radix before exponentiation: this public value object
        # must not let a hand-built instance trigger an unbounded allocation.
        if type(self.base) is not int or not 2 <= self.base <= 10:
            raise ValueError(("digit-modulus-budget-exceeded", self.base, 10))
        if type(self.work) is not SmallModulusWork:
            raise TypeError("radix port requires a bounded work record")
        expected_modulus = _bounded_radix_power(self.base, 6)
        if (
            type(self.modulus) is not int
            or self.modulus != expected_modulus
            or self.work.modulus != self.modulus
        ):
            raise ValueError("port modulus does not match its six-digit demand")
        if type(self.boundaries) is not tuple or self.boundaries != PORT_BOUNDARIES:
            raise ValueError(self.boundaries)
        if type(self.source_prefix) is not int or type(self.target_prefix) is not int:
            raise ValueError("source/target prefixes must be exact integers")
        if not (
            0 <= self.source_prefix < self.modulus
            and 0 <= self.target_prefix < self.modulus
        ):
            raise ValueError("source/target prefix is outside its radix modulus")
        if any(
            type(wires) is not tuple for wires in (self.carry, self.borrow, self.xor)
        ):
            raise TypeError("carry/borrow/XOR wires must be exact tuples")
        if len(self.carry) != 5 or len(self.borrow) != 5 or len(self.xor) != 5:
            raise ValueError("incomplete five-wire carry/borrow port")
        if any(
            type(bit) is not int or bit not in (0, 1) for bit in self.borrow + self.xor
        ):
            raise ValueError("borrow and XOR wires must be Boolean integers")
        if any(type(value) is not int for value in self.carry):
            raise ValueError("carry wires must be exact integers")
        if self.xor != tuple(
            (carry & 1) ^ borrow
            for carry, borrow in zip(self.carry, self.borrow, strict=True)
        ):
            raise ValueError("carry/borrow parity port is inconsistent")

    @property
    def output_key(self) -> tuple[object, ...]:
        """Occurrence descriptor; this is deliberately not a cache identity."""
        return (
            "source-bound-unwrapped-radix-ports",
            self.family,
            self.parameter,
            self.level,
            self.base,
            self.boundaries,
            self.carry,
            self.borrow,
            self.xor,
        )

    @property
    def semantic_observation(self) -> tuple[object, ...]:
        return (
            "source-bound-radix-port-value",
            self.family,
            self.base,
            self.boundaries,
            self.carry,
            self.borrow,
            self.xor,
            self.target_prefix,
        )

    def digit_at(self, position: int) -> int:
        if type(position) is not int or not 0 <= position < 6:
            raise ValueError(position)
        place = 1
        for _ in range(position):
            place *= self.base
        return (self.target_prefix // place) % self.base


def _radix_port_from_source_residue(
    family: str,
    parameter: int,
    level: int,
    base: int,
    source: int,
    work: SmallModulusWork,
) -> UnwrappedInnerRadixPort:
    modulus = _bounded_radix_power(base, 6)
    target = (source * source - (2 if family == "mersenne" else 0)) % modulus
    digits: list[int] = []
    probe = source
    for _ in range(6):
        digits.append(probe % base)
        probe //= base
    coefficients = [0] * 6
    if family == "mersenne":
        coefficients[0] = -2
    for index, left in enumerate(digits):
        for other, right in enumerate(digits[: 6 - index]):
            coefficients[index + other] += left * right
    carries: list[int] = []
    incoming = 0
    for coefficient in coefficients:
        incoming = (coefficient + incoming) // base
        carries.append(incoming)
    selected = tuple(carries[boundary - 1] for boundary in PORT_BOUNDARIES)
    borrows = tuple(
        int(target % (base**boundary) < source % (base**boundary))
        for boundary in PORT_BOUNDARIES
    )
    xor = tuple(
        (carry & 1) ^ borrow for carry, borrow in zip(selected, borrows, strict=True)
    )
    return UnwrappedInnerRadixPort(
        family,
        parameter,
        level,
        base,
        PORT_BOUNDARIES,
        modulus,
        source,
        target,
        selected,
        borrows,
        xor,
        work,
    )


def demand_unwrapped_inner_radix_port(
    family: str, parameter: int, level: int, base: int
) -> UnwrappedInnerRadixPort:
    """Demand six radix digits and five exact raw-square carry/borrow wires."""
    require_source_no_wrap(family, parameter, level)
    if type(base) is not int or base < 2 or base > 10:
        raise ValueError(("digit-modulus-budget-exceeded", base, MAX_DIGIT_MODULUS))
    modulus = _bounded_radix_power(base, 6)
    _check_digit_modulus(modulus)
    source, work = _source_residue(family, level, modulus)
    return _radix_port_from_source_residue(family, parameter, level, base, source, work)


__all__ = [
    "MAX_DIGIT_MODULUS",
    "MAX_MULTIRADIX_PLACES",
    "MAX_SOURCE_LEVEL_BITS",
    "MAX_SPARSE_DIGIT_POSITIONS",
    "MULTIRADIX_BASES",
    "PORT_BOUNDARIES",
    "FermatMultiradixPort",
    "SmallModulusWork",
    "ThreePowerRadixBoundary",
    "UnwrappedInnerDigitStencil",
    "UnwrappedInnerRadixPort",
    "demand_three_power_multiradix_port",
    "demand_unwrapped_inner_digit_stencil",
    "demand_unwrapped_inner_radix_port",
    "require_source_no_wrap",
    "source_no_wrap_guard",
]
