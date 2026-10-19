"""Core dyadic difference-germ geometry and candidate-ring guards."""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.sequences.power_numbers.numbers import (
    fermat_number,
    mersenne_number,
)
from number_compiler.sequences.prime.set import jacobi_symbol, smallest_factor


class AmbientCapacityUnavailable(RuntimeError):
    """Raised when no exact candidate-derived splitting-weight query is known."""


@dataclass(frozen=True, slots=True)
class DifferenceMomentJumpAudit:
    levels: int
    max_power: int
    root_d: int
    formal_branch_nodes: int
    moment_state_cells: int
    binary_matrix_compositions: int
    iterative_moments: tuple[int, ...]
    jumped_moments: tuple[int, ...]

    @property
    def exact(self) -> bool:
        return self.iterative_moments == self.jumped_moments


@dataclass(frozen=True, slots=True)
class AmbientCapacityTruth:
    """Bounded factor-backed truth label; never a candidate-derived certificate."""

    family: str
    parameter: int
    modulus: int
    local_factors: tuple[int, ...]
    local_ambient_v2: tuple[int, ...]
    baseline_order_v2: int
    local_lift_depths: tuple[int, ...]

    @property
    def minimum_local_depth(self) -> int:
        return min(self.local_lift_depths)

    def splitting_weight(self, level: int) -> int:
        level = int(level)
        if level < 1:
            raise ValueError(level)
        return sum(depth >= level for depth in self.local_lift_depths)


@dataclass(frozen=True, slots=True)
class FormalPhaseFrobeniusAudit:
    """Candidate-derived action on the already-known formal 2-primary circle."""

    family: str
    parameter: int
    lift_level: int
    modulus: int
    formal_order_exponent: int
    candidate_exponent_residue: int
    canonical_action: str
    candidate_derived: bool = True
    factor_enumeration: int = 0
    root_branch_enumeration: int = 0
    splitting_sensitive: bool = False


@dataclass(frozen=True, slots=True)
class ExtensionFrobeniusProbe:
    """One off-circle candidate-ring N-power defect experiment.

    ``defect`` is kept CRT-valued rather than collapsed to a Jacobi sign.
    Nontrivial gcds of its coefficients with ``N`` are retained as natural
    reduction witnesses.  The probe is *not* credited as a capacity oracle:
    all-split composite controls show that global N-power is a generic
    Frobenius-pseudoprime test, not the product of local Frobenius maps.
    """

    family: str
    parameter: int
    modulus: int
    algebra: str
    base: tuple[int, ...]
    expected_prime_frobenius: tuple[int, ...]
    powered_value: tuple[int, ...]
    defect: tuple[int, ...]
    nontrivial_gcds: tuple[int, ...]
    ring_multiplications: int
    candidate_derived: bool = True
    factor_enumeration: int = 0
    root_branch_enumeration: int = 0
    selective_capacity_query: bool = False

    @property
    def defect_zero(self) -> bool:
        return not any(self.defect)


@dataclass(frozen=True, slots=True)
class AllSplitCompositeControl:
    algebra: str
    modulus: int
    supplied_prime_components: tuple[int, ...]
    all_local_algebras_split: bool
    defect: tuple[int, ...]
    defect_zero: bool


@dataclass(frozen=True, slots=True)
class MixedCapacityControl:
    """Supplied factor witnesses showing the special family is not one-depth."""

    family: str
    parameter: int
    supplied_factors: tuple[int, ...]
    factor_witnesses_valid: bool
    local_ambient_v2: tuple[int, ...]
    local_lift_depths: tuple[int, ...]
    global_special_v2: int


# ---------------------------------------------------------------------------
# Constant-degree Mersenne difference correspondence and formal moments.
# ---------------------------------------------------------------------------


def _poly_add(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    n = max(len(a), len(b))
    out = [0] * n
    for i in range(n):
        out[i] = (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def _poly_scale_shift(
    a: tuple[int, ...], scale: int, shift: int = 0
) -> tuple[int, ...]:
    return (0,) * shift + tuple(int(scale) * value for value in a)


def mersenne_difference_moment_matrix(max_power: int) -> tuple[tuple[int, ...], ...]:
    """Return the exact moment transfer for X^2 - 4 d X - 12 d.

    For one parent difference ``d``, the child power sum P_r(d) satisfies

        P_0 = 2,
        P_1 = 4 d,
        P_r = 4 d P_{r-1} + 12 d P_{r-2}.

    Therefore each next-level moment M'_r is an integer linear combination of
    M_0..M_r and the transfer has fixed dimension independent of branch count.
    """
    max_power = int(max_power)
    if max_power < 0:
        raise ValueError(max_power)
    polys: list[tuple[int, ...]] = [(2,)]
    if max_power:
        polys.append((0, 4))
    for _r in range(2, max_power + 1):
        first = _poly_scale_shift(polys[-1], 4, 1)
        second = _poly_scale_shift(polys[-2], 12, 1)
        polys.append(_poly_add(first, second))
    size = max_power + 1
    rows: list[tuple[int, ...]] = []
    for poly in polys:
        rows.append(tuple(poly[i] if i < len(poly) else 0 for i in range(size)))
    return tuple(rows)


def _mat_vec(
    matrix: tuple[tuple[int, ...], ...], vector: tuple[int, ...]
) -> tuple[int, ...]:
    return tuple(sum(a * b for a, b in zip(row, vector, strict=True)) for row in matrix)


def _mat_mul(
    left: tuple[tuple[int, ...], ...],
    right: tuple[tuple[int, ...], ...],
) -> tuple[tuple[int, ...], ...]:
    n = len(left)
    if n != len(right) or any(len(row) != n for row in left + right):
        raise ValueError("square matrices required")
    columns = tuple(tuple(right[i][j] for i in range(n)) for j in range(n))
    return tuple(
        tuple(sum(a * b for a, b in zip(row, col, strict=True)) for col in columns)
        for row in left
    )


def _matrix_power_counted(
    matrix: tuple[tuple[int, ...], ...],
    exponent: int,
) -> tuple[tuple[tuple[int, ...], ...], int]:
    exponent = int(exponent)
    if exponent < 0:
        raise ValueError(exponent)
    n = len(matrix)
    identity = tuple(tuple(int(i == j) for j in range(n)) for i in range(n))
    result = identity
    base = matrix
    compositions = 0
    power = exponent
    while power:
        if power & 1:
            result = _mat_mul(result, base)
            compositions += 1
        power >>= 1
        if power:
            base = _mat_mul(base, base)
            compositions += 1
    return result, compositions


def difference_moment_jump_audit(
    *,
    levels: int = 32,
    max_power: int = 5,
    root_d: int = 166,
) -> DifferenceMomentJumpAudit:
    levels = int(levels)
    max_power = int(max_power)
    root_d = int(root_d)
    if levels < 0 or max_power < 0:
        raise ValueError((levels, max_power))
    transfer = mersenne_difference_moment_matrix(max_power)
    initial = tuple(root_d**power for power in range(max_power + 1))
    iterative = initial
    for _ in range(levels):
        iterative = _mat_vec(transfer, iterative)
    jumped_matrix, compositions = _matrix_power_counted(transfer, levels)
    jumped = _mat_vec(jumped_matrix, initial)
    return DifferenceMomentJumpAudit(
        levels,
        max_power,
        root_d,
        1 << levels,
        (max_power + 1) ** 2,
        compositions,
        iterative,
        jumped,
    )


# ---------------------------------------------------------------------------
# Bounded factor truth for the actual missing ambient capacity.
# ---------------------------------------------------------------------------


def _truth_prime_factors(value: int) -> tuple[int, ...]:
    """Complete bounded factorization for differential truth labels only."""
    remaining = int(value)
    if remaining < 2:
        return ()
    out: list[int] = []
    while remaining > 1:
        factor = smallest_factor(remaining)
        prime = remaining if factor is None else factor
        while remaining % prime == 0:
            remaining //= prime
            out.append(prime)
    return tuple(out)


def ambient_capacity_truth(family: str, parameter: int) -> AmbientCapacityTruth:
    """Return exact local 2-capacity using factor truth, for audit only.

    Fermat: ord_q(2)=2^(n+1), hence remaining root depth is
        v2(q-1) - (n+1).

    Mersenne reverse LL torus: the terminal trace phase has order four, while
    the local torus has order q-(12/q), hence remaining reverse half-lifts are
        max(0, v2(q-(12/q)) - 2).
    """
    family = str(family)
    parameter = int(parameter)
    if family == "fermat":
        modulus = fermat_number(parameter)
        factors = _truth_prime_factors(modulus)
        baseline = parameter + 1
        ambient = tuple(v2_positive(q - 1) for q in factors)
        depths = tuple(max(0, value - baseline) for value in ambient)
    elif family == "mersenne":
        modulus = mersenne_number(parameter)
        factors = _truth_prime_factors(modulus)
        baseline = 2
        ambient = tuple(v2_positive(q - jacobi_symbol(12, q)) for q in factors)
        depths = tuple(max(0, value - baseline) for value in ambient)
    else:
        raise ValueError(family)
    return AmbientCapacityTruth(
        family, parameter, modulus, factors, ambient, baseline, depths
    )


# ---------------------------------------------------------------------------
# Candidate-derived on-circle N-power action: exact but splitting-blind.
# ---------------------------------------------------------------------------


def formal_phase_frobenius_audit(
    family: str,
    parameter: int,
    lift_level: int,
) -> FormalPhaseFrobeniusAudit:
    """Show why the full N-power phase residue is predetermined on the circle.

    Fermat level k uses B_k = R[z]/(z^(2^k)-2).  The special-number identity
    2^(2^n)=-1 gives z^(2^(n+1+k))=1.  Throughout the relevant lift range,
    F_n == 1 mod 2^(n+1+k), hence z^N=z in B_k even if B_k is nonsplit locally.

    Mersenne reverse level k has formal phase order 2^(k+2).  Since
    M_p == -1 mod 2^(k+2) for k+2<=p, z^N=z^-1 formally, again independent of
    whether the local torus has room for that phase.
    """
    family = str(family)
    parameter = int(parameter)
    lift_level = int(lift_level)
    if lift_level < 0:
        raise ValueError(lift_level)
    if family == "fermat":
        n = parameter
        modulus = fermat_number(n)
        order_exp = n + 1 + lift_level
        if order_exp > (1 << n):
            raise ValueError(("outside-formal-fermat-lift-range", n, lift_level))
        order = 1 << order_exp
        residue = modulus % order
        if residue != 1:
            raise AssertionError((n, lift_level, residue))
        action = "identity"
    elif family == "mersenne":
        p = parameter
        modulus = mersenne_number(p)
        order_exp = lift_level + 2
        if order_exp > p:
            raise ValueError(("outside-formal-mersenne-lift-range", p, lift_level))
        order = 1 << order_exp
        residue = modulus % order
        if residue != order - 1:
            raise AssertionError((p, lift_level, residue))
        action = "inversion"
    else:
        raise ValueError(family)
    return FormalPhaseFrobeniusAudit(
        family,
        parameter,
        lift_level,
        modulus,
        order_exp,
        residue,
        action,
    )


# ---------------------------------------------------------------------------
# Off-circle full CRT-valued Frobenius-defect experiments.
# ---------------------------------------------------------------------------


def _power_in_binomial_algebra(
    base: tuple[int, ...],
    exponent: int,
    degree: int,
    constant: int,
    modulus: int,
) -> tuple[tuple[int, ...], int]:
    """Power in (Z/NZ)[x]/(x^degree-constant), counting ring products."""
    if len(base) != degree:
        raise ValueError((len(base), degree))

    def multiply(first: tuple[int, ...], second: tuple[int, ...]) -> tuple[int, ...]:
        temporary = [0] * (2 * degree - 1)
        for i, left in enumerate(first):
            for j, right in enumerate(second):
                temporary[i + j] = (temporary[i + j] + left * right) % modulus
        for power in range(len(temporary) - 1, degree - 1, -1):
            if temporary[power]:
                temporary[power - degree] = (
                    temporary[power - degree] + temporary[power] * constant
                ) % modulus
        return tuple(temporary[:degree])

    result = (1,) + (0,) * (degree - 1)
    current = tuple(value % modulus for value in base)
    e = int(exponent)
    if e < 0:
        raise ValueError(e)
    products = 0
    while e:
        if e & 1:
            result = multiply(result, current)
            products += 1
        e >>= 1
        if e:
            current = multiply(current, current)
            products += 1
    return result, products


def _nontrivial_coefficient_gcds(
    defect: tuple[int, ...], modulus: int
) -> tuple[int, ...]:
    out: list[int] = []
    for coefficient in defect:
        common = gcd(int(coefficient), int(modulus))
        if 1 < common < modulus and common not in out:
            out.append(common)
    return tuple(out)


def extension_frobenius_probe(family: str, parameter: int) -> ExtensionFrobeniusProbe:
    """Keep the complete candidate-ring defect and every natural coefficient gcd.

    Fermat F4/F5 uses x^4=2: F4 has enough ambient capacity for a fourth root
    of 2, whereas each F5 component has only the first extra square-root layer.

    Mersenne M13/M11 uses the bounded constant-degree control d=166 from the
    difference correspondence.  Jacobi(d,N)=+1 for both candidates, while d is
    locally split for M13 and nonsplit on both M11 factors.

    The fixed bases were chosen *before* reduction and do not enumerate factors
    or roots.  They intentionally demonstrate that natural gcd leakage can occur.
    """
    family = str(family)
    parameter = int(parameter)
    if family == "fermat":
        modulus = fermat_number(parameter)
        degree, constant = 4, 2
        base: tuple[int, ...] = (1, 2, 0, 0)
        expected = base  # prime F4: fully split quartic algebra, Frobenius=id
        algebra = "(Z/NZ)[x]/(x^4-2)"
    elif family == "mersenne":
        modulus = mersenne_number(parameter)
        degree, constant = 2, 166
        base = (1, 2)
        character = jacobi_symbol(constant, modulus)
        expected = (base[0] % modulus, character * base[1] % modulus)
        algebra = "(Z/NZ)[eta]/(eta^2-166)"
    else:
        raise ValueError(family)
    powered, products = _power_in_binomial_algebra(
        base, modulus, degree, constant, modulus
    )
    defect = tuple(
        (value - target) % modulus
        for value, target in zip(powered, expected, strict=True)
    )
    gcds = _nontrivial_coefficient_gcds(defect, modulus)
    return ExtensionFrobeniusProbe(
        family,
        parameter,
        modulus,
        algebra,
        base,
        expected,
        powered,
        defect,
        gcds,
        products,
    )


def all_split_composite_controls() -> tuple[AllSplitCompositeControl, ...]:
    """Counterexamples proving N-power defect is not a splitting predicate.

    The components are supplied explicitly as test fixtures; no factorization
    algorithm is called.  In the quartic control, 2 is a fourth power modulo
    both 73 and 89.  In the quadratic control, 166 is a square modulo both 11
    and 13.  Nevertheless the global composite N-power defect is nonzero.
    """
    rows: list[AllSplitCompositeControl] = []

    components = (73, 89)
    modulus = components[0] * components[1]
    base: tuple[int, ...] = (1, 2, 0, 0)
    degree, constant = 4, 2
    split = all(
        pow(constant, (q - 1) // gcd(degree, q - 1), q) == 1 for q in components
    )
    powered, _ = _power_in_binomial_algebra(base, modulus, degree, constant, modulus)
    defect = tuple(
        (value - target) % modulus for value, target in zip(powered, base, strict=True)
    )
    rows.append(
        AllSplitCompositeControl(
            "(Z/NZ)[x]/(x^4-2)",
            modulus,
            components,
            split,
            defect,
            not any(defect),
        )
    )

    components = (11, 13)
    modulus = components[0] * components[1]
    degree, constant, base = 2, 166, (1, 2)
    split = all(jacobi_symbol(constant, q) == 1 for q in components)
    powered, _ = _power_in_binomial_algebra(base, modulus, degree, constant, modulus)
    defect = tuple(
        (value - target) % modulus for value, target in zip(powered, base, strict=True)
    )
    rows.append(
        AllSplitCompositeControl(
            "(Z/NZ)[eta]/(eta^2-166)",
            modulus,
            components,
            split,
            defect,
            not any(defect),
        )
    )
    return tuple(rows)


def mixed_capacity_controls() -> tuple[MixedCapacityControl, ...]:
    """Show that Fermat/Mersenne forms do not force one local capacity value.

    These are supplied divisors, not discovered factors.  Divisibility is
    checked directly from the defining special-number congruence so the guard
    does not depend on a factor-search implementation.

    F9 already has divisor witnesses with different Fermat ambient valuations
    (16 and 11).  M29 factors completely as 233*1103*2089 and its local LL
    torus valuations are (1,1,3).  Thus neither family collapses the hidden
    capacity vector to one scalar depth.
    """
    f_parameter = 9
    f_factors = (
        2424833,
        7455602825647884208337395736200454918783366342657,
    )
    f_valid = all((pow(2, 1 << f_parameter, q) + 1) % q == 0 for q in f_factors)
    f_ambient = tuple(v2_positive(q - 1) for q in f_factors)
    f_baseline = f_parameter + 1
    f_depths = tuple(max(0, value - f_baseline) for value in f_ambient)

    m_parameter = 29
    m_factors = (233, 1103, 2089)
    m_valid = m_factors[0] * m_factors[1] * m_factors[2] == mersenne_number(
        m_parameter
    ) and all(pow(2, m_parameter, q) == 1 for q in m_factors)
    m_ambient = tuple(v2_positive(q - jacobi_symbol(12, q)) for q in m_factors)
    m_depths = tuple(max(0, value - 2) for value in m_ambient)

    return (
        MixedCapacityControl(
            "fermat",
            f_parameter,
            f_factors,
            f_valid,
            f_ambient,
            f_depths,
            v2_positive(fermat_number(f_parameter) - 1),
        ),
        MixedCapacityControl(
            "mersenne",
            m_parameter,
            m_factors,
            m_valid,
            m_ambient,
            m_depths,
            v2_positive(mersenne_number(m_parameter) + 1),
        ),
    )
