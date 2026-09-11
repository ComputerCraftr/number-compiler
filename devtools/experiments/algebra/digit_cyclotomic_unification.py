"""Cross-family source-digit cyclotomic decomposition audit for v0.26.

The experiment deliberately distinguishes three facts:

1. raw arithmetic operators can be tiny in cyclotomic coordinates;
2. radix normalization is the shared ``base-z`` defect map;
3. finite-field factors are only independent dynamical observers when the
   *normalized* successor descends to them, not merely because raw products do.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass

from number_compiler.arithmetic.fields.radix import digits_lsd, reverse_radix_integer
from number_compiler.arithmetic.functions.finite_unary import analyze_observer
from number_compiler.arithmetic.polynomials.cyclotomic_factor import (
    cyclotomic_factors_mod_prime,
    multiplicative_order_mod,
)
from number_compiler.arithmetic.polynomials.cyclotomic_family import (
    collatz_cyclotomic_step,
    fermat_cyclotomic_step,
    mersenne_cyclotomic_step,
    reverse_add_cyclotomic_step,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock


@dataclass(frozen=True, slots=True)
class NormalizationUnitRow:
    base: int
    coefficient_modulus: int
    tested_orders: int
    unit_orders: tuple[int, ...]
    singular_orders: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class FamilyAuditRow:
    family: str
    cases: int
    components: int
    exact_components: int
    unit_normalizations: int
    recovered_carry_components: int


@dataclass(frozen=True, slots=True)
class FactorSplitRow:
    family: str
    parameter: int
    coefficient_prime: int
    cyclotomic_order: int
    whole_degree: int
    factor_count: int
    factor_degree: int


@dataclass(frozen=True, slots=True)
class FactorClosureRow:
    family: str
    parameter: int
    coefficient_prime: int
    selected_factors: tuple[int, ...]
    classes: int
    conflicts: int
    target_separating: bool


@dataclass(frozen=True, slots=True)
class CarryDependencyProfile:
    family: str
    base: int
    steps: int
    orders: int
    components: int
    unit_components: int
    recovered_components: int


@dataclass(frozen=True, slots=True)
class UnifiedDigitCyclotomicMetrics:
    single_canonical_digit_block: bool
    normalization_units: tuple[NormalizationUnitRow, ...]
    family_audit: tuple[FamilyAuditRow, ...]
    carry_dependency: tuple[CarryDependencyProfile, ...]
    factor_splits: tuple[FactorSplitRow, ...]
    factor_closure: tuple[FactorClosureRow, ...]
    mersenne31_factor_count: int
    mersenne31_factor_degree: int
    all_exact: bool


def normalization_unit_rows(
    *, modulus: int = 32, max_order: int = 16
) -> tuple[NormalizationUnitRow, ...]:
    rows = []
    for base in (2, 3, 4, 10, 16):
        units: list[int] = []
        singular: list[int] = []
        for order in range(1, int(max_order) + 1):
            block = CyclotomicDigitBlock.identity(order, int(modulus))
            (units if block.linear_factor_is_unit(base) else singular).append(order)
        rows.append(
            NormalizationUnitRow(
                base,
                int(modulus),
                int(max_order),
                tuple(units),
                tuple(singular),
            )
        )
    return tuple(rows)


def _reverse_audit() -> FamilyAuditRow:
    value = 196
    cases = components = exact = units = recovered = 0
    orders = (1, 2, 3, 4, 5, 7, 8, 16)
    for _ in range(64):
        for order in orders:
            step = reverse_add_cyclotomic_step(
                value,
                base=10,
                order=order,
                modulus=32,
            )
            components += 1
            exact += int(step.exact)
            units += int(step.normalization.normalization_factor_is_unit)
            recovered += int(step.normalization.carry_recovered_exactly)
        cases += 1
        value += reverse_radix_integer(value, 10)
    return FamilyAuditRow("reverse-add", cases, components, exact, units, recovered)


def _collatz_audit() -> FamilyAuditRow:
    cases = components = exact = units = recovered = 0
    orders = (1, 2, 3, 4, 5, 7, 8, 16)
    for base in (2, 3, 4, 10, 16):
        value = 27
        while value != 1:
            if not (value & 1):
                value //= 2
                continue
            target = None
            for order in orders:
                step = collatz_cyclotomic_step(
                    value,
                    base=base,
                    order=order,
                    modulus=32,
                )
                target = step.target_value
                components += 1
                exact += int(step.exact)
                units += int(step.normalization.normalization_factor_is_unit)
                recovered += int(step.normalization.carry_recovered_exactly)
            cases += 1
            if target is None:
                raise AssertionError(value)
            value = target
    return FamilyAuditRow("collatz", cases, components, exact, units, recovered)


def _mersenne_audit() -> FamilyAuditRow:
    cases = components = exact = units = recovered = 0
    p = 7
    factors = cyclotomic_factors_mod_prime(p, 2)
    for state in range((1 << p) - 1):
        for factor_index in (None, *range(len(factors))):
            step = mersenne_cyclotomic_step(
                state,
                p,
                coefficient_modulus=2,
                factor_index=factor_index,
            )
            components += 1
            exact += int(step.exact)
            units += int(step.normalization.normalization_factor_is_unit)
            recovered += int(step.normalization.carry_recovered_exactly)
        cases += 1
    return FamilyAuditRow("mersenne", cases, components, exact, units, recovered)


def _fermat_audit() -> FamilyAuditRow:
    cases = components = exact = units = recovered = 0
    n = 2
    width = 1 << n
    integer_modulus = (1 << width) + 1
    factors = cyclotomic_factors_mod_prime(2 * width, 3)
    for state in range(integer_modulus):
        specs = [
            {"coefficient_modulus": 2, "local_power": power} for power in (1, 2, width)
        ]
        specs += [
            {"coefficient_modulus": 3, "factor_index": i} for i in range(len(factors))
        ]
        for spec in specs:
            step = fermat_cyclotomic_step(state, n, **spec)
            components += 1
            exact += int(step.exact)
            units += int(step.normalization.normalization_factor_is_unit)
            recovered += int(step.normalization.carry_recovered_exactly)
        cases += 1
    return FamilyAuditRow("fermat", cases, components, exact, units, recovered)


def family_audit_rows() -> tuple[FamilyAuditRow, ...]:
    return (_reverse_audit(), _collatz_audit(), _mersenne_audit(), _fermat_audit())


def carry_dependency_profiles() -> tuple[CarryDependencyProfile, ...]:
    rows = []
    orders = tuple(range(1, 17))

    value = 196
    units = recovered = 0
    steps = 256
    for _ in range(steps):
        for order in orders:
            step = reverse_add_cyclotomic_step(value, base=10, order=order, modulus=32)
            units += int(step.normalization.normalization_factor_is_unit)
            recovered += int(step.normalization.carry_recovered_exactly)
        value += reverse_radix_integer(value, 10)
    rows.append(
        CarryDependencyProfile(
            "reverse-add",
            10,
            steps,
            len(orders),
            steps * len(orders),
            units,
            recovered,
        )
    )

    for base in (2, 3):
        value = 27
        step_count = unit_count = recovered_count = 0
        while value != 1:
            if not (value & 1):
                value //= 2
                continue
            target = None
            for order in orders:
                step = collatz_cyclotomic_step(
                    value, base=base, order=order, modulus=32
                )
                target = step.target_value
                unit_count += int(step.normalization.normalization_factor_is_unit)
                recovered_count += int(step.normalization.carry_recovered_exactly)
            step_count += 1
            assert target is not None
            value = int(target)
        rows.append(
            CarryDependencyProfile(
                "collatz",
                base,
                step_count,
                len(orders),
                step_count * len(orders),
                unit_count,
                recovered_count,
            )
        )
    return tuple(rows)


def factor_split_rows() -> tuple[FactorSplitRow, ...]:
    specs = [
        ("mersenne", 7, 2, 7),
        ("mersenne", 17, 2, 17),
        ("mersenne", 23, 2, 23),
        ("mersenne", 31, 2, 31),
        ("fermat", 2, 3, 8),
        ("fermat", 3, 3, 16),
        ("fermat", 5, 3, 64),
        ("fermat", 5, 7, 64),
    ]
    rows = []
    for family, parameter, prime, order in specs:
        factors = cyclotomic_factors_mod_prime(order, prime)
        degree = multiplicative_order_mod(prime, order)
        rows.append(
            FactorSplitRow(
                family,
                parameter,
                prime,
                order,
                sum(len(factor) - 1 for factor in factors),
                len(factors),
                degree,
            )
        )
    return tuple(rows)


def _special_key(
    state: int,
    *,
    family: str,
    parameter: int,
    prime: int,
    selected: tuple[int, ...],
    factors: tuple[tuple[int, ...], ...],
) -> tuple[tuple[int, ...], ...]:
    if family == "mersenne":
        width = parameter
        digits = digits_lsd(state, 2, width)
        order = parameter
    elif family == "fermat":
        width = 1 << parameter
        scale = 1 << width
        digits = (
            (-1,) + (0,) * (width - 1)
            if state == scale
            else digits_lsd(state, 2, width)
        )
        order = 2 * width
    else:
        raise ValueError(family)
    return tuple(
        CyclotomicDigitBlock.from_coefficients(
            digits,
            order=order,
            modulus=prime,
            factor=factors[index],
            length=width,
        ).residue
        for index in selected
    )


def _factor_closure(
    *,
    family: str,
    parameter: int,
    prime: int,
    selected: tuple[int, ...],
) -> FactorClosureRow:
    if family == "mersenne":
        modulus = (1 << parameter) - 1

        def successor(state: int) -> int:
            return (state * state - 2) % modulus

        def target(state: int) -> bool:
            return state == 0

        order = parameter
    elif family == "fermat":
        width = 1 << parameter
        modulus = (1 << width) + 1

        def successor(state: int) -> int:
            return state * state % modulus

        def target(state: int) -> bool:
            return state == modulus - 1

        order = 2 * width
    else:
        raise ValueError(family)
    factors = cyclotomic_factors_mod_prime(order, prime)
    keys = tuple(
        _special_key(
            state,
            family=family,
            parameter=parameter,
            prime=prime,
            selected=selected,
            factors=factors,
        )
        for state in range(modulus)
    )
    next_keys = tuple(keys[successor(state)] for state in range(modulus))
    audit = analyze_observer(
        keys, next_keys, tuple(bool(target(state)) for state in range(modulus))
    )
    return FactorClosureRow(
        family,
        parameter,
        prime,
        selected,
        audit.classes,
        audit.successor_conflicts,
        audit.target_separating,
    )


def factor_closure_rows() -> tuple[FactorClosureRow, ...]:
    rows = []
    for family, parameter, prime in (("mersenne", 7, 2), ("fermat", 3, 3)):
        order = parameter if family == "mersenne" else 2 * (1 << parameter)
        count = len(cyclotomic_factors_mod_prime(order, prime))
        for mask in range(1, 1 << count):
            selected = tuple(index for index in range(count) if mask >> index & 1)
            rows.append(
                _factor_closure(
                    family=family,
                    parameter=parameter,
                    prime=prime,
                    selected=selected,
                )
            )
    return tuple(rows)


def unified_digit_cyclotomic_metrics() -> UnifiedDigitCyclotomicMetrics:

    units = normalization_unit_rows()
    audit = family_audit_rows()
    dependencies = carry_dependency_profiles()
    splits = factor_split_rows()
    closure = factor_closure_rows()
    m31 = next(
        row for row in splits if row.family == "mersenne" and row.parameter == 31
    )
    all_exact = all(row.components == row.exact_components for row in audit)
    return UnifiedDigitCyclotomicMetrics(
        not any(
            hasattr(__import__("number_compiler", fromlist=[name]), name)
            for name in ("CyclotomicJetBlock", "CyclotomicProjectionBlock")
        ),
        units,
        audit,
        dependencies,
        splits,
        closure,
        m31.factor_count,
        m31.factor_degree,
        bool(all_exact),
    )


def metrics_as_jsonable(metrics: UnifiedDigitCyclotomicMetrics) -> dict[str, object]:
    return asdict(metrics)


__all__ = [
    "CarryDependencyProfile",
    "FactorClosureRow",
    "FactorSplitRow",
    "FamilyAuditRow",
    "NormalizationUnitRow",
    "UnifiedDigitCyclotomicMetrics",
    "carry_dependency_profiles",
    "factor_closure_rows",
    "factor_split_rows",
    "family_audit_rows",
    "metrics_as_jsonable",
    "normalization_unit_rows",
    "unified_digit_cyclotomic_metrics",
]
