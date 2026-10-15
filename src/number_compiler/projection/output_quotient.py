"""Lightweight output-relative quotients for unresolved special sources.

This module is intentionally dependency-light so :mod:`sequence_compiler` can
construct a fail-closed PASS/FAIL coordinate only at a theorem-sensitive output
frontier, without importing convolution, cyclotomic, or oracle machinery.  Raw
Fermat/Mersenne source compilation carries no theorem coordinate at all.
One-shot output fibers are separated from successor-congruent machine quotients,
and a Boolean output coordinate is only constructed after an exact factor-through
audit.
"""

from __future__ import annotations

from collections.abc import Hashable, Iterable, Sequence
from dataclasses import dataclass
from enum import Enum

from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent, Extent


@dataclass(frozen=True, slots=True)
class OutputFiberQuotient:
    """Exact one-shot quotient ``s ~ s' iff pi(s) == pi(s')``."""

    outputs: tuple[int, ...]
    class_ids: tuple[int, ...]
    fibers: tuple[tuple[int, ...], ...]

    @property
    def state_count(self) -> int:
        return len(self.fibers)


def output_fiber_quotient(
    outputs: Sequence[int] | Iterable[int],
) -> OutputFiberQuotient:
    values = tuple(map(int, outputs))
    if not values:
        raise ValueError("empty output domain")
    by_value: dict[int, int] = {}
    fibers: list[list[int]] = []
    classes: list[int] = []
    for index, value in enumerate(values):
        cls = by_value.get(value)
        if cls is None:
            cls = len(fibers)
            by_value[value] = cls
            fibers.append([])
        fibers[cls].append(index)
        classes.append(cls)
    return OutputFiberQuotient(
        values,
        tuple(classes),
        tuple(tuple(fiber) for fiber in fibers),
    )


@dataclass(frozen=True, slots=True)
class ProjectionMachineQuotient:
    """Successor-congruent refinement of an output-relative partition."""

    outputs: tuple[int, ...]
    successors: tuple[int, ...]
    initial_class_ids: tuple[int, ...]
    class_ids: tuple[int, ...]
    refinements: int

    @property
    def initial_state_count(self) -> int:
        return len(set(self.initial_class_ids))

    @property
    def state_count(self) -> int:
        return len(set(self.class_ids))

    @property
    def output_fibers_successor_closed(self) -> bool:
        return self.class_ids == self.initial_class_ids


def canonical_partition_labels(
    signatures: Iterable[Hashable], *, labels: dict[Hashable, int] | None = None
) -> tuple[int, ...]:
    """Assign first-seen labels, optionally extending an existing partition."""
    if labels is None:
        labels = {}
    result: list[int] = []
    for signature in signatures:
        label = labels.get(signature)
        if label is None:
            label = len(labels)
            labels[signature] = label
        result.append(label)
    return tuple(result)


def minimize_projection_machine(
    outputs: Sequence[int] | Iterable[int],
    successors: Sequence[int] | Iterable[int],
) -> ProjectionMachineQuotient:
    """Refine output fibers to the coarsest unary successor congruence.

    This is the deterministic one-successor form of partition refinement.  It
    is intentionally small: callers with richer alphabets should provide the
    corresponding transition signatures rather than assuming output equality
    alone is temporal closure.
    """
    values = tuple(map(int, outputs))
    next_states = tuple(map(int, successors))
    if not values or len(values) != len(next_states):
        raise ValueError((len(values), len(next_states)))
    size = len(values)
    if any(not 0 <= successor < size for successor in next_states):
        raise ValueError(("successor-out-of-range", next_states, size))

    initial = output_fiber_quotient(values).class_ids
    classes = initial
    refinements = 0
    while True:
        signatures = tuple(
            (values[index], classes[next_states[index]]) for index in range(size)
        )
        updated = canonical_partition_labels(signatures)
        if updated == classes:
            break
        classes = updated
        refinements += 1
    return ProjectionMachineQuotient(values, next_states, initial, classes, refinements)


@dataclass(frozen=True, slots=True)
class BinarySourceFactorAudit:
    """Finite-domain proof that an output factors through a supplied source bit."""

    source_bits: tuple[bool, ...]
    outputs: tuple[int, ...]
    false_values: tuple[int, ...]
    true_values: tuple[int, ...]

    @property
    def false_count(self) -> int:
        return sum(not bit for bit in self.source_bits)

    @property
    def true_count(self) -> int:
        return sum(self.source_bits)

    @property
    def both_classes_observed(self) -> bool:
        return self.false_count > 0 and self.true_count > 0

    @property
    def factors_through_source_bit(self) -> bool:
        return len(self.false_values) <= 1 and len(self.true_values) <= 1

    @property
    def coordinate_available(self) -> bool:
        return self.both_classes_observed and self.factors_through_source_bit


def audit_binary_source_factor(
    source_bits: Sequence[bool] | Iterable[bool],
    outputs: Sequence[int] | Iterable[int],
) -> BinarySourceFactorAudit:
    raw_bits = tuple(source_bits)
    if any(not isinstance(bit, bool) for bit in raw_bits):
        raise TypeError("source coordinate must contain literal bool values")
    bits = raw_bits
    values = tuple(map(int, outputs))
    if not bits or len(bits) != len(values):
        raise ValueError((len(bits), len(values)))
    false_values = tuple(
        sorted({value for bit, value in zip(bits, values, strict=True) if not bit})
    )
    true_values = tuple(
        sorted({value for bit, value in zip(bits, values, strict=True) if bit})
    )
    return BinarySourceFactorAudit(bits, values, false_values, true_values)


class SpecialOutputMode(str, Enum):
    CONCRETE = "Concrete"
    GUARDED = "Guarded"
    RESOLVED = "Resolved"


@dataclass(frozen=True, slots=True)
class SpecialBranchMask:
    """Two-sheet admissibility mask used by lazy special-source projections.

    Bits 0 and 1 select the local PASS and FAIL alternatives. Their names alone
    do not establish prime/composite semantics. A caller must supply a checked
    connection before transporting a local constraint to a theorem coordinate.
    """

    bits: int = 0b11

    def __post_init__(self) -> None:
        bits = int(self.bits)
        if bits < 0 or bits > 0b11:
            raise ValueError(bits)
        object.__setattr__(self, "bits", bits)

    @classmethod
    def from_checks(cls, pass_ok: bool, fail_ok: bool) -> SpecialBranchMask:
        if not isinstance(pass_ok, bool) or not isinstance(fail_ok, bool):
            raise TypeError("branch checks must be literal bool values")
        return cls((1 if pass_ok else 0) | (2 if fail_ok else 0))

    @property
    def pass_alive(self) -> bool:
        return bool(self.bits & 0b01)

    @property
    def fail_alive(self) -> bool:
        return bool(self.bits & 0b10)

    @property
    def impossible(self) -> bool:
        return self.bits == 0

    @property
    def resolved(self) -> bool:
        return self.bits in (0b01, 0b10)

    @property
    def failure_bit(self) -> bool | None:
        if self.bits == 0b01:
            return False
        if self.bits == 0b10:
            return True
        return None

    def intersect(self, other: SpecialBranchMask) -> SpecialBranchMask:
        if not isinstance(other, SpecialBranchMask):
            raise TypeError(type(other))
        return SpecialBranchMask(self.bits & other.bits)

    def require_possible(self) -> SpecialBranchMask:
        if self.impossible:
            raise ValueError(
                "all special-source branches violate the source constraints"
            )
        return self


@dataclass(frozen=True, slots=True)
class SpecialSourceShape:
    """The theorem-free binary geometry of one Fermat or Mersenne source.

    These are source facts, not primality facts.  They therefore provide cheap
    branch quotients that may kill an impossible sheet before any factor search,
    terminal certificate, or idempotent selector is requested.
    """

    family: str
    parameter: int

    def __post_init__(self) -> None:
        family = str(self.family)
        parameter = int(self.parameter)
        if family not in ("fermat", "mersenne"):
            raise ValueError(family)
        if parameter < 0 or (family == "mersenne" and parameter <= 0):
            raise ValueError(parameter)
        object.__setattr__(self, "family", family)
        object.__setattr__(self, "parameter", parameter)

    @property
    def bit_length(self) -> Extent:
        return (
            DyadicExtent(self.parameter, 1)
            if self.family == "fermat"
            else self.parameter
        )

    @property
    def top_bit(self) -> Extent:
        return (
            DyadicExtent(self.parameter)
            if self.family == "fermat"
            else self.parameter - 1
        )

    @property
    def boundary_sign(self) -> int:
        """Return -1 for Fermat negacyclic and +1 for Mersenne cyclic closure."""
        return -1 if self.family == "fermat" else 1

    @property
    def odd(self) -> bool:
        return True

    def digit(self, index: int) -> int:
        index = int(index)
        if index < 0:
            raise ValueError(index)
        if self.family == "fermat":
            return int(index == 0 or self.top_bit == index)
        return int(index < self.parameter)

    def digit_mask(
        self, index: int, pass_digit: int, fail_digit: int
    ) -> SpecialBranchMask:
        expected = self.digit(index)
        a, b = int(pass_digit), int(fail_digit)
        if a not in (0, 1) or b not in (0, 1):
            raise ValueError((a, b))
        return SpecialBranchMask.from_checks(a == expected, b == expected)

    def length_mask(self, pass_length: int, fail_length: int) -> SpecialBranchMask:
        expected = self.bit_length
        a, b = int(pass_length), int(fail_length)
        if a <= 0 or b <= 0:
            raise ValueError((a, b))
        return SpecialBranchMask.from_checks(a == expected, b == expected)

    def odd_mask(self, pass_value: int, fail_value: int) -> SpecialBranchMask:
        a, b = int(pass_value), int(fail_value)
        if min(a, b) < 0:
            raise ValueError((a, b))
        return SpecialBranchMask.from_checks(bool(a & 1), bool(b & 1))

    def boundary_mask(self, pass_sign: int, fail_sign: int) -> SpecialBranchMask:
        expected = self.boundary_sign
        a, b = int(pass_sign), int(fail_sign)
        if a not in (-1, 1) or b not in (-1, 1):
            raise ValueError((a, b))
        return SpecialBranchMask.from_checks(a == expected, b == expected)

    @staticmethod
    def carry_mask(
        expected: int, pass_carry: int, fail_carry: int
    ) -> SpecialBranchMask:
        """Intersect an independently known carry checkpoint with both sheets."""
        expected, a, b = int(expected), int(pass_carry), int(fail_carry)
        return SpecialBranchMask.from_checks(a == expected, b == expected)

    def constrain(
        self,
        *,
        digit_checks: Sequence[tuple[int, int, int]] = (),
        lengths: tuple[int, int] | None = None,
        odd_values: tuple[int, int] | None = None,
        boundary_signs: tuple[int, int] | None = None,
        carry_check: tuple[int, int, int] | None = None,
    ) -> SpecialBranchMask:
        """Intersect multiple cheap source invariants into one two-bit mask."""
        mask = SpecialBranchMask()
        if lengths is not None:
            mask = mask.intersect(self.length_mask(*lengths))
        if odd_values is not None:
            mask = mask.intersect(self.odd_mask(*odd_values))
        if boundary_signs is not None:
            mask = mask.intersect(self.boundary_mask(*boundary_signs))
        if carry_check is not None:
            mask = mask.intersect(self.carry_mask(*carry_check))
        for index, pass_digit, fail_digit in digit_checks:
            mask = mask.intersect(self.digit_mask(index, pass_digit, fail_digit))
        return mask.require_possible()


@dataclass(frozen=True, slots=True)
class SpecialSourceGuard:
    """Output-frontier unresolved PASS/FAIL coordinate for one special term.

    Raw Fermat/Mersenne source compilation never constructs this guard.  A
    theorem-sensitive projection creates it lazily only after theorem-free source
    constraints have had the opportunity to kill impossible sheets.

    ``failure_bit=False`` means the terminal PASS/prime sheet and ``True`` the
    FAIL/composite sheet.  ``None`` is the fail-closed unresolved state.  The
    guard does not decide primality; it only lets an independently proved
    output-factor audit postpone or specialize that decision without guessing.
    """

    family: str
    parameter: int
    failure_bit: bool | None
    method: str

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne"):
            raise ValueError(self.family)
        if self.failure_bit is not None and not isinstance(self.failure_bit, bool):
            raise TypeError("failure_bit must be bool or None")
        if int(self.parameter) < 0 or (
            self.family == "mersenne" and int(self.parameter) <= 0
        ):
            raise ValueError(self.parameter)
        if not str(self.method):
            raise ValueError(self.method)
        object.__setattr__(self, "parameter", int(self.parameter))
        object.__setattr__(self, "method", str(self.method))

    @classmethod
    def from_certificate_status(
        cls,
        family: str,
        parameter: int,
        status: str,
        method: str,
    ) -> SpecialSourceGuard:
        status = str(status)
        if status == "prime":
            bit = False
        elif status == "composite":
            bit = True
        elif status == "unknown":
            bit = None
        else:
            raise ValueError(status)
        return cls(str(family), int(parameter), bit, str(method))

    @property
    def mode(self) -> SpecialOutputMode:
        return (
            SpecialOutputMode.GUARDED
            if self.failure_bit is None
            else SpecialOutputMode.RESOLVED
        )

    @property
    def resolved(self) -> bool:
        return self.failure_bit is not None

    def project(self, audit: BinarySourceFactorAudit) -> BinaryOutputCoordinate:
        """Apply a proved output-relative quotient to this source coordinate."""
        return BinaryOutputCoordinate.from_factor_audit(
            audit,
            resolved_bit=self.failure_bit,
        )

    def project_branch_values(
        self,
        pass_value: int,
        fail_value: int,
    ) -> BinaryOutputCoordinate:
        """Minimal one-coordinate quotient for exact PASS/FAIL branch outputs."""
        audit = audit_binary_source_factor(
            (False, True),
            (int(pass_value), int(fail_value)),
        )
        return self.project(audit)

    def project_digit(
        self,
        pass_value: int,
        fail_value: int,
        index: int,
    ) -> BinaryOutputCoordinate:
        """Digit quotient: dependency is the selected bit of ``pass XOR fail``."""
        index = int(index)
        if index < 0 or min(int(pass_value), int(fail_value)) < 0:
            raise ValueError((pass_value, fail_value, index))
        return self.project_branch_values(
            (int(pass_value) >> index) & 1,
            (int(fail_value) >> index) & 1,
        )

    def project_length(
        self,
        pass_value: int,
        fail_value: int,
    ) -> BinaryOutputCoordinate:
        """Canonical binary-length quotient for exact PASS/FAIL branch values."""
        a, b = int(pass_value), int(fail_value)
        if min(a, b) < 0:
            raise ValueError((a, b))
        return self.project_branch_values(
            max(1, a.bit_length()), max(1, b.bit_length())
        )

    def project_carry(
        self,
        pass_carry: int,
        fail_carry: int,
    ) -> BinaryOutputCoordinate:
        """Boundary-carry quotient; equal carries collapse immediately."""
        return self.project_branch_values(int(pass_carry), int(fail_carry))


@dataclass(frozen=True, slots=True)
class BinaryOutputCoordinate:
    """One exact Boolean output coordinate after a factor-through proof."""

    false_value: int
    true_value: int
    resolved_bit: bool | None = None

    def __post_init__(self) -> None:
        if self.resolved_bit is not None and not isinstance(self.resolved_bit, bool):
            raise TypeError("resolved_bit must be bool or None")
        object.__setattr__(self, "false_value", int(self.false_value))
        object.__setattr__(self, "true_value", int(self.true_value))

    @classmethod
    def from_factor_audit(
        cls,
        audit: BinarySourceFactorAudit,
        *,
        resolved_bit: bool | None = None,
    ) -> BinaryOutputCoordinate:
        if not isinstance(audit, BinarySourceFactorAudit):
            raise TypeError(type(audit))
        if not audit.coordinate_available:
            raise ValueError(
                "output is not proved to factor through both Boolean source classes"
            )
        return cls(audit.false_values[0], audit.true_values[0], resolved_bit)

    @property
    def derivative(self) -> int:
        return self.true_value - self.false_value

    @property
    def separates_source_bit(self) -> bool:
        return self.false_value != self.true_value

    @property
    def quotient_states(self) -> int:
        return 2 if self.separates_source_bit else 1

    @property
    def mode(self) -> SpecialOutputMode:
        if not self.separates_source_bit:
            return SpecialOutputMode.CONCRETE
        if self.resolved_bit is None:
            return SpecialOutputMode.GUARDED
        return SpecialOutputMode.RESOLVED

    @property
    def value(self) -> int:
        if self.mode is SpecialOutputMode.GUARDED:
            raise ValueError("guarded coordinate has no concrete value")
        if not self.separates_source_bit:
            return self.false_value
        return self.true_value if self.resolved_bit else self.false_value

    def resolve(self, source_bit: bool) -> BinaryOutputCoordinate:
        if not isinstance(source_bit, bool):
            raise TypeError("source_bit must be bool")
        return BinaryOutputCoordinate(
            self.false_value,
            self.true_value,
            source_bit,
        )

    def restrict(self, mask: SpecialBranchMask) -> BinaryOutputCoordinate:
        """Specialize this coordinate when cheap source constraints kill a sheet."""
        if not isinstance(mask, SpecialBranchMask):
            raise TypeError(type(mask))
        mask.require_possible()
        bit = mask.failure_bit
        if bit is None:
            return self
        if self.resolved_bit is not None and self.resolved_bit is not bit:
            raise ValueError(
                "source constraint contradicts an already resolved coordinate"
            )
        return self.resolve(bit)

    def recover_source_bit(self, concrete_value: int) -> bool:
        """Hard lower-bound inverse when this coordinate separates the classes."""
        if not self.separates_source_bit:
            raise ValueError("coordinate does not separate the source classes")
        value = int(concrete_value)
        if value == self.false_value:
            return False
        if value == self.true_value:
            return True
        raise ValueError((value, self.false_value, self.true_value))


__all__ = [
    "BinaryOutputCoordinate",
    "BinarySourceFactorAudit",
    "OutputFiberQuotient",
    "ProjectionMachineQuotient",
    "SpecialBranchMask",
    "SpecialOutputMode",
    "SpecialSourceGuard",
    "SpecialSourceShape",
    "audit_binary_source_factor",
    "minimize_projection_machine",
    "output_fiber_quotient",
]
