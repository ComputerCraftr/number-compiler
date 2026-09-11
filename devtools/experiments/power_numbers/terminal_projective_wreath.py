"""Projective Cayley and wreath-section research for terminal Frobenius chunks.

This module tests the nonlinear/transducer route that remains after the terminal
Frobenius chunk quotient.  It does two exact things:

* Cayley-homogenize the Lucas trace map ``x -> x^2-2`` as
  ``(A:B) -> (4AB:(A+B)^2)``.  In ``S=A+B, D=B-A`` coordinates this is
  ``S -> 2S^2-D^2, D -> D^2``; the difference coordinate is therefore a
  completely known dyadic clock.
* Identify a local Frobenius stride ``k`` with the binary odometer action on the
  rooted 2-tree.  The exact wreath recursion is

      tau_(2a)   = (tau_a, tau_a)
      tau_(2a+1) = (tau_a, tau_(a+1)) sigma.

  Consequently, when the root permutation is trivial (the current lift passes),
  the section is exactly ``tau_(k/2)``, which is the Frobenius stride at the
  doubled boundary.  This proves the desired conditional section formula
  ``Section(Frob_m) = Frob_(2m)`` without expanding the tree.

Factor truth is used only by the local audit wrapper to label ``k``.  No function
in this module claims to extract the section from an unfactored candidate; that
candidate-to-section map remains the theorem frontier.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from typing import Never

from devtools.experiments.power_numbers.terminal_frobenius_chunk import (
    special_local_frobenius_chunk_audit,
)
from number_compiler.arithmetic.fields.binary_piecewise import (
    BinaryBranchDecision,
    BinaryPiecewiseHandler,
)
from number_compiler.sequences.power_numbers.numbers import (
    fermat_number,
    mersenne_number,
)


@dataclass(frozen=True, slots=True)
class ProjectiveLucasState:
    """Division-free homogeneous Cayley coordinate for one Lucas trace state."""

    modulus: int
    a: int
    b: int
    steps: int = 0

    def __post_init__(self) -> None:
        modulus = int(self.modulus)
        if modulus <= 1 or not (modulus & 1):
            raise ValueError(modulus)
        object.__setattr__(self, "modulus", modulus)
        object.__setattr__(self, "a", int(self.a) % modulus)
        object.__setattr__(self, "b", int(self.b) % modulus)
        object.__setattr__(self, "steps", int(self.steps))
        if self.steps < 0:
            raise ValueError(self.steps)

    @property
    def sum_coordinate(self) -> int:
        return (self.a + self.b) % self.modulus

    @property
    def difference_coordinate(self) -> int:
        return (self.b - self.a) % self.modulus

    @property
    def target_gcd(self) -> int:
        """Natural packet for the projective target ``x=0 <=> A+B=0``."""
        return gcd(self.sum_coordinate, self.modulus)

    @property
    def difference_gcd(self) -> int:
        return gcd(self.difference_coordinate, self.modulus)

    def trace(self) -> int | None:
        """Return ``x=2(A+B)/(B-A)`` when the projective denominator is a unit."""
        d = self.difference_coordinate
        if gcd(d, self.modulus) != 1:
            return None
        return (2 * self.sum_coordinate * pow(d, -1, self.modulus)) % self.modulus

    def double(self) -> ProjectiveLucasState:
        """Exact Cayley lift of ``x -> x^2-2`` with no division."""
        s = self.sum_coordinate
        return ProjectiveLucasState(
            self.modulus,
            4 * self.a * self.b,
            s * s,
            self.steps + 1,
        )

    def double_sd(self) -> tuple[int, int]:
        """Return the same next state directly in ``(S,D)`` coordinates."""
        s, d, n = self.sum_coordinate, self.difference_coordinate, self.modulus
        return (2 * s * s - d * d) % n, (d * d) % n


@dataclass(frozen=True, slots=True)
class ProjectiveLucasAudit:
    family: str
    parameter: int
    modulus: int
    initial_pair: tuple[int, int]
    initial_trace: int
    steps_checked: int
    cayley_commutes: bool
    difference_clock_exact: bool
    proper_target_gcds: tuple[tuple[int, int], ...]
    terminal_target_gcd: int
    polynomial_terms_materialized: int = 0
    factor_enumeration: int = 0


def _projective_seed(family: str) -> tuple[int, int, int]:
    fam = str(family)
    if fam == "fermat":
        # t=(x-2)/(x+2)=3/7 for x=5.
        return 3, 7, 5
    if fam == "mersenne":
        # t=(x-2)/(x+2)=1/3 for x=4.
        return 1, 3, 4
    raise ValueError(fam)


def projective_lucas_audit(
    family: str, parameter: int, steps: int
) -> ProjectiveLucasAudit:
    """Check the projective Cayley quotient against the scalar Lucas recurrence."""
    fam, par, count = str(family), int(parameter), int(steps)
    if count < 0:
        raise ValueError(count)
    modulus = fermat_number(par) if fam == "fermat" else mersenne_number(par)
    a0, b0, x = _projective_seed(fam)
    state = ProjectiveLucasState(modulus, a0, b0)
    initial_d = state.difference_coordinate
    proper: list[tuple[int, int]] = []
    commute = clock = True
    for j in range(count + 1):
        trace = state.trace()
        commute &= trace == x
        expected_d = pow(initial_d, 1 << j, modulus)
        clock &= state.difference_coordinate == expected_d
        g = state.target_gcd
        if 1 < g < modulus:
            proper.append((j, g))
        if j != count:
            sd_next = state.double_sd()
            state = state.double()
            commute &= (state.sum_coordinate, state.difference_coordinate) == sd_next
            x = (x * x - 2) % modulus
    return ProjectiveLucasAudit(
        fam,
        par,
        modulus,
        (a0, b0),
        _projective_seed(fam)[2],
        count,
        commute,
        clock,
        tuple(proper),
        state.target_gcd,
    )


ODOMETER_BINARY_HANDLER = BinaryPiecewiseHandler("frobenius-odometer")


@dataclass(frozen=True, slots=True)
class OdometerSectionStep:
    """One binary self-branching odometer step using the shared dispatcher."""

    stride: int
    decision: BinaryBranchDecision
    status: str
    next_stride: int | None = None


def odometer_section_step(stride: int) -> OdometerSectionStep:
    """Consume one root bit: ZERO sections to ``k//2``; ONE terminates FAIL."""
    k = int(stride)
    if k < 0:
        raise ValueError(k)
    decision = (
        BinaryBranchDecision.zero("odometer-root-permutation")
        if (k & 1) == 0
        else BinaryBranchDecision.one("odometer-root-permutation")
    )
    return ODOMETER_BINARY_HANDLER.dispatch(
        decision,
        zero_branch=lambda d: OdometerSectionStep(k, d, "CONTINUE", k >> 1),
        one_branch=lambda d: OdometerSectionStep(k, d, "FAIL", None),
        split_branch=_unreachable_branch,
        unknown_branch=_unreachable_branch,
    )


@dataclass(frozen=True, slots=True)
class BinaryOdometerSection:
    """One exact wreath-recursion node for addition by a nonnegative stride."""

    stride: int
    root_permutation: int
    left_section_stride: int
    right_section_stride: int

    @property
    def root_passes(self) -> bool:
        return self.root_permutation == 0

    @property
    def next_boundary_stride(self) -> int | None:
        """Conditional section relevant after a successful current lift."""
        return self.left_section_stride if self.root_passes else None


def odometer_wreath_section(stride: int) -> BinaryOdometerSection:
    """Return ``tau_k`` in ``Aut(T_2) = (Aut x Aut) semidirect C2`` form."""
    k = int(stride)
    if k < 0:
        raise ValueError(k)
    a, bit = divmod(k, 2)
    return BinaryOdometerSection(k, bit, a, a if bit == 0 else a + 1)


def odometer_identity_on_prefix(stride: int, depth: int) -> bool:
    """Identity on the first ``depth`` levels iff ``2^depth`` divides stride."""
    k, depth = int(stride), int(depth)
    if k < 0 or depth < 0:
        raise ValueError((k, depth))
    return depth == 0 or (k & ((1 << depth) - 1)) == 0


def conditional_odometer_section(stride: int, passed_levels: int) -> int | None:
    """Return the depth-r section only when the first r root actions are trivial."""
    k, r = int(stride), int(passed_levels)
    if k < 0 or r < 0:
        raise ValueError((k, r))
    if not odometer_identity_on_prefix(k, r):
        return None
    return k >> r


@dataclass(frozen=True, slots=True)
class LocalFrobeniusWreathAudit:
    family: str
    parameter: int
    supplied_prime_factor: int
    start_level: int
    span: int
    reaches_start_boundary: bool
    stride_quotient: int | None
    root_permutation: int | None
    left_section_stride: int | None
    right_section_stride: int | None
    next_boundary_stride: int | None
    direct_next_boundary_stride: int | None
    conditional_section_formula_exact: bool
    identity_on_span: bool
    chunk_all_pass: bool
    tree_nodes_materialized: int
    one_level_replays: int
    factor_truth_only: bool = True


def local_frobenius_wreath_audit(
    family: str,
    parameter: int,
    start_level: int,
    span: int,
    supplied_prime_factor: int,
) -> LocalFrobeniusWreathAudit:
    """Verify the conditional section formula against the existing local chunk law."""
    row = special_local_frobenius_chunk_audit(
        family,
        parameter,
        start_level,
        span,
        supplied_prime_factor,
    )
    if not row.reaches_start_boundary:
        return LocalFrobeniusWreathAudit(
            row.family,
            row.parameter,
            row.supplied_prime_factor,
            row.start_level,
            row.span,
            False,
            None,
            None,
            None,
            None,
            None,
            None,
            True,
            False,
            row.all_levels_pass,
            0,
            0,
        )

    assert row.stride_quotient is not None
    k = row.stride_quotient
    step = odometer_section_step(k)
    wreath = odometer_wreath_section(k)
    if (step.decision.kind == "ZERO") != wreath.root_passes:
        raise AssertionError((k, step, wreath))
    if step.next_stride != wreath.next_boundary_stride:
        raise AssertionError((k, step, wreath))
    direct_next = None
    exact = True
    if row.span > 1:
        nxt = special_local_frobenius_chunk_audit(
            row.family,
            row.parameter,
            row.start_level + 1,
            row.span - 1,
            row.supplied_prime_factor,
        )
        if wreath.root_passes:
            if not nxt.reaches_start_boundary:
                exact = False
            else:
                assert nxt.stride_quotient is not None
                direct_next = nxt.stride_quotient
                exact = direct_next == wreath.next_boundary_stride
        else:
            # An odd stride has exactly the current boundary valuation, so the
            # doubled boundary cannot be reached.
            exact = not nxt.reaches_start_boundary
    identity = odometer_identity_on_prefix(k, row.span)
    exact &= identity == row.all_levels_pass
    return LocalFrobeniusWreathAudit(
        row.family,
        row.parameter,
        row.supplied_prime_factor,
        row.start_level,
        row.span,
        True,
        k,
        wreath.root_permutation,
        wreath.left_section_stride,
        wreath.right_section_stride,
        wreath.next_boundary_stride,
        direct_next,
        exact,
        identity,
        row.all_levels_pass,
        0,
        0,
    )


@dataclass(frozen=True, slots=True)
class CandidateFrobeniusSectionProbe:
    """Fail-honest status of the still-missing candidate-to-section constructor."""

    family: str
    parameter: int
    start_level: int
    span: int
    status: str = "UNKNOWN"
    method: str = "candidate-derived-wreath-section-unavailable"
    candidate_derived_section: int | None = None
    factor_enumeration: int = 0
    tree_nodes_materialized: int = 0
    one_level_replays: int = 0


def candidate_frobenius_section_probe(
    family: str,
    parameter: int,
    start_level: int,
    span: int,
) -> CandidateFrobeniusSectionProbe:
    fam, par, start, span = str(family), int(parameter), int(start_level), int(span)
    if fam not in ("fermat", "mersenne") or par < 0 or start < 1 or span < 1:
        raise ValueError((fam, par, start, span))
    # The control skeleton is shared with Collatz, but the candidate-derived
    # discriminator is still the theorem frontier.  UNKNOWN must short-circuit
    # before either semantic branch executes.
    decision = BinaryBranchDecision.unknown(
        "candidate-derived-wreath-section-unavailable"
    )
    return ODOMETER_BINARY_HANDLER.dispatch(
        decision,
        zero_branch=_unreachable_branch,
        one_branch=_unreachable_branch,
        split_branch=_unreachable_branch,
        unknown_branch=lambda d: CandidateFrobeniusSectionProbe(
            fam,
            par,
            start,
            span,
            method=d.method,
        ),
    )


__all__ = [
    "ODOMETER_BINARY_HANDLER",
    "BinaryOdometerSection",
    "CandidateFrobeniusSectionProbe",
    "LocalFrobeniusWreathAudit",
    "OdometerSectionStep",
    "ProjectiveLucasAudit",
    "ProjectiveLucasState",
    "candidate_frobenius_section_probe",
    "conditional_odometer_section",
    "local_frobenius_wreath_audit",
    "odometer_identity_on_prefix",
    "odometer_section_step",
    "odometer_wreath_section",
    "projective_lucas_audit",
]


def _unreachable_branch(decision: BinaryBranchDecision) -> Never:
    raise AssertionError(decision)
