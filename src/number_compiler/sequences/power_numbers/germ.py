"""Constraint-pulled binary germ for Fermat/Mersenne theorem frontiers.

The old germ split deterministic dyadic transport from one detached support
observation performed after powering.  That ordering was wrong for a lazy
compiler: source/output constraints discovered while constructing a powered
block must flow back to the unresolved theorem sheet immediately.

This module therefore carries two compact objects together:

* ``SquareTileAction`` -- the shared universal dyadic square/trace transport,
  powered by the shared binary monoid; and
* :class:`SpecialGermConstraintState` -- a two-sheet PASS/FAIL survivor mask
  plus, when available, the candidate-ring support gcd of a proved defect.

The PASS/FAIL sheet is invariant under the deterministic transport, so pulling
an output mask back through a block is just exact mask intersection.  CRT
support is invariant by candidate component as well, so adjacent defect ideals
compose by gcd.  Neither operation enumerates factors or local slots.

A :class:`SpecialGermPlan` never performs a detached support scan.  If its
accumulated constraints remain unresolved, ``probe()`` returns ``UNKNOWN``.
The demanded theorem path preserves that unresolved result. Research recurrence
oracles and historical factor-slot scans are not production fallbacks.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from math import gcd

from number_compiler.arithmetic.fields.morphism_core import (
    binary_power_composition_count,
)
from number_compiler.arithmetic.polynomials.arithmetic_tile import (
    SquareTileAction,
)
from number_compiler.projection.output_quotient import SpecialBranchMask
from number_compiler.sequences.power_numbers.frobenius_chunk import (
    SpecialFrobeniusChunkResult,
    SpecialFrobeniusChunkSpec,
    SpecialFrobeniusDefectPacket,
)


@dataclass(frozen=True, slots=True)
class SpecialGermConstraintState:
    """Compact constraints already pulled back to the source theorem sheet.

    ``mask`` uses bit 0 for PASS/prime and bit 1 for FAIL/composite.  Optional
    ``support_gcd`` is the support of a candidate-derived zero/unit defect:
    ``N`` means every CRT component passes, ``1`` means every component fails,
    and a proper divisor means mixed support and therefore compositeness.

    The state is constant-rank.  Composing arbitrarily many blocks never adds
    a new Boolean dimension and never stores a list of factor slots.
    """

    mask: SpecialBranchMask = field(default_factory=SpecialBranchMask)
    support_modulus: int | None = None
    support_gcd: int | None = None
    checks: int = 0
    pullbacks: int = 0
    method: str = ""
    candidate_derived: bool = True

    def __post_init__(self) -> None:
        if not isinstance(self.mask, SpecialBranchMask):
            raise TypeError(type(self.mask))
        checks, pullbacks = int(self.checks), int(self.pullbacks)
        if checks < 0 or pullbacks < 0:
            raise ValueError((checks, pullbacks))
        object.__setattr__(self, "checks", checks)
        object.__setattr__(self, "pullbacks", pullbacks)
        method = str(self.method)
        object.__setattr__(self, "method", method)
        if not isinstance(self.candidate_derived, bool):
            raise TypeError("candidate_derived must be bool")

        modulus, support = self.support_modulus, self.support_gcd
        if modulus is None:
            if support is not None:
                raise ValueError((modulus, support))
            return
        modulus = int(modulus)
        if modulus <= 1 or not (modulus & 1):
            raise ValueError(modulus)
        if support is None:
            raise ValueError((modulus, support))
        support = int(support)
        if not 1 <= support <= modulus or modulus % support:
            raise ValueError((modulus, support))
        object.__setattr__(self, "support_modulus", modulus)
        object.__setattr__(self, "support_gcd", support)

    @classmethod
    def identity(cls) -> SpecialGermConstraintState:
        return cls()

    @classmethod
    def from_mask(
        cls,
        mask: SpecialBranchMask,
        *,
        method: str,
        candidate_derived: bool = True,
    ) -> SpecialGermConstraintState:
        if not isinstance(mask, SpecialBranchMask):
            raise TypeError(type(mask))
        mask.require_possible()
        return cls(
            mask=mask,
            checks=1,
            method=str(method),
            candidate_derived=bool(candidate_derived),
        )

    @classmethod
    def from_defect(
        cls,
        modulus: int,
        defect: int,
        *,
        method: str,
        candidate_derived: bool = True,
    ) -> SpecialGermConstraintState:
        modulus = int(modulus)
        if modulus <= 1 or not (modulus & 1):
            raise ValueError(modulus)
        support = gcd(modulus, int(defect))
        return cls(
            support_modulus=modulus,
            support_gcd=support,
            checks=1,
            method=str(method),
            candidate_derived=bool(candidate_derived),
        )

    def then(
        self, downstream: SpecialGermConstraintState
    ) -> SpecialGermConstraintState:
        """Pull downstream evidence back and intersect it with this block.

        The unresolved theorem coordinate does not change under the dyadic
        transport, hence the Boolean pullback is the identity map on the sheet.
        Candidate CRT components are likewise preserved as components, so
        support ideals intersect by gcd.
        """
        if not isinstance(downstream, SpecialGermConstraintState):
            raise TypeError(type(downstream))
        mask = self.mask.intersect(downstream.mask)
        if mask.impossible:
            raise ValueError("adjacent germ constraints eliminate every theorem sheet")

        if self.support_modulus is None:
            modulus, support = downstream.support_modulus, downstream.support_gcd
        elif downstream.support_modulus is None:
            modulus, support = self.support_modulus, self.support_gcd
        else:
            if self.support_modulus != downstream.support_modulus:
                raise ValueError((self.support_modulus, downstream.support_modulus))
            modulus = self.support_modulus
            if self.support_gcd is None or downstream.support_gcd is None:
                raise AssertionError("support modulus requires gcd")
            support = gcd(int(self.support_gcd), int(downstream.support_gcd))

        if not self.method:
            method = downstream.method
        elif not downstream.method or self.method == downstream.method:
            method = self.method
        else:
            method = "mixed-constraint-pullback"
        return SpecialGermConstraintState(
            mask=mask,
            support_modulus=modulus,
            support_gcd=support,
            checks=self.checks + downstream.checks,
            # Every downstream check crosses the upstream transport once.
            pullbacks=self.pullbacks + downstream.pullbacks + downstream.checks,
            method=method,
            candidate_derived=self.candidate_derived and downstream.candidate_derived,
        )

    @property
    def constraint_failure_bit(self) -> bool | None:
        """Classify a constant-rank pulled-back constraint state, if possible."""
        bit = self.mask.failure_bit
        support_bit = None
        if self.support_gcd is not None:
            support_bit = self.support_gcd != self.support_modulus
        if bit is not None and support_bit is not None and bit != support_bit:
            raise ValueError(
                "theorem-sheet mask contradicts pulled-back support evidence"
            )
        return bit if bit is not None else support_bit

    @property
    def decided(self) -> bool:
        return self.mask.resolved

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "special-germ-constraints",
            self.mask.bits,
            self.support_modulus,
            self.support_gcd,
            self.method,
        )

    def result(self, spec: SpecialFrobeniusChunkSpec) -> SpecialFrobeniusChunkResult:
        """Describe algebraic constraint state without authenticating it.

        Masks and defect fields are caller-constructible observations.  Their
        abstract classification is useful for checking the support algebra,
        but the candidate-derived bit is reserved for a separate source-bound
        verification at the plan probe boundary.
        """
        if not isinstance(spec, SpecialFrobeniusChunkSpec):
            raise TypeError(type(spec))
        method = (
            "constraint-pullback:" + self.method
            if self.method
            else "constraint-pullback-unresolved"
        )
        bit = self.mask.failure_bit
        support = self.support_gcd
        modulus = self.support_modulus

        support_status: str | None = None
        if support is not None and modulus is not None:
            support_status = (
                "ALL_PASS"
                if support == modulus
                else "ALL_FAIL"
                if support == 1
                else "SPLIT"
            )

        if bit is not None and support_status is not None:
            support_failure = support_status != "ALL_PASS"
            if bit != support_failure:
                raise ValueError(
                    "theorem-sheet mask contradicts accumulated support evidence"
                )

        if support_status == "SPLIT":
            return SpecialFrobeniusChunkResult(
                spec,
                "SPLIT",
                method,
                gcd_packet=support,
                candidate_derived=False,
            )
        if support_status == "ALL_PASS" or bit is False:
            return SpecialFrobeniusChunkResult(
                spec,
                "ALL_PASS",
                method,
                True,
                candidate_derived=False,
            )
        if support_status == "ALL_FAIL" or bit is True:
            return SpecialFrobeniusChunkResult(
                spec,
                "ALL_FAIL",
                method,
                False,
                candidate_derived=False,
            )
        return SpecialFrobeniusChunkResult(
            spec,
            "UNKNOWN",
            method,
            candidate_derived=False,
        )


# Compatibility name for callers of the former power-number-local wrapper.
# Production plans now instantiate the shared arithmetic action directly.
SpecialGermTransfer = SquareTileAction


@dataclass(frozen=True, slots=True)
class SpecialGermPlan:
    """Binary-powered transport and its source-pulled constraint state.

    There is deliberately no detached support observation count.  A plan is
    decided only by evidence already accumulated into ``constraints``.
    """

    spec: SpecialFrobeniusChunkSpec
    transfer: SquareTileAction
    constraints: SpecialGermConstraintState = field(
        default_factory=SpecialGermConstraintState.identity
    )
    one_level_replays: int = 0
    factor_enumeration: int = 0
    root_tree_nodes: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.spec, SpecialFrobeniusChunkSpec):
            raise TypeError(type(self.spec))
        if not isinstance(self.constraints, SpecialGermConstraintState):
            raise TypeError(type(self.constraints))
        if (
            self.transfer.family != self.spec.family
            or self.transfer.span != self.spec.span
        ):
            raise ValueError((self.spec, self.transfer))
        if any((self.one_level_replays, self.factor_enumeration, self.root_tree_nodes)):
            raise ValueError("production germ plan cannot hide replay/enumeration work")

    @property
    def support_observations(self) -> int:
        """Compatibility metric: detached support observations are now zero."""
        return 0

    @property
    def binary_compositions(self) -> int:
        return self.transfer.compositions

    @property
    def endpoint_level(self) -> int:
        return self.spec.end_level

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "special-germ-plan",
            self.spec.canonical_key,
            self.transfer.canonical_key,
            self.constraints.canonical_key,
        )

    def pullback_mask(
        self,
        mask: SpecialBranchMask,
        *,
        method: str,
        candidate_derived: bool = True,
    ) -> SpecialGermPlan:
        evidence = SpecialGermConstraintState.from_mask(
            mask,
            method=method,
            candidate_derived=candidate_derived,
        )
        return SpecialGermPlan(
            self.spec,
            self.transfer,
            self.constraints.then(evidence),
        )

    def pullback_defect(
        self,
        modulus: int,
        defect: int,
        *,
        method: str,
        candidate_derived: bool = True,
    ) -> SpecialGermPlan:
        evidence = SpecialGermConstraintState.from_defect(
            modulus,
            defect,
            method=method,
            candidate_derived=candidate_derived,
        )
        return SpecialGermPlan(
            self.spec,
            self.transfer,
            self.constraints.then(evidence),
        )

    def then(self, downstream: SpecialGermPlan) -> SpecialGermPlan:
        """Compose adjacent constrained blocks with exact evidence pullback."""
        if not isinstance(downstream, SpecialGermPlan):
            raise TypeError(type(downstream))
        spec = self.spec.then(downstream.spec)
        return SpecialGermPlan(
            spec,
            self.transfer.then(downstream.transfer),
            self.constraints.then(downstream.constraints),
        )

    def probe(self) -> SpecialFrobeniusChunkResult:
        """Accept only a proper divisor verified against this exact source.

        Caller-supplied masks and the ``candidate_derived`` metadata are
        retained as algebraic constraints, but cannot decide a prime sheet.
        A proper divisor is independently sufficient evidence of
        compositeness, provided its modulus matches the plan's Fermat or
        Mersenne candidate exactly.
        """
        from number_compiler.sequences.power_numbers.numbers import (
            verified_special_divisor,
        )

        spec = self.spec
        support = self.constraints.support_gcd
        modulus = self.constraints.support_modulus
        if (
            type(spec.family) is str
            and spec.family in ("fermat", "mersenne")
            and type(spec.parameter) is int
            and type(modulus) is int
            and type(support) is int
        ):
            try:
                verified = verified_special_divisor(
                    spec.family, spec.parameter, modulus, support
                )
            except (TypeError, ValueError):
                pass
            else:
                return SpecialFrobeniusChunkResult(
                    spec,
                    "SPLIT",
                    "verified-source-bound-proper-divisor",
                    gcd_packet=verified,
                    candidate_derived=True,
                )
        return SpecialFrobeniusChunkResult(
            spec,
            "UNKNOWN",
            (
                "constraint-pullback-unresolved"
                if self.constraints.checks == 0
                else "constraint-pullback-unverified-evidence"
            ),
            candidate_derived=False,
        )

    def classify_defect(
        self,
        modulus: int,
        defect: int,
        *,
        method: str,
        candidate_derived: bool = True,
    ) -> SpecialFrobeniusChunkResult:
        return self.pullback_defect(
            modulus,
            defect,
            method=method,
            candidate_derived=candidate_derived,
        ).probe()


def build_special_germ_plan(spec: SpecialFrobeniusChunkSpec) -> SpecialGermPlan:
    """Build the canonical logarithmic transport with an unconstrained sheet."""
    if not isinstance(spec, SpecialFrobeniusChunkSpec):
        raise TypeError(type(spec))
    transfer = SquareTileAction.atom(spec.family).power_block(spec.span)
    expected = binary_power_composition_count(spec.span)
    if transfer.compositions != expected:
        raise AssertionError((transfer.compositions, expected))
    return SpecialGermPlan(spec, transfer)


def compose_support_packets(
    left: SpecialFrobeniusDefectPacket,
    right: SpecialFrobeniusDefectPacket,
    *,
    method: str = "support-ideal-intersection",
) -> SpecialFrobeniusDefectPacket:
    """Compose adjacent zero/unit defect packets by candidate-ring gcd."""
    if not isinstance(left, SpecialFrobeniusDefectPacket) or not isinstance(
        right, SpecialFrobeniusDefectPacket
    ):
        raise TypeError((type(left), type(right)))
    a, b = left.spec, right.spec
    if left.modulus != right.modulus:
        raise ValueError((left.modulus, right.modulus))
    if (
        a.family != b.family
        or a.parameter != b.parameter
        or a.baseline_local_v2 != b.baseline_local_v2
        or a.modulus_bits != b.modulus_bits
        or b.start_level != a.end_level + 1
    ):
        raise ValueError((a, b))
    combined_spec = SpecialFrobeniusChunkSpec(
        a.family,
        a.parameter,
        a.start_level,
        a.span + b.span,
        a.baseline_local_v2,
        a.modulus_bits,
    )
    defect = gcd(left.modulus, left.defect, right.defect)
    return SpecialFrobeniusDefectPacket(
        combined_spec,
        left.modulus,
        defect,
        str(method),
        candidate_derived=left.candidate_derived and right.candidate_derived,
    )


__all__ = [
    "SpecialGermConstraintState",
    "SpecialGermPlan",
    "SpecialGermTransfer",
    "build_special_germ_plan",
    "compose_support_packets",
]
