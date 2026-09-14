"""Fail-closed block quotient for terminal special-number Frobenius lifts.

The terminal Fermat/Mersenne certificate needs only one predicate: every local
2-primary lift in a requested block succeeds.  Locally, after a boundary with
2-adic stride ``m``, write the relevant prime action as ``q = eps + m*k``.
For a block of ``r`` future lifts the complete negacyclic Frobenius action
retains only

    rho = k mod 2**r.

In the larger quotient ``X**(m*2**(r-1)) + 1`` the folded ``X`` coefficient of
``X**q`` is ``+1`` exactly when ``rho == 0``.  Thus an arbitrarily long block
has a one-bit semantic quotient: all lifts pass or they do not.

This module deliberately does *not* pretend that the zero class can already be
extracted from an unfactored Fermat/Mersenne candidate.  The production probe
therefore remains ``UNKNOWN`` until a candidate-derived coefficient extractor
is proved.  No carrier enumeration, factor/CRT reconstruction, or recurrence
replay is permitted here.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

_VALID_STATUS = frozenset({"ALL_PASS", "ALL_FAIL", "SPLIT", "UNKNOWN"})


@dataclass(frozen=True, slots=True)
class SpecialFrobeniusChunkSpec:
    """One contiguous block of local 2-primary Frobenius lift queries."""

    family: str
    parameter: int
    start_level: int
    span: int
    baseline_local_v2: int
    modulus_bits: int

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne"):
            raise ValueError(self.family)
        if self.parameter < 0 or self.start_level < 1 or self.span < 1:
            raise ValueError((self.parameter, self.start_level, self.span))
        if self.baseline_local_v2 < 0 or self.modulus_bits <= 0:
            raise ValueError((self.baseline_local_v2, self.modulus_bits))

    @property
    def base_stride_v2(self) -> int:
        """v2 of the stride known before the first level in this chunk."""
        return self.baseline_local_v2 + self.start_level - 1

    @property
    def required_local_v2(self) -> int:
        """v2 required after every level in the chunk passes."""
        return self.base_stride_v2 + self.span

    @property
    def end_level(self) -> int:
        return self.start_level + self.span - 1

    @property
    def folded_half_degree_log2(self) -> int:
        """log2 of ``M=m*2**(span-1)``; ``M`` itself is never materialized."""
        return self.base_stride_v2 + self.span - 1

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "special-frobenius-chunk",
            self.family,
            self.parameter,
            self.start_level,
            self.span,
            self.baseline_local_v2,
            self.modulus_bits,
        )

    def adjacent(self, span: int) -> SpecialFrobeniusChunkSpec:
        span = int(span)
        if span < 1:
            raise ValueError(span)
        return SpecialFrobeniusChunkSpec(
            self.family,
            self.parameter,
            self.end_level + 1,
            span,
            self.baseline_local_v2,
            self.modulus_bits,
        )


@dataclass(frozen=True, slots=True)
class SpecialFrobeniusChunkResult:
    """Fail-closed semantic result for one contiguous Frobenius chunk."""

    spec: SpecialFrobeniusChunkSpec
    status: str
    method: str
    zero_class: bool | None = None
    gcd_packet: int | None = None
    first_failure_offset: int | None = None
    candidate_derived: bool = True
    polynomial_terms_materialized: int = 0
    one_level_replays: int = 0
    raw_trace_squarings: int = 0
    factor_enumeration: int = 0

    def __post_init__(self) -> None:
        if self.status not in _VALID_STATUS:
            raise ValueError(self.status)
        if any(
            value != 0
            for value in (
                self.polynomial_terms_materialized,
                self.one_level_replays,
                self.raw_trace_squarings,
                self.factor_enumeration,
            )
        ):
            raise ValueError(
                "Frobenius chunk result cannot hide expanded/replayed work"
            )
        if self.status == "ALL_PASS":
            if self.zero_class is not True or self.gcd_packet is not None:
                raise ValueError((self.status, self.zero_class, self.gcd_packet))
            if self.first_failure_offset is not None:
                raise ValueError(self.first_failure_offset)
        elif self.status == "ALL_FAIL":
            if self.zero_class is not False or self.gcd_packet is not None:
                raise ValueError((self.status, self.zero_class, self.gcd_packet))
            if self.first_failure_offset is not None and not (
                0 <= self.first_failure_offset < self.spec.span
            ):
                raise ValueError(self.first_failure_offset)
        elif self.status == "SPLIT":
            if self.gcd_packet is None or self.gcd_packet <= 1:
                raise ValueError(self.gcd_packet)
            if self.zero_class is not None:
                raise ValueError(self.zero_class)
        else:
            if self.zero_class is not None or self.gcd_packet is not None:
                raise ValueError((self.zero_class, self.gcd_packet))
            if self.first_failure_offset is not None:
                raise ValueError(self.first_failure_offset)

    @property
    def decided(self) -> bool:
        return self.status != "UNKNOWN"

    @property
    def all_pass(self) -> bool:
        return self.status == "ALL_PASS"

    @property
    def proves_composite(self) -> bool:
        return self.status in ("ALL_FAIL", "SPLIT")

    def compose(
        self, downstream: SpecialFrobeniusChunkResult
    ) -> SpecialFrobeniusChunkResult:
        """Compose adjacent conditional chunks without reopening individual levels.

        A downstream chunk is meaningful only after every level in this chunk
        passed.  Hence PASS delegates to the downstream result; FAIL/SPLIT
        short-circuit; UNKNOWN remains UNKNOWN.  This is the exact conjunction
        quotient required by the terminal certificate.
        """
        if not isinstance(downstream, SpecialFrobeniusChunkResult):
            raise TypeError(type(downstream))
        a, b = self.spec, downstream.spec
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
        method = f"compose({self.method},{downstream.method})"
        if self.status == "ALL_PASS":
            if downstream.status == "ALL_PASS":
                return SpecialFrobeniusChunkResult(
                    combined_spec, "ALL_PASS", method, True
                )
            if downstream.status == "ALL_FAIL":
                offset = downstream.first_failure_offset
                if offset is not None:
                    offset += a.span
                return SpecialFrobeniusChunkResult(
                    combined_spec,
                    "ALL_FAIL",
                    method,
                    False,
                    first_failure_offset=offset,
                )
            if downstream.status == "SPLIT":
                return SpecialFrobeniusChunkResult(
                    combined_spec,
                    "SPLIT",
                    method,
                    gcd_packet=downstream.gcd_packet,
                )
            return SpecialFrobeniusChunkResult(combined_spec, "UNKNOWN", method)
        if self.status == "ALL_FAIL":
            return SpecialFrobeniusChunkResult(
                combined_spec,
                "ALL_FAIL",
                method,
                False,
                first_failure_offset=self.first_failure_offset,
            )
        if self.status == "SPLIT":
            return SpecialFrobeniusChunkResult(
                combined_spec,
                "SPLIT",
                method,
                gcd_packet=self.gcd_packet,
            )
        return SpecialFrobeniusChunkResult(combined_spec, "UNKNOWN", method)


def folded_x_coefficient_from_stride_residue(stride_residue: int, span: int) -> int:
    """Return the folded coefficient of ``X`` for an r-level local action.

    Locally ``q=eps+m*k`` and ``rho=k mod 2**r``.  Reducing ``X**q`` in
    ``X**(m*2**(r-1))+1`` gives coefficient +1 at X iff ``rho=0``, -1 iff
    only the top residue bit is set, and 0 otherwise.  The computation depends
    only on the compact residue and never constructs the cyclotomic degree.
    """
    rho, span = int(stride_residue), int(span)
    if span < 1 or rho < 0:
        raise ValueError((rho, span))
    if span < rho.bit_length():
        raise ValueError((rho, span))
    if rho == 0:
        return 1
    top = 1 << (span - 1)
    if rho == top:
        return -1
    return 0


def stride_zero_class(stride_residue: int, span: int) -> bool:
    return folded_x_coefficient_from_stride_residue(stride_residue, span) == 1


@dataclass(frozen=True, slots=True)
class SpecialFrobeniusDefectPacket:
    """One candidate-ring generator for the terminal chunk failure ideal.

    ``defect`` is normalized so that every local passing component sees zero,
    while every locally failing folded-X coefficient sees a unit.  Therefore
    ``gcd(defect, modulus)`` is the exact support intersection: the full
    modulus means all components pass, one means all components fail, and a
    proper gcd is a natural factor packet.

    The packet does not prescribe how ``defect`` is extracted.  In production
    it may only be constructed by a separately proved unfactored candidate
    evaluator.
    """

    spec: SpecialFrobeniusChunkSpec
    modulus: int
    defect: int
    method: str
    candidate_derived: bool = True
    polynomial_terms_materialized: int = 0
    one_level_replays: int = 0
    raw_trace_squarings: int = 0
    factor_enumeration: int = 0

    def __post_init__(self) -> None:
        modulus = int(self.modulus)
        if modulus <= 1 or not (modulus & 1):
            raise ValueError(modulus)
        object.__setattr__(self, "modulus", modulus)
        object.__setattr__(self, "defect", int(self.defect) % modulus)
        if any(
            value != 0
            for value in (
                self.polynomial_terms_materialized,
                self.one_level_replays,
                self.raw_trace_squarings,
                self.factor_enumeration,
            )
        ):
            raise ValueError("defect packet cannot hide expanded/replayed work")

    @property
    def support_gcd(self) -> int:
        return gcd(self.defect, self.modulus)

    def classify(self) -> SpecialFrobeniusChunkResult:
        g = self.support_gcd
        if g == self.modulus:
            return SpecialFrobeniusChunkResult(
                self.spec,
                "ALL_PASS",
                self.method,
                True,
                candidate_derived=self.candidate_derived,
            )
        if g == 1:
            return SpecialFrobeniusChunkResult(
                self.spec,
                "ALL_FAIL",
                self.method,
                False,
                candidate_derived=self.candidate_derived,
            )
        return SpecialFrobeniusChunkResult(
            self.spec,
            "SPLIT",
            self.method,
            gcd_packet=g,
            candidate_derived=self.candidate_derived,
        )


def folded_x_defect_from_stride_residue(stride_residue: int, span: int) -> int:
    """Local normalized defect: zero on the stride-zero class, a unit otherwise."""
    return folded_x_coefficient_from_stride_residue(stride_residue, span) - 1


def classify_frobenius_chunk_defect(
    spec: SpecialFrobeniusChunkSpec,
    modulus: int,
    defect: int,
    *,
    method: str,
) -> SpecialFrobeniusChunkResult:
    """Classify an already-proved candidate-derived folded-X defect by one gcd."""
    return SpecialFrobeniusDefectPacket(spec, modulus, defect, method).classify()


def special_frobenius_chunk_probe(
    spec: SpecialFrobeniusChunkSpec,
) -> SpecialFrobeniusChunkResult:
    """Production-safe candidate probe for the r-level zero class.

    The local quotient is proved, but the unfactored candidate-derived
    coefficient extractor is still the theorem frontier.  Until that extractor
    exists this surface is intentionally UNKNOWN and performs zero hidden work.
    """
    if not isinstance(spec, SpecialFrobeniusChunkSpec):
        raise TypeError(type(spec))
    return SpecialFrobeniusChunkResult(
        spec,
        "UNKNOWN",
        "frobenius-chunk-zero-class-extractor-unavailable",
    )


__all__ = [
    "SpecialFrobeniusChunkResult",
    "SpecialFrobeniusChunkSpec",
    "SpecialFrobeniusDefectPacket",
    "classify_frobenius_chunk_defect",
    "folded_x_coefficient_from_stride_residue",
    "folded_x_defect_from_stride_residue",
    "special_frobenius_chunk_probe",
    "stride_zero_class",
]
