"""Minimal terminal all-local thresholds for Fermat and Mersenne candidates.

This module owns only the *reduction theorem* and the fail-closed production
query surface.  It does not implement the missing higher-Kummer/Artin support
selector by falling back to Pepin, Lucas--Lehmer, carrier enumeration, CRT
factorization, or a hidden discrete logarithm.

For a Fermat candidate ``F_n`` (``n >= 2``), every prime divisor ``q`` has
``ord_q(2)=2^(n+1)``.  The historical full-pure threshold
``2^n-n-1`` forces ``q=F_n`` individually.  Prime *classification* needs less:
if every divisor satisfies ``2^(2^(n-1)) | q-1``, then
``q >= 1+2^(2^(n-1)) > sqrt(F_n)``.  A composite integer must have a prime
divisor at most its square root, so this smaller all-local threshold is already
equivalent to primality.

For an odd Mersenne exponent ``p >= 3``, the reverse Lucas--Lehmer local torus
has order ``q-(12/q)``.  The historical full-pure threshold is ``p-2``.  For
classification it suffices that every divisor satisfies
``2^((p+1)/2) | q-(12/q)``: in either character branch this forces
``q >= 2^((p+1)/2)-1 > sqrt(M_p)``.  Thus the prime-decision lift horizon is
roughly half of the full filtration horizon.

The query result lattice is deliberately explicit:

    ALL_PASS | ALL_FAIL | SPLIT(g,N/g) | UNKNOWN

Only an independently proved candidate-derived transverse unit/annihilator
extractor may return the first three for a nontrivial candidate.  Production
now retains the correct symbolic square-root progression but does not evaluate
its linear-size interval product.  Tiny cases whose guaranteed base stride
already exceeds the square-root bound can be decided structurally; deeper
candidates remain ``UNKNOWN`` until the compact holonomy pullback is proved.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.sequences.power_numbers.admission import (
    require_special_candidate_budget,
)
from number_compiler.sequences.power_numbers.frobenius_chunk import (
    SpecialFrobeniusChunkSpec,
)
from number_compiler.sequences.power_numbers.transverse_pullback import (
    SpecialTransverseWindow,
    build_compact_transverse_pullback,
)


@dataclass(frozen=True, slots=True)
class SpecialTerminalThresholdSpec:
    family: str
    parameter: int
    modulus_bits: int
    terminal_level: int
    baseline_local_v2: int
    required_local_v2: int
    pass_iff_prime: bool
    proof_method: str
    prime_decision_level: int
    prime_decision_required_local_v2: int
    prime_decision_proof_method: str

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne"):
            raise ValueError(self.family)
        if self.parameter < 0 or self.modulus_bits <= 0:
            raise ValueError((self.parameter, self.modulus_bits))
        if self.terminal_level < 1 or self.baseline_local_v2 < 0:
            raise ValueError((self.terminal_level, self.baseline_local_v2))
        if self.required_local_v2 != self.baseline_local_v2 + self.terminal_level:
            raise ValueError(
                (
                    self.required_local_v2,
                    self.baseline_local_v2,
                    self.terminal_level,
                )
            )
        if self.prime_decision_level < 0:
            raise ValueError(self.prime_decision_level)
        if (
            self.prime_decision_required_local_v2
            != self.baseline_local_v2 + self.prime_decision_level
        ):
            raise ValueError(
                (
                    self.prime_decision_required_local_v2,
                    self.baseline_local_v2,
                    self.prime_decision_level,
                )
            )
        if self.prime_decision_level > self.terminal_level:
            raise ValueError((self.prime_decision_level, self.terminal_level))


@dataclass(frozen=True, slots=True)
class SpecialTerminalThresholdResult:
    family: str
    parameter: int
    level: int
    status: str
    method: str
    modulus_bits: int
    root_witness: int | None = None
    witness_power_residue: int | None = None
    gcd_packet: int | None = None
    character_queries: int = 0
    reciprocity_descents: int = 0
    candidate_derived: bool = True
    carrier_states_enumerated: int = 0
    raw_specialization_squarings: int = 0
    transverse_window: SpecialTransverseWindow | None = None
    transverse_pullbacks: int = 0
    transverse_atom_evaluations: int = 0
    transverse_product_multiplications: int = 0

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne"):
            raise ValueError(self.family)
        if self.status not in ("ALL_PASS", "ALL_FAIL", "SPLIT", "UNKNOWN"):
            raise ValueError(self.status)
        if self.level < 0 or self.modulus_bits <= 0:
            raise ValueError((self.level, self.modulus_bits))
        if self.carrier_states_enumerated or self.raw_specialization_squarings:
            raise ValueError("terminal threshold query cannot hide carrier/replay work")
        if min(
            self.transverse_pullbacks,
            self.transverse_atom_evaluations,
            self.transverse_product_multiplications,
        ) < 0:
            raise ValueError("transverse work counters cannot be negative")
        if self.transverse_window is not None and (
            self.transverse_window.family != self.family
            or self.transverse_window.parameter != self.parameter
        ):
            raise ValueError("terminal result has another transverse window")
        if min(self.character_queries, self.reciprocity_descents) < 0:
            raise ValueError((self.character_queries, self.reciprocity_descents))
        if self.status == "SPLIT":
            if self.gcd_packet is None or self.gcd_packet <= 1:
                raise ValueError((self.status, self.gcd_packet))
        elif self.gcd_packet is not None:
            raise ValueError((self.status, self.gcd_packet))

    @property
    def decided(self) -> bool:
        return self.status != "UNKNOWN"

    @property
    def all_pass(self) -> bool:
        return self.status == "ALL_PASS"

    @property
    def proves_composite(self) -> bool:
        return self.status in ("ALL_FAIL", "SPLIT")


def fermat_terminal_threshold_spec(index: int) -> SpecialTerminalThresholdSpec:
    n = int(index)
    if n < 2:
        raise ValueError(n)
    width = 1 << n
    baseline = n + 1
    terminal = width - baseline
    if terminal < 1:
        raise AssertionError((n, width, baseline, terminal))
    # Prime classification does not need to force every passing divisor all
    # the way up to F_n.  If every prime divisor has q >= 1+2^(width/2), then
    # every divisor exceeds sqrt(F_n), so a composite factorization is
    # impossible.  This cuts the required local 2-adic threshold in half.
    decision_required = max(baseline, width // 2)
    decision_level = decision_required - baseline
    return SpecialTerminalThresholdSpec(
        "fermat",
        n,
        width + 1,
        terminal,
        baseline,
        width,
        True,
        "fermat-divisor-lower-bound",
        decision_level,
        decision_required,
        "fermat-sqrt-divisor-lower-bound",
    )


def _mersenne_branch_lower_bound(exponent: int, local_v2: int) -> int:
    """Least positive q allowed by the order and torus congruences.

    For a prime divisor q of M_p with p prime, ord_q(2)=p, hence
    q=1+2*p*k.  Requiring q == chi (mod 2^v), chi in {+1,-1}, gives
    two CRT branches.  This helper returns the smaller branch lower bound
    without enumerating factors or residue classes.
    """
    p, v = int(exponent), int(local_v2)
    if p < 3 or not (p & 1) or v < 1:
        raise ValueError((p, v))

    plus = 1 + p * (1 << v)
    if v == 1:
        # +/-1 coincide modulo 2.  q=1+2pk with k>=1 is the sharp
        # positive lower bound supplied by ord_q(2)=p.
        minus = 1 + 2 * p
    else:
        modulus = 1 << (v - 1)
        # q=1+2pk == -1 (mod 2^v) iff p*k == -1 (mod 2^(v-1)).
        k0 = (-pow(p, -1, modulus)) % modulus
        if k0 == 0:
            k0 = modulus
        minus = 1 + 2 * p * k0
    return min(plus, minus)


def _square_exceeds_mersenne(lower: int, exponent: int) -> bool:
    """Return ``lower**2 > 2**p-1`` without constructing ``2**p-1``.

    Integer discreteness makes this equivalent to ``lower**2 >= 2**p``.
    Bit lengths decide every case except the single odd-boundary case, where
    one square is still sufficient and no p-bit candidate integer is retained.
    """
    lower, p = int(lower), int(exponent)
    if lower <= 0 or p < 1:
        raise ValueError((lower, p))
    e = lower.bit_length() - 1
    if 2 * e >= p:
        return True
    if 2 * (e + 1) <= p:
        return False
    return (lower * lower).bit_length() > p


def _mersenne_prime_decision_required_v2(exponent: int) -> int:
    """Minimum torus v2 threshold whose CRT lower bound exceeds sqrt(M_p).

    The branch lower bound is monotone in v, so binary search costs O(log p)
    threshold probes.  The comparison is symbolic against ``2**p`` and never
    allocates the full Mersenne candidate merely to compare magnitudes.
    """
    p = int(exponent)
    if p < 3 or not (p & 1):
        raise ValueError(p)
    lo, hi = 1, p
    while lo < hi:
        mid = (lo + hi) // 2
        lower = _mersenne_branch_lower_bound(p, mid)
        if _square_exceeds_mersenne(lower, p):
            hi = mid
        else:
            lo = mid + 1
    return lo


def mersenne_terminal_threshold_spec(exponent: int) -> SpecialTerminalThresholdSpec:
    p = int(exponent)
    if p < 3 or not (p & 1):
        raise ValueError(p)
    terminal = p - 2

    # Every prime divisor q of M_p satisfies ord_q(2)=p, hence
    # q == 1 (mod 2p).  Combine that exact divisor law with the local
    # torus condition q == chi (mod 2^v), chi=(12/q).  The two CRT
    # branches have explicit least positive representatives.  Once both
    # representatives exceed sqrt(M_p), an all-local pass at v forces
    # primality.  This is strictly sharper than the generic
    # 2^((p+1)/2)-1 square-root bound.
    decision_v = _mersenne_prime_decision_required_v2(p)

    # For p=3,5,7 the order-divisor lower bound 1+2p alone already exceeds
    # sqrt(M_p), so no torus lift query is necessary.  Keep the semantic
    # baseline at v2=2 for compatibility with the existing chunk coordinate.
    if decision_v <= 2:
        decision_level = 0
        decision_required = 2
        method = "mersenne-order-divisor-sqrt-bound"
    else:
        decision_required = decision_v
        decision_level = decision_v - 2
        method = "mersenne-crt-torus-sqrt-bound"

    return SpecialTerminalThresholdSpec(
        "mersenne",
        p,
        p,
        terminal,
        2,
        p,
        True,
        "mersenne-torus-divisor-lower-bound",
        decision_level,
        decision_required,
        method,
    )


def terminal_threshold_spec(
    family: str, parameter: int
) -> SpecialTerminalThresholdSpec:
    family = str(family)
    if family == "fermat":
        return fermat_terminal_threshold_spec(parameter)
    if family == "mersenne":
        return mersenne_terminal_threshold_spec(parameter)
    raise ValueError(family)


def _fermat_f2_terminal_witness() -> SpecialTerminalThresholdResult:
    # F_2=17 and its terminal level is one.  The canonical transverse root is
    # t+t^-1 with t=2, namely 11; 11^2 == 2 (mod 17).
    modulus = 17
    witness = 11
    residue = pow(witness, 2, modulus)
    if residue != 2:
        raise AssertionError((witness, residue))
    return SpecialTerminalThresholdResult(
        "fermat",
        2,
        1,
        "ALL_PASS",
        "explicit-first-transverse-root",
        modulus.bit_length(),
        witness,
        residue,
    )


def _mersenne_m3_small_witness() -> SpecialTerminalThresholdResult:
    # M_3=7 is a fixed tiny exact case.  Keep it explicit rather than treating
    # a zero-span torus query as though the baseline v2 condition were automatic
    # for arbitrary Mersenne factors.
    return SpecialTerminalThresholdResult(
        "mersenne",
        3,
        0,
        "ALL_PASS",
        "explicit-small-mersenne",
        3,
    )


def prime_decision_chunk_spec(
    spec: SpecialTerminalThresholdSpec,
) -> SpecialFrobeniusChunkSpec:
    """Return only the unresolved local-lift block needed for primality.

    Fermat divisors for n>=2 satisfy the stronger classical congruence
    q == 1 (mod 2^(n+2)), so the first lift above the order baseline n+1
    is automatic and must not be charged to the chunk extractor.  Mersenne
    has no analogous universally reached torus-v2=2 boundary, so its chunk
    starts at level one and may fail before that boundary.
    """
    if not isinstance(spec, SpecialTerminalThresholdSpec):
        raise TypeError(type(spec))
    if spec.prime_decision_level <= 0:
        raise ValueError((spec.family, spec.parameter, spec.prime_decision_level))

    guaranteed_levels = 1 if spec.family == "fermat" and spec.parameter >= 2 else 0
    span = spec.prime_decision_level - guaranteed_levels
    if span <= 0:
        raise ValueError((spec.family, spec.parameter, span))
    return SpecialFrobeniusChunkSpec(
        spec.family,
        spec.parameter,
        1 + guaranteed_levels,
        span,
        spec.baseline_local_v2,
        spec.modulus_bits,
    )


def terminal_threshold_probe(
    family: str, parameter: int, *, max_candidate_bits: int = 1_000_000
) -> SpecialTerminalThresholdResult:
    """Return the exact terminal threshold result currently known scalably.

    This is the single production choke point for the missing support selector.
    New higher-Kummer/Artin constructions belong here only after they have a
    complete proof and explicit nonunit/gcd accounting.
    """
    # Admit the symbolic candidate before terminal_threshold_spec computes any
    # family metadata containing ``2^parameter``.
    require_special_candidate_budget(family, parameter, max_candidate_bits)
    spec = terminal_threshold_spec(family, parameter)
    if spec.family == "fermat" and spec.parameter == 2:
        return _fermat_f2_terminal_witness()
    if spec.family == "mersenne" and spec.parameter == 3:
        return _mersenne_m3_small_witness()

    if spec.prime_decision_level == 0:
        return SpecialTerminalThresholdResult(
            spec.family,
            spec.parameter,
            0,
            "ALL_PASS",
            spec.prime_decision_proof_method,
            spec.modulus_bits,
        )

    # The relevant candidate-derived object is the transverse Frobenius
    # holonomy, not a supplied zero-section defect.  Keep its square-root
    # progression symbolic: a balanced product tree would still evaluate every
    # atom.  The compact request remains fail-closed until a source-bound
    # unit/annihilator evaluator is proved and implemented.
    pullback = build_compact_transverse_pullback(
        spec.family,
        spec.parameter,
        max_candidate_bits=max_candidate_bits,
    )
    return SpecialTerminalThresholdResult(
        spec.family,
        spec.parameter,
        spec.prime_decision_level,
        "UNKNOWN",
        pullback.method,
        spec.modulus_bits,
        candidate_derived=pullback.candidate_derived,
        transverse_window=pullback.window,
        transverse_pullbacks=1,
        transverse_atom_evaluations=pullback.atom_evaluations,
        transverse_product_multiplications=pullback.product_multiplications,
    )


__all__ = [
    "SpecialTerminalThresholdSpec",
    "SpecialTerminalThresholdResult",
    "fermat_terminal_threshold_spec",
    "mersenne_terminal_threshold_spec",
    "terminal_threshold_spec",
    "prime_decision_chunk_spec",
    "terminal_threshold_probe",
]
