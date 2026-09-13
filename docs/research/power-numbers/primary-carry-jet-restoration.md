# Primary carry jet and étale factor output

The September 12 attachments supply a candidate quotient and bounded experiments,
not a completed compact primality algorithm. This checkout did not contain the
named `PrimaryEtaleCarryJetTransducer`, the claimed 45-sheet corpus, or its audit
implementation. The exact transducer algebra is now restored in
[`primary_carry_jet.py`](../../../src/number_compiler/arithmetic/polynomials/primary_carry_jet.py).
The corpus statistics below are attributed to the supplied research; they have
not been independently reproduced from a complete factor dataset in this change.

## Exact algebra now available in production

For binary normalization of a length-L coefficient word, put
`Q(z) = sum c_(i+1) z^i`, with incoming and outgoing carries `u,v`. Then

```
A(z)-R(z) = (2-z)Q(z) - u + v*z^L.
```

This follows by summing `a_i+c_i = r_i+2*c_(i+1)` against `z^i`.
In `J=(Z/16)[y]/y^2`, `y=z+1`, write `Q=q0+q1*y`. The defect coordinates are

```
d0 = 3*q0 - u + v*(-1)^L
 d1 = 3*q1 - q0 - v*L*(-1)^L                 (mod 16).
```

Multiplication by `3-y` is invertible: its inverse is `11+9*y`. Thus this
conversion loses no information once the boundary is known. The implementation
provides both directions. This repeated-root carry algebra is an observer for
the étale problem; the algebra J itself is not claimed to be étale.

The parity projections follow directly from substituting `z=-1`:

```
order-4/mod-2 harmonic: (q0+q1, q1) mod 2
carry sum, one-based moment: (q0, q0+q1) mod 2.
```

`PrimaryEtaleCarryJetTransducer` retains the response for the entire declared
incoming-carry interval. For low block A followed by high block B, composition
feeds A's outgoing carry into B and adds `z^length(A)*Q_B` to `Q_A`.
Associativity and binary powering are inherited from the existing
`CarryCyclotomicTransducer`; no second composition algorithm was introduced.
A seam key requires an actual signed fixed carry of that response: outgoing
equals incoming for cyclic closure, or its negative for negacyclic closure.
Keys are observations within their declared geometry, not cross-ring identities.
The key's `deck_branch` is the input sign-canonicalization bit. The distinct
signed-minus-one negacyclic output chart is certified by a unit jump between the
seam input and its next carry port, proving an ordinary all-ones remainder.
Changing that payload to `(-1,0,...)` adds one to each outgoing internal carry,
so its jet correction is the powered all-ones block. This uses the existing
`PrimaryJetBlock` power owner and fails closed if the needed carry port or chart
premise is unavailable. A sampled seam key
is not used as a temporal state or a prime-bit decoder.

`ArithmeticTile.step_with_primary_carry_jet()` now constructs the exact key
from the transient field of one ordinary family square/trace-square, reusing
the existing sign canonicalization, convolution, fold, and normalization owners.
The returned step retains its convolution work counters. The observer constructs
its carry response only for the actual seam, plus the next port when the signed
output chart requires it.

The coefficient constructor still reads its supplied coefficient block. It is
not the missing direct pullback from a compact special-number clock. Composing
and powering an already constructed block is a separate, exact capability.

## Primality bit recovery and its remaining premise

The existing production terminal reduction is preserved. For Fermat numbers,
a terminal root of `x^(2^(2^n-n-1))=2` in every residue field forces an element
of order `F_n-1` in each such field. Every prime divisor q then satisfies
`q-1 >= F_n-1`, hence q=F_n. Conversely, a prime Fermat field has the required
cyclic capacity. The smaller square-root threshold and the Mersenne torus
threshold remain owned by `terminal_threshold.py`.

These are reductions from an **all-local** bit to primality. They do not
construct the all-local bit. Neither a product of local signs nor the formally
predetermined global candidate Frobenius action recovers that bit. Likewise,
zero Frobenius-additivity defect is not accepted as a prime certificate.
Production returns `unknown` when the compact extractor is unresolved. Pépin
and Lucas–Lehmer are confined to research oracles and cannot be enabled in the
production compiler. Candidate-derived mod-16 shadow-cylinder recovery and its
all-local-bit refinement remain release blockers.

## Factor printing: exact conditional proof and production path

The previously research-only quadratic Frobenius probes now have one production
owner, [`etale_factor.py`](../../../src/number_compiler/sequences/power_numbers/etale_factor.py).
Research imports that owner. They do not use factor tables or factor searches.

For Mersenne candidates, compute `(3+s)^N-(3-s)` in
`(Z/N)[s]/(s^2-3)`. For prime candidates with odd exponent, Frobenius sends
`s` to `-s`, so a nonzero coefficient defect proves compositeness. For Fermat
n>=3, use `(1+y)^N-(1+y)` in the canonical first-root quadratic algebra; the
corresponding prime field is split and its Frobenius fixes y.

For each already-produced ring coefficient a, Euclid's algorithm gives
`g=gcd(N,a)`. If `1<g<N`, then `N=g*(N/g)` is an exact nontrivial factorization.
If g is 1 or N, there is no proper factor to print from that coefficient.
Keeping the coefficients separate avoids losing a useful leak by combining
coefficients with different local zero supports. The stronger root-specific theorem is now formalized: if a canonical
`D*(D+2)=0 mod N` lies outside `{0,N-2}`, its gcd is necessarily proper.
`factor_from_etale_root(N,D)` checks that root equation and returns the gcd.
This guarantees output from a nontrivial root, while leaving root construction
as a separate requirement.

The restored probes reproduce M11→23, M23→47, M83→167, M131→263. The public
compiler accepts `collect_etale_factor=True`; the CLI exposes this as:

```
number-compiler classify mersenne 131 --factor --format json
```

An available terminal gcd packet is also preserved through the certificate and
resolution instead of being discarded. The additional étale query runs only
when explicitly requested and within its product budget. A checked proper
divisor proves compositeness even if the prime-bit extractor is unavailable;
a non-splitting result leaves `unknown` unchanged. Its quadratic multiplication
count is reported as `etale_ring_multiplications`, and repeated compiler demands
reuse the factor result. Raw source compilation does not request this work.

“Free factor printing” means conditional output from an available annihilator,
with no factor search. It does **not** mean zero-cost gcds, zero-cost construction
of the étale coefficients, or guaranteed factorization. The optional quadratic
probe has linear-in-candidate-bit-length ring-product work. It is separate
from the still-missing mod-16 shadow-cylinder recovery.

## Supplied support experiments and open work

The attachment reports 45 complete sheets / 320 CRT orientation rows, with 320
seam classes and no Boolean, support, or idempotent conflicts. It reports that
each coordinate is necessary somewhere in that corpus. Generic testing reports
150 sheets / 4,272 rows through width 80 without support conflicts, then a
negacyclic width-91 support collision at depth two, repaired at depth four.
Lower precision or shallower depth also has stated counterexamples.

This is evidence for a grammar-specific theorem, not proof of one. Neither the
complete 45-sheet dataset nor the explicit width-91 collision rows were attached;
this restoration does not fabricate them. The later definition supplied by the user identifies these rows as all CRT
orientations on the quadratic root variety `D*(D+2)=0 mod N`, followed by one
ordinary square/trace-square. There was no temporal admission rule or terminal
clock construction. The [Isabelle formalization](etale-isabelle-proof.md)
develops the exact algebra, local-to-global thresholds, proper-gcd output,
and an odd-width Mersenne zero-section theorem. Universal support separation,
the Fermat zero-section, and a candidate-derived compact terminal clock pullback
remain unresolved. Consequently there is no production lookup table trained
on these statistics and no claimed restored proof of a universally fast selector.

The [validation record](../../../results/current/cylinder-ray-restoration-2026-09-12/README.md)
records test counts and the four independently reproduced pre-existing failures.
Validation covers independent direct carry evaluation, concatenation, binary
powering, defect/jet round trips, parity projections, proper-factor divisibility,
prime controls, unknown boundaries, and actual public compiler/CLI output.
