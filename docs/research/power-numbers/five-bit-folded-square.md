# Five-bit folded-square observation

The [radix-64 mirror refinement](radix64-mirror-refinement.md) supersedes this
packet as the current bounded support experiment. It adds the coefficient-five
modulo-sixteen production observer and resolves the M53 false positive on the
augmented 72-sheet corpus. The old packet and its admission counterexample
remain valid arithmetic and historical evidence; neither zero test is promoted
as an unrestricted acceptance certificate.

The production arithmetic tile now exposes `ArithmeticTile.folded_square_packet()`.
It computes only coefficients one and two of the folded square, modulo four and
eight, without constructing a complete convolution, running a carry scan,
changing the square's sign representative, or reconstructing a source integer.
The packet is a transient output; work counts are separate from its two-residue
identity. This deploys an exact arithmetic observer. It does **not** enable a
new Fermat/Mersenne primality decision in the CLI.

## Observation and known reference

Use the existing orientation defect `nu=b-1=-2e`. The binary polynomial of its
canonical nonnegative representative is `X(z)=sum x_i z^i`, of width `w`.
Fermat uses `w=2^parameter` and fold sign `-1`; Mersenne uses `w=parameter` and
sign `+1`. Fermat's candidate has **w+1 integer bits**, which must not be used as
the polynomial fold width.

For full support, the orientation is `b=1` and the defect is zero. The reference
raw field is zero for Fermat and the constant `-2` for Mersenne. Consequently
the two nonconstant reference coefficients are zero in both families. With
`c_k=sum_(i+j=k) x_i*x_j`, the exact projections are

```
r1 = c1 + sign*c(w+1)
r2 = c2 + sign*c(w+2)
packet = (r1 mod 4, r2 mod 8)
```

The Lucas correction only changes coefficient zero. No carry normalization is
needed for this observation. Nor may the existing normalized-square sign/deck
optimization be applied before observing these polynomial coefficients: equality
of the resulting integer residues is a different consumer contract.

The supplied research claims `full_support iff packet=(0,0)` on its bounded
admitted sheets. The packet has 32 possible pairs. That storage bound alone
proves neither that five bits are minimal on a corpus nor that its zero test
classifies arbitrary candidates. Both require separate checks.

## Reproduced bounded corpus

The executable research owner is
`devtools/experiments/power_numbers/five_bit_support.py`. It reuses the
repository's supplied factor tables for F4–F7 and M11/M13/M17/M19/M23/M29/M31/
M37/M43/M47/M61. Their complete CRT orientation sheets contain 60 rows. Four
additional F9 rows use only the two supplied divisors, with modulus their product
and polynomial width 512; they test local support over that partial modulus,
not a complete F9 factorization or candidate certificate.

All 64 rows have exact agreement with the existing full folded convolution and
zero sheet-label errors for the `(mod 4, mod 8)` zero test. Searching pairs of
power-of-two moduli gives minimum total precision five bits, attained at
`(mod 4, mod 8)` and `(mod 8, mod 4)`. Independently, deleting any one of the
five individual bits from the chosen `(mod 4, mod 8)` packet fails on this
corpus. The partial F9 adversary is essential to that minimum.

The temporal filtrations reproduce these first holes:

| Control | Supplied local depths | First failed level | Packet there |
| --- | --- | ---: | --- |
| F4 | (11) | 12 | (0, 6) |
| F5 | (1, 1) | 2 | (0, 6) |
| F9 partial modulus | (6, 1) | 2 | (0, 2) |
| M11 | (0, 0) | 1 | (1, 2) |
| M13 | (11) | 12 | (3, 4) |
| M29 | (0, 0, 1) | 1 | (1, 7) |

M43 has a packet `(1,2)` collision between orientations `(−,−,−)` and `(+,+,−)`;
their raw coefficient pairs are `(41,42)` and `(17,18)`. M47 has a packet `(2,7)`
collision between `(+,−,−)` and `(+,−,+)`, with raw pairs `(14,15)` and `(18,23)`.
These are actual different support sheets, not duplicated coefficient encodings.
All of these observations use factor truth only in research.

### Admission cannot be omitted: an additional M53 sheet

The bounded rule does not extend to arbitrary CRT sheets. An additional
adversarial control has

```
N = 2^53 - 1 = 6361 * 69431 * 20394401
b = 4573151866567654
x = b - 1 = 4573151866567653
b mod (6361, 69431, 20394401) = (1, 1, -1)
(r1, r2) = (12, 16)
packet = (0, 0)
gcd(x, N) = 441650591 < N
```

The orientation is mixed, so full support fails despite the zero packet. The
regression checks the CRT congruences, complete product, independent full folded
square and proper defect gcd. This example is outside the reported 64-row
corpus. Its local depths are `(1,0,0)`, so the sheet `(+,+,−)` cannot arise by
testing all depths against one common level. It is **not** a counterexample
to the tested temporal filtrations or to a more restrictive clock-cylinder
admission theorem. It does rule out interpreting packet zero as an unrestricted
support certificate.

## Production implementation and cost

The canonical implementation is
`src/number_compiler/arithmetic/polynomials/folded_square_packet.py`. It visits
unordered mirror pairs for degrees `1`, `2`, `w+1` and `w+2`; off-diagonal terms
contribute twice and diagonal terms once. Operands and accumulators are reduced
before arithmetic. Signed coefficient representatives differing by multiples of
eight produce the same packet.

`FoldedSquarePacket` contains only the two reduced residues and their joint zero
predicate. `FoldedSquareProjection` reports coefficient reads, pair visits and
actual scalar products separately. It retains no source coefficients, complete
folded field, support-sheet identifier, factor data or temporal history.

This removes the full-convolution dependency for an explicitly requested packet,
but the present extraction is linear in the supplied coefficient width. For an
all-one width-w polynomial it visits `w+1` unordered pairs and records `3w+2`
coefficient reads, including input validation. Reducing every accumulator modulo
four/eight does not remove those visits. The implementation is not represented
as a logarithmic HashLife constructor.

On the supplied sheets, the measured worst-case work is:

| Control | Coefficient reads | Unordered pair visits | Nonzero scalar products |
| --- | ---: | ---: | ---: |
| F4 | 50 | 17 | 17 |
| F5 | 98 | 33 | 33 |
| F6 | 194 | 65 | 65 |
| F7 | 386 | 129 | 129 |
| F9 partial modulus | 1,538 | 513 | 3 |

The F9 partial source has few contributing nonzero products, yet the generic
implementation still inspects the mirror positions and validates its width-512
input. The read and visit counters prevent that work from being hidden behind
the small packet or the low nonzero-product count.

A separate dense all-one control compares the new observer with the existing
adaptive full-square implementation, asking for the same two folded residues:

| Width | Full-square scalar products | Demanded packet scalar products |
| --- | ---: | ---: |
| 16 | 136 | 17 |
| 32 | 528 | 33 |
| 64 | 2,080 | 65 |
| 128 | 8,256 | 129 |
| 512 | 26,244 | 513 |

This is a real reduction in demanded arithmetic, including about 51 times fewer
scalar products at width 512. It measures extraction from an already supplied
polynomial, not candidate-to-cylinder work, cache hits, or logarithmic temporal
powering. The complete five-width probe ran in 0.571 seconds with a
46,678,472-byte sampled peak.

The supplied dyadic constructor measurements likewise remain relevant:

| Fermat control | Width | Reported active mirror-pair states |
| --- | ---: | ---: |
| F4 | 16 | 10 |
| F5 | 32 | 52 |
| F6 | 64 | 100 |
| F7 | 128 | 238 |
| F9 | 512 | 498 |

The reported F9 total is 988 states. These are supplied research measurements,
not counters from this new dense-coefficient projection. Both measurements
identify a construction-cost issue; neither changes the information content
of the two-residue output.

## Formal proof boundary

`Five_Bit_Folded_Square.thy` belongs to the existing `Temporal_Clock_Jumps`
Isabelle session. It establishes modular arithmetic factorization, the
32-element packet space, and invariance of the zero predicate under packet
equality. The fold theorem connects the selected full-fold coefficients to the
two-term projection at positions one and two.

Consumer transfer remains explicitly conditional on an admitted observable
factoring through the packet. The theory does not assume or certify primality,
complete etale support, candidate-side construction of the orientation cylinder,
or a logarithmic spatial work bound. A definition of a two-residue function is
not a proof of any of those obligations.

## Remaining production promotion gates

The next spatial object is the cross-child mirror-correlation consumer, reduced
modulo four/eight before interning. A concatenation law must account for its
cross-child terms and show that their boundary payload has a bounded closed
quotient. Small final packets are insufficient evidence about this constructor.

The classifier additionally needs an admitted theorem connecting the source's
orientation cylinder and this zero predicate to the demanded support bit.
Bounded CRT sheet enumeration is validation data, not an allowed production
source of that cylinder. The research module remains outside production imports.

Therefore CLI theorem resolution and its explicit classical fallback policy
remain unchanged. Enabling a default five-bit primality result while these gates
are open would contradict the supplied research's failed promotion result.

## Validation

The final focused selection passes 47 tests in 0.73 seconds, including:

- Exhaustive binary polynomials through width eight against the existing full
  convolution, for both fold signs; signed-coefficient and modular-lift checks.
- Production API poison checks forbidding full squaring, stepping, sign-sheet
  rebinding and integer reconstruction during the packet query.
- The 64-sheet corpus, minimum-bit searches, first holes, noninjective aliases
  and the separately labelled M53 admission counterexample.
- Existing CLI classification tests, preserving unresolved/certificate behavior.

The restored `Temporal_Clock_Jumps` Isabelle session passes in 11.219 seconds
with a 449,662,240-byte sampled peak and the explicit no-oracle gate. Its
`Five_Bit_Folded_Square.thy` proves the arithmetic projection, not the support
equivalence or constructor cost. An optional attempt to kernel-normalize the
entire numerical M53 example timed out twice at the unchanged 35-second guard;
that theory and its registration were removed. M53 is therefore an executable
exact regression, not an additional Isabelle certificate.

The final repository-policy/production-boundary selection and repeated packet
tests pass 57 tests in 7.12 seconds; the separately marked long validation case
was deselected and is not counted. Strict mypy passes all 1,223 Python files.
Changed-file Ruff and
`git diff --check` pass. Generated test/proof logs and reports remain in `/tmp`.
No theorem premise, time/memory budget, production admission rule or fallback
policy was relaxed to obtain these results.
