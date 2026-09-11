# Clock-coordinate implementation and growth audit

The [September 11 endpoint-seam audit](endpoint-seam-powering-audit.md) adds a
successful exact-endpoint quotient and stronger depth-germ proofs. The finite
tangent counterexamples and earlier public-cache measurements below remain
valid for their stated carriers.


This checkpoint implements exact normalized clock occurrences and shared local
actions. It does not make finite clock observations into complete exact source
states. The new F/M action machines use the existing target-distance owner;
Collatz uses the existing three-unit phase and Hensel-cylinder owners. No new
candidate primality certificate or public CLI scheduler admission is introduced.

## Fermat and Mersenne

`PrimeTwoPrimaryPhaseOccurrence` stores depth and exact odd phase separately.
A direct duration jump increments depth and truncates newly invisible phase
bits. Small odd payloads do not allocate a modulus with the full live precision.
Explicit exponent materialization has a bit budget. Mersenne canonicalizes the
trace deck `u ~ -u`; Fermat retains its oriented phase and exceptional ring zero.
These are conditional dynamics: the caller must supply the correct admitted
pure two-primary carrier.

The shared depth-machine cache keys only family and parameter. An allocation
limit is checked before lookup and is not semantic state. Two permissible
limits now return the same cached machine. The cache retains at most 128 machines.
The occurrence is not included in this ActionID.

The bounded probe independently enumerates the actual raw recurrence and
minimizes its terminal Moore observer. Enumeration and phase lookup are charged
as setup, not treated as a fast candidate-injection algorithm.

| Carrier | Exact states | Depth actions | Independent Moore classes |
|---|---:|---:|---:|
| F2 complete residue ring | 17 | 5 | 5 |
| F3 complete residue ring | 257 | 9 | 9 |
| F4 complete residue ring | 65,537 | 17 | 17 |
| M5 generated circle traces | 17 | 5 | 5 |
| M7 generated circle traces | 65 | 7 | 7 |
| M13 generated circle traces | 4,097 | 13 | 13 |

The partitions agree extensionally, not just in size. Direct jumps are checked
at A1, A2, …, A1024 and duration `10^12`, reconstructing the returned occurrence
and comparing with the bounded recurrence. Each jump uses zero primitive
successors. The tiny controls have already exhausted their phase precision by
N=16, so their zero remaining phase bits through N=1024 demonstrate saturation,
not a measured asymptotic theorem for growing candidates. Tests also exercise
a large declared capacity with odd phase one without allocating its modulus.

The earlier pulled Fermat filtration is a different observer/carrier; its
12-class F4 result is not replaced by the full-ring 17-class result.

**M11 correction:** the generated unit has order 990 and 276 distinct traces.
Trace zero is absent. Its terminal-only Moore machine therefore has one
all-false class. The pure depth clock is rejected because 990 is not 2048.
The attachment's 276 refined classes concern a stronger phase/germ observer,
not this terminal observer. A composite local-capacity construction and
candidate-side injection remain separate obligations.

## Collatz

The normalized inverse-three clock canonicalizes phase modulo `2^(q-2)` for
q≥3. Its radix-64 consumer interns one match skeleton and six mismatch-depth
skeletons. Exact odd mismatch tangents remain occurrence payload; they are not
discarded to achieve the seven-action count. A finite window alone remains
explicitly non-successor-complete.

The local consumer now reads a fixed 16-phase radix-64 root table rather than
computing the full q-bit root and discarding its high bits. A high-precision
poison regression rejects wide-root evaluation on this path. Signed higher
inputs represent source-tail minus root-tail; negative displacements are valid.

The first lift at q=6 uses inverse coefficient 35. For q≥7 the stable inverse
coefficient is 3. The effective digit slope multiplies that coefficient by the
low root, so slopes are not constant across all phases. The Isabelle integer
lift theorem treats the bootstrap separately from the arbitrary-precision law.

The q=6 exhaustive local sweep has 1,024 phase/digit requests, seven retained
skeletons and 1,017 actual interner hits. Extending the phase-context sweep from
16 to 1,024 retains 16 canonical clock keys and seven skeletons; requests rise
to 65,536 and hits to 65,529. This is an all-context consumer sweep, **not** a
Collatz trajectory or a proof that future valuation discovery is constant cost.
Exact suffix demand and increasing required precision remain the growth sources.

## 196 fixed roots and phase rebasing

The primary ring coordinate is y, with positional `z=y-1`. Growth transport is
`y=(0,1,0,0,0)`, not `(1,1,0,0,0)`. The corrected audit uses this same convention
as `PrimaryJetAffineMorphism.reverse_add_event`. The all-port audit reuses the
existing pair-step owner, extended with an optional incoming carry; its duplicate
transition formula has been removed.

For the action `J'=A*J+B`, the fixed roots are `-B` without growth and
`-z^-1*B` with growth. If `W=J-r`, then

```text
W' = A*W + (r-r')
z^-(L+g)*W' = (z^-g*A)*(z^-L*W) + z^-(L+g)*(r-r').
```

The factor `z^-g` on transport is necessary when growth changes width. The
audit normalizes the tangent itself, checks both ports and compares successor
**signatures**, separately from exact successor payloads.

A concrete three-source negative control survives the correction:

```text
(0,0,0,0,0,0)
(5,17,14,14,17,5)
(7,3,6,6,3,7)
```

These have the same all-port root-normalized tangent but their successors
split. The exhaustive six-cell symmetric carrier contains 6,859 pair fields. Its
13,718 all-port fixed-point and phase-rebase checks all pass. There are 1,665
alias fibers; 1,647 split under the next **tangent signature**, while all 1,665
split as exact successor fields. This distinction avoids mistaking failure of
exact decoding for failure of quotient congruence. Fixed-root algebra is
therefore useful normalization, yet this finite
tangent is not a successor-closed quotient. The attachment's larger tropical
trajectory counts are not substituted for an independent congruence check.

The charged seed-196 trajectory has the following measured interner growth:

| N | Pair width | Retained tangent IDs | Cache hits | Primitive successors |
|---:|---:|---:|---:|---:|
| 16 | 9 | 16 | 0 | 16 |
| 32 | 16 | 32 | 0 | 32 |
| 64 | 31 | 64 | 0 | 64 |
| 128 | 58 | 128 | 0 | 128 |
| 256 | 113 | 256 | 0 | 256 |
| 512 | 222 | 512 | 0 | 512 |
| 1024 | 421 | 1024 | 0 | 1024 |

This is the exact five-component tangent at both ports, not the attachment's
coarser tropical signature. No temporal skip is credited to this experiment.

## Isabelle scope

The clean `Temporal_Clock_Jumps` session contains five accepted theories.
New statements prove the F/M exponent rebase and dead-phase truncation for
arbitrary durations, rational inverse-three coordinate conjugacy, signed
radix-64 tangent reconstruction, and decimal fixed-root/growth rebasing.
`Inverse_Three_Lift.thy` proves, for every q≥7,

```text
3^(2^(q-2)) = 1 - 3*2^q  (mod 2^(q+6)),
```

with a separate q=6 inverse certificate using coefficient 35. It also proves
the vanishing second difference of affine phase translation. Every theorem
group rejects oracle dependencies; there are no `sorry` or `oops` admissions.
These are exact algebraic specifications, not a proof of Python extraction or
an unconditional theorem discovering future valuation/candidate clocks.

## Public runtime boundary

The public cache probe still measures the actual 196 and physical Collatz
indexed-output paths, with exact output and boundary contexts retained. The
new conditional F/M and local inverse-clock APIs are not automatically admitted
as those schedulers' temporal certificates. A successful local quotient does
not establish equality for their stronger output consumers.

The frozen public report is exactly equal to the pre-change diagnostic
counter report:

| Family | N | Retained results | Early hits / result requests |
|---|---:|---:|---:|
| 196 | 8 | 143 | 47 / 305 |
| 196 | 16 | 597 | 228 / 1,197 |
| 196 | 32 | 2,305 | 1,000 / 4,593 |
| Physical Collatz | 8 | 111 | 48 / 231 |
| Physical Collatz | 16 | 248 | 140 / 530 |
| Physical Collatz | 32 | 1,024 | 579 / 2,136 |

Every identical warm point query has one point-cache hit and zero new result
work. At N32, 2,035 decimal and 991 Collatz entries contain boundary context.
Dropping boundary operands creates 54 and 33 conflicted fibers respectively;
those operands cannot simply be omitted from the equality key. This is where
public result growth still concentrates.

The F/M audit measures known-capacity occurrence jumps and charged bounded
setup, not a faster production candidate classifier. Candidate construction
(`nth`) is also a different operation from a Pépin/LL recurrence test.

Fresh counts and validation details are recorded in the
[evidence report](../results/current/clock-coordinate-growth-2026-09-10/README.md). They distinguish actual interner hits, endpoint grammar size, primitive
trajectory work, and cold/warm public requests. The unresolved work is exact
future boundary/suffix demand for 196/Collatz and candidate-clock injection for
F/M, rather than duplicate storage of the already-consumed phase history.


## Validation

All five Isabelle theories pass the clean session. The frozen source passes
72 focused regressions and 43 repository checks, strict mypy across 1,198 files,
Ruff, and `git diff --check`. Every accepted command stays within the existing
35-second/1-GiB guard. The combined policy invocation timed out; its two complete
files passed separately without raising that limit. This is not a full-suite run.
