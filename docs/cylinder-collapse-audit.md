# Cylinder pullback and future-collapse audit — September 11, 2026

The recorded collapses are real, but they certify different layers. Exact
endpoint sharing saves future evaluations across a corpus. Collatz's bounded
physical cylinder experiment additionally stabilizes its scalar future work.
Neither result supplies the missing general production constructor theorem.
This audit reads the current proof and implementation owners and repeats the
small physical-chart and seed-196 memo probes. It does not rerun the large
width-eight or odd-16-bit corpus enumerations.

## What is already proved or implemented

For `P(x)=(3^h*x+c)/2^k`, the exact integral preimage of `C(q,r)` is

```
C(q+k, 3^(-h) * (2^k*r-c) mod 2^(q+k)).
```

`HenselCylinder.pullback` implements this formula, including integrality.
`Hensel_Cylinders.thy` proves the congruence characterization and
`odd_inverse_cylinder_pullback`, under its explicit cancellation and anchor
premises. It also proves integral branch composition, sibling union and
radix-64 prefix consumption. These are existing results, not missing formulas.

`Collatz_Cylinder_Constructor.thy` derives valuations from exact occurrences,
proves normalized prefix composition and embeds accelerated events into physical
time. Its concrete `collatz_cylinder_block` definition follows the exact
successor for each event. The theorem
`collatz_cylinder_constructor_evaluations_exact` explicitly proves that this
constructor takes `events` valuation constructions. It is an exact semantic
reference, not a logarithmic implementation proof.

For 196, `Decimal_Publisher_Constructor.thy` proves the two-port local publisher,
normalization at the seam, and consumer pullback:

```
pullback(P,D) = D o P
pullback(P2 o P1,D) = pullback(P1,pullback(P2,D))
[a*(M*x+b) >= t] = [(a*M)*x >= t-a*b].
```

Its 25-slot theorem bounds transported contributions under the stated
nilpotence hypotheses once their itinerary is available. It explicitly does
not construct all future growth/birth itineraries or bound publisher DAG work.
The symbolic composition identities do not define an executable canonical
grammar for every growing, reflected, two-port publisher.

## Growth evidence and what actually merges

The existing [endpoint audit](endpoint-seam-powering-audit.md) records:

| Corpus | Source states | Powered endpoints | Work still performed |
| --- | ---: | ---: | --- |
| Reverse/add reachable width eight | 123,462 | 33,429 at A32 | 1,227,529 primitive transitions; 16,375,578 input pair-position visits |
| Accelerated Collatz odd 16-bit sources | 32,768 | 4,474 at A16 | 195,658 primitive transitions |

These are exact endpoint mergers. Each distinct current endpoint is advanced
once on the following frontier, so sharing saves real future computation.
The reverse/add baseline without frontier sharing is 3,950,784 primitive
transitions. The audit still constructs intermediate endpoints; it does not
discover all those mergers before performing their producing transitions.

The fresh physical Collatz probe uses one arena per source chart and requests
T16, T128 and T1024 in that order:

| Positive source chart | T16 endpoint / weighted IDs | T128 IDs | T1024 IDs | Scalar future evaluations at T128 / T1024 |
| --- | --- | --- | --- | --- |
| `0<x<2^3` | 3 / 3 | 3 / 3 | 3 / 3 | 27 / 27 |
| `0<x<2^5` | 8 / 10 | 3 / 7 | 3 / 7 | 471 / 471 |
| `0<x<2^8` | 84 / 98 | 3 / 20 | 3 / 20 | 3,928 / 3,928 |

This reproduces actual future-work stabilization on the bounded positive
charts. Weighted IDs retain demanded event counts. Zero original-source bit
callbacks does not mean zero arithmetic: `_constant_powers` explicitly evaluates
`3*x+1` or `x//2` at scalar future endpoints and counts those evaluations.
The three terminal values are the reached physical cycle. This probe makes
no universal positive convergence claim and includes no negative inputs.

The fresh seed-196 endpoint-memo probe reproduces:

| Duration | Endpoint width | Cumulative primitive successors | Retained result keys | Extra primitives on repeat |
| ---: | ---: | ---: | ---: | ---: |
| 16 | 9 | 16 | 31 | 0 |
| 32 | 16 | 32 | 63 | 0 |
| 64 | 31 | 64 | 127 | 0 |
| 128 | 58 | 128 | 255 | 0 |
| 256 | 113 | 256 | 511 | 0 |
| 512 | 222 | 512 | 1,023 | 0 |
| 1024 | 421 | 1024 | 2,047 | 0 |

Thus warmed result reuse is real, but this executor has no cold temporal
work collapse on seed 196. The earlier 4,095-state orbit audit likewise
reported distinct A1 endpoints throughout. This does not rule out sharing of
internal cylinder substructures in a better constructor.

## Exact remaining obligations

For a represented morphism A and admitted occurrence X, the desired constructor
must establish all of the following together:

1. The normalized application agrees with the exact demanded output, including
   boundary ports, growth/cropping and physical/event weights where requested.
2. Composition stays inside the representation and implements composition of
   the represented functions. Normalization preserves every admitted future
   consumer, rather than only the current domain label or endpoint sample.
3. Substitution constructs no forbidden dense midpoint and counts all newly
   built predicates, publisher applications, source reads and retained payload.
4. A size/work bound relates those counts to the source grammar and duration.
   A small final root, or one primitive object, is insufficient by itself.

For 196 the missing concrete owner is a lazy **two-port** future publisher.
The removed A4 prototype emitted index one as 10 instead of 11 because it
evaluated one direction before the opposite composite port was available.
Both port applications must remain symbolic until paired emission. This is
an implementation failure, not a domain-only counterexample to the clock.

For Collatz the research guard pullback and finite-image normalization already
perform useful composition. The missing production/formal bridge covers that
complete normalizer, source-chart admission, recursive target-tile publication,
resource ownership and arbitrary physical-time block selection. The old
accelerated guard constructor reached four final decision nodes at N16 while
performing 12,223 guard visits; its N32 guard-budget failure is historical
evidence about that route, not a failure of the newer sparse physical probe.

The [production audit](constructor-quotient-proof-audit.md) still records rising
cold causal frames from T16 to T32: 15,912 to 53,396 for 196, and 5,588 to
21,233 for Collatz 27. These historical scheduler measurements were not rerun
here. Supported Collatz root/cycle dispatch is already integrated, but the
general research constructor is not a production tile publisher.

## Fresh validation

The combined bounded probe completes in 0.693 seconds with a sampled peak of
52,167,136 bytes. All **32** selected cylinder, endpoint and constructor-obligation
regressions pass in **0.55 seconds**, including midpoint/primitive poison checks
and the 471-consumption physical-power regression. The large historical corpus
counts above remain labelled historical; this is not a new full-suite or
general logarithmic-powering certificate. Logs and resource JSON remain in
`/tmp`. No production behavior or theorem statement changed during this audit.
