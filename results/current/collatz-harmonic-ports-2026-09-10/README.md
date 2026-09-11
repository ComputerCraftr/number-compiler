# Collatz harmonic projection and refinement evidence

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

This checkpoint applies the carry/harmonic proof to Collatz and reproduces the
specified finite output-response refinement. The research code does not alter
production quotient identity. The linked [research note](../../../docs/collatz-harmonic-port-actions.md)
states the algebra, observer definitions, and remaining closure obligations.

## Reproduced controls

- Two-wire F2[y]/y^5 carry-occupancy responses at lengths 1..8:
  **5,17,53,161,485,1457,3752,7568**. There are **29,655** explored generator
  transitions; every retained response is checked on all three incoming ports
  against an independently scanned witness. All project onto the five domain
  actions; empty identity is 012.
- The binary temporal identity is checked over every odd 16-bit original
  source with a nonempty normalized radix-64 tail. Even normalized tails and
  residual phase zero remain admitted: **32,766** nonempty tails, **two** empty
  tails, and **518** even normalized tails out of **32,768** odd original
  sources. JUnit records all 16 partition counts and phases 0..5.
- All **7,776** residual-phase sequences annihilate the homogeneous fifth-order
  source jet. Actual trajectories 1 and 27 demonstrate that source-dependent
  birth offsets can still differ after five events.
- On the existing **1,984-source** fixture, full binary output rows
  `(J(3m),J(3m+1),J(3m+2))` plus the prior domain/Hensel key give **1,977**
  classes and **7 conflicts / 14 sources**. The exact pairs are pinned in
  `test_harmonic_response_refinement.py`.
- Phi5 has fibers **28/16/4/7/9**. Adding its pointwise digit word yields
  **1,984 singleton classes**, an injective control rather than closure.
  All six consumed-frame gauge families at depths 1,193,385 remain equal.

## Definitions and failed candidates

The complete binary output response includes transported source and carry
birth. Using only the binary birth jets gave **1,702 classes / 253 conflicted
classes / 535 conflicted sources** (`fixture-definition-check.log`); this
candidate was rejected. `output-response-definition-check.log` identifies the
correct all-port output observer. Neither observer should be confused with
the spatial radix-64 wire-occupancy function.

The attachment's named 381-line relational decimation test and exact
5,000-source corpus are absent from this tree. Its reported (2,3) results
(1,744 classes, 652 conflicted classes) have not been independently reproduced.
No selective refinement of those missing corpus classes is claimed.

The supplied five-round nonlinear refinement conclusion does not follow from
linear source death. The proof compares identical event/birth lists; new
source-dependent births can retain distinctions. A forcing-root mismatch is
also a valid dying event under an unrestricted occurrence domain, not a symbol
that may be dropped from admission. Refinement needs labelled transitions and
the independent occurrence-admission domain.

## Formal scope

`Collatz_Harmonic_Ports.thy` proves exact two-wire projection, reachable carry
ports, spatial composition, and conditional five-step linear source death.
The subsequent geometry update adds Boolean last-decisive and two-wire prefix
laws. The full session passes without oracle dependencies; final proof evidence
is in [the geometry checkpoint](../geometry-derived-carry-2026-09-10/README.md).
Python oracle tests establish the concrete jet identity and finite counts;
the theory does not verify that Python program or nonlinear powered closure.

## Validation organization

The exhaustive work is in the opt-in validation partition: 18 harmonic proof
tests and three response-refinement tests. Ordinary tests retain only small
algebraic/negative controls. Final source fingerprints and combined targeted
checks are recorded in the [geometry checkpoint](../geometry-derived-carry-2026-09-10/README.md),
which also incorporates the user's follow-up request to remove expanded
geometry-derived carry tests. This is not a new full ordinary or unfiltered
release-suite result.

Earlier `*-first` and definition-check logs are exploratory evidence. The
final JUnit and guard reports identify the tests run on the final authored
source; no timing from an intermediate source is presented as final evidence.

On the final combined source
`26257fefdc724c218dc34ee128f93e0634f0e3f5b77d563312c1de48050a44a8`,
all **29** selected Collatz validation tests pass in **23.706 seconds** of
aggregate JUnit time: 18 harmonic proofs, three new refinement tests, and eight
existing carry-domain/Hensel controls. The ordinary harmonic and geometry
regressions also pass within the combined 109-test focused run. Final JUnit and
guard files live in the geometry checkpoint, where their fingerprints and
complete selected manifests are verified in `validation-summary.json`.
