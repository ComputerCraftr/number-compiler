# Cylinder CLI release fixes — 2026-09-12

> Superseded classification policy, September 12: production recurrence runners
> and their CLI enabling flags have been removed. Commands using
> `--allow-classical-ceiling` or `--max-classical-squarings` below are historical
> and now rejected. See the [current recurrence-removal record](production-shadow-jet-release-blocker-2026-09-12.md)
> and [candidate recovery audit](candidate-shadow-recovery-audit-2026-09-12.md).
> The release remains blocked by the missing powered construction and proofs.

This follows the [adversarial audit](cylinder-cli-adversarial-audit-2026-09-12.md).
The implementation fixes concrete dispatch, work accounting, repeated-work and
association defects. It does **not** close the universal terminal selector,
nonlinear quotient or all-future ray theorem. Release claims requiring those
results remain blocked; no acceptance assertion or release time limit was relaxed.
The [P0 acceptance ledger](cylinder-p0-release-gates-2026-09-12.md) supersedes
earlier audit priorities. Conditional checked factor output is accepted; the
powered construction, refinement and performance obligations remain P0.

## Implemented behavior

- Classical certificate construction collects a gcd only when the factor
  consumer requests it. `classify --factor` has an explicit
  `--max-factor-products` budget (default 4096); preflight occurs before candidate
  powering. JSON reports `product-budget-exceeded`, `no-split`, or `available`.
  Increasing a budget can retry a cached theorem without replaying its recurrence.
- `--max-classical-squarings` (default 4096) independently bounds the opt-in CLI
  recurrence. An unresolved result stays unknown when the budget is insufficient.
  `--max-candidate-bits` remains a separate admission limit.
- Large Mersenne exponent gates return unknown outside the supported exact
  primality range, except immediately known even/divisible-by-three composites.
  Within the exact 64-bit gate, composite status does not require complete
  exponent factorization: the optional symbolic witness search checks divisors
  only through 1000. A missing witness never turns a composite bit into prime.
- The CLI's coefficient probe and supplied-root helper share the proper-gcd
  consumer. `classify` identifies a numeric witness as `proper-coefficient-gcd`;
  it does not claim that a Frobenius coordinate is a quadratic root.
- `observe` exposes actual demanded observer results. Collatz uses the existing
  digit-step owner to discover a bounded prefix from an odd seed, charges that
  discovery, constructs canonical event actions and consumes their observers.
  Discovery remains linear in this finite prefix. These are accelerated odd
  events; ordinary `nth collatz` indices still count physical steps.
- `observe 196` consumes the powered current target's mirror obstruction.
  `observe fermat/mersenne --defect` checks a **supplied** quadratic root, then
  consumes the primary carry key and signed field from one shared square.
  Neither command claims an all-future or candidate-derived terminal theorem.
- Event words now have a canonical largest-dyadic-prefix association. Different
  parenthesizations of the same event word intern to the same node. Uniform runs
  retain logarithmic shared construction, including an action of length `10^100`.
  This is an association quotient; distinct words are not merged using sampled
  observers. General normalization work is charged and may exceed observation
  work; there is no universal small-node-growth claim.
- A Collatz observer caches at most 16 demanded specializations, including their
  shared intermediate nodes. A tile caches its prepared square and normalization,
  without retaining successor tiles or a whole orbit. These caches rely on the
  owners' immutable-value contract, as existing action/cocycle caches do.
- The scalar mirror ladder reads each noncentral digit once, retains the mirror defect,
  and folds that shared word per sheet. A 1024-digit palindrome now requires
  1024 digit callbacks rather than 24,576. Coefficient folding still costs work
  per sheet, so this observer is demand-driven.
- Positive-generation mirror demands now fold shared clipped subtrees of the
  completed output DAG, with no scalar point queries. Forward and reverse
  summaries compose in opposite orders, using the clipped child span for the
  exponent shift. Each sheet has its own fold; leaf work across sheets is
  charged. Two workspace accounts are reused, cleared after every sheet and
  disposed when the projection closes. Interior padding is rejected. CLI JSON
  includes work counters and peak/retained node counts. Cold output construction
  is still required; this does not close the powered-constructor gate.
- Unsupported primitive wiring is rejected before the completed-result lookup.
  The lookup retains its full key/context validation.
- Issued applications retain a charged copy of their admitted action, source and
  wiring, together with the exact immutable port tuple. Repeated point reads
  reuse port admission while retaining live source/action/wiring checks; forged
  tuple replacements and in-place handle changes are rejected before a cache
  answer. The registry also binds the original source lease ID, rejecting an
  alias to a second lease of the same tile. It independently audits the new
  eight-node admission record.
- Numeric Collatz materialization skips exact width discovery if the existing
  conservative bound already fits the requested output cap. Tight caps still
  receive the exact check. A local radix-6, seed-27, index-50 sample improved
  from the audit's approximately 4.4 seconds to 2.7 seconds. This single timing
  is not a general scaling claim.

## CLI examples

```sh
number-compiler observe collatz 3 --seed 27 --kind modular
number-compiler observe collatz 3 --seed 27 --kind hensel --precision 8 --target 47
number-compiler observe collatz 3 --seed 27 --kind tropical --s-weight 1 --z-weight -1
number-compiler observe 196 3
number-compiler observe mersenne 11 --defect 621
number-compiler classify mersenne 131 --factor --allow-classical-ceiling
number-compiler classify fermat 12 --factor --allow-classical-ceiling --max-factor-products 4098
```

The three-event Collatz output is `(upper, offset, lower)=(27,23,16)`;
`(27*27+23)/16=47`. The source prefix reports nine radix-4 source-digit visits.
The supplied M11 root 621 prints factor 23. Supplying the actual Frobenius
coordinate 391 to the root command is rejected because it is not a root.
The final F12 command explicitly permits the previously unbudgeted extra 4098
ring products; a proper split is still not guaranteed.

## Isabelle boundary

`Cylinder_Vector_Refinement` now proves coefficientwise signed shifts, vector
append, clipped append, forward-minus-reverse equality to `folded_difference`,
and terminal-sheet zero iff the digit list equals its reversal. It covers the
cyclic and negacyclic sheets used by `TwistedCylinderProjection.append`; it does
not substitute scalar evaluated equality for a vector invariant. The companion
word-summary append/clip/associativity lemmas use an explicitly imported
polynomial theory. The entire session builds with oracle-dependency checks.
Python arena refinement and cheap construction of the demanded target remain
separate obligations.

`Runtime_Cylinder_Refinement` is part of `Etale_Primary_Carry`. It proves:

- Nonzero folded **vectors** imply a current mirror mismatch, and a zero vector
  at a sheet at least as wide as the target is equivalent to palindrome equality.
  The exact ladder is modeled: cyclic width `d`, negacyclic width `d`, then
  negacyclic widths `2d`, `4d`, and so on. Its first stopping index exists for
  positive `d`; returning no obstruction is equivalent to current-target
  palindrome equality. This closes the earlier coarse-bound-only proof gap.
- The Hensel result equals the explicit residue
  `inv(a) * (2^E*r - b) mod 2^(q+E)`, assuming the modular-inverse equation.
  Membership is equivalent to existence of an integral affine output in the
  target cylinder. These are `runtime_hensel_returned_residue` and
  `runtime_hensel_integral_target`; exact event-valuation admission is separate.
- Event-tree counters refine list length and summed divisions, including the
  exact S-arithmetic exponent and physical-tick records.
- Min-plus transfer composition is associative. The offset of the event-tree
  transfer equals the minimum of its recursively defined polynomial support
  weights, for arbitrary integer weights and with `None` for empty support.
- Concrete M11/F5 counterexamples separating the premises: the zero root exists
  on composite M11; neither actual M11 probe coordinate is a quadratic root;
  the stated nonzero F5 coordinates both have gcd one with F5.

All exported theorem groups reject oracle dependencies. This adds formal
semantics matching the runtime predicates and Python differential/dispatch
checks. It is not an extracted implementation or a complete Isabelle proof of
Python arena allocation, cache integrity, or its normalization algorithm.

The following obligations remain open and **must not** be marked green:

1. A candidate-derived terminal construction with the required root/nontrivial
   support properties and equality to the compact carry key.
2. The Fermat/Mersenne separation property needed by that construction.
   A zero root alone cannot determine primality, and a nonzero Frobenius defect
   alone cannot guarantee a proper coefficient gcd. Factor printing is conditional;
   universal factor discovery is not the accepted release requirement.
3. A nonlinear source quotient with genuine aliases, successor and consumer
   agreement, and acceptable discovery/normalization growth for general rays.
   Reassociation of an already known word is insufficient.
4. Separately, the all-future Collatz and 196 research assertions. Current-target observations do not
   prove them.

## Verification

The new CLI regression tests cover actual dispatch, known numeric values,
proper-factor output, invalid-root rejection, all seven Collatz observer kinds,
budget cutoffs, witness retry, exact-cap rejection, shared square work, shared
observer work, all ternary valuation words of length five under different
associations, and the huge uniform-action control.

`python -m devtools.proofs.cylinder_skew_probe` now also records source-derived
prefixes for seeds 27, 97 and 871 at 1, 2, 4, 8, 16 and 32 events. At 32 events:

| Seed | Discovery digit visits | Arena nodes | Normalization compositions | Observer nodes |
| --- | ---: | ---: | ---: | ---: |
| 27 | 145 | 72 | 70 | 23 |
| 97 | 143 | 70 | 66 | 23 |
| 871 | 197 | 74 | 71 | 26 |

These measurements retain all construction costs instead of substituting the
11-node supplied A1024 control for actual-input evidence.

The first broad unit diagnostic timed out at the unchanged 300-second guard
while sources were still being edited; it is not release evidence. A subsequent
frozen serial run completed in 296.8 seconds with **4,718 passed, four failed**
and 1,254 validation tests deselected. All four failures matched the baseline:
two repeated port-admission work failures and two wiring-before-lookup failures.
They were then fixed without changing the tests. The relevant authority suite
passed **157 tests**; wiring and CLI regressions, including three new forged
binding checks, passed **76 tests**. The full rerun is described below.
The preceding full run reached the final portion with no failure markers before
its unchanged 300-second guard stopped it. It is incomplete. A subsequent
source-lease alias fix has separate targeted validation; the full time gate
has not been established on that revision.

The broader opt-in Collatz audit distinguishes three problems:

- The no-interpreter test asserts zero `temporal_leaf_applications`, although
  the current metric counts actual canonical finite tile evaluations. These
  evaluations remain charged; the metric has not been zeroed to pass the test.
- The production physical point path does not consume the binary-to-radix-4
  source morphism. The current route is `PoweredCollatzTerm` →
  `HashLifeBlockIndex` → certified tile projection → `PrimitiveTileKernelAdapter`.
  The radix-4 codec instead has a consumer in the separate `FieldTransferExecutor`
  backend. Closing this requires a real source-arena handoff and an
  output-equivalence check; merely bumping its counter would be false.
- The probe expects an old interface-work blocker, while current measurements
  report completed-result retention outside the doubling envelope (248 to 1,024
  entries from N16 to N32). The gate remains red. No expectation was relaxed.

Earlier targeted checks passed **134 tests** (four validation cases deselected
by the existing default marker). The full `Etale_Primary_Carry` session, including
min-plus event-tree semantics, the exact mirror stopping ladder and explicit
Hensel pullback semantics, built successfully with oracle checks enabled.
The final lease-alias and authority regression group passed **238 tests** in
19.5 seconds. Ruff, strict mypy and repository line/recursion/package checks
passed; no authored source exceeds 1,000 lines. Strict mypy over `src tests devtools`
passed for 1,243 files. Running mypy over `.` instead encounters pre-existing
duplicate generated modules under ignored `results/`; the authored directories
were checked explicitly. No test assertion or release time limit was relaxed.

Local diagnostics:

- `/tmp/cylinder-fix-final-selected-0912.{log,json}`
- `/tmp/cylinder-fix-frozen-unit-0912.{log,json}`
- `/tmp/cylinder-admission-fix-0912.{log,json}`
- `/tmp/cylinder-admission-regressions-0912.{log,json}`
- `/tmp/cylinder-final-unit-0912.{log,json}`

The final frozen unit run is recorded in
`/tmp/cylinder-final-frozen-unit-v2-0912.{log,json}`. It also hit the unchanged
300-second guard near the end, with no failure markers in the captured output.
It did not finish: **the ordinary-unit time gate remains unpassed**. The final
admission-only check passed **61 tests** in 9.7 seconds and is recorded in
`/tmp/cylinder-final-authority-0912.{log,json}`.
The documented mathematical and production source-bridge blockers remain open;
this change must not be represented as a green release.

## P0 follow-up validation

The final finite-DAG/factor/authority regression group passed **86 tests** in
13.05 seconds. Strict mypy checked **1,245 authored files**; Ruff and repository
line/recursion/package checks passed. The complete `Etale_Primary_Carry` session
also passed, including the new vector-to-palindrome theorem and oracle checks.
Isabelle used a separate 4 GiB build allowance; Python performance gates retain
their existing 1 GiB allowance and time limits.

With the rejected action-child cache removed and live action validation intact,
fresh 196 terms returned the same mirror certificates through both consumers:

| Generation | Scalar point consumer | DAG consumer | Scalar requests, old → new | Peak nodes, old → new |
| --- | ---: | ---: | ---: | ---: |
| 8 | 0.633 s | 0.448 s | 6 → 0 | 7,239 → 7,249 |
| 16 | 1.669 s | 1.183 s | 8 → 0 | 15,718 → 15,723 |

These are single local samples, not a general complexity claim. The DAG fold
still constructs the target first and performs a separate traversal per sheet.
The peak counts include that construction. The shared uniform 65,536-digit
control required 17 subtree evaluations for one sheet; it is a sharing control,
not evidence that arbitrary powered targets admit such compression.

Source fingerprint for the final frozen run:
`d7acca6110eb5e6327c45bfcc5cbed844a2a05569aaa61ea2c5fb9a97ff698a2`.
Local evidence:

- `/tmp/cylinder-p0-final-selected-v2-0912.{log,json}`
- `/tmp/cylinder-p0-vector-proof-final-0912.{log,json}`
- `/tmp/cylinder-p0-final-mirror-compare-0912.{log,json}`
- `/tmp/cylinder-p0-policy-final-0912.{log,json}`
- `/tmp/cylinder-p0-frozen-unit-final-0912.{log,json,xml}`

The final frozen ordinary-unit run **timed out at 300.08 seconds**, with progress
near 98% and no captured failure markers. It produced no completed JUnit report.
The source fingerprint was unchanged before and after the run. Sampled group
footprint peaked at 680,936,408 bytes, below the unchanged 1 GiB limit. The
ordinary-unit time gate remains unpassed; none of the new finite proofs or
selected tests changes that result.

The [retained evidence](../results/current/cylinder-p0-release-2026-09-12/validation.json)
records the release hold and copies the completed diagnostics out of `/tmp`.

The three-case opt-in Collatz group timed out at 35 seconds after two failure
markers, so it is incomplete. Rerunning its first two gates alone completed in
30.79 seconds with **two failures**: N256 still reports seven
`temporal_leaf_applications` against the unchanged zero assertion, and N64 has
no `collatz_radix4_source_morphism_compilations` counter because that production
path still does not consume the codec. These results are preserved in
`source-gates.*` in the evidence directory. No work counter was fabricated,
assertion changed, or release condition relaxed.
