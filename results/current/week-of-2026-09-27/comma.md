# Comma / A367620

[Week of 2026-09-27](README.md) · [Documentation index](../../../docs/index.md)

## Records

- [Weighted tree locator and shared control proofs](#weighted-tree-locator-and-shared-control-proofs)

- [Comma canonical rank checking and bounded sector reuse](#comma-canonical-rank-checking-and-bounded-sector-reuse)
- [September 27: symbolic Near proof and demand-only totality evaluation](#september-27-symbolic-near-proof-and-demand-only-totality-evaluation)
- [One-step comma rank checking and summary transport](#one-step-comma-rank-checking-and-summary-transport)
- [Powered comma decade layers](#powered-comma-decade-layers)
- [Comma packed temporal control](#comma-packed-temporal-control)
- [Comma Entry diagonal and Frobenius audit](#comma-entry-diagonal-and-frobenius-audit)
- [Comma Frobenius recurrence and proof construction](#comma-frobenius-recurrence-and-proof-construction)

- [Residual blocks and lazy proof contexts](#residual-blocks-and-lazy-proof-contexts)
- [Direct guarded cycle count](#direct-guarded-cycle-count)
- [Ordered-root admission and demand-only proof evaluation](#ordered-root-admission-and-demand-only-proof-evaluation)

- [Punctured-port construction and physical prefixes](#punctured-port-construction-and-physical-prefixes)

## Provenance

Original records and caveats follow. Their evidence certifies only its recorded
source and scope. Records without a precise day retain their original weekly
context; listing order is not evidence of execution order.

## Direct guarded cycle count

**2026-09-27. Changes.** `safe_complete_cycles` now evaluates the strict
guard floor/clamp formula directly, instead of allocating a `PrefixSafety`
action and asking for its first failure. The formula is the existing
`comma_safe_cycle_count_maximal` theorem: a positive count `c` is admitted
exactly while `G + (c-1)*D < H`, also bounded by the requested term count.

**Independent review and repair.** A forged-transfer test exposed a helper
that trusted supplied period/displacement/guard values. Those fields now
require exact integer types and the shared phase-displacement formula before
any division or skip. Validation constructs no replacement action and scans
no phase cycle. Tests retain all 90 sector/phase combinations, strict equality,
zero targets, large clamps, and malformed or foreign transfers.

The review also rejected using a matching last digit as a complete fork
classifier: source 19630 reaches fork 19918 after eight steps, whereas 19640
reaches 19928, which has one child. Root-chamber and digit coincidence do not
replace exact headroom. No forest or fuel gate was removed. The compact
all-source constructor/rank instance, weighted lift and unconditional future
branch safety remain separate release obligations.

## Ordered-root admission and demand-only proof evaluation

**2026-09-27. Changes.** The response evaluator now selects one child before
evaluating it, instead of mapping evaluation over every child and selecting
afterward. The equation preserves invalid-index behavior. Rank checking
reuses one context-owned theorem auditor, after checking each proposition,
premise and hypothesis boundary. Final whole-theorem oracle audits remain.
Evaluation and audit times are reported separately.

**Measured boundary.** At source
`73abbfe793050860e61db51078c22e551deec6ba3cce563fc823e1b66dc0f5ab`,
the focused mask, rank-smoke and Mahler sessions passed. The full
`Comma_Fast_Totality` gate timed out at 60.179 seconds / 2,553,664,552 sampled
peak bytes. A preceding 91-row smoke measured 6,032 ms evaluation and 51 ms
auditing. It does not support attributing the remaining timeout to auditing.
The concrete residual classifier is still absent; the full check still uses
84,084 local rank obligations.

**Root-frame repair.** The new focused `Comma_Vieta_Root` session reuses
actual phase/displacement definitions for ordered roots, guarded first-boundary
run counts, residual transport and exact terminal consumers. Local arithmetic
has no rank-candidate premise. It does not supply an all-state residual
classifier, weighted recurring return or global branch-safety theorem.

The proposed one-row normalization needs a correction: for sector 1, orbit 5,
period 460, the roots at indices 4, 5, 6 are 99, 98, 87. Point 90 lies in
interval 6, but point 100 lies in interval 4. Decrementing the index only once
does not normalize the translated point. Canonical admitted Entry states at
clock six, offsets 55 and 65, bind these two diagonal positions. This is an
admitted-state witness, not a source-20 trajectory witness or a refutation of
the complete cylinder. Correct normalization must select the first crossed
ordered root and allow a second crossing.
The root-entry run formula also requires its explicit small-residual domain;
dropping it makes `f=3,d=2,u=25` a counterexample. The corrected local row
port uses the actual adjacent phase-gap sum (at least 12), preserves the
ordered-root equation and handles zero, one or two crossings. A separate
bounded selector examines at most ten actual phase positions, with explicit
headroom, alignment and source-frame premises. It does not establish cyclic
re-entry, the all-state residual classifier or the weighted winning return.

**Remaining release authority.** Canonical successor-source authentication,
the concrete residual classifier, weighted occurrence lifting and the checked
314-fork/+924 return must precede forest deletion. No imported Mahler
higher-half claim, generated rank values or passing local arithmetic lemma is
substituted for them. Final validation below records the later source and
does not reinterpret this timeout as success.

## Comma canonical rank checking and bounded sector reuse

Record period: 2026-09-26–27. Cross-week work is filed once, in its completion week.

**Objective (September 26–27).** Repair the concrete constructor-rank proof
without treating it as the separate future-branch theorem or authorizing the
forest cutover prematurely.

**Changes and checked scope.**

- Added a downstream observation bridge from the weighted round, and proved
  successful macro uniqueness plus boundary existence conditional on a checked
  decade rank. The `THE` interface has no executable code equation and does not
  discharge that condition.
- Defined the untrusted rank candidate through typed, shared list blocks.
  This replaces a giant textual HOL definition whose type inference timed out.
  No generated transition, successor or successful-check flag is assumed.
- Centralized numeral canonicalization at source, observed target and lookup
  boundaries. The `1`/`Suc 0` regression proves equal, closed, oracle-free rank
  equations. Added the missing closed-natural subtraction rules.
- Replaced per-row generic proof search with Continue/Fork/Landmine rules and
  balanced adjacent-interval aggregation. The checker still proves every row;
  its candidate numbers are not a proof.
- Reused exact completed sector links through an 8,192-entry owner-local cache.
  Keys preserve the complete phase/source chart; binding and oracle checks
  precede publication. Changed-source, changed-phase, repeat and invalidation
  checks pass. Admission predicates also use a bounded exact-proposition memo.
- Removed duplicated sector-link certification, narrowed closed key arithmetic,
  and rechecked generation after the final rank oracle audit. Optional progress
  output survives watchdog termination and is never consumed as proof input.

**Independent review.** The old aggregation was a two-level chain, not a flat
84,084-link conjunction; no quadratic aggregation claim is supported. Current
balanced aggregation is checked. The new cache does not equate occurrences
merely because their arithmetic representatives agree. There is no unconditional
constructor-totality or infinite-branch theorem in this increment.

**Performance provenance.** Local evidence lives under
`results/current/comma-total-cutover-2026-09-26/`; these are local evidence names,
not portable downloads. All Isabelle runs retain the 60-second/4-GiB guard,
50-second internal timeout, one ML thread and the five-second local diagnostic.

| Revision / evidence | Result and scope |
| --- | --- |
| `balanced-rank-smoke-2` | All 91 phase-zero rows PASS; observation 13,186 ms, lookup 174 ms, comparison 8 ms, aggregation 12 ms. |
| `full-rank-2`, `e80999674c0c` | Full-instance TIMEOUT at 60.10 s; fingerprint and revision unchanged. Buffered progress is unavailable, not zero. |
| `sector-cache-rank-smoke`, `e796af4bbd27` | All 91 rows PASS; observation 11,212 ms, lookup 159 ms, comparison 10 ms, aggregation 12 ms. This is one trial, not a general speed bound. |
| Final source | `a8cf618a84a53929fc7cef687bee86bb662a40c2ff648cd65d525781857bd23b`; final validation recorded below. |

**Remaining obligations.** Complete the 84,084-state constructor rank, then
check the distinct 14,784-state boundary classification (14,470 losing, 314
winning), the lifted 314-fork/+924 return with positive literal weight, and
termination of the 17 decimal roots below 20. The source-20 unique prelude is
already proved; joining it to the winning classification remains necessary.
Executable weighted selection and public CLI refinement must agree with those
results. Production forest admission and its budget boundary remain in place;
no positive acceptance assertion was removed or converted into a refusal test.

The final full-instance attempt (`final-full-rank`) timed out at **60.112 s**
with **1,150,389,464 sampled bytes**; content and revision were unchanged. Its
append-only diagnostic records four completed phases (364 rows) at 39,926 ms:
38,911 ms observation, 805 ms lookup, 40 ms comparison and 58 ms aggregation.
It had constructed 1,349 Entry and 2,357 Near conversions by that checkpoint.
The remaining interval before termination is unclassified work, not zero work.
No complete rank theorem was exported. This demonstrates the next bottleneck
in the actual all-state run; the small regression improvement does not close it.

Final validation on the fingerprint above:

| Evidence | Result | Guard elapsed / sampled peak |
| --- | --- | --- |
| `final-witness` | Weighted/projection agreement, exact cache binding, repeat/phase/source changes and invalidation PASS | 28.66 s / 1,167,363,288 bytes |
| `final-rank-smoke` | Canonical alias and all 91 phase-zero rank rows PASS; generic total-macro session current | 40.07 s / 1,176,767,704 bytes |
| `final-observation-slice` | All 91 unchanged phase-five count/chart/event fixtures and forbidden-eager-work assertions PASS | 28.93 s / 1,170,181,264 bytes |
| `final-focused` | 409 arithmetic, CLI, cache, candidate-generation, history, evidence and proof-inventory tests PASS | 50.07 s / 89,408,112 bytes |
| `final-full-rank` | TIMEOUT; no complete rank theorem | 60.11 s / 1,150,389,464 bytes |
| `final-quality` | Strict mypy, Ruff, formatting (1,524 files), policy, documentation, proof inventory (47 sessions/160 theories) and diff checks PASS | 11.07 s / 636,224,880 bytes |

The final phase-zero rank profile records 10,999 ms observation, 167 ms lookup,
8 ms comparison and 15 ms aggregation. These are scoped measurements, not an
arbitrary-size verification bound. The 91-row regression and the failed full
instance remain separate acceptance results. No public CLI behavior changed.
Full units, P0, installed-wheel, growth and all-session acceptance were not
rerun for this proof-only increment; their existing holds remain active.



## September 27: symbolic Near proof and demand-only totality evaluation

Objective: remove eager Isabelle work identified by the Closed-Near review,
without treating local totality or a conditional infinite-path theorem as the
production forest cutover.

### Changes and established results

- Replaced the 4,860-case Near recurrence generator with generic phase,
  displacement, strict-prefix and maximality proofs. The executable closed germ
  divides out complete cycles and uses a natural-number residual counter;
  it does not allocate an ignored index list or enumerate admitted headrooms.
- Added a control-only sector/decade evaluator, proved equal to the canonical
  control owner on admitted states. Totality evaluation does not build weighted
  records or all-exponent occurrence certificates for each state.
- Kept binary numeral evaluation and explicit lazy case/Boolean congruences.
  Certified demand caches bind complete typed closed terms in one immutable
  context. Each category retains at most 8,192 equalities. Failed proofs do not
  publish; cache statistics include failures, evictions and inclusive time.
- Independent review found self-simproc re-entry on a miss; the evaluator now
  excludes its own procedure while retaining dependency procedures. Runtime
  probes additionally exposed nonmatching free-variable patterns and a unary-only
  numeral validator. Both were corrected before measuring successful reuse.
- A measured phase proof was executing repeatedly through the proof-method
  entry point. Smoke and full-range construction now run once in local setup,
  publish kernel-proved facts, and reuse those facts in final assertions.
  The unused replayable tactic/method was removed. The 32 disjoint full ranges
  and balanced joins preserve the original single-session resource budget.
- Moved generic unique-path lemmas into one Literal Bridge owner. Generic future
  proofs no longer rebuild source-20 entry or candidate rank data. Candidate
  tables belong to the concrete checked-instance session; source-20 applications
  remain downstream. No candidate number is imported as a theorem premise.
- The generic future session now checks complete-child rank soundness, exact
  delta paths, literal lifting, losing-branch exclusion and conditional infinite
  paths. The rank/cycle instance remains an explicit hypothesis.

### Validation and provenance

Final authored-source fingerprint: `ad218d3fc84fc32dd647c5bbd88360d6a920a004781861d8cc58dfc1f48ff33e`.
The focused builds below are incremental, serialized runs, with a 60-second/
4-GiB external guard and a 50-second Isabelle session timeout. Raw logs and
profiles remain ignored local evidence under
`results/current/comma-fast-control-2026-09-27/`; these are not portable downloads.
Earlier run names identify intermediate source and must not certify later edits.

| Local evidence prefix | Result and measured scope |
| --- | --- |
| `near-period-v7` | PASS: 9.624 s theory / 22.966 s guarded wall; universal phase/displacement lemmas. |
| `closed-near-analytic-v4` | PASS: 6.523 s theory / 19.928 s guarded wall; symbolic closed-germ correctness. |
| `fast-control-v3` | PASS: 1.982 s theory / 16.360 s guarded wall; admitted control refinement. |
| `totality-smoke-profile-v3` | Earlier no-memo probe timed out after offset 58; not a phase theorem. |
| `totality-smoke-memo-v3` | Intermediate memo probe proved rows then replayed them; timed out. This prompted the once-only entry fix. |
| `totality-smoke-memo-v4` | PASS: all 91 rows once, 22.748 s session execution / 37.165 s guarded wall. |
| `totality-smoke-memo-v5` | PASS after lower arithmetic reuse: 12.262 s session execution / 34.869 s guarded wall, sampled peak 1,176,030,328 bytes. Wall includes rebuilding the changed checker heap. |
| `totality-full-v1` | TIMEOUT inside range `[0,28)`: 59.911 s guarded wall, sampled peak 1,168,133,336 bytes. No full rectangle theorem. |
| `future-check-v15` | PASS: 11.175 s session execution / 26.160 s guarded wall, sampled peak 1,179,503,976 bytes; generic conditional future lemmas only. |

The final smoke profile records 2,180 period hits, 1,215 power-residue hits,
1,836 Near hits, 326 sector hits and 122 decade hits, with no failed cache
publication. All 91 offsets are visited exactly once. Inclusive timings overlap
across dependency levels and must not be added together.

The full-range timeout reports 2,329 decade hits, 1,179 published decade
results and one interrupted decade miss. This is measured partial progress,
not zero-cost missing instrumentation or a completed range. Headroom arithmetic
and new decade proof construction remain material costs.

Independent scope review found no weakened admitted Near domain, missing decisive
endpoint premise, hidden enumeration or oracle publication. It also checked
full-range coverage, own-procedure exclusion and closed cache authority.

### Remaining work and release status

- Complete the 84,084-state totality gate within the unchanged budget. The first
  28-phase range still times out despite local proof reuse.
- Check the concrete 14,784-state future classification and 314/+924 return;
  then discharge source-20/global-earliest and production weighted-selection
  obligations. Conditional infinite-path lifting is not that instance.
- Production forest admission and fuel remain in place. No CLI cutover, global
  safety claim, aggregate Isabelle pass or full-unit pass is claimed here.
  Existing unrelated family blockers remain active.

Final `final-checks` at the recorded fingerprint: **50 focused tests PASS**;
strict mypy, Ruff, formatting (1,526 files), repository policy, documentation,
proof inventory (58 sessions/179 theories) and diff checks PASS. Guard:
20.856 seconds / sampled peak 638,305,672 bytes under 35 seconds/1 GiB.
Full units and aggregate Isabelle acceptance were not rerun in this proof-only
change. Independent final review confirmed that the future theorems retain their
rank/cycle hypotheses and accumulate actual exponent deltas, rather than deriving
924 from phase equality. Raw profiles remain ignored; no production branch
admission was changed.


## One-step comma rank checking and summary transport

Record date: exact day not recorded; retained in its documented weekly context.

**Objective.** Replace repeated 27-round termination searches with one checked
successor per state, without turning untrusted rank data into branch authority.
This is proof-path work; production comma admission is unchanged.

**Changes.**

- One `Comma_Fast_Kernel` owns closed control evaluation. Rank checking adds
  only its predicate and selected candidate lookup; no weighted occurrence or
  `Comma_Round_Witness` evaluator enters that path.
- Rank data moved unchanged to a data-only session. The single selected lookup
  implementation retains internal table blocks, not a second parser or a full
  normalized table per query. The 84,084 decade heights and 14,784 future-branch
  rank codes are different mathematical candidates, with different obligations.
- The replacement release checker verifies strict rank decrease and the bound
  26 together. Its conclusion preserves the existing 27-inspection totality
  assertion. Phase ranges share one evaluator and are joined in a balanced tree.
- Endpoint projection now avoids normalizing the discarded sector count and
  `q*L+j`. The original arithmetic definitions remain the refinement owner.
- Removed the old observed-rank checker, its rules/ML driver and smoke, and the
  duplicate full `Comma_Decade_Rank_Instance`. The replacement assertion mapping
  is: full canonical rank → `Comma_Fast_Totality`; all phase-zero rows and
  numeral alias → `Comma_Fast_Rank_Smoke`; source/target lookup and authority →
  the single data owner and closed-term kernel. Flat-rank and insufficient-bound
  rejection are additional checked regressions. Weighted witness/phase-slice
  proofs remain for their distinct consumers.

**Established results.** `Comma_Fast_Decade_Rank` proves one-step checking
implies the existing semantic rank condition, bounded termination, and exact
height/terminal-label induction. `Comma_Decade_Summary_Transport` derives actual
exponent gain from the canonical crossing and refines a boundary constructor
using one initial round plus one summary lookup to `comma_total_macro`.
The latter theorem explicitly requires a checked complete summary table;
no such concrete table has yet been certified. Terminal delta zero is checked
in each terminal-summary row, not assumed from residue-phase equality.
Existential fuel remains only in the refinement statement connecting to the
existing reference semantics; the new boundary function has no fuel argument.

**Measurements and rejected closure.** The rank-only first-phase evaluator
performed exactly 91 decade observations, with zero decade memo hits: no hidden
termination-chain traversal. Before endpoint projection this phase took 8.77 s;
the endpoint-only samples took 5.73 s and 7.80 s. These are diagnostic samples, not a paired latency
acceptance result. The full final run completed phases 0–10 (1,001 rows) and
then timed out at 60.10 s, using 928,090,704 sampled bytes. It did not export
the complete theorem. Its final joins had not begun; recorded control-evaluation
cost dominates, so blaming the timeout on final range aggregation is unsupported.
The resource limit and positive assertions are unchanged.

**Independent review.** A separate explorer reviewed source binding, cache keys,
rank/proof ownership and exact exponent transport. It found no cross-engine
memo collision. Its confirmed dead sector-count normalization was removed.
The missing concrete summary, future partition, winning cycle and production
refinement remain explicit. A convenience terminal-delta lemma is not a
substitute for checking the table or its future consumers.

**Validation and provenance.** The constructor/full-gate source fingerprint is
`c3692ae800b79e7bcf54c07ddaf69576bcd1eaf3c3bdc29e9b2817771861ba10`.
The final source is `4c837efb14c41d69b9031533af61808c63083756b757260ddfcffd51d24080bf`;
the only subsequent source change strengthened the smoke's numeral-alias check
to exercise actual lookup-cache hits and retained-block reuse. It changes no
constructor, arithmetic theorem or full-rank dependency. `rank-smoke-alias`
passes in 25.06 s / 947,866,720 bytes.
The local ignored evidence directory is
`results/current/comma-rank-cutover-2026-09-27/`.
`rank-smoke-final` passes (28.53 s / 922,831,536 bytes, including a dependency
build); `summary-5` passes (15.78 s / 917,785,240 bytes); `rank-full-final`
is a timeout, not a pass. `regression-final` preserves the independent bounded
termination-search regression (31.67 s / 943,672,944 bytes); it is absent from
the release rank path. Strict mypy (1,531 files), Ruff, formatting, repository
policy, proof inventory (60 sessions / 181 theories), documentation and 47
proof-index tests pass in `quality-final` and again after the alias regression
in `quality-alias`. The independent Python candidate checks reproduce
all 84,084 heights; 11 candidate tests pass. The comma/API/firewall selection
passes 339 tests in 46.70 s under the 300-second/1-GiB unit limit. Its first
attempt incorrectly used the shorter 35-second probe limit and timed out;
that attempt remains recorded. Initial proof-script and diagnostic-path errors
also remain in the raw logs and are not presented as successful builds.

**Remaining release gate.** Finish the all-state kernel proof within 60 s;
instantiate and check terminal summaries; check the complete 14,784-state
future classification and 314-return; finish source-20 entry/earlier-source
exclusion and weighted scheduler selection. Neither the forest asset nor its
CLI admission is removed without those results. No whole-unit, installed-wheel
or aggregate release completion is claimed for this proof-only change.


## Powered comma decade layers

**Objective (2026-09-27).** Implement the review's missing decade-level
`Live/Stop` skew square, then use checked phase layers instead of an outer
boundary search budget. This is separate from checking which literal branches
terminate and from selecting a term by its literal transition weight.

**Changes.**

- Proved the continuation phase helix and terminal delta-zero invariant.
  Added chronological first-stop composition, dyadic refinement, and checked
  91-offset phase layers. Squares use the transported right phase
  `(r + 2^k) mod 924`.
- Factored Entry endpoints by their short cyclotomic phase. Retained the full
  occurrence cache alongside this local arithmetic cache; removing it made
  phase normalization repeat. Canonical Near seam events now reuse the existing
  `comma_near_event` owner at delta zero, with occurrence transport afterward.
- Added one postorder layer builder with closed theorem publication, bounded
  retention, admission before work, request-local rollback, and separate
  base/square/failed-work accounting. Squares exclude the scalar run, recursive
  power specification and control evaluator from their rewrite context.
- Retained checked child-length equations and weak congruences so immutable
  child lists are not repeatedly normalized as arguments. Sequential selected
  list indexing remains; this change does not prove an optimal lookup bound.
- Added a fuel-free boundary interface that actually consumes a guarded layer
  lookup. Its refinement and completeness theorems explicitly require checked
  all-phase layers; they do not call the recursive power specification during
  execution or imply that the concrete instance has passed.
- Kept the positive B5 all-state assertion active. The instance generates bases
  from HOL definitions, squares layers, checks first-stop height at most 26,
  and joins exactly `[0,924)`. It imports no Python rank rows or success flags.

**Independent review and corrections.** The auditor caught an initial boundary
consumer that still called the recursive specification; it now uses lookup.
An explicit full-interval assertion supplements the final theorem's coverage
requirement. The review found no new cross-owner memo collision. D4 exposed a
missing unit-exponent rewrite, correctly rejected as incomplete publication;
`power_one_right` and its successor-zero form were added (`power_one` alone proves the different identity `1^n=1`). Diagnostics now identify the
unresolved cell without printing its entire retained layer. Small regressions
check wraparound, repeated-request reuse, invalid phases, live-layer rejection
and capacity failure before additional arithmetic.

**Evidence scope.** Raw logs stay ignored at
`results/current/comma-powered-decades-2026-09-27/`; these are machine-local
paths, not portable downloads. The intermediate `boundary-4` build passed
(21.28 s / 887,393,352 sampled bytes). The focused comma/API/proof-index/docs
selection passed 333 tests, with four deselected, in 46.03 s / 89,555,568 bytes;
this ran while the later proof-only cache optimization was being edited and
is not frozen-source release evidence. Source entry/prefix uniqueness already
have separate checked proofs; they are not being relabeled as new results here.

**Release scope.** Complete base coverage is still necessary even when higher
layers use squaring. Finite constructor termination does not establish the
14,470-losing/314-winning future partition, the
314-fork/+924 return, or exact weighted selection. No production forest path,
certificate admission or runtime fuel was removed by these generic lemmas.

**Checked local construction.** On source
`1321d814ebcf76dcf6177f908f2c4609eda494416f6c171212006bd04f12849b`,
`layer-check-power` passes (17.01 s / 927,959,680 bytes), and
`layer-smoke-power` passes (46.71 s / 929,008,328 bytes). These are focused
builds with saved parent heaps, not aggregate acceptance. D4 is checked in
addition to D2 and wrapped-phase D2. The main smoke engine checks 455 base
states, four squares and nine retained layers; a separate capacity-one engine
charges another 91 base states before refusing and rolling back publication.
Main-engine construction is 25,805 ms: 22,719 ms in bases and 3,085 ms in
squares. Its canonical seam cache records 3,320 hits and 446 misses. These are
single-run diagnostics, not paired benchmark acceptance or all-state coverage.

The alphabet-only build `alphabet-event-1` passed earlier in 41.89 s /
837,127,648 bytes. Its unchanged theory sources are retained in the final
layer dependency graph; the later unit-exponent repair affects only the layer
checker. Intermediate failures and the smoke run that completed its theory
but timed out while finishing the session remain recorded as failures.

**Final full gate.** Source
`9b45f62fd0a4952e41d8d3e697d5775f03a2311e9bba35af405193e9759ad2ec`
replaces the restricted evaluator's numeral-power rewrite with the standard
recursive even/odd power equations, avoiding an unresolved internal `Num.pow`
term at D8. `layer-check-numeral` passes (15.30 s / 923,602,064 bytes).
`layer-full-numeral` **times out** at 60.089 s / 929,401,472 bytes. Its last
progress reports 14 completed base phases (1,274/84,084 states) and ten
completed squares. No complete B5 phase or all-state theorem was published.
Unreported interrupted work is not zero. Earlier `layer-full-final` failed
on numeric normalization and is not a timeout or successful proof.

The next acceptance dependency is successful complete base/layer construction
within the existing bound, followed by an authenticated concrete layer owner,
the complete future graph and weighted return refinement. The new conditional
boundary theorem stays proof-internal. Runtime forest admission remains intact;
there is no source-global safety claim or production performance claim.

**Frozen validation.** On the final `9b45f62fd0a49` source,
`boundary-final` passes in 22.82 s / 925,174,472 bytes, checking the conditional
fuel-free lookup refinement. `quality-final` passes in 24.24 s /
640,124,320 bytes: strict mypy (1,531 files), Ruff, formatting, repository
policy, proof inventory (66 sessions / 188 theories), documentation and 53
repository tests. No skipped proof, new axiom or theorem oracle was introduced.
The full B5 timeout is unchanged; focused parent builds do not replace it.

`focused-final` passes 280 comma/API units (four validation cases explicitly
excluded by the existing unit marker) in 33.83 s / 85,361,240 bytes. The separate
`cli-release-final` selection passes all four positive existing prefix assertions
in 6.23 s / 48,759,384 bytes, including the first selected fork child. Both JUnit
files validate against their independently collected selections and the final
source fingerprint. These tests exercise the retained forest-backed production
route; they do not certify its deletion. A first evidence-validation attempt
used an unfiltered required manifest against the unit-only result and correctly
rejected it; validating the two recorded scopes separately succeeds. No whole
unit, installed-wheel or aggregate release completion is claimed.


## Comma packed temporal control

**Objective (September 27).** Apply the reviewed offset-fiber and packed-phase
quotient before temporal squaring, preserving exact control and the separate
weighted production-admission obligation.

**Changes.** `temporal_masks.py` builds a postorder sector DAG from canonical
chart arithmetic, branching only on the short cyclotomic periods. Its complete
924-bit words are composed by positive phase pullback and exact first-stop
labels. The displacement-period catalog now has one shared arithmetic owner.
No forest file, runtime fuel guard or positive release assertion was removed.

**Established finite results.** The symbolic constructor agrees with all
42,504 representative scalar rounds. It uses 430 base sector clauses and 450
including the boundary starts, 3,571 short-phase branches and 18,044 canonical
chart moves. B32 has no live outputs, 204 distinct terminal summaries and
maximum crossing height 26. The losing iteration gives 14,470 states and
maximum candidate rank 136; all 314 remaining states lie on the source cycle
with exponent gain 924. These are finite executable results, not proof premises.

**Audit corrections.** Rotation is defined by `R_n(M)[r]=M[(r+n) mod 924]`;
child-mask pullback therefore uses positive gain. Signed subtraction must
precede the offset reduction. The 46-state quotient is control-only: offsets
`0,1,12,33,64` share a fiber but have chart-position counts `52,51,50,49,48`.
Weights and source authority cannot be merged on that key. Boundary admission
now explicitly rejects incomplete stop words; local periods must divide 924.
The surviving source cycle is checked against the entire computed complement.

**Development validation.** `symbolic-1` compared every representative round:
0.076 seconds for base symbolic construction versus 3.214 seconds for its
scalar reference in that run. `symbolic-2`, without the reference, completed the
whole finite candidate in 0.588 seconds / 23,003,640 sampled peak bytes under
35 seconds / 1 GiB. This is research-compiler evidence, not a CLI timing or a
universal complexity bound. The report separates chart work, mask intersections
and retained clause counts; it does not claim complete operand-bit accounting.

The orbit theorem build `orbit-10` passed in 28.888 seconds / 923,601,584 bytes
under 60 seconds / 4 GiB, including its checked local endpoint instance and
oracle audit. Earlier builds failed on proof syntax, rewrite order or tactic
cost and do not count as passing evidence. The development tests passed 14 new
finite-control regressions and all 263 existing comma units. Strict mypy passed
1,534 files; Ruff and touched-file formatting passed. These development runs
precede the final source freeze and do not certify later edits.

**Remaining obligation.** Complete kernel-checked packed-mask coverage,
losing/winning classification, repeating literal branch safety and the exact
weighted scheduler consumer. Generic composition or representative raw
evaluation cannot substitute for the concrete packed constructor. Production
still requires the forest; no CLI cutover is claimed.

Raw logs under `results/current/comma-temporal-masks-2026-09-27/` are ignored
local evidence, not portable download links.

**Earlier proof-producer refinement (September 27).** The sparse-row assembler
uses balanced joins, a shared checked period cache and one evaluated crossing
decision per branch. Complete source keys and mask coverage are checked before
publication. At this intermediate revision, insertion-based outcome packing had quadratic worst-case
cost in its row count; its input/output sizes and comparison upper bound are
reported separately. Recursive inclusive timing is labelled summed call time.

Guard construction previously spent 6,906 ms of a 7,067 ms four-guard run
rotating large masks (`masks-36`). The checked short-phase substitution reduced
that same four-guard evaluator workload to 211 ms (`masks-37`). The complete
62-guard catalog, plus the changed-shift case, then checked with 466 retained
nodes and 455 joins in 5,069 ms (`masks-39`). These are scoped development
measurements, not CLI timings. Later generic sparse-row proof failures still
made those overall sessions fail; the guard result alone is not cutover evidence.

The complete `Comma_Decade_Masks` development session first passed in
`masks-48`: 27.248 seconds / 963,742,480 sampled peak bytes under the unchanged
60-second / 4-GiB limit. It checked the row-construction and base-projection
theorems, all 62 guards, and a concrete `Entry(9,0)` row. That concrete row
used three local clauses and two joins. This is deliberately not reported as
the 46-row instance or future-safety proof. The subsequent
`Comma_Sector_Mask_Instance` is a positive first-decade construction check;
it remains subject to its own validation and cannot be replaced by a refusal test.

Independent read-only review found complete source/action keys, consistent
positive phase transport, strict closed-theorem publication and safe retention
of already checked child entries after a failed parent. It also confirmed the
remaining scope gaps: no complete base instance, B32 coverage, concrete
losing/winning classification or occurrence-weighted production admission.

**Explicit mask algebra and eager-work removal (September 27).** The subsequent
review identified whole-cache eviction and repeated row normalization. The
replacement uses one bounded arithmetic owner with explicit checked AND, OR
and positive-rotation equations. Commutative reuse restores the caller's exact
operand order. Capacity eviction removes one oldest entry, rather than clearing
the table. Zero/self identities use checked algebraic rules.

The sector constructor now discovers only reachable short clauses, publishes
them bottom-up, and consumes explicit mask equations through checked singleton
transport, equal-outcome merge and join rules. One structural list conversion
finishes each row. Rule templates normalize small sector numerals before guard
words are inserted. The retired insertion/packing implementation and its HOL
support are removed; the remaining induction uses ordinary lists. The previous
root-driven engine already shared suffix memo entries, so this change is not
reported as eliminating 46 independent executions.

Native intersection tests are construction hints only. Every retained outcome
has a kernel certificate and the final union must cover the complete phase
word. Separate adversarial tests omit all necessary intersections or just one
unique nonempty component: publication must fail, then an exact retry must
succeed. Both passed in development `instance-14`, as did source-bound terminal
row publication. The explicit arithmetic API, FIFO, swapped AND/OR operands
and positive rotation passed in `instance-15`; that overall session still
failed in a new sparse-composition proof. These component results do not
certify the failed session or a production cutover.

The same runs exposed cold arithmetic cost: three fresh 924-bit intersections
cost about 1.3–1.7 seconds. Root-level cache hits do not establish that this cold
work has disappeared. A constructor-directed per-bit proof cache was tested
and **removed**: it displaced whole-operation proofs and regressed the terminal
row from roughly 0.4–0.55 seconds to 2.52 seconds. Its cold 924-bit intersection
still took 517 ms. `instance-19` reached 51 completed sector rows from 327
discovered sources before its 40-second diagnostic deadline, with 14,500 cache
evictions. These measurements reject that implementation, not the quotient.

The generic sparse-composition theory now checks exact first-stop offsets,
positive phase transport, coverage and binary-power refinement. Its base-row
assumptions are explicit. Full base coverage, B32 totality, finite future
classification and weighted literal lifting remain required before fuel or
forest removal. The independent audit found no reachable source-key collision;
its findings about the rejected per-bit cache do not apply to the retained
root-only cache.

**Checked shortcuts and final scope.** The retained proof API seeds bounded-word
facts from checked phase guards. Full-mask identities use those facts; an
overwide input falls back to exact arithmetic. Bound facts share the existing
FIFO capacity. Duplicate publication cannot add stale queue tokens, and direct
canonical cache hits retain exact-term validation without repeating the oracle
audit. New swaps and derived identities still receive that audit.

The producer's second full arithmetic kernel was also removed. Crossing checks
now use only natural arithmetic and constructor cases, because the crossing
predicate ignores headroom and target offset. A lazy smoke probe proves the
original crossing expression with opaque endpoint fields; ordinary construction
does not run this regression probe. Independent review found no weakened source
binding, mask coverage or shortcut premise. One reviewer incorrectly disputed
the overwide regression; the claim was retracted: `2^924 AND (2^924-1)=0`.

Final code fingerprint:
`19e84dc4f72f28ee18cdf6205a2f43ebde3a15858b72a0f3518452b42b6983b7`.
`final-masks` passes the complete `Comma_Decade_Masks` session, including sparse
composition and the new regressions, in 33.653 seconds / 1,027,034,352 sampled
peak bytes. `final-instance` remains **FAIL**: its 40-second diagnostic timeout
leaves the positive complete-row assertion unproved. It finishes 64 of 327
discovered sector rows, with 623 intersections, 818 packed misses, 687 hits and
zero evictions. Packed arithmetic uses 21.526 seconds and local clause proofs
10.510 seconds; these are scoped counters, not additive whole-run timings.
The guarded process ends in 52.860 seconds / 935,512,800 bytes. Both reports
verify unchanged source fingerprints and filesystem revisions.

The new review's custom-converter deletion is therefore applied and checked,
but its prediction that this alone makes the first complete row green is not
supported. No general removal of quadratic proof work is claimed. Fixed-limb
arithmetic is a remaining measured-construction question: decomposition and
reassembly would need their own checked costs. All 46 base words, concrete B32
all-stop coverage, the 16-schema losing fixed point and weighted 314/+924 return
remain open. Production fuel and forest admission remain unchanged.

On that same frozen source, `frozen-focused` passes all 278 comma/research
tests in 27.194 seconds / 86,753,880 sampled bytes. `final-quality` passes strict
mypy, Ruff and formatting on 1,534 Python files, repository policy,
documentation checks, the 69-session/201-theory inventory and diff checks in
14.523 seconds / 644,679,096 bytes. These are focused results; the full-unit,
installed-wheel, aggregate proof and cross-family performance gates were not
rerun for this proof-generator cleanup.



## Comma Entry diagonal and Frobenius audit

Date: 2026-09-27. Objective: replace duplicated Entry proof work with the
proposed spatial/Frobenius coordinates, without mistaking local control
sharing for global branch safety.

- `Comma_Frobenius_Entry` proves signed headroom normalization and connects it
  to `comma_entry_alphabet_endpoint` and `comma_fast_sector_target`. The checked
  key is `(sector,digit,diagonal)`; digit-orbit elimination is still separate.
- An experimental additional diagonal cache rewrote occurrences to this key
  and transported their equations back to the original source. It recorded
  680 hits but timed out during discovery (149 sectors; no published rows).
  It duplicated the existing Near cache's equivalent headroom sharing and
  added expensive source proofs, so it was removed. The original cache remains
  the owner. Tests distinguish equal local effects, changed phase, and exact
  negative multiples. No Python result or candidate flag is a premise.
- Production `phase_prefix_displacement` reuses the existing closed cycle sum.
  Only an incomplete phase tail is enumerated. The bounded-work regression now
  requires one visit instead of three for a two-phase complete cycle plus tail;
  its exact large-integer result is unchanged.
- The research compiler checks the anchored CRT clock `(mod4,mod3,mod7,mod11)`,
  orbit potential, signed deck, centered innovation and occurrence correction.
  All 450 local controls are covered by a finite differential test. This does
  not establish complete temporal or weighted closure.
- Independent review found no authority leak in the experimental diagonal cache;
  the coordinator's performance gate subsequently rejected that extra layer.
  It confirmed that the receiving clock cannot be erased: residues 1 and 23
  share control `(1,0,22)` and next entry `(2,49)`, but recenter to 0 and 24.
  The initial review's 9/15 numbers were wrong and were corrected by the test.
  A second regression preserves canonical/actual headrooms 300/299 at x=1.
- Rejected optimization: reconstructing production Entry headroom through the
  extra diagonal arithmetic measured about 11% slower. The original direct
  formula remains; coordinate experiments did not become another runtime path.

The raw build attempts and measurements are ignored local evidence under
`results/current/comma-frobenius-entry-2026-09-27/`. Failed proof attempts include
an invalid method, an expanding simplifier rule and a missing signed exact-modulus
normalization rule; none is passing evidence. The final verification and the
remaining construction gate are recorded below.

Frozen source fingerprint:
`1e4bf6ffe8dc07bd9a9df242ad2f1d69ea62d378e453fbfc49b06094a36ad8a7`.
These results apply to this fingerprint only, not to subsequent edits.

| Check | Result | Time / sampled peak | Scope |
| --- | --- | --- | --- |
| `Comma_Decade_Masks` with retained Entry theorem and smoke regressions | PASS | 60.082 s / 983,124,800 bytes | Kernel-checked local refinement; configured 60 s guard completed with a small sampling overshoot |
| `Comma_Sector_Mask_Instance` | FAIL: internal timeout | 56.117 s / 930,777,704 bytes | 65 published rows, 327 discoveries; internal request took 40.621 s; complete classification not checked |
| Focused comma arithmetic, images, weighted selection and Frobenius tests | 234 PASS | 7.511 s / 83,296,856 bytes | Bounded correctness and authority regressions |
| Public comma CLI and certificate cache/reporting | 36 PASS | 28.934 s / 51,069,504 bytes | Existing admission, output and lazy-reporting contracts preserved |
| Strict mypy, Ruff, formatting, policy, docs and proof index | PASS | 20.683 s / 649,217,416 bytes | 1,544 Python files; 202 theories indexed, not all rebuilt |
| Isolated phase-prefix benchmark | PASS | 0.442 s / 14,991,864 bytes | Five alternating paired trials, 10,000 calls each; not a CLI or temporal-construction bound |

The closed phase sum took 0.426, 0.561 and 0.501 times the preceding local
implementation's median time on the three measured cases. This removes one
redundant bounded sum; it does not establish subquadratic cross-sector execution.
The retained proof evaluator publishes 65 rows, versus zero for the rejected
extra-cache experiment. Neither run establishes complete classification.

**Remaining cutover obligation:** prove orbit-potential elimination together
with receiving-clock transport, the complete weighted transition, successful
bounded-constructor totality and the checked repeating winning branch. The
450-control experiment alone cannot replace any of these results. The runtime
4096 bound, forest admission and finite-prefix behavior remain unchanged.
Aggregate Isabelle, the full unit suite and the full release performance matrix
were not rerun for this scoped change; previous results do not certify it.


## Comma Frobenius recurrence and proof construction

Date: 2026-09-27. Objective: implement the supplied clock recurrence and use
checked arithmetic reuse while preserving the forest cutover requirements.

- The focused `Comma_Frobenius_Recurrence` session imports only
  `Comma_Arithmetic`. It proves divisibility by ten, the wrapped successor law,
  arbitrary iteration, factor composition/squaring and the fixed-period seed.
  No generated transition rows, Python flags or extra axioms are premises.
- `Comma_Entry_Arithmetic.build` evaluates 17 exponent-five seeds and derives
  the other 99 power equations from each preceding checked equation. The
  successor's restricted simplifier has no modular-exponentiation evaluator.
  All 116 exact exponent bindings and the existing oracle audit remain.
- The Python arithmetic owner avoids modular powering on the six period-one
  channels. It still charges the constant seed's integer arithmetic. No new
  runtime cache, table, scheduler or branch selector was added.
- A macro-local transported-clock dictionary reduced power calls but regressed
  measured execution and increased charged work. It was removed, including its
  callback and helper API, before final validation.
- New tests check all 17 by 924 raw transitions, wrap, shared affine block
  composition, reduced-orbit reflection, diagonal transport, receiving clocks,
  symbolic weights and charged fixed clocks with `pow` forbidden. Reduced
  affine/reflection results remain finite tests, not claimed Isabelle results.
- Proof development exposed a self-normalizing decomposition and eager
  expansion of `10^(r+923)` into a huge closed factor. Explicit equality
  transport and narrowly instantiated power laws replaced those simplifier
  paths. Failed and timed-out drafts are not proof evidence; temporary file
  diagnostics were removed before final validation.
- Independent review confirmed the remaining classification/safety gap. Its
  initial description of the new source as already proved preceded a kernel
  build and was not accepted as verification. Its timing observations concern
  earlier fingerprints, not this run. Final results below are the authority.

The public `CommaTerm._resolve` still runs guarded sector cycles and certified
fork selection. The private boundary-template constructor consumes the
optimized power arithmetic, but the automatic public resolver does not yet use
that constructor. These changes therefore claim neither CLI cutover nor a
public-query speedup. Full successor/rank coverage, weighted lifting and the
concrete repeating winning branch remain necessary before forest/fuel deletion.

Raw attempts are ignored local evidence under
`results/current/comma-frobenius-recurrence-2026-09-27/`; final validation follows.

Frozen source fingerprint:
`575aef31e6007c0b8f5e9c9516cc6433004a1be3440bf65691e35cf0ae5de736`.

| Check | Outcome | Time / sampled peak | Scope |
| --- | --- | --- | --- |
| `Comma_Frobenius_Recurrence` and `Comma_Fast_Arithmetic` | PASS | 28.343 s / 961,023,888 bytes | New recurrence and compiled arithmetic consumer, with oracle audits; Entry construction checked in its parent session |
| Focused comma arithmetic, macro, scheduler and recurrence tests | 273 PASS | 6.663 s / 88,654,424 bytes | Exact outputs, local recurrence and bounded differential evidence |
| Public CLI and certificate cache/reporting tests | 36 PASS | 28.373 s / 53,969,472 bytes | Existing public contracts; forest admission remains required |
| Strict mypy, Ruff, formatting, policy, docs and proof index | PASS | 17.652 s / 648,480,160 bytes | 1,545 Python files; 203 theories indexed, not all rebuilt |
| Isolated residue benchmark | PASS | 0.592 s / 16,515,576 bytes | Five alternating paired samples, 157,080 queries each; exact result agreement |

The residue benchmark's paired median new/old ratio was 0.939. This is a local
arithmetic measurement, not an end-to-end CLI or temporal-complexity claim.
The focused recurrence theory itself took about four seconds of prover CPU in
the final build after replacing eager simplifier expansions. Full mask/rank
instances, aggregate Isabelle, full units, installed-wheel validation and the
release growth matrix were not rerun; no earlier fingerprint is substituted
for those missing checks. No positive release assertion was skipped or weakened.

**Disposition:** local recurrence and arithmetic optimizations checked; full
forest/fuel cutover unfinished. The complete successor/weighted-lifting and
repeating-branch instances remain required. The new local theorem supplies no
authority to remove runtime admission or the finite constructor limit.

## Residual blocks and lazy proof contexts

Date: 2026-09-27. Supplied residual-review SHA-256:
`caca8558c4ab4cd71e0bfa5f738c2f86bc9e029731d8fa658527b63ce10a0bc7`.
Its 204-class, 1,228-node and 3,279-class measurements are supplied research
claims; no checked classifier or ordered boundary-graph artifact was found.

- **Checked local mathematics:** `Comma_Decade_Blocks` reuses the existing
  exact `(height, terminal)` summary. It now proves the closed residual
  step, block composition, squaring and B32 bound, as well as stop/live
  refinement to the actual decade source run. A checked strict rank implies
  an exact residual; rank at most 26 then implies B32 stopping. The checked
  rank remains an explicit premise, not imported enumeration evidence.
- **Removed repeated proof setup:** each fast-kernel boundary now creates its
  immutable simplifier context once on first demand, instead of rebuilding it
  on every cache miss. Dependency procedures, exact theorem-key checks and
  kernel/oracle audits are preserved. Counters distinguish context creation
  from concrete theorem evaluation.
- **Dependency correction:** concrete residual-consumer corollaries were
  initially added to the full candidate-check session. They were removed
  again so checking source ranks does not load downstream consumer proofs.
  The generic checked-rank bridge can be instantiated after source checking.
- **Build scope:** dependency rebuild attempts hit the unchanged 60-second
  limit. Incremental continuation checked the new Blocks theory in 22.53 s
  (1.95 GB sampled peak); the fast-kernel and first-phase smoke sessions also
  checked. A first-phase smoke run created each demanded boundary context
  once, while certifying 91 concrete decade evaluations.
- **Still red:** the source-identical full rank retry took 60.14 s and timed
  out at phase 12, after completing 12 of 924 phase ranges (1,092 of 84,084
  occurrences). No theorem for full source coverage was published. The
  compact classifier, its successor equation, ordered future congruence and
  weighted repeating winning path remain required before forest/fuel removal.

Evidence is local under `results/current/temporal-residual-cutover-2026-09-27/`:
`blocks-*`, `proofs-final.*`, `totality-*` and `totality-progress.txt`.
Earlier failing and timed-out runs remain visible. Focused checked residual
algebra does not certify the unfinished full rank or the production cutover.
The forest and finite admission guard therefore remain in production.

### Classifier-first correction

The subsequent supplied review (`8a7f258f-e815-4a44-9fd7-382decb7625b`)
correctly challenges using the expensive rank instance to establish residual
existence. The shared one-step predicate already checked successor admission,
height decrement, terminal label and zero terminal delta. Its induction is now
`comma_decade_summary_recurrence_sound`, independent of rectangle enumeration.
The old enumerated-check theorem is a compatibility corollary of that proof.

`comma_decade_residual_classifier_ok` reuses this predicate, and
`comma_residual_classifier_sound` connects an arbitrary checked classifier to
the exact source summary. `comma_residual_classifier_B32` needs classifier
correctness and its height bound, **no checked rank premise**.
`comma_residual_classifier_rank` derives rank validity in the other direction.
These definitions remain in the existing proof owners; no duplicate classifier
semantics or expensive rank instance is imported by the new theorem.

**Still missing:** a concrete compact classifier and proofs of its source-domain
recurrences. The asserted 204 domains and 3,279 ordered boundary residuals are
not supplied executable artifacts. Fewer leaf labels do not themselves bound
the cost of proving their domains. The weighted occurrence lift and repeating
winning-branch instance therefore remain unresolved. Fuel and forest admission
have not been removed.

The focused Blocks and Balanced Dyadic sessions passed in 31.91 seconds with
3,856,012,040 sampled peak bytes (`classifier-proof-3.*`). A preceding command
mistakenly used Isabelle `-D`, selecting additional sessions, and hit the 4-GiB
limit; focused commands use `-d`. A first centered-conjugacy proof script also
failed before its case tactic was corrected. Neither attempt counts as release
evidence. The final run checked the theories with their oracle audits, while
reusing checked unchanged parent heaps; it was not an aggregate build.

## Punctured-port construction and physical prefixes

**2026-09-27. Objective.** Apply the corrected 81-port quotient without confusing
diagonal dwell with physical sequence time. The supplied review is research
input, not evidence of global branch safety.

**Changes.** The shared comma arithmetic now constructs punctured digit ports
and selects an exact physical Near prefix by its weighted orbit. Scheduler
phase-prefix actions validate source phase and strict seam admission, retain
normal occurrence authority and charge selection, validation and integer work.
No phase-prefix action chooses a fork child. The payload audit recognizes the
new sealed action kind without evaluating another orbit.

**Established scope.** Independent tests cover 81 ports, 450 canonical diagonal
rows, all bounded headrooms through 540, and the 17 weighted cycle moduli. The
new Isabelle theory proves local port laws, arbitrary admitted dwell offsets,
ordered-root refinement and physical-prefix validator soundness. Its bounded
source/chart assumptions are explicit; it is not an unconditional source-global
classifier theorem. The proof index therefore does not label it a complete
Python constructor refinement.

**Rejected shortcut.** Replacing literal time by diagonal dwell is invalid.
For sector one at headroom 460, one physical step leaves 459, whereas one
diagonal translation changes the chart by ten. Runtime and proofs keep these
units separate.

**Validation and provenance.** Local evidence is stored in the ignored directory
`results/current/comma-punctured-port-2026-09-27/`. The initial test run caught
a missing payload-audit action case (451 passed, one failed); it was repaired.
The next run passed 463 tests, but concurrent theory edits invalidate its
frozen-source attribution. Proof generation `proof-3` passed at source
`f013eaec1741f79493705f7c443487d52cfe74b6ce384af1ee2c4e097b7cde81`
in 17.992 seconds / 2,936,443,416 sampled peak bytes. Later changes require
fresh evidence.

**Remaining work.** The all-state inter-sector constructor, source anchoring,
losing/winning instance and repeating branch theorem remain release gates.
Forest admission and the boundary worklist limit stay active until those
results and weighted production refinement are checked.

**Construction and proof follow-up.** Boundary macros now use the same weighted
port classifier to group strict-interior Near moves. Literal `chart_step` stays
as a bounded reference and seam owner. For `N(2,10)`, chart visits fall from 93
to 68 and all 67 retained weighted fragments are identical. Counted work rises
from 253 to 728 (operand-bit charges 23,044 to 23,541), so this is structural
replay removal, not a demonstrated construction speedup. The independent
review confirmed strict prefix guards and unchanged ordered alternatives.

The first weighted-cycle proof expansion timed out twice at 60 seconds. The
repair certifies each next trace from the prior checked trace, rather than
normalizing from the root. The repaired theory checks all 81 weighted cycles
and row coverage within nine ports, in addition to the physical validator.
Temporary progress writes were removed. A subsequent locator proof needed
restricted simplification to preserve its explicit witness. No proof oracle,
new axiom or imported cycle/rank table was introduced.

Input review SHA-256: `0d501ab1b5ca62cae9e32896a73910a8ae3e25877ac3d49c02ef961e73377fe3`.
The old modular-power tests now distinguish bounded phase inverses from
decimal powers; they still forbid absolute endpoint construction and constrain
all decimal exponents to 5–32.

**Frozen validation.** Source
`34c0aed92ea8a622ea58eb5d1a8edfa576e1fcb37cfed6ac6bd0e171c0438c7c`
was checked with unchanged inputs throughout each final run:

| Check | Result | Time / sampled peak | Scope |
| --- | --- | --- | --- |
| Focused comma and reporting tests | 480 PASS | 22.397 s / 89,064,024 bytes | Full local comma suite, including source authority and grouped-prefix poison tests |
| Strict mypy, Ruff, format, policy, docs, proof index | PASS | 12.497 s / 657,409,464 bytes | 1,548 Python files; 205 theories indexed, not aggregate-built |
| Isabelle `Comma_Vieta_Root`, `Comma_Fast_Rank_Smoke` | PASS | 9.869 s / 1,595,903,216 bytes | Final input check reuses previously kernel-checked heaps; fresh pair-port proof previously took 19.622 s |
| Clean installed-wheel validation | PASS | 26.287 s / 116,983,920 bytes | Built from a clean source copy, isolated environment and package/source inventory equality |
| Arithmetic growth probes | 135 samples | 4.573 s / 57,181,168 bytes | Five trials at 16–1024, 20,000 and 412,987,859; cold, repeated and cache-bypassed; forest admission excluded |

At index 20,000 the cold arithmetic construction median is 49.053 ms, with
6,332 charged operations, 39 explicit startup/seam transitions and 84 grouped
physical-prefix transitions. At index 412,987,859 it is 109.976 ms, with
17,654 operations, 75 explicit transitions and 197 grouped transitions. These
are measured absolute costs, not comparisons proving a speedup. Repeated
resolved endpoints perform no new construction; they do not establish a cold
construction bound. Probe and wheel commands/results are recorded locally as
`probes-final`, `arithmetic-{cold,repeat,bypass}`, and `wheel-2`. An initial
wheel wrapper lacked the build backend; the successful retry used standard
isolated build dependencies.

**Independent sign-off scope.** A reviewer other than the implementation/proof
authors checked source authority, retained physical weights, strict fork/seam
guards, hidden replay and memo identity. A separate proof pass checked the
incremental closed theorem construction and its shared certification context.
It confirmed that row coverage is not source anchoring and that ordered-root
pumping does not prove cyclic wrap or source-20 infinitude. The review approves
those local claims only, not full constructor or release completion.

**Complete unit result.** The frozen full-unit run `unit-final` completes in
273.575 seconds / 856,016,000 sampled peak bytes under the unchanged
300-second/1-GiB limit: **7,369 passed, 42 failed, 1,989 deselected**. Comparing
JUnit failure identities with the previous `temporal-residual-cutover` run
finds exactly the same 42: no additions and no removals. The command remains
failing. This is regression evidence, not release approval; explicit validation
selections and aggregate Isabelle acceptance are not replaced by this run.


## Rank-free residual ownership and executor cost

**Objective.** Apply the independent Entry/port review without confusing a
smaller number of chart visits with cheaper construction or source totality.

**Changes.** `Comma_Decade_Residual_Core` now owns exact terminal summaries,
block composition and the residual classifier law. Blocks, total-macro,
summary transport and powered-boundary theories consume that owner. Rank
checking consumes the core and owns its three rank-dependent totality
corollaries. An independent import audit found a second rank dependency in
summary transport; it was removed too. AST-based tests cover session ancestry
and theory imports, including the powered consumer.

The optional grouped macro executor remains available for comparison. The
default is restored to the cheaper exact constructor: on `N(2,10)` both produce
the same complete weighted macro, but the default charges 253 operations versus
728 for the grouped classifier. The test poisons grouped classification on the
default route and compares complete outputs and work. Public physical-prefix
construction remains separate; the macro measurement does not establish that
its grouped prefix operation is slower.

**Established scope.** The local classifier-to-totality theorem no longer
passes through rank. The concrete classifier, physical port-selection bridge,
ordered future-child classifier and repeating branch are still obligations.
No forest admission, prefix limit or proof assumption was removed on the basis
of these dependency and performance changes.

**Evidence.** Raw logs are ignored local artifacts in
`results/current/comma-residual-core-2026-09-27/`, not portable download links.

| Date | Source fingerprint | Command / evidence | Limit | Outcome / scope |
| --- | --- | --- | --- | --- |
| 2026-09-27 | `a3c6455c6c478408cfb06c10ced5a7a683918d987513d61de438bb4baa7bec8f` | `core-proof-1`: build Core, Blocks, Rank, TotalMacro, SummaryTransport | 60 s / 4 GiB | PASS, 43.781 s / 2,497,089,832 bytes; initial extraction only |
| 2026-09-27 | `23de0ecc19e85b7633bb0e80ce53b3640131db0cd5c9b0bad21b0be12e415e3f` | `core-proof-2`: build SummaryTransport, PoweredBoundary, Rank | 60 s / 4 GiB | PASS, 34.373 s / 3,432,846,976 bytes; second dependency leak removed |

These historical snapshots do not certify later edits. The independent reviewer
confirmed single ownership, unchanged mathematical assumptions and retained
oracle audits. It explicitly did not approve a concrete classifier or forest
cutover. Focused development tests passed 160 cases; frozen final evidence is
recorded separately after the Entry proof checks.


**Entry proof and new review.** The new `Comma_Entry_Port` child session reuses
the checked `Comma_Vieta_Root` heap. This avoids rebuilding its 81-port laws
on each local repair. Snapshot
`38c58aaff5b49365b3bcf71a493ab994c21a274bf397f1b3894739110978fc5a`
built successfully in 17.479 seconds / 2,437,419,112 sampled bytes
(`anchor-proof-10`, 60-second/4-GiB limit). It checks signed Entry conjugacy,
row admission, root periodicity/source transport and weighted root induction.
The crossing counter is a proof measure only; no runtime itinerary is retained.
The independent reviewer found the earlier source-anchor conclusion still
contained `comma_near_closed_germ`, so this result is not a complete physical
selector or permission to delete forest admission.

The later pair-field review has a local arithmetic error: its second adjacent
root uses a punctured successor instead of the raw predecessor. The exact
admitted witness `f=d=1, u=3` crosses gaps 11 and 1 and leaves residual 1;
substituting gap 91 predicts one crossing. A permanent literal regression now
covers this distinction. The pair-field bijection and 17 distinct weighted
cycles remain valid; their count is not evidence that 68 chart visits or
complete future branch classification have disappeared. Existing cycle tests
now also check the gcd cycle count and distinct cycle weights.


**Corrected continuation order.** The pair-field proposal is incorporated with
raw zero-root preservation. It does not reset the checked proof work:

1. Finish source phase → selected weighted interval → exact physical target.
2. Share the 17 weighted cycles while keeping position, exponent and source
   authority in occurrences; measure construction and lookup work separately.
3. Recenter exact receiving Entries and prove decade-control equality.
4. Check a concrete compact residual classifier and its height bound before
   replacing fuel with structural residual application.
5. Check ordered N/Z losing and winning continuations, including the repeating
   return, before removing forest admission.

The injective 81-port pair re-encoding alone is not a smaller behavioral
quotient. Any claim of fewer than 68 visits must come from an actual composed
consumer measurement, not the number of local cycle identifiers.

## Nine-action locator and CRT-core refinement

**Objective.** Move the orbit residue out of the shared carry action while
preserving the weighted occurrence, then connect the selected port directly to
its actual Entry target. This is not a claim that nine local actions establish
all future branch choices.

**Changes and established results.**

- Production modular powers now use nine coprime cores. The seventeen physical
  displacements retain their primary lifts and exponent-five seeds. The kernel
  uses no factor discovery, modular inverse, source table, or forest replay.
  Operand accounting includes phase reduction, core powering and lifting.
- The checked carry conjugacy separates normalized phase/carry from orbit
  residue. The weight formula still depends on that residue. The generic
  multiplicative lift and a small checked factor catalog prove the core power
  evaluator equals the existing modular-power owner.
- The corrected raw pair field encodes all 81 ports with two fields and no
  puncture bit. It retains the zero predecessor for the second-root test.
- The weighted Entry selector now has a checked exact physical endpoint. The
  imported nine-action refinement was strengthened: it returns the terminal
  headroom directly, with both weighted interval bounds proved before natural
  subtraction. The older conditional source-anchor wrapper was deleted.
- Rank-free residual ownership remains enforced by the AST dependency checks.
  No rank instance became an admission premise for the new local theorems.

**Review input.** The supplied `A367620_nine_action_weighted_locator_refinement.patch`
has SHA-256 `05d12ab3f50b665247f7bfbe59b62322ec0100fdddcf4f003d5f4649f7dd17ab`.
Its original final target still called the old Near evaluator. The integrated
version reuses `comma_entry_weighted_target` and has no such call in the result.
The uploaded file is research provenance, not build evidence.

**Proof performance repairs.** Self-referential simplifier rules expanded an
index inside its own subtraction and a modulus inside its own factorization.
These are now single substitutions. The factor catalog checks closed numeric
metadata before joining it; it does not unfold recursive gcd arithmetic under
a symbolic list predicate. The intermediate builds that timed out remain
failed evidence. No fuel, memory limit, oracle or proof assumption was relaxed.
Temporary machine-local tracing statements were removed before final validation.

**Independent review.** Reviewers confirmed the source-key premise, both
weighted bounds, physical zero-root semantics and preservation of full modulus
and weight. They approved those finite claims, not all-future safety. The nine
sector actions and nine CRT cores are different quotients; neither count means
that 68 macro chart visits have become nine.

**Assertions retained.** The two modular-power instrumentation tests now assert
core moduli and exponents 0–27 in place of full-modulus exponents 5–32. Their
forbidden representative-scale construction checks remain active. Independent
comparisons cover every admitted displacement and all 924 clock residues;
carry tests cover every sector, orbit and phase. No prefix-refusal or global
release assertion was removed.

**Release boundary.** The concrete source-to-decade residual classifier and its
height bound, the closed losing/winning instance, source/root admission, and
weighted scheduler selection along the infinite winning path remain required.
Production still enforces the certified prefix and forest-backed branch
admission. The new local key/locator equality does not supply those theorems.

**Frozen validation.** Source fingerprint:
`ba93033afe9b939fab1d2152686fb0bfa8ec74b99edd9d9d7ce392c12eb0a464`.
Raw evidence is ignored local data in
`results/current/comma-residual-core-2026-09-27/`.

| Evidence | Command / scope | Limit | Result |
| --- | --- | --- | --- |
| `proof-final` | `isabelle build -j 1 -o threads=1 -o parallel_proofs=0` for Frobenius_Recurrence, Entry_Port, residual Core, Blocks, TotalMacro, SummaryTransport, PoweredBoundary and Fast_Decade_Rank sessions | 60 s / 4 GiB | PASS, 25.085 s, 2,398,736,584 sampled bytes; focused dependency closure, not the unresolved global instance |
| `quality-final` | strict mypy, Ruff, formatting, policy, docs and AST proof index | 35 s / 1 GiB | PASS, 16.047 s, 656,475,552 bytes; 74 sessions / 210 theories inventoried |
| `tests-final` | all comma sequence tests, comma CLI tests including validation-marked assertions, Frobenius coordinate tests and proof-index tests; pytest defaults cleared | 300 s / 1 GiB | 583 PASS, 48.090 s, 90,096,216 bytes |
| `wheel-final` | clean installed-wheel inventory and isolated CLI/resource checks | 35 s / 1 GiB | PASS, 27.604 s, 115,378,240 bytes; existing unresolved-result contracts retained |
| `probe-cold`, `probe-repeat`, `probe-bypass` | existing `production_p0_probe --family a367620 --arithmetic-only --trials 5`, each mode | 35 s / 1 GiB each | PASS; 45 rows per mode, complete 16–1024 workloads plus 20,000 and first fork |

The probe excludes certificate admission and uses a warm interpreter. It is not
an installed-process cold benchmark. Compared with the earlier recorded
`34c0aed92ea8` snapshot, structural measurements are mixed:

| Index | Charged work, old → new | Port visits, old → new |
| --- | --- | --- |
| 16 | 597 → 602 | 12 → 11 |
| 1,024 | 3,096 → 3,062 | 70 → 55 |
| 20,000 | 6,332 → 6,293 | 124 → 106 |
| 412,987,859 | 17,654 → 17,602 | 249 → 220 |

The last row's cold-construction median is 105.18 ms; cache-bypassed is
104.66 ms. Five repetitions do not establish an asymptotic speedup. The number
of evaluated seam transitions remains 75 there. On the current source the
separate grouped `N(2,10)` macro charges 737 operations versus 253 for the
default exact constructor; the earlier 728 figure belongs to the preceding
seed convention. The grouped executor stays opt-in.

## Weighted tree locator and shared control proofs

**2026-09-28. Objective.** Apply the supplied weighted/control reduction to the
live comma query and proof evaluator, and recheck the fuel-deletion premise.
Source fingerprint:
`fceb4e0a103d1c038ad3b2c19aafbc3c6e676b24425f2e27772565b084d39b5f`.

**Implemented.** Nine weighted actions retain their 17 distinct occurrence
weights. A static optimal alphabetic locator replaces the skipped-port walk;
all 450 ordered rows are independently checked. Digit 9 remains selectable.
The literal HOL leaves contain the same digit and lower/upper interval data as
the Python catalog. `comma_entry_stored_tree_locator_refines_source` connects
stored-leaf selection to the existing Entry consumer, preserving both bounds.
The runtime still validates the physical displacement and terminal guard.

The nine coprime cores use exact halfcycles, parity and rotations; core 21
reuses core 7. `comma_recursive_core_residue_refines` and
`comma_recursive_core_power_residue_refines` prove equality with the original
power and physical lift. Neither theorem establishes global branch safety.
Tests now prohibit modular powering instead of demanding that the retired
bounded power call execute. Endpoint-materialization poisons remain active.

**Actual proof work removed.** Near sector requests share phase-zero arithmetic
through the existing phase-independence theorem. The returned proof is
transported back to the exact requested source; Entry phase and occurrence
delta remain in their keys. The base-layer constructor now uses the checked
46-orbit representative theorem before control evaluation. The 91-result layer,
chronological square and lookup semantics are unchanged. Five smoke phases
certify 455 positions with 230 decade misses and 225 hits; the previous record
had 455 misses. These are measured counters, not an inferred runtime bound.

**Rejected inference.** The attachment calls all-state B5 completion already
checked. Independent inspection found only the conditional theorem and an
uncompleted concrete-instance source. The full B5 attempt on this fingerprint
still timed out at 60.183 seconds / 1,724,617,192 sampled bytes. No all-state
completion or future-branch theorem was published. Nine local weighted actions
are not an all-decade control classifier; their output is a Near target.

**Proof validation.** The final focused Entry/core/layer-smoke build passed in
42.999 seconds / 3,613,004,768 sampled bytes. The actual new layer and smoke
rebuild passed in 59.842 seconds / 1,920,438,856 bytes. All runs retained the
60-second/4-GiB limit and oracle checks. A first ground simp attempt timed out;
bounded kernel-checked core evaluation repaired it. Intermediate source-changing
builds are not final evidence.

**Remaining release obligations.** Complete the concrete B5 classifier under
the unchanged limit; connect it directly to future rank/cycle evaluation and
the weighted literal bridge; check the closed losing/winning instance and
source/root admission. Production certificate admission, finite prefix refusal,
and chart bound remain in place. This change does not delete the forest or
claim a fuel-free release.

Raw logs and reports: local ignored directory
`results/current/comma-tree-locator-2026-09-28/` (not portable download links).

**Python validation and measurements.** All 518 comma tests pass in 21.955
seconds / 87,196,248 bytes; strict mypy (1,550 files), Ruff, formatting,
repository policy, documentation and proof-index checks pass in 15.634 seconds
/ 660,555,168 bytes. Clean installed-wheel checks pass in 23.068 seconds /
114,755,672 bytes. The five-trial fresh-compiler/repeat/cache-bypassed arithmetic probes
cover 16–1024 and the large prefix queries, producing 45 rows per mode with
unchanged source. These are same-process arithmetic measurements, explicitly
excluding forest certificate admission. Installed-wheel subprocess checks
provide separate connectivity evidence, not a cold-latency performance gate.

The independent ordered-row comparison gives 1,083 tree comparisons versus
1,564 linear visits across 450 rows. The attachment's 1,088 was not reproduced.
For the actual first-fork arithmetic query, `trace.log` records 58 selected
ports, 154 tree comparisons and 110 runtime port constructions, versus 220
visits for an independently counted old linear walk on those same occurrences.
The result remains `19999999918`; all 75 seam steps remain charged. The raw
counter `comma_port_visits` now counts selected leaves; the added
`comma_locator_comparisons` reports the search separately. Neither is a claim
that skipped comparisons were free. Total charged work remains substantial
(17,658 operations in the cold probe), so this does not establish cheap global
construction or a broad latency improvement.

**Independent review.** A separate explorer checked occurrence authority,
representative congruence, all retained layer positions, port construction,
charged comparisons, and the lack of per-query table generation. No safety
assumptions were removed. The source-bound inverse-phase/whole-cycle refinement
remains distinct from the checked local Entry locator. The nine-action result
cannot replace the full B5 classifier by itself.

**Final evaluator refinement.** The first representative rewrite still
recomputed its signed coordinate formulas for every phase. On final source
`afa77a39e758a5be3cdc2467507350b659c7578952494279432002e003ae2953`,
`comma_layer_offset_constants` compiles exactly 91 closed, dependency-certified
representative equalities once. Only the base evaluator consumes them; square
and completeness semantics remain unchanged. Independent review confirmed their
closed source, bounded natural RHS, and oracle audit. The rebuild passed in
48.264 seconds / 1,942,377,128 bytes. Its five-phase base work was 13.865 seconds
versus the intermediate rewrite's 24.510 seconds, with unchanged 230 misses and
225 hits. These are single scoped proof timings, not a latency guarantee.

The final full-instance attempt (`full-b5-constants`) still timed out at
60.128 seconds / 1,591,562,608 bytes. The explicit progress log records 20 base
phases, 1,820 certified base positions and 16 squares. It published no complete
B5 phase or all-state theorem. The preceding uncompiled-representative attempt
reached ten base phases in the same limit. Partial progress is not totality:
forest/fuel deletion remains red on the final source as well.

Final serialized validation on `afa77a39e758a5be3cdc2467507350b659c7578952494279432002e003ae2953`:

| Evidence | Result | Seconds | Sampled bytes |
|---|---|---:|---:|
| `quality-frozen` | strict typing, lint, formatting, policy, docs and proof index PASS | 11.600 | 660112824 |
| `tests-frozen` | 518 comma tests PASS | 21.443 | 87114328 |
| `probes-frozen` | 135 same-process arithmetic rows PASS | 4.300 | 57197552 |
| `wheel-frozen` | clean installed-wheel checks PASS | 22.608 | 115443752 |
| `proof-frozen` | focused Entry/core/layer smoke PASS, cached dependencies | 10.708 | 1464650872 |
| `full-b5-constants` | all-state completion TIMEOUT; gate remains red | 60.128 | 1591562608 |

All source-fingerprint checks remained unchanged. The focused proof cache pass
is supported by the actual rebuilds recorded above; it is not an aggregate
Isabelle release pass. Existing unrelated production obligations remain open.


## Forty-six-cell B5 and sparse base construction

**Objective (September 28).** Apply the corrected orbit-layer review without
changing the all-source B5 assertion or declaring fuel/forest admission closed.
Input patch SHA-256:
`ead1f7dde2418dbae8d71de0ce09309c221e5f09259a423d5cf361aa73262aec`.
The author explicitly reported no Isabelle build for that patch.

**Changes.** The new layer stores 46 orbit cells and recovers all 91 offsets
through checked lookup. Squaring preserves phase transport and exact stop
height. The imported conditional simplifier rule required explicit source
instantiation to avoid a rewrite stall; stopped branches also needed explicit
power equations. Closed orbit-slot equations are compiled once. Malformed
layers and out-of-range lookups reject explicitly.

The sparse fallback now has checked partial-row composition and a concrete
46-row base gate calling the existing shared constructor once. Each source row
is named, checked against its exact representative and checked for admission;
structural `list_all2` aggregation avoids reopening all row payloads. The
constructor exposes its already-certified full-mask equation for this bridge.
No diagnostic rank count or host omission decision is a proof premise.

**Measured obstruction.** The first complete 46-cell B5 attempt reached only
16 base phases and 11 squares in 60 seconds. No complete B5 phase was exported.
The sparse diagnostic discovered 430 reachable sector rows and 3,455 short
clauses, then published 57 rows before its 40-second internal diagnostic cap.
Clause proof time was 16.284 seconds and packed arithmetic time 15.561 seconds.
The outer gate remained 60 seconds / 4 GiB. The diagnostic cap preserves time
for reporting a failure; it does not make the construction assertion pass.

**Rejected optimization.** Caching every recursive numeral suffix through a
nested simplifier regressed the existing mask session beyond 60 seconds. A
direct structural converter removed that repeated simplification, but storing
all suffix equations displaced checked mask bounds from the bounded FIFO.
Those regressions are failed evidence, not accepted performance improvements.
The existing bound-reuse assertions were preserved.

Raw logs are ignored local evidence under
`results/current/comma-orbit-b5-2026-09-28/`; they are not portable download
links.

**Retained optimization and audit.** Direct kernel conversions now normalize
packed numeral children without reentering the simplifier at every suffix.
Only roots enter the existing bounded FIFO; full typed equation validation and
oracle certification remain at publication. Repeated recursive left-hand-term
and premise scans were removed because the fixed kernel rewrite/congruence
pipeline already guarantees them. Independent read-only review found no
semantic authority weakening. The reviewed scope excludes concrete B5
completion and general runtime performance.

The final mask session passed in 40.034 seconds / 3,774,321,344 sampled bytes.
A single cold 924-bit AND took 72 ms with 922 counted recursive nodes and one
retained root (earlier baseline 304 ms). These are scoped arithmetic timings,
not a complete-constructor speedup. The final sparse base run discovered 430
rows and 3,455 clauses, but published only 56 rows by its 40-second cap
(53.562 seconds including session startup). Clause work took 16.995 seconds;
packed arithmetic took 13.908 seconds. The earlier 60-row diagnostic and this
56-row result do not establish a throughput improvement.

**Remaining execution order.** Finish shared base-mask construction, then prove
both zero live mask and complete bounded-stop coverage for B5. Retarget the
concrete losing/winning induction and weighted consumer to that theorem.
Only after those checks may the existential-fuel owner and production forest
be deleted. No smaller speculative port quotient or diagnostic rank premise
is introduced. The unbuilt B5 evaluator draft remains ignored local work,
outside registered proof sessions.

Final serialized validation below uses source
`1aff485dd1e1b1411c9aa17c401f2c3b088fd2e4d778744f9bda02180b8982a7`.


| Evidence | Result | Seconds | Sampled bytes |
|---|---|---:|---:|
| `root-check` | mask algebra and arithmetic smokes PASS | 40.034 | 3774321344 |
| `orbit-final` | generic 46-cell layer PASS; cached checked dependencies | 10.142 | 1595821272 |
| `base-final` | concrete base FAIL: 40-second constructor timeout | 53.562 | 1766855192 |
| `full-final` | all-state B5 TIMEOUT; no complete phase | 60.174 | 1727517136 |
| `quality-final` | strict typing, lint, formatting, policy and documentation PASS | 12.129 | 659588512 |
| `tests-final` | 518 comma tests PASS | 24.041 | 86131288 |
| `wheel-final` | installed-wheel CLI PASS | 22.603 | 115509336 |

The frozen full B5 attempt reached 23 base phases and 19 squares; it exported
no complete B5 phase. All fingerprint checks were unchanged. Fuel and forest
admission remain present. These scoped checks do not certify unrelated release
gates or an aggregate Isabelle build.

## Canonical Near proofs and temporal-cylinder review

**Objective (September 29).** Apply the temporal-cylinder reviews to the actual
constructor, preserving complete source authority and the existing positive
fuel-deletion gate. The fixed-quotient report is finite experimental evidence,
not a checked classifier instance. Its SHA-256 is
`486b493168958ac909b8986971ac858ae10cf5f04f16a1b2657f6ed79f36e3a0`;
the shifted-bit/forwarding review is
`2807c54313d74a786d9f3df83f2acb88deac1253940c41c9176c95e1894b4782`.
Original inputs remain in Downloads and the supplied attachment; those paths
are local provenance, not portable evidence links.

**Changes.** Canonicalize the checked Entry endpoint before looking up the Near
step theorem. Two source expressions with equal `(f,h)` now reuse that theorem;
exact congruence restores each original left-hand side before publication.
Raw-clause counts and canonical Near counts remain separate. Both stores retain
the existing explicit bounds. Invalid phase, foreign theorem, unfinished proof,
retention refusal and recovery remain tested.

The new `comma_sector_mask_period_one_forward` theorem proves equality of the
full control-response function for a period-one noncrossing clause. Publication
rebinds the child's row and singleton certificates to that equality and reuses
its masks. No parent intersections or merges are needed. Retained theorem
counts and rebinding work remain charged. Fault-injected omission paths retain
the regular coverage check; the independent ordinary-path smoke proves the
alias makes zero mask transports.

**Proof ownership review.** The existing `comma_word_then` and
`comma_orbit_word_square` already implement phase-shifted squaring, absorbing
stops and exact stop-height addition. A proposed second Live/Stop datatype was
removed before registration because it would duplicate those laws without
constructing M1. The complete weighted germ remains a separate owner. Period-one
forwarding preserves its stated control-result type, not unrepresented literal
weights. The reports' zero-observer and homogeneous-run counts are not imported
as action congruences or proof premises.

**Validation.** The first build exposed a meta-equality/HOL-equality mismatch
in the forwarding rule application. Converting the checked branch equation to
its required HOL equality repaired it; the original failure remains recorded.
The repaired mask session passes in 33.802 seconds / 3,436,925,512 sampled bytes.
Independent reviewers checked the canonical memo's source rebinding and the
forwarding theorem's scope. No skipped proofs, axioms or theorem oracles were
introduced.

The concrete base run makes 3,455 branch requests, constructs exactly 446 Near
proofs and records 3,009 canonical hits. This reproduces the report's local
quotient inside the proof-producing evaluator. Four forwarding aliases were
published before the run stopped. The complete base remains red: 60/430 rows
in the 40-second constructor cap, 52.062 seconds including startup. Clause work
was 13.515 seconds and packed arithmetic 18.342 seconds. These measurements do
not establish an end-to-end speedup or B5 completion.

The unchanged remaining gate is concrete source classification with complete
bounded-stop coverage, followed by losing/winning and occurrence-weighted
consumer refinements. Binary elapsed coordinates alone do not discharge it.
Fuel and forest admission are retained; no runtime cutoff is silently removed.

Raw evidence is ignored local data under
`results/current/comma-temporal-cylinder-2026-09-29/`.
Source fingerprint:
`748666a2de9ebf37aa154478d30ba76d1ae608788f726336d6a9221a2907d718`.

| Evidence | Result | Seconds | Sampled bytes |
|---|---|---:|---:|
| `masks-repair` | generic mask proofs and cache/forwarding smokes PASS | 33.802 | 3436925512 |
| `base` | concrete base FAIL at diagnostic constructor cap | 52.062 | 1780190664 |
| `quality` | strict typing, lint, formatting, policy and docs PASS | 12.166 | 661030328 |
| `tests` | 518 comma tests PASS | 23.432 | 87147096 |
| `wheel` | installed-wheel CLI PASS | 24.269 | 114559064 |

All measured source fingerprints remained unchanged. The current runtime path
was preserved; installed-wheel success does not mean forest removal. Aggregate
Isabelle and unrelated production release gates are outside this validation.
