# Source-bound skew scheduler implementation

Status: **in progress; release blocked**. This work extends the existing
HashLife execution owner. It does not replace family source admission with
equality of an observer tuple.

## Research input

The input is `antihydra_goldbach_higher_recursive_power_observer_prover_release.tar.gz`,
SHA-256 `478d3adc3676540dcdab0cd411174a60ac60ff66b517399dfc6a4ed78a5118b2`.
All 222 manifest entries verify. The archive contains no Isabelle theories.
The [input audit](../results/current/skew-scheduler-unification-2026-09-13/archive-input.json)
records provenance and scope. Archive reports are research evidence, not proof
certificates or repository instructions.

The archived successor-prime constructor allocates a bitmap of the old
primorial period, enumerates its surviving positions, and scans them for every
fresh-prime phase. Its binary powering avoids rescanning the represented long
interval **after** that construction. The construction itself does not satisfy
production's descriptor-only acceptance condition.

The phase table stores length, count, first/last mark and maximum internal gap.
Those statistics compose, but do not determine arbitrary rank/select. For
example, marks `{0,2,3,7}` and `{0,1,3,7}` in a length-eight interval have equal
statistics and different ranks before position two. The archive's separate
scan tree retains the descendants needed for rank/select; the powered phase
table does not retain that tree.

## Execution and proof contract

The shared owner must compose an action with the second action transported to
the first action's admitted image. Its source, action, boundary ports, extent,
orientation, radix and precision remain part of admission. An image is usable
by a successor only under that binding. A cyclic or tropical observation may
forget information without authorizing the scheduler to forget it.

Prime generation retains the single-forbidden-residue numerical Phi owner.
Goldbach paired residues are a separate specialization. Lazy progression
counts and phase actions must account for construction, not just power-node
counts, and must preserve the descent needed for linear prefix selection.
No bounded number of phase classes is assumed from the archived experiments.

Formal obligations distinguish the implemented deterministic evaluator from
generic composition laws, mathematical count specifications and existence of
some successful evaluator run. Cache validity, admission, publication and the
actual consumer mapping require their own evidence.

The macro contraction laws, seven-deletion bound and eight-survivor implication
were separate formalization targets. `Prime_Wheel_Skew_Actions.thy` now checks
the seven-deletion bound and eight-survivor implication; recursive macro
contraction remains open. The archived prebirth tail through stage 256 and
postbirth audit through stage 1000 remain finite evidence. They establish
neither universal Goldbach multiplicity nor an arbitrary-stage performance
bound. Antihydra's source-7 non-halting certificate remains separate.

## Implemented components and adversarial findings

`hashlife/execution/source_bound_images.py` supplies the iterative execution core
owned by `TileScheduler`. It publishes scoped images, transports the second
child through the first admitted image, and keeps projection caches separate
from source/action authority. Relative action reuse requires the adapter's
complete admitted-input key and explicit transport operation. Clear/dispose
invalidate old handles and release ledger stores. This core is not yet the
execution owner for every family, and its images are not yet integrated with
the existing leased process cache.

Prime CLI rank descent now uses `PrimePartialSuccessorAdapter`: an admitted
parent-wheel interval is filtered by its source-discovered fresh prime. The
removed count is the parent Phi count on the divided interval. Subinterval
descent demands counts from that same admitted image. The CLI poison test
rejects delegation to the retired `count_leq` wrapper. The separate complete
period descriptor supports lazy fresh-prime ports and binary powering without
materializing the period; production partial queries avoid constructing that
period altogether. Ordinary parent-wheel obstructions are single residues;
this is not a complete paired-residue Goldbach constructor.

The adversarial review found and repaired uncharged prime adapter work and
in-place mutation of frozen publication fields. Complete structural integrity
checks initially caused a measured warm regression against the last frozen
wheel; the diagnostic comparison remains recorded as failed. Passing the older
pre-bridge baseline alone is insufficient acceptance.

A reporting audit also found that the API dropped the scheduler metrics already
computed by selection. The CLI now exposes separate scheduler work, peak entries
and the named source-image construction/projection/seal counters, labeled
`query_before_disposal`. Existing Phi/factor allocation fields keep their original
meaning. The new counters do not claim to include later disposal or failed-query
snapshots.

Antihydra's bounded adapter composes leaf and prefix cylinder descriptors in
the shared core. Intermediate images retain those descriptors and parent
handles rather than full coefficient grids or endpoint words. The source arena
binds both lane widths, both signs, modulus, position/time phases and the exact
source cylinder. Demanding the final fragment still walks the bounded leaves
and visits every return. A repeated request on the **same run** reuses the
retained fragment; a new CLI query constructs a new run. Neither this reuse nor
the binary image tree establishes an arbitrary-size construction bound.

Independent review found aliased frozen fields, missing delayed-demand source
validation, temporary context retention, unaccounted capacity, and a detached
cache that accepted supplied coefficients with a genuine key. The cache now
accepts a live source-image handle and computes the coefficients through the
registered driver itself before retaining an independent seal. It cannot issue
authority by accepting a coefficient tuple. Regression tests cover incorrect
coefficients both outside and during an active image computation. Source
contexts and image scopes are cleared after each fragment, including failure.
The adapter only handles safe returning runs; guarded first-failure descent and
the other demanded projection families are not supplied by this adapter.

The 196 audit found spatial two-port composition, but no implementation of the
temporal emitted-image constructor. `ReversePoweredLocalCodec` scans one spatial
source; the existing `compose_temporal` protocol has no implementation that
transports all thirteen channels through growth. The preserved P0 tests still
fail at `cutover_complete`. The recorded constructor trace has continuation
work 0, 0, 16, 58, 204, 735 at horizons 1, 2, 4, 8, 16, 32. This is an
implementation obstruction, not a counterexample to the full cylinder.

A further independent two-port audit identified the dependency precisely.
`HigherSummaryArena` contextual inputs are `SourceCellID` values, whereas a
`RecursiveOutputTemporal` is a provider/action/interface descriptor and is not
an admitted context input. The temporal provider consequently calls
`runtime.point(composed_action, original_source, coordinate)`. That observes the
composed action from the original source; it does not construct the successor
from the first emitted image. Several spatial interface slots are local activity
or placeholder values; their names alone do not supply dynamic temporal extent,
growth or first/last-active channels.

The candidate chronological law would run the second action's local emitter on
the first image, transporting its left and right context transfers over that
same image. Mirror orientation must exchange directional ports and halos, and
growth must use the prior image's dynamic active extent. The missing construction
is an authenticated image-input/context-transfer arena implementing those laws
for all thirteen channels. Existing transient bindings can grow with every
visited source-DAG node, and no finite sublinear construction or retention bound
has been established. This candidate law is a research obligation, not a newly
implemented constructor or an impossibility theorem.

The Collatz audit distinguishes the two current consumers precisely: ordinary
terms use `HashLifeBlockIndex.direct_physical_support`, while event queries
discover whole accelerated events in `CollatzSourcePublisher`. A real common
image must handle an ordinary target inside `O E^v`, initial even runs, and the
total 1–4–2 cycle while event queries stop at one. Wrapping the completed event
publisher would not establish this bridge. Those constructors and refinement
lemmas remain missing.

Fermat/Mersenne still lack the candidate-derived compact evaluator of
`product(1+C*m, m=1..L)` and its executable terminal bridge. The existing semantic
unit criterion and an enumerated product tree do not supply that evaluator.
There is also an exact research evaluator using baby-step/giant-step polynomial
multipoint evaluation, without enumerating every progression leaf. It needs
roughly square-root-window polynomial storage and sublinear window work, which
remain exponential in candidate bit length. Its measured research controls do
not meet the production compact-construction gate. It is not imported into the
CLI. The missing obligation is an accepted construction and bound, not merely
moving that research function into a production module.
Requested unresolved classifications remain UNKNOWN. No classical primality
fallback or supplied-factor shortcut has been introduced.

## Closure ledger

The new `Prime_Wheel_Bridge` session build passes in 16.249 seconds with a
sampled peak of 3,712,177,072 bytes under the unchanged 35-second/4-GiB guard.
[Build evidence](../results/current/skew-scheduler-unification-2026-09-13/prime-isabelle-25.guard.json)
and [the build log](../results/current/skew-scheduler-unification-2026-09-13/prime-isabelle-25.log)
record the checked checkpoint. The new theory proves numerical progression
counts, fresh-prime half-open interval semantics and known-factor restoration,
phase transport/closure, and the finite-set deletion implication.
Oracle-dependency assertions run inside the
session. This does not prove the Python deterministic worklist, lease lifecycle,
lazy port evaluator, or full rank/select consumer refinement.

| Obligation | Required evidence | Status |
|---|---|---|
| Shared source-image executor | Real production consumers, chronology, authentication, cleanup and accounting | Open |
| Prime successor construction | Descriptor-only count/phase construction and CLI rank/select refinement | Open |
| 196 image | Both carry ports, growth seam and continuation-free composition | Open |
| Collatz image | Common admitted support for physical and accelerated consumers | Open |
| Antihydra image | Composed projection fragments and guarded first-failure refinement | Open |
| Fermat/Mersenne terminal image | Candidate-derived compact unit/annihilator evaluator and terminal bridge | Open |
| Projection proofs | Exact support-to-consumer factor maps for demanded observations | Open |
| Performance | Frozen installed-wheel, cold/warm/bypass and complete growth evidence | Open |

Validation retains the existing workload assertions and limits: 35 seconds /
1 GiB per probe, 35 seconds / 4 GiB per Isabelle build, and 300 seconds / 1 GiB
for the full unit suite. The coordinator serializes expensive jobs. A timeout,
missing sample, unimplemented constructor or unresolved requested result is
not a passing performance gate.

## Frozen validation on September 14

The [final evidence](../results/current/skew-scheduler-unification-2026-09-13/README.md)
pins authored source `95353e85f969895d8c6cc2bc9ab08c9dc7ac48d892bd323e8b798038853d1b24`
and the separately installed wheel. The focused selection passes 346 tests.
Repository policy, authored-tree typing/Ruff and installed-wheel checks pass.
The ordinary unit suite has **5,205 passes and four failures** in 229.82 seconds;
the unchanged explicit P0 selection has **seven passes and 15 failures**. The
full-unit process stays within its 300-second/1-GiB limits. No test assertion,
workload, index or resource threshold was weakened.

All five final Isabelle session checks pass with cached dependencies. The fresh
prime theory build cited above supplies evidence of checking the added proofs;
cached success does not establish any of the absent theorems. An earlier
dependency-inclusive Temporal build timeout remains in the superseded evidence.

Prime warm nth1000 improves from 16.219 ms to 2.339 ms against the current
pre-bridge wheel. Against the fastest prior frozen wheel, however, 1.153 ms to
2.323 ms misses the allowed one-millisecond regression tolerance. Several cold
installed-prime comparisons also fail. Antihydra's installed 2,048-return
spacetime query matches the semantic lanes but takes 239.994 ms versus
182.367 ms, exceeding the allowed 10%. The cold Collatz comparison times out
at 35 seconds without a complete paired result. These are performance failures,
not acceptable replacements for constructor evidence.

The unchanged growth manifest attempted all **105 trials**: 80 completed and
25 timed out. Fixed-width temporal horizon 1,024 and growing-196 horizons
128–1,024 time out in every trial. The fully measured spatial series also fails
existing work/retention growth envelopes. The manifest therefore remains RED;
all trials being attempted does not make missing measurements complete.

An additional 35-sample Antihydra API probe passes semantic, incremental-work
and retention checks at horizons 16–1,024. Repeating a demand on the same run
constructs no additional primitive fragments and visits no leaf returns. Cold
observation nevertheless visits every return and takes a median 141.040 ms at
1,024 returns, compared with 1.576 ms for the same-run repeat. This is useful
bounded reuse, with its scope measured explicitly; it does not satisfy the
cold powered-construction acceptance condition.

Whole-tree typing is still obstructed by duplicate archived result-module names;
whole-tree Ruff reports three existing E701 errors in a September 10 measurement
script. Authored code checks passing does not make these whole-tree checks pass.

Independent review is recorded in
[the scoped audit](../results/current/skew-scheduler-unification-2026-09-13/independent-review.md).
It accepts the repaired prime CLI metrics mapping and Antihydra image-handle
cache publication, and identifies the unimplemented family and proof contracts.
It does not provide an all-family release sign-off. Shared process leases,
remaining temporal constructors, executable refinement, complete projections,
macro contraction, universal Goldbach multiplicity and the Antihydra source-7
barrier retain their separate obligations.
