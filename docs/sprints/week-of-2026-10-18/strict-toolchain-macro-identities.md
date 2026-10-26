# Strict toolchain and guarded macro identities

Period: 2026-10-18 through 2026-10-24 (Sunday–Saturday).

[Week index](README.md)

## Objective

Consolidate typed registry and guarded macro ownership, install the selected
current validation tools, and enforce strict whole-repository diagnostics without
weakening source, lifecycle, arithmetic, or performance assertions.

## Current status — 2026-10-26

This is the current development snapshot for the dirty checkout based on
`f33a96c0a34491d33361ad5b6e92781a82850a72`; it is not clean-commit release
acceptance. Current receipts and timings are recorded here once.

| Gate | Current result | Evidence and limit |
| --- | --- | --- |
| Full default Python suite | PASS | Final native and Colima full selections meet the 300-second limit; [current runtime evidence](#adversarial-identity-lifecycle-and-source-analysis-audit--2026-10-26) |
| Colima Linux full suite | PASS | Full default selection passed; temporary environment cleaned up. [Current Linux evidence](#adversarial-identity-lifecycle-and-source-analysis-audit--2026-10-26) |
| Python static quality | PASS, whole tree | Strict mypy and Pyright cover all 2,381 maintained files; all 96 serial Pyright batches have zero errors and warnings. Ruff and formatting also pass. Complete quality receipt: `20261026T174753Z-0b04e46ae325455e89d2775eb95e8330` |
| Repository source policy | PASS | Whole-tree line limits, duplicate bodies, recursion, ownership and launch policy pass; `results/nc19-adversarial-policy-final.json`. Assertions and independent oracles were retained |
| Generic guarded source-action proofs | PASS, scoped dependency acceptance | `Comma_Semantic_B1` includes the parameterized Near first-hit, ordered-child, source-port and pair-evaluation theorems. Its accepted heap was reused by the final source-graph gate; this reuse does not establish cold-build performance |
| Supporting source graph and coverage contracts | PASS, scoped kernel build | `Comma_Semantic_Graph_Instance` rebuilt: 143.4065 s guarded time, peak 2,091,589,840 bytes, cleanup confirmed; `20261026T023228Z-b2263cee7ef549f5909b6a1417772b34`. Native fixtures poison literal Near replay and test distinct H=82/H=92 bindings, warm reuse, invalid requests and non-numeral step rejection before caching. Supporting heaps were reused. This supplies no concrete replacement domain/rank certificate |
| Event-height and local-step arithmetic regressions | PASS, scoped Python selection | 45 tests passed in 0.72 s; `20261026T000342Z-499e3623281a4e048a9af1eff861dd90`. Includes 855 literal first-event comparisons, 480 comparisons for each height/completed/source channel, and the separate 62,000 local-step event and period grids. Same-control/different-valuation cases retain the exact occurrence cocycle. This is not kernel or global authority |
| Shared prime-adic arithmetic | PASS, scoped kernel build | `Shared_S_Arithmetic` completed in 50.3934 s guarded time, peak 2,483,147,152 bytes, cleanup confirmed; `20261026T001924Z-7bb56d3468204bd7b58397da311a8bbb`. Covers local-step residue signs and guarded additive periods plus signed-affine valuation thresholds; these are optional arithmetic laws, not B1 authority |
| Carry-first arithmetic regressions and proof-shape contracts | PASS, scoped Python selection | 51 passed in 1.45 s; `20261026T024441Z-66df2e31ba2d424cbe106d2dcc8e6a94`. Includes the 11,583-case reconstruction grid, 18,711 phase/width shift comparisons, all 4,860 bounded Near first-hit cases, and the H=82/H=92 false-merge regression |
| Carry-first C1 operator, saturation and Entry consumer | PASS, scoped dependency acceptance | The accepted `Comma_C1_Occurrence` dependency includes coefficient annihilation, exact 50-step carry monodromy, the adaptive modulo-32 period, 924-width saturation from width 7, and the width-5/6 exceptions. Its heap was reused by the final source-graph gate. This is not concrete B1/B32/global acceptance or evidence that every constructor erases nilpotent terms before allocation |
| Optional event-height/valuation transport | NOT ACCEPTED | The bounded Near first-hit bridge is accepted. Full source-selected event-height, terminal-integer and valuation transport remains unaccepted; inspection and completed-crossing ticks stay distinct. These observers follow source binding and are not prerequisites for B1 operator identity |
| Proof inventory | PASS, static | 139 sessions / 451 theories; `results/nc19-adversarial-proof-index.json`, 27.5676 s, cleanup confirmed |
| Concrete comma B1 instance and source-action bridge | NOT ACCEPTED | The latest concrete run exhausts its unchanged retained action/proof arena before completion. [Current B1 evidence](#comma-near-reuse-and-crt-retention-repair--2026-10-26). The passing source-side sessions do not establish the joined C1/B1 consumer |
| Symbolic rank probe | Discovery only | Its candidate ranks are not kernel authority or a Moore-minimality proof. Rank-zero includes Fork as well as Landmine, so the bound concerns reaching the first boundary action, not future behavior after that fork |
| Comma cold/bypass performance | OPEN | The 35-workload cold/bypass command reaches its 60-second limit. The 4.12-second warm repeat is not evidence of a cold-path speedup |
| Forest/fuel cutover | NOT APPLIED | The prepared patch remains unapplied and the artifact registry is empty; B32/global producer authority is unaccepted |

The fresh whole-tree quality run found one mypy error: a candidate test accessed
`SOURCE_COUNT` through the provider's non-exported import. It now imports the
constant from its public codec owner. The complete guarded quality command
then passed dependency consistency, strict mypy, all Pyright batches, Ruff,
formatting, source policy, documentation, proof inventory and installed-wheel
checks. Pyright batches used at most 25 files and a 2-GiB Node heap; the largest
sampled process-tree footprint was 629,109,864 bytes, with cleanup confirmed for
every batch. No checker rules, suppressions, exclusions or coverage were changed.
Earlier scoped receipts remain historical evidence. This run establishes
current whole-tree command-line quality; Pylance's editor diagnostics remain
separately scoped. The affected complete-source-map test also passes:
`20261026T175241Z-113c58283871468a8b6381f581b3c293`.

The nine-core/AddSub/Frobenius Entry chain is transitively visible to B1 through
`Comma_Decisive_Endpoint_Quotient`. The phase-only C1 carrier and the
characteristic-32/`z`-inverse normalization morphism are kernel-accepted. Their
physical-path statements remain guarded wrappers. The Entry count consumer
obtains its carry result from the Euclidean packet before legacy headroom
binding. Near operator IDs now exclude headroom, while transition rows and
publication bind the exact source application. The conservative physical-state
relation is unchanged; sharing the operator does not equate H=82 and H=92.
The native production catalogue contained eight Near operators/applications and
zero equivalent-operator reuse hits, so its counts establish no CLI speedup.
The isolated fixture demonstrates reuse without polluting those counters.
Beta/suffix and derived time/count residues are not replacement semantic IDs.
The generic guarded source-action proofs are kernel-checked. The concrete
`B1_Instance` selector-normalization session remains unaccepted. Local coverage
and phase/rank transport contracts remain available, but the rejected late
mask publisher was removed after profiling showed that its HOL publication
exceeded the aggregate memory bound. The source-independent future-action
owner, concrete rank certificate and downstream weighted consumers remain
unaccepted. Prime-adic sign events are a derived observer, not extra B1 IDs.
Full CRT structural normalization alone is not source-action equivalence. See
the [release gates](../../release-status.md),
[comma scope](../../research/comma.md), and the [unapplied patch note](../../../devtools/cutovers/README.md).

## Changes

The family registry now uses typed identifiers and lazy adapter contracts.
Observation packets and JSON boundaries have explicit types. Cross-module API
helpers have public names; superseded private re-exports and duplicate JSON
walkers were removed. Macro identity snapshots distinguish complete guarded
cycles, entry phases, paths, and finite bursts from display labels.

The Python development pins are declared in `pyproject.toml`; exact transitive
constraints identify CPython 3.14.9 on macOS arm64. Pyright is installed through a
private locked npm package. The quality runner checks dependency consistency and
runs serial batches of at most 25 authored files with a 2-GiB Node heap. Missing,
truncated, malformed, or incomplete diagnostic output fails the gate. Pylance is
strict with open-file background analysis; its editor results are separate.

The AST policy checks typed registry/macro boundaries and duplicate declarations.
The resource/scheduler migration replaces untyped task stacks with operation-specific
frames and separates causal state from spatial buffers. Review found and repaired
failed-insertion rollback, mutable operation tags, and missing buffer-growth
accounting. Audits still inspect actual retained payloads and backing-store identity.
Completed causal results validate their lease and authority without an unchecked
adapter cast. Helpers read the active run admission through a typed, read-only
interface; issuance and invalidation remain private to the engine. Cross-module
test helpers now have canonical public names.

The ownership audit now includes reverse/add, `2rev10`, Antihydra/Mahler and
Fermat/Mersenne. Reverse/add and `2rev10` source-bound trace builders are named
`border_occurrences`, rather than catalogues: they consume issued adjacent
children and share the existing guarded identity and exact-join contracts.
Redundant stored phase metadata was removed; Q19 ports and residue certificates
remain with their family issuers. Antihydra/Mahler supplied-action powers now
reuse the shared binary-composition owner, retaining their distinct spatial,
integer-cylinder and odd-return guards. Fermat and Mersenne clock identifiers own their arithmetic parameters and
serialized labels in typed declarations, replacing the separate display-label map.
Antihydra odd motifs now use a shared typed structural path identity, separate
from exact source and safety authority. Fermat/Mersenne joins consume the shared
clock/domain/seam contract and conditional radix-row composition; physical ticks
and trace-squaring steps remain distinct. Harmonic snapshots capture enum values
structurally, so mutation cannot hide behind the retained member object.

The temporal-bank audit extracted the common decimal five-band/F5 projection
into `arithmetic.fields.decimal_pair_partition`. Typed band identities replace
the reverse-local classifier, and reverse/add and `2rev10` frame builders share
the same projection. The generic compressed temporal-word concatenation owner
now lives in `arithmetic.automata.temporal_slp`; its reverse-local copy was deleted.
The seven-band successor partition and oriented family carry/borrow laws remain
separate. Band-only queries avoid allocating a complete projection record.

In Isabelle, the shared carry-domain owner now provides idempotence and decimal
threshold refinement to reverse consumers. The duplicate reverse proofs and
unreferenced Comma-local carry-power/reset chain were deleted. Carry orientation,
radix-specific emissions, and the distinct spatial/run Moore observations remain
with their semantic owners; local proof-fact names are not execution APIs. The duplicated first-reset scan
from reverse length and terminal output now has one owner in `Reverse_Residuals`;
terminal output projects its result while retaining the original theorem
statements and the independent query-count/palindrome arguments.

The ring consolidation removes the reverse-local channel tuple and repeated channel
projections. Typed family outputs extend the shared five-band partition; wire
names are emitted only at observation boundaries. The shared polynomial owner
now evaluates all four F5 modes in one Horner traversal, and finite ring period
search uses the existing linear word-period owner. 2rev10 width growth and skew
use `SkewMoment`; the mod-99 exponent proof consumes the shared weighted-exponent
composition theorem. Its source-specific growth schedule remains separately
admitted.

The Walsh audit found one remaining production butterfly in reverse/add. Its
signed convention is now derived from the common Boolean transform by
`W(1 - 2b) = 64 e0 - 2 W(b)`. Explicit low-64 masking preserves the old
observation boundary. The duplicate Walsh width and open-Moore state cap were
removed. Composable six-phase H5 actions, full Walsh64 transforms, physical
tripling clocks, Hensel precision, parity moments and norm-one trace clocks
remain distinct laws. Numerically equal caps for bits, nodes and physical ticks
are not treated as one resource limit. No production random-test generator was
found; seeded test distributions remain independent fixtures.

The port ownership audit found that `CrossFamilyPortAction` joined Collatz
border actions, not sequence families. Its owner is now
`collatz.source_closed_port_action.SourceClosedPortAction`, with callers
migrated and no alias. Schema-eight packet and metric spellings stay unchanged.
Generic diamond kernels and interfaces remain shared because reverse/add also
consumes them. The production HashLife tree and generic diamond test helpers
have no family imports. Collatz-only test setup is separated from those generic helpers;
the shared ordered-support layer owns joins, while family hooks own branch
interpretation and source admission.

Ring mutation review also found aliased enum snapshots, a stale positional
identity check and omitted center/mod-99/mod-198 retention. Value snapshots and
accounting now cover those fields. Public ring construction accepts authenticated
sources and demands, or two admitted adjacent children; it does not accept an
unchecked raw payload for publication. Source-owned frame windows validate once
at the batch boundary and retain child-issuance checks.

The audit did not justify interning Fermat/Mersenne issuer objects across
independent demands. Matrix/trace requests already share one query-context
construction, while adjacent matrix joins preserve exact issuer identity through
`rebase` and `then`. Fermat tripling clocks and Mersenne trace-squaring clocks
remain different laws. No global cache or alternative scheduler was introduced.

The audit interfaces now expose typed, read-only snapshots of retained stores and
source bindings. Developer statistics consume published metadata rather than
private execution fields. Forensic audits still validate the actual registered
backing store, malformed entries and nested issued authority on every requested
audit, including after disposal. Snapshot creation does not publish actions or
increment execution counters. Extracted contracts and audit helpers have one
canonical owner; callers import that owner directly.

The pending comma forest/fuel change is maintained as an authored, unapplied
[cutover patch](../../../devtools/cutovers/README.md). Its comparison tests retain
foreign, forged, stale and raced-lease checks. It does not register the candidate
artifact or replace the missing B1/B32/global kernel acceptance.

The typing tranche also repairs the runtime regressions exposed by migrated
audit interfaces. Reverse field and coordinate audits compare independently
computed actions with the actual canonical backing objects. Prime prefix
validation detects mutations in its admitted store. Causal queries authenticate
their issued action authority before selecting primitive or composite inputs;
replacing the record validator is rejected before invoking it. Ordinary Collatz
queries import lightweight physical-state helpers without loading proof engines.

Suite profiling removed repeated setup within individual inventory tests while
retaining fresh audits, mutation checks and independent output assertions.
Exhaustive research selections remain explicit validation work. The default
suite still includes production, source-authority and lifecycle regressions;
its watchdog and all positive F4/P0 assertions remain unchanged.

## Established results

The ownership migration preserves source authority and independent output checks.
Scoped typing, runtime, proof and packaging checks are recorded once below.
The [release gate table](../../release-status.md) owns the current cross-topic
release disposition; this topic does not duplicate that table.

## Rejected approaches

No diagnostics are suppressed, source roots excluded, or checks downgraded to
make the baseline green. Runtime handle authority is not replaced by annotations.
A generic constructor returning differently typed scheduler subclasses did not
provide sound static narrowing; operation-specific frames are replacing it.

Test-only historical dependency traversal helpers were removed. The current
source/ownership checker retains relative, absolute, alias and TYPE_CHECKING/else
coverage. The actual arithmetic and independent endpoint assertions remain.

The unused Antihydra `_runs`/`_run_steps` selector and its helper-only test were
removed after source-derived caller inspection. Production uses the punctured-step
selector; its independent output, source-authority and safety checks remain.

## Validation provenance

Development evidence at Git HEAD
`068827840bf80120b5bb6e8bd55cc202323466b8`, with pre-existing dirty work preserved.
Each receipt describes its tested working tree and selection, not acceptance of
this commit. Raw receipts remain in ignored `results/runs/` directories.

| Scope | Latest relevant receipt | Result and limits of claim |
| --- | --- | --- |
| Clean locked environment | `20261018T194706Z-8bc6691dce554af2826ce20f12337cb0` | Reproduced 16 locked packages; dependency consistency passed. |
| Whole-tree quality (historical) | `20261019T030413Z-04794486e19e486e9127bbfe33ad282a` | Historical October 19 receipt: strict mypy and repository checks passed, while that snapshot's Pyright backlog kept its quality gate red. It is superseded by the later zero-diagnostic checkpoint below. |
| Complete strict Pyright sweep (historical) | `20261019T030413Z-04794486e19e486e9127bbfe33ad282a` | Historical 9,950-error receipt from October 19; it is superseded by the October 22 quality checkpoint. |
| Causal authority and admission | `20261019T030355Z-29d5f582ef6b496d8cc1d14a807b1401` | 66 tests passed in 3.13 seconds, including changed-validator rejection, composite-sort enforcement, run invalidation and forged-token tests. |
| Shared carry and reverse refinement | `20261018T231229Z-6fe10baced854f8f91a914547826d9bb` | Three sessions rebuilt and passed; largest session took 278 seconds. |
| Decimal arithmetic extraction | `20261019T020716Z-3a94f3c875e94fdd9a04c83341e62b81` | Double_Reverse_Temporal_Refinement rebuilt in 90.4 seconds; unchanged shared dependency reused. No aggregate proof acceptance claimed. |
| Fresh wheel | `20261019T030413Z-04794486e19e486e9127bbfe33ad282a` | Fresh installed-wheel validation passed, including 40 family-first CLI cases, poisoned reconstruction checks and actual cross-seed and Mahler/Antihydra reuse. |
| Minimum Python wheel | `20261019T030923Z-d7c81b379bb745fb86446bd6810a9c1a` | The same wheel passed isolated Python 3.11.17 validation. |
| Complete default suite | `20261019T030950Z-e7be06380f2942d8bcb6e177bd614ca7` | 11,252 passed; one existing F4 concrete-resolution assertion failed. Pytest completed in 289.15 seconds, guarded wall time 291.70 seconds, peak footprint 850,379,928 bytes. No timeout or migration failure. |
| P0 release selection | `20261019T031450Z-dc7f1473375c49d3a5538a177de52d6f` | 61 passed, nine existing holds failed in 10.92 seconds: Antihydra source-7 non-halting, four candidate prime-bit decisions and their four CLI consumers. Reverse/add and Collatz passed. |
| Pending cutover quality | Comparison receipt `20261019T031650Z-1b0ecf53e363422b9adfe906e2d3f8cf`; baseline `20261019T031511Z-160d211458454520920f0374b2d639ca` | Ruff, formatting and strict mypy passed. Across 21 surviving affected Python files, the candidate has 113 Pyright diagnostics versus 128 on the baseline: zero added, 15 removed. Existing diagnostics remain failures. |
| Pending cutover behavior | Comparison receipt `20261019T031719Z-df1fcccafbce4aa095464aaf07e9e1fb` | 75 passed, including bounded-audit exhaustion tests; two positive public-global-authority assertions failed because the production release registry is empty. |
| Pending cutover source policy | Comparison receipt `20261019T031742Z-473dec6f82d54ec99bbb6686363e1249` | Whole-tree source policy passed, including line limits, recursion, duplicate bodies, ownership and validation entrypoints. |

The complete-suite timing record separates 13.74 seconds of collection, 7.41 of
setup, 259.04 of calls and 0.71 of teardown. Its slowest test took 3.75 seconds.
The 300-second suite and 60-second per-test limits were unchanged; cleanup was
confirmed and timing instrumentation completed normally.

Comparison checks used the candidate checkout's `src` before the editable main
installation. Synthetic admissions in mechanism tests do not establish kernel
acceptance. The two positive global-authority failures remain genuine gates;
the patch is unapplied and the live CLI retains forest admission. The developer
audit walker is bounded independently of the removed production fuel.

Earlier repaired import, fixture, typing and stale-wheel failures are superseded
by the corresponding checks above. Their raw diagnostics remain available;
repeating their old counts does not describe the remaining backlog.
Use the [central validation guide](../../development.md#reproducible-release-commands)
for current commands and limits.

## Remaining work

The October 22 baseline below supersedes the older diagnostic backlog and
default-suite failure counts. Pylance editor review remains separate from the
command-line Pyright sweep. Mathematical and consumer obligations remain in the
[release gate table](../../release-status.md).

`2rev10` still lacks a term-owned published border-occurrence cursor for a
standalone `temporal.macro` request. Its exact typed occurrences are available
through explicit matrix traces. Advancing future children merely to manufacture
a macro summary would violate demand laziness; an always-unavailable registry
entry would not close that integration gap. Reverse/add's existing
`temporal.macro` remains its finite boundary-window certificate.

## October 22 — certified carry-period integration

Development work starts at Git `f33a96c0a34491d33361ad5b6e92781a82850a72`.
The implementation checkout is dirty; no release commit is certified. An isolated
checkout at that commit supplies the baseline. Downloads are integration inputs,
not proof or performance evidence for the implementation.

The new shared Boolean sparse-row owner preserves branching and empty successors,
and requires the same nominal state-space owner for composition. Mahler constructs
only the reachable source-conditioned rows, joins those rows, and materializes the
100-row result once. Full source fibers, exterior ports and ordered prefix-safety
witnesses remain the authority. Incremental ledger events retain work performed
before an exception; scratch reservations unwind on failure. Combined matrix and
trace requests share the existing query-context publication.

Collatz can reuse an admitted carry program on a compatible translated source.
Its narrower radix-6 bridge is reissued when that source is outside the old bridge
cylinder. A poison regression forbids recomposing the carry program in this case.
This is finite admitted-action reuse, not new future-parity discovery.

`2rev10` trace windows share a single authenticated adjacent-root path. Bounded
fallback summaries skip matrix construction and intermediate point projections;
all source, border, phase and generation checks remain. Duplicate root lists were
removed, and path/window scratch is reserved through the existing ledger. Reverse
pointed paths compose their finite F5 endpoint action without multiplying dense
singleton matrices. Conditional alternatives are retained separately.

The raw-×15 clock stores period and total as symbolic power-of-two expressions.
Its tests cover valuation/transient boundaries, both total signs, and source 1 at
depth 35 without expanding its 2^31-tick period. It does not issue repetition
authority. The current Antihydra observation uses x=H−1, so the corrected source
satisfies 10H'=15H−5(H mod 2); its changing correction word cannot be discarded.
Fermat's issued ×3 action likewise needs a separate signed-cut refinement.

The benchmark harness now passes `shared_cache=False` for embedded bypass runs.
Clearing caches is no longer labelled bypass. Fresh CLI processes remain cold.
Matrix comparisons retain the full packet and its clock unit, including refusals.

### Runtime and diagnostic evidence

All paths below are relative to the indicated checkout's `results/runs/`.

| Check | Result | Evidence |
| --- | --- | --- |
| Clean baseline default units | 11,143 passed, 687 deselected; 227.63 s | Baseline `20261022T064036Z-9e81dc9d6b654aaba5c61150d5818f1c` |
| Clean baseline strict Pyright | Zero errors across 2,347 files | Baseline `20261022T063359Z-0dcf69938614459b95cba04703a7cfe4` |
| Implementation whole-tree quality checkpoint | All 95 Pyright batches, strict mypy, Ruff, formatting, docs, proof inventory and package checks pass; final comma changes receive separate delta checks | `20261022T090248Z-e2d38cc08e27491ea4c1100b80f61f9b` |
| Implementation default units, including final comma consumer | 11,199 passed, 687 deselected; 204.54 s | `20261022T093811Z-17e595fa11b841248c83509d50f8dfeb` |
| Final comma delta quality | Whole-tree strict mypy, Ruff, formatting, source policy, proof inventory and wheel pass; 13-file strict Pyright delta passes | `20261022T094425Z-77177b3ed2184b4f80dc3d6bad3216c4` |
| P0 | 61 passed, nine failures: source-7 non-halting plus Fermat/Mersenne candidate prime bits | `20261022T073648Z-4b21a9bb3cca4c6c90e064d1ec9826d3` |

The baseline wheel smoke referenced the removed `_compile` hook. It now poisons
the live `compile_completed` hook; the wheel check passes. This preserves the
forbidden-reconstruction assertion. No workload or assertion was removed to make
the full suite fit. The final guarded invocation took 206.66 s overall, sampled
peak footprint was 427,164,512 bytes, and cleanup/instrumentation completed.
The final quality run required only regenerating the weekly documentation
navigation count; its code, policy and packaging checks passed. Pylance's editor diagnostics were not independently exercised.

### Measured scope

Five-trial public-query workloads retain horizons 16, 32, 64, 128, 256, 512 and
1,024, both output bases, and valid point coordinate zero. Collatz seed 27 median
warm CLI time was 7.146→7.153 ms; Antihydra was 3.790→3.850 ms. These are unchanged
ordinary-query measurements, not evidence of a general temporal speedup.
Baseline runs are `20261022T073518Z-d30c2d7909c04c1cb20af9f9dc54a641` and
`20261022T074250Z-c063b08ccf404c379bade787372b038d`; replacement runs are
`20261022T073607Z-3b8f86bd18fe4ee5bcb615a76be91990` and
`20261022T074424Z-b3c42ccc4d4244cfb286273a3b884e88`.

For seed-196 `2rev10`, selected term 32, the available 128-tick trace's median warm
CLI time improved 285.33→237.37 ms (about 17%); the 64-tick trace improved
135.93→112.74 ms. The 128-tick summary was 13.25→12.65 ms. Baseline matrix run:
`20261022T063319Z-115dede944f449929a24d2730706769f`; replacement:
`20261022T074727Z-35e523d7f18f453b982718286d3527af`. Earlier baseline “bypass” rows
only cleared caches and are excluded from bypass comparisons.

Antihydra term 16, 32-tick matrix summary, improved 10.29→8.45 ms median warm
CLI time (about 18%); its trace improved 13.20→11.18 ms. The replacement performs
32 candidate checks, 31 sparse joins, one 100-row publication and no dense row
products. These counters describe executed construction separately from the
logical dense products avoided. Baseline evidence is
`20261022T065431Z-f0fff08c8b1b4895b4746a5effe03e9b`; final matrix evidence is
`20261022T075014Z-e66abf9ee28047878a8301f320ac0438`. Cold process measurements
include interpreter startup and are not attributed wholly to matrix construction.

Reverse seed 196, term 42, horizons 16 and 22 refused at the same uncertified
growth seam in both checkouts. Those measurements do not establish a CLI speedup.
The raw-×15 descriptor has no complete production signed-cut consumer yet.

### Remaining consumer and proof gates

The plan remains incomplete. The downloaded digit-period selector requires an
ordered carry-word producer that is absent from the current aggregate F5 owner.
The raw-×15 period still needs its full carry-total and source/correction-word
refinement before it can replace corrected Antihydra or Fermat work. Collatz's
fixed-word lemmas do not yet establish the production mixed-word/CRT selector
binding and radix-6 summary refinement. Query-local matrix reuse does not establish
a process-wide completed-transfer cache. Shared_Carry_Dynamics passes in run
`20261022T081855Z-44b80700bbaa4e7c841840dae30f4d42`, including ordered words,
sparse rows and the raw-×15 multiplicative period. The finite double-reverse
lineage consumer passes in `20261022T082734Z-4bb861534f3f445a920a0aac0d1ec316`
(63 s session). These accepted statements do not establish the missing
source-selection, carry-total or signed-cut refinements. The quality checkpoint
used CPython 3.14.9 and its freshly reproduced exact dependency constraints.
The earlier checkpoint’s sole source-policy failure was the rejected B1 memo experiment; after that
experiment was removed, policy passed in
`20261022T091711Z-26257d2ebd24457890ce047cfeed8e27`.

## October 22 — comma carry-clock consumer

The joined download was ported into the existing boundary occurrence owner.
Macro templates now retain and seal their exact chart segments and terminal
chart. Occurrence execution validates those segments against the receiving
source instead of rediscovering each fragment's decimal sector and C1 source.
The ledger owns the added graph, including nested chart/weight references;
partial publication rolls back reservations. Equal-valued substituted objects
and malformed segment seals are rejected.

For an issued Entry→Near segment, the consumer now uses
`K = scale//100 - ceil(headroom/100)` directly. It checks the source, physical
weight, displacement, headroom, target suffix and exact high-prefix difference.
It does not replay or repower that Entry segment. Near→Near segments still use
the shared powered C1 return; sector crossings remain exact literal seams.
Tests compare the closed counts with the independent powered oracle and poison
Entry repowering. The symbolic clock also supports very large exponents without
materializing their decimal powers. An unused unbudgeted materializer was removed.

The checked `Comma_C1_Occurrence` session now includes the cumulative wire law,
the exact Entry count, and the closed higher-wire formulas, including zero at
the leading input wire. Run
`20261022T093527Z-e205a3998fb5479ba1294142c7f84906` completed the session in 34 s
with four threads (39 s total invocation). The Entry refinement theory took
4.811 s. The proofs use explicit quotient bounds and source-admitted endpoint
facts, with no added axiom, skipped proof or assumed endpoint equality.
The downstream producer record consumes these formulas, but its enclosing
future session remains unaccepted behind B1.

The Near refinement now includes terminal and sector-seam composition, not
only a strict interior prefix. Run
`20261022T153549Z-ff031e65a7cb4a5b8b84739993775f98` kernel-checked the expanded
`Comma_C1_Occurrence` session in 75.419 s (79 s in the console summary).
The proof derives the endpoint, literal path, admitted physical occurrence
and higher-wire totals from the existing Near prefix. It then composes that
physical prefix with the checked round-close suffix, preserving terminal
labels, crossing labels and the sum of their weights. It does not identify
the physical C1 clock with the independent 924-phase exponent clock.

The grouped Near consumer now requires the composed certificate beside its
924-phase weighted-prefix certificate. That downstream consumer has not yet
been kernel checked because its session depends on concrete B1 acceptance.
The C1 theorem alone still does not authenticate a published CRT column ID.

The focused final consumer/lifecycle selection passed 84 tests in 6.20 s:
`20261022T093628Z-5e30941acab441748983e70fb706a4bb`. Full-suite and final quality
results are recorded in the table above.

### Concrete B1 and cutover boundary

The concrete producer now certifies output-free route geometry and exact result
bindings separately. Its action-cover contract implies the unchanged local-fiber
contract through a kernel-checked theorem. The old per-child fiber contract is a
derived view, rather than the concrete producer's proof input. The geometry key
contains authenticated columns, scope, shifts and ordered routes; it excludes
source indices and output labels. A missing route still requires a checked empty
fiber, and a selected route requires its exact result binding. The 278 unlabelled
partition templates do not establish 278 distinct labelled actions.

The implementation removes recursive whole-row simplification from route proof
assembly, reuses exact list-selection equations, and specializes literal-list
rules before traversing their rows. Child admission and width facts already
implied by geometry and binding are derived generically instead of checked again
for every Goto. The outer template bound, rebase, beta and column equations are now transported
from the exact descriptor resolver instead of checked again for each source.
Supported columns and the complete source/ref/action witness remain explicit.
Exact final theorem, CID, source, clock and label checks remain.
The physical C1 clock remains distinct from the 924-phase selector.

| Gate | Fresh development evidence | Result |
| --- | --- | --- |
| Generic route/action-to-fiber and future contracts | `20261023T101034Z-a435670162a34d69b9994c3ead3b6aa4` | Rebuilt `Comma_Semantic_B1` in 52 s and `Comma_Semantic_Future` in 34 s; generic resolver exposure and concrete metadata/publication bridge passed kernel checking |
| Concrete B1 | `20261023T101034Z-a435670162a34d69b9994c3ead3b6aa4` | Failed the 300-second session limit; process-tree peak 2,636,759,656 bytes, descendant cleanup confirmed |
| Focused action, authority and future repository contracts | `20261023T102101Z-fe07ff52429447a48a50f8fcfadb6af7` | 115 tests passed; no skips or weakened positive assertions |
| Changed repository tests | `results/comma-action-audited-mypy.json`, `results/comma-action-audited-pyright.json` | Six files pass strict mypy, Pyright, Ruff and formatting; scoped checks, not fresh whole-tree acceptance |

The final generic build with the oracle checks registered passed in
`20261023T102231Z-673fddfe8ed14a939546f364bf2d09a2`. The source-derived proof
inventory passes (`results/comma-action-proof-index-audited.json`). Six missing
theory-local oracle audits were connected; the unrecognized publication fixture
wrapper was removed, and its unchanged release-claim checks now execute directly
in the registered publication theory. Tests inspect the parsed audited claims
instead of requiring that wrapper's implementation name. Concrete endpoint audits
remain behind the failed B1 certificate and are not claimed as executed.

The latest run completed source index 157 and was certifying index 158 at
termination. Canonical geometry used about 62 s, including about 28 s of guarded
implication checks, 14 s of assembly and 12 s of row selection. The enclosing
action-cover checks used about 245 s; these timings overlap and must not be
added. The direct equality path handled 1,337 reflexive requests without
simplifying their operands, but this did not establish an end-to-end speed gate.
The profile counter formerly called “indexed items” counts checked atomic
propositions, not indexed-loop iterations; its diagnostic has been corrected.
These are single-run proof profiles, not CLI speed evidence.

The owner-level Live/Stop fixture checks geometry reuse with distinct bindings,
and rejects wrong results and invalid clocks. It is not evidence of a checked
pair of distinct production sources; that acceptance case remains open.

B1 is still the failed release gate. B32/global and the concrete producer release
contract remain unaccepted, and the production artifact registry is empty. The
prepared `devtools/cutovers/comma-global-future.patch` passes `git apply --check`
but remains unapplied. Acceptance must use `Comma_Semantic_Future_Instance` and
its producer release contract, not the legacy native/rank
`Comma_Global_Future_Safety` session. No public comma CLI speedup or forest/fuel
retirement is claimed.

The runtime review repaired two authority defects: equal scalar FutureCIDs no
longer allow a selection from another provider to authorize a child, and an
issued macro child rejects replacement of its selection by an identical-looking
foreign selection. Store leases still reject reset generations. Issuance checks
retain Boolean-CID rejection. JSON decoding/encoding helpers now have one codec
owner, and retained-node accounting includes the provider's issuer token.

These are development results at Git
`f33a96c0a34491d33361ad5b6e92781a82850a72` with a dirty worktree, not acceptance
evidence for that commit. The full repository suite, global producer kernel
contract and CLI performance cutover were not validated by the 1,328-test slice.

## October 22 — adversarial ownership and Colima audit

Three independent explorers reviewed proof authority, duplicated family code, and
cache/lifecycle behavior. The reviewed Isabelle statements and ML stores did not
expose a false accepted lemma, proof oracle, or stale theorem-authority collision.
In particular, a theorem over the coarse offset rectangle is not unsound merely
because Python admits a narrower reachable domain. The missing concrete
serialization/producer bridge remains an explicit obligation. This source audit
is not a fresh Linux Isabelle kernel build and does not close B1/global.

The runtime audit found and repaired three concrete defects:

- A mutated reverse local-action handle could carry an unsupported transform
  into a cached composition. Resolution now validates the proved mirror subgroup
  before cache lookup; admission checks the actual port-domain sizes.
- Conditional Collatz memo lookup scratch accounts were not tied to memo close.
  Each memo now owns one reusable scratch account, independently of other memos
  sharing its ledger, and closes it even when another disposal raises.
- A direct Collatz binary source-cell request published its binding twice,
  inflating ledger reservations. Cell and forest publication now use one shared
  transactional publisher, with exact insertion rollback before releasing charges.

The common local-codec owner now provides handle validation, chronological finite
map composition, source-forest folding and binding publication. The two family
codecs consume those operations; their different arithmetic and port domains
remain separate. Existing literal-output and warm-cache poison assertions remain.
No second scheduler, catalogue, or proof issuer was introduced.

Colima validation uses a Linux aarch64 CPython 3.14.9 environment installed from
the exact declared tool pins. Lock selection now matches the runtime target and
rejects missing or ambiguous locks. The container has an init reaper and a 4-GiB
limit; the ordinary guarded runner preserves the same test deadlines. The first
container attempt exposed an evidence-directory symlink incompatibility with a
Git path test. Replacing that symlink with a directory mount fixed the environment
without changing the assertion.

The focused codec, authority, lifecycle and toolchain selection passes 131 tests
in run `20261022T102221Z-b81d83690d154ffbb8e1602a3c7ca2ad`; cleanup is confirmed.
All evidence in this tranche identifies dirty development sources based on Git
`f33a96c0a34491d33361ad5b6e92781a82850a72`; it is not clean-commit acceptance.

The Colima whole-tree Pyright sweep covered all 2,359 Python sources in 95 serial
batches with zero diagnostics (`20261022T102226Z-cac17a845c4f41439f6447b4f8a31fcc`).
That initial quality run found one new mypy variable-name collision and one
formatting change; both were repaired. Final-source run
`20261022T102816Z-4760961d386348738d75fc9ba35c5ed8` passes whole-tree strict mypy,
Ruff, formatting, source policy, documentation, proof index, installed-wheel
checks and a Pyright recheck of the changed files. No exclusions or suppressions
were added. The wheel smoke checks include source-bound parent reuse.

The final Colima default suite passes **11,212 tests**, with 687 explicit
validation cases deselected by the unchanged unit tier, in **199.50 s**
(201.60 s guarded invocation):
`20261022T102959Z-54be3a415c5c4248bb50df82119fb018`. Collection took 12.00 s;
the slowest setup/call/teardown total was 3.28 s. Sampled aggregate RSS plus swap
peaked at 404.1 MiB; timing instrumentation and descendant cleanup completed.
The whole-tree Pyright sweep peaked at 442 MiB per guarded batch and confirmed
cleanup for every batch. These measurements establish bounded validation, not
a new end-to-end CLI speedup claim.

Colima P0 run `20261022T103336Z-0d741293efeb4bcd833cbbad182ec1d9` reports
61 passed and the same nine existing failures in 10.21 s: source-7 installed
non-halting authority and four candidate prime-bit cases at both the arithmetic
and CLI layers. Reverse/add and Collatz P0 remain green. No failing P0 assertion
was removed or weakened. Isabelle was not installed in this Linux container;
the kernel results above remain the separately identified macOS runs.

## October 23 — source-selected graph and action congruence

The release source consumes the continuation graph through chronological action
powers. The split-MDD/lift compiler is gone. Ordinary CRT algebra remains where
current consumers require it.

Completed-action forwards are admitted before source-word construction. Their
contract requires an independently checked local representative, the same CID,
admitted normalized sources, and exact all-clock output transport. It retains
the receiving clock and strict sector progress. It does not equate physical
elapsed weights or an alias's immediate Goto with its representative's edge.

The accepted source-graph dependency build
`20261024T134952Z-70a9695fda6f4521a7e8ed69959abd63` took 92.063 seconds: 430
source bindings, 327 action words/nodes and 103 certified forwards. Its enclosing
concrete B1 build failed later on an extracted ML helper reference; the source-graph
session completed successfully. The native fixture
compiles Entry(4,0,7), then Entry(3,0,1) with zero additional word proofs. The
word producer rejects admitted aliases. Local representatives alone receive
pointwise row proofs; publication consumes checked lookups and rows directly.
These numbers are scoped evidence, not a proof of Moore minimality or current
B32 acceptance. Parent periods do not replace the child's receiving clock.

The B32 source now uses quotient-level backward reachability. One generic
observer-parametric transfer is certified per graph node, with exact terminal
labels, guarded local slots and same-clock Goto children. Its supported result
labels give a checked observer congruence. The current migration carries opaque,
owner-issued mask handles through the producer and consumers. Canonical keys
contain CRT axes and ordered child handles, not recursively expanded HOL terms.
Boolean Apply canonicalizes commutative operands while its checked theorem
retains the requested operand order; indexed-union keys retain slot order.
Interpretations and complete operation equations are emitted lazily and retained
under the existing shared bound. An address is never proof or source authority.

Projection reuse keys on the compiled operator and a canonical signature of its
supported mask handles. Exact observer aliases precede even pure selection;
changed observers compute their signatures before constructing binding proofs.
Congruence transport retains semantic signatures under the existing FIFO
envelope. A checked observation replaces only the current application payload
for its signature; optional old-observer aliases cannot evict primary semantic
results. New result admission discards aliases before the oldest primary.
A native one-entry regression promotes two different equivalent observers and
poisons repeated binding/selection, proving exact reuse without a larger cache.
A separate native
fixture revisits two earlier observers with selection callbacks poisoned, using
fresh stores so it cannot warm production construction. The native owner, union
and poisoned-observer fixtures pass, including zero new words/proofs on repeat
requests. Complete predecessor closure still awaits kernel acceptance;
source-level checks alone do not establish it.

The predecessor publisher constructs only checked per-root lookup equations
for the symbolic iteration. It does not publish per-layer literal tables or
exact-rank planes. Already-full roots remain full through the monotonicity
lemma; other roots consume the parametric transfer. Coverage at depth 26 is the
concrete premise for the generic exact Stop242 transport. The old scalar
candidate generator, seven-observer rank publisher and bitplane comparison
layer have been deleted, together with unused checked-rank action helpers and
the old exact-rank transport theorem. The remaining transport owner is named
`Comma_Semantic_Graph_Stop_Transport`.

The generic congruence, predecessor-soundness, symbolic mask and direct CRT
cofactor algebra session is kernel-accepted in
`20261024T134810Z-1040b63867f44b56b8bfeba5a3e75b5c` (28.297 seconds, four
threads). This includes zero-weight selector projection, terminal pointed
selection, the universal Zero/Full row-cofactor law, and bounded prefix
independence, plus the modular-translation law; none assumes source termination.
The concrete root/control and Stop transport proofs also pass.
The new mask owner interns ordered CRT decision nodes over 4 × 3 × 7 × 11;
it replaces the numerical 924-bit mask projection that exceeded the session
limit. The opaque-handle owner and poisoned-observer fixtures are accepted, but
the concrete predecessor gate remains red. The unsuccessful persistent
complete-selector application cache has been deleted. Reusable row-cofactor
actions exclude selector offset and predecessor depth from their keys and
retain exact ordered results in the existing bounded owner store. Zero/Full
row vectors admit one universal action template for every axis and slot.

Each canonical node now retains a closed prefix-independence certificate with
its existing interpretation. Earlier-axis cofactors instantiate this shared
certificate before expanding child rows; same-axis selection consumes the
selected child's certificate. Exact axis/slot premises come from at most 35
owner-local arithmetic facts, with original-context native certification.
No MDD capacity or FIFO allowance was increased. Arithmetic contexts and the
bounded nth converter are initialized once per owner; row selection reuses the
existing row cterm. First-layer root lookups compose checked equations directly.

Run `20261024T130551Z-c98b9bd832c14286bff29b5ea889ad17` passed the native mask,
row, lifecycle and poisoned-observer fixtures, including all 14 earlier-axis
slots and exact same-axis child selection. At the matched 288-projection
checkpoint, it retained the same 1,903 canonical nodes while reducing cold
cofactor proofs from 21,611 to 8,704 and evictions from 21,475 to 8,447.
Cofactor time fell from 17.6 to 7.1 seconds. The complete first layer took
239.319 seconds, versus 281.246 seconds before node certificate sharing.
That session still timed out at 300 seconds in layer two.

Rotation now converts only the bounded list/index spine, reuses the existing
word cterms and issued child equations, and instantiates the checked CRT law
directly. It no longer proves those row/union equalities with whole-word
simplification. Clock index transport similarly consumes a closed action
certificate for `(period, axis, slot)`; the receiver is universally quantified
and is specialized only at application. The existing FIFO owns these typed
certificates under its unchanged allowance. Scalar deltas are coefficients,
not mask IDs. Cache publication remains idempotent and rejects kind collisions.

The clock-repair measurement is
`20261024T135500Z-ac12e43474e84a15a7dddf9bc0cf54f1`. Its native fixtures pass
receiver changes, owner isolation, invalid-input rejection, exact row order,
and warm reuse without new certificates. At 320 projections, 192 clock
certificate builds serve 67,141 reuses; index arithmetic falls from 127.8 to
16.3 seconds with the same 2,852 nodes. The first layer completes in 114.907
seconds versus 239.064 seconds before clock-action transport. The session
still times out at 300 seconds in layer two, at the last checkpoint of 480
projections and 5,373 canonical nodes. Repeated cofactor/rotation certification
and eviction pressure remain; the limit and node allowance were not increased.
This is a failed concrete gate, not B32/global acceptance or a CLI speedup claim.

The final native run is
`20261024T142601Z-282a7277708f4b2282ecbae1272efcb3`. It also passes the
one-entry promotion regression: checked observer changes retain the same
semantic result, and poisoned exact repeats perform no selection, binding or
discovery. Alias admission cannot evict that primary. The complete B1 session
still reaches its unchanged 300-second limit in layer two, at the last
480-projection checkpoint. B32/global and producer acceptance remain blocked.

Cold Apply now uses checked list-spine conversions and direct law instantiation;
uniform unions bypass guard/intersection/join construction. The replacement
removes nonuniform union folding in favor of direct CRT cofactor selection,
interning only the selected decision branches before emitting their equations.
Miss producers run before input-word interpretation; warm pure Apply, rotation
and cofactor requests probe the existing store before walking children.
Reentrant same-key publication is idempotent, so a completed node certificate
cannot duplicate its parent's FIFO entry. Strict-child cofactor proofs use
that same store, and proof emission retains certified row cterms instead of
recertifying their full payloads.

The limit is unchanged. No per-mask theory constants or eager term-to-ID adapter
remain. The 28 focused Python contracts pass. The cache-first structural check
now follows the extracted row helper and its owner-validation callback; it
retains the same ordering assertion and native poison coverage. Strict mypy,
Ruff, formatting and bounded Pyright pass for that maintained Python test.
The latest completed default-unit checkpoint passed in 225.31 seconds
(11,179 passed, 687 validation cases deselected), run
`20261025T060917Z-f02d714eb3554e87be87d98d868d883a`. This includes the closed
C1 coefficient and modular-inverse regressions; subsequent B1/B32 migration
edits still require their own frozen-source validation.
Repository policy passes in 36.83 seconds with no ownership, option, line-limit,
duplicate-body or entrypoint findings (`results/comma-owner-final-repository-policy.json`).
These are dirty-tree development results at Git `f33a96c0`, not reusable commit
acceptance. Concrete coverage and performance remain unaccepted. Larger hit
totals do not establish B1/B32 or producer acceptance.
Forest/CLI authority remains disabled.

The arithmetic owner retains only bounded, checked whole-operation equations.
Numeric suffix caching and the unsuccessful four-/32-bit recipe machinery have
been removed. The final guarded audit is
`20261024T032859Z-2d14d251608e4154b5ff45c1792c1e1b`: 52.92 seconds outer wall time,
1.96 GB sampled peak, exact wide AND/OR and lifecycle checks passed. Its matched
62-guard fixture executes 53,710 primitive conversions, retains no numeric
suffixes, and retains 520 root entries with the original root-cache ceiling.
Packed time is 2.111 seconds versus the earlier fixture's 4.673 seconds. This
is diagnostic arithmetic evidence, not a five-trial CLI speedup or B32 proof.

The full modulo-924 clock is retained. Discovery audits found cycles after
clock erasure and exact-output collisions under smaller modulo projections.
The 327 completed-return and 294 translated-return census counts therefore do
not authorize dropping clocks, physical cocycles or seam guards, and do not
supply global future congruence by themselves.

The semantic Future provider now has a generic weighted normal-form publisher
composed from authenticated graph descriptors for the 16 source families; the
older 14,784 per-source/phase publication loop has been removed from that
producer. The generic global audit now names the weighted five-square bound
and its regression test instead of the retired transfer-mask theorem. Neither
change is accepted producer authority until the concrete B1 session and
consumer chain pass. A Stop carries
terminal position `J` (which determines its Fork/Landmine label) and a separate
additive complete-decade weight `H`; the consumer reconstructs the exact result
`D = 9H + J`. Neither `H` nor packed `D` is a semantic ID. Chronological
composition must preserve exact results and phase shifts: the existing word law
adds a preceding span `n` to `H`, keeps `J`, and therefore adds `9n` to `D`.
The kernel bridge must bind the normal form to the candidate provider's exact
terminal label, ordered children, and distinct local/complete weights. The
candidate map remains untrusted input; matching its IDs is not itself proof of
the semantic action.

The completed-graph refinement must cover the exact 16 initial-source bindings
as well as the 46 roots, with source membership established explicitly. For
each `(kind, leading digit)` source, connect the compiled action to the
period-aware `comma_decisive_endpoint_packet` route. On a guarded crossing,
keep local exponent displacement `d` distinct from completed occurrence
displacement `Delta = d + H`: the provider is selected at phase `(r+d) mod 924`,
`D` is reconstructed from `(H, J)` and terminal control, and ordered successor
classes are selected at `(r+Delta) mod 924`. Direct fork and landmine outcomes
must retain their exact displacements and child order too. This theorem and the
Future consumer transport remain unaccepted.
Boolean B32 termination coverage alone cannot replace exact
`D`, `Delta`, phases, guards, or ordered child IDs. The 278 geometry templates,
327 completed actions, and 4,716 future classes describe different equivalence
domains; none supplies the others' authority. Do not add a 924-one-hot or
rank-bitplane expansion. B32 coverage, exact Stop242, future transport, and
global producer acceptance remain successive gates before the prepared
forest/fuel deletion can be applied. Legacy sparse/native rank sessions
outside the semantic dependency closure are separate audit owners.

The source analyzer now measures actual ML indentation. Previously its regex
matches began before leading whitespace, making nested bindings look like
siblings and truncating outer function bodies. Nested-scope and duplicate-body
fixtures cover the repair. Historical filename-absence/rank-plane assertions
are replaced by current constructor, congruence, clock and bound contracts.

Concrete B1/B32, global induction and producer acceptance remain release holds.
The forest/fuel patch remains unapplied, and the artifact registry is empty.
Artifact admission and the accepted producer chain are required before
production retirement. The passing full unit suite and scoped Python quality
batch do not replace kernel acceptance or clean-commit release checks. All
results here are dirty-tree development evidence at Git `f33a96c0`.

## Antihydra and Mahler cold integration — 2026-10-26

Selective integration of the eleven NC19 cold-scheduler reports uses the
existing source-image issuer and balanced residue worklist. Exact short runs
and the source-certified odd-macro selector retain priority. On a selector miss,
an exact root of 65–4,096 returns publishes the shared balanced effect directly,
eliminating the generic composite wrapper's redundant composition. Warm
consumer lookup still precedes discovery. Selector imports are lazy; benchmark
and poison-test hooks now target their owning modules.

Mahler's source-prefix constructor collapses maximal even runs and exact
odd-to-odd event blocks, retaining the half-open fractional guard and min-plus
summary. Consecutive odd symbols are still separate events. The shared even-run
constructor also replaces supplied zero-word powers in event/odd-macro clients.
No floating logarithm is used to authorize a run.

The archive's flat eight-tick carry kernel was rejected after the operand-work
audit found growing coefficient/tail arithmetic omitted by its original
counters. It is not retained as a second production constructor. Mod-101,
graph/remainder and polynomial packets in the predecessor archives are separate
observer proposals, not substitutes for exact source or safety authority. This
integration does not add those packets, restore alternate matrix algorithms,
or enlarge the current 32-tick Mahler matrix contract. Existing sparse matrix
changes already present in the dirty checkout are not new cold-speedup evidence.

| Gate | Development evidence |
| --- | --- |
| Affected runtime selection | 392 passed in 4.11 s; `20261026T092639Z-6beea77b759e45b995809a7eb09af618` |
| Complete default units | 11,276 passed, 715 validation cases deselected, in 213.41 s; guard elapsed 215.65 s, sampled peak 430 MB; `20261026T093335Z-f7306a4a5dba4045a09015a10c30010b` |
| Exhaustive source/event/centered/grammar selection | 156 passed in 1.27 s; `20261026T093842Z-aa822b50a5c849c1bc31cf493a96c2e2` |
| New exact carry/event theory | `Mahler_Source_Transport` rebuilt in 11 s, runner 18.39 s, sampled peak 1.80 GB; `20261026T092456Z-e992b50af0a94947a6e7a3c5e65cc9c1` |
| Existing numerical consumer refinement | `Balanced_Dyadic_Integration` rebuilt in 16 s; `20261026T093753Z-d101d7d512a74341a8a46490e23c4bb2` |
| Scoped quality | Strict mypy, Ruff and Pyright clean across 11 changed Python files; Pyright 1.1.414 used one serial batch and a 2-GiB heap. Evidence: `results/nc19-{mypy-final,ruff-final,pyright-complete}.json`. Formatting only collapsed one test-helper signature after the full run. |
| Installed wheel | Fresh build and 40 family-first contract cases pass, including Mahler composed-image and Antihydra parent-reuse poisoning; 29.61 s under the standard guard; `results/nc19-wheel.json`. This run used Python 3.14.9, not a fresh minimum-version environment. |
| Antihydra P0 selection | Two passed; the unchanged source-7 non-halting certificate gate failed; `20261026T094050Z-7da9b8104e99479486f58d801a83dd46` |

The new registered theory proves chronological weighted carry composition,
source-word splitting, `H=D+1` offset transport, high-fiber invariance and the
exact even-run guard. Equality at `2*num*3^k = den*2^k` fails the half-open guard.
The two proof sessions rebuilt their selected heaps and reused prerequisite
heaps; this is not a clean rebuild of all dependencies. Runtime handle issuance,
unrestricted future closure and global non-halting are not consequences of these
finite arithmetic theorems.

Five-trial CLI comparisons retained the 16–1,024 workloads, warm requests and
genuine process-cache bypass on the same sources. All value/non-metrics packets
match baseline. For the 1,024-return integer request, bypass median changed
6.49→5.16 ms, warm 4.24→3.90 ms, and fresh-process 176.60→171.99 ms. Counted
operand work fell 109,191→107,567 bits: the removed generic wrapper accounted
for 1,624 bits; the actual balanced compositions remain counted. These are
bounded measurements, not logarithmic arbitrary-source construction.
Baseline/final runs are `20261026T085451Z-872f44dae9694ab588a04ad169409ff8`
and `20261026T093248Z-f488aa027c1e4dd2824486eae869c086`.

Mahler-only and matrix cold timings varied and do not establish a repeatable
speedup. The final Mahler 1,024-return bypass sample was slower (6.47→7.47 ms),
although an earlier replacement run was near baseline. Its exact packets still
match. No broad Mahler/matrix cold-performance gate is declared green. Mahler
baseline/final evidence is `20261026T085535Z-29972f8335634b3fb58f0dcb871b0f26`
and `20261026T093309Z-13743c3adc334dde8250bb721c428f5d`; the 16/32-tick matrix
comparison is `20261026T092551Z-ff39573731d8472d8a7c7152d11abcd5`.

The whole-tree policy scan reports existing duplicate test bodies in HashLife,
Comma and double-reverse files, with none in this change (`results/nc19-policy.json`).
No source-line, ownership, recursion, option or validation-entrypoint violations
were reported. Source-7 non-halting, primality and Comma forest/fuel retirement
remain separate release holds. All results above are dirty-tree development
evidence at Git `f33a96c0`; no release commit is certified.

## 2rev10 four-port and outer-port integration — 2026-10-26

The NC19 reports were selectively ported into the existing SLP arena and
source adapter. The general two-step successor composes four ordered carry
ports over EMPTY/TERM/CONCAT/REPEAT; the old two-step machine and five memo
owners were removed. The finite temporal cone now uses exact content-interned
binary tiles and the overlapping `U_(2s)` square. Spatial repetition and the
bounded temporal square remain distinct from an indefinite orbit certificate.

The temporal route handles complete halos through 2,048 digits / 512 two-step
updates. Existing source-issued growth ports retain border and phase authority.
Larger cones and prepublication scratch refusals retain the exact fallback.
Chunked reservations use the existing ledger, release slack before publication,
and clear temporary graphs even when exceptions retain their tracebacks.
Unpublished arena suffixes roll back on output or memo-publication failure.

The source-conditioned matrix trace rejects incompatible two-bit outer-port
classes before copying and stepping halos. Full halo, odd-step, seam and
pointed checks remain. The existing residue observation additionally reports
an exact source-bound joint border-phase/mod-99/mod-198 period; width drift and
physical transient are separate payloads, not full-word periodicity authority.

| Gate | Development evidence |
| --- | --- |
| Affected runtime and shared fold | 434 passed in 17.28 s after ownership cleanup; `20261026T124430Z-02fa24e2e0cd4c0aa8ef2f2f04a59b97` |
| Scoped strict typing and lint | Zero mypy, Pyright and Ruff findings across 19 files; `results/nc19-2rev-lazy-{mypy,pyright,ruff}.json`; formatting also passes |
| Complete default units | 11,325 passed, 715 validation cases deselected, in 204.56 s; `20261026T125741Z-0a9959e7e33744b5ac930ec367b9b958` |
| Installed wheel | Fresh installation and 40 CLI contracts pass in 27.78 s; `results/nc19-2rev-complete-wheel.json` |
| Colima Linux default units | 11,325 passed, 715 deselected, in 197.61 s; `20261026T124633Z-f8b0af26691e4093894de86dc868d10c` |
| Proof inventory and documentation | PASS: 139 sessions / 451 theories; documentation index passes |
| Concrete kernels | `Double_Reverse_Temporal_Refinement` rebuilt successfully in 65.83 s session timing / 77.95 s guarded orchestration; `20261026T123601Z-1f79cd202bf248f482e12446fd6af507` |

The full unit invocation took 206.69 s including orchestration, with 12.05 s
collection and 445,941,056 bytes sampled peak aggregate memory. Its longest
individual call was 3.27 s; descendant cleanup was confirmed. The existing
validation tier and per-test/invocation deadlines were unchanged.

The native build used the standard four prover threads, one session building,
300-second session timeout and 6-GiB aggregate guard. It peaked at
2,287,657,048 bytes and confirmed descendant cleanup. Parent heaps were reused;
the affected session was rebuilt. Its registered additions check the finite
mod-32 carry cut, exact numeric two-step endpoint and zero-suffix contraction,
four-port SLP repetition, outer-port quotient, and the recursive dyadic cone
against full decimal stencil iteration. Oracle/skip-proof checks remain active.

The Linux run used a copied authored tree and Git metadata, the pinned
CPython 3.14.9 environment, an init reaper, and a 4-GiB container ceiling. Its
guarded invocation took 199.79 s and peaked at 425,799,680 bytes. The temporary
container was removed and Colima restored to its prior stopped state. The
subsequent import deferral was covered by the final native full suite and
fresh-process CLI comparisons.

The subsequent [adversarial audit](#adversarial-identity-lifecycle-and-source-analysis-audit--2026-10-26)
resolved the source-policy findings from this checkpoint. Cone code shares
temporary-store cleanup, and cache publication stays in the existing engine.
The compiler import occurs only after an applicable completed-parent lookup
misses.

Five-trial ordinary CLI comparisons preserve seed 196, the 16–1,024 workloads,
full decimal output and metrics. Fresh processes include interpreter startup;
bypass disables process-cache retrieval and publication on the same source.

| Requested index | Cold before → after | Warm before → after | Bypass before → after |
| --- | --- | --- | --- |
| 16 | 173.09 → 178.81 ms | 9.65 → 9.74 ms | 9.63 → 9.43 ms |
| 128 | 195.13 → 191.55 ms | 30.39 → 20.34 ms | 30.67 → 20.13 ms |
| 512 | 431.74 → 280.42 ms | 238.83 → 109.15 ms | 237.33 → 108.58 ms |
| 1,024 | 887.78 → 501.92 ms | 723.24 → 329.66 ms | 744.79 → 327.48 ms |

These are medians, not an asymptotic or all-source speed claim. At index 1,024,
retained ledger nodes fall from 112,763 to 4,219 and peak nodes from 112,773 to
74,490; output-stream visits remain 1,019. The baseline and replacement records
are `20261026T113108Z-05a62f79125b446fb0693078983d8da2` and
`20261026T125422Z-54a6cf0d55d443368e869e48ea3397b7`. An initial per-operation
reservation implementation regressed; profiling identified reservation-state
lookups, and bounded chunk reservation removed that overhead without weakening
live-use checks or resource ownership.

The existing shared base-z inverse is reused with finite-cut terminal carry
retained. No unrestricted constructor, primality, comma or non-halting gate is
closed by this integration. Evidence is development-only from the dirty tree
at Git `f33a96c0a34491d33361ad5b6e92781a82850a72`.

## Adversarial identity, lifecycle and source-analysis audit — 2026-10-26

Three bounded reviews covered the recent 2rev10 fold/cone publication paths,
the shared resource lifecycle, four Comma ML evaluator/certificate owners,
the shared mod-32 proof dependencies, and Isabelle lexical source analysis.
This is not a whole-tree Moore-minimality or concurrency proof.

The four-port projection had no binding to the particular source whose
word had been folded. An equal-width action from the same arena could therefore
be substituted at its consumer. The fold result now binds the arena, source
node object, action and four ordered rows, with the consumer checking that
binding before using the result. Recycled integer indices, changed actions and
changed rows are rejected. Issuance remains private to the fold; this is a
module provenance boundary, not protection against arbitrary private Python
introspection. The unused source-node count was removed. Snapshot capacity is
reserved before allocation through the existing scratch owner.

Failure review found temporary action tables and projection locals surviving
in retained tracebacks after rollback. The generic SLP fold clears its pending
work and computed values on failure; the four-port wrapper and consumer clear
their temporary references on every exit. Tests retain the actual exceptions
to inspect these failure paths. Existing cone and arena rollback rules remain.

The shared fused workspace also stopped cleanup at the first failed stack
release. Cleanup now attempts both owned stacks, retains unreleased charges
for a retry, and releases workspace capacity only after both stacks are empty.
A pop whose release failed before committing restores its item; an error after
committing leaves consistent accounting. Partial disposal blocks re-entry and
can finish retiring owners on retry. Failure injection covers both sides of
accounting updates, partial clear, retained body errors and partial retirement.

The inspected Comma ML memos are created inside their owning evaluator and
check exact closed theorem requests. Their occurrence keys are application
bindings, not claims of Moore-minimal control identity. No stale-context hit
was reproduced in those owners. The expensive predecessor/weighted-DAG/Stop242
chain remains a separate proof obligation; this audit does not justify its
deletion. Likewise, local 2rev10 tile indices remain inside one temporary
exact-content arena rather than becoming portable semantic IDs.

Both Comma and 2rev10 already consume
`decimal_normalization_mod32_reconstruct_cut`. The review retained their
different physical carry refinements and removed only two unused forwarding
corollaries: their claims remain at `double_reverse_cut_mod32_carry_projection`
and `double_reverse_cut_integer_carry_projection`. The affected
`Double_Reverse_Temporal_Refinement` session rebuilt under the standard policy
in 66.48 seconds of session time / 79.02 seconds guarded orchestration, using
2,494,046,608 sampled peak bytes with cleanup confirmed. Receipt:
`20261026T131733Z-e8b2c3026b4a4a918d766ea101df018c`; supporting heaps were reused.
The finite HOL cone theorem and Python differential tests remain distinct
evidence; no unrestricted future-constructor theorem was added.

The Isabelle parser now distinguishes HOL quoted terms, executable ML
antiquotations, diagnostic strings and dynamic theorem-name lookups. Strings
cannot conceal unused declarations; dynamic lookups and mutual ML function
groups remain review findings, not automatic deletion candidates. Typed
reference evidence is shared within one inventory invocation. Global lookup
uncertainty is computed once, and cross-file reference matching visits only
mentioned names rather than every declaration for every file. Reports keep
their existing public shape and do not serialize the internal evidence.

The existing duplicate test groups were consolidated into test-owned input
validation, immutable payload readers and assertion helpers. Direct arithmetic
oracles, each fresh forensic audit, fixture cases and exhaustive selections
remain. Research pages now link to these dated implementation records instead
of repeating reservation mechanics, historical failed-test counts or current
acceptance tables; their equations, assumptions and source-owner links remain.

Validation for this audit uses the same dirty Git base identified above. The
native default suite initially exposed stale generated sprint navigation;
regenerating it through the existing scaffold resolved the failure without
changing any assertion. The final native receipt below includes that repair.

| Gate | Result and receipt |
| --- | --- |
| Native full default suite | 11,349 passed / 715 deselected in 203.92 s; `20261026T135034Z-82133c452ca14578a853d8084e4bad3a` |
| Colima Linux full default suite | 11,349 passed / 715 deselected in 199.00 s; `20261026T140310Z-85e15966407448faa21a72aa80c1f4a4`. CPython 3.14.9 with pinned development tools, 4-GiB container and standard runner guards |
| Affected exhaustive event-height and prime-adic selections | 45 passed in 0.65 s, including the unchanged independent grids; `20261026T135513Z-b6b4ec676e714031b7d112088e9ae2f0` |
| Strict diagnostics | Zero mypy, Pyright and Ruff findings across the 20 changed Python files; `results/nc19-adversarial-{mypy,pyright,ruff}-final.json`. This scoped receipt does not certify whole-tree status or the Pylance extension; the fresh whole-tree result is recorded in Current status |
| Whole-tree source policy | PASS in 36.68 s, including duplicate bodies and ownership; `results/nc19-adversarial-policy-final.json` |
| Installed wheel | PASS in 28.72 s, cleanup confirmed; `results/nc19-adversarial-wheel.json` |

The first Linux attempt used an image containing retired source files and
therefore collected an obsolete test absent from this checkout. The final run
replaced that source tree with the current Git-discovered authored files before
execution; no assertion was changed to accommodate the stale image. The
temporary container and source archive were removed, and Colima was returned
to its prior stopped state.

The scoped runtime and proof repairs do not make Comma B1/B32/global accepted.
No forest/fuel gate or prepared cutover patch was removed on the strength of
these audits, and no new whole-tree performance or Moore-minimality claim is
made.

## Comma Near reuse and CRT retention repair — 2026-10-26

The Near constructor now selects a checked one-step action before row reuse.
Its physical step count and exact source application remain separate payloads.
Receiving sources must prove their own admission and selection-ID equality
before consuming a representative row. H82/H92 remain distinct. The isolated
H9/H10 fixture reuses a completed row without another transition evaluation;
it is not included in the published production graph. This is one-step control
reuse, not a proved minimal future quotient or physical-duration refinement.

`Comma_Semantic_Graph_Instance` rebuilt successfully in 137.721 seconds of
session time, with 2,010,402,808 sampled peak bytes and cleanup confirmed:
`20261026T143902Z-7cfaf1ba2f6842d69c324a831612b4f3`. Its production catalogue
has eight Near action classes and eight representative proofs, with zero
Near reuse hits. That catalogue does not demonstrate a Near proof speedup.

The weighted CRT transport now prepares its immutable arithmetic simplifier
once. Exact reflexive actions and canonical numeral offsets use kernel
reflexivity; differing offsets still receive checked arithmetic conversions.
Selector plans publish child proofs in postorder, then release detailed input
and piece lists. A charged, scope-local key/result memo remains. Parents
revalidate and reseed their completed children's endpoint terms after child
cleanup, preventing repeated serialization. Proof publication is inside its
reservation, so failed publication rolls back the uncommitted charge while
previously completed child proofs remain available. The predecessor theory's
unbound `offset` pattern was also renamed to avoid resolving to an imported
record selector.

The latest native B1 run passed its cache, foreign-context, offset, rollback,
new-parent reuse and bounded selector fixtures. It then failed the concrete
constructor's unchanged 8,192-entry arena limit at 169 completed graph actions:
3,879 retained nodes and 3,872 proof entries, with scratch returned to zero.
The checkpoint was 236.736 seconds into construction; guarded orchestration
took 259.128 seconds, peaked at 2,584,252,840 bytes and confirmed cleanup.
Receipt: `20261026T152022Z-cd44987798cd437fb71c4e475e41ea73`. Supporting heaps
were reused. This is a failed B1 gate, not an accepted B1 heap.

At the matching 128-action checkpoint, the revised run took 80.626 seconds
versus 242.143 seconds in the archived
`20261025T192712Z-4a3a0900fde2441a905fed1653712d39` run. Both retained 1,815
nodes and 1,790 proofs. Compared with this turn's pre-reclamation run, peak
entries fell from 6,194 to 4,082. These are checkpoint improvements, not an
end-to-end proof or CLI performance pass. The remaining bottleneck is retained
action/proof expansion; current totals do not distinguish auxiliary selector
proofs from normalization proofs well enough to justify selective retirement.
Neither capacity increases nor uncharged caches were introduced.

The 36 focused Python contract tests pass in 1.640 seconds
(`20261026T145057Z-1af9435f63994ce4894e9756eac40df7`). The three changed Python
test files have zero strict mypy, Pyright, Ruff and formatting findings in
`results/comma-near-quality-{mypy,pyright,ruff,format}.json`.
The full default suite also passes: 11,349 tests in 203.775 seconds, collection
in 12.308 seconds, 451,642,688 sampled peak bytes and cleanup confirmed
(`20261026T153115Z-53ad514bcb84460d94ef714587f29835`). No workload or assertion
was removed to obtain this result.
Repository policy, documentation links and the registered proof index pass
under the standard guards (`results/comma-near-policy-final.json`,
`results/comma-near-docs.json`, `results/comma-near-proof-index.json`). The
source-policy repair removed a redundant closing comment from the graph
constructor; its executable ML did not change after the passing graph build.

The prepared forest patch applies cleanly and preserves the extracted test
payload helper. Its non-authoritative candidate JSON was removed. The cutover
README now requires an accepted native global artifact and an independently
reviewed production admission entry before activation; a positive test-only
registry is not production authority. The patch remains unapplied, the live
registry remains empty, and B32/global/producer acceptance is still required.
