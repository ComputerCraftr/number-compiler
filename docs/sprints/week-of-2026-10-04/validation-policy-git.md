# Validation budgets and Git provenance

Period: 2026-10-04 through 2026-10-10 (Sunday–Saturday).

[Week index](README.md)

## Objective

Replace competing validation deadlines and custom source-version tracking with
one execution policy and Git-owned provenance. This migration does not complete
the comma forest cutover or any other mathematical or production obligation.

## Changes

The shared policy sets Python tests to 60 seconds including fixtures and teardown,
Python selections/full suites to 300 seconds, and standalone commands to 60
seconds, all under a 4-GiB process-tree guard. Each Isabelle session has a native
60-second limit with four prover threads, one building session, Java maximum
1 GiB, Poly/ML maximum 4 GiB and an external 6-GiB process-tree guard.

The release runner owns pytest execution, exact repeated selectors and one
collection manifest. Its parent watchdog also checks the active test deadline,
so native calls holding the GIL cannot disable enforcement. Timeout overrides
are rejected. Nested commands retain the enclosing deadline and memory budget.
Standalone developer entrypoints use the same guard. Isabelle's own session
inventory determines the orchestration fail-safe; declared ROOT imports are
reported separately from actual native build dependencies.

Git commit/tree object IDs, object format and dirty status replace recursive
source hashes and fingerprint versions. Development evidence is never reusable
acceptance. Acceptance consumes one clean detached worktree without staging,
committing or discarding user work. Run-local generation tokens retain stale
proof-context rejection. Artifact integrity and mathematical hashes remain.

The Python runner also accepts opt-in `--profile` for diagnostic cProfile output
under the same deadlines. Phase records retain bounded failure excerpts after a
watchdog kill. Each recorder owns its diagnostic caps: tests of small log limits
cannot truncate the enclosing suite's recorder.

Profiling led to concrete construction changes. Canonical run words now use a
binary construction frontier instead of repeatedly rebalancing growing prefixes.
Nested joins reuse their boundary validation, and the word authority uses one
weak registry instead of two. Public type, shape, authority and mutation checks
remain. Factored-carrier source admission checks the supplied tuple directly;
output decoding intersects three run streams instead of descending from each
plane root for every coefficient. Exhaustive cases and reconstruction poisons
are unchanged.

Primitive binding resolves its compiler handle once per lookup. Decoder-table
audits share one local traversal and validate input signatures independent of
their canonical port ordering. Source-policy checks share one authored AST
snapshot per invocation. Repository proof ancestry tests share an immutable
parsed graph; mutation tests and the cold inventory test still construct fresh
graphs. Comma tests similarly share only immutable reference inputs, retaining
fresh runtime/cache construction where that is the tested behavior.

## Established results

The source-20 prelude now builds under the standard Isabelle policy:
`Comma_Source_Entry_Witness` takes 18 seconds and `Comma_Source_Entry` takes
5 seconds in development run `20261004T100019Z-7693c18fc18849939bf1d1af209e3998`.
The witness reuses the checked arithmetic catalog and restricts simplification
to the required arithmetic/list rules. Profiling isolated the previous timeout
to inherited automation in concrete edge and weight evaluation; the generic
induction and all 230 edge checks took about 1.3 seconds after that repair.
The exact prelude, terminal fork and transition-weight assertions are retained.
This establishes the source-entry bridge, not the B1/B32/global forest cutover.

The new output-template experiment exposed a separate construction regression:
run `20261004T094254Z-8501d1570ccb4dd4b403a01f323afc9e` exceeded the 60-second
individual-test limit while rebuilding shifted Boolean columns. That failure
remains diagnostic evidence; the template producer must be repaired before it
can serve as a production owner. Generic template equivalence alone does not
replace the sparse B1/B32 or forest-admission implementations.

The first focused migration run passed 148 tests and failed four new fixtures.
The next run passed 209 tests and exposed 13 fixture/API migration failures.
These runs are diagnostic development evidence, not final acceptance.

Installed-wheel validation completed in 35.576 seconds under the new 60-second
command limit. `Comma_Round_Witness_Check` completed in 9 seconds with four
threads. `Comma_Sector_Mask_Instance` hit its native 60-second limit. A profiled
rerun reached 80 of 327 sector rows: several regular publications took roughly
2–2.5 seconds each. Repeated theorem-bearing mask publication remains a concrete
proof-construction bottleneck.

The broad Collatz/automata selection passed 753 tests in 36.42 seconds; its one
failure was the reverse probe's removed metric key. All selected Collatz cases,
including the current source-image P0 assertions, passed. The reverse probe test
is migrated to its actual source-image publication, replay, scalar equality and
explicit audit fields. Its measured higher-runtime work remains visible and the
separate reverse performance gates remain required.

A post-optimization slice passed 26 tests, including decoder forgery/mutation
audits, symbolic return construction, and all 6,859 cases in width-eight partition
zero. That partition took 9.366 seconds versus 10.649 before the bulk builder and
streaming decoder changes. This comparison predates the additional direct-source
admission optimization; it is a diagnostic sample, not five-trial acceptance.

The full all-tests selection still reached the 300-second watchdog. It is not a
pass. Inspection also found the timing test's module-global cap mutation had
truncated its enclosing log; the new recorder-isolation regression covers that
failure. At that checkpoint no workload was reduced and no exhaustive test was deleted: independent
review found that the carrier, geometry and harmonic grids test different
implementations and are not interchangeable coverage.

The cache-isolation, timing-recorder and validation-policy selection passed
45 tests in 6.19 seconds. A fresh isolated process cache prevents tests that
require a cold cache from clearing unrelated retained objects; teardown restores
the prior cache and invalidates only the explicitly owned instance.

The B1 whole-grid key audit and 46-by-924 source/chart comparison are now
validation-only. Cheap collision witnesses and production CLI tests remain in
the unit selection. Whole-repository policy and registered-proof inventory
conformance checks likewise run in validation; the mandatory quality commands
already perform those complete scans. Adversarial temporary-tree tests and
specific release-dependency assertions remain unit tests. The whole-tree package
ownership scan is likewise validation-only; package-contract fixture tests and
public import assertions remain unit tests. This changes selection
ownership, not the exhaustive assertions or the production workload.

The default unit selection then completed in 295.07 seconds: 8,855 passed,
five failed and 2,008 validation cases deselected. This closes that run's timeout
only. Four reverse higher-runtime assertions and one special-number resolution
assertion remain failing; no Collatz failures were observed.

The source-20 bridge now derives an indexed trace by induction on the checked
control trace, instead of evaluating `comma_finite_weighted_run`. Three
source-specific fuel bridge lemmas were replaced by the shared
`comma_control_trace_indexed` theorem. The exact first fork, 412,987,858
transitions and endpoint uniqueness are retained. The rebuilt source witness,
source entry and uniqueness sessions took 17, 4 and 4 seconds respectively;
the subsequent native dependency audit of the source-20 theorems passed in a
five-second uniqueness build. This does not discharge the B1/B32/global future
instance or authorize deleting production forest admission.

The revised Python return-template selection passes 39 tests in 37.51 seconds.
It preserves exact output-label reconstruction, separates occurrence shifts,
rejects invalid CRT scopes and checks interrupted atom-relabeling cleanup.
The earlier mismatch was an inverted parity predicate; the correction reuses
the canonical component-equality builder. The scope quotient now derives
anchors from extensional decision structure rather than the input scope split.
This is constructor validation, not evidence that the public CLI has migrated.

A later focused selection includes dynamic memo accounting and passes 66 tests
in 30.82 seconds. The unchanged selection previously took 45.23 seconds. The
profile isolated 9,013 intermediate maximal-scope extractions; continuation
construction now retains reduced MDD columns and reconstructs scopes at the
selected output boundary. Template rebasing shifts the four CRT components
directly. Output labels, phase transport and source authority remain separate.
These timings are development measurements, not a cold CLI cutover claim.

The B1 timeout was narrowed to a missing modular-bound rewrite in the graph
root bridge. Explicit modular equations also repaired the phase-translation
proof. The column/reconstruction theorems and dependency audits now complete;
the session subsequently reached the previously unloaded ML constructor and
exposed ordinary API/syntax errors. Typed records, named graph constants and
set-typed binding membership replace the malformed term construction. The
new publication theory still needs a checked concrete instance before it can
replace sparse B1/B32 or global forest admission.

The repaired generic `Comma_Semantic_B1` session passes in 24 seconds, including
the publication lemmas, ML loading and dependency audits. The separate concrete
graph instance still times out at 60 seconds while proving source rows (roughly
355 source occurrences reached). It has not reached template publication.
This distinguishes a checked generic interface from the unresolved executable
instance and prevents attributing the generic timing to the CLI cutover.

Whole-tree quality checks passed after the generic repair: strict mypy, pinned
Ruff, formatting, source policy, documentation, proof inventory and installed
wheel. The installed CLI retains its existing release holds; this check does
not certify new forest admission or reverse temporal construction.

## Rejected approaches

No timeout increase, skipped assertion or expected failure was used to obtain a
pass. Following the explicit scope adjustment, exhaustive research-only grids
run through the existing validation selection; their cases remain intact. A cached heap is not cold-build performance evidence.
Dirty Git status before and after does not prove dirty source was unchanged.
Historical SHA-256 evidence is not translated into current commit acceptance.

The assertion migration preserves the following contracts:

| Previous mechanism | Replacement coverage |
| --- | --- |
| Recursive source fingerprint and inode snapshots | Git commit/tree/dirty tests, isolated clean worktree tests, changed-checkout rejection and preserved user work |
| Separate pre-collection pytest process | Exact same-run collection manifest and missing/unexecuted-node rejection |
| Independent 35-second signal alarms around workloads | Unchanged measured latency assertions; termination belongs to the shared 60-second test watchdog |
| Per-launcher timeout and memory flags | Canonical policy, forbidden-override tests, nested deadline/memory clamping and descendant cleanup |
| Fingerprint-bearing proof generation | Run-local generation IDs with context ownership and stale-generation rejection |
| Old Collatz `TileScheduler.point`/`TileRadixObservation` ownership | Positive spies on the admitted physical-image observers, poisoned original-source reconstruction and unchanged exact output assertions |
| Reverse probe tile-leaf/profile columns | Actual source-image publication/replay and explicit ownership audit; higher-runtime work remains a measured diagnostic with separate P0 assertions |
| Repeated current-tree proof parsing per ancestry case | One immutable module fixture; all ancestry cases and temporary-tree mutation checks retained |
| Whole-tree policy and proof inventory rescans inside unit | Mandatory quality commands and validation tests retain all global assertions; adversarial small fixtures and dependency checks remain unit |
| Unmarked exhaustive B1 key/source comparisons | Existing validation selection retains all 42,504 cases; unit keeps collision witnesses and production consumers |
| Per-case fresh poison mocks in exhaustive reverse checks | One poison around the unchanged full enumeration; exact source/output comparisons retained |

## Validation provenance

All runs in this record are development runs on dirty Git HEAD
`5f15e7f7915fc98b7a324b70a0400d7b984557f4`, tree
`3e10b65d7496d1af3dbe523fb61c805dac051e16`, object format `sha1`.
These Git IDs identify the committed base only; they do not certify the edited
workspace. The runner did not stage or commit it.

Local ignored run directories:

- `20261004T073453Z-0fc6eeed65294c3d8c72318dcf8798e5`: initial focused tests.
- `20261004T073551Z-86edb12c6c924c5c9ce4df151d084493`: initial quality and installed-wheel checks.
- `20261004T074010Z-7431a7819fa44c7db6b559d35653fe3c`: focused proof build.
- `20261004T075128Z-606e77a6ef104bf9a52170f0862fd21f`: second focused test run.
- `20261004T075750Z-0d2b4fa1c1c1476c868c8b35e34e9104`: profiled sector-mask timeout.
- `20261004T083314Z-045cd711544a40759ea5933544fb9164`: lazy reverse, continuation and decoder cProfile.
- `20261004T084415Z-ca8ed5d8ac0d4f0481b1e8634432be1e`: exhaustive width-eight constructor cProfile.
- `20261004T084953Z-f24070001f854e8180e347fa45437af1`: broad Collatz and word-constructor checks.
- `20261004T085141Z-55cace522c034950bd67e8d0660a422b`: 26-test post-optimization slice.
- `20261004T085329Z-b03bf3446ee0413281b882d0ae1fa17e`: incomplete all-tests selection, watchdog timeout.
- `20261004T091425Z-e37d79cf35e1488d8b7cf9f4074994b3`: 45 cache-lifecycle and validation-policy tests passed.
- `20261004T092327Z-101e48a647cc4a6ebe6337ab07585720`: complete default-unit run, 295.07 seconds, five failures retained.
- `20261004T091504Z-2cf8c764d17d4d1b97262d9b7ab414e9`: source-entry witness timed out after rewrite repair; not a proof pass.
- `20261004T100555Z-ce09834b70854fc78c62445d1016c422`: source-entry and uniqueness sessions passed; Semantic B1 failed, so the invocation is not an aggregate pass.
- `20261004T100740Z-d604caa9198644e88f76157065969ae5`: source-20 native proof-dependency audit passed.
- `20261004T101336Z-108e9a888e7c40e0957ae62ea41df138`: revised Python template construction completed in 50.28 seconds, with 35 passing tests and two exact-reconstruction failures retained.
- `20261004T102100Z-e8f3b0c6e9a94e77bb23576f49e6a9ba`: focused cProfile run identified repeated template-key construction as the dominant cost.
- `20261004T103121Z-cdcdecdda1e84d9dba97fb7519158d21`: 39 focused template/function tests passed in 37.51 seconds after the parity and canonical-anchor corrections.
- `20261004T103731Z-2d521549d69440989750bf554cd24afd`: 66 template/function/ledger tests passed in 39.33 seconds.
- `20261004T104949Z-6e35fcda62f847f6b0f57d2d29f4c074`: the same 66 tests passed in 45.23 seconds; the slowdown prompted another profile.
- `20261004T105136Z-b48b7d1f0f0441909359b3c78410e49e`: focused cProfile run passed in 34.21 seconds and identified intermediate scope normalization as the remaining dominant cost.
- `20261004T110016Z-fda567bee1f44c29ba9170a65bb999a8`: 66 tests passed in 30.82 seconds with MDD-preserving continuation construction.
- `20261004T110230Z-e04a99b6147c468e9ed2e2c33687cfda`: column proofs, audits and ML loading completed; the new publication theory failed three local proof obligations. The session remains red.
- `20261004T111102Z-1db4322411fb45b8bf6bade158e6de48`: whole-tree quality and installed-wheel checks passed.
- `20261004T111409Z-0be0138efe644363b954328e2f639a89`: 28 cache-authority and source-clone tests passed in 0.71 seconds.
- `20261004T111429Z-4407e2cfe2bd4d72822a451b81d7bddb`: generic Semantic B1 session passed in 24 seconds under the standard policy.
- `20261004T111633Z-74b97c3b263e442986577bee5670d188`: concrete source-graph construction timed out at 60 seconds; no concrete template or global-cutover claim follows.
- `20261004T112649Z-a1f2695e1f14462b8c2ed2c707bac06f`: extra local memoization still timed out before concrete quotient publication. That tuning was removed in favor of reversing the source-certificate dependency.
- `20261004T113107Z-dbdbfe7e160a44bb9fe4eeb628fa526a`: direct symbolic B1–B32 poison test reached the 60-second test limit.
- `20261004T114409Z-037e3a2ff4c94a42b4cd2a917ae08f1d`: 28 checks passed; one malformed overlap fixture hit the period check first. The fixture was corrected to isolate the overlap invariant.
- `20261004T114534Z-c91694e55b974532bf9424c27153778f`: corrected shape and observer-poison checks passed; the unchanged full powering test still timed out.
- `20261004T115004Z-eba1e8e37970491380c1b80567a2639d`: 23 return checks passed, including collision-safe cached hashing and shared cardinality accounting; full powering still timed out.
- `20261004T115150Z-529dc9ccecb74c90a9c967398798e00d`: bounded profile retained B1 diagnostics before timeout in B2. A reporting-field typo also failed the wrapper; this is diagnostic evidence only. B1 showed repeated Boolean MDD composition and translation dominating construction.

The next dependency deletion separates the optional scope/function observer
from direct CRT-column construction. Source-row theorems remain available only
through the explicit graph audit; the unused graph-validity ML publisher was
deleted. The unregistered graph/CID table prototype was replaced by a direct
packet-slot source interface and registered for kernel checking. Its source-fold
refinement, concrete template publication, semantic B32 and global future
connection are still required before forest admission can be removed.

Python canonicalization no longer exports every output column to scope lists.
MDD nodes cache their structural hash without changing exact equality, and
partition cardinalities share subgraph work. The direct MDD uses true CRT radices
4/3/7/11; invalid binary encodings belong to the separately tested optional
bit-vector observer. These changes do not establish a CLI cutover or erase the
remaining powered test deadline failure.

The effective toolchain is recorded in each run manifest; this migration used
Python 3.14.8, pytest 9.1.1, pytest-timeout 2.4.0, mypy 2.3.1 and Ruff 0.16.9.

The follow-up dependency audit removed candidate prerequisites on physical
source-row theorems and graph validity, and removed unused per-source action
closures and proof-goal terms. The old graph constructor is explicitly an audit
owner. Candidate ML evaluation supplies untrusted data; it does not certify its
own result. The aggregate source-fold and occurrence-binding proofs are still
required before these data can replace release authority.

Python squaring now cofactors matching CRT nodes rather than taking a Cartesian
product of output columns. An owned transport memo shares translated child
geometry while keeping each occurrence's output labels separate. In bounded
run `20261004T122053Z-165b041fb75246b884c4beb702b222d1`, B2 took 4.70 seconds
versus 30.66 seconds in `20261004T115926Z-1f3b4bcc110649c2a3c6967f7bb0b78f`.
B4, B8 and B16 took 5.44, 14.86 and 17.08 seconds respectively. The invocation
still timed out before B32; repeated canonical subtree translation remains
measured work, not an accepted performance result.

Additional bounded validation:

- `20261004T115647Z-4ab55d70222d4f0680983f1f198151bf`: the minimal direct-slot source interface passed its Semantic B1 kernel session in 15 seconds. This predates the expanded source-fold theory.
- `20261004T120239Z-253748e98b564593b1af56b684da9f3d`: four source-dependency checks passed.
- `20261004T121617Z-b9fd111bffed40109f0145039f1481f3`, `20261004T121834Z-77dccf019e12430b9abcd778a9313c00`, and `20261004T122210Z-eb5d4971ffda471ca4713ff810d5838b`: expanded source-transform kernel builds failed on syntax/local proof obligations. None is a proof pass.
- `20261004T121716Z-adcf8687453847d18bcd205bb6bc5165`: selection referenced nonexistent filenames; no tests ran. The selection was corrected.
- `20261004T121727Z-a47c04b771fb41dd9953ebeb526a3e63`: full symbolic-power test timed out at 60 seconds; cleanup was confirmed.
- `20261004T122015Z-0c456582f3ba45dfa6e114f0d1890b4a`: 28 symbolic-return and source-dependency tests passed.

The October 4 follow-up distinguishes internal B1 template minimization from
powered root application. B2 and later now publish their completed columns
without searching clock rebases again. `(level, root)` addresses a macro within
its authenticated owner; it is not a claim of universal extensional action
minimality. Exact Boolean columns share a ledger-owned interner, while output
labels and clock transport remain occurrence bindings. Temporary translation
work uses scoped reservations.

The former positive template-hit assertion is replaced by positive exact-column
retrieval and absorbing-terminal reuse assertions. Exact sample outputs, the
sharp B32 stop at `(root=24, phase=42)`, all 276 publications, no point replay,
warm-demand laziness and ledger cleanup remain checked.

- `20261004T123048Z-c29e621e269c4589a09c09364ea160d8`: the expanded generic source-transform theory and candidate ML compilation passed the kernel session in 21 seconds. Concrete candidate evaluation and table exactness were not established by this run.
- `20261004T123621Z-adc1885e1c8f42cd9bcfc9ca1e70bd1e` and `20261004T123837Z-35dbdf79240e42d6ab59e094d4a19beb`: candidate-data execution exposed missing generated-computation numeral inputs. These are failed runs, not certificates.
- `20261004T123934Z-455d910114de48ce85acb7953d96de5e`: 31 focused tests passed in 42.67 seconds. The unchanged B1–B32 exactness/poison test took 15.79 seconds.
- `20261004T124111Z-1055f11a982b4623b2a621491011fe00`: the standalone cold symbolic-power probe completed in 13.48 seconds, with sampled aggregate peak memory 92,029,504 bytes. Per-level construction times were B1 5.038, B2 2.973, B4 2.398, B8 1.533, B16 0.720 and B32 0.430 seconds. Rebase candidate counts stayed at 249 after B1; the B32 square added nine exact column entries. These are symbolic-constructor measurements, not public CLI or global-proof acceptance.

Global safety still imports sparse B32 and native rank/run-cycle authority.
Changing that edge requires the checked source-fold and binding refinement,
the semantic power/B32 provider and its concrete future occurrence bridge.
Candidate counts and the Python speedup do not discharge those obligations.

- `20261004T124436Z-58d85bef9bb34c078e524af49cd4657b`: 32 focused checks passed in 42.44 seconds. The B1–B32 test took 14.15 seconds with template canonicalization poisoned after B1; shared transport retained separate output labels and released failed workspace reservations.
- `20261004T124911Z-579354dc9d0d45beb7e139f62f431e24`: typing, lint, formatting, documentation and installed-wheel checks passed. Policy found duplicated negative-test setup; proof inventory found the new source-transform theory lacked an explicit oracle audit. Both findings require repair and a new quality run.
- `20261004T124600Z-022e7c6b9bbd46298a9181aff7c72c5e`, `20261004T125133Z-cd5da5d6ee894862a7b7498f11f98bfd` and `20261004T125330Z-137f5252d7d0499d849da8397353e617`: the new one-step source/return bridge failed local instantiation and syntax obligations. These runs do not certify the candidate evaluator or the global provider.

Independent review confirmed the input-translation sign, absorbing terminal
weights, owner-local cache authority and absence of a Cartesian column join.
The column store currently interns exact immutable MDD roots; cold translation
still visits and charges MDD nodes. It is not yet the proposed full translation
orbit `ColumnCID` algebra. Review also identified queued workspace objects
allocated before reservation; that accounting repair is tracked separately
from output correctness.

The subsequent scheduling review removed the newly added, unused
`comma_semantic_b1_source_slot_round_output` case proof and its eager
consolidation block. The eventual publisher refinement must consume the
canonical continuation theorem rather than introduce a second endpoint proof.
Local foundation results retain one batched native/oracle dependency audit.

Ordinary `writeln` markers were not visible through the bounded build's profiling
channel. Missing markers therefore did not establish that construction was
unreached. All new diagnostics now use `Comma_Proof_Profile`. In
`20261004T131913Z-68e6ce1700524608b2ba7ca984d530ea`, the bridge and safety audits
completed, source discovery took 8.814 seconds, and the session timed out in
aggregate table evaluation. This identifies a second bottleneck beyond the
reviewed proof scheduling issue; neither run is global acceptance.

- `20261004T130333Z-8a17dc7bb2e74f5c92c8f651a0405dae`: 34 focused tests passed in 48.95 seconds, including Stop-only B32 bindings and the attained height 26. Complete powering took 21.57 seconds after additional allocation accounting.
- `20261004T132218Z-19df76eeab004ef2a4a304ad7264e271`: 35 focused tests passed in 50.69 seconds after separating transient workspace lifetimes from retained output reservations. The added budget test checks repeated compositions reuse scratch without accumulating historical reservations.

The direct B1 candidate fold now reuses discovered packet actions and combines
normalized CRT/MDD columns. The aggregate HOL evaluator and its row parser were
removed. The physical-row audit remains a separate session; a dependency test
prevents it becoming a semantic B1 prerequisite. Its redundant oracle walk was
also removed because the shared native dependency check already checks oracles.

- `20261004T133245Z-81ecddaff138414e8e0ef9d8583bce55`: `Comma_Semantic_B1` rebuilt successfully in 41 seconds with the standard four-thread, 60-second session policy. The guarded build peaked at 2,136,330,880 bytes. Discovery took 11.144 seconds, the symbolic fold 2.194 seconds, rendering 0.022 seconds and interning 0.894 seconds. Candidate construction retained 430 source bindings, 46 roots and 278 templates. These counts are diagnostic data, not a concrete refinement certificate.
- `20261004T133349Z-0797fcf5a4e44e8597d86d58256594ee`: typing, lint, formatting, documentation, proof inventory and installed-wheel checks passed. Policy identified duplicated workspace setup in two tests; all four copies of that setup were subsequently consolidated into one accounting helper without removing assertions.

The remaining semantic obligation is a generic source-table fold refinement,
a checked source-order instance, and exact reconstruction from emitted template
bindings. The existing continuation theorem supplies local arithmetic but does
not alone discharge those composition obligations. Global B32/Future authority
and production forest admission have not been switched by this candidate build.

Follow-up cleanup removed unused scope-building helpers and explicit
intermediate consolidation from the column and publication theories. Shared
native/oracle audits remain. Final validation after those changes:

- `20261004T133712Z-b90345d8514d4a95aa70dbeec5ee5f83`: 36 focused Python tests passed in 49.68 seconds after consolidating workspace accounting.
- `20261004T133917Z-91669edad59a45a6a65ffd223c996661`: the rebuilt B1 session passed in 54 seconds under the same standard limits. Discovery took 20.477 seconds, symbolic folding 2.335 seconds and interning 0.990 seconds. This latest timing has less margin than the earlier rebuilt results and is not evidence of a global proof cutover.
- `20261004T134041Z-f43636b4fee645b1ba21bd80bb0e0edc`: typing, lint, source policy, documentation, proof inventory and installed-wheel checks passed. Formatting required collapsing one test expression; after that edit, the standard guarded formatting recheck `20261004T134221Z-5ee2ebc091aa4b7e9d52535551e3e724` passed.

### Global semantic-provider review and suite accounting

The new review confirms three distinct migration gates: certify the symbolic
source fold and output bindings, publish concrete semantic powers through B32,
then connect the resulting boundary occurrence to global future safety.
Sparse/semantic agreement remains a differential bridge, not replacement
authority. The new local slot-output lemma is now consumed by the source-row
refinement; this differs from the earlier unused case proof removed above.

The candidate constructor no longer renders an all-source HOL table or keeps
discarded source binding rows. It interns during folding and retains normalized
template columns plus the 46 root bindings. The checked finite instance is still
pending. In `20261004T140801Z-338d6cedf8b74a44b3047e0a4a70b180`, folding and
interning took 1.617 seconds, with 278 templates, 10,397 template columns and
2,258 root binding rows. The session failed new local proof obligations, so this
is construction timing only, not proof acceptance.

The first full run (`20261004T134359Z-fbc70c4439bb4f0bb6ac91fdddd34c20`)
timed out at 95 percent. It also exposed a shared ownership regression: every
`OwnedMemo` allocated an unregistered cost dictionary. Dynamic costs now reside
in immutable wrappers in the existing ledger-owned store, while public reads
and audit payloads expose the original values. The combined resource/cache and
symbolic-power selection passed 52 tests in 23.51 seconds in
`20261004T135508Z-1822d5b900804f26b93e1a360f512acb`.

Test ownership was corrected without deleting assertions or reducing workloads:

| Previous default coverage | Replacement execution | Contract preserved |
| --- | --- | --- |
| Abstract comma temporal-observer census | Explicit validation selection | Complete research census and observer distinctions |
| Reverse geometry: mod9 skew, consumer schema/pullback, mirror-pair quotient, growth coboundary and threshold geometry | Explicit validation selection | Research-only geometry and finite quotient experiments |
| Development forest regeneration | Explicit validation selection | Reproducible generator output; production certificate tests remain default |
| Exact sparse B1 import tuple | Updated migration guard | Compact publisher remains authority; semantic agreement is allowed without claiming replacement |

All migrated research tests and the updated proof guards passed together:
`20261004T140929Z-2eb6213d43ee4ba88ee2856141102ced`, 61 tests in 7.16 seconds.

The next complete default run finished within policy:
`20261004T135738Z-7465c68825034f53bf0d5b8072bf1131`, 8,816 passed and six failed
in 285.76 seconds (287.79 seconds including the guard). Sampled aggregate peak
memory was 436,765,584 bytes and cleanup was confirmed. No Collatz test failed.
One failure was the import assertion repaired above; the other five are the
existing special-number resolution and reverse continuation-work assertions.
Those assertions remain unchanged and red. This dirty development run is not
commit acceptance.

The follow-up shared memo typing repair exposed a profile audit reading private
memo storage directly. It now uses the canonical audit accessor, preserving
payload unwrapping without executing an observer. Resource, profile, symbolic
power and repository checks passed together in
`20261004T141816Z-e69834f5329943a5a5a81ac20d94dd9b`: 79 tests, 36.41 seconds.

New generic proof interfaces cover source-row scope refinement, weighted column
composition and the semantic Stop-to-literal-occurrence bridge. They are not a
concrete finite provider. The bridge retains exact ordered alternatives and
uses exponent increment `h`, decoded from `D=9h+J`; it does not use `D` as an
exponent increment. Future-class sharing still requires the exact list-valued
child-map congruence, including multiplicity.

Validation caught a session-scheduling regression in
`20261004T142446Z-7b0d70872ca546d7bf502746d673d5b8`: declaring B1 only as an
additional session dependency left semantic-future rebuilding upstream
arithmetic from source. It timed out at the unchanged 60-second limit. The
existing semantic-future session now inherits the B1 heap. No extra session or
timeout allowance was introduced.

The generic table-transform theory also ran an audit-only candidate constructor,
printed its metrics and discarded the result. That invocation was deleted;
the constructor definition remains available for the eventual checked publisher.
This removes unused construction, not a mathematical obligation. Subsequent
checks reached concrete local proof errors in 26–27 seconds; those failed runs
do not certify the new interfaces. The regression checks against eager audit
execution and concrete sparse authority passed in
`20261004T143228Z-b0253c92589440639bc21e21f44c9dff`: nine tests, 0.27 seconds.

The later B1 check (`20261004T144204Z-b5a68ccfc4174790808a74355e91125a`)
again reached the 60-second session limit. The Isabelle command-timing database
showed the source-row dependency audit completed, while the weighted-power
proof did not. Its final column proof was expanding the action cases after the
exact column theorem had already established them. That expansion is being
replaced by direct set extensionality and the existing square theorem, without
changing the session limits. The next run
(`20261004T144946Z-9d892d525cc143b085a255e2f561a56d`) stopped on local Isar and
existential-witness errors in 26 seconds; it is failed evidence, not proof
acceptance.

The timeout persisted in `20261004T145407Z-6e641fbeb95243c796aa1d64f0d677e9`.
Inspection then found a missing premise in the earlier row-soundness proof:
it tried to infer membership in the left column from membership in a composed
row without using the relation between those rows. The repair first derives
left-column membership from the composition definition and then applies row
exactness. The earlier suspicion that the final square proof alone caused the
timeout was too narrow.

The proof schedule is now repaired. The row proof first establishes the
left-column phase membership, coverage fixes the known left action before
simplification, and set proofs reuse the exact-column equation. The temporary
completion diagnostics were removed. The source-fold induction, weighted
column theorems and candidate ML compile together: B1 rebuilt in 19 seconds in
`20261004T150604Z-d8cd9c39d09b40219559646f63188014`. That run still failed in the
future bridge's dependency audit because it asked for all three conclusions of
a shared lemma although only conclusion 2 was used. The bridge now names that
exact conclusion. The follow-up
`20261004T150742Z-821d6032794b4b42a2779e1a203204b4` passed, rebuilding semantic
future in 31 seconds and reusing the B1 heap. Both used the standard per-session
60-second, four-thread, 6-GiB policy.

Candidate construction also now indexes output bindings and canonical partition
representatives rather than repeatedly scanning them. Reporting retains scalar
snapshots rather than the scope/shift scratch caches; binding-row counts are
recorded when rows are constructed rather than reparsing generated HOL terms.
These changes are kernel-compiled ML, not a newly measured concrete-candidate
performance result.

These green generic proofs remain conditional on exact source order/bindings
and an exact B32 provider with Stop weight at most 242. The concrete semantic
B1/B32 publisher and future-class/global instantiation are still outstanding.
The active production forest authority has not been deleted or relabeled as
proved by these interfaces.

Final focused validation passed 61 tests in 21.78 seconds in
`20261004T151000Z-fbe2b9bf570f48fcb74f8c14bdade9b2`, covering semantic/sparse
migration guards, symbolic B32 construction and resource/process-cache lifecycle.
Whole-tree mypy, Ruff, formatting, source policy, documentation, proof inventory
and packaging passed in
`20261004T150835Z-fd3580dd5df44273818c95cf6b4b7eee`. These are development runs
on the existing dirty checkout; the earlier complete-suite result and its five
remaining genuine release failures have not been superseded by a new full run.

The follow-up review identified eager right-column translation before Boolean
intersection. Python's existing multi-output substitution now selects the right
cofactor at `(digit + shift) mod period` within its iterative traversal. Squaring
passes the completed right binding and its clock shift directly; it no longer
materializes a shifted right graph first. B1 normalization remains a one-time
boundary operation. Absorbing Stop outputs and false masks do not descend into
the right graph. Binding checks and temporary sorted bindings are charged, and
shortcut-returned tuple ownership remains reserved until publication.

The exact clock, absorbing traversal, scratch lifetime and B32 poison tests
passed with the repository guards: 43 tests in 43.74 seconds in
`20261004T154648Z-a3a2254ad9584de0844375060091068b`. The B32 test now forbids eager
translation after initial B1 rebases, as well as point replay and repeated
template normalization. This is focused development evidence, not full-suite
or public forest-cutover acceptance.

The Isabelle counterpart is being checked at the executable CRT-column layer.
The grouped source-binding bridge preserves exact output labels and occurrence
clock transport. Concrete packet-action/source-order certification, concrete
CRT B32 publication and global future instantiation remain distinct obligations;
the current forest route has not been removed on the strength of local Boolean
or set-level identities alone.

The expanded focused selection passed 49 tests in 44.13 seconds in
`20261004T160133Z-f57c1bbcd2f947ea90fea30187793514`. It exercises all four CRT
characters and verifies that cancellation/failure disposes the registered
composition workspace. The first follow-up quality run passed typing, source
policy, documentation, proof inventory and packaging, but found two lint
issues and one formatting issue in these edits; those were repaired and require
a fresh quality run.

That fresh quality run completed successfully in
`20261004T161421Z-68e5585d322c4e94b85fd61eec37f6f0`: strict mypy, pinned Ruff,
formatting, source policy, documentation, proof inventory and packaging all
passed. This remains dirty-tree development evidence, not commit acceptance.

The concrete source-order instance now calls the shared discovery owner directly.
It no longer constructs unconsumed candidate MDD partitions, nat-set column terms
or occurrence bindings merely to certify packet actions and ordering. The full
candidate constructor reuses the same discovery result. Representative IDs keep
their original first-seen order while using a scalar counter and one final list
reversal instead of repeated list length/append operations.

`Comma_CRT_Power` adds executable Live-row fused composition and absorbing
Stop/Invalid rows, with an explicit projection into the existing set-level square
theorem. It is not a concrete B32 instance or a global-safety certificate. The
source-fold-to-CRT publication and the global authority migration remain pending
kernel checks and concrete integration.

The final focused rerun passed 50 tests in 50.08 seconds in
`20261004T161717Z-457f2a4c9c1b4ad297cfa1f69b03ff61`, including the new
discovery-only publication regression. Independent review confirms that the
per-output CRT theorem must not become a per-label reconstruction loop in the
concrete publisher: compose each root/level once, group completed columns by
outcome, and prove table-level exactness before publishing B32. The existing
semantic Stop occurrence bridge can then consume that certified provider;
all-fork descent and unique-survivor evidence remain separate requirements.


The follow-up kernel run `20261004T164222Z-b318558ee6894964a8569bae007912be`
built `Comma_Semantic_B1` in 21 seconds under the standard four-thread,
60-second/session policy. This checks the fused shifted CRT apply, executable
row-composition refinement and source-binding bridge. The generic source-scope
proof now uses explicit cases and the shared CRT meet theorem rather than broad
case automation; the three constant lcm facts use kernel-checked computation.

The same run did not complete the concrete `Comma_Semantic_B1_Instance`:
source discovery finished in 9,172 ms, then the bulk `packet_action_check`
reached the session timeout. Thus the measured remaining failure is concrete
certificate construction, not a failed CRT composition identity. Global proof
and CLI forest removal remain blocked; this run is not full cutover acceptance.


Quality was rerun successfully in
`20261004T164941Z-d17b787538b247d0998b47d13c20591f` after the generic proof
repairs. The concrete publisher is being checked separately: it now uses the
existing memoized endpoint arithmetic kernel for local packet equations and a
restricted structural/natural-arithmetic join. Candidate source/slot values
are compared with checked equation results before publication; the final join
cannot invoke endpoint arithmetic as a fallback.


The revised publisher was kernel-tested in
`20261004T165518Z-79f6505c367141bbbdbc37a6d869056d`. Generic B1 passed again
in 21 seconds. Discovery completed in 9,222 ms, but the concrete instance
still reached its 60-second session timeout inside `local_packet_equations`;
it did not reach the structural join or shape check. The earlier concrete
comparison failure was an unreduced occurrence-shift expression, repaired with
the existing `comma_source_continuation_shift.simps` equations. No mismatch
was accepted and no proof or timeout gate was weakened. The local conversion
route is not yet performance acceptance for the full source certificate.


### Compact B1 ownership repair

The replacement B1 instance now defines a root-indexed CRT provider directly
from `comma_crt_source_recursive_rows`. Only roots below 46 are admitted;
other indices return `None`. The recursive provider follows actual Goto
children, using strict sector decrease as its well-founded measure. It no
longer requires a discovered physical-source list or a concrete packet/Goto
certificate before applying the generic refinement theorem.

The old full-action-row publisher, Goto-only certificate publisher, source-order
instance launcher, parallel scope-fold and scope-binding theories, and unused
scope-row construction/conversion are deleted. The remaining candidate
constructor retains only the template data fold; candidate data has no theorem
authority. Its serializer emits structural CRT nodes rather than expanded
phase-set expressions.

The assertion and claim mapping is:

| Removed path | Retained obligation/owner |
| --- | --- |
| Physical source-order/Goto certificate | Actual-Goto sector decrease and recursive provider exactness |
| Scope-row fold and conversion | Direct slot columns and `comma_crt_source_rows_from_exact` |
| Per-output power-column observer | `comma_crt_power_table_refines_for_targets` and `comma_crt_square_table_refines` |
| Separate partition proof | Coverage, exact fibers, distinct columns and disjointness in `comma_semantic_b1_binding_table_exact` |
| Static tests requiring retired files | Direct-provider import, source-domain and required-child checks |

A missing child cannot be inferred from exactness of present records. The
provider contract explicitly requires child lookup availability, and the
recursive constructor supplies it from the actual Goto slot. The square
contract uses `comma_orbit_word_live_bound` to require right-table exactness
only for reachable roots below 46. The concrete table adapter must return
empty rows on out-of-domain lookup. Equal finite labels never supply a missing
source occurrence.

The old action-congruence lemma now lives beside the binding-table definition,
with unchanged statement and assumptions. Recursive equations are unfolded
once where needed rather than installed as an eager simplifier expansion of
all child calls. Grouping still has a separate performance obligation:
association-list insertion can scan distinct labels, and Boolean unions can
revisit growing columns; one grouping pass is not a linear-work theorem.

Validation remains development evidence on the dirty checkout:

| Run | Result |
| --- | --- |
| `20261005T002435Z-db96f18760894a5fb81602cd145f7238` | Earlier nine structural checks passed in 0.22 s; predates the recursive replacement |
| `20261005T012105Z-d94e2c12163f4b058bc128961ef4c0fa` | Generic B1 hit the 60 s limit while the obsolete column route remained |
| `20261005T014149Z-6632738b585b471e8346e33cf99c9194` | Generic B1 still hit 60 s; theorem-handle collection took 4 ms, native-dependency audit did not finish |
| `20261005T014429Z-0c98424a5c4f4b8a8e103bb341720951` | All nine migrated structural checks passed in 0.21 s |

Profiling isolated two deferred proof stalls: grouped-column membership and
zero-shift fiber normalization. Directed induction, explicit equality transport,
and the shared `comma_semantic_b1_binding_row_exact_zero_iff` replace the broad
automation. In run `20261005T021516Z-082dffa201084412a02363580b3ba9f2`, grouped-table
exactness checked in 391 ms and the complete CRT power dependency audit in
1.074 s. The session still failed at the provider's forward reference and
terminal Exit case; it is not a session pass. Temporary repeated oracle scans
and local timing blocks have been removed, together with an unused unrestricted
power wrapper. The bounded-target power theorem remains the square owner.

Run `20261005T024008Z-f614cd13526e417b8f6b019ac4bfa55a` reached the recursive
provider in 29 seconds. All direct-provider lemmas passed, including the final
fold refinement (89 ms). Two additional broad searches over paired intersection
membership were replaced by explicit projection/intersection rewrites; the
temporary per-theorem scans were then removed. The remaining errors are the
recursive function package's relation introduction and a missing Boolean
simplification in its one-step unfolding, not concrete packet enumeration.
This run is still a failed session, not release acceptance.

The root instance now also contains direct public-B1 and `orbit_word 0` bridges,
an empty-on-invalid total row accessor, and CRT squaring refined to
`orbit_word k` for every valid root. The `k=5` corollary establishes B32
refinement without invoking a sparse publisher. Run
`20261005T025537Z-45bb52d2af12425fbe98b41485300c4d` passed the instance in
5 seconds, reusing the generic B1 heap built in 53 seconds in
`20261005T025337Z-e58d79c7608c4d2abdce8194445c7ab6`. That earlier run
passed the generic parent and then failed on two repaired instance errors;
the final run rebuilt the instance only.
The 278 candidate identifies
completed partition geometry, not a shared Goto transition. Every occurrence
must preserve its exact output binding and clock shift; no transition congruence
is inferred from the candidate count. Evaluated template publication, the
concrete B32 Stop-only certificate and global bridge still require kernel
acceptance. The old global sparse
provider and production forest admission have not been removed. No timeout,
proof-authority or output assertion was weakened, and these structural tests
do not certify the final cutover.

The current generic owner passed in 28 seconds in
`20261005T033446Z-3b9a2c57d2f2455ba72601b81bdf3b94`, including common clock-shift
transport, structural option lookup and `comma_crt_result_at_stop242`.
`comma_crt_rows_stop242` checks published result labels; it does not enumerate
924 phases. The concrete instance's Stop theorem still requires the all-root
row certificate. Its new proof-producing converter and that certificate are
not accepted by this generic-session result. The arbitrary-offset occurrence
bridge is being connected separately, preserving `p+h` at the endpoint.
The ten focused repository checks passed in 0.25 seconds in
`20261005T031302Z-c951967812d240db98e32c674634c695`.

The converter audit identified a further execution distinction: a normal
simplifier procedure runs after argument traversal, so a nested cache hit alone
does not demonstrate avoided child work. The replacement must intercept closed
structural operations before that traversal, preserve exact theorem ownership,
and measure actual work. No sparse or forest authority has been deleted on the
basis of the conditional Stop theorem or the root-zero diagnostic.

The arbitrary-offset Stop bridge passed in `Comma_Semantic_Future` in
40 seconds (51 seconds including orchestration), run
`20261005T034807Z-98a3b22638ca4eaaae20dcea3fe8d890`. It lifts B32 results for
all admitted offsets, preserves endpoint exponent `p+h`, and returns the
complete ordered child set. The unused representative-only wrapper was removed;
its broad automation had caused the preceding timeout. Its coverage is supplied
by the stronger arbitrary-offset theorem. The eleven focused structural checks
passed in 0.27 seconds in
`20261005T035108Z-94d17270bc2b4b1e806677eb073bcaeb`.

The concrete converter has not passed its instance gate. The latest attempt
reached local endpoint arithmetic but returned an incompletely normalized row
expression; constructor-shape validation rejected it. A closed equation alone
is not proof that its right side is an executable completed row table. The
all-root Stop certificate, global boundary adapter and production forest removal
remain unaccepted. These are dirty-tree development results, not release
acceptance.


### Per-root B32 publication and evaluator staging

The concrete publisher now invokes the all-root certificate. Each root is
constructed by the checked provider, its completed row labels are certified
with columns opaque, and the 46 proofs are combined by list rules. The final
aggregation normalizes only the root-index list; it does not reopen a single
proposition containing every powered computation. The exported Stop corollary
consumes that certificate. This wiring is not itself evidence that the
concrete instance meets its execution bound.

The converter audit found and repaired three independent execution defects:
missing source-shift reduction; option/action case evaluation that normalized
unselected recursive tails; and duplicate memo lookups. Closed but incomplete
row expressions are now rejected at publication. Operand staging separates
canonical algebra requests from their input syntax and leaves the powered
right-table callback lazy. Row, column and label visits are separately counted.
The option-case regression is checked before source construction, and the
existing warm-parent check remains in the concrete publisher.

The boundary/occurrence session, including the new provider boundary adapter,
passed in 35 seconds in `20261005T043324Z-b6308941d4634e0380ca167a9ca18b41`
(44 seconds including orchestration). Its final child relation uses the same
endpoint exponent `p+(h+1)` as the occurrence continuation. The 13 focused
repository checks passed in `20261005T043859Z-5186808439f04fafadec542f76c35312`.
They protect publication and dependency structure, not mathematical acceptance.

The concrete instance remains a separate red gate: after removing repeated
source-tail evaluation, `20261005T043452Z-9536830a4e284706a849eefb767709be`
still hit the 60-second session limit in CRT row combination. The all-root
Stop theorem has not been accepted, and neither global authority nor the
production forest has been switched. All runs used the standard four-thread,
6-GiB Isabelle policy; these are dirty-tree development results.

The final converter check in
`20261005T044215Z-d0233072058442bcb315ca54a74fce16` passed both executable
laziness assertions (unselected source and completed-Stop warm parent) before
timing out in the first B1 source return. Exact parent-application bindings are
retained alongside canonical algebra entries under the same cache bound;
dropping those bindings would make warm requests stage their operands again.
This run does not establish the all-root range certificate.

### Online geometry and occurrence fold

The follow-up review changed the constructor boundary: each internal source
must publish `(template, clock rebase, exact binding)` immediately after its
local slots have been folded. A Goto consumes that child occurrence and
intersects the rebased canonical geometry with its slot cylinder. Physical
source addresses remain occurrence lookups, not Boolean geometry identities.
All internal bindings must survive; retaining only the 46 root bindings would
force parents to reconstruct physical child returns.

The previous candidate did not satisfy that contract. It interned templates
during traversal but retained a full labeled MDD partition for each child and
discarded non-root bindings. Thus its template count did not establish cold
construction reuse. The replacement must separate geometry-only shift/lift
caches from exact `Live`, `Stop` and `Invalid` output bindings. Output labels
cannot be erased from application semantics merely because two geometries
share a template.

Geometry memo keys exclude output labels. Completed application memo keys
must still distinguish the exact binding and rebase: sharing a geometry does
not authorize reusing another occurrence's `Live` target or `Stop` weight.

The corresponding proof obligation is a sector-decreasing occurrence fold:
exact child occurrences and checked local slots imply an exact parent
occurrence, with canonicalization preserving its rebase and binding. The
reported 278 templates remain differential evidence, not a theorem premise.
After selecting the root occurrences, powering must use only geometry and
bindings; source constructors must not re-enter the powered layer. A fused,
support-aware row fold is useful transitional work but does not by itself
establish this cutover.

The candidate ML fold now retains all source occurrences, with geometry-only
shift and slot-lift caches. Goto reads the child occurrence's template and
binding; the old per-source physical-partition table and eager labeled-row
serialization are deleted. An independent review checked the inverse-shift
convention and binding order. It also identified a hard-coded zero-work
statistic, which was removed rather than reported as a measurement. Bounded
ML examples exercise asymmetric rebasing and different output bindings on
shared geometry. The 15 repository checks passed in 0.32 seconds in
`20261005T051052Z-dfd8e2cd16794da48f039e4f3e9c1786`; they are ownership and
wiring checks, not an accepted concrete 278-template or B32 certificate.

`Comma_Semantic_B1` then passed in 28 seconds in
`20261005T051522Z-7688facb353745b7b73e082a543ac7cb`. This includes the generic
support-aware composition lemmas and compilation/bounded examples of the
online candidate. It does not execute full candidate discovery or certify
the concrete source-to-template bindings.

The generic occurrence-fold theory was subsequently registered and checked
in `20261005T052244Z-393564759d0f44f0ba91990425160941`; the B1 session finished
in 31 seconds. It retains separate geometry, rebase and binding, rejects
malformed occurrence shapes in its invariant, and proves the local parent
step from explicit child presence/exactness and candidate-equivalence
premises. Two terminal arithmetic lemmas were moved, unchanged, into the
shared table-transform owner instead of duplicated. The concrete ML output
has not yet discharged the candidate-equivalence premise, so this theorem
does not certify the full source catalogue or replace the global provider.

The complete generic boundary occurrence bridge then passed in
`20261005T053022Z-d5b54fd7302f4841aea1c404bdfd2b4e`:
`Comma_Semantic_Future` took 40 seconds (50 seconds including orchestration).
The proof covers direct and crossing Fork/Landmine cases, unique literal
prefixes, complete child sets, and exponent transport. Repairs supplied
distinct endpoint/weight witnesses, avoided a shadowed fork binder, and reused
the canonical child-admission theorem. This is a conditional bridge from an
exact decade provider; it does not turn the unaccepted concrete B32 output
into global future authority. The production forest and fuel remain in place.

## Remaining work

Complete frozen-source quality, focused, full-unit, P0 and aggregate proof
validation. Resolve new migration failures without weakening coverage. The
global provider refinement and existing unrelated release obligations remain
blocking; no clean committed acceptance result exists for this dirty workspace.

The expanded focused regression selection passed **16 tests in 0.33s**
(`results/runs/20261005T053140Z-d8dedefc6d63428db8c77ed5867f2a72/unit.log`).
The compact certificate interface now separates one template-geometry list
from source-indexed `(template index, rebase, binding)` descriptors; resolving
a descriptor explicitly rejects an out-of-range template index. This is
representation safety, not evidence that the concrete candidate is exact.

The next integration removed a hidden eager check: occurrence wellformedness
was a quantified specification over the clock. Its executable checker now
uses structural column admission, support, pairwise disjointness and union
equivalence to True. A single sector-decreasing induction establishes exact
published occurrences from local validity and child closure; it does not
retain a proof object per source. The serializer also publishes checked
root-to-occurrence indices without adding root addresses to template IDs.

Validation found and repaired an ML range-expression precedence error, two
local proof rewrites, and a broad image-set witness search. The latter hit
the unchanged 60-second session limit. Replacing it with an explicit image
rewrite and witness extraction restored a **34-second** B1 build in
`20261005T055442Z-bb28e3692dca4a54a1c03b1302d9ebff` (44 seconds with orchestration).
This checks the compact serializer and generic structural shape/occurrence
proofs. The slot-checker-to-candidate-match theorem and the concrete
catalogue/B32 publication remain separate obligations. No production forest
or fuel authority has been removed on this evidence.

The local structural-check soundness theorem is now complete and registered:
`comma_semantic_b1_crt_occurrence_structural_check_matches` selects the
containing parent/child columns, proves the corresponding shifted
intersection is supported, and uses its binding guard. It covers terminal
and Goto cases without enumerating clock phases. Its dependency audit, the
structural shape checker, and the map induction all pass the native-proof
check. Parent/slot geometry is computed outside the child-pair loop. An
unused support wrapper was deleted, and the candidate no longer requires
the emergent 430-source census as an admission condition.

The final checked proof run is
`20261005T060445Z-5d5edcc379ad4fb18f6809af256bf077`: **B1 29 seconds; semantic
future/boundary 47 seconds**, each under the unchanged 60-second, 6-GiB,
four-thread policy. Total dependency-aware orchestration took 87 seconds;
that is not a larger per-session allowance. These are dirty-development
results, not clean-commit acceptance.

The concrete release gate remains open: serialize and certify the candidate
occurrence catalogue, publish all B32 Stop bounds from that owner, then bind
the exact provider into global future/earliest-path authority. The old
physical-row instance has not been rerun or silently treated as passing.
Neither a freshly measured 278-template census nor end-to-end CLI speedup is
claimed by these generic proof results; production forest/fuel deletion still
requires that concrete gate.

Final focused regressions: **17 passed in 0.45s**, recorded in
`20261005T060656Z-f9055cdf6dfa46718e3aa5873300f734`. They include an explicit
guard against reintroducing quantified wellformedness into the executable
checker. The new proof files contain no skipped proofs or new axioms; each
modified source remains below the 1,000-line limit. Whole-tree quality, full
units, concrete B32 and installed CLI acceptance were not run in this slice.
