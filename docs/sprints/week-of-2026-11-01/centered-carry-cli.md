# Centered carry actions and finite CLI repair

Period: 2026-11-01 through 2026-11-07 (Sunday–Saturday).

[Week index](README.md)

## Objective

Integrate the November 3 centered-harmonic, Center11 and finite cold-CLI repairs
from a clean baseline at Git `2994b2841317fd141cd7913142c53f38685838a7`.
Downloaded measurements and archive bypasses are not acceptance evidence.
Current results below describe this working tree, not a committed release.

## Changes

### November 7 issuer-owned continuation

The follow-up retains the same dirty Git baseline and the existing query,
scheduler and ledger owners. The new archive reports are integration inputs,
not acceptance evidence. In particular, a seed-196 low-band period cannot
authorize a full-numeral period or bypass source-binding validation.

CLI metadata no longer imports the resource ledger, reverse/add extent owner
or decimal renderer through annotation-only dependencies. Help and family
listing now have explicit cold-import regressions. The focused rendering and
stream-lifecycle selection passes 99 tests
(`20261107T064824Z-fb38f2465ad5498f8baf9d2e8905b2f3`), with strict mypy,
Pyright, Ruff and formatting passing for the changed files.

Antihydra registration uses typed owner entry points and exact runtime type
checks before accessing stores. Projection audit callbacks load on audit
demand; the ordinary source owner remains registered. The focused audit,
fragment, failed-refresh and CLI selection passes
(`20261107T065831Z-067d540d567b48c69e1003755f982bb0`), including forged
module/class-name and registry-reset cases. Its changed files pass strict
mypy and Pyright.

Fresh five-trial Antihydra baselines cover 0, 16–1,024 and 3,072/3,073;
Collatz seed 27 covers 16–1,024. Both include cold processes, warm requests and
actual cache bypass. Antihydra output agreement passes after registration
changes, but the two follow-up runs vary: the 3,072 cold median is 176.81 ms
then 142.36 ms against a 160.69 ms baseline. This does not yet establish a
repeatable CLI improvement. The corresponding runs are
`20261107T064325Z-f2c7f401ec2e498b8e1117030058c138`,
`20261107T065843Z-7633650466e84e2c97307ba432ad09ce` and
`20261107T070138Z-b00a948094074171b5061dd53343ca50`.

The November 7 nonuniform-SLP audit found a remaining production dispatch bug:
only T2/T4 requests and repeat counts of at least 16 reached the compressed
projector. All admitted horizons now preserve nonuniform repeats with counts
greater than one. The coefficient decoder no longer has a copy-by-copy
`REPEAT_REST` branch. The DAG admission scan reserves scratch before allocation,
counts visited nodes and clears its buffers on exceptions. Source issuance,
width bounds and rollback cache invalidation remain unchanged.

The focused regression selection passes
`20261107T072748Z-11a6b550052c41c4830537307da9d550`: it compares literal
outputs through 64 ticks, poisons run expansion for small repeat counts,
projects a trillion-copy grammar through 16 ticks, and checks failed-action
rollback and recovery. This avoids spatial expansion; physical ticks are still
executed individually. It is not evidence of logarithmic arbitrary-source
reverse/add time.

The Collatz follow-up public benchmark passes output agreement at all unchanged
16–1,024 horizons (`20261107T072814Z-77d97189d17c407497525a790430d0c1`).
Cold medians at 16 and 1,024 are 247.71 and 266.06 ms, versus baseline 266.52
and 261.08 ms. The mixed result does not establish an overall CLI speedup.
A fresh-process regression poisons the optional innovation-Moore module and
still obtains the independent seed-27/index-16 result 121. This confirms lazy
observer construction, separately from latency.

The parity-tape consumer now computes one affine action during named-macro
admission and streams requested prefix letters through an ordered worklist.
Prefix action folds also share one request-local memo across overlapping
grammar chunks; all chunks remain alive until that memo is cleared. No
per-node persistent coefficient cache or unaccounted balanced grammar was
imported from the download.
Nested-repeat and partial-prefix comparisons, a deep-grammar visit bound,
second-fold poisoning and retained-exception cleanup pass
(`20261107T073338Z-82f0c7ad034d440b8fdb975ebebc5eda`). Strict mypy and
Pyright pass all 11 files in the combined SLP/CLI follow-up batch.

The broader reverse/add punctured selection also passes
`20261107T073043Z-cdaf3babefc847ca877d247a6b60af0f`. The unchanged five-trial
public workloads at 16–1,024 pass cold/warm/bypassed output agreement
(`20261107T073758Z-fda87487283946749b2b054121e00e09`). At 1,024 the medians
are 253.40/17.80/17.87 ms; this is current-route evidence without a matched
baseline, not a demonstrated end-to-end speedup.

The shared projector audit also found that two consumers could bind the same
empty memo stores and later collide on arena-local integer keys. Binding now
claims the stores atomically for one consumer, checks their ledger and backing
identities, and retains that claim through clearing and disposal. Both reverse
owners use the same audit contract. A failed multi-store clear attempts every
store and quarantines the projector until a successful retry; it cannot return
a stale node after arena rollback. The focused ownership, punctured-output and
publication-lifecycle selection passes
`20261107T080719Z-3abb8605a12f4fea8c070f8d61d3717d`.
The claim also checks the exact consumer through a weak reference, rejecting
copied binding tokens without retaining a discarded projector. The provider
audit preserves its separate requirement that ordinary comma memos remain
unclaimed. The combined ownership, lifecycle and bounded-helper selection
passes 89 tests (`20261107T082026Z-177b4b4445584032a2b3c4761ec822d6`);
the provider/boundary follow-up passes 31 tests
(`20261107T083011Z-0debf1d5e0f94b93aa32b02bdc539ed3`).
The follow-up audit found another stale-hit route: retargeting a populated
projector's machine or arena. Operations and ownership audits now compare
those identities with the constructor's bindings, including after a cache
clear. Machine/arena substitution, shared-prefix reuse and exception cleanup
pass the 17-test selection
`20261107T094525Z-70a0aca5f7934ea1b9795c67b8ddc7a8`.
Arena node-ID invalidation now also advances a generation before destructive
rollback or disposal. A projector rejects that generation until all cache
stores clear successfully, and a clear cannot revive a disposed arena.
Historical ownership audits still recognize fully disposed, empty bindings.
The expanded 82-test selection passes
`20261107T100628Z-d23a3904bd284851afb9531f150d9ef9`, including partial rollback,
no-op rollback, node-ID reuse and failed-clear recovery.
The signed-carry summary owner now pins the same source arena, root and node-ID
generation, rejecting summary reads after disposal or rollback. SLP node cleanup
uses the shared accounted-store helper, including pending releases when a
mutation callback fails after deletion or ledger release fails before/after
commit. The 29-test follow-up passes in
`20261107T104531Z-26caedb5b2704db38e4943f2ff17fea3`. No separate cleanup owner
or persistent source fingerprint was introduced.

The seed-196 low-four-digit source refinement and its required width bound are
kernel-checked in `20261107T111911Z-992b2bebb8bc4547a57f91891edf9d5e`.
The existing `Double_Reverse_Temporal_Refinement` session rebuilds in 122.718
native seconds, including 7.320 seconds for the source-induction theory.
Finite guard cases use terminating decimal-mask equations. One native oracle
audit covers each exported bundle; a second `has_skip_proof` traversal was
redundant because an empty `all_oracles` result already excludes skip proofs.
The digit consumer uses this bounded projection only for admitted even
generations, the first four digits, and the existing conservative bit bound.
It validates source bindings and reserves scratch before work. Source digit
metadata is part of the authenticated snapshot, so mutation cannot weaken that
bit bound. Other demands retain the exact existing route.

The matched five-trial baseline is
`20261107T104935Z-5f463fdcc8e241258d0275ceafdb61e4`; replacements are
`20261107T112900Z-5c280362eb044294b835128a1130a51d` and
`20261107T112956Z-24fbec4e33334216b5eb534646836be1`. All agree on outputs.
At 1,024 physical steps, cold public point requests (including projection
construction, excluding interpreter startup) fall from 8.423 ms to
0.886/0.868 ms. Genuine bypass falls from 8.104 ms to 0.411/0.410 ms; warm
requests fall from 0.125 ms to 0.049/0.050 ms. Endpoint/stencil poisoning
establishes the avoided construction independently of timing. Full-value CLI
medians are 187.875 ms before and 183.455/184.114 ms afterward; this small
difference does not establish a full-value CLI acceleration.

The final focused runtime selection passes 71 tests in
`20261107T112851Z-200e404e050a440ab163202c74d7278d`. It includes reservation
transfer failures before and after commit, failed interner publication and
cleanup, subsequent node-ID reuse, and low-band source-metadata tampering.
The signed-carry demand checks preserve signed-minus-one behavior and source
authority. The later verifier repair below replaces prefix reconstruction
with a fresh grammar-summary audit and ordered carry recurrence.

The follow-up Collatz audit found that conditional memo seals omitted the
joined parity tape. A changed tape could therefore survive a same-source hit
and reach a prefix consumer. Seals now pin the admitted nodes and their exact
word/child tuples, check the tape's action at admission, and validate those
bounded records on hits without following replaced topology or refolding the
action. Memo candidates reject unissued fallback grammar selectors. Snapshot
storage is reserved before sealing and transferred through the existing
`OwnedMemo.adopt_reserved` path; failed publication clears only the newly
created seal. Existing malformed-cache error behavior is preserved.

The 66-test conditional scheduler, lifecycle, guarded-join and parity-tape
selection passes in `20261107T122107Z-263547cacc06472ab097ce581acc1d3d`.
This includes warm-fold poisoning, Boolean digit substitution, child cycles,
root replacement, source/phase mutation, budget refusal and failed adoption.
The four-file strict Pyright/mypy checks pass. Whole-tree mypy still checks
2,453 sources, and Ruff/formatting pass in `results/nov7-runtime-whole-*-v3`.
The full-suite checkpoint below includes this cache repair and the native
candidate importer tests.

The concrete proof constructor now certifies states postorder, discards
cofactor memo tables after each semantic root, and exports universal root
certificates. Goto consumes the child source binding already admitted by the
compiler. The old environment-indexed action table, pointwise reconstruction
cache and duplicate source normalization are removed. Publication releases
per-node scratch immediately, and the shallow consumer reads the publisher's
named definition instead of retaining or reconstructing another copy.

Native run `20261107T135354Z-3635e2710cf649858bc996c36d6a0a17` passes generic B1
and certificate smoke, with 110.930 seconds aggregate guarded time and
3,053,658,488 sampled peak bytes; descendant cleanup is confirmed. Generic B1
rebuilt in 79.370 native seconds. The smoke fixtures certify real Terminal,
three-phase sector-9 Entry Branch, and Near-to-Entry Goto actions, alongside
publication rollback and stale committed/aborted handle rejection.

The repaired consumers transport the checked local action through its proved
period, eliminate the selected-output existential explicitly, and consume
checked finite-range and slot-coverage equations. They no longer reopen ranges
with `upt_rec` or named roots with broad definition unfolding. Period-one
sources avoid CRT-axis proof construction after guard validation. The shared
rewrite filter rejects reflexive quantified/conditional equations, and Goto
consumes source equality without rebuilding a rank-equality theorem.

The obsolete malformed-bind assertion required data-node growth from the
removed reconstruction path. Its replacement requires unchanged node/scratch
counts, zero published binds after rejection, and a successful closed-theorem
retry without new data nodes. A separate fixture retains the post-allocation
failure contract by aborting after a real named definition and reservation
transfer. These changes preserve the authority checks rather than replacing
failed proof work with acceptance.

Concrete B1 remains a failed gate. Its constructor now applies the checked
child and guard implications with fixed `spec`, `mp` and conjunction rules,
without conditional rewriting or general proof search. Shallow proof caches
use nested root reservations and discard intermediate cache handles on scope
exit; final source/root records and publisher definitions retain their own
authority. Native smoke covers nested restoration, sibling rebuilding,
foreign/stale tokens and failure cleanup in the unchanged arena limits.

Generic B1 rebuilt in 84.178 native seconds in
`20261107T150743Z-14468bfc74a843c89ab99b3d462346e6`; the final scope smoke
passes in 12.817 seconds in
`20261107T151639Z-3cd7814f9718498ab53371a1317c7d96`. That full profiled
constructor still times out at the 300-second session limit, with 2,450,841,472
sampled peak bytes. The same source without optional tracing also times out:
`20261107T152200Z-c4f617a9bf014493992eb8cf97c789c5`, peak 2,293,784,496 bytes.
Both confirm descendant cleanup. The latter includes a one-second OS stack
sample; generated ML functions were unresolved, so it supplies no named
hotspot attribution. Neither run establishes complete arena sufficiency or
B1/B32/global acceptance. Temporary native sampling is diagnostic work only. Both the OS stack sample
and Poly/ML sampler returned unresolved generated-function names; neither
establishes the dominant proof cost. The temporary sampler wrapper was removed
after confirming descendant cleanup.

The subsequent coarse-stage diagnostic
`20261107T153807Z-f05e1eac176347638d1d51ace12d1a80` also reaches the session
deadline. Its 1,144 completed states account for 72.562 seconds in publication
and 161.178 seconds in local proofs. Receiving-context setup, named lookup and
final checks round to zero milliseconds in those records. The temporary probe
was removed. This measurement includes partial construction, not a successful
B1 result.

The repair moves the already-existing immutable arithmetic simplifier database
to the shared CRT transport owner and reuses it throughout the compiler,
shallow proofs and rank consumers. Per-proof source facts still enter only the
receiving context. The clock-proof timer now includes rule setup. Each active
semantic-root scope also constructs its source guard/period bundle once and
revalidates the exact source, key, binding and receiving context on reuse;
nested roots use separate reservations. This removes duplicate proof setup,
but does not yet replace the transient cofactor proof contract with the full
symbolic future-action contract.

The source-certificate contract now carries full weighted application through
Shallow, StateCertificate and ProgramCertificate. The concrete rank consumer
projects the output label only after checking that application theorem. The
local zero edge weight remains distinct from the physical writer clock.
The shared cofactor and branch-cover lemmas preserve both label and weight;
nonzero edges cannot pass a label-only comparison.

The old synthetic selector/bind equation was unused by production consumers.
It and its private payload-only helper lemmas have been deleted. Branch
certification now publishes only the selected-child application facts its
consumer requires. This removes proof construction, not just retained data.

The cache audit rejects expired reservations before Shallow cache hits and
before StateCertificate can publish a node. Expired scopes can still be closed
without leaking scratch or proof entries. Native fixtures cover wrong
partitions, nonzero weights, warmed expired caches, changed-source proof
bundles and failed publication.

The current transport uses the existing selector/branch laws rather than the
removed recursive pair walk. Scoped selectors avoid interning a raw parent
solely to prove normalization. First-port admissibility combines already
checked row facts in a restricted simplifier. Collapsed rows use bounded
replicate-spine conversions with opaque payloads.

Real `Local_Theory.define` fixtures exposed name/body mismatches that the older
literal fixtures missed. One shared helper now transports only exact issued
one-node definitions, checking both endpoints, closure, type, receiving theory
and absence of oracles. Lower-axis results retain their published child names
through parent composition; equal-row collapse proves its opaque-name result
before exact definition transport. The resolver contains input roots and actual
selected pieces, without eagerly checking all unselected children. Fixtures
cover mixed CRT axes, equal-row collapse, wrong partitions, cold normalized
parent reuse and warm completed-action reuse.

Latest native acceptance on the dirty development tree based on Git
`2994b2841317fd141cd7913142c53f38685838a7`:

| Gate | Result | Evidence |
| --- | --- | --- |
| Generic B1 | PASS, 82.429 seconds, four threads | `20261107T201229Z-9b27d534bddd4aaf89a55de9388e0536` |
| Certificate smoke, including published names | PASS, 13.088 seconds | Same run; guard 115.827 seconds, peak 3,008,930,216 bytes, cleanup confirmed |
| Graph prerequisite | PASS, rebuilt in 145.980 seconds | `20261107T201431Z-5c534622a03e4405a2477aae702fa1d4` |
| Concrete B1 | FAIL, native 300-second session timeout | Same run; dependency build 472.537 seconds, peak 2,371,067,800 bytes, cleanup confirmed |
| B32/global, artifact admission and CLI retirement | NOT ACCEPTED | Concrete B1 remains a prerequisite |

The last completed constructor checkpoint has 128 visited sources, 120 completed
programs, 1,280 transient states and peak arena occupancy 2,528 (limit 8,192).
Its cumulative branch-certification time is 128.678 seconds; local-action
conversion is 43.155 seconds, Goto certification 30.954 seconds and terminal
certification 8.368 seconds. These are partial measurements before timeout,
not a completed benchmark or a claimed CLI speedup. The accepted name fixes
remove correctness defects but do not remove per-environment proof production.

The architectural review distinguishes the surviving work precisely: the
per-program environment memo is transient, and completed root proofs are keyed
by program, but every transient state still invokes `certify_state`. The
universal source-action constructor/refinement required to replace that proof
recursion is not implemented. A data-only environment table or renamed cache
would not satisfy the quotient-first contract.

The semantic B32 summary now uses the checked semantic stopping theorem
directly. The new Future rank-B1 adapter maps the checked source DAG's leaf
alphabet and transports its symbolic B32 power into crossing consumers. It
replaces the graph-power weighted-stop adapter and fixes an undeclared initial
NF refinement reference. This downstream migration is not kernel-accepted yet.
The initial-source ML producer still consumes the legacy graph-authenticated
NF actions, and the source compiler still constructs transient phase-environment
proofs. Neither has become the plan's universal successor-closed action
certificate. Physical writer weights remain distinct from local zero weights
and encoded stopping heights. No global artifact is admitted, and the
forest/fuel cutover remains disabled.

The repository contract test now checks the semantic stopping lemma's parsed
body for its checked semantic B32 authority, replacing the old assertion that
required the redundant graph stopping theorem. Its executable graph-adapter
and writer-contract assertions remain. The focused producer/dependency
selection passes all 20 tests in
`20261107T202246Z-6f3bfa0d9eb94b9c8bb76e642327199d`.

The downstream audit also corrected an extra `nat` argument in
`comma_semantic_future_action_of_weighted_stop`; its declaration now agrees
with its three-argument definition and callers. That downstream theory has
not been kernel-accepted in this wave.

The downstream import audit found no ROOT-only unused theory among the 34
Future-session registrations. The old predecessor setup still publishes
action-vector refinements, lengths and shapes used by the provider proof;
removing only its named stop theorem would not remove those dependencies.
Native candidate export is now attached after the release theorem audit and
checks receiving-theory ownership. Its Python importer passes 44 tests in
`20261107T125536Z-f207065f41084baeb1240922fd3dac2b`, including malformed and
noncanonical input rejection. No exported artifact has been admitted: the
native B1/B32/global chain must finish first.

The audit also retains two distinct performance holds. The optional Collatz
successor-partition API revalidates the same parity grammar for narrowed source
children; source search found no internal production caller of that partition.
`GuardedPortJoin.then()` has the same cumulative-fold issue but no current
repository call site. Neither establishes a default-CLI slowdown by itself.
The wide signed-carry constructor still retains full weighted summaries per
node. Its verifier now freshly checks each reachable grammar summary once,
then streams the carry recurrence and verifies the signed seam. It no longer
reconstructs a growing prefix for every boundary. Exact row membership,
integer-key types, source generation, sign, budgets and stored seam fields
remain checked; a cached result does not replace a fresh audit. Demanded
packets compute each requested prefix only once.

The signed birth-window API now consumes those packets instead of separately
querying every carry and then querying it again through `digit_at`. It reads
one prefix per requested position plus the final boundary. The expanded
42-test selection passes in
`20261107T155327Z-71f418e48efa4e18bad08da87184045c` (0.76 seconds), including
an exact-output comparison and duplicate-prefix poisoning. Neither ordinary
Fermat nor Mersenne CLI construction currently supplies this signed-fold
source, so this is a bounded API improvement only.

The 41-test carry/Fermat-integral-ideal/signed-halo selection passes in
`20261107T151232Z-fab1a105cdfd4e368e4c64b6ddd4d360` (1.13 seconds). It retains
independent cyclic, negacyclic and signed-minus-one fixtures, poisons prefix
replay during verification, and rejects missing, extra, aliased or corrupted
summary rows, including forged Boolean fields inside frozen blocks. The old test that injected a boundary by replacing `carry_at`
was tied to the removed implementation; summary/seam tampering and independent
literal boundary comparisons retain its mathematical contract. An 8,192-cell
repeated grammar bounds verification's weighted compositions by the repeat
exponent's bit length. This establishes avoided prefix work, not linear total
integer cost or an ordinary CLI speedup. Changed-file strict Pyright and
whole-tree mypy/Ruff pass; the full-suite checkpoint below includes the final verifier and forged-field
regressions.

The archived `mahler_seed_moore.py` evaluator is absent from the current tree;
its timing claims do not describe the current CLI. The bounded direct
`MahlerJointFutureAction.from_source_prefix` API did have a growing left fold.
It now uses the existing shared `balanced_fold` over the same source-selected
adjacent runs, preserving admission before composition and the final exact
endpoint check. It does not infer a repeated motif or change the 4,096-step
bound. The 24-test owner selection passes in
`20261107T134034Z-50754a14463b4d24a984506abbf8562d` (1.02 seconds), including
complete coefficient/guard/safety equivalence, first-refusal behavior and
reduced aggregate operand-width work. The single-zero-run assertion now
requires zero compositions and the same exact action, replacing the old
one-composition assertion with a stronger avoided-work contract. Changed-file
strict mypy/Pyright pass. This direct fallback still lacks a composition ledger
hook; no new cache was added. The normal workspace-backed associated-action
path already avoids this fold, so no CLI acceleration is claimed. The full
suite checkpoint below includes this reassociation and the final carry-demand
and independent Collatz fixture changes.

Standalone SLP storage now uses a guarded sequence rather than a list subclass,
so built-in list descriptors cannot bypass mutation invalidation. Destructive
edits poison the canonical interners and invalidate consumers; append-only
growth preserves existing IDs. Projectors and signed-carry consumers pin the
exact store and generation. Copying or serializing arena authority is rejected.
Explicit standalone reinitialization installs fresh storage and advances the
generation; ledger-owned storage must use its owner's lifecycle protocol.
The focused reset/cache selection passes 55 tests, and the full suite below
includes the additional generation regression. Generic bimachine protocols
now live with the transducer owner rather than as private SLP-only contracts.

Fresh five-trial 16–1,024 public workloads agree across cold, warm and genuine
cache-bypassed modes for reverse/add seed 196 and Collatz seed 27:
`20261107T171636Z-2f5a379ffc9648cfb8cfe0c8dda2798a` and
`20261107T171710Z-81bcd3a87b9e41659452d1a642599006`. At index 1,024, decimal
CLI medians are 274.19/18.94/18.91 ms for reverse/add and
262.18/3.79/3.64 ms for Collatz. The earlier reverse measurement was
253.40/17.80/17.87 ms; the Collatz comparison was 261.97/3.68/3.78 ms.
These measurements do not demonstrate an ordinary-CLI speedup. The proven
avoided-work claim is compressed nonuniform spatial projection, not arbitrary
physical temporal powering; the intervening repairs prevent attributing all
latency variation to one change.

Whole-tree development gates:

| Gate | Development result |
| --- | --- |
| Default units | 12,199 passed; six preserved comma CLI failures; 711 validation deselections |
| Suite resources | 215.973 seconds guarded, 443,696,496 sampled peak bytes, cleanup confirmed |
| Strict typing | Whole-tree mypy: 2,456 sources; prior 99-batch Pyright sweep plus all subsequent changed-file batches: zero findings |
| Source checks | Ruff, formatting, source policy, documentation and proof registration pass |
| Reverse/add and Collatz P0 | 43 passed in the fresh follow-up selection |
| Installed wheel | Built, but acceptance rejects the missing admitted comma future artifact |
| Concrete comma cutover | Not accepted; no global CLI artifact published |

The current unit run is `20261107T171251Z-c79274c12ebc400aac680ae4b136a696`
(213.71 seconds inside pytest). Collection takes 12.712 seconds; setup, calls
and teardown total 2.254, 191.226 and 0.653 seconds respectively. The slowest
individual test, including fixtures, takes 3.617 seconds. The timing journal
is complete. This passes the timing budget but remains a failed correctness
gate because the six positive Comma CLI assertions require a native global
artifact. No workload, assertion threshold, validation tier or deadline was
weakened. These are dirty development results, not commit acceptance.

Whole-tree mypy and formatting pass in
`results/nov7-storage-complete-{mypy,format}.json`; Ruff and source policy pass
in `results/nov7-storage-final-{ruff,policy}.json`. The final 11-file strict
Pyright batch reports zero diagnostics in
`results/nov7-storage-final-pyright2.json`. Proof registration passes with
139 sessions and 491 theories in `results/nov7-storage-final-proof-index.json`.
The fresh wheel builds, but installed acceptance still fails for the absent
Comma global artifact (`results/nov7-storage-final-package.json`).

Colima acceptance remains unavailable: the installed runtime is stopped and
Docker has no `colima` context (`results/nov7-colima-status.json` and
`results/nov7-colima-inventory.json`). No Linux result is inferred from the
native macOS runs.

The refreshed seed-27 Collatz public benchmark preserves the five-trial
16–1,024 workloads in cold, warm and bypass modes:
`20261107T133009Z-577f22b7ca3e49089c0b345492591bd3`. It passes route/output
agreement in 19.823 guarded seconds with cleanup confirmed. Position zero is
used because later terminal-cycle values have no digit at position two; the
earlier position-two attempt correctly raised `IndexError` and is not counted
as a passing measurement. This refresh supplies no baseline-relative speedup
or new temporal-complexity claim.
The fresh 43-test reverse/add and Collatz P0 run is
`20261107T134611Z-ec2ce17f2c7a4890bf3dbad3ca20ba80` (1.53 seconds).
This does not certify the separate prime/non-halting P0 obligations.

### November 6 branch reconciliation

The default-suite checkpoint for this earlier stage is
`20261107T053512Z-b226e8a01c364ae49b56cf1cccd49762`: **12,065 passed, six
preserved comma CLI failures, 711 validation deselections**, in 231.41 seconds.
The guarded command takes 234.14 seconds, peaks at 453,018,512 bytes and confirms
cleanup. Collection takes 14.153 seconds. This meets the runtime budget but is
a failed correctness gate because no global comma artifact is admitted.
No test limits, assertion thresholds, workloads or tiers were relaxed.

The final lifecycle audit clears projector task/value/orbit buffers and packed
publisher digits before releasing scratch, even when an exception retains their
frames. It also clears both balanced-concatenation work rows. The unused private
`_repeat_action` compatibility implementation had no production callers and was
removed; its new private-only test was removed with it. Live action cleanup is
checked through `forward()`, while the independent repeated-word projection
fixtures retain the chronological, partial-exit and large compressed-word
contracts. No runtime interface or recurrence semantics changed.

The downloaded Collatz eight-symbol table was tested in the current source
issuer before acceptance. A five-trial guarded comparison with the committed
scalar issuer found a cold regression: a 512-symbol field request took about
1.11 ms versus 0.64 ms, while a short field request took 0.70 ms versus 0.043 ms.
Warm field lookup improved, but endpoint-only lookup remained slower. The
process-owned table attempt is therefore removed from production rather than
reported as a CLI speedup. This comparison is a source-constructor profile,
not an end-to-end CLI benchmark (`results/nov7-collatz-source-profile.json` and
its output log).

The independent repeated-skew grammar repair remains: it verifies one powered
issued action and preserves `(AB)^q` in chronological order instead of
validating and appending the same action `q` times. Its direct regression checks
the ordered output, one endpoint evaluation, forged guard rejection and ledger
cleanup. The archive's Antihydra compiler is connected to its issued-carry producer,
but its reported large cold CLI win comes from a separate scalar adapter that
bypasses query context, ledger ownership and carry issuance. That adapter is not
ported. Its global eight-bit table also outlives the temporary reservation and
has no reset/accounting owner. The existing source-sealed ×15 morphism and
Laurent projection remain authoritative. A safe, measured substitution inside
`IssuedWeightedCarry` is still outstanding; no new Antihydra CLI speedup is
claimed from this reconciliation.

After removing the slower Collatz table, the five-trial public harness passes
seed 27 at horizons 16–1,024 in cold, warm and genuine cache-bypassed modes
(`20261107T054147Z-c49294ae6c9c415dbf517ddfae3ed653`). It uses digit position
zero so terminal-cycle point requests remain valid. At 1,024, CLI medians are
251.63/2.40/2.44 ms respectively. This records current route/output agreement;
there is no matched end-to-end baseline establishing a Collatz speedup here.

The later November 6 branch repair reconnects nonuniform spatial repeats to
the existing Q19 projector for bounded T2/T4 actions. The production publisher
retains its source issuance, width checks and transaction. Failed publication
clears the projector's caches before rolled-back node IDs can be reused; the
shared projector owns that cleanup operation. Existing native block limits
remain 1,024 physical ticks and width 20,000. No archive-only admission widening
or alternate scheduler was imported.

The packed double-reverse consumer now builds one charged byte buffer before
integer conversion and uses four decimal Boolean predicates instead of eight
digit-equality masks. Odd-width packing preserves the leading nibble; failure
paths clear the buffer even when a traceback retains its frame. These are exact
bounded source-window optimizations, not moving-cut period authority.

The focused repeat/packed tests pass (41 tests,
`20261107T041650Z-16e2afd607164f2a9af350695dfd202c`); the complete two-family
selection passes 1,859 tests in 62.69 seconds
(`20261107T042032Z-d5633a306ec84094b106655a71481e5c`). The reverse source-image,
generic-range and temporal-publisher P0 selection passes 36 tests
(`20261107T042420Z-c3b3ff8581104de69581480ba45cbbf4`).

The existing five-trial public-query comparison at seed 196, horizons
16 through 1,024, passes in
`20261107T041937Z-a8e84f87ccc64e329a2303d50acee6ad`. Against the preceding
November 6 run, these small ordinary queries are essentially unchanged:
at 1,024, cold/warm/bypassed medians are 95.85/13.66/17.86 ms versus
93.73/13.60/17.75 ms. No general CLI speedup is claimed from these results.
The unchanged workloads are retained; larger packed-cone performance requires
its own evidence. The registered `Double_Reverse_Temporal_Refinement` session
passes in `20261107T043058Z-3427536cbdf849a6954834990666139c` (105 seconds
reported, 98.386 seconds native execution). The new Boolean theory takes
1.221 cumulative seconds. It proves the admitted decimal-lane expressions and
their packed source-plane meaning against the existing equality-mask semantics.
This is finite arithmetic refinement, not extraction of Python allocation or
handle authentication.

The November 6 continuation selectively ports the November 5 reports into
the existing shared owners. `BimachineSLPProjector` now emits a repeated
block from the two finite context orbits: prefix, paired cycle, remainder,
and suffix. It no longer visits every copy of a nonuniform repeated word.
The same projector is consumed by reverse/add and double-reverse. Its tests
include a trillion-copy compressed word and partial-DFA exits immediately
before and after the last demanded copy.

The shared Pascal moment owner uses bounded Lucas coefficients modulo eleven
and reduces spatial repeat counts by the moment period. It retains exact
length and both endpoint markers, including nonempty zero-moment repeats.
Other coefficient moduli keep the existing exact path. This does not issue
temporal repetition authority; the current Isabelle finite-word theory still
covers only orders zero and one, so arbitrary-order kernel refinement remains
open. No archive band class or second family-specific moment implementation
was restored.

Carry suffix bootstrap now uses the actual number of no-growth steps rather
than requiring the whole fixed history window. Shape checks and the shared
Horner fold do not authenticate a source history. Insufficient erasure,
nonbinary carries, Boolean coercions and inconsistent widths are rejected.
The reverse/add punctured producer reserves from the normalized output width;
its horizon and width admission bounds are unchanged.

`Reverse_Growth_Admission` passes with the concrete carry-suffix refinement in
`20261106T085023Z-6a147c49ed79495a8863dd64697acd9b`: 15 seconds reported and
11.304 seconds native session execution. The proof connects the actual
punctured T2 producer to the quiet/growth carry formulas, chronological Horner
composition and mod-32 erasure after five actual quiet steps. Canonical Q19
coefficient bounds then recover the exact endpoint coefficient. Width births
use `1+z`, so five arbitrary chronological rows are not sufficient. This is a
source-generated finite-run theorem, not admission of a fabricated carry tape.

The guarded shared/reverse selection passes 212 tests in
`20261106T074034Z-b20ecfbd5f4f4de1bf49800a87ce359c`.
The existing five-trial public-query harness completes seed-196 `2rev10`
workloads at 16 through 1,024 in cold, warm and cache-bypassed modes:
`20261106T074332Z-833150d2bd664ee3b67df1bd56ea7c5e`.
This establishes current output agreement across those routes, not a
before/after CLI speedup. A separate five-trial shared-kernel comparison against
Git HEAD projects 1,024 repeated blocks in a median 0.072 ms versus 1.17 ms,
with identical output (`results/nov6-slp-kernel-comparison.log`). Source
construction and rendering are excluded from this measurement.

The Collatz carry view delegates authority to its issued source window and
reads the existing endpoint without replaying the action. It remains an
explicit selector input: a proposed default handoff merely moved the same
numerator calculation and introduced redundant admission, so that path was
removed. The Antihydra carry result is a demanded observation snapshot,
computed once after source validation and scratch reservation; it is not a
new certificate issuer. Source mutation is rejected before another projection
is published. Existing snapshots have no execution authority.
The focused radial/SLP/public-Collatz selection passes 86 tests in
`20261106T083236Z-ad225fcb07af41e79fbb16ffaf556e81`. The changed radial, shared
SLP/carry and Pascal files pass focused strict mypy and Pyright checks.

The shared power helper replaces duplicate Collatz carry-program and reverse
Center11 power loops. Independent literal Pascal checks cross the reduced
period boundary, including order eleven. The final focused follow-up passes
103 tests. Whole-tree strict mypy and Ruff pass; the changed nine-file Pyright
batch has zero diagnostics, and whole-tree formatting passes.
Source-policy and documentation checks pass. The source-policy duplicate
finding was resolved by the shared power helper, without changing its rules.

The reverse/add integration consumes the existing native physical stream for
bounded Laurent projections and adds a separately demanded centered carry
action over the same Q19 normalization laws. The archive's retained cochain
history is omitted: the new observer retains current native decimal buffers and one
fixed-size matrix, with scratch reserved before source expansion. Its central
coefficient and incoming carry come from that same physical source stream.
This is bounded observation work, not reuse of a published successor path.
The 512-tick horizon remains subject to scratch admission; the default CLI
budget can refuse smaller requests. The existing
Laurent owner remains authoritative for its modular observations.
The 2rev10 integration extends the exact packed execution kernel within
finite source and memory guards, preserving the smaller semantic-admission API.
Its centered harmonic projection uses issued endpoints and the existing clock.
The follow-up shares nested center windows and intervening carry halos, streams
defect emissions into compact period views, and removes the second driver pass.
Q19 public digit streams validate once. Small carry cochains use a bounded
stream; larger compressed sources retain the shared DAG fold with charged
reachable tasks and summaries. A tiny evicting cache was rejected because it
would repeatedly evaluate shared subgraphs.
The shared fold now counts reachable child references, rejects cycles, and
releases each summary after its final parent consumes it. This preserves
one evaluation per node without retaining every intermediate summary. Task,
reference and value reservations unwind on failure. Two existing bank CLI
regressions pass at their unchanged resource limits after this repair.
The cochain work counter records one evaluated algebra node per visit rather
than counting a DAG composite twice. Q19 output-node visits exclude the walker's
repeat-continuation tasks, matching the double-reverse instrumentation.
Mirror-sheet projection reuses the admitted
output buffer; the callback interface still reads each requested digit at most
once. Failed streamed observations release reservations and leave the source
usable for a subsequent request.
Repeated Center11 requests reuse one term-owned scratch account. Each call
returns it to zero live entries and nodes, including failed source rebinding;
disposed-account metadata no longer grows with the number of observations.
The exception audit also clears owned native decimal buffers and pending
grammar tasks when a traceback is retained. Failure tests keep the traceback
alive, inspect the cleared working state, verify balanced reservations, and
retry the same source. Original exceptions and their chaining are preserved.
An independent final review found no additional early-close, retained-traceback
or shared-summary lifetime defect. It confirmed that disposal waits for active
Q19 walkers to release their tasks and that summaries survive until their last
parent consumes them.

The public comparison harness now forwards explicit step and state-bit budgets
through the same parser as the measured request. No alternate parser, `-S`
interpreter or archive test launcher is used.

## Established results

### November 3 follow-up: Pascal product folds

The downloaded dyadic/Pascal changes are adapted to the existing source-root
owner. One SLP-node summary now computes residues and explicitly demanded
Pascal moments together; nested bands reuse that summary map. The finite
period-driver scan consumes the already checked source residues instead of
folding the source again. Ordinary term, help and metrics demands do not
request these moments. Reflection and repeat preserve chronological spatial
order. Moment data carries no temporal repetition authority.

The shared `PascalWordMoments` arithmetic accepts a caller-supplied Boolean
marker. The double-reverse adapter supplies the decimal threshold. Changing
an optional demand does not change exact source/root adjacency, and order
zero is preserved through temporal squaring. Failure during interval extraction
clears the product-summary map before releasing its reservation, including
when the caller retains the exception traceback.

Reverse/add's event reconstruction now uses a chronological Horner fold,
removing the per-event binomial convolution. Five alternating trials of 160
reconstructions on the same width-113 H20 input produced identical exact
outputs: median 0.14735 seconds at Git HEAD versus 0.03218 seconds for the
shared Horner implementation. This is a kernel comparison, not CLI speed evidence.
Evidence: `20261104T072154Z-4cdfad8dd69f4fd286c5fe0b69f3e188`.
The H12 source-potential and homogeneous mod-32 erasure refinement passes in
`Reverse_Growth_Admission`: 13 seconds, run
`20261104T080115Z-63a98068748349cba2b31d52e08ead61`.
Runtime retains H20 pending the actual shorter-window consumer admission;
homogeneous erasure does not remove the nonlinear forcing or authenticate an
arbitrary supplied event history.

The new optional moments add diagnostic information; they do not change
ordinary nth execution. The shared order-zero/order-one Isabelle refinement
passes in the rebuilt `Shared_Carry_Dynamics` session: 45 seconds under the
standard policy, run `20261104T075512Z-73f2cccbeb104d678794adab2d40f67c`.
The accepted claims include exact signed finite sums, composition, reflection
and repeated words modulo eleven. Higher Pascal orders remain independently
tested finite arithmetic without that kernel claim. Current validation and measurements
for the combined projection follow below; superseded development runs remain
in Git and the evidence directory.

The November 4 mod-70/Phi6 and bank-stencil reports add integration inputs,
not acceptance evidence. Their predecessor `JoinedPascalCarryBand` owner is
absent here; porting must extend the existing product fold rather than restore
an additional source traversal. Shared interpolation/CRT and ordered word
laws belong to arithmetic; decimal threshold, GT/EQ propagation, birth,
normalization and source/halo admission remain family-specific.
The reverse/add raw GT mask must not replace its propagated EQ carry response.
The doubled-digit glyph and normalized multiplication must remain distinct,
including both reflection conventions. New projections stay demanded, with
their scratch and retained summaries charged. Ordinary nth receives no
speedup claim from these optional observations, and spatial-copy period bounds
do not certify a source's temporal repetition. The optional double-reverse
word/mask/glyph projection is now in the existing product fold, with separate
glyph-of-reversed-source orientation and a guarded whole-source two-tick
projection. Its finite word algebra belongs to shared arithmetic; the family
retains recurrence and source admission. The focused carry/family/contract
selection passes 202 tests in 3.98 seconds, including independent literal and
CLI comparisons and both two-tick growth branches, run
`20261104T080725Z-0ea46865edca41f88dcb84ee277fd5d4`.
All 16 changed Python/test files pass strict mypy, strict Pyright, Ruff and
formatting; the current documentation check also passes, run
`20261104T080801Z-69cb0a47faed418ebaece639f64238bd`. Pyright runs in one
bounded serial batch. This is scoped quality evidence, not a whole-tree sweep.
No second SLP traversal or new CLI selection was added.
The final five-trial cold/warm/bypassed medians are 0.38107/0.19136/0.19003
seconds at 512 ticks and 0.50721/0.29405/0.29576 at 1,024 ticks, in the same
run as the kernel comparison above. All non-metric packets agree across cache
modes. The enlarged optional packet has no measured CLI speedup; ordinary nth
does not request it. The finite Phi6/Pascal proof-consumer gates remain separate.
The rebuilt `Double_Reverse_Temporal_Refinement` session passes in 93 seconds,
run `20261104T095316Z-edc3fe3b55b54d748f19d8c668085670`, peaking at
3,238,093,608 sampled process-tree bytes. The new T²/mod-70 theorem derives
the actual four-port output from a canonical source, and the no-growth
prefix-mod-7 identity follows from its carry split. Neither assumes a guessed
endpoint. The Python SLP-summary-to-HOL mod-7 bridge and the penultimate
threshold-unit refinement are still required for a full consumer extraction
claim. These finite theorems grant no temporal period or halo authority.
The reverse Q19 port now supplies a demanded `source_carry_phi6` packet through
the existing `spatial.bank-morphism` consumer. It retains both true forward
carry responses at roots three and five. Raw bank reflection is restricted to
the complete symmetric source, not arbitrary blocks. The base summary stays
unchanged; a charged additional projection pass uses the shared SLP walker,
without rendering digits or rebuilding the Q19 summary. Ordinary values,
metrics and temporal summaries do not request it. Source/interner, cached
first-pair metadata, foreign-handle, failed-allocation and disposal checks
remain active. `occurrence_temporal_steps` names the existing Q19 clock;
it is not relabelled as an input-word generation. The affine mod-seven port
consumes the normalized value returned by that occurrence, with explicit input
and output clock positions. Independent literal checks retain that distinction.
The active-scratch lifecycle scope now covers both streamed digits and the
demanded carry fold. Reentrant disposal during a cancelled fold preserves the
original exception, defers scratch disposal until reservations unwind, and
leaves no live ledger allocation.
The focused family/CLI/lifecycle selection passes 55 tests in 2.56 seconds,
run `20261104T125309Z-789b1874b3724926bf429e84bc9dbe1b`.
All eight changed source/test files pass strict mypy, strict Pyright, Ruff and
formatting, run `20261104T124423Z-f25e7d79da70496f8d8bb5fcb7dc4e14`.
This is scoped diagnostic coverage, not whole-tree quality acceptance.
The [full-suite record](comma-global-cutover.md#validation-provenance) includes
this integration. This packet is a spatial diagnostic, with no CLI speedup or
temporal-successor authority claimed. Its weighted mod-seven SLP refinement,
source binding and interpolation/CRT kernel proofs remain open; the existing
mod-five harmonic and temporal Laurent theorems do not prove those claims.
The interior stencil port still
requires an authenticated exterior halo and explicit birth/normalization
handling.

### Earlier centered-carry baseline

The earlier centered-carry revision passed 11,893 default tests in 205.84 seconds, with the
existing 715 validation deselections unchanged. This includes the shared-DAG
lifetime repair and retained-traceback fixes. The affected runtime and
reverse/add–Collatz P0 selection passes 81 tests. The reverse/add Center11
source refinement and double-reverse centered word/source-window refinements
passed kernel checking. These results precede the subsequent comma and Pascal
changes; they do not certify the current dirty tree.
A controlled matrix or endpoint forcing identity does not authenticate an indefinitely repeating
physical port program. The ordinary full-word producer and finite modular
projection are measured separately.

## Rejected approaches

Do not restore archive global cochain caches or raw issuer tokens. A finite
arithmetic summary has no execution authority. Do not label physical native
ticks as powered skips, infer a center return from mod-5 cancellation alone, or
infer source-period closure from matching projected residues. The extended
packed kernel remains a bounded, potentially quadratic calculation.

## Validation provenance

Baseline reverse/add: five cold trials each at generations 2,048 and 4,097,
innovation modulus 7, normal interpreter and existing public comparison runner:
`20261103T093542Z-63760fe8c142432e972c37e67bb733cb`.

Baseline 2rev10: the initial default-budget request refused before execution;
the measured run uses explicit 10,000-step and 100,000-bit budgets for both
baseline and replacement. Run
`20261103T093640Z-28aced64422140b4bc29872d95f15e78` retained all five cold
generation-4,096 samples and one generation-8,192 sample (33.45 seconds), then
hit the unchanged 60-second command limit during the next sample. This is not
a completed five-trial measurement at 8,192; the partial journal is preserved.

Replacement cold comparisons use the same normal interpreter and query budgets:

- 2rev10: `20261103T095445Z-02ac651eb382442b89fde86c41ef8b20`.
- Reverse/add: `20261103T095507Z-25815ac5f2a445979f0553822e69a14d`.

| Request | Baseline seconds | Replacement seconds | Samples |
| --- | ---: | ---: | --- |
| 2rev10 seed morphism, 4,096 physical ticks | 0.3010 | 0.2856 | Five cold trials each |
| 2rev10 seed morphism, 8,192 physical ticks | 33.4524 | 0.4290 | One completed baseline sample; five replacement trials |
| Reverse/add mod-7 innovation, 2,048 ticks | 0.4825 | 0.1147 | Five cold trials each |
| Reverse/add mod-7 innovation, 4,097 ticks | 1.6879 | 0.1365 | Five cold trials each |

Five-trial entries are medians. The 8,192 baseline is explicitly a single
completed observation, not a baseline median or a full benchmark pass.

Warm and genuinely cache-bypassed comparisons use the same receiving source:
`20261103T101112Z-d119184688194c65a97146e0b75ec6ad` (2rev10) and
`20261103T101130Z-c0bf3bb833204391a35e49ffb77d5bb5` (reverse/add).
Five-trial medians at the larger horizon are 0.2863/0.2608 seconds for
2rev10 warm/bypassed and 0.0316/0.0320 seconds for reverse/add. These embedded
requests exclude fresh interpreter startup. They establish equivalent results;
they do not show an additional warm-cache speedup. Before/after non-metric CLI
packets are identical at all four measured horizons.

The streaming observer follow-up uses five fresh CLI processes per case,
with identical non-metric packets before and after. Center-driver scans request
32 samples at depth 2; defect-clock requests 64 samples of 18 digits.

| Demanded observation | Baseline median seconds | Streaming median seconds |
| --- | ---: | ---: |
| 2rev10 seed 196 center drivers, 512 ticks | 0.6830 | 0.3577 |
| 2rev10 seed 196 center drivers, 1,024 ticks | 0.9652 | 0.4529 |
| 2rev10 seed 168 defect clock, 512 ticks | 0.1978 | 0.1968 |
| Reverse/add seed 196 Center11, 64 ticks | 0.1006 | 0.1004 |
| Reverse/add seed 196 Center11, 256 ticks | 0.1078 | 0.1024 |

Only the center-driver comparison establishes a substantial cold CLI improvement.
The other streaming changes reduce duplicated traversal or retained intermediate
records; these measurements do not establish a meaningful latency improvement.
They do not change ordinary nth execution.

The same center-driver demands also agree in five-trial warm and genuine
cache-bypass runs: `20261103T123740Z-38a91ceeda2146d99850b04fb7478c44`.
Warm/bypassed medians are 0.1846/0.1849 seconds at 512 ticks and
0.2872/0.2871 seconds at 1,024 ticks. These measurements establish no additional
warm-cache advantage; the improvement comes from sharing work within the demand.

Baseline/replacement run pairs:

- Center drivers: `20261103T102400Z-6f39db6fe9ba49569aa5d5687a38165a` /
  `20261103T104541Z-970129fbe754482896180567b908c518`.
- Defect clock: `20261103T102451Z-a18b5a98d447485089597a9fef68d1af` /
  `20261103T104549Z-fdd06ab47e1c45edab41a77806619afa`.
- Reverse Center11: `20261103T102546Z-2936d4bb7c404929b96a261fa4d90f0f` /
  `20261103T104559Z-26f6a83c755a4f1d96b43d342ee61117`.

Runtime evidence:

- Final complete default suite:
  `20261103T132610Z-7ff6d05242184605a537786b1d82586b`;
  all 11,893 default tests pass after the final theory split, with cleanup
  confirmed. The guarded invocation takes 208.006 seconds and peaks at
  438,437,376 sampled process-tree bytes.
- Retained-traceback lifecycle, shared fold, cochain and mirrored projection:
  `20261103T113501Z-4e8d780539a14b6caa70b6e4592d3dd2`, 145 passed in 0.85 seconds.
- Final affected packed/center and applicable reverse/add–Collatz P0 tests:
  `20261103T101145Z-83797758fabd42fb832a65435bf82e27`, 81 passed in 6.97 seconds.
- Reverse observer, metrics and benchmark contract checks:
  `20261103T095822Z-09a0eb9b938744fea55dd0b9afda9f46`, 195 passed in 3.81 seconds.

The rebuilt `Reverse_Residuals` session passes in 62 seconds under the standard
300-second, 6-GiB, four-thread policy:
`20261103T123138Z-6ab6f046e21c45969cf33fa08af46612`.
The new Center11 source theory proves the half residues of actual successors,
admission of their extracted ports, and finite induction over those successors.
Symbolic coordinate and Boolean-branch lemmas replace repeated expansion of
the concrete source tick. Accumulator translation preserves the public initial
half-difference convention. This is a finite arithmetic refinement, not
unrestricted source-period authority or extraction of Python issuer validation.

The rebuilt `Double_Reverse_Temporal_Refinement` session passes in 91 seconds:
`20261103T132222Z-81e88308f71448cab6fbd667057c6d67`.
Its process-tree peak was 2,664,264,656 bytes, below the standard 6-GiB limit;
dependency heaps were reused, while the affected session was rebuilt.
The centered word theory took 22.038 cumulative seconds and the source-trace
theory 1.397 seconds. Explicit modular congruences replace the expensive
Presburger calls, and the exact weighted action supplies the digit bound
without a second trace induction. Word composition lives in a separate theory
within the same session and deadline.
The accepted claims cover four physical steps, chronological finite words,
mod-5 forcing/telescoping, terminal parity and a finite source-window endpoint.
The source trace assumes the exact SLP slice and decimal window; it allows
zero padding and does not authenticate a Python-issued cursor, an arbitrary
future repetition, or unrestricted temporal closure.

The earlier November 7 quality checkpoint is
`20261107T054223Z-a2dade34c5a6420cafce46cd63324f17`: strict mypy and all 99
serial Pyright batches cover 2,451 maintained sources with zero diagnostics;
Ruff, formatting, documentation and proof registration pass. Source policy's
one duplicate setup finding was repaired by a typed fresh-chain test helper;
the nine focused tests and strict Pyright pass again, and the final policy
check passes in `results/nov7-final-policy-v2.json`. The installed-wheel check
builds the wheel but rejects the absent admitted comma future artifact. Its
older green result does not establish acceptance after forest deletion.
The reverse/add and Collatz P0 selection at that checkpoint passes 43 tests in
`20261107T054924Z-881ee1b167084f0399d810588541e070`.
The registered `Collatz_Cylinder_Refinement` session rebuilds successfully in
`20261107T054954Z-91021b8582dc4e398469632fe528f7ed`: 20.801 native seconds
(24 seconds reported), with `Shared_S_Arithmetic` rebuilt separately in
47.046 native seconds (52 reported). Existing guarded-word repetition,
endpoint and accumulator laws are rechecked; this does not supply missing
future parity choices or a Python extraction theorem.
These are dirty-tree development results at Git
`2994b2841317fd141cd7913142c53f38685838a7`; they do not certify a committed
release. No fresh Colima or minimum-Python acceptance is claimed.

## Remaining work

The downloaded Vieta temporal join requires a source-authenticated temporal
output owner that the current Q19 block producer does not publish. The archive
attaches packets to guarded transition letters from the same emitted carry
trace. The current producer returns the final occurrence and may use a native
decimal block, so copying only the packet module would create a disconnected
observer. The join remains open; port equality is not a future-state identity.

Unrestricted source-period closure, comma, primality and non-halting gates remain
separate. No downloaded success flag or finite diagnostic retires those holds.
Production cursor admission remains covered by runtime authority tests rather
than a complete Python-to-Isabelle extraction theorem. Fresh Colima acceptance
and clean-commit release acceptance remain separate from this native
development run.
