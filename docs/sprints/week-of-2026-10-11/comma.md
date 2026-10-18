# Comma labelled-selector proof cutover

Period: 2026-10-11 through 2026-10-17 (Sunday–Saturday).

[Week index](README.md)

## Objective

Replace repeated concrete Boolean-partition certification with a checked labelled
selector and transport its fibers into the existing B1 occurrence contract.
B1 must pass before B32/global acceptance and production forest/fuel retirement.

### October 17 cold LiftProofID repair

A controlled child-list proof schedule was tested and rejected. Run
`20261017T185209Z-cae440792f98418eb1ba45c0aeb7080a` passed the kernel fixtures,
including a demanded scheduler-hit assertion, and certified 36,120 scheduled
nodes / 146,661 children at its last indexed checkpoint with zero scheduler
fallbacks or failures. It nevertheless timed out at 300 seconds (309.12 seconds
guarded, 3,455,071,376 sampled bytes, cleanup confirmed). At the same 910 cold
lifts, admission took 174,248 ms versus 158,963 ms with the existing rewrite
schedule and repaired caches. The prototype, loader, counters and prototype-only
fixture assertion were removed; the existing exact-output assertions remain.
The experiment did not justify replacing the live proof schedule.
After removal, quality run `20261017T185751Z-7bdea62081f04762a33c911d7a66f3cc`
passed all seven checks, including installed-package validation. Focused run
`20261017T185928Z-da499fa21dc241c1a8b9912d6d4dcd96` passed all 80 tests.

The diagnostic attempts preceding that run caught ML syntax/type mistakes,
missing finite-range rewrite rules, a mismatched profiler-stage name, and a
map-congruence middle-term mismatch. The last required using the actual
kernel-rewritten head instead of reconstructing a beta-equivalent application.
Those attempts did not reach concrete certification and are not performance
evidence. No B32/global or production forest/fuel acceptance is claimed.

Run `20261017T183247Z-6b9756c0f3144cc09a2fe3576832e695` passed the shared
cofactor and bounded interval-cache fixtures, but again timed out at 300 seconds
(309.39 seconds guarded, 3,164,570,504 sampled bytes, cleanup confirmed). The
last indexed checkpoint completed 974 cold lifts: admission 228,382 ms, active
Apply 203,779 ms, operand normalization 54,869 ms and reification 36,861 ms.
At the comparable 910-lift checkpoint admission was 158,963 ms versus 165,022 ms
in the preceding run. These partial measurements do not establish B1 acceptance.

The interval owner now evicts completed facts instead of permanently refusing
retention once full. At 974 lifts it retained 8,192 facts, recorded 90,678 hits,
16,026 misses and 7,834 evictions, with no capacity refusals. Keys retain the
checked block constant and exact interval; new facts are checked before
publication. The shared cofactor cache retains a schematic-column transport
alongside its scalar equation; each source transition remains separately
authenticated. Earlier attempts `183018` and `183045` exposed a tuple-call error
and bound-variable typing error; review also corrected the eviction fixture's
expected concrete result. All were repaired without weakening assertions.

Quality run `20261017T183826Z-1c67634a030044ac8da9ccd62cc9c676` passed typing,
lint, formatting, policy, documentation, proof inventory and installed-package
checks. The strengthened downstream C1-to-B1 source-slot record is wired into
the producer but remains unbuilt behind concrete B1. Forest/fuel authority is
unchanged. Further work targets the cold recursive Apply rewrite schedule.
Focused run `20261017T184131Z-250f216f572f420eaa2d572987ab5114` passed 80 tests
in 1.89 seconds after updating the static interval-cache assertion to follow
the new checked publication and authority-qualified key. The prior focused
run failed only that stale implementation-spelling assertion.

Run `20261017T181919Z-0d6bef50e8d3420ab22aaf385eebe0b1` passed the repaired
kernel fixtures and reached concrete lift certification, but still timed out
at 300 seconds (309.42 seconds guarded, 3,133,416,352 sampled bytes, cleanup
confirmed). At 910 lifts, admission fell from 200,190 to 165,022 ms and active
Apply from 177,578 to 139,280 ms versus run `175353`. Final operand-normalization
time was 37,989 ms; the bounded scalar cache built 745 equations and recorded
142,266 hits. These are partial-stage measurements, not a completed build.
Reification reached 68,015 ms before timeout. The 910-lift checkpoint had
7,621 retained interval certificates against an 8,192-entry ceiling; its
refuse-after-capacity behavior is being audited as a possible later cost cliff.

The scalar-cofactor repair adds a bounded, context-owned cache of exact digit
equations. It does not cache source authority: each cold cofactor still checks
the owned column and exact transition theorem. Quality run
`20261017T180831Z-fa35fe700f184531ae2f57ba6f6bd216` passed all seven checks;
the preceding quality attempt found a test import/type issue and the missing
explicit native audit on the new right-clock theory. Focused run
`20261017T181016Z-b3d5497b459746269fdd1d1c7d7e0aeb` passed 80 tests in 1.91 seconds.

Kernel runs `20261017T181044Z-a154bf1d57134a258c9028ad376b9ff6` and
`20261017T181235Z-c7f7261b68ea4d2a9ca7c08f2730b262` exposed, respectively,
a term/integer argument mismatch in the scalar-cache call and an object/meta
equality mismatch in a migrated fixture. Both were corrected without weakening
the assertions. Run `20261017T181347Z-fb9c0342bfb044e6a67385a375e90d0e` was
interrupted after 71.91 seconds, with cleanup confirmed, when the migrated
literal-column fixture exposed a no-progress fallback recursion. The repair
rejects unchanged cofactor/source expressions before recursion and restores
the fixture's authenticated reference boundary. These diagnostic runs did not
reach concrete B1 certification and provide no performance acceptance.

Run `20261017T175353Z-bb7f437db4244ffa946600733fb2e83d` passed the new
owned-reference and comparison poison fixtures, but again timed out at the
300-second session limit (309.22 seconds guarded, 2,836,988,592 sampled bytes,
cleanup confirmed). At the same 910-lift checkpoint, admission was 200,190 ms
and active Apply was 177,578 ms. Removing reflexive comparison storage and
already-owned reference reification therefore did not close the gate.
New stage timings measured 77,174 ms operand normalization, 21,725 ms
reification and only 94 ms theorem-shape validation at that checkpoint. Nested
rewrite/derive totals are inclusive and must not be added together.

The preceding diagnostic attempts caught two instrumentation/fixture errors:
`20261017T174226Z-dfbe8cabccb74bd19ec57fc50b48a66b` hit the Standard ML value
restriction in the polymorphic timer record; the timer now uses a monomorphic
state and a polymorphic top-level function. Run
`20261017T174840Z-435beb341be34c1792f041e529de0ee6` rebuilt prerequisites but
rejected a curried fixture lambda; its syntax is corrected. Timings accumulate
full `Time.time` durations before conversion to milliseconds, so short calls
are not silently lost. Neither failure changed mathematical assumptions.

The subsequent concrete run `20261017T172936Z-2cd4aa9db97b481b9a66f2783a49a95c`
passed the mixed-level clock, exact admission and warm-parent kernel fixtures,
but still timed out at 300 seconds (309.51 seconds including orchestration and
cleanup; 3,075,744,504 sampled bytes; cleanup confirmed). Its last indexed
checkpoint had 910 cold lifts: 202,730 ms admission, including 179,507 ms active
Apply work. By termination the Apply owner had published 36,278 keys, reused
125,253 requests and constructed 34,286 recursive certificates, with no capacity
refusals. Depth transport and right-column clock rules were reused, but those
results do not establish a successful concrete B1 build.

The actual-DAG fixture also exposed a swallowed admission-producer exception:
an authenticated column could silently lose its right-clock quotient when its
proof producer failed. That exception now propagates, with a poison fixture;
unknown columns still return the explicit unsupported result. The fixes preserve
the zero-clock branch and exact source-owned column authority. Further work is
targeting repeated normalization and reification of already-canonical columns,
with separate timings for cold recursive proof construction.

The desktop candidate was selectively rebased onto the current proof owner.
The first instrumented build, `20261017T164641Z-3af252a674fa42d699aead8fd4be200f`,
still hit the standard 300-second session limit. Its last completed checkpoint
was lift 928: admission consumed 235,767 ms, specialization 420 ms, and binding
resolution 5,622 ms. These partial totals isolate the dominant stage; they do
not establish concrete B1 acceptance or a cold-build speedup.

The follow-up audit found that both syntactic and opened Apply shortcuts
returned checked results without publishing them in the canonical Apply memo.
The repair transports each admitted result to its exact normalized depth/clock
key before publication. It retains the existing 65,536-entry bound and records
capacity refusals. The admission simplifier base is now shared too, and the
profile separates catalogue selection, sterile option specialization and active
Apply work. Exact request equations, catalogue authority, foreign-reference
rejection and closed-theorem checks remain mandatory.

The first kernel fixture run (`20261017T165811Z-2147c6c39f084534a2e2345b14837527`)
caught an obsolete cold-counter expectation: a preceding fixture had already
published the same canonical shortcut. The replacement assertions require
exact and clock-alias hits with no additional shortcut or recursive proof;
cold-publication coverage remains in the preceding fixture. The normalized
conditional-input test likewise now requires reuse of the already checked key.

Run `20261017T170016Z-f5f116796ed24a4da175aec2e3920961` passed those kernel
fixtures but still exhausted the 300-second B1 limit. At the same 928-lift
checkpoint, admission took 213,028 ms versus 235,767 ms in the candidate-only
run; specialization took 335 ms and binding resolution 5,053 ms. This is a
partial-stage improvement, not an accepted B1 result. At checkpoint 672 the
Apply memo recorded 89,712 hits, 27,275 retained keys and zero capacity refusals;
96,978 unused-depth strips exposed another repeated proof-transport cost.

Full Python run `20261017T170623Z-2b2b4ae7d99c4af793504f16a4fb0c7e` completed
in 274.24 seconds with 10,908 passes, 418 validation-only deselections and the
existing F4 concrete-output failure. Proof edits overlapped this development
run, so it is not acceptance evidence for the final proof source.

The right-operand clock quotient passed the generic `Comma_Semantic_B1`
kernel build in `20261017T171412Z-72ef3f3152ea45cfbfdeac2d06edd56e`:
39 seconds native, 50.35 seconds guarded, 2,439,221,672 sampled bytes and
confirmed cleanup. The new theorem checked in 0.265 seconds. It derives
clock equivalence from the admitted right column's remaining CRT levels,
while preserving the separate zero-mod-924 shortcut branch. The left
operand's unshifted levels do not constrain that clock. It is imported by
the live support theory, not registered as a detached experiment. The first
attempt failed at an unchanged-node admission proof; retaining the original
child-admission fact fixed it without changing the theorem's assumptions.

C1 reuses the arithmetic owner's complete-cycle displacement instead of
recomputing it inside its powered return. The scalar and C1 callers share one
bounded-tail implementation, with validation at their respective boundaries.
The existing Entry bridge now also publishes its selected weighted move, while
keeping the physical clock independent of the exponent clock. Its kernel rebuild
passed in `20261017T165345Z-5b7aef1cdc734ceea1b21f0f2189614d` (33 seconds native).
The preceding attempt failed because the new proof omitted existing sector and
offset assumptions; those assumptions are now supplied explicitly.

Carry, borrow, occurrence and comma CLI checks passed 92 tests in 7.54 seconds
in `20261017T165520Z-87ca2f0da9e24834b14d17a6e393ea54`. The warm borrow test
now poisons the actual displacement owner after the helper migration, preserving
its no-reconstruction assertion. Cache/producer source checks passed 24 tests in
`20261017T165659Z-cf99b7820c67431ab273ec29bd00fb71`. C1 is consumed by the
source-bound occurrence/provider path; these results do not establish that it
replaces the default CLI constructor or the B1 lift-binding proof.

Development run `20261017T102058Z-c5def5c161d049e5b48cabd72c7d2d25`
passed the shortcut-admission and warm-alias fixtures but hit the unchanged
300-second B1 session limit (310.114 seconds guarded, 3,363,484,744 sampled
bytes, descendant cleanup confirmed). Its last indexed checkpoint had 782
completed lift bindings, 28,353 recursive Apply certifications and 132,885
Apply requests. The preceding depth-quotient run stopped at 526 completed
bindings; partial checkpoint counts are not an end-to-end benchmark or a pass.
The shared incremental oracle certifier took 264 ms at the latest checkpoint.
Root-exposure counters mostly reflect shallow cached theorem applications,
not new recursive column proofs. The dominant measured work remains concrete
lift-binding certification and normalization; no scalar-decade replay was
recorded. C1 Entry integration is a separate obligation and cannot be credited
with eliminating that work.

The early syntactic Apply shortcut now validates operands before invoking its
counted rewrite. The foreign-operand and normalized-conditional fixtures caught
the earlier ordering error; their assertions were preserved. Fresh depth
admission facts are oracle-audited through the column owner's shared certifier
before publication, while exact proposition and theorem-cleanliness checks
remain at reuse boundaries. No forest/fuel retirement follows from these
repairs.

C1's source-bound Entry bridge passed the kernel in development run
`20261017T102617Z-10f2302f64f249bbb6a3ff490f59886d` (33 seconds native,
40.856 seconds guarded, 1,885,896,672 sampled bytes, cleanup confirmed).
The new theory checked in 0.601 seconds; imported chart theories account for
most of the session work. It retains the high prefix and proves the exact
physical duration, powered endpoint/carry count, source guard and literal
Entry-to-Near path. The guard proof uses the checked headroom bound before
natural subtraction, avoiding eager simplification of the chart expressions.
This does not identify the physical 50-step clock with the 924-phase exponent
clock or prove complete B1 selected-action equality. The Entry writer now
consumes the C1 path theorem, but that downstream producer theorem remains
unbuilt behind concrete B1. Forest/fuel admission is unchanged.

The proof inventory subsequently caught missing local oracle audits in the two
new theories. Both now have explicit transitive oracle checks. The C1 session
rebuilt successfully in `20261017T102922Z-497109cee2b140b5a961fbdcb293f60a`
(34 seconds native, 41.521 guarded seconds, 1,853,825,040 sampled bytes,
cleanup confirmed); the new theory and audit took 1.164 seconds. This replaces
the earlier C1 checkpoint for current-source evidence.

The focused carry, occurrence, producer-source and cache selection passed
63 tests in 1.32 pytest seconds (1.857 guarded seconds, 64,242,624 sampled
bytes) in `20261017T102723Z-7ad4eb50caaa4429a7046dc97d6c4c75`.
The same selection plus a new clock/seam regression passed 64 tests in
`20261017T103047Z-fe1daa01ff5b4d59a104bec672569742`. The regression fixes the
physical example `900000 → 999900` after 1,850 C1 steps, followed by the two
literal Near edges `999900 → 999909 → 1000000`; only the final edge advances
the exponent. Extending the fixed-sector C1 action across that seam is rejected.
The whole-tree quality rerun passed typing, lint, formatting, source policy,
documentation, proof inventory (139 sessions / 405 theories), and installed-wheel
checks in `20261017T103113Z-e0aa6a6f88f24ea9ad588b8bcd777ccc`. These development
checks do not replace the failed B1 build or constitute full-unit acceptance.

The suffix-clock transport theorem passed its generic kernel build in
`20261017T092909Z-fb85db6ca4d44502971b09a6fd49ca19` (74.234 seconds guarded
elapsed, 2,847,715,944 sampled bytes). It preserves the zero-shift shortcut
branch and quotients the remaining clock dimensions by depth. Its concrete
warm-alias fixture also passed: shifts 1 and 12 at the final clock dimension
reuse one recursive action proof while retaining their exact request equations.

Concrete run `20261017T093325Z-dcc0fa88d3de4edb984989c4585faf26` still timed
out at 300.045 native seconds (309.645 guarded seconds), with a sampled peak
of 3,183,141,816 bytes and confirmed cleanup. The latest indexed checkpoint
contained 654 completed lift bindings, 23,807 recursive apply certifications
and 12,207 suffix-rule hits. Lift-binding inclusive time was 233.195 seconds;
no scalar decade expansions were recorded. These counters do not establish
a net speedup or concrete B1 acceptance. The next audit identified literal
Boolean children failing to re-enter authenticated column references, leaving
expanded node trees in the apply path. That repair remains separately gated.

Development run `20261017T094416Z-ff669be09e3148a1be224f3880a51957`
passed the Boolean-child reification, symmetric comparison-cache and shortcut
result-normalization fixtures, then timed out at 300.059 native seconds
(310.874 guarded seconds). Peak sampled memory was 3,499,910,288 bytes and
cleanup was confirmed. Its latest indexed checkpoint contained 622 completed
lift bindings, 105,557 apply requests and 22,615 recursive certifications.
These changes did not close concrete B1. The C1 physical occurrence bridge is
a separate integration obligation; no measured scalar-decade replay was
removed by merely adding that dependency.

The extracted fixture-owner source check passed 11 tests in 0.45 seconds
(`20261017T091416Z-7e465d7f67e3481fbdc1f46a70a8f47b`). No new B32/global,
installed-wheel, full-unit or production activation claim follows.

Development run `20261017T074801Z-76b4ab56c49a4799a7dab536497f9835`
passed the shifted-apply fixtures after demand-local node-level and column-ID
normalization. It reached 558 of 2,444 cold lift bindings at its last indexed
checkpoint, with 263,028 apply requests, before the unchanged 300-second
session deadline. Peak sampled process-tree memory was 2,948,707,088 bytes;
descendant cleanup was confirmed. Selected descriptor equations and successful
admission are now reused, but the recursive apply proof still traverses its
result repeatedly. This run does not admit B1 or the global provider.

The release contract now explicitly includes grouped-chart termination as well
as the scalar chart-to-publisher bridge; both await a concrete kernel build.
The focused authority/consumer/source-contract selection passed 70 tests in
1.98 seconds (`20261017T074741Z-253d852efa3d4588a4628f6377cc93b9`).

The October 17 shared-column comparison repair passed its production-shaped
kernel regressions in development run
`20261017T072501Z-3fff55e7f78045efa3e9da76f281b359`. The concrete occurrence
certificate still exceeded the 300-second session limit. Its final profile
recorded 127,233 apply requests, 114,992 hits, 11,360 retained keys and zero
derive rejections; the latest indexed checkpoint had certified 302 lift
bindings. This is repeated lift-row work, not evidence of concrete B1 or
global acceptance. The guard confirmed descendant cleanup and sampled a
3,016,766,512-byte peak under the unchanged 6-GiB limit.

The scalar chart walk now has a proposed bridge to the same first-terminal
events, writer fragments and indexed macro, included in the global producer
release contract. It remains pending kernel validation. An independent review
confirmed the staged removal of the 4096-step chart cap matches the scalar
production iterator; grouped execution is not a production caller. The three
forest/runtime, packaging and legacy-proof deletion patches apply together in
a temporary snapshot, but remain unapplied. The runtime artifact registry is
still empty. Source-to-artifact binding, B32/global acceptance and positive
installed CLI checks are required before activation.

The runtime admission audit now rejects reversed ordered-child class bindings
before publication. The focused branch/provider/producer-contract selection
passed 70 tests in 2.27 seconds in
`20261017T073148Z-ff5753d9e3074367adefd8e7e4cdfaf5`. These are dirty-tree
development results at Git HEAD `f31261a6`, not release acceptance.

An earlier concrete checkpoint is development run
`20261017T051717Z-00eb70eceadc484faafea5367edd7c4b`: all 278 template mass
proofs, 430 occurrence transports and the 3,225-to-2,444 used-lift projection
passed. The build then rejected lift-descriptor admission before certifying
its binding. It ended with a proof error, not a timeout. The generic compact
coverage/mass induction passed in
`20261017T050441Z-568b73cc9c61489093841a3d0f80469b` (48 seconds native session
time). Neither result accepts concrete B1, B32, the global release theorem or
the production cutover.

Run `20261017T053430Z-d5832d1348e143a8a6e747d30cc5ca1d` narrowed that
admission refusal to an unreduced finite-set membership test for period 28,
not an invalid descriptor. Lift checks now use the prepared operation context
and explicit finite-set rules; they precede the independent mass checks so a
lift regression fails before mass certification. The subsequent run
`20261017T053941Z-021acae37f634d3fbfae59c57220b61e` passed descriptor
admission but reached the 300-second session limit during lift binding:
roughly 357 of 2,444 bindings were captured, with over 74,000 CRT apply parse
rejections. The new profile separates rejection shapes, and mass-owner
construction is now deferred until its first demand. These repairs still
require a passing concrete session.

Diagnostic run `20261017T054803Z-67e489f9735c4342ac75f1cf93dcd790` was
interrupted through the guard after identifying the dominant rejection:
production columns retain authenticated `column_at(dag,cid)` children, while
the apply cache accepted only expanded literal trees. Its first 738 production
parse rejections were all right-column shape rejections. An independent caller
audit also found the older column procedure could evaluate apply requests in
the assembled occurrence context before the shared apply owner. The repair
must connect shallow checked column equations and the same apply owner to that
context; accepting arbitrary references or eagerly expanding the DAG is not
an equivalent fix.

Run `20261017T060023Z-484c1780a22542c79c88009d7dc4a9ce` exercised that
shared reference-aware apply owner, but failed after 137 seconds at a cold
lift-binding exactness check. It published 390 apply equations and recorded
3,352 hits; generated source-axis/conditional operands still remained outside
the completed-column cache contract. This is an incomplete concrete proof,
not a passing B1 result or a timeout. The next repair must normalize those
operands with checked equations and strengthen the nonterminal production
fixture; cache-hit counts alone do not establish complete binding evaluation.
The stronger full-depth, nonempty period-28 fixture failed early in
`20261017T061543Z-6ce742dcbb494d6e9078287feabce5b1` (54 seconds native).
It exposed missing source-node normalization rules and a fixture callback
running before staged-converter initialization. Both are being repaired in
the actual occurrence context; the no-fallback fixture is retained.

The subsequent nonempty-column failures were evaluator incompleteness, not a
false phase result. Development run
`20261017T062846Z-e9eab0f2839947c3aa45d83f69845dc1` exposed the residual
`comma_crt_eval 27 (Comma_CRT_Bool True)`. Replacing the recursive node code
equation had left the Boolean leaf equation unregistered. The canonical CRT
and MDD evaluator owners now explicitly restore their leaf code equations,
as the support evaluator already did. The production fixture keeps the
depth-four shifted operation, exact phase-27 witness, independent kernel
evaluation, warm-hit no-recursion check and foreign-reference rejection.
This repair still requires the concrete B1 and global session builds; it does
not register the runtime candidate or authorize forest deletion by itself.
Run `20261017T063102Z-c909875048a0459f98465d4957fea3b7` rebuilt generic
B1 in 59 seconds and semantic-future lemmas in 35 seconds. The strengthened
shifted fixture passed, but concrete B1 rejected lift binding 113 with an
unresolved conjunction. The profile identified conditional operands left
outside the apply normalizer. The follow-up selects only the branch of a
closed, checked guard and keeps the complete binding assertion; the global
artifact registry remains empty. Shared lookup and indexed-range helpers
have also moved to their existing owners, replacing duplicate implementations.

The runtime artifact regression also exposed duplicate reservation accounting:
the authored quotient exceeded the default 131,072-node budget when parsing
workspace and retained-provider costs were charged simultaneously. Publication
now transfers its existing reservation into the retained memo. The actual
artifact fits that unchanged budget in focused development testing. Run
`20261017T054509Z-afe1b87190a449e2b522957311e3453e` passed 97 resource,
provider and proof-cache source tests in 1.80 seconds. Run
`20261017T054523Z-62d225119ee04fab85c93b01d91f49a6` passed 92 additional
artifact, branch-selection, certificate-observer and CLI tests in 25.67 seconds.
These are dirty-tree development results, not global proof acceptance.
The broader resource/admission selection passed 640 tests in 29.09 seconds
(`20261017T055318Z-b13d36d9d28240ea9dbda2aa9b6b3b88`). Authored-table
consumer coverage passed two tests in 1.43 seconds
(`20261017T055751Z-cb5d918738be40bd9726594fd347e361`), including the public
CLI at index 143,710,993,553 with forest verification poisoned and explicit
test-only global admission. Bounded literal windows and independent terminal
fixtures check later forks; the 143-billion-transition macro is not replayed
literally. This fixture cannot authorize the production registry.
The strengthened CLI regression then passed in
`20261017T060723Z-ef753716416e40a98c9f9f85baf36a00` (two tests, 1.42 seconds).
It requests the result after two post-entry macro decisions and verifies both
N(2,10) and N(7,12) provider selections. This closes the earlier test's
coverage gap; it still uses explicitly synthetic global admission.
Read-only certificate reporting for an already loaded provider previously
incremented lease-resolution counters. Its shared validation path now has a
snapshot mode, preserving store, ledger, generation and theorem authority
checks without changing counters. The focused provider/admission/reporting
selection, including repeated loaded-provider snapshots, passed 66 tests in
1.84 seconds (`20261017T061806Z-7a8f10ddf5b84828b82e42d7d8f0e216`).

## Changes

The October 17 review traced the concrete release dependency rather than adding
another global lemma. `Comma_Semantic_Future_Instance` already connects B1's
B32 result to the decade summary, ordered future children, global path agreement
and producer refinement. Its prerequisite B1 occurrence publisher is still the
blocking executable certificate. The older native/sparse global session is a
separate route; a pass there does not certify the semantic provider.

The remaining proof-reuse work has two owners: context-bound lift certificates
for repeated descriptor applications, and checked operation-DAG composition for
first-time shifted CRT applications. Template equality alone cannot replace
either obligation. Keys must preserve the exact shift, Boolean operation,
ordered column operands and catalogue authority; output bindings remain checked
separately. The global provider registry remains empty until the concrete
release session and the exact packaged artifact are accepted.

The harmonic-ring review applies at the composition boundary: the second action
must consume the first action's certified successor and transported clock.
Comma already has orbit-word, semantic-word and CRT split-power composition
theorems; no 2rev10-specific recurrence is substituted for them. The missing
integration is concrete source-action certification from shared template and
lift facts. An exact-expression apply cache alone does not establish that
quotient or an end-to-end speedup.

The generic selector proves exact column fibers and the unchanged partition
checker. Labels identify columns; source bindings, clock shifts and continuation
weights remain separate. Total selection alone does not certify the columns.

The concrete driver now reuses certified directory intervals and subtrees, composes list
proofs from certified tails, and checks whole-result equality at publication.
It retains atom authority, ordering, multiplicity and foreign-CID checks.
The redundant vector cache had zero hits in 3,690 lookups because the parent
state cache already intercepted reuse. Its replacement warm-parent fixture
requires unchanged cold-work counters and the same closed theorem.

Source discovery evaluates bounded batches while retaining every source's exact
action row for the subsequent fold. This amortizes evaluator calls; it does not
remove arithmetic discovery or claim logarithmic cold work.

Stable indexed filtering removes false columns from residual proof keys while
preserving the positions and multiplicity of every retained column. A generic
induction transports the compact selector witness back to the full column list.
Raw embeddings and compact states have separate bounded caches. Directory keys
contain shallow owner constants and bounds, not recursive bodies. Cold publication
checks authority; point specialization preserves exact roots and intervals. The warm fixture
replays the raw wrapper; generic lift instantiation remains measured work.

The producer bridge preserves exact summary, writer and partial-selection
contracts. Its corrected existential token and aggregate release statement are
not yet accepted by a concrete downstream build. Runtime staging is fail-closed:
no global artifact is registered, and failed staging closes its temporary store.

The multiset transport theorem derives an exact occurrence permutation inside
HOL and transports only the existential selector witness. Numeric CID multiset
equality is checked before mapping to columns; semantic equality after mapping
cannot replace that admission. The concrete helper deletes the per-index
inverse/projection-table pipeline and retains exact source/target cache keys.
At the same 78-template checkpoint, numeric transport certification fell from
5,285 ms to 438 ms. Cofactor-vector proofs then dominated at 8,392 ms. Identity
transports now check the exact closed theorem too; negative fixtures reject
open assumptions, wrong levels, unrelated truth and malformed column mappings.

A generic admission lemma proves that a cofactor below the admitted node level
is the column itself. Its concrete branch uses the checked header admission,
without unfolding the node and constructing its raw child-admission proof.
The ordinary at-level branch retains its existing exact decoder checks.

Two unused partition checker/session wrappers and a duplicated row projector
were removed. The legacy state prover remains only in adversarial fixtures;
the live checker uses the labelled driver. Assertions now inspect canonical
owners; foreign handles, reset races, failed staging and changed witnesses
retain positive and negative coverage.

### Assertion migration

| Previous implementation assertion | Retained behavioral coverage |
| --- | --- |
| Per-source piece blocks, origin multiplicities and piece-directory projection | Removed with that artifact shape; compact source coverage, child ordering, template geometry and exact lift-ID bindings remain checked. Executable fixtures reject stale descriptors and incorrect output labels. |
| Directory lookup unfolds `dag_lookup.simps` per CID | Exact interval transfer, unchanged point endpoints, same-block warm reuse, foreign-root/block/bounds rejection |
| Cached residual retains a concrete selector tree | Closed existential witness for the exact ordered columns, unchanged partition checker, wrong-phase and wrong-label fixtures |
| Every retained column is proved non-false during compression | Exact positional embedding; retained false is permitted, omitted true is rejected; partition coverage remains required |
| Every captured certificate rescans all oracle dependencies | Every root is checked by the existing immutable-node certifier; failed checks do not publish; final bundle keeps the full audit |
| Numeric permutation requires `Code_Simp` | Exact closed numeric relation, inverse/multiplicity checks, mapped column relation and oracle audit remain mandatory |
| Lookup fixtures reside in the large column-regression module | The same fixtures execute through a dedicated lookup fixture owner in the same session, including foreign roots, changed bounds and warm reuse |

The generic embedding migration has passed; its concrete use still exceeds the
session deadline. These replacements do not weaken exact output or admission tests.

## Established results

Generic `Comma_Semantic_B1`, including the full indexed-label transfer, rebuilt
in 35 seconds. Generic `Comma_Semantic_Future` previously rebuilt in 30 seconds.
Earlier concrete B1 runs exceeded their then-current 60-second deadline. The pre-compression driver
completed 75 template partitions, compared with 54 in the clean baseline.
The first compact-label integration regressed to 50 completed partitions:
at its last diagnostic checkpoint, label-compression proofs consumed 6,469 ms
and child-list proofs 5,944 ms. This exposed full-simplifier traversals inside
the otherwise shared construction. Node-presence proofs were below the
millisecond counter resolution at that checkpoint. Source discovery took
7,349 ms versus the baseline's 8,818 ms. Partial counts are not accepted bounds.

The follow-up replaces label filtering, child selection and child counts with
certified list-spine conversions, and beta-normalizes only the demanded outer
application. One common exact witness check replaces duplicated branch checks.
Those changes reached 66 partitions. Replacing child-selector trees with a
proved existential partition witness reached 81 partitions while reducing the
measured child-proof fold from 2,015 ms to 156 ms at comparable checkpoints.
The generic witness chain passed in 35 seconds. Concrete B1 still timed out;
its remaining measured costs include fresh column directory lookup and shallow
column unfolding, so the child-fold improvement is not end-to-end acceptance.
The existential witness retains exact ordered columns, including a checked lift
from compressed labels; it does not replace partition coverage with mere
reference validity.

The offset-mask constructor reduced embedding proof work from 5,590 ms to
477 ms at the same 78-template checkpoint. It proves only that omitted columns
are false; it preserves every retained occurrence and validates the complete
positional result. Shared dependency certification reduced the corresponding
captured-root audit time from 1,577 ms to 43 ms. Concrete B1 nevertheless timed
out after 82 template partitions: previously eager column unfolding now appears
in cofactor-vector work, so these component reductions are not an end-to-end pass.

The profile-only permutation diagnostic found 815 exact state misses but 393
distinct multisets at that checkpoint. The new generic permutation theorem now
transports a sorted partition witness back to the exact requested column order.
It preserves multiplicity and uses numeric permutation certificates lifted
through an opaque column map. The existing ordered embedding is unchanged.
Separate bounded caches retain sorted witnesses, requested-order witnesses and
permutation certificates; warm checks forbid certificate reconstruction and
transport. Cold certificates share immutable proof-dependency checks through
the existing context-owned certifier.

The generic transport chain passed in 35 seconds. Profiling its development
identified an unused distinctness derivation that exhausted the session limit;
that derivation and its unused multiplicity bundle were deleted. The operational
relation retains both inverse round trips and all bounds. Exact selector
transport and duplicate-column rejection remain kernel-checked. This generic
pass does not certify concrete B1 or the global release.

The first concrete permutation run exposed repeated numeric list indexing:
a 13-column certificate took 435 ms and a 16-column certificate took 611 ms.
The run reached a 39-column root permutation before timing out. The numeric
conversion itself now closes, including its post-conversion list simplification;
the remaining cost is proof construction, not a failed equality. Root rows
already have canonical order, so sorting them adds transport without reuse.
Child-level permutations remain useful and must preserve exact labels.

Replacing generated-code conversion with checked numeric projections still
regressed the complete run to 34 partitions. A 17-column certificate took
89 ms, and 156 certificates consumed 5,188 ms by an early checkpoint. These
figures include projection construction. The cold-column path now proves only
the selected raw node using checked child headers. Its final publication uses
the exact admission theorem rather than unfolding that guard again. The
remaining permutation scans still require removal; this run is not acceptance.

The expanded focused selection passed all 101 tests in 2.15 seconds.
Whole-tree quality passed before the
latest concrete-driver edits. The full Python suite finished within the
300-second budget: 9,171 passed, 14 failed, 2,103 validation-only deselected in
280.06 seconds. Failures are reverse/add completed-child accounting/routing
and special-source guarded output; no failing assertion was weakened.

## Rejected approaches

A structurally recursive list fold still re-certified every remaining suffix;
it regressed from 51 to 27 completed templates. Certified subterm reuse replaced
it. Cache-hit totals and partial template counts do not establish acceptance.

A single literal ragged store replaced 430 source declarations experimentally,
but expanded cold publication and projection setup. Its concrete build reached
the first partition only near the deadline. That migration was rejected; the
authenticated named-child store and its negative fixtures are retained.

Do not infer B1 authority from the downstream future instance, remove false
positions without an exact label embedding, bypass the shared policy, or delete
forest/fuel admission before the concrete replacement passes.

## Validation provenance

October 17 baseline at dirty Git HEAD `f31261a`: the guarded candidate,
producer-release-source and runtime-provider selection passed 92 tests in
19.45 seconds including runner overhead, with a sampled process-tree peak of
177,324,728 bytes and confirmed cleanup. Evidence is in
`results/runs/20261017T031337Z-2d45e78199c14eadb4b7cff69ba3ae70/`.
This is Python/development evidence, not a completed Isabelle build or
authorization to remove the forest gate.

The first operation-DAG integration passed its kernel fixtures but the concrete
B1 build still hit the standard 300-second session timeout. Run
`20261017T033219Z-1fad0b7ca8b84a2789cc79298dd65b94` took 313.47 seconds including
orchestration and shutdown. Its last profile recorded 5,251 shifted-apply calls
and 10,794 node calls; the new DAG reported only its startup fixture. This is a
failed integration gate, not evidence that the cache accelerated publication.
The source/cache regression selection subsequently passed 45 tests in run
`20261017T034309Z-2dd2fbd4024d44b9919161bef3df26b6` (2.30 seconds including runner
overhead). These static/behavioral checks do not substitute for the B1 build.

The local-cover bridge now obtains child wellformedness only for the exact
referenced Goto child. Its index bound is extracted from that slot's checked
reference; terminal slots do not require unrelated children. A separate generic
lemma obtains occurrence wellformedness from exact template geometry, binding
and supported-column facts. `Comma_Semantic_B1` rebuilt successfully in 57
seconds in run `20261017T035733Z-1df1e70924054b1280e2fba5fbc3b745`; the build
invocation including startup and shutdown took 68 seconds. This checks the
generic bridge, not its concrete publisher or the final global release theorem.

Run `20261017T040052Z-4fb5a3a5825f403395a9de7b612ee903` passed the new apply-DAG
fixtures and reached the concrete occurrence check, but exceeded the native
300-second session limit without stopping. The coordinator interrupted the
guarded invocation at 397.53 seconds; cleanup was confirmed and sampled peak
process-tree memory was 4,151,916,192 bytes. This is failed, incomplete evidence.
The interrupted build did not preserve its buffered DAG counters, so counts
from earlier runs must not be attributed to it. The outer orchestration limit
covered the dependency closure and did not enforce the stalled session itself.

The guard now also tracks inventory-admitted session start/finish events and
enforces the unchanged per-session limit externally. Repeated start events cannot
reset it, and the orchestration allowance cannot extend it. The guard/watchdog
selection passed 49 tests in 7.34 seconds in run
`20261017T041516Z-95628c2dd11d48f79e9dac4386c80c83`, covering descendant cleanup,
cancellation, split output and independent sequential session deadlines.

Initial validation of the piece-free generic replacement in runs
`20261017T041346Z-00f73bd41253488a83f83eb251775913` and
`20261017T041536Z-305c480277784a1ba3bce87101b1d229` failed respectively on an
unavailable list helper and a nested proof-goal mismatch. Neither was a timeout
or a concrete B1 pass. The compact source contract retains result-directed local
coverage, exact bindings and independently checked partition geometry; published
lift-column IDs still require their separate artifact-binding check.

The corrected compact generic refinement passed in
`20261017T041945Z-f6bb6036bf4d4a12b2e744407e29aa8b`: the rebuilt
`Comma_Semantic_B1` session took 72 seconds (83 seconds for the build invocation).
The checked contract has no construction-piece premise. It derives exact local
source behavior from shared template geometry, supported columns, source/shift
bindings and result-directed slot coverage. Concrete publication, B32/global
acceptance and runtime activation remain separate gates.

The concrete publisher and checker now use that compact contract. The obsolete
construction-piece projection module (498 lines), piece serialization, origin
sorting and grouped-piece checker components were deleted. Run
`20261017T042925Z-ecc4f4f2592a44e199473542895df920` passed the executed binding
reuse/rejection fixtures and all 278 mass certificates, then failed because the
new shared template-geometry list had no matching evaluator dispatch. Its
148-second build invocation was not a timeout. Saved counters show three
recursive apply certifications, eight hits and no fallback at that failure;
they do not establish end-to-end B1 performance.

The initial aggregate-dispatch repair shared exact template geometry and used-lift
certificates; the subsequent induction removes the geometry evaluator. Lift publication keeps the deduplication operation symbolic and
transports the checked item facts through `list_all_remdups`, instead of proving
concrete duplicate removal over the entire reference stream. The focused
source/authority selection passed 109 tests in 20.91 seconds in
`20261017T044014Z-b05f62d836394bc9844f8a4674ea93b6`. An independent coverage
review prompted a compact Goto regression with fixed result labels and changed
parent rebase or child net shift. Both negatives are checked by the kernel
fixture, alongside valid admission and warm certificate reuse.

Run `20261017T044128Z-dba28fc846e94d8a8a23434cdff82ae1` passed those fixtures
but exposed a redundant partition-proof path in the new geometry dispatcher.
It completed geometry entries 0 through 129 before the external session
watchdog stopped the build at 300.014 seconds; total invocation time including
shutdown was 310.183 seconds, sampled peak memory was 3,676,411,192 bytes, and
descendant cleanup was confirmed.

The replacement derives parent coverage by induction from the compact local
witness and already checked child occurrences, then derives disjointness from
the checked mass of 924. Generic `Comma_Semantic_B1` passed with this bridge in
48 seconds in run `20261017T050441Z-568b73cc9c61489093841a3d0f80469b`.
This removes the second concrete geometry certificate while retaining the
partition theorem; concrete B1 timing remains a separate gate. The driver also
replaces pairwise duplicate-ID scans with first-seen term-table lookups. Root
checks retain source/index/occurrence validation and obtain construction
validity from the aggregate source theorem rather than rechecking 46 roots.

Concrete run `20261017T050549Z-a3439c2dc7114aa6bd2720ebb1b84e14` rebuilt the
semantic future dependency in 32 seconds, completed all 278 template-mass
proofs and reused them for all 430 occurrences. It then failed the used-lift-ID
projection shape guard; the 206-second build invocation was not a timeout.
The projection conversion is being repaired without relaxing catalogue bounds.
The migrated source/authority tests passed 109 cases in 19.40 seconds in
`20261017T051127Z-6c168a48f5624e1fb5e4b4ad7a0867b6`.

The runner/provenance selection passed 68 tests in 12.49 seconds in
`20261017T042544Z-3f04d075188b43a7a010f8778fe12890`. Profiling now has a fresh
run-local file when requested with `COMMA_PROFILE_LOG=1`; explicit paths remain
caller-owned. The evidence manifest records the chosen path.

Baseline Git `7e9a85d` was clean. All later results below are dirty-tree
development evidence, not acceptance of a commit. The standard runner enforces
300 seconds per Isabelle session (updated by user request on 2026-10-12),
6 GiB aggregate memory, four prover threads
and one session at a time. Python runs retain 60 seconds per test and 300 seconds
per suite under 4 GiB.

Commands use `devtools.checks.release`. Proof selection:
`--suite proofs --session Comma_Semantic_B1_Instance`, with `COMMA_PROFILE_LOG=1`.
Focused unit selections cover column authority, semantic future, producer
bridge, future provider and global prefix admission. Full suite: `--suite unit`.

| Run | Result |
| --- | --- |
| `20261011T160518Z-da8f629baa0f4c768b7dc058a645e0df` | Clean baseline B1 timeout; 54 template partitions |
| `20261011T175942Z-59553a06d2134fc789e50ce6aa9438bb` | Generic B1 33 s; generic Future 30 s; concrete integration error |
| `20261011T180203Z-43df0ff46a9c4c29b84c2b735850f19b` | Concrete B1 timeout; 51 partitions |
| `20261011T180431Z-67b84f42f21b4b2c8ce19ffc6add7a4b` | Typing, lint, formatting, policy, documentation, proof inventory and package checks pass |
| `20261011T181137Z-3e465af14b7a42d2b40502952352acca` | Rejected suffix-fold regression; 27 partitions |
| `20261011T181342Z-bbf5841967ce41d6934659e958f678d7` | Focused 90 tests pass |
| `20261011T181414Z-9a1914c4f70e4c248a2141f81ab71cf6` | Full units finish in 280.06 s; 14 failures |
| `20261011T182225Z-7f39837b6aa24f14a718a0fecd608eb7` | Concrete B1 timeout; 75 partitions |
| `20261011T185921Z-b7501a2abd3c4869ae5f45d7bcbca065` | Generic B1 with indexed-label witness lift passes in 35 s |
| `20261011T190619Z-4a3dc0b1f1034b67bef5523c2c4fc2d5` | Concrete compact-label B1 timeout; 50 partitions; compression and child-fold costs identified |
| `20261011T191805Z-67d661b48ef44d30a1c3bd2430bed4e4` | Structural indexed-label conversion: B1 timeout, 66 partitions |
| `20261011T192310Z-7bb1194d0efb4f8caa40bd50669845ae` | Generic paired-child induction passes in 34 s |
| `20261011T192519Z-e49f2776eca841d4840b48746b7cbb5d` | Paired-child concrete B1 timeout, 81 partitions |
| `20261011T193009Z-6236ddcc87494d87998846a354b05d69` | Generic existential partition-witness chain passes in 35 s |
| `20261011T193101Z-afaf099957c34be48686e6c52e91d84d` | Theorem-only cache: B1 timeout, 81 partitions; child fold 156 ms |
| `20261011T193950Z-73d304726a104075a06d9c67438b2d2a` | Generic B1 with directory interval transfer passes in 34 s |
| `20261011T194047Z-6b634d96edd043218da615b86fa0b773` | Directory interval reuse: B1 timeout, 86 partitions; at checkpoint 78, lookup 2,065 ms and compression 5,590 ms |
| `20261011T195746Z-55a1fe91603f4eb183b51ae9ffec97a6` | Generic offset-mask embedding, including retained-false and omitted-true fixtures, passes in 35 s |
| `20261011T200107Z-ffc7ac07275f472889680b518b277895` | Concrete B1 timeout, 82 partitions; offset-mask and dependency-certification reductions measured at checkpoint 78 |
| `20261011T200515Z-5d01efd11ef64675bb8a1b6738589417` | Focused authority, occurrence cache, future, producer and runtime admission tests: 101 passed |
| `20261011T203804Z-b8b4550bf563458f986e1d16db187974` | Generic B1 with exact sorted-witness transport and duplicate-column rejection passes in 35 s |
| `20261011T204236Z-d0d8401d434c46289e1b89b92ddeb10c` | Generic B1 with finite executable permutation equation passes |
| `20261011T205157Z-4b33df4a1d1e4b46a240d379e156a3f2` | Concrete B1 timeout; numeric permutation certificates close, repeated list-index work measured |
| `20261011T205939Z-1603d312452a4ae48bfaadce0ad36df8` | Focused authority and runtime admission selection: 102 passed in 2.13 s |
| `20261011T210203Z-c473c8761f354c6bb1fa85a24fd4f917` | Typing, lint, documentation, proof inventory and package checks pass; formatting and oversized fixture module require repair |
| `20261011T210926Z-56caed03498e408294f3a574d7070fdf` | Concrete B1 timeout at 34 partitions; numeric projection cost remains too high |
| `20261011T212059Z-8c6b8f6f99b14ed1b0ef9aa1938843b3` | Timeout in first numeric permutation; unrestricted recursive range simplification identified |
| `20261011T212527Z-9332cd34d2cd46ea9eaebfe5c49dc526` | Early fixture rejects unevaluated range after unsafe rule removal |
| `20261011T212745Z-9ddfb51e66bc4081aa41a96a38b2d1b9` | Early fixture reaches finite fold; missing Boolean simplification repaired |
| `20261011T212826Z-63e1145d1bf64c0c9121e6b02d31d5b5` | Concrete B1 timeout at 81 partitions; 393 shared states at checkpoint 78, permutation certificates 5,285 ms |
| `20261011T213233Z-91abc06e13f54b6288176d37433d9ef9` | Focused authority/runtime selection: 102 passed |
| `20261011T213434Z-61b0d48fc0744862a679713b8146cd7b` | Generic B1 with multiset witness transport: kernel build passes in 41 s |
| `20261011T214038Z-e2cd1cbc68e440e49afe407cc1bec0ca` | Generic Future passes in 32 s; concrete B1 still times out; transport certificates 438 ms at checkpoint 78 |
| `20261011T214533Z-899033477dfa491c80f2c2c43f166665` | Focused authority/runtime selection: 102 passed in 2.26 s |
| `20261011T214551Z-6b6ba6da1671449ba936bf8bb5a1fcee` | Whole-tree typing, lint, formatting, policy, documentation, proof inventory and package checks pass |
| `20261011T214840Z-5d80d69e603a4c97947cd136b2878803` | Generic admission/cofactor lemma passes; concrete negative fixture exposes an ML bound-variable typing error, then repaired |
| `20261011T215047Z-78c126d6806c462ba815ac090f191bd1` | Negative fixtures pass; concrete skip branch requires explicit successor/numeral normalization before rule application, then repaired |
| `20261011T215221Z-f8bd2877052b431d83835dbd2c3dbed8` | Skip-rule conclusion normalized but premise remained symbolic; full premise normalization repaired the integration |
| `20261011T215405Z-c2d6a7c5881b45d29ec01f5b751f7527` | Concrete shortcut accepted, B1 timeout after 83 root partitions; checkpoint 78 vector proofs 7,667 ms, transport certificates 411 ms |
| `20261011T215542Z-95b4f1b7f57e4a4f82c76f3614d73521` | Final focused authority/runtime selection: 102 passed |
| `20261011T215754Z-ac0428fb34424fa99b1298ee98369d37` | Final whole-tree typing, lint, formatting, policy, documentation, proof inventory and package checks pass |

## Remaining work

Validate the compact concrete B1 driver, then B32 and the global producer chain.
Independent review confirms that source-piece partition plus one-way containment
does not establish parent geometry: overlapping parent cells remain a real
counterexample. The new constructor bridge preserves result-directed coverage
and requires the ordered sum of parent-column cardinalities to equal 924.
Counting the ordered list preserves multiplicity, so overlapping or duplicated
nonempty columns cannot pass. The inverse rebase transports coverage without
repainting the parent. These parent-partition lemmas passed kernel checking in
development run `20261012T005938Z-fdbe416ec5c24c62a71ef7c520aa6e82`;
the complete session did not pass.

CRT phase replacement, later-coordinate evaluation invariance, cofactor
partition preservation and inductive checker completeness passed kernel
checking in development run `20261012T011345Z-888378ae393940888f93ad4f9a8540aa`.
Exact projection and specialization rules replace broad automation in terminal
coverage and parent-bound extraction. The residue-cardinality and ordered-mass
lemmas also passed kernel checking in development run
`20261012T015600Z-6e523adf8c7e45cda21ee368d2893271`. The complete generic
`Comma_Semantic_B1` session then passed in 48 seconds in development run
`20261012T021128Z-2e228e037e23484db4302869b7cb9ce5`, including source-order
constructor refinement. The catalog wrapper had incorrectly used named
conclusion labels as propositions; explicit quantified conclusions repaired
that failed proof search. This does not yet certify the concrete B1 instance.

Concrete publication is being changed to checked template masses at source
owners and exact bindings for used Goto lifts. Its numeric mass calculations
still require kernel certificates; the ML constructor's counts are not proof
authority. The concrete mass route remains over budget. In development run
`20261012T023213Z-8a414ebcedab4a40a590451696b84586`, the last diagnostic
checkpoint contained 70 certified template masses and 1,449 distinct column
mass proofs. Local mass proof time was 931 ms, compared with 3,471 ms at the
same checkpoint in `20261012T022658Z-e4b1897044cf4eacad2252f6bd5e307d`.
The session still timed out: inclusive template work was 10,981 ms and column
step work was 3,976 ms. These are component measurements, not a passing B1
bound. Fixed proof contexts now have owner-local lifetimes, and closed step
equalities are transported structurally rather than starting a fresh tactic
proof for each mass node. Exact equation, context and oracle checks remain.
The next run, `20261012T024029Z-81c4c18e0dbb43ffa763b1a4c1a4f6e4`, also
timed out at the 70-template diagnostic checkpoint. Reusing exact level-bound
proofs reduced column admission time from 1,992 ms to 1,115 ms. Its new phase
counters separate 112 ms selecting ID rows, 5,832 ms requesting column masses,
3,960 ms proving complete template rows, and 188 ms transporting requested CIDs.
The driver retains ordered arithmetic occurrences and reuses the checked ID-row
equation during the final row proof. Remaining concrete work, rather than cache
capacity or generic CRT completeness, still prevents acceptance.
The unused parent-extraction adapter and duplicate grouped-cover wrapper were
removed before publication, with their claims retained in the shared parent
bridge. Original occurrence theorem signatures are preserved by wrappers around
the shared partition-or-mass proof. Static assertions for source origins and
coverage now inspect that shared owner. The focused selection passed 111 tests
in 2.33 seconds in development run
`20261012T020103Z-89ff98bcc82942a69a82ce7e4c6f3521`. This is source-contract
and runtime coverage, not acceptance of the unbuilt concrete certificate.

The next repair separates arithmetic proof sharing from column authority.
Generic mass-step transport consumes the exact decoded node and its ordered
child-mass equations. Numeric schemas are shared by level and mass vector;
row sums are shared by mass multiset with multiplicity preserved. Exact row
resolution remains a separate premise. Publication checks the distinct used
template catalogue once and transports it to each source descriptor. It no
longer asks for a template theorem through every source index. The row checker
explicitly disables inherited recursive sum rules, requiring its cached
numeric equation. Foreign-column and repeated-child fixtures preserve the
authority boundary.

The extended generic `Comma_Semantic_B1` session passed in 48 seconds in
development run `20261012T032921Z-3f94d752b96445698a9801b102f42e35`.
The preceding run exposed and repaired two proof failures in list membership
and multiset-sum transport; it is not passing evidence. Source-policy checks
for the changed mass and occurrence owners passed 31 tests in 0.98 seconds
in `20261012T032855Z-05f162df254346f39927ed0666ec7b9e`.

The later audit found a missing `Column_DAG` import in the new mass-transport
theory: its intended decoder name had been parsed as a free function. The
explicit import repairs the executable connection. Earlier generic builds do
not certify that corrected connection. With the import, development run
`20261012T040443Z-f7b95bf9876f4d03aae05aec794028ea` passed
`Comma_Semantic_B1` in 53 seconds and `Comma_Semantic_Future` in 36 seconds.

Concrete B1 still exceeds its 60-second session limit. The structural mass-map
implementation compiled in
`20261012T041814Z-d7f756ae50d64e11802a03869d4f323a`, but the instance timed out
after 52 templates. At the 48-template checkpoint, mass requests took 3,747 ms
and row certification 2,091 ms, using 27 numeric histogram schemas. Source
discovery took 12,392 ms and artifact definitions 11,996 ms. This is not a
measured improvement over the preceding run. Initialization variability and
partial checkpoint counts cannot establish a complete-session bound.

The exact ordered mass map now uses kernel list congruence instead of a
recursive simplifier call. Its row sum composes that equation with a separately
cached arithmetic proof. Independent review retained catalogue authority,
bounds, row resolution, order and duplicate multiplicity. The focused runtime
and source-contract selection passed 152 tests in 14.11 seconds in
`20261012T041949Z-c8d6bb5e005a467abf56a59e32b22690`.

A scalar Python-chart induction bridge is registered and connected to the
B32 release statement in source, but has not passed kernel validation. It
does not cover the grouped `classify_near_port` classifier. Both the concrete
B1 gate and that executable grouped-classifier obligation remain open. All
runs above are development evidence for dirty work based on Git commit
`7e9a85df6610a948f99bd89d15fc310995991f5d`, not reusable acceptance evidence.

The artifact registry remains empty, and forest/chart
move gates remain active. Generic proofs and Python tests do not authorize
removing those gates.

The next generic map bridge preserves exact catalogue authority, ordered ID
resolution and all bounds while avoiding per-column `list_all2` normalization.
Its checked version passed with generic B1 in 51 seconds and Semantic Future
in 36 seconds in `20261012T043334Z-d365ade0a7b7464cb0be9ad4545f65df`.
The intermediate attempt used a nonexistent list lemma; this was corrected to
`list_all_length`. Concrete testing also caught two ML shape errors: a Boolean
equation required `Trueprop` congruence for proof transport, and a comparison
under an abstraction required an explicit type instead of `fastype_of` on a
loose bound variable. Both were repaired before the final timed probe.

In `20261012T043904Z-b9e33514d117408583e8e72f569b0c56`, the same 80-template
checkpoint measured 226 ms of total row certification, including 199 ms of
bounds, 21 ms of structural mapping and less than one measured millisecond of
resolution transport. The earlier 80-template checkpoint in
`20261012T041320Z-a1e1b5d042fe497191ade184fb762097` measured 3,433 ms.
The aggregate counter now includes all moved components; the earlier isolated
4-ms sum-proof reading was not comparable to the former row total.

The final concrete session still timed out at 60 seconds. At the 2,560-column
checkpoint it retained 2,559 completed mass entries, recorded 11,692 hits and
zero capacity refusals. Exact column-step work was 7,031 ms, local mass proof
work 1,388 ms and numeric-schema work 1,161 ms (the latter is part of local
proof work, not additional time). Source discovery took 8,171 ms and 99 column
block definitions took 6,868 ms. This identifies remaining cold lookup and
publication costs; it does not prove a complete constructor bound.

Catalogue readers now return their already authenticated meta equations, and
lift consumers no longer normalize those equations again. The final imported
oracle audit remains mandatory: several bundles are checked there for the
first time and cannot simply be removed. The quality run
`20261012T042944Z-1748ce8e09824ed88dd0968f2807e9d2` passed typing, pinned lint,
formatting, source policy, documentation, proof inventory and packaging.

The final focused selection passed 153 tests in 13.93 seconds in
`20261012T044137Z-e1078cb6c8e541eb8f2706c4b56065c5`. The preceding selection
had one obsolete source-shape assertion: it required passing both selected
row equations to a simplifier. Its replacement requires structural composition
of those same exact equations, preserving the assertion's authority contract.
No runtime or mathematical assertion was removed. New shape checks cover
explicitly typed bound variables and `Trueprop` transport.
The final quality rerun also passed all seven checks in
`20261012T044202Z-0142adf84d3644ec9da7bf90b6fd8c0d`.

The shared annotation theorem subsequently passed kernel checking in
`20261012T053832Z-31a486a0a2574bbab1107e4f979b368f`: generic B1 took 55 seconds
and generic Semantic Future took 40 seconds. The annotation contract preserves
exact DAG authority, ordered child multiplicity, strict child descent, levels,
radix arity and mass recurrence. Checked negative instances reject missing or
forward children, deduplicated mass, wrong arity and foreign extent.

Concrete source certification now transports 61 checked block intervals for
the 31,073-node demanded closure instead of producing a source-lookup theorem
for every node. In `20261012T061554Z-888b52b597fd4ecf86b1da58743d7a57`, candidate
construction took 77 ms; source bindings completed at 1,651 ms from that same
start. These cumulative timings must not be added. Binding authority checks
preserve exact base, extent, block definition and interval theorem.

That concrete session still timed out. All 31,073 height proofs were reached,
but only 8,192 ordering nodes were completed at the last checkpoint; row
validity had not started. The ordering cache recorded no hits and has been
removed without changing the proposition being proved. This is an identified
cost removal, not evidence that concrete B1 now passes. The directed mass-row
helper is under fixture validation and is not the live annotation row owner.

The scalar-to-grouped chart bridge is now registered and connected to the B32
release theorem in source. Its concrete kernel build remains blocked behind
B1; source registration is not proof acceptance. The focused source-contract
selection passed 18 tests in
`20261012T061428Z-8dacf77a46914df1b3b00f8edf74369f`. Replacement coverage maps
the former per-CID source-lookup shape assertion to exact authenticated block
intervals; no output or mathematical assertion was removed.

Current gates remain: generic mass induction checked; concrete B1 timed out;
B32/global and grouped runtime refinement unaccepted; production forest and
fuel retirement blocked. These dirty development runs use the same Git HEAD
listed above and do not certify a release commit.

The next integration replaces per-node height and ordering certification with
the shared midpoint-layout theorem. The generic B1 session rebuilt in 48
seconds and Semantic Future rebuilt in 31 seconds in
`20261012T073645Z-8f9d88788c354820806f376f55478e51`. That invocation did not
validate the concrete instance: its source-digest check rejected an ML helper
edited after the build started. Later probes use a frozen proof source.

The concrete checker now uses one theory-owned annotation constant. Its row
proofs no longer retain a full-tree equality assumption, and source rows use
the authenticated block intervals. Duplicate callback validation and an
intermediate oracle scan were removed; exact row checks and the final
certificate oracle audit remain. The old node-by-node height/order loop and
its unused simplifier setup were deleted.

Kernel fixtures caught and corrected two distinct integration errors: list
normalization omitted the radix lookup rules, and the alias validator
incorrectly required annotation rows for terminal CIDs 0 and 1. Those
terminals have independent checked mass equations; nonterminal roots still
require exact body membership. Missing, negative and duplicate roots and
invalid extents have separate rejection fixtures.

`20261012T074334Z-d681a80746f242178415b51a1261aa30` still timed out at the
native 60-second limit. It reached the full 31,073-row layout input but did
not finish the sortedness/bounds proof. This measures a remaining concrete
consumer cost, not a failure of the generic layout theorem. The replacement
uses carried certified list nodes and local arithmetic instead of whole-list
simplification; its concrete performance is not yet accepted.

The focused Python/source-contract selection passed 44 tests in 12.11 seconds
in `20261012T073957Z-5c79a344c8a040eabdb222b18beed8b1`. The replacement shape
test maps the removed height/order loop to the exact midpoint builder
equality and wrong-shape/payload rejection fixtures. These source checks do
not substitute for the concrete kernel gate. B32/global acceptance, runtime
artifact admission, and forest/fuel deletion remain open.

The later cold probes refine that attribution. In
`20261012T075241Z-9dbab64329d646fb954e67d3cfff2f0a`, layout parsing began about
55 seconds after the first fixture marker; the timeout cannot be assigned
entirely to layout. In
`20261012T075814Z-a9f4447d6b1e45c7b9c5170ff05e159c`, the native session timeout
occurred before layout. The 480-definition artifact batch took 15.477 seconds,
including 430 separately named construction-piece sources. The helper fixture
measured in the preceding run took only 76 milliseconds; the surrounding gap
was not evidence of an expensive fixture loop.

The next repair targets both representation costs: direct exact-subtree
layout certificates replace row-list sorting and midpoint reconstruction;
checked construction-piece blocks replace per-source constant publication.
Neither change authorizes forest/fuel retirement before the concrete B1,
B32/global and runtime consumer gates pass. The obsolete non-midpoint-layout
fixture is replaced by interval, duplicate-key and AVL-shape checks: midpoint
shape itself is not a semantic invariant. Wrong-mass coverage remains with
the mass-row checker, and exact payload binding remains with theorem/source
authority validation.

The direct-layout source contract passed all 18 tests in 0.32 seconds in
`20261012T081553Z-3e060792f7844a77b5d301d42c709e45`. Its negative fixtures now
require the intended bounds/balance/extent error, instead of accepting every
non-interrupt exception. Child cterms are reused and each returned height is
normalized to a numeral before its parent consumes it. The old midpoint
proof chain was deleted; the generic layout theory is 88 lines.

The generic rebuild in
`20261012T081214Z-98fb53bade8d409389ddf28cf6804085` itself timed out under the
unchanged 60-second session policy before reaching the new layout theory.
Its sampled peak was 2,370,666,968 bytes; descendant cleanup was confirmed.
The prior 48-second generic result is therefore not current acceptance.
This remaining generic cost and the concrete publisher are audited
separately; neither result permits retiring production admission gates.

Construction-piece publication now groups the unchanged ordered source rows
into blocks of 32, reducing 430 per-source definitions to 14 block definitions
plus their directory. The selector authenticates canonical names, exact
root/directory equations, block order, total source extent, and each source's
row extent. Cached selected-source theorems remain bounded and context-owned;
locator steps and cache retrieval/build counts are separate measurements.
The duplicate oracle scan inside catalogue admission was removed; the source
bundle audit remains.

Assertion disposition for that storage migration: the old literal
`! source ! row` source-text assertion is replaced by the exact nested `nth`
fixture through the shared block selector; the old `HOLogic.mk_list sourceT`
root assertion is replaced by checked concatenation of canonical source
blocks. Reordered/foreign definitions and incorrect source-specific extents
remain rejection cases. The first focused run after migration was 43 passed,
2 stale representation assertions failed
(`20261012T082737Z-fb73af768447481786145403b48adc38`); those two assertions were
then migrated with the equivalent coverage described above.

The migrated source-contract and runtime selection passed 45 tests in 12.10
seconds (`20261012T083253Z-57809621b9524d83808d69fcd60c69e4`). The subsequent
kernel run (`20261012T083335Z-e0a9bd163dc84a6ba7d276885daf72c7`) failed at the
generic parent-bound conjunction extraction, rather than at the session
timeout. The direct-layout lemmas were checked, but concrete ML publication
was not reached. These source tests therefore do not certify the new concrete
publisher or authorize the runtime cutover.

The direct-layout helper now rejects open annotations, wrong term types and
column extents below two before certification, independently of its caller.
Its fixtures require the corresponding error category. This owner selection
passed 19 tests in 0.28 seconds
(`20261012T084430Z-b43eb6f87e7b4fc6b87f4c734ba1d1ad`). A concrete ML call to
`Int.max` was also corrected to its tupled signature during preflight review.

The generic `Comma_Semantic_B1` session rebuilt successfully in 43 seconds in
`20261012T084953Z-bd4997cb1c2c4271933eb4adcdc73861`, under the standard
60-second/6-GiB/four-thread policy. The parent-bound extraction now rewrites
the proven admission guard directly, preserves descriptor conjunction
grouping, and projects nonempty/distinct bindings separately. This is generic
proof acceptance; concrete publication and downstream release gates are
reported separately.

In that same run, the generic `Comma_Semantic_Future` dependency rebuilt in
31 seconds. Concrete B1 compiled the direct-layout checker and passed its
small shape fixtures, then failed at a construction-piece projection fixture.
The artifact batch contained 65 definitions and took 9.149 seconds, compared
with the earlier 480-definition, 15.477-second batch. These are single-run
development measurements, not full concrete or global acceptance.

The selected-source length reducer needed the existing
`comma_selected_length_cons` equation after opening its authenticated source.
The next run (`20261012T085528Z-8297880eb73e43ffb19c8ce0e302ae0f`) passed that
projection and reached the later out-of-range row fixture. Its expected error
was migrated from the retired generic depth-bound message to the new
source-specific extent message; the invalid request still must be rejected.

The concrete direct layout completed all 31,073 annotation nodes in 10.54
seconds in `20261012T085840Z-9cb3bec5bc1342078482d088818bdba3`. Its height
cache built 16 exact scalar certificates and reused them 31,057 times. The
complete session nevertheless timed out after layout. This establishes that
the giant row-list/midpoint-reconstruction obligation was removed, not that
B1 or the downstream forest cutover passed.

The following change carries certified subtree terms through mass-row
validation and replaces per-row proof-goal setup with an exact rewrite to
`True` followed by kernel equality elimination. It checks the exact requested
left side, closed premises and result; child multiplicity remains unchanged.
Run `20261012T090644Z-bf4c142d9e1a48a4a2fb7e9682496ee7` caught an ML wildcard
syntax error, which was repaired. Run
`20261012T090738Z-a14715a4dcc84c639c53b44a9a77ce39` compiled the repair but
timed out during layout after slower publication/setup. Neither run reached
mass-row completion. The standard limits and forest/fuel gates remain intact.

The focused source-authority/runtime selection passed 46 tests in 12.18
seconds (`20261012T091655Z-5631284accc4482ba8984b8e0a4080a5`). The assertion
for certified left/right child terms was migrated from the retired
`instance_ct` helper to typed kernel instantiation; it still requires the
exact child cterms. New checks require direct row rewrites to preserve their
left side, close all premises and return `True` before equality elimination.

The shared interval-transport lemmas passed in `Comma_Semantic_B1` in 59
seconds (`20261012T091739Z-e01b822da7b64741bfb3770693c70624`); this has little
timing margin. `Comma_Semantic_Future` rebuilt in 33 seconds in the following
run. The concrete consumer now collects exact named-root lookup equations in
one tree traversal, retaining exact HOL interval terms and separate integer
bounds. It does not put the complete concrete tree into each row request.
Integration checks corrected an undefined equality-rule name and moved the
layout helper before its row-fixture consumer. The wrong-mass fixture now
requires the specific row-predicate rejection instead of accepting any ML
error. Concrete acceptance remains separate from these generic proof results.

Run `20261012T092338Z-2fe067f542d34285bd2a985077df1107` completed direct layout
in 8.01 seconds and all 31,073 named-root interval lookup facts in about 7.6
seconds, then timed out after 1,024 row proofs. Those row checks averaged
about 4.5 ms each. This is a measured remaining bottleneck, not evidence that
the complete constructor passes. The replacement source-row helper composes
each checked directory interval with its exact block definition once and
derives point equations in one traversal, preserving original child vectors.

The generic rebuild in `20261012T093246Z-05a18a00cb7d475d867bf10393388c6a`
also timed out, before loading the new source-block transport lemmas. Its
slowdown is distributed across earlier proof stages compared with the
59-second passing run; no isolated failing tactic was established. Both
results remain development evidence, and the generic session has insufficient
measured timing margin. The 47-test selection passed in 12.66 seconds in
`20261012T092927Z-0851726477714131ba9f9127d30e3799`, before the source-block
helper integration; it does not certify that later change.

The user authorized a repository-wide increase after the concrete 60-second
failures. Validation policy 2 now uses 180 seconds per Isabelle session; Python
remains 60 seconds per test and 300 seconds per suite. Earlier run limits and
outcomes above are historical evidence and have not been rewritten.

Run `20261012T093552Z-72f63065ece6475899d2ae6ccab83a9a` rebuilt the generic
B1 session in 50 seconds and the generic future session in 31 seconds. Concrete
B1 completed direct layout in 8.79 seconds but timed out in source-row proof
construction. Run `20261012T094645Z-da90d2223b00483eac0c54b969e449bb` compiled
the typed shared-rule instantiation repair and reached source block 27,650
before its 60-second timeout. These runs do not establish concrete acceptance.

The current change shares a single node-split theorem for lookup transport and
introduces an exact ordered-child summary before row validation. Missing
nonterminal lookups remain `None`; terminal 0/1 masses remain separate; repeated
children remain repeated contributions. The first 180-second-policy rebuild,
`20261012T095429Z-577a35354124458fb9b2fc4987edb83e`, rejected a new scalar name
that collided with Isabelle's multiset `count` constant. This is a source error,
not a passing proof or a timeout. The replacement remains under validation.

The generic summary and direct row-refinement lemmas passed the kernel in
47 seconds in `20261012T100341Z-ee351809ca794767aa7426b8d6200155`.
The seven-file focused regression selection passed 85 tests in 17.74 seconds
in `20261012T095934Z-4ff9826d0bac42a8af801aba6d3417b8`.

Concrete run `20261012T100640Z-1884d82801934865a77b47f376ff9907` completed
all 31,073 mass rows and their validity/soundness bridge. Row-summary checking
accounted for 87.12 seconds; the complete validity phase took 116.94 seconds.
It reached the 278-template checks and timed out at template 3 under the
180-second policy. This is progress through the former mass-row blocker, not
concrete B1 acceptance. The user also authorized a five-minute limit if three
minutes proved insufficient. The central policy is therefore moving to
300 seconds per Isabelle session, retaining 6 GiB aggregate memory, four
prover threads and one building session. Python limits are unchanged.

The five-minute policy is now version 3. Guarded policy/runner validation
passed 37 tests in 5.72 seconds (`20261012T101449Z-1927645a381a4b0798912141b462b322`).
Independent review confirmed all active Isabelle consumers use the central
limit; no registered ROOT overrides were found.

Mass-row validation now returns its immutable, exact named-root lookup
provider to the same mass owner. Template requests reuse those point proofs;
missing or out-of-range IDs fail closed, and terminals remain separate. The
callback-taking constructor is private, preventing arbitrary external theorem
providers without rescanning the entire proof dependency graph per lookup.
The small fixture separately rejects missing and out-of-range IDs. A source
test initially expected the wrong diagnostic spelling; that test was corrected.

Run `20261012T101759Z-21a9cfd3ccd74457a3de0eeb065daeb9` reached 186 template
proofs, taking 4.212 seconds combined, with 3,654 exact lookup reuses. It failed
on the previously unvisited true-terminal mass simplification, not a deadline.
Sampled process-tree peak was 4,162,258,808 bytes; cleanup was confirmed.
Adding the explicit Boolean conditional rules allowed all 278 template proofs
to pass in `20261012T102140Z-41eccbb1d16c4be7a63c756e225588e6`. That run failed
at the following exact `list_all` fold contract, after 2:55 native elapsed
time. Concrete B1 is not accepted by either run; B32/global and forest/fuel
removal remain gated.

The final fold repair uses exact-term conversions, avoiding schematic-index
renumbering caused by composing theorem rules before instantiation. Its small
fixture executes when the ML file is loaded. Run
`20261012T103449Z-77c0b2ceea704fa49e15b9963d59dc6d` passed that fixture, all
278 templates (5.277 seconds of template proof work), and the exact catalogue
transport. The concrete set-inclusion transport cost 12.927 seconds. It then
hit the native 300-second deadline during subsequent occurrence checks:
24,576 misses were reported while the positive memo remained at 7,935 entries.
This is a new measured stage, not B1/B32 acceptance. No global or runtime
admission claim follows from the passing intermediate proofs.

The follow-up removes the concrete set-inclusion proof entirely: each original
occurrence ID selects its exact already-checked distinct-item theorem, and the
same structural fold produces the literal `list_all` theorem. No semantic item
is re-proved for a repeated occurrence. The exact remdups and named-catalogue
transports remain unchanged. The occurrence memo audit also found that its
combined 8,192-entry capacity stopped admitting completed facts permanently
once filled. Bounded replacement and stale-negative-marker cleanup are being
validated; no performance result is claimed for those edits yet.


The bounded memo replacement now uses synchronized exact-term storage with a
shared 8,192-entry limit for completed facts and incomplete markers. It evicts
the least recently used completed entry instead of permanently refusing new
completed facts. Successful publication removes a same-key incomplete marker;
authoritative store lookup precedes negative-marker suppression. Load-time
fixtures check refresh order, eviction, partial capacity and negative-to-positive
publication. The evaluator's active-request recursion guard is unchanged.

Run `20261012T105307Z-ff34fea0fe5e4f3d942e4f5786320b7b` passed the new LRU
fixtures, all mass rows and all 278 template proofs. The original occurrence
list reused 430/430 checked item facts; its transport took 683 ms, versus the
previous run's 12.927-second concrete subset proof. The memo continued
publishing after reaching capacity: the final checkpoint recorded 18,842
publications, 10,907 evictions and 7,935 retained completed facts alongside
257 incomplete markers. These counts establish replacement behavior, not
end-to-end performance acceptance.

The session still hit its native 300-second timeout during subsequent
occurrence evaluation; the last reported operation was
`comma_crt_apply_shifted`, before source binding began. Guarded elapsed time,
including build shutdown, was 316.354 seconds; sampled process-tree peak was
3,971,913,496 bytes and descendant cleanup was confirmed. The five-minute
limit remains the central policy; it is not extended again. Concrete B1/B32,
global acceptance and production forest/fuel removal remain blocked.

The final focused cache/proof selection passed 50 tests in 12.31 seconds
(`20261012T105245Z-7c52a41b6f3247d1a0865e62ddf0a628`); policy/runner checks
passed 37 tests in 5.46 seconds
(`20261012T104926Z-670933a3c8e14dcda5415443ba438cd0`). Quality run
`20261012T105909Z-7f4eb0927361472a90a2d2a9b69f1c54` passed typing, Ruff,
source policy, documentation, proof inventory and installed-package checks.
Its sole formatting failure was the layout of the new pairwise timeout-option
assertion; that layout was corrected before the final quality rerun. All
results remain dirty-tree development evidence at Git HEAD `7e9a85d`.

Final quality rerun `20261012T110108Z-a06a76001fcd4f8aa31ec2e05c3907af`
passed all seven checks: strict typing, pinned Ruff, formatting, source policy,
documentation, proof inventory and installed-package validation. The concrete
Isabelle timeout above remains a separate release failure.
