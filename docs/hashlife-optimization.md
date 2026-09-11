# Tile cutover and optimization plan

## Current execution boundary

Public reverse-add, physical Collatz, and supported generic compositions now
construct the canonical tile/result/scheduler stack. The former family runtime
builders have been removed. Finish the remaining radix admission and remove
retired private execution dependencies; do not restore a continuation fallback
while tuning performance. Current checks and limitations belong in
[release status](release-status.md), separately from historical checkpoints.

Retain one scheduler and four distinct identities: source-independent action,
exact tile content, bounded local interface, and certified profile-bound future
behavior. Required causal regions, including a whole sibling when justified by
the recurrence, remain permitted exact canonical tiles. Flat future words,
generation itineraries, packed carry history and unrelated completion remain
forbidden.

For reverse/add, the source-independent action is a product of three execution
layers. None may stand in for either of the others:

1. **Algebraic sector transport.** Store symbolic branch-dependent `q`, `r`, and the canonical product of
   every reverse/add Frobenius/cyclotomic sector admitted by the kernel
   certificate. A sector contains its reduced unit action, 2-adic valuation and
   projected affine innovation. Temporal composition composes these sector
   records directly before spatial descent.
2. **Bounded local behavior.** The mixed-radix `(alpha, beta, nu)` output law,
   the LT/EQ/GT `CarryFn` monoid, normalization, halos, activity and growth form
   the executable bounded interface. Profile-bound Myhill--Nerode aliases may
   merge only complete consumer behavior proved successor-closed.
3. **Exact spatial result.** Canonical source and future `TileID`s retain exact
   output content when requested. A completed result also retains outgoing
   contracts and cocycles. Exact content equality is independent of sector and
   interface equivalence.

The first layer is not a single `mod32` or `source_annihilated` flag. For each
certified power-of-two sector `m`, it retains a canonical descriptor equivalent
to `(rho_m, v_m, B_m)`, where `v_m = q + floor(r / m)`. Source dependence may be
removed from that sector only after its own modulus-precision annihilation
condition is proved. The exact output morphism, another live sector, and the
input tile binding keep any source dependency they still require. H=20 is an
aggregate theorem observation assembled from powered actions; it is not this
product and cannot replace it.

An action's repetition count cannot determine numerical `q`, `r`, or `B`.
The carry-domain interfaces determine growth and forcing; these are available
local observations, not missing mathematical input. The tile-sector consumer
now derives the complete bounded affine product from executed interfaces
without requesting a complete endpoint or an event itinerary. The separate
source-independent plan remains a symbolic bound. Do not count derivation of
an affine product as avoided causal work unless a consumer actually uses it
to discharge an otherwise unresolved dependency.

The current `ReverseFrobeniusPlan` integration is intentionally narrower: it
records the branch-independent lower bound `min(5, floor(N / m))` for sectors
`m = 1, 2, 4, 8` on homogeneous decimal powers. That is a certified
source-coefficient death predicate. It contains no live unit action or affine
innovation and therefore does not complete the algebraic sector layer above.
Its composition counter is compiler metadata, not evidence that the scheduler
executed a sector quotient. The legacy family arenas likewise report
`*_source_annihilation_derivations` when composition proves a dead source
coefficient; those compiler facts do not increment the schema's executed
`source_annihilations` counter.

The new [decimal research summary](research/reverse-add/decimal-pair-algebra.md)
supplies a concrete local-output optimization. It changes the arithmetic
implementation inside this stack, not the representation or public routing.

The [carry-domain research update](architecture/carry-domain-quotients.md) adds
two concrete constraints to this work:

- **Reduce reverse transport and birth together.** The supplied collision
  witnesses have different sources, carry fields and transport terms but the
  same combined successor. An unreduced `(transport, birth)` product must not
  become exact output identity. The tile runtime's combined output leaves and
  canonical children already provide the appropriate publication boundary;
  retain the new witness and warm-consumer regressions when optimizing it.
- **Reuse the existing carry algebra for Collatz.** Eligible radix multiply-by-3
  carry factors into two `CarryFn` wires, with `+1` as the incoming port. Five
  nonempty actions and a distinct empty identity suffice for that spatial carry
  law. Its metadata construction is now bounded independently of radix. A
  carry-response jet, frame gauge and projected 576/1152 action remain distinct
  from exact output and physical-time weights. Integrating their observations
  into deeper consumers must preserve these distinctions.

The immediate optimization removes two unused full-interval transfer requests
when a causal region consists of one canonical tile. There is no internal
midpoint in that case. Multi-piece dependencies still require their two-sided
transfers. The dedicated scan-poison tests cover both directions and unequal
noninitial exteriors. Measure these task reductions and the once-per-parent
fused-context traversal before claiming any improvement in the cold scaling
exponent; neither is a substitute for complete active-consumer reuse.

## Delivery sequence

0. **Stop uncontrolled diagnostic allocation.** Use the shared
   `devtools.checks.process_guard` launcher for expensive checks and probes, with
   one worker group at a time, a default 1 GiB measured group-footprint limit,
   and the existing 35-second probe deadline. Terminate the group, verify no
   live members remain, and reap the direct child on failure, interruption or
   timeout. A tool yielding a session
   is not a timeout. Measure macOS physical footprint rather than RSS alone;
   compressed/swapped allocations can hide behind a small resident count.
   The watchdog samples memory and can overshoot between samples; it does not
   replace arena reservations or establish an exact peak. Do not repeat the
   wide-radix allocation failure until bounded composition replaces the cause.
1. **Stabilize the public tile route.** Preserve heterogeneous input/midpoint/output
   alphabets, separate producer/consumer contracts, outgoing carry/remainder,
   physical ticks, event counts, normalization and frame deltas. Wide-radix
   division must use symbolic bounded remainder laws in the same adapter;
   enumerating a table proportional to the radix is not acceptable. Preserve
   P⁴/P⁸ noncommuting/noninitial-port and exact/fused differentials.
   Compact kernel admission alone is insufficient: composing a universal
   64-bit remainder BDD created millions of allocations in diagnostic runs.
   The parent now uses a closed modular-affine remainder transfer and activation
   threshold in the existing quotient arena. Both the output law and the carry
   law remain present. Boolean activity functions discard unobserved remainder
   coefficients, so equal activation thresholds share the same representation.
   Later division powers decline the incompatible primitive-pair BDD shortcut
   and continue through the same causal scheduler. Preserve and extend this
   bounded path; keep exact quotient output separate from carry equivalence.
   Declared domain cardinality is neither allocated state population nor work.
2. **Install the factored decimal leaf law.** Exhaustively verify the 19 valid
   `(alpha,beta,nu)` encodings, 38 carry/normalization cases, all 100 digit-pair
   combinations, all local two-carry cases, and growth rewiring against the
   existing exact pair recurrence. Compile the F₅ phase and Boolean full adder
   with existing semantic functions and the shared CarryFn monoid. Keep base
   2–5 regressions; decimal factoring is not a replacement for their laws.
   Reuse existing primitives rather than adding an independent state hierarchy.
   Decimal spatial parents now use closed arithmetic left/right/output functions
   instead of repeated Boolean substitution. Preserve the exhaustive finite-port
   comparisons, fixed construction-workspace charges, and nondecimal generic
   kernel coverage when removing the superseded decimal compilation path.
3. **Connect local output to parent reuse.** Spatial composition consumes child
   transfers in physical carry order. Temporal composition substitutes the
   factored output law through both midpoint contracts. Preserve the balanced
   action DAG; never expand `pair_steps` into a stage itinerary. Early parent,
   interface and boundary-result probes precede admission, reduction and
   descendants. Promote already completed children without forcing missing
   siblings or complete intermediate roots.
4. **Compose the complete sector product, then apply behavioral reductions.**
   Audit the existing reverse/add radial-innovation and cyclotomic transport
   theorems and list the sectors actually certified for the runtime kernel.
   Publish their canonical product in the temporal action; composing an action
   must compose/reduce every admitted sector before any tile descent. Reuse
   fixed-arity exponent/affine DAG constructors and drop an old source term only
   in the particular certified annihilated sector. Decimal H=20 is theorem
   metadata, assembled through shared powers and 16+4, never an exact bootstrap
   slab. Branch-dependent growth and forcing still come from executable local
   laws. Add active carry-consumer classes only after complete spatial and
   successor obligations are discharged. Exact output retains its own TileID;
   the mixed-radix bijection and mod-32 residue do not authorize content merging.
5. **Normalize certified symmetries and expanded regions before work.** Transform
   action, oriented tile views, both contracts, operands, phase and wiring as
   one request; preserve the inverse result transform. Start with certified
   mirror/conjugacy, report that subgroup accurately, and reject uncertified D4
   operations. Reuse contained dyadic results and child-transform relationships;
   do not scan a future tile to discover an equivalent representative.
6. **Delete superseded execution with migration evidence.** First record a
   recursive inbound-import and call-site manifest for every candidate. Classify
   each caller as public production, semantic compiler, proof/test, audit-only,
   or dead. Remove old family callbacks, providers and higher interpreters only
   after public replacements pass poisons and differentials and all retained
   semantic construction has a canonical owner outside the old executor.
   Payload audits must inspect the new live arenas directly; they cannot keep an
   unreachable executor importable solely to report compatibility zeros.
   Migrate obsolete private-carrier setup while preserving each semantic
   assertion, coordinate, fixture and resource limit. Keep independent exact
   proof algorithms, not a copied legacy backend. Add import/call-graph and
   installed-wheel checks that prevent deleted paths returning.
7. **Profile the remaining tile work, then proof construction.** Measure one cold
   point, width, dense output, and radix sequence independently. Address repeated
   causal coverage, semantic admission/substitution, and GC/recreation before
   optimizing duplicated immutable proof artifacts. Reuse proof artifacts only
   through the existing registry with fresh runtime scopes and ledgers.
   The original-source affine observation now builds one canonical dyadic
   three-state carry/shift summary in `O(W)` source work and answers each later
   digit in `O(log W)` summary visits. It retains neither shifted output digits
   nor coordinate-indexed carries, and its construction workspace is charged
   before allocation. This removes that radix-specific quadratic prefix rescan;
   it does not establish sublinear reverse-196 execution or the full release
   timing bound.

## Publication and lookup contracts

Normalized execution requests retain complete producer and consumer edge
semantics; the same total exponent cannot erase distinct wiring. Probe in order:

1. completed exact result;
2. certified active future-behavior transition;
3. completed fused transfer or bounded interface observation;
4. exact causal region and contained completed dyadic pieces;
5. an already available producer midpoint;
6. unresolved, deduplicated scheduler dependencies.

A midpoint miss does not force its completion. A behavior hit may discharge
only its certified consumer observations. The exact causal route remains the
correctness path for an unsupported profile, through the same scheduler.
Budget exhaustion rolls back and raises; it does not trigger another executor.

Publish only completed tiles/results and fully certified semantic functions.
Reserve entries, node storage and boundary retains atomically. Keep canonical
IDs non-recycled, application/subresult leases explicit, memos non-owning, and
retirement reverse indexes complete, including lease-only boundary operands.
Warm lookups validate authority/liveness and immutable publication integrity
without repeating semantic proofs or reduction.

Semantic-function transactions now charge staged nodes and transaction maps
before insertion, reserve preparation workspace, and convert charges atomically
on publication. Multi-arena journals restore both before-insertion and
after-insertion failures. Cancellation clears the discarded DAG and releases its
workspace; closed transient IDs reject access. Continue auditing local scratch
storage as well: final reachable node count cannot stand in for transient
reduction storage.

## Legacy deletion audit

Deletion follows reachability, not naming. The current public certified-family
route is `runtime_router -> tile_projection -> PrimitiveTileKernelAdapter ->
TileScheduler`. It does not construct either family-specific field-action arena.
The installed source tree also contains no reverse slab/cut/bootstrap type or
row-recovery API. Those facts are useful boundary evidence, but they do not by
themselves make every continuation module removable.

The remaining old graph has two different roles that must be separated:

| Current cluster | Inbound use | Required migration before deletion |
| --- | --- | --- |
| Collatz recursive image, temporal emission, field observer and radix image input | removed September 9, including their optional image branches and audit roles | keep physical-absence tests and current tile observation/ownership regressions |
| Recursive coordinate output/provider carriers | old higher macro composer and legacy payload audits | replace retained semantic output construction with the canonical interface/output law |
| Higher/concrete runtime executors | proof tools, private tests and legacy family adapters | migrate assertions to TileApplication or an independent proof oracle; keep no production executor copy |
| Continuation expression and finite-map primitives | retained semantic interface compiler | extract the still-live bounded compiler primitives to their interface owner before deleting the executor package |
| Remaining Collatz concrete-port and higher-interface adapters | proof/private execution and tests; the reverse concrete adapter is deleted | migrate their last semantic callers and remove the adapters rather than forwarding them |

Resource reporting is not a reason to retain a dead executor. Split
`payload_audit`, `field_image_payload_audit`, `higher_payload_audit`, and
`radix_provider_payload_audit` so canonical tile, result, quotient, action and
workspace stores are audited without importing old runtime types. Delete each
legacy branch together with its final audited store. Compatibility fields then
come from current ledger roles or an observed zero; no dummy arena is built to
populate them.

Repository source inventory and package identity are already discovered from
the authored roots. Keep the small intentional public-package/export contract,
but do not add handwritten per-file source lists or migration inventories.
Historical result manifests remain attached to their artifacts and are not
used as current source authority.

Atomic macro components already masked by the interface's Boolean validity
condition can bypass a second normalization rewrite. The shortcut probes the
canonical predicate representation without speculative publication. Product and
function-valued components keep the full normalization path. Count predicate
validation and mask elisions separately from memo hits; this optimization alone
does not establish a better temporal growth bound.

## Measurements that decide whether this helps

Keep schema 6 and obtain compatibility fields from one read-only ledger
snapshot. The finite factorization is useful only if it reduces total work,
not merely the number of stored labels. Record these independently:

| Category | Required evidence |
| --- | --- |
| Temporal construction | action/component nodes, composition requests/evaluations; O(log N) construction |
| Actual execution | requested and successfully absorbed span; demanded descents, primitive decisions, transfer and fused-transfer evaluations |
| Cache levels | exact result, causal region, bounded interface, active behavior, symmetry: requests, early hits, failures, publications, late duplicates |
| Algebra | per-sector compositions/reductions, carry, phase/full-adder, affine transport, certified sector-local source annihilation, substitution and reduction operations |
| Causal coverage | requested union, exact-cache service, behavior/interface discharge, new construction, required sibling extent, unrelated extent |
| Repetition | first leaf evaluations, all leaf evaluations, repeated parent work and recreation after eviction |
| Resources | cumulative allocation, live/peak tiles, interface classes, memo/reverse-index slots, leases, workspace and explicit emissions |
| GC | memo eviction, tile retirement, reverse-index work and Python GC pauses separately |
| Process memory | sampled physical footprint, swap/compression diagnostics, group population, memory-limit failures and worker cleanup |

Use spatial coverage within a logical field binding and semantic coverage
distinguished by action, both contracts and consumer profile. Coordinate overlap
alone cannot merge different fields. Served extents can overlap; do not present
them as an exclusive partition or as invented operations saved. A cached large
tile represents many coordinates without implying that many leaf evaluations.

Keep normal counters lightweight. Run detailed coverage, CPU/allocation profiles
and graph audits separately, charging trace storage and processing. Preserve the
8,192-record/8-MiB diagnostic cap; truncated evidence cannot pass complete
coverage gates. GC callbacks must be restored and ordinary GC stays enabled for
release timing.

The [September memory incident](../results/current/memory-incident-2026-09-08.md)
records the stopped diagnostic jobs. Their failed runs are incomplete evidence,
not performance samples. Low RSS or a finite residue bound cannot authorize a
memory-use claim. The 196 Frobenius/annihilation optimization must pass the same
process and arena memory checks; the incident itself was attributed to wide
radix composition and does not establish a measured 196-specific cause.

Example guarded probe (use fresh artifact paths for each run):

```bash
python -m devtools.checks.process_guard \
  --output /tmp/number-compiler-probe.log \
  --report /tmp/number-compiler-probe.json \
  -- python -m pytest tests/repository/test_process_guard.py -q
```

The default deadline is for probes. A full serial release run retains its
300-second target and must use an explicit 300-second group watchdog; increasing
either limit to make an algorithm pass is not an optimization. Diagnostic
measurements and ordinary release timing remain separate.

Compare factored/unfactored local compilation and quotient-enabled/disabled
fresh runtimes through the same tile scheduler. Include classification,
normalization and reduction work. Freeze the audited profile-specific causal
work bound before scaling trials; do not tune its constant to fit a bad curve.

Run N=16,32,64,128,256,512,1024 with acceleration disabled, separately for fixed
source width, growing 196, fixed-time spatial width, Collatz physical/event
observations, radix and explicit lowering. Publish source fingerprint,
environment, completion status, five-process median/spread, raw work and
retention, increments, doubling ratios and
`p_N = log2(W(2N)/W(N))`. Missing/zero denominators and interrupted runs remain
unavailable. Classify work, retention and timing separately as observed
sublinear, linear/output-sensitive, superlinear, or insufficient evidence.

Algebra counters are execution counters. Constructing or interning a temporal
action may increment compiler/publication counters, but it must not increment
sector-operation, innovation-application or source-annihilation execution
counters. Those advance only when `TileScheduler` executes the corresponding
component for a normalized dependency. Report requests, early hits,
evaluations, publications and late aliases separately by sector. A cache hit may
increment its request/hit counters but performs zero sector evaluation. Record
annihilation as `(sector, precision, transition)` evidence and count it only
when execution changes that sector from source-dependent to certified dead.
Repeated observation of an already-dead sector is a hit, not another
annihilation. Add an independent payload regression showing that all live
non-annihilated sectors and the exact coordinate-output dependency survive.

## Acceptance

The current spatial composer directly reuses its two identity-bound midpoint
functions after complete signature validation. It performs seven meaningful
child substitutions instead of nine. Total Boolean carry identities also reduce
before entering the general partial-function Shannon scheduler. These are
bounded local reductions, not a trajectory quotient. The shared composer now
owns exactly one spatial probe/publication; duplicate publication no longer
inflates late-alias telemetry. Counters expose identity-substitution elision and
Boolean reduction separately from true parent cache hits.

- Preserve all ten absorption fixtures and semantic poisons with the approved
  TileApplication setup. Unresolved cold leaf work is permitted and counted;
  retired temporal-interpreter calls are zero.
- Check equal carry exits with different digits, positive certified active
  aliases, two-sided composition order/interchange, growth edges, admissibility,
  symmetry and cocycles. An active profile must be successor-closed, not merely
  conflict-free on the current sample.
- Verify the complete certified reverse sector product participates in binary
  temporal composition. For each sector, compare composed valuation, unit and
  innovation against the independent small exact oracle. Poison tile descent
  while testing pure sector composition, and poison compiler composition while
  testing a warm executed sector result.
- Assert compiler-only action construction reports zero executed sector
  operations and zero executed source annihilations. A cold scheduler witness
  must report nonzero sector work; its second identical request must report an
  early hit without increasing sector evaluations. An annihilation witness may
  erase the source reference only in the certified sector, while another live
  sector and the exact output projection retain theirs.
- Warm completed, interface-only, behavioral and symmetry-related requests
  survive poisoned constructors, reducers, source scans and descendants. New
  coordinates and larger demands reuse existing regions; no-eviction repeated
  completed demands perform zero repeated leaf work.
- Public reverse, Collatz, radix and supported generic paths demonstrably enter
  TileScheduler. No fallback continuation calls, generation replay, flat
  intermediate scans, or unrelated exact construction occur.
- Reconcile resources independently under invalid/foreign/stale IDs, failed
  publication, eviction, lease-only retention and retirement. Reporting is
  read-only and counts failed/cache-hit work.
- Preserve existing work/retention envelopes and radix medians: cold <=0.25s,
  repeat <=0.01s across five fresh processes. Serial unfiltered pytest must pass
  under 300s, with Ruff, whole-tree strict mypy and recursive policy checks on
  the same frozen fingerprint. Fixtures, budgets, tracing and watchdogs remain
  unchanged.

The local algebra is not a proof of sublinear execution. Exact output of width W
requires at least W emissions. A successful production cutover is necessary
but does not by itself close the performance release.
