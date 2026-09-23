# 2026-W39 implementation and validation record

Period: 2026-09-21 through 2026-09-27. Updated through September 22.
Status: finite integrations and audits advanced; production release remains blocked.

## Sprint summary

- **Objective:** share authenticated arithmetic and consumers while removing
  duplicate work without claiming unsupported temporal compression.
- **Changes:** carry/F5 integration, source macro construction, cache-authority
  repairs, lazy observations and finite safety transformers.
- **Established results:** scoped arithmetic laws and bounded regressions below.
- **Rejected approaches:** observer equality as source authority, future-orbit
  inputs as source construction, and warm/refusal timings as cold performance.
- **Validation:** each record retains its own fingerprint, commands and limits.
  An earlier result does not certify a later edit; see the
  [release ledger](../../../docs/release-status.md) for the current gate table.
- **Remaining work:** successful generic reverse/add temporal construction,
  source-discovery and executable refinement bounds, and the separately stated
  source-global mathematical obligations remain open.

## Provenance and reading guide

These records were relocated from the maintained research papers on September
22. Their implementation narratives are historical snapshots, preserved with
original results and caveats. Words such as “now” and “remaining” in a record
refer to that snapshot. Later entries can supersede its integration status.
Raw artifact paths are local/CI evidence references, not portable downloads.
Missing fingerprints have not been invented. The movement changes no code,
proof, test assertion or release gate.

The papers retain definitions, theorem assumptions, counterexample scope and
current construction boundaries. Detailed records below are expandable to keep
this weekly summary navigable.

| Topic | Maintained synthesis | Implementation and evidence |
| --- | --- | --- |
| Shared execution | [Shared actions](../../../docs/research/shared.md) | [Audits](#shared-execution) |
| Collatz | [Source cylinders](../../../docs/research/collatz.md) | [Integration records](#collatz) |
| Antihydra/Mahler | [Arithmetic and safety](../../../docs/research/antihydra-mahler.md) | [Integration records](#antihydra-and-mahler) |
| Reverse/add | [Temporal construction](../../../docs/research/reverse-add.md) | [Integration records](#reverseadd) |

## Shared execution

### Profiler and cache authority audit

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

The development environment now includes the optional Pyinstrument profiler;
the [development guide](../../../docs/development.md#resource-controlled-diagnostics)
documents sampling, exact call counts and guarded test-phase measurements.
Runtime dependencies are unchanged.

- **Fixed stale reuse:** a warm source-image projection authenticated its
  publication seal but skipped adapter authority checks. Revoking the backing
  payload could therefore leave a cached result usable. Warm hits now perform
  the same source/action/payload validation as cold demands, before counting
  a successful hit. A revocation regression covers this distinction.
- **Reviewed identities:** the bounded audit found no additional reproducible
  collision in typed process-cache keys, generation-bound leases or the
  consumer-bound, request-local higher-temporal memo. This is scoped review,
  not a proof that all caches are defect-free. Complete-image application
  keys remain shared across demands; a demand must not replace the admitted
  image with an incomplete observer packet.
- **Reduced observer work:** Antihydra tape Hasse queries authenticate one
  interval view for all orders. Directional moments combine adjacent moves
  with the same direction and build exact binomial rows once. Negative
  coordinates and control labels in the underlying source remain intact.
- **Reduced test-tool work:** recursion checking collects calls during its
  existing AST traversal instead of walking every function body again.
  Package checks use exact AST shapes for path/module-identity bans rather
  than repeatedly rendering expressions. No test oracle or production cache
  is shared between independent tests to obtain this reduction.

The bounded Hasse comparison uses `antihydra --nth 1024 --no-value --info hasse
--width 8 --format json`. Against the preceding installed wheel, requested
values are identical; call counts fell from 5,416,919 to 1,046,849, and a
separate unprofiled cold run fell from 6.93 s to 1.97 s. This observer still
samples represented returns and does not establish sublinear temporal
construction. The two structural test profiles fell from 98,040,202 calls
to 77,503,820; profiled guard time fell from 24.24 s to 19.63 s. Instrumented
times describe these probes, not an arbitrary-size performance bound.

Local evidence is under `results/current/profiler-cache-audit/`:
`hasse-comparison.json`, `hasse-unprofiled-*.guard.json`,
`repository-comparison.json` and the focused cache/tool regressions.
The active reverse/add construction failures remain release failures;
profiling a fast refusal is not successful digit production.

</details>

### Memo authority and accounting audit

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

The September 22 adversarial audit found implementation defects, not new
mathematical quotients:

- Scheduler origin, application, relative-input and projection keys compared
  Boolean and integer components using Python equality. `True` and `1` could
  select the same cached result even when the adapter distinguished them.
  The scheduler now compares typed structures, including nested frozen
  descriptors. Hashing traverses shared descriptor DAGs with an explicit
  postorder stack and per-node memo, rather than expanding repeated subgraphs.
  Origin publication seals retain the actual source, avoiding a redundant seal
  of its cache-key wrapper while checking that both identify the same source.
- The process cache now rejects Boolean components in source/local authority
  keys; its prime consumers use exact integers and strings. Boolean payloads
  remain supported. Lease validation uses exact scalar types and the issued
  partition identity. Failed close attempts preserve the ability to correct
  and release a lease. Active-lease counts increase only after successful
  resource reservation and publication; refused admission cannot leave a phantom
  lease. A mutated generation cannot impersonate an actual reset
  and leave a live partition permanently pinned. Issued leases remain strongly
  held until close/reset, preventing object-ID reuse from overwriting authority
  records. Their retention is charged to the bounded store.
- Higher temporal image node and blank memos now include the complete
  consumer declaration. Its independent seal snapshots types, values and
  scoped-handle fields, so mutating the composer and its memo key together
  does not authorize a warm hit. Workspace probes and memo hits are counted
  separately from newly visited image nodes.
- Spatial and temporal constructors share one sealed consumer declaration.
  Provider registration now authenticates the output/source/action relation,
  including warm alias requests, and pins the runtime and callbacks. Individually
  valid handles are not sufficient evidence of that relation. Already issued
  provider bindings survive clearing the construction workspace.

The temporal-image reproduction warmed a private blank-macro workspace and
then changed its consumer. The public `step()` in the audited checkout already
clears that workspace in `finally` and rejects composite consumers. Its
independent 16-step output/work regression does not reproduce free D8/D16
construction. No zero-work observation from a different experimental harness
certifies temporal compression without that harness's source and binding
trace. The retained positive release gates remain unchanged.

Final source fingerprint: `de9d18c1c6f587015138c049cded52cbd70d43d9cfb1791d18f26964da4614e1`.
The frozen run passed 213 focused checks, strict typing/lint/formatting, repository
policy, proof inventory and installed-wheel checks. Full unit validation reports
6,279 passes and the same 42 failing cases as its baseline; the explicit cutover
selection retains 14 failures and six passes. No Isabelle theorem changed in
this memo audit, and no new mathematical refinement is claimed.

Local evidence is under `results/current/temporal-memo-audit-2026-09-22/`.
The implementation regression tests are
[source-bound scheduler tests](../../../tests/hashlife/execution/test_source_bound_images.py),
[process-cache tests](../../../tests/resources/test_process_cache.py),
[macro authority tests](../../../tests/hashlife/execution/test_higher_macro_authority.py), and
[higher temporal image tests](../../../tests/hashlife/execution/test_higher_temporal_image.py).

</details>

### Eager-work audit scope

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

The September 22 follow-up audit assigned separate owners to dyadic execution,
output projection and Antihydra observers, with cross-review before validation.
The changes remove repeated work without substituting observation equality for
source authority:

- Antihydra cursor admission snapshots the authenticated segment fields once,
  with reservation before allocation. Transitions check the current segment;
  final validation still checks the complete result. Whole-segment validation
  visits during cursor traversal fell from 46, 164, 616 and 2,384 to zero for
  128, 256, 512 and 1,024 returns. Admission and finish remain linear.
- Scalar Collatz digits use exact affine threshold admission followed by
  modular extraction. They do not multiply the complete affine numerator.
  A conservative bit bound rejects remote coordinates before allocating
  a radix power. Explicit complete output still lowers once on demand.
  A dedicated exterior-coordinate signal preserves blank/zero padding without
  swallowing internal projection errors.
- Dyadic cycle summaries fold one authenticated period without rebuilding
  rotated state, weight and prefix arrays. Signed short numerators avoid
  oversized moduli; negative constant residues retain canonical low bits.
- Combined Mahler/Hensel requests share one authenticated tangent evaluation.
  Their packets remain distinct, and Hensel alone does not request the Mahler
  associated action or a physical roof.
- Prime progression inverses are shared by depth within one fixed-modulus
  query, in a charged workspace cleared on success or failure. A six-factor
  probe reduced inverse calls from 124 to six; the zero-residue case uses none.
  It does not introduce a cross-query authority or change numerical Phi.
- CLI rendering uses a byte buffer rather than a list of character references.
  For 200,000 output characters, measured Python allocation peak fell from
  3,424,137 to 415,106 bytes with identical output hashes. This measures the
  renderer, not family construction or process RSS.

Cross-review rejected a full seal copy on every cursor transition and a proposed
full-numerator implementation of direct radix digits. Both would have retained
the repeated work being removed. Mutation, foreign-source and budget checks
remain active. The generic reverse temporal constructor, source discovery bounds
and exact powered spacetime projection remain separate open obligations.

Local probe data is under `results/current/eager-work-audit/`. Final validation
and its source fingerprint are recorded in [the release ledger](../../../docs/release-status.md).

The bounded regressions can be reproduced without timing thresholds:

```console
python -m pytest -q tests/api/test_antihydra_projection_occurrences.py tests/sequences/prime/test_successor_action.py tests/projection/test_lazy_radix_intervals.py tests/hashlife/execution/test_dyadic_effect_reuse.py
python -m pytest -q tests/api/test_cli_query_context.py::test_antihydra_mahler_extends_shared_tangent_without_aliasing
```

These tests check work counters, exact outputs and forbidden allocations; they
do not replace the unchanged family growth manifest or its construction gates.

</details>

## Collatz

### Saturated finite safety and source binding

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

The downloaded source-free quotient patch is selectively integrated through
[saturated_future.py](../../../src/number_compiler/sequences/collatz/saturated_future.py).
The retained finite action has an exact skew endpoint and the shared
[threshold envelope](../../../src/number_compiler/arithmetic/fields/threshold_envelope.py).
Its occurrence adds the Hensel source cylinder and event count. It contains no
valuation word, midpoint list, birth history or child-action tree. It is an
arithmetic value, not an authentication token for a source occurrence.

- **Implemented composition:** for chronological blocks A then B, the endpoint
  composes by the existing skew law. The threshold is
  `max(F_A(T), endpoint_A^-1(F_B(T)))`, normalized by exact rational hull rules.
  Source admission intersects A's cylinder with the pullback of B's cylinder.
- **Production consumer:** `collatz --events N --info safety` traverses the
  already authenticated event publication. It does not run the streaming
  selector again. Ordinary digits and unrequested information do not build
  this envelope. Empty prefixes have no descent; equality at the threshold
  is not strict descent.
- **Source-free descriptor:** squaring adds event counts without a source.
  Binding uses the existing radix-64 selector and bounded publication buffers;
  it still allocates event stages and performs per-event digit transport.
  Removing retained history does not establish cheap source application.
- **Shared consumers:** the prime/deck research adapter calls the existing
  ledger-owned `PrimeBucketWorkspace`. No second partition algorithm or
  unbounded global cache was imported. Neither its 55 bucket total nor a
  six-choice suffix authorizes an exact successor merge.
- **Finite experiment:** independent integer arithmetic over all `6^6` words
  with valuations in 1..6 confirms 46,625 cylinders whose every natural high
  fiber descends, 30 whose fibers do not descend in the block, and one with only
  the origin safe: `(2,2,2,2,2,2)`. These are source-cylinder branches, not
  all branches visited by one trajectory or a global safety theorem.

The optional observation reports `all_time_claim: false`. Antihydra and Mahler
share the arithmetic and authenticated aggregate publication boundary, but
retain their own source laws and distinct ledger/positivity predicates.
The Collatz lane multiplier `3/2^q` cannot replace Mahler's `(3/2)^q`.
The report's recursive scalar/midpoint constructor was not imported into the
production path.

Reproduction: `python -m number_compiler collatz --events 20 --seed 27
--info safety --format json`. Local integration evidence is recorded under
`results/current/saturated-transformer-integration/`. Full source-application
complexity, Python worklist refinement and all-time claims remain separate
obligations.

</details>

### Shared branch observers and joint experiment

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

The bounded suffix monoid, finite prime bank, exact phase laws and possibility
partition owner now live in
[branch_quotients.py](../../../src/number_compiler/arithmetic/fields/branch_quotients.py).
Mahler research imports this implementation instead of maintaining another
copy. A ledger-owned workspace caches partitions by **family and prime**,
charges phase/refinement visits, reserves scratch storage before construction,
and releases it after failure. These counters measure bounded operations,
not exact integer bit complexity.

- Mahler's lane multiplier is `(3/2)^q`; accelerated Collatz's is `3/2^q`.
  Their source-derived exponents differ and remain separately bound.
- The 67 Mahler and 55 Collatz bucket counts are sums over the finite prime
  bank. They are not cardinalities of an exact joint successor alphabet.
- The suffix records at most six sibling choices among the first three
  admitted branches. It does not encode an unbounded event exponent.
- The joint experiment combines those observers with the 64-sheet deck and
  729 chart. It checks source-reachable witnesses and reports unexplored
  branches. Equal observer keys never merge source occurrences in production.

The exhaustive positive odd 16-bit Collatz sample has 32,768 rows and no
repeated full keys. Thus its lack of conflicts is insufficient evidence for
a reusable successor rule. See the [joint research owner](../../../devtools/experiments/antihydra/joint_future_quotient.py)
and [regressions](../../../tests/validation/proofs/test_joint_future_quotient.py).
This transfer removes duplicated observer algebra; it does not yet provide
a source-selected temporal pump for the CLI.

Status: **finite physical/event refinements and source lifts are checked; the
remaining compact publication and growth gates are not implied by them**.

The CLI's `--nth` counts ordinary Collatz iterations. Accelerated events are a
separate coordinate. A valid cylinder therefore records both physical tick
count and event count rather than identifying them.

</details>

### Carry/F5 directional integration (2026-09-21)

Record period: 2026-09-21.

<details>
<summary>Implementation, validation and remaining work</summary>

- **Canonical projection:**
  [collatz_binary_forcing.py](../../../src/number_compiler/arithmetic/carry/collatz_binary_forcing.py)
  now owns the existing `binary_carry_birth` and `radix64_phi5` functions.
  The harmonic research module imports those same functions. No second phase
  definition is used. The F5 fibers have sizes `(28,16,4,7,9)` and the joint
  `(five-way carry action, phase)` observer has 15 realized classes.
- **Exact scope of the missing port:** positive odd sources 67 and 75 have
  identical two-cell class words and Hensel gap one, but their accelerated
  targets are 101 and 113, with different low-cell classes. This distinguishes
  the proposed leaf projection; it is not a counterexample to the full source
  cylinder. The fixed-shift directional response resolves this witness.
- **Implemented finite refinement:**
  [collatz_f5_quotient.py](../../../src/number_compiler/arithmetic/carry/collatz_f5_quotient.py)
  partitions rows and columns of the exact join observation. Left/right class
  counts for shifts 0–5 are `(15,1)`, `(12,2)`, `(10,4)`, `(8,8)`, `(4,9)` and
  `(2,13)`. Distinct rows/columns supply distinguishing contexts, proving
  minimality among independent one-sided response partitions for this fixed
  consumer. This does not prove closure under repeated temporal application.
- **HashLife arithmetic consumer:**
  [CollatzOutputMorphism](../../../src/number_compiler/sequences/collatz/output_morphism.py)
  composes these reduced ports in the existing `BitFunctionArena`, without
  constructing the joined target digit. Optional F5 tables and its result
  memo are demanded lazily. The ledger accounts for the evictable memo;
  clearing it preserves issued semantic handles. These observer IDs do not
  authorize replacing source occurrences or successor images.
- **Validation:** independent binary-output identities check the phase;
  exhaustive finite joins check every raw pair and residual shift. Symbolic
  tests check every reduced port pair, foreign handles, wrong-shift binding,
  cache clearing, and unchanged nodes on warm demand. The focused selection
  passed 83 tests in 3.26 seconds under the 35-second/1-GiB guard. This is
  executable finite evidence, not a new checked Isabelle constructor theorem.

</details>

### Cross-family work and cache measurements

Record period: 2026-09-21.

<details>
<summary>Implementation, validation and remaining work</summary>

At source fingerprint
`94396a4d75337002e208641a0de41d1a4be03c6ccba776a039f22c6eb3ac9401`,
five trials per case separated cold construction, repeated demand, and demand
after clearing the result memo. Median times in milliseconds:

| Component | Cold | Warm | Memo cleared, arithmetic retained |
| --- | ---: | ---: | ---: |
| 196 supplied forcing, growth exponent `5^64-1` | 7.6423 | 0.0165 | 4.9278 |
| Collatz fixed-shift-1 F5 consumer | 9.1897 | 0.0106 | 8.2569 |

Warm demand recorded exactly one request and one component memo hit, with no
new arithmetic nodes, no repeated forcing shifts and no repeated directional
construction workspace. These are local arithmetic/observer hits, not temporal
source-image cache hits. The 196 component constructs 514 arithmetic records;
the ledger charges 702 node units including retained integer sizes.

The same fingerprint was measured through the CLI and public API at every
power-of-two horizon 16–1024, with five trials per horizon. Collatz used seed
`931386509544713451`; all 140 outputs matched a separate bounded recurrence.
Selected median times in milliseconds:

| Horizon | Fresh CLI process | First API query | Repeated API query | API cache bypassed |
| ---: | ---: | ---: | ---: | ---: |
| 16 | 441.733 | 1.057 | 0.029 | 0.670 |
| 256 | 440.616 | 3.968 | 0.033 | 3.546 |
| 1024 | 471.993 | 15.320 | 0.029 | 14.738 |

The CLI times include startup, rendering and requested metrics; API query
times include construction/materialization but exclude the subsequent metrics
snapshot. They are different measurement boundaries. The existing API owner
cache already reuses Collatz construction. Its ordinary digit path does not
consume the new F5 observer, so these timings establish no CLI improvement
attributable to F5. The recorded transport-bit work still grows from 1024 to
3072 to 8192 at horizons 256, 512 and 1024. Source leaf work and payload-audit
branch work both still equal the requested horizon in these samples.

All 140 reverse/add attempts returned construction refusal, beginning with
the unsupported same-carry exit at D16. Their work samples are unavailable,
not zero, and refusal latency is not a speedup. Source-derived forcing and
complete output-carrier publication remain required before that cutover.

Raw evidence and reproduction scripts are local under
`results/current/f5-cross-family-2026-09-21/`. The Collatz process group took
18.03 seconds with 104,416,312 bytes sampled peak; the reverse/add group took
3.34 seconds with 34,915,312 bytes. Both used the unchanged 35-second/1-GiB
guard. These are source-fingerprinted finite probes, not full release approval.

Reproduce the finite consumer and reuse checks with:

```console
python -m pytest -q -o addopts='' tests/sequences/collatz/test_f5_directional_quotient.py tests/arithmetic/fields/test_f5_innovation.py tests/sequences/reverse_add/test_powered_cocycle_regions.py
```

</details>

### Downloaded spatial-grammar patch

Record period: 2026-09-21.

<details>
<summary>Implementation, validation and remaining work</summary>

The subsequently supplied `collatz_radix5_future_grammar.patch` (SHA-256
`775ecdcf23730b2a354af17c9c12137eec5a664d45826f139edc2730c3e121c7`)
and `collatz_radix5_future_grammar_report.md` (SHA-256
`e9aad67d05b8e48ca843050c7eefeeb4d1d9c191e778c5e03f5fb3790c310537`)
add a spatial observer semigroup. The local port refinement above and this
spatial concatenation law are distinct operations.

`CollatzF5SpatialAction` in the canonical F5 quotient module now owns the
patch's `(carry action, additive phase)` law. Physical concatenation applies
the more significant carry map after the less significant one. The phase is
the sum of the leaf `phi5` values, **not** the binary forcing jet of the entire
word. It cannot be substituted for that jet or for a temporal source image.

The adapted
[radix5_future_grammar.py](../../../devtools/experiments/collatz/radix5_future_grammar.py)
uses that production arithmetic owner. Its exact-length state-language
construction now uses the existing `binary_power` work loop over finite sets
instead of iterating once per represented cell. An explicit empty-word
identity is separate from the five nonempty carry actions. The patch's
repeated verifier calls, unchecked digit indexing and typing suppression were
removed. Independent tests check physical carry on all two-cell radix-64
words; alphabet cardinalities alone cannot detect reversed spatial order.

At fingerprint
`cddaa2890f2d97766a9616ac8dd3dc80d4333b36a81e74e9ba53dd76a0633a24`,
five paired trials with the same action kernel measured these state-language
construction medians (milliseconds):

| Region length | Sequential length recurrence | Binary set composition |
| ---: | ---: | ---: |
| 5 | 1.504 | 1.174 |
| 25 | 9.348 | 2.443 |
| 125 | 45.810 | 4.540 |
| 625 | 233.180 | 5.233 |

Length `5^64` returned 17 states in one 99.68-ms sample. This is a finite
observer-language constructor, not a source trajectory or a CLI output jump.
The original report's deterministic 96-source, 240-cell D0–D64 occurrence
table reproduced exactly. Across its sampled horizons only one prior
five-cell occurrence was reused (at D8); all 25- and 125-cell occurrences
were new. Thus the fixed 17-state macro alphabet does not itself establish
useful reuse of complete future regions.

The combined patch, directional, harmonic and F5 integration selection passed
51 tests in 6.73 seconds. The guarded probe took 2.46 seconds and sampled
25,346,576 bytes peak. Evidence is local in
`results/current/f5-cross-family-2026-09-21/`, including the supplied report
and patch. No Isabelle temporal-constructor or production source-publication
obligation was closed by this spatial observer integration.

```console
python -m pytest -q -o addopts='' tests/validation/research/collatz/test_radix5_future_grammar.py tests/sequences/collatz/test_f5_directional_quotient.py
```

The installed implementation shares directional carry actions, source Hensel
anchors, physical/event clocks, and demanded output buffers. Terminal output
allocation is charged before materialization. Cached support belongs to the
source occurrence and cannot be reused after provenance changes.

The remaining release work is to keep construction and demanded projection
within the public resource contract for arbitrary admitted queries. A local
free-selection theorem or curvature view does not remove the source event
pipeline. The three-cycle identities for source one describe that admitted
cycle; low-residue equality alone is explicitly not cycle admission.

</details>

### Shared temporal effect reuse

Record period: 2026-09-21.

<details>
<summary>Implementation, validation and remaining work</summary>

The production [dyadic scheduler adapter](../../../src/number_compiler/hashlife/execution/dyadic_return_images.py)
now uses [admitted-cylinder reuse](../../../src/number_compiler/hashlife/execution/dyadic_return_reuse.py).
Previously it always declined the scheduler's relative-reuse hook.

- **Implemented:** the same action and source residue at the demanded precision
  share their complete skew, branch support, weights and minimum prefix. Each
  occurrence receives a separately authenticated image. No midpoint, output
  word or branch replay is needed on a reuse hit.
- **Cycle admission:** exact singleton shortcuts retain the high fiber in
  their key. For nonnegative branch offsets, a high fiber above every cycle
  state excludes the cycle throughout the block. Only that checked case may
  share a cylinder effect across high fibers.
- **Checked mathematics:** existing `exact_precision_source_lift` gives the
  shared branch word and endpoint transport. The new
  `dyadic_source_orbit_lower_bound` and
  `dyadic_high_fiber_excludes_small_states` prove the cycle exclusion used by
  the adapter. These do not constitute a formal Python cache refinement.
- **Remaining construction:** the 17-state spatial F5 observation is not the
  reuse key. Normalization across different residue clauses remains missing.
  This change does not establish a bounded future grammar for every source.

The September 21 paired probe covers horizons 16–1024 with five trials each,
fresh ledgers, a reuse-disabled control and warm repeated requests. All 280
endpoints agree with bounded independent arithmetic. This measurement predates
the subsequent sealed-publication audit checks; its timings are historical,
not measurements of the hardened path. At 1,024 steps:

| Source and law | Support nodes, disabled → enabled | Discovered branches | Median construction, disabled → enabled |
| --- | ---: | ---: | ---: |
| Collatz, `2^4096` | 31 → 5 | 1024 → 64 | 14.36 → 4.59 ms |
| Antihydra arithmetic, `2^4096` | 31 → 5 | 1024 → 64 | 13.62 → 4.36 ms |
| Collatz, `931386509544713451` | 31 → 31 | 1024 → 1024 | 14.51 → 15.24 ms |
| Antihydra blank source, `8` | 31 → 31 | 1024 → 1024 | 14.12 → 14.58 ms |

The aligned Antihydra case tests the production arithmetic law with an
alternate source; the public Antihydra CLI remains pinned to 8. Matching cases
retain 144 ledger entries rather than 455; unmatched cases retain 486 rather
than 455. Timings exclude endpoint observation, rendering and validation, which
are recorded separately or explicitly outside the timed constructor. Reuse
bookkeeping has a measured cost when no clauses match.

Fresh CLI traces additionally check the Collatz digit path and Antihydra's
Mahler consumer. Raw measurements, commands and source fingerprints remain
local in `results/current/dyadic-effect-reuse-2026-09-21/`; they are focused
evidence, not the full release growth manifest. Reproduce the semantic checks:

```console
python -m pytest -q -o addopts='' tests/hashlife/execution/test_dyadic_effect_reuse.py tests/api/test_antihydra_mahler_action.py
```

</details>

### Updated saturated publication patch

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

The downloaded `collatz_final_quotient_powered_integration.patch` supplies
two changes now integrated through existing owners:

- **Production:** `DyadicReturnImageWorkspace.saturated_summary()` projects
  the sealed source image to its affine map, extent, aggregate clock, minimum
  prefix and cycle metadata. Collatz digit consumers and shared Antihydra
  arithmetic observers use it. Every demand revalidates the image; there is
  no extra unchecked summary cache. Support stays with the scheduler for
  first-failure descent. This removes no source-discovery obligation.
- **Finite experiment:** the common prime-possibility refinement now accepts
  Collatz's distinct phases `3*2^(-q)`, using `u=-3*x-1`. The pinned bank has
  55 buckets in total, compared with Mahler's 67 under `(3/2)^q`. The exact
  recurrence and representative-independent possible outputs are tested.
  Bucket equality does not admit an exact next event.

The patch's public occurrence dataclasses only type-check a supplied
action/cylinder pair. That is insufficient production admission. Its balanced
source constructor also discovers scalar leaves and evaluates left endpoints
to construct right children. Neither that constructor nor its unaccounted
summary cache was installed as a replacement for the authenticated scheduler.
The finite tropical-envelope algebra is described below. Its all-prefix
constructor remains to be connected with the actual source owner and charged
work; the entire downloaded patch is not integrated.

```console
python -m pytest -q -o addopts='' tests/api/test_shared_dyadic_digits.py tests/validation/proofs/test_mahler_source_observers.py
```

</details>

## Antihydra and Mahler

### One scheduler for arithmetic and finite Mahler safety

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

The later saturated-transformer integration routes arithmetic result and Mahler
consumer reads through the shared `DyadicAggregateSummary`. That public value
contains no support handle or branch word; the scheduler still retains the
authenticated support required by optional physical observations. The
`Associated_Action_Core` session no longer imports unrelated decimal temporal
proofs. Its registered build and `Antihydra_Mahler_Integration` now pass together
under the original 35-second/4-GiB limit. This checks finite action laws and the
pinned consumer, not a new source-global invariant. See the
[finite threshold proof scope](../../../docs/proofs.md#finite-saturated-threshold-actions).

The production Mahler associated action is now a lazy projection of the
Antihydra arithmetic scheduler's authenticated root image. The separate
Mahler action arena and scheduler have been removed. The source image supplies
the composed skew transfer; the pinned source's centered `11` prefix supplies
the finite cap law. Publication still checks source, action, extent, law and
the nonpositive tail offset. Repeated requests reuse the sealed projection.

- **Implemented:** `--info mahler` uses the same admitted arithmetic image as
  the value and ledger. It does not request physical roofs or extract the
  event history. Hensel remains a distinct lazy observation.
- **Finite predicate:** the pinned source's Mahler margin first fails at
  return two. Its Antihydra ledger does not fail there. The two predicates
  remain separate in output and proofs.
- **Measured scope:** at horizons 16, 64, 256 and 1024, incremental Mahler
  publication fell from 903 ledger nodes / 51 entries to 95 nodes / 2 entries,
  with identical complete packets. This measures observation after arithmetic
  construction; it is not a bound on cold source discovery.
- **Remaining proof boundary:** the demanded algebraic projection is modeled
  in the associated-action theory. Full Python worklist/resource refinement
  and a source-global temporal grammar remain separate obligations.

Owners: [arithmetic image adapter](../../../src/number_compiler/sequences/antihydra/arithmetic_images.py),
[Mahler consumer](../../../src/number_compiler/sequences/antihydra/mahler_action.py),
[publication regressions](../../../tests/api/test_antihydra_mahler_action.py).
The associated-action theory's new demanded projection, pinned prefix cases
and conditional negative-cap result pass a scoped Isabelle build with the
exact proof body. Only its theory name and parent import were remapped.
The registered integration build still times out in `Temporal_Clock_Jumps`
under 35 seconds; this scoped check does not replace aggregate acceptance.
Local measurement evidence: `results/current/joint-future-integration/mahler-measurements.json`.
The comparison loads the preceding wheel's Mahler consumer over the same
current arithmetic source owner, with a fresh term for each observation.

</details>

### Joint future-observer experiment

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

The [joint audit](../../../devtools/experiments/antihydra/joint_future_quotient.py)
combines the bounded branch suffix, prime possibility buckets and deck/chart
observations. Each edge is reconstructed from an admitted source cylinder;
its event exponent and fractional guard are checked. Additional high-fiber
and fractional probes vary the actual parameters within that cylinder.
These are admitted finite initial states, not observations along one fixed
blank-tape trajectory.

| Bounded sample | Result | Interpretation |
| --- | --- | --- |
| Full prime bank, depth 32, high-fiber and fractional probes | 1,377 rows, 254 repeated full keys, 10 coarse outputs, no coarse conflicts | Finite evidence only; larger event exponents remain unexplored |
| Same sample, exact continuation diagnostics | 476 differences within repeated keys | The finite key is insufficient as an exact endpoint identity |
| Three-prime bank, depth 8, both probes | 298 rows, eight coarse conflicts; zero after adding exact fraction as a diagnostic | The reduced observer must retain fractional safety binding; exact fraction is not proposed as a finite quotient |
| All positive odd 16-bit Collatz sources | 32,768 rows, no repeated full keys | Does not demonstrate reusable transition classes |

One small-bank conflict uses the same source 13, width 4, exponent 3 and
suffix `(1,2)`. Both fractions `885/2048` and `1935095/4194304` satisfy the
current source clause; only the second admits the selected next safe event.
This concerns the finite observer key that forgot fractional information.
It is not a counterexample to the complete parameterized skew-cylinder action.
Likewise source 20 and source 46,676 share a finite key but reach 230 and
531,671: source authority must remain separate from observer equality.

The [joint algebra theory](../../../devtools/proofs/isabelle/mahler_transport/Mahler_Joint_Quotient_Algebra.thy)
checks bounded suffix composition, its base-three encoding modulo 729, and
the distinct lane laws. It does not prove completeness of the experimental
partitions or legal-continuation closure. Its registered
`Mahler_Source_Transport` session passes within the 35-second/4-GiB guard.

The full key observes the completed edge, including its after-edge prime
lanes; it is tested against *subsequent* continuation. It is not evidence
that the current edge can be predicted without source construction. A
pre-edge ablation is reported separately. No experiment publishes a pump,
merges production sources, or certifies all-time safety.

```console
python -m devtools.experiments.antihydra.barrier_search --mode joint --joint-depth 32 --joint-collatz-sources 65535 --joint-primes full --joint-high-fiber-probes --joint-fractional-probes --max-nodes 20000000
python -m pytest -q -o addopts='' tests/arithmetic/fields/test_branch_quotients.py tests/validation/proofs/test_joint_future_quotient.py
```

Both probes release their ledger-owned retained storage. Local evidence:
`results/current/joint-future-integration/joint-final.log` and
`joint-small-final.log`, with guarded execution reports. The bounds are
explicit experiments, not arbitrary-depth grammar closure or proof of a
production construction bound.

</details>

### Bounded projection publication

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

The projection adapter now references the occurrence cursor's sealed complete
bounded image. It no longer constructs a second chain of eight-return roof
fragments over that image. Source, action, projection key and exact arithmetic
endpoint checks still run before publication. The occurrence owner charges
the class payload; the adapter charges its references and seals.

This removes duplicate chronology, not the cursor's bounded physical discovery.
Mahler associated actions retain their separate predicate from physical ledger
safety. Neither the Q95 local interface nor the new Collatz prime buckets
establishes source-7 non-halting or an all-depth Mahler safety invariant.

```console
python -m pytest -q -o addopts='' tests/api/test_antihydra_support_cache.py tests/api/test_antihydra_fragment_audit.py tests/api/test_antihydra_projection_occurrences.py tests/api/test_antihydra_mahler_action.py
```

Status: **finite arithmetic and demanded-cylinder laws are checked; the
source-7 all-time barrier and complete literal/macro refinement remain open**.

Antihydra has three related semantics that must remain distinct: the total
arithmetic family, the guarded ledger computation, and the literal six-state
machine. Mahler/Hensel outputs are projections of authenticated arithmetic
source data; they are not alternate evidence that the literal machine never
halts.

</details>

### Shared Collatz F5 spatial action: checked transfer

Record period: 2026-09-21.

<details>
<summary>Implementation, validation and remaining work</summary>

The September 21 [Collatz spatial patch](../../../docs/research/collatz.md) applies to the centered
Antihydra/Mahler coordinate through the **same production carry/F5 owner**:
[`collatz_f5_quotient.py`](../../../src/number_compiler/arithmetic/carry/collatz_f5_quotient.py).
No second F5 alphabet or source recurrence is needed.

- **Exact arithmetic:** for `D=a-1`, the next centered state is
  `D' = floor((3D+1)/2)`, and the next Antihydra value is `D'+1`.
  This also holds for even `D`; the extra one is discarded by division.
- **Spatial projection:** a radix-64 cell uses the same five complete
  multiplication carry actions on incoming ports `0,1,2`. The joint
  carry/phase leaf alphabet has 15 classes and its spatial compositions reach
  17. The phase is the additive sum of the fixed incoming-one leaf `phi5`
  observations. It is **not** the whole numeral's carry jet, and actual
  inter-cell carries still travel through the complete carry action.
- **Division boundary:** the existing directional F5 views pair adjacent raw
  multiplication outputs after a one-bit shift. They observe the exact next
  centered cell without identifying its source with a class ID.
- **Conditional spatial pumping:** a supplied repeated block can use shared
  binary composition. The new tests power every radix-64 leaf through
  `5^64` spatial repetitions and compare all three carry ports with Mahler's
  independently checked fixed-carry compression. Composition count is
  `bit_length(n)-1+bit_count(n)`; no repeated numeral is expanded.

The [spatial theory](../../../devtools/proofs/isabelle/mahler_transport/Mahler_Spatial_Carry_Pump.thy)
adds `mahler_spatial_low_block_transport` and
`antihydra_centered_spatial_low_block_transport`. For `D=u+2bv`, write
`e=(3u+1) mod 2b` and `c=(3u+1) div 2b`. They prove

\[
D'=\lfloor e/2\rfloor+b(3v+c),\qquad a'=D'+1.
\]

At radix 64, `b=32`. This transports both the emitted block and its high
boundary, for arbitrary high part `v`. It reuses the existing centered-step
and carry-conservation lemmas. The owning `Mahler_Source_Transport` session
passed its oracle audits on September 21 in 8.81 seconds with 1,672,236,704
sampled peak bytes, within the unchanged 35-second/4-GiB limit. These are
checked arithmetic transport lemmas, not a formal refinement of the Python
F5 tables or a complete temporal constructor.

The [production bridge tests](../../../tests/validation/proofs/test_mahler_f5_production_bridge.py)
check every two-cell residue at both a small high fiber and `2^80+37` against
`admitted_arithmetic_cylinder`. They also compare spatial carry actions with
the independent Mahler multiplier reference and preserve the observer
collision `67,75 -> 101,113`. That collision concerns the reduced spatial
observation, not the complete source-bound cylinder.

**Temporal boundary:** for an odd centered source `U` and
`a=v2(3U+1)`, Antihydra's next odd event is

\[
U'=3^{a-1}(3U+1)/2^a,\qquad E'=E+3-a.
\]

The extra `3^(a-1)` distinguishes it from an ordinary accelerated Collatz
event. Bounded tests compare this law, the actual parity word, and the
minimum-prefix ledger with production cylinders for every odd source from
5 through 4095. The fractional-safe guard remains a separate consumer.
Neither the 17 spatial classes nor fast powering of a supplied repeated
block proves a source-compatible temporal grammar, a CLI speedup, Mahler's
global exclusion, or the Antihydra source-7 barrier.

Reproduce the bridge with:

```console
python -m pytest -q -o addopts='' tests/validation/proofs/test_mahler_f5_production_bridge.py tests/validation/proofs/test_mahler_centered_production_bridge.py tests/validation/proofs/test_mahler_spatial_carry.py
isabelle build -d devtools/proofs/isabelle Mahler_Source_Transport
```

Local validation evidence and its source fingerprint are retained under
`results/current/mahler-f5-bridge-2026-09-21/`. Historical measurements do not
certify subsequent edits or the aggregate release.

</details>

### Demanded history and the shared joint-adic chart

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

Antihydra arithmetic results and Mahler associated actions now consume the
same authenticated dyadic summary without copying its chronological segments.
`AntihydraArithmeticTerm.segments` is an explicit lazy demand; physical and
support observations still obtain the exact bounded cylinders. A failed
segment publication releases its new entries and can be retried without
invalidating the arithmetic result. Payload audits inspect retained state
without causing materialization.

The Mahler source-prefix check uses the pinned source `h=8`, centered `D=7`,
source precision and arithmetic law. It does not trust a caller-supplied odd
state or rebuild the segment sequence merely to check the initial `11`.
Mahler's existing associated-action projection remains distinct from the
Antihydra ledger predicate.

`source_macro_projection_correct` and `six_step_constant_three_lift` prove
finite endpoint/gain projection and the six-step high-fiber multiplier 729.
`six_step_three_adic_high_fiber_forgetting` proves its contribution vanishes
modulo `3^h` when `h <= 6`. This does not remove the integer high fiber, the
source-selected offset, or the fractional-safety guard. The shared Collatz
carry/F5 observer and Mahler prime/deck restrictions remain projections with
their existing admission conditions. They are not interchangeable source
identities or an all-time safe/fail certificate.

Tests poison segment extraction during public digit, Mahler, metrics and
payload-audit queries. Explicit physical/support demands retain their source,
overwrite and first-failure checks. Python construction/refinement and a global
source-compatible safety invariant remain separate obligations.

At fingerprint `6560841b95ca428e64f941235defc4318cec58b9cfe2f56e9cec7086a894443d`, the 1,024-return probe retained zero copied
segments after digits and after Mahler demand. Explicit segment demand created
16 entries and validated all 16. Total ledger nodes were 7,266 after digits,
8,169 after Mahler and 8,185 after segment demand. Underlying authenticated
source support remains counted; zero copied segments is not zero retained
source history or zero construction work. The endpoint matched an independent
bounded recurrence. Evidence is local under
`results/current/joint-cylinder-2026-09-22/`.

</details>

### Recovered bounded tree-choice observer

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

Antihydra's arithmetic and guarded block composition now use the shared
`PrefixSafety` minimum-prefix transformer, also used for Collatz cycle
compression. Mahler's saturating affine consumer shares the positive affine
threshold inverse with the finite upper-envelope algebra. These are distinct
predicates over admitted actions: the Mahler `11` first-failure regression
still prevents transferring positivity to Antihydra ledger safety. No cycle
or non-halting certificate is inferred for the Antihydra source. See the
[safety integration scope](../../../docs/research/collatz.md#shared-safety-transformers-and-exact-cycle-acceleration).

The external Mahler release contains executable suffix code, not only the
standalone tree-address experiment: `outputs/antihydra_mahler_joint/src/mahler_branch_suffix_observer.hpp`
and `BRANCH_OBSERVER.md` in the supplied September 20 conversation repository.
Its exact observer is now ported as `BranchChoiceSuffix` in
[source_observers.py](../../../devtools/experiments/antihydra/source_observers.py).

- The alphabet is the one-based sibling index 1, 2 or 3, ordered by the legal
  menu. It is not the unbounded q exponent. Length plus ternary code preserves
  leading choice-1 symbols, giving 1,093 encodings for at most six choices.
- Chronological composition truncates concatenation to its last six symbols.
  It neither owns the source nor determines whether an edge is legal.
- All 1,093 states and one-symbol extensions, representative associative
  compositions, malformed inputs and the existing 67-bucket checks pass in
  19 focused tests. This is executable finite validation, not a new Isabelle
  source-closure theorem.
- The 67 figure sums partition sizes across the 20 prime lanes. It is not the
  number of classes of their joint product. The original buckets abstract
  `u -> (3/2)^q*u - 1` over all phases. Direct deterministic transfer to an
  accelerated Collatz event requires a separate intertwining/admission law.
  Sources 3 and 7 have the same mod-5 bucket and both exact Collatz gap 1;
  targets 5 and 11 have different buckets. This witnesses only that particular
  single-observer failure, not failure of the proposed cross-product.

The recovered archive already audits suffix plus prime buckets and a supplied
menu/u729. Its suffix-plus-20-bucket candidate has four repeated interior
keys, three menu conflicts and four successor conflicts; adding the supplied
menu and u729 makes the finite corpus injective. Those historical zero-conflict
rows establish no merger or closure. Their outputs include q-labelled future
classes and bank births, not merely endpoint equality.

The proposed new experiment remains worthwhile: combine the source-bound
joint-adic cylinder, a specified deck projection, the prime possibility lanes
and this bounded choice context, then compare coarsened safety/continuation
outputs. It must derive the common q from the actual family source, specify
how q maps to the sibling alphabet, avoid supplying the very safety/menu output
being predicted as a key, and count repeated keys as well as conflicts. Its
64/729 coordinates must identify their chart: the archive's normalized Z and
u residues are not automatically the accelerated Collatz source/target chart.
This exact combined Collatz experiment has not yet been implemented or proved.
The reusable suffix component is integrated as a research observer; production
admission and current release assertions are unchanged.

</details>

## Reverse/add

### Pullback implementation milestone: 2026-09-21

Record period: 2026-09-21.

<details>
<summary>Implementation, validation and remaining work</summary>

The first prerequisite is implemented in the existing
[`SymbolicInnovationArena`](../../../src/number_compiler/arithmetic/fields/symbolic_innovation.py):
`substitute_many` transports primitive-atom expressions through multiple
innovation roots in one frozen environment. It uses an iterative postorder
worklist and one shared memo, rebuilding through the existing radial, chart
and signed-sum normalizers. It never evaluates coefficients, projects a
polynomial, or recursively rewrites replacement expressions.

Environment, memo and frame storage are ledger owned and released on both
success and refusal. Already interned arithmetic nodes remain valid and
charged after a failed request; no result tuple is returned. Counters separate
attempts, root/binding checks, traversal frames, distinct nodes and memo hits.
The tests cover simultaneous swaps, cancellation, growth/reflection transport,
independent residue-environment evaluation, thirteen shared roots, a depth-1100
DAG, binary-encoded huge extents/powers, foreign handles and budget cleanup.

This is an arithmetic prerequisite, **not yet a production consumer** of the
complete thirteen-channel return. The existing finite-function substitution
and this innovation substitution still need a shared admitted cylinder
environment. Next are predicate/growth transport and complete-effect
normalization, followed by D2/D4/D8 and scheduler publication. The current
chronological refusal and all cutover assertions remain unchanged. The
[proof index](../../../docs/proofs.md) distinguishes the checked substitution specification
from the unproved executable-worklist and temporal-constructor refinements.

Validation at source fingerprint
`c724147015087bf0e15df3ec67fb11d4502169a30242c11669e7e3c6f7be5165`:
the eight new substitution tests, existing innovation/local-output tests and
unchanged range/CLI cutover selections produced **56 passes and 26 failures**.
All failures are the twelve generic-range and fourteen CLI cutover cases.
The 35-second/1-GiB guard recorded 18.16 seconds and 92,979,800 sampled peak
bytes. Local evidence is
`results/current/reverse-pullback-2026-09-21/final-substitution-and-cutover.{log,json}`.
The aggregate Isabelle memory refusal is recorded separately in the proof
index; this milestone is not release closure.

</details>

### F2 forcing elimination in the shared arithmetic

Record period: 2026-09-21.

<details>
<summary>Implementation, validation and remaining work</summary>

Integration date: 2026-09-21. The supplied `196_f5f2_carrier_summary.md`
identifies an independent coordinate that can be removed: for an admitted
block of at least four steps, the homogeneous parity transport is zero and
`F2_block = epsilon_out`. Output parity itself remains part of the complete
carrier. A local 190-class encoding includes the pair symbol and incoming
carry; decoding it does not construct either of those inputs.

The existing `F2SpatialTransport.apply_with_output_forcing`,
`F2AffineTransport.apply` and `F2AffineTransport.then` now return the surviving
forcing directly when the relevant homogeneous transport is annihilated.
They no longer invoke `add(source, source)` or other arithmetic callbacks on
the discarded term. Composition uses this shortcut only when the **later**
linear action is zero; a live later action still transports earlier forcing.
Output-chart alignment and the source pullback of later forcing remain
explicit caller obligations.

`SymbolicInnovationArena.substitute_parity_many` uses the same owned iterative
substitution worklist as exact substitution. It prunes positive no-growth
radial factors and even integer scales before child traversal, reduces odd
scales modulo two, and cancels identical XOR operands. It still substitutes
the surviving forcing in the original environment. The returned expressions
are equivalent **only modulo two**; they cannot replace exact carry/output
expressions or authenticate a successor. Exact substitution is unchanged.

The `Reverse_Growth_Admission` session adds `source_four_step_no_growth`,
`source_block_parity_forcing` and `source_196_block_parity_forcing`. These
derive annihilation from the valid source trajectory, rather than a supplied
growth itinerary. The checked build took 7.89 seconds with 1,341,738,464 sampled
peak bytes under the unchanged 35-second/4-GiB guard. These statements do not
prove the Python worklist, spatial grammar closure or the generic CLI cutover.

Poison tests prevent access to a dead symbolic child and annihilated affine
callbacks; bounded tests preserve reflected charts, signed coefficients,
simultaneous replacements and exact/parity separation. The existing research
carrier consumer is tested with its dead homogeneous application poisoned,
and its no-growth output aliases the forcing handle. No 190-cell word or new
execution owner is introduced. Generic production D4/D8 publication and
elimination of the remaining forcing-discovery scans are still open.

At source fingerprint
`c3017221c1a44fea3a4137c996767ee6feeb6a835b1ca2a4c3257a166482e4e0`,
the combined arithmetic, carrier and unchanged cutover selection reports
**132 passed, 26 failed** in 4.11 seconds. The failures remain the twelve
generic-range and fourteen CLI cutover cases. Guarded runtime was 4.72 seconds
and sampled peak memory 82,002,520 bytes. Raw evidence is local under
`results/current/f2-pullback-2026-09-21/`; this is not a full-suite or release
performance pass.

</details>

### F5 operator reuse versus region-occurrence construction

Record period: 2026-09-21–22.

<details>
<summary>Implementation, validation and remaining work</summary>

The existing `F5SpatialTransport.apply` already constructs the homogeneous
operator through radix-five Frobenius factors. For `r = sum d_j 5^j`, it makes
`sum d_j` shift calls, the same number of addition calls, and one scale call.
That is logarithmic in the growth exponent **if callbacks construct shared
operation handles**. Callback cost, source discovery and carry-forcing
construction are separate; a fixed 25-entry addition table does not bound how
often those operations are applied to different source occurrences.

A 2026-09-21 bounded seed-196 reference supplied the following growth counts.
The callback counts were checked against the existing transport implementation
using opaque operation handles, not a region evaluator or a powered CLI run:

| Right-half interval | q | r | Frobenius factors (stride, multiplicity) | Shift/add pairs | Expanded nonzero shifts |
| --- | ---: | ---: | --- | ---: | ---: |
| 64 to 128 | 37 | 27 | (1,2), (25,1) | 3 | 6 |
| 128 to 256 | 73 | 55 | (5,1), (25,2) | 3 | 6 |
| 256 to 512 | 147 | 109 | (1,4), (5,1), (25,4) | 9 | 50 |

Right-half growth must not be confused with cumulative root growth: D512 from
the original seed has growth 219 and therefore includes stride 125. Reusing
an operator rule does not assert equal growth for both halves of a square.

`ReverseActiveOutputArena.transported_alpha` is a different, bounded point
consumer: it calls `shifts()` and binds one source function per expanded term.
It cannot be treated as the region-transform constructor. The region path must
retain the factored operator and share admitted source-region demands without
expanding them through that point API. The older plane-gate reference instead
zips concrete grammar intervals, which can incur work for each distinct
aligned occurrence despite the fixed gate table.

The added `test_dense_radix_five_transport_keeps_shared_operator_structure`
poisons coefficient expansion and checks a dense exponent `5^64-1`: 256
shift/add pairs share prior roots, even though the expanded support has
`5^64` terms. This is an operator-construction regression, not a proof of cheap
source-bound region evaluation.

The baseline archive was located on 2026-09-21 as
`number-compiler-main-powered-f5f2-carrier.zip` in the supplied Downloads
directory, SHA-256
`780e37ea4abff740976dff4db37ddbe075ad15691b1120b14bbcba33bd140c7e`.
Its `devtools/experiments/reverse_add/powered_f5f2_carrier.py` checks affine
forcing composition and the 190-carrier alphabet. In that bounded reference,
`reverse_add_pair_orbit` computes a literal orbit and `powered_block` obtains
forcing by subtracting the transported source from an already available
target. These are finite algebra checks, not source-derived construction
measurements. The archive itself identifies spatial region quotienting as
remaining work.

The later `powered_class190_regions.py` fragment was supplied separately on
2026-09-21. It composes **supplied** adjacent block observations: transport
left forcing, add right forcing, and retain the right output carrier. Its
shift/add passes scan the entire word, so it establishes the local rule
catalog and exact forcing law, not a source-derived region constructor or
subquadratic temporal construction.

#### Carry-free alphabet and output-residue threshold integration

The September 22 supplied `README(20260922-065353).md` corrects the
alphabet to **95 = 19 pair symbols × 5 forcing values**. Incoming carry is
the prefix action of the threshold field at carry zero, so including it again
in a local symbol is redundant. The maintained
[bounded reference](../../../devtools/experiments/reverse_add/powered_f5f2_carrier.py)
now constructs this word directly, without invoking its carry-report scan.
That report retains incoming/outgoing values only for independent comparison.
The historical 190-class counts below remain historical measurements.

- **Implemented production consumer:**
  [SourceCarryPorts](../../../src/number_compiler/sequences/reverse_add/source_ports.py)
  derives a second-layer threshold directly with `decimal_add_cocycle` from
  the two normalized F5/parity output channels. Reflection uses output extent
  `m+g`; the new leading digit has channels `(1,1)`. Physical carry still goes
  exclusively LSD to MSD. No next-pair coefficient is reconstructed for this
  threshold demand, and the carry interval cache retains only monoid actions.
- **Checked local theorem:** `output_crt_threshold_exact` and
  `normalized_output_crt_threshold_exact` in
  [Reverse_Threshold_Cocycle](../../../devtools/proofs/isabelle/Reverse_Threshold_Cocycle.thy)
  establish the residue-to-threshold law. They consume normalized digits;
  they do not derive an arbitrary future digit's residues from the source.
- **Finite validation:** supplied adjacent blocks compose exactly through D512
  with the 95-symbol alphabet. The 25 F5 additions, 20 nonzero scalar maps and
  95 attachments all occur in the bounded corpus. Source-port tests poison
  next-pair reconstruction and cover seeds 0, 1, 18, 99, 196, 909, 1041, 1051,
  1593. On decisive constant sources of width 16–1024, length demands have
  zero next-pair reads and one CRT-threshold query; validation remains charged.
- **Validation disposition:** the old length counter now requires zero
  second-pair reconstructions plus one CRT-threshold query, preserving the
  source-read and validation bounds. The layer-scoped identity poison moved
  from `_raw_second_pair` to `_second_decimal_cocycle`; it additionally checks
  that the two layers still return distinct actions after a failed demand.
  No positive construction assertion was removed or relaxed.
- **Remaining constructor:** the supplied patch itself says its threshold or
  output grammar must already be available. Computing the right block's
  threshold/output grammar through the left complete effect remains required.
  The positive production D4/D8/D16 tests still fail. Neither a 95-symbol
  alphabet nor a carry prefix query is that missing constructor or its bound.

#### Reachable operator catalog versus the source-only macro

The subsequently supplied `196_powered_reachable_grammar_closure.md` and
`number_compiler_powered_reachable_grammar.patch` describe a fixed catalog of
95 symbols, 25 F5 additions, 20 scales, 19 threshold rules and 9 carry
compositions. Their larger radix-5 strides reuse the existing Frobenius law.
The reported D8192 saturation is a finite experiment, not a size bound for
future recursive occurrences.

The patch's `root_power_grammar_table` first calls
`reverse_add_pair_orbit(seed, max_power)`, then derives both half-block effects
with `powered_block`. Its right block is still supplied by the future orbit.
Consequently the audit does not provide the missing source-only `J4` or `J8`.
No endpoint-oracle table, duplicate finite arithmetic helper or new region
scheduler from that patch has been installed as a production constructor.
The 95-state source representation and the transition constructor are separate
obligations; no additional independent carry-in coordinate is being requested.

#### Local integration of the supplied class-190 fragment

- **Production arithmetic:**
  [compose_f5_forcing](../../../src/number_compiler/arithmetic/fields/f5_innovation.py)
  binds `F5AffineTransport.then` to the existing ledger-owned
  `SymbolicInnovationArena`. Closed chart shifts and shared sums construct
  `L_after B_before + B_after` without coefficient observations. No scheduler
  or occurrence-authority mechanism is added. Both operands must already be
  pulled back into a common source/chart environment; this arithmetic function
  does not establish that admission.
- **Important type scope:** the returned F5 affine action contains integer
  lifts valid modulo five. These lifts must not substitute for exact decimal
  innovations. Source bindings, growth discovery, right-block output carriers
  and F2 admission remain the enclosing constructor's responsibility.
- **Bounded reference:**
  [powered_cocycle_regions.py](../../../devtools/experiments/reverse_add/powered_cocycle_regions.py)
  ports the fragment using the same production Frobenius operator rather than
  copying its factor loop. It reports decoded, shifted, added, scaled and
  attached cells separately from the original 25/20/190 rule catalog
  (updated to 25/20/95 below). For width `w`
  and `s = sum(base5_digits(r))`, its shift work is `sw` and addition work is
  `(s+1)w`. This reference remains outside the installed package.
- **Independent finite checks:**
  [the orbit reference](../../../devtools/experiments/reverse_add/powered_f5f2_carrier.py)
  was selectively recovered from the pinned archive. Its forcing oracle uses
  ordinary binomial coefficients independently of the production Frobenius
  decomposition. Seed-196 supplied-block squares through D512 agree with both
  the word reference and the production shared-handle composition. Carrier
  discovery is poisoned during composition, after fixtures are prepared.
- **Construction check:** dense exponent `5^64-1` creates 514 arithmetic nodes
  from two existing forcing atoms, with 256 shift requests and no coefficient
  expansion. A subsequent integration added a lazy ledger-owned result memo:
  repeating the request validates the handles and reuses the forcing result
  without repeating the shifts or normalization. Clearing that memo retains
  the arithmetic DAG but repeats charged construction requests. This is an
  operator-construction measurement, not a
  source-trajectory performance claim or an Isabelle constructor theorem.

The focused arithmetic/fragment selection passed **27 tests** in 0.28 seconds
under the 35-second/1-GiB guard (0.87 seconds including startup;
41,681,472 bytes sampled peak). Strict mypy passed for the five added files.
Raw local evidence: `/tmp/f5-class190-integration-2.log` and
`/tmp/f5-class190-integration-2.json`. These historical measurements do not
certify later source changes.

```console
python -m pytest -q -o addopts='' tests/arithmetic/fields/test_f5_innovation.py tests/sequences/reverse_add/test_powered_cocycle_regions.py tests/arithmetic/polynomials/test_f5_transport.py tests/arithmetic/polynomials/test_centered_f5.py
```

**Remaining production gate:** `source_images.py` still cannot construct the
right forcing and complete output carrier from the admitted earlier image.
The class-190 composition function consumes that carrier unchanged; it does
not construct it. The generic D4/CLI assertions remain active and are not
discharged by these supplied-block tests.

</details>

### Native source-only D4 squares

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

**Implemented bounded constructor (2026-09-22):**
[FactoredTemporalPower](../../../devtools/experiments/reverse_add/factored_power.py)
now accepts the existing `(domain, F5, epsilon)`
[CocycleReverseCarrier](../../../devtools/experiments/reverse_add/cocycle_carrier.py).
Its base macro constructs at most four native grammar advances. Higher powers
compose the emitted `F5AffineTransport` objects; the right macro receives the
left macro's returned grammar, rather than an oracle trajectory row.

- No pair tuple decoding, future orbit lookup or coefficient-array import is
  needed after admitting the source. The existing bounded reference remains
  available for independent verification; its supplied right rows are not used
  by this constructor.
- Every positive block retains its terminal normalized F5/parity output
  channels. The symmetric pair grammar alone loses digit orientation and is
  insufficient for terminal emission. Index zero still uses the original seed.
- Tests poison orbit helpers, pair decoding and plane imports while constructing
  D4, its right D4, D8, D16 and D20. Eight seam seeds are checked against an
  independent integer reference. Seed 196 at D20 emits `70446464506`.
- Lifetime plane-work and gate-hit counters survive per-operation resets.
  A repeated macro reuses its result; this is measured separately from cold
  source construction.
- Temporal composition retains the right block's returned grammar. It no
  longer reapplies the accumulated F5 action to the original source at every
  internal node. Tests forbid that redundant application during construction
  and check its equality separately afterward.

**Proof scope:** `native_emit_refines`, `native_step_refines`,
`native_iteration_refines`, `native_terminal_emission_refines` and
`native_macro_refines` in
[Reverse_Threshold_Cocycle.thy](../../../devtools/proofs/isabelle/Reverse_Threshold_Cocycle.thy)
specify native carry, growth, output and chronological macro semantics.
They prove equality with the literal pair recurrence for every finite macro
level. This executable word model is the specification of the rope operations;
it does not prove the Python rope interner, resource publication or compression.

**Remaining construction and production obligation:** cold D20 on seed 196
still performs 20 native grammar advances. No bounded vocabulary or sublinear
temporal construction follows from composing their affine projections. The
research rope arena is endpoint-construction guarded and has process-global
interning, not production ledger admission. It remains outside the installed
package. Generic production D4 acceptance is therefore still required; importing
this arena into the CLI would bypass the very gate being tested.

Frozen-source diagnostic measurements (`6e8eb712f8a1`, five fresh processes per
extent through D256) separate construction from source import and digit output:

| Extent | Native advances | Construction work | Median construction |
| --- | ---: | ---: | ---: |
| D4 | 4 | 542 | 3.51 ms |
| D16 | 16 | 3,401 | 22.33 ms |
| D20 | 20 | 4,789 | 31.67 ms |
| D64 | 64 | 36,082 | 273.75 ms |
| D128 | 128 | 128,622 | 1,077.93 ms |
| D256 | 256 | 471,980 | 4,507.35 ms |

Removing redundant accumulated-action application reduced work by about
24–25% at D20, D64 and D256. A single additional D512 sample completed in
21.28 seconds including process startup; D1024 timed out at 35 seconds. These
last two extents do not have five final-source samples and do not satisfy the
complete release manifest. Earlier five-trial measurements, before that
removal, completed through D512 and timed out on every D1024 sample. Full
diagnostic records live locally under
`results/current/source-macros-2026-09-22/`; they are not portable artifacts.

Reproduce one cold sample in a fresh process; the command reports the warm
repeat separately and performs literal validation only after construction:

```console
python -m devtools.proofs.reverse_factored_carrier native-macro --seed 196 --steps 20
python -m pytest -q -o addopts='' tests/sequences/reverse_add/test_cocycle_carrier.py tests/sequences/reverse_add/test_factored_carrier.py
isabelle build -d devtools/proofs/isabelle Reverse_Residuals
```

</details>

### Spatial residual bisimulation and repeated-work fixes

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

The native constructor avoids integer endpoint decoding, but still makes one
grammar advance per represented temporal step. Each advance can encounter new
spatial regions. Thus its quadratic measurements cannot be attributed solely
to a cache bug or interpreted as a counterexample to a complete cylinder.

The September 22 profile did identify removable repeated work in
[PlaneAlgebra](../../../devtools/experiments/reverse_add/factored_planes.py):

- Gate requests now normalize constants and repeated aligned input views into
  a complete finite residual function before traversing a region. Gate names
  and the original positions of constant runs do not distinguish semantics.
  Partial functions retain `None`; undefined inputs never become defined zero.
- Constant and projection residuals return a run or an existing input subtree.
  A clipped projection visits only the two interval boundaries, preserving
  complete interior subtrees instead of rebuilding an identity map.
- Exact residual results share a bounded 4,096-entry FIFO of weak references.
  This cache does not own endpoint words. The source-free cofactor catalog has
  a separate 512-entry bound; eviction, reset, bypass, compilation and hits are
  measured. Neither cache authorizes substitution of a different source image.
- [Canonical rope memo cleanup](../../../src/number_compiler/arithmetic/automata/program_word.py)
  no longer scans accumulated global tables on every grammar advance.
  Automatic sweeps wait for the population to double after cleanup; explicit
  cleanup remains immediate. The probe reports visited cleanup keys separately.

**Checked local laws:** `plane_complete_residual_bisimulation`,
`plane_cofactor_entry_refines`, `plane_cofactor_undefined_exact`,
`plane_projection_elimination`, `plane_constant_elimination`,
`plane_cofactor_spatial_split` and `plane_cofactor_interval` in
[Reverse_Factored_Channels.thy](../../../devtools/proofs/isabelle/Reverse_Factored_Channels.thy).
The executable table model checks equality on every supplied assignment, with
constants and aliased ports substituted simultaneously. Python enumerates the
complete finite input product. The tests independently exercise all 81 partial
two-input Boolean tables under every constant/alias pattern, large projection
intervals, foreign sources, eviction and weak-reference lifetime.

`automatic_sweep_charged_to_insertions` supplies the local amortized inequality:
when the population has doubled, visiting it costs at most twice the entries
inserted since the previous sweep. This bounds cleanup bookkeeping, not the
number of semantic regions the temporal constructor creates. The checked
spatial rules likewise do not establish finite temporal bisimulation, Python
worklist refinement or production admission. Those release gates remain active.

**Measured scope:** authored-source fingerprint
`2f3dc54b3011e335bd7e6be41f4591ead9f7e4ee412d239591879bd9fa4ffe95`.
Five fresh-process trials per horizon used the unchanged 35-second/1-GiB
guard; discovery, construction, warm repeat and rendering were recorded
separately. The following medians describe the research constructor, not the
installed CLI:

| Steps | Construction | Plane work | Native grammar advances | Exact residual reuse hits |
| --- | --- | --- | --- | --- |
| 20 | 33.77 ms | 4,402 | 20 | 326 |
| 64 | 274.93 ms | 26,158 | 64 | 2,158 |
| 128 | 1.060 s | 90,304 | 128 | 6,364 |
| 256 | 4.329 s | 332,484 | 256 | 17,602 |
| 512 | 19.179 s | 1,277,547 | 512 | 48,913 |
| 1,024 | All five timed out | Unavailable | Unavailable | Unavailable |

The prior D128 measurement was 128,622 plane operations / 1.078 seconds;
the new work count is 29.8% lower, but latency improves only slightly. Small
horizons incur some normalization overhead. These historical timing samples
are not paired acceptance comparisons. The approximately quadratic temporal
cost remains visible; no missing timeout sample counts as zero work.

**Remaining composition defect:** `FactoredPowerBlock.action` is a
source-specific F5 affine action. The complete target domain/parity grammar
and emission are concrete returned objects, not a normalized transformer
that can be squared on a new source. After constructing seed-196 D4, disabling
`successor_with_emission` makes D8 fail at `FactoredTemporalPower.block`'s
native base branch. The right half still needs fresh grammar advances.
This is an implementation-obligation witness, not a counterexample to a
possible complete cylinder quotient. The existing research bimachine
composer first constructs universal witness contexts and does not supply the
required source-admitted replacement.

Local evidence resides under
`results/current/plane-bisimulation-2026-09-22/`: `reverse-trials.json`,
`reverse-summary.json`, `d4-no-replay.json`, guards and raw logs. The full
unit selection has 6,229 passes and exactly the same 42 failing node IDs;
the explicit CLI cutover selection retains 14 failures and six passes.
The 71 focused checks pass, including complete partial-table enumeration,
cache reset/eviction and source-authority tests. These results preserve the
positive construction gates rather than treating refusal as success.

```console
python -m pytest -q -o addopts='' tests/sequences/reverse_add/test_factored_carrier.py tests/sequences/reverse_add/test_cocycle_carrier.py
python -m devtools.proofs.reverse_factored_carrier native-macro --seed 196 --steps 128
isabelle build -d devtools/proofs/isabelle Reverse_Residuals
```

</details>

### Demand-specific forcing retention

Record period: 2026-09-22.

<details>
<summary>Implementation, validation and remaining work</summary>

The research `FactoredTemporalPower` now shares one postorder driver between
endpoint-only and complete-action requests. Endpoint requests retain the
returned native grammar and omit composition of unrequested historical affine
forcing. Complete requests still construct the exact accumulated F5 action.
Their caches are distinct: a complete action can answer an endpoint request,
but an endpoint memo entry cannot authorize a complete action. Both count
against the same cache-entry limit.

This removes redundant action work, not primitive source discovery. Cold D32
still makes 32 native advances. The research constructor remains outside the
installed reverse/add production path until the complete temporal admission
and construction gates pass.

The proposed local encoding `(S mod 5, S mod 2, [S>9])` is injective on the
admitted decimal pair range `0..18`. It collides on 10 and 20 outside that
range. It also does not define a context-free successor: seeds 111 and 191
have pair fields `(2,2,2)` and `(2,18,2)`, sharing the low pair 2, while their
next pair fields are `(4,4,4)` and `(5,16,5)`. The difference comes from the
spatial carry context. These scoped witnesses reject an overextended local
recoding rule, not the complete source-bound cylinder. Physical carry remains
LSD to MSD.

The endpoint tests poison historical affine composition, compare bounded
independent pair arithmetic, and then demand the complete action to ensure
endpoint reuse cannot hide missing action work. No subquadratic temporal bound,
complete grammar closure or new production cutover follows from this change.

At authored-source fingerprint `6560841b95ca428e64f941235defc4318cec58b9cfe2f56e9cec7086a894443d`, five cold/warm trials for each
seed 1 and 196 and each horizon 4, 8, 16, 32 and 64 passed independent bounded
pair recurrence checks. Selected seed-196 medians:

| Horizon | Endpoint plane work | Complete-action plane work | Endpoint cold ms | Complete-action cold ms | Primitive advances, either demand |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 16 | 2,475 | 2,904 | 19.143 | 22.074 | 16 |
| 32 | 5,972 | 7,348 | 56.399 | 67.208 | 32 |
| 64 | 18,725 | 23,185 | 216.360 | 261.014 | 64 |

Warm requests added no primitive advances. The 100 demand samples completed
in a 6.60-second/26,362,360-byte guarded probe. These are research demand
comparisons, not cold CLI timings or the full 16–1024 release manifest. Local
evidence is `results/current/joint-cylinder-2026-09-22/demand-measurements.json`;
its companion `demand-probe-definition.json` records the exact bounded probe.

</details>


## Additional dated evidence

These relocated records supplement the topic summaries above.

### Source-only macro construction measurements

Relocated evidence from the collatz synthesis; original scope and dates below.

<details>
<summary>Recorded implementation and evidence</summary>

**Performance scope:** generator reuse is measurable, but cold construction
still creates a number of residuals proportional to unmatched source extent.
The first five-trial comparison retained the same number of support nodes and
regressed median latency at extent 1024: Collatz 16.245 → 19.625 ms;
Antihydra 15.405 → 20.005 ms. These samples are local diagnostic evidence under
`results/current/source-macros-2026-09-22/`, not a speedup claim or a replacement
for the unchanged release workloads.

```console
python -m pytest -q -o addopts='' tests/hashlife/execution/test_dyadic_effect_reuse.py tests/api/test_antihydra_mahler_action.py
isabelle build -d devtools/proofs/isabelle Shared_S_Arithmetic
```

</details>

### Exact cycle acceleration measurements

Relocated evidence from the collatz synthesis; original scope and dates below.

<details>
<summary>Recorded implementation and evidence</summary>

Five-trial measurements at source fingerprint `6196423ddd7f` cover seed 27
and physical horizons `1000`, `10^6`, `10^12`. Fresh CLI median latency was
108, 142 and 138 ms; cache-bypassed API value demands were 6, 18 and 41 ms.
All three constructed 128 primitive steps before reusing exact cycle effects.
Retained entries were 169, 502 and 1,180: temporal extent still has logarithmic
scheduler overhead. Warm medians were 13–16 microseconds and are reported
separately. Local raw evidence is `results/current/cycle-safety/measurements.json`;
these are cycle-specific measurements, not the full growth manifest or a
paired before/after speedup claim.

</details>

## Documentation consolidation, September 22

- Moved 34 implementation/evidence records from four research papers into
  W38/W39. Research prose fell from 3,092 to 2,087 lines across the six papers
  (about 32%); mathematical scope and open obligations remain explicit.
- Added topic navigation, expandable historical detail, provenance mapping and
  a documentation-placement rule. Preserved existing incoming section anchors.
- The documentation checker and its six regressions pass. Both preserved
  external reverse/add archive hashes are unchanged.
- Authored code/proof fingerprint remains
  `a7b76d65ad48bb81284a90e21a552ab739e33f7e2fc262d8f0755d73cf65a1b3`.
  No runtime, proof or performance gate was rerun or closed by this edit.

Reproduction:

```console
python -m devtools.checks.docs_index
python -m pytest -q -o addopts='' tests/repository/test_docs_index.py
```

## Temporal patch cutover audit

- **Objective:** evaluate the new 196 patch for source-bound temporal cutover
  and remove redundant semantic state without weakening admission.
- **Input scope:** the downloaded Frobenius patch changes a research experiment,
  bounded tests and result files. It has no production constructor or Isabelle
  edits. `root_lift_table` calls a literal orbit; generator routines expand
  integer coefficient tuples. The corrected semantic tables supersede the
  earlier claim that exact B layers must be retained quotient state, but still
  leave recursive source-occurrence construction/right congruence open.
- **Changes:** complete finite transforms now identify undefined and false
  guards through a total admission predicate. Reverse/add derives Q95 carry
  without interning a redundant coordinate-output view. A Collatz regression
  verifies that equal carry/F5 observations at sources 67 and 75 do not permit
  borrowing their different second-event source continuations.
- **Proof scope:** canonical guard and complete partial-image composition laws
  were added to the existing interface theory, with oracle audits. Extensional
  congruence assumes complete function equality. Occurrence-only equality and
  incomplete modular views remain insufficient; these are not counterexamples
  to the proposed complete cylinder.
- **Validation:** 153 focused tests pass; strict mypy, Ruff and formatting pass.
  The registered temporal session exceeded 35 seconds at 3,725,219,864 sampled
  peak bytes. A focused session checked exact copies of the changed theory and
  its three local dependencies in 8.62 seconds / 1,504,333,376 bytes. No theorem
  bodies or imports were weakened. That diagnostic is not aggregate acceptance.
- **Independent review:** the cross-family reviewer verified admission
  totalization and flagged the retained-observer boundary. The first full run
  caught a scalar-restriction regression, and review caught a subset-port guard
  regression in the proposed batch fix. Final normalization widens the guard
  and totalizes it with selection; the scalar path remains poisoned. Only output functions
  participate in successor identity; separately requested observers cannot be
  silently promoted to future-relevant state. No 196 Q95 recurrence was
  substituted for the distinct Collatz or Antihydra laws.
- **Remaining work:** `source_images.py` still has no general chronological
  reverse/add constructor. D2 and a guarded same-carry chamber are insufficient
  for generic D4/D8. Source occurrence plus saturated regional action must produce
  the complete target occurrence without replay or midpoint realization. That
  constructor, executable refinement and a successful cost bound remain red.
  Raw B history need not be restored to semantic ActionID.

Frozen authored source:
`ef94eb6e60425427778a600008a38d0f9831f7a7ba21573a54299f9fff0ddee9`.
Local evidence: `results/current/temporal-patch-cutover-audit/` (`scope.json`,
`focused-v3`, `proofs`, `proofs-scoped`, `scoped-proof.json`).

| Downloaded input | SHA-256 |
| --- | --- |
| `number_compiler_196_f5_lift_frobenius_release.patch` | `3b00788b2e3166bfe5fa6278a8383cdb2652cdde1f8aa318ad198bb649acac26` |
| `196_f5_lift_frobenius_release_table.md` | `b9f5ea4ce8a29e94f79321bf861a58918c5e06fa6483143d747279ab2b4fc8df` |
| `196_corrected_semantic_innovation_table.md` | `929e48a4975fa3b5739bf38d91d30c99e6e7d46000064c27ee425fae0799a0e0` |
| `196_release_semantic_only_table.md` | `29a2ad710246704afee53cace0e8c0a650b97ae6ebe1fa87274beff2c39415f9` |

Final serial validation on that fingerprint: **6,446 unit PASS / 42 FAIL**,
with exactly the same failing node IDs as the preceding sprint run; no skips
were added. The unchanged explicit cutover selection has **14 FAIL / 6 PASS**.
The unit guard completed in 210.13 seconds with 812,352,640 sampled peak bytes
under the 300-second/1-GiB limit. Final focused validation has 153 passes in
3.75 guarded seconds. Raw final stems are `unit-final`, `focused-v3`,
`cutover-final` and `failure-comparison.json`. No successful recursive source
construction or new asymptotic performance evidence was produced.

Strict mypy (1,475 files), Ruff, formatting, repository policy, documentation
links and the proof inventory pass on the frozen source. The fresh installed
wheel check passes in 5.16 seconds / 115,165,224 sampled peak bytes. Evidence:
`quality.json`, `installed-wheel`; wheel SHA-256
`3b42ed1a34644cfaf6dd5354e6a0b96729bafa1b9697b7d52104e904d72ed279`.

## F5 observer and safety transfer

- **Objective:** transfer the shared carry/F5 observer into Mahler source
  observations and state precisely what dying inherited forcing permits.
- **Changes:** `source_observers.observe_event` folds each multiplication's
  radix-64 columns into the existing `CollatzF5SpatialAction`. It retains one
  summary per multiplication, replacing the per-column carry-map tuples. All
  three incoming carry responses and the additive F5 phase survive. Source,
  prime lanes, subtraction and fractional guards keep their existing owners.
  Column visits and F5 compositions remain charged; this bounded diagnostic
  still computes its supplied event and is not a new CLI jump constructor.
- **Established results:** `at_least_five_births_source_independence` and
  `annihilated_jet_future_consumer` extend the existing checked nilpotence law
  to longer blocks and subsequent shared continuation actions. The proof
  counts multiplication births, not physical ticks. Newborn offsets and the
  source authority selecting future births are not erased. No skipped proofs
  or new axioms were introduced; both results enter the existing oracle audit.
- **Regression coverage:** independent integer carries and binomial-coefficient
  F5 references check the Mahler observer, including a 120-bit numerator.
  Admitted Antihydra centered macros match the common primary transport over
  moduli 5 and 32. Collatz sources 1 and 5 reach the same constant jet after
  eight events, but their source-relative strict-descent answers differ. This
  only distinguishes the jet projection from the complete safety action; it
  is not a counterexample to the complete cylinder.
- **Validation:** 132 focused tests and 211 dependent Mahler/F5 tests pass under
  separate 35-second/1-GiB guards. Strict mypy checks all 1,475 configured
  files; Ruff and formatting pass. Exact copies of the three-theory harmonic
  dependency chain pass in 13.10 guarded seconds / 1,499,188,416 sampled bytes.
  The first registered-session build exceeded 4 GiB; its failure is retained.
  The registered `Reverse_Residuals` session then passed in 29.93 seconds /
  718,146,992 bytes with task-local Java heaps of 128–512 MiB and ML heaps of
  128–1,800 MiB, under the unchanged 35-second/4-GiB guard. All proofs remained
  enabled; no user settings were changed.
- **Remaining work:** no general future-birth constructor, source-global safety
  theorem, non-halting result or CLI asymptotic speedup follows from these
  changes. Existing production release holds remain unchanged. The full unit
  and aggregate release selections were not rerun for this scoped change.

Authored source fingerprint:
`d8acff413e7042d79e3a7ddd50d9b51d1130d2b5523039b086f3fd5b7a94abc5`.
Local evidence: `results/current/f5-safety-transfer/` (`focused`,
`mahler-consumers`, `proof`, `proof-scope.json`, `registered-proof`,
`registered-proof-small-heaps`).

Reproduction:

```console
python -m pytest -q -o addopts='' tests/validation/proofs/test_mahler_source_observers.py tests/validation/proofs/test_mahler_f5_production_bridge.py tests/arithmetic/polynomials/test_primary_jet.py tests/sequences/collatz/test_saturated_future.py tests/api/test_antihydra_mahler_action.py
isabelle build -d devtools/proofs/isabelle -j 1 -o threads=1 -o parallel_proofs=0 Reverse_Residuals
```

## Provider executor and reverse cutover trace

- **Finding:** the production `ProviderFieldImageExecutor` contains the iterative
  publication traversal, but has no reverse family adapter. Its existing
  completed-provider test supplies an idempotent fake adapter and returns a
  cached parent, so it does not establish cold reverse temporal construction.
  The real reverse `apply_composite` still selects D2 or same-carry chambers;
  `compose_chronological` refuses. `196 --nth 20` still fails there.
- **Missing integration:** implement complete temporal output/admission
  composition and growth/reflection transport in the provider adapter's
  `compose_actions`, `compile_leaf` and `join` hooks. The current local codec
  is spatial; the primitive thirteen-channel substitution is not yet lifted
  to this recursive temporal adapter. No counterexample to the proposed
  complete cylinder was established by this trace.
- **Fix:** completed provider inputs now revalidate exact image bindings and
  published extent/context before resolution, including warm hits. Tests
  reject altered source, level, extent and request records, and a revoked image
  binding while the image itself remains live. No new evaluator was introduced.
- **Validation:** 95 provider/image tests pass; strict mypy (1,475 files),
  focused Ruff and formatting pass. The unchanged cutover selection remains
  **14 FAIL / 6 PASS**. No full-unit or Isabelle rebuild was needed for this
  scoped Python validation fix; no mathematical proof changed.
- **Completion boundary:** this fixes publication authority, not the missing
  reverse constructor. The CLI has not been reconnected and the production
  release hold is unchanged. The prior F5 observer work was a separate task.

Authored source fingerprint:
`4a6075b9c4d35885ddcc0292f98955eeddfa40c89bb9f0aadf2940515103869f`.
Local evidence: `results/current/provider-cutover-audit/` (`focused`, `cutover`,
`scope.json`). Commands use the unchanged 35-second/1-GiB process guard:

```console
python -m pytest -q -o addopts='' tests/hashlife/test_provider_bindings.py tests/resources/test_recursive_field_images.py tests/hashlife/test_image_domains.py
python -m pytest -q -o addopts='' tests/validation/proofs/test_reverse_temporal_publisher_cutover.py tests/validation/proofs/test_family_digit_cylinder_cutover.py
python -m number_compiler 196 --nth 20
```

## Temporal production agent wave

- **Ownership:** reverse constructor/streaming worker; cross-family authority
  and slow-path worker; provider extent/refinement worker. The coordinator
  handled traversal accounting, the streaming proof and serialized validation.
  Workers independently reviewed chart separation, extent propagation, handle
  keys and failure cleanup after implementation.
- **Reverse output:** D1 and D2 streaming now carry one physical LSD-to-MSD
  carry instead of issuing a second-layer prefix query for every emitted
  digit. D2 obtains its source pairs lazily through the existing output
  cocycle. Independent bounded references and poisoned point/prefix helpers
  cover growth, zero, changed carries and 256-digit sources. First-layer
  discovery remains charged; this does not remove temporal construction work.
- **Provider correctness:** cold traversal keys include the complete input and
  chart. Image occurrence and provider-binding keys include admitted active
  extent, while semantic action identity remains independent of that extent.
  A scoped root does not silently authorize its children: their exact scoped
  image publications must exist before splitting. Temporary traversal frames
  and result bindings are charged and released on success or failure; cached
  child visits remain visible in work counters.
- **Shared seals:** remove per-field anchor tuples from publication guards and
  account for the smaller retained representation. Snapshot and typed-key
  checks now include handle-subclass fields, including orientation and
  innovation seals. Owner identity remains exact. Only the known immutable
  action-transform enum is admitted; foreign mutable enum payloads are rejected.
- **Checked theorem:** `streamed_digits_fold` and
  `streamed_digits_refines_terminal` in `Reverse_Digit_Terminal_Refinement`
  prove the streaming consumer for admitted pair coefficients. They enter the
  existing oracle audit. The first registered build timed out after rebuilding
  `Reverse_Residuals`; the retry passed in 7.71 seconds / 675,172,576 sampled
  bytes with that checked parent cached. Both attempts retain the unchanged
  35-second/4-GiB guard; task-local heap sizes were reduced without changing
  Isabelle settings. No powered source-constructor theorem is claimed.
- **Open constructor:** arbitrary reverse D4+ still needs a complete recursive
  output/admission/growth transformer for the provider adapter's leaf and join
  operations. The primitive spatial codec and generic traversal do not supply
  that operation. Neither a deferred midpoint evaluator nor four primitive
  grammar advances was accepted as powered construction. No counterexample to
  the proposed full cylinder was found.
- **Other families:** profiling still finds bounded source discovery and
  publication work in Collatz and Antihydra/Mahler. The smaller seals preserve
  authority but do not establish sublinear source construction. Antihydra
  N2048 still exceeds its default publication-node budget; no limit was raised.

Authored source fingerprint:
`0447102b0e0b1a2fe46d6ff1e283159924d6ad96064a62c0035a2b80d4c756f5`.
Local evidence: `results/current/temporal-production-wave/`. The combined
focused selection passes 293 tests. Frozen-source results below do not
supersede historical performance gates.

Frozen-source validation:

| Check | Result | Evidence and scope |
| --- | --- | --- |
| Focused provider, seal, streaming and family consumers | 293 PASS | `focused.xml`, `focused.guard.json`; 3.32 s / 98,124,904 sampled bytes |
| Default unit selection | 6,468 PASS / 42 FAIL / 1,893 deselected | `unit-final.xml`, `unit-final.guard.json`; 208.93 s / 801,358,976 bytes; same 42 failed node IDs as the previous baseline, no new failures |
| Unchanged reverse/family cutover selection | 14 FAIL / 6 PASS | `cutover.xml`; no gate was removed, skipped or converted to expected failure |
| Strict mypy, Ruff, formatting, policy, documentation | PASS | `quality.json`; 1,475 configured files, no new suppressions |
| Isabelle inventory | PASS | 19 sessions / 106 theories; structural inventory is separate from proof execution |
| Registered `Reverse_Digit_Terminal` build | PASS on retry | `reverse-stream-proof-v2`; scoped streaming theorem only, cached checked parent; original timeout retained |
| Isolated wheel and installed CLI | PASS | `wheel-build-isolated`, `installed-wheel`; installed check 5.06 s / 113,969,192 bytes; source fingerprint unchanged |

Reproduction uses the existing process guard: 35 seconds / 1 GiB for probes,
300 seconds / 1 GiB for the default unit suite, and 35 seconds / 4 GiB for
Isabelle. The two production profiles (`collatz.prof`, `antihydra.prof`) are
diagnostics, not five-trial performance acceptance. Complete growth and
all-session gates remain at their previously recorded release holds.

## Bounded D4 bases and larger transported powers

- **Authorized change:** a constant number of linear base steps is allowed.
  This does not authorize describing one nonlinear advance per represented
  temporal step as sublinear source construction.
- **Production change:** the shared dyadic residue owner constructs D1–D4
  directly from at most four low-residue branch classifications. It computes
  the chronological skew numerator/denominator, branch word, odd count and
  prefix-safety minimum together. D8+ uses the existing transported right
  residue and composition worklist. Collatz and Antihydra use the same code;
  Mahler consumes Antihydra's admitted composed image. Each base step and its
  arithmetic operand sizes are counted. No persistent D4 cache was added.
- **Rejected cache:** independent review found that the tentative retained D4
  entries did not independently authenticate foreign-law replacement and
  could consume capacity needed by required publication. The candidate was
  removed; the bounded base has no extra retained cache or authority.
- **Metrics repair:** unindexed reports now forward the recorded direct point
  query count instead of a positional default zero. A regression checks the
  captured report is stable and reading it causes no additional queries.
- **Measurements:** fresh source-image workspaces at N1024 reduce arithmetic
  macro compositions from 456 to 240 for Collatz seed 931386509544713451 and
  from 470 to 240 for Antihydra. The respective bounded base-step counts are
  608 and 664. Retained nodes stay 5,862 for both. These are different work
  categories, not a claim that 240 operations represent all construction work.
  N4–1024 diagnostics include five fresh after-change trials; the before-change
  sample has one trial per point, so no paired latency gate is claimed.
- **Reverse audit:** the existing research J4 returns an exact three-plane
  occurrence and affine projections. Its D8 still constructs the right J4 by
  further nonlinear advances. Fresh seed-196 D4/D8/D16/D32 use respectively
  4/8/16/32 advances and 655/1,517/3,300/8,064 plane-work ticks; seed 1 uses
  112/517/1,399/5,768 ticks. No production cutover was made: the complete
  recursive domain/F5/half output and growth/admission transformer remains
  missing. This is an implementation trace, not a counterexample to the full
  cylinder or a request for additional semantic history.

Local evidence: `results/current/d4-temporal-connection/`, including
`before.json`, `after.json`, `reverse-construction.json`, and `proof-scope.json`.

- **Proofs:** `collatz_physical_admitted_leaf_loop_refinement` and its D4
  specialization in `Collatz_Physical_Cylinder_Lift` model the new loop's
  current value, complete skew coefficients, branch labels, odd count, delta
  and minimum. The registered `Collatz_Cylinder_Refinement` / `Antihydra`
  command passes in 12.80 seconds / 710,675,840 sampled bytes under the
  unchanged 35-second/4-GiB guard (`proofs-leaf-v8`). Antihydra reuses its
  existing checked leaf-loop and ledger-split results. Oracle audits include
  the new Collatz theorems. Failed development builds remain local evidence
  for their earlier source revisions; they do not certify the final revision.
- **Focused checks:** 133 unit cases pass (`focused-final`), including
  independent high fibers and public Collatz/Antihydra D4/D8/D16/D32 queries
  and a partial-block boundary with physical and causal execution poisoned.
  The broader initial selection also exposed three existing Collatz validation
  failures involving legacy source-morphism and metric expectations. They are
  retained as failing release checks, not replaced by the new unit tests.
- **Review:** independent agents reviewed the bounded generator arithmetic,
  occurrence authority, lack of extra retention and proof scope. All rejected
  persistent-cache edits were removed before freezing.

Frozen authored-source fingerprint:
`95b10a87614f42ac6f4f13ba44c25e4c8e3ebeb1193454022776882620d4a5ce`.
Final full-unit, quality and installed-wheel results are recorded with that
fingerprint in the local evidence directory. Reverse CLI cutover, general cold
construction bounds and global safety/non-halting remain separate release holds.

Final validation on this fingerprint:

| Check | Result | Scope |
| --- | --- | --- |
| Full unit selection | 6,479 PASS / same 42 FAIL | 202.50 s / 812,385,408 sampled bytes; exact failed-node comparison has no additions or removals |
| Expanded cutover selection | 17 FAIL / 9 PASS | Original reverse/family selection remains 14 FAIL / 6 PASS; the added Collatz module contributes three failures and three passes |
| Strict mypy, Ruff, formatting, policy, docs, proof inventory | PASS | 1,475 configured files; 19 registered sessions / 106 theories |
| Focused finite proofs | PASS | Registered sessions and exact theorem scope above; no all-session or source-global theorem claim |
| Isolated wheel and installed CLI | PASS | `installed-wheel`; 5.18 s / 114,362,408 sampled bytes; 15 public CLI contract cases |

The internal bounded-work assertion now charges every direct base step and
checks at most four steps per base call. Its previous bound counted memoized
one-step alphabet admissions inside a different base implementation. Literal,
high-fiber, skew, branch, safety and release-construction assertions remain.


## Adversarial ownership and duplicate cleanup

**Objective:** remove unused execution owners and duplicated arithmetic/proofs,
while retaining positive tests for the incomplete powered constructors. Three
agents audited continuation ownership, family algebra and theory dependencies;
the continuation and algebra owners then reviewed each other's changes.

| Component | Disposition | Verification scope |
| --- | --- | --- |
| `virtual_field_provider.py` | Deleted its 154-line unreferenced implementation | No repository imports, dynamic names, facade exports, tests or proof consumers; absence added to the existing retired-module test |
| Antihydra total/guarded cylinder joins | One CRT/source-chart/skew helper | Both consumers retain their own semantics; high-fiber composition, ledger threshold and physical identity regressions |
| Arithmetic-only Antihydra queries | Physical roof translation remains lazy | Independent review caught and removed an extra bigint calculation introduced during consolidation |
| Private Collatz compiler forwarding method | Removed; dispatcher calls the canonical implementation directly | Public compilation API and explicit orbit semantics unchanged |
| Palindrome reflection proof | One `Mirror_Pair_Step.palindrome_nth_reflect` | Publisher and growth proofs reuse the same assumptions/conclusion; no new import edge |
| Finite event-clock claims | Names and scope corrected | `reassociation_preserves_clock_transfer` and `event_clock_s_arithmetic_exponents` do not claim CLI refinement |
| Higher temporal/provider contracts | Retained, with narrower ownership descriptions | Still used by tests/proof oracles; a generic executor or point observer does not supply the missing reverse D4+ constructor |

The central Isabelle parser inventories 19 sessions and 106 theories. Its
remaining exact-statement duplicate is a named one-line Collatz corollary, not
a second independent proof. A theory's leaf position alone did not justify
deletion. No tests, release assertions, public term APIs or resource limits
were removed or weakened.

The F5 audit found one canonical `radix64_phi5` definition. Directional
observers and delegated centered/spatial transports have distinct roles and
were retained. The higher temporal provider's sole binding validator fixes
its producer action and checks the exact compiled source/output. No admitted
collision was reproduced in 20 singleton and 400 pair probes; this finite
check is not a proof of successor right-congruence.

Evidence is local under `results/current/adversarial-ownership-cleanup/`
(`scope.json`, guarded logs and JUnit reports); the central-parser inventory
is under `results/current/proof-hygiene-audit/inventory.json`. Authored-source
fingerprint: `6e61aa4d41d992d540316ea1bb6f5a58494b257abc766df6368a2994b66661d0`.

The combined reverse/étale proof invocation exceeded the unchanged 35-second
limit after rebuilding `Reverse_Residuals` in 25 seconds. The separately
guarded `Etale_Primary_Carry` build passed in 18.72 seconds. This is focused
proof evidence, not an all-session acceptance result. Missing complete reverse
construction, classification and source-global safety obligations remain open.

The first wheel check rejected a real stale build product: setuptools had
repackaged the deleted provider from ignored `build/`. After confirming that
`build/` contained no tracked files, that generated tree was removed and the
wheel rebuilt. Raw failure evidence remains in `installed-wheel.log`; the
source/package equality check was retained unchanged.

### Collatz validation-owner migration

The fresh cutover run disproved an audit inference from historical output:
`direct_powered_point_queries` is now correctly one. The three live failures
were retired tile/radix-4 counters and schema 6 expected from a schema 7 probe.
The migration is limited to `test_collatz_block_power.py` and its existing
`collatz_temporal_power_probe.py`; no production executor changed.

| Previous assertion | Current acceptance | Preserved requirement |
| --- | --- | --- |
| Positive bounded-local-interface applications at N256 | Positive admitted source-image, postorder, primitive and bounded-base work | Exact digit and width, no temporal leaf execution, direct demand and <25,000 measured operations |
| Exactly one radix-4 source morphism at N64 | Positive dyadic action, image and projection publication | Exact digit, old radix-4 codec poisoned, no scalar generation |
| Schema-6/tile-counter report | Schema-7 source-image report with required instrumentation | Original horizons and numerical doubling envelopes; audited entries and nodes, separate operation/operand-bit/seal-byte measurements |

The finite 16/32 workload passes its measured envelope while the report stays
RED for the unresolved global source-construction bound. The independent
positive `cutover_complete == 1` tests were not changed to expected failure or
expected refusal. A new poison regression removes mandatory instrumentation
and requires rejection; missing measurements cannot be treated as zero work.
The old source-image-unconnected provider contracts remain explicitly scoped
as tested primitives, not evidence that the reverse CLI cutover is complete.

Final authored-source fingerprint after this validation-owner migration:
`7562db08d01b1abd53d7c91007aa457daf7e5b023c99f37ae1a46e174a6bd2a3`.
The initial 6,484-pass/42-failure run belongs to the preceding cleanup
fingerprint above; final reports use the `frozen-` evidence prefix.

Final validation on the final fingerprint:

| Check | Result | Evidence and limit |
| --- | --- | --- |
| Full unit selection | 6,485 PASS / same 42 FAIL | `frozen-unit`; 202.00 s / 813,220,968 sampled bytes, within 300 s / 1 GiB; no new failed node IDs |
| Migrated Collatz checks | 7 PASS | `frozen-collatz`; includes missing-instrumentation poison |
| Expanded reverse/family/Collatz cutover | 14 FAIL / 13 PASS | `frozen-cutover`; three obsolete Collatz tests migrated, every reverse assertion retained |
| Separate positive Collatz cutover | 5 FAIL | `frozen-positive-cutover`; original tests remain active and unchanged |
| Strict mypy, Ruff, format, policy, docs, proof inventory | PASS | `frozen-quality-v3`; 1,474 files, 19 sessions / 106 theories |
| Focused Isabelle | PASS | `Reverse_Residuals` and separate `Etale_Primary_Carry`; no skipped proofs or new axioms |
| All registered Isabelle sessions | TIMEOUT | `frozen-proofs-all`; 35.07 s / 733,745,472 sampled bytes under 35 s / 4 GiB |
| Clean installed wheel | PASS | `frozen-installed-wheel`; source/package equality and 15 CLI contracts |

The full unchanged Collatz probe (`frozen-collatz-probe`) reports RED with
`source_image_work_exceeds_doubling_envelope` and
`source_global_powered_construction_bound_unproved`. Its source-image operation
counts at N=16/32/64/128/256 are 326/368/434/1,165/1,719. In particular,
1,165 exceeds the preserved `2*434+64` envelope. The smaller 16/32 test's
finite PASS is not the full probe's result. Operand-bit and seal-byte volumes
are separate columns rather than being counted as operation counts.

This audit removes confirmed unused code and duplicate ownership. It does not
close the reverse temporal constructor, F4 terminal resolution, the broader
performance gates or aggregate proof acceptance. Remaining tested provider
primitives have explicit conditional scope; their presence is not a production
cutover certificate.

## Temporal macrocell streaming and schema 8

Objective: integrate the September 23 patches without mistaking an undemanded
symbolic descriptor or zero scheduler-primitive calls for a completed jump.

- Pinned the reverse candidate patch as
  `e0d3b40fdbd173b0022672313537c5811ff17eb8e2709606c48e541a6dbecd55`
  and Collatz patch as
  `760bebe8228656e2eca54a2420ea5bc83834fac337c21772b607ad9602938529`.
  Local `results/current/temporal-macrocell-cutover/patch-inventory.json`
  inventories every patch target and whether it exists in the current tree.
- Added branch-aware range streaming to the existing recursive output arena.
  Linked frames are ledger-charged, isolated between interleaved iterators,
  and released on exhaustion, close, invalid range, evaluator error or
  allocation refusal. Child bounds use the original pair of boundary values.
- Independent review found a cropped-range bypass: an undemanded sibling could
  contain a temporal reference. Publication now derives spatial completion from
  both children, and the retained payload audit verifies that metadata.
- Added schema-8 compact CLI diagnostics from one snapshot. Semantic actions,
  occurrence applications and projections have separate counters. Unmeasured
  fields remain `null`. Detailed Python ledger metrics remain available for
  probes, without changing term/query interfaces.
- Full Antihydra semantic audit was unsuitable for ordinary metrics: it repeats
  an endpoint demand. CLI metrics now use the shared read-only collector with
  `audit_complete=false`. Poison tests verify no endpoint/roof discovery for
  metrics-only queries and no extra endpoint demand with ledger information.

The checked spatial theorem covers cropping and sibling-boundary transport,
not the temporal constructor or the iterative runtime's cost bound. The
reverse candidate still ignores returned provider images and recompiles the
complete action from the original source. Collatz's proposed direct-composite
loop still discovers at most 64 physical residues per chunk. Neither path was
imported as a complete powered constructor or enabled for CLI cutover.

A D2 authority regression verifies that a step-count payload cannot authorize
the D4 right half, including a foreign source owner. This is a negative
integrity test; all positive D4/D8 and release assertions remain active.
No once-per-source 0/D4/D8 admission rule, arbitrary-jump bound or complete
recursive temporal normalizer was established in this wave.

Validation evidence and exact final fingerprint are recorded below after the
frozen checks. The raw local evidence directory is
`results/current/temporal-macrocell-cutover/`; its paths are not portable links.

Final source fingerprint:
`62b9fe536c15c4d4fc1f19a89a526a5f1cbd9dde38e09bd6e90010b09cebb854`.

| Check | Result | Evidence and scope |
| --- | --- | --- |
| Full default unit selection | 6,511 PASS / same 42 FAIL | `final-unit`, 223.33 s / 795,903,128 sampled bytes under 300 s / 1 GiB; exact failed-node comparison has no additions or removals |
| Explicit broader P0 selection | 13 PASS / 50 FAIL | `final-p0`, seven selected reverse/family/shadow/Antihydra/reporting modules; no skipped cases; this is broader than the preceding 27-case cutover selection |
| Strict mypy, Ruff, format, policy, docs and proof inventory | PASS | `final-quality`; 1,477 checked source files, 19 sessions / 106 theories |
| Clean installed wheel | PASS | `final-installed-wheel`, 15 CLI contracts plus installed ownership and Mahler checks; package contents match the source |
| Spatial range proof | PASS | `proofs-spatial-v6`; cropped completed branch semantics and output count only |
| Repository Isabelle aggregate | PASS | `proofs-repository`, all repository sessions selected with `-D`, 53.73 s / 745,738,560 sampled bytes under 60 s / 4 GiB; final frozen check in `final-proofs` |
| Collatz current-owner probe | RED | `final-collatz-probe`: work envelope and global source-construction bound still fail; current schema counts at 16/32/64/128/256 are 336/378/444/1,195/1,771 (including newly visible request events) |
| Full 16–1024 five-trial growth manifest | Not rerun in this wave | No new temporal constructor was produced; prior failures remain release holds, not zero measurements |

The first full run exposed seven additional instrumentation regressions. Invalid
Collatz coordinates had incremented a counter before type validation; validation
now precedes that increment. Exact warm-counter assertions gained only the new
query/request fields. Foreign-radix tests now capture width before taking their
immutable snapshot, retaining exact equality after a rejected foreign lookup.
A second full run confirms the original 42 failing node IDs and no new failures.

Independent review also required unknown Antihydra accounting deltas to remain
`null`; incomplete audit status cannot turn an unavailable comparison into zero.
The aggregate command audit found that `-d ... -a` had selected unrelated bundled
Isabelle sessions. Its timeout is retained as `proofs-all`, but the corrected
repository acceptance command selects all project sessions and their dependencies
with `-D`, under the same declared limit.

`scope.json`, `independent-review.json`, `failure-comparison.json` and
`validation.json` retain the detailed disposition. No temporal cutover, eight-step
bootstrap theorem, generic cold-discovery bound or source-global safety result
is claimed. The replacement reverse CLI route remains disabled.


## CLI selector and reporting audit

- **Objective:** align common information columns and eliminate execution caused
  only by reporting. Three agents audited selectors, resource extraction and
  cross-family output independently.
- **Changes:** common CLI packets now carry `family`, `kind`, `index`,
  `index_unit` and `status`. Selector units distinguish Collatz physical ticks
  from accelerated events and Antihydra post-startup return coordinates.
  Collatz event queries reject unused radix/output controls; family help and
  listing expose selector-specific choices. An unresolved special-number factor
  request now retains UNKNOWN and exit 3.
- **Reporting:** reverse/add, Collatz and Antihydra share the scalar-ledger
  schema-eight snapshot. CLI reporting never runs semantic payload audits or
  inventory callbacks. Observer packets omit unsolicited work-counter copies;
  direct Python APIs preserve their detailed default reports. Extraction counts
  are separate from computational counters; dictionary conversion and JSON
  serialization are not claimed as measured execution work.
- **Validation work:** Antihydra authority checks stream retained segments,
  rejecting the first mismatch without allocating a second complete tuple.
  Reconstruction counts and operand-bit work are exposed. Repeated validation
  across separate public trust boundaries remains required; this change does
  not introduce an unauthenticated shortcut or establish constant-time sealing.
- **Assertion mapping:** CLI raw work maps move to explicit `--info metrics`.
  Physical clock publication and Antihydra return/Mahler assertions remain.
  Installed event safety keeps its exact output checks and inspects the actual
  published production support for discovery accounting. Detailed Python audit
  inventory checks remain separate from the poisoned CLI audit path.
- **Scope:** no mathematical indices, recurrence, constructor, proof assumption,
  or positive reverse/add release assertion changed. Event metrics remain
  unsupported by the existing selector contract and are identified as such in
  help. No new temporal cutover or performance-bound claim follows.

Local evidence: `results/current/cli-schema-audit/`. The final validation record
and fingerprint are in `validation.json` and `source-fingerprint.txt`; raw logs
are local evidence, not portable download links. Prior failing constructor tests
remain active. Isabelle theory sources were not edited in this audit.

Validation on `c471e9e126d7787536f97f3d2be8700897abe16328159dca134127458d447ccf`: full units **6,536 PASS / same 42 FAIL**,
1,893 validation deselections; zero added or removed failure node IDs.
The full run took 221.16 s and 795,214,976 sampled bytes under 300 s / 1 GiB.
Installed-wheel inventory, CLI and source-owner checks passed in 5.18 s.
Quality, documentation and proof-index checks passed; Isabelle builds were not
rerun because this audit did not edit theorem sources. The first wheel command
lacked a local setuptools backend; isolated wheel building succeeded without
changing repository dependencies.

## A367620 integration

Objective: add the one-based comma-child family through the existing scheduler,
with exact output conditional on independently checked finite-region evidence.

- Added fixed-source parsing, budgets and exact public demands. `clock`,
  `tropical`, `certificate` and schema-eight metrics share the query owner.
  Metrics-only queries do not initiate certificate or arithmetic computation.
- Guarded phase-cycle actions use shared `PrefixSafety` and authenticated
  scheduler images. Mixed actions retain chronological children. The audit
  fixed dropped children, zero-limit defaulting, float admission, interrupted
  publication, missing certificate-version bindings and work-accounting gaps.
- Production now admits indices **1 through 412987860**, including the first
  fork's forced lower child. Later indices return exit 3 with a null JSON value
  and a structured boundary error. Pruning evidence is checked at runtime;
  `isabelle_instance_checked` remains false.
- The packaged certificate exhausts the 49 roots other than 20 and the first
  fork's right child. It contains 84,764 sector records and 505,013 bounded
  boundary classifications, with every outgoing alternative present. The raw
  canonical JSONL is 38,171,326 bytes; gzip is 813,641 bytes. Verification
  streams the artifact and retains only bounded BFS frontiers. The production
  checker imports no generator or OEIS choice fixture.
- The first right branch contributes 405 records and 2,466 boundary checks.
  Its exhaustion forces the first A399179 choice 0. The remaining 29 published
  choices are not yet production certificates.
- All 20,000 published terms agree with an independent literal reference.
  Guarded constructions and a separate full literal C enumerator put the first
  fork at one-based index **412987859**, value **19999999918**, with children
  **19999999999** and **20000000000**. The paper/OEIS label 412987860 differs.
  Thus the last admitted value, at 412987860, is **19999999999**.
- The focused Isabelle session checks root coverage, guarded fixed-phase
  literal paths, compressed-region soundness and the finite-right branch
  implication. It does not yet refine the full Python parser/checker or check
  the concrete artifact instance. Scheduler cost and complete prefix theorems
  remain formal release obligations.

Regenerate the immutable certificate with:

```sh
python -m devtools.experiments.comma.closed_region_certificate /tmp/comma-prefix.jsonl.gz --verify
```

SHA256: `f6e864b26ca9c8164ed91594d995aca15b19e027166d469844be37268896e4eb`.
The only process-cache payload is an authenticated verification marker, bound
by source, decimal semantics, artifact hash, version and reset generation.
A bypassed query uses its own ledger-owned marker after verifying once.
Repeated demands still read/hash the compressed asset; those bytes are charged.

Certificate work counts bounded nine-candidate classifications and record
operations; candidate trials are also reported separately. This is an explicit
operation unit, not an instruction count. Arithmetic transfer construction,
operand widths, attempted image evaluation and successfully published
transitions have separate counters. No missing instrumentation is recorded as
zero.

The first public cold run of index 412987860, including clock and certificate
output, completed in 5.65 seconds / 22,561,296 sampled bytes under 35 seconds /
1 GiB. This establishes a working bounded prefix query, not global periodic
quotient closure or a complete asymptotic proof.

Local evidence is under `results/current/a367620-integration/`; raw evidence
stays ignored. Earlier `proof-v*`, arithmetic-only and blocked-prefix runs retain
their original scopes. Current-source validation is recorded below after the
freeze. Mathematical definitions belong in the
[comma synthesis](../../../docs/research/comma.md).


Frozen integration source:
`4188758779ab96d115dbe4430a830030cebf85a9e666bc2b5521ab72fe288845`.
Independent read-only review by `comma_arithmetic` covers runtime pruning,
source/cache authority and the final arithmetic-only benchmark boundary fix.
It explicitly excludes the unfinished concrete Isabelle instance.

The certified API growth probe has **115 passing samples**: five trials for
cold and cache-bypassed requests at each horizon 16–1024, and five warm trials
at those horizons plus 20,000 and 412987860. Every report pins the same source.
These run in a warm interpreter; fresh installed CLI checks are separate.

| Mode | Scope | Median total | Included certificate cost |
| --- | --- | --- | --- |
| Cold | each 16–1024 horizon | 4.95–5.03 s | 4.91–5.01 s, complete verification |
| Cache bypass | each 16–1024 horizon | 4.90–4.97 s | 4.88–4.95 s, complete verification |
| Repeated owner | 16–412987860 | 0.408–0.444 ms | 0.397–0.430 ms, charged hash/admission |

Five-trial probe processes each remained below 35 seconds / 1 GiB. Arithmetic
construction medians ranged from roughly 7 to 43 ms over 16–1024. Observer and
render timings are recorded separately. Warm reuse does not establish cold
construction complexity. Certificate work is deliberately included; it is not
reported as free setup. The arithmetic-only benchmark ends at index 412987859,
whereas runtime-certified queries include its checked child at 412987860.


| Frozen validation | Result | Local evidence stem |
| --- | --- | --- |
| Comma/API/metrics unfiltered focused selection | 175 PASS | `enabled-focused-final` |
| Full units | 6,696 PASS / same 42 FAIL; 1,897 validation deselections | `enabled-unit-final`; 220.30 s / 799,081,576 sampled bytes |
| Existing explicit P0 selection | 13 PASS / same 50 FAIL | `enabled-p0`; exact baseline failure IDs compared |
| Strict mypy, Ruff, formatting, repository policy | PASS; 1,494 typed/formatted source files | `enabled-mypy-final`, `enabled-ruff`, `enabled-format-final`, `enabled-repository_policy` |
| Documentation and proof index | PASS | `enabled-docs_index`, `enabled-isabelle_proof_index` |
| Clean wheel and installed public CLI | PASS | `enabled-wheel-build-final`, `enabled-installed-final`; installed check 11.13 s |
| All registered Isabelle sessions | PASS | `enabled-isabelle-final`; 11.96 s / 1,708,854,536 sampled bytes |
| Certified cold/warm/bypassed growth queries | 115 samples PASS | `enabled-growth-*`, `enabled-growth-summary.json` |

No new unit or P0 failure IDs were introduced. Existing reverse/add,
special-number and other release obligations remain active. Successful
Isabelle builds certify the registered statements, not the missing concrete
certificate instance or full production refinement.

Two validation-invocation errors were corrected without repository exceptions:
`mypy .` included generated `build/lib` duplicates, so final strict checking used
all authored `src tests devtools`; non-isolated wheel building lacked a local
setuptools backend, so the final build used standard isolated build dependency
installation. The benchmark boundary edit was formatted before the final
fingerprint and full-suite run. Failed/intermediate logs remain local evidence.
