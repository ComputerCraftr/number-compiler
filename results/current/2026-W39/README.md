# 2026-W39 implementation and validation record

Period: 2026-09-21 through 2026-09-27. Updated through September 23.
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

### Shifted parity germs and batched limbs

Record period: 2026-09-23. This increment implements the supplied-germ
arithmetic and repairs production point-demand costs and cache validation.
It does not replace the balanced source constructor.

<details>
<summary>Germ semantics, production fixes, validation and remaining constructor</summary>

**Input.** The attachment `df0e7f24-5e0c-4b35-a8e9-0862f17a063a/Pasted text.txt`
has SHA-256 `c2675360712a03b3eadfd4226eb07a8f066dfdaa61a6230bb94e43f3d8ef031d` and
describes the normalized Collatz parity conjugacy and two-phase physical
suspension. Its cursor is a supplied shifted parity word. The report explicitly
separates cursor construction from finite-residue observation.

**Implemented.** The shared odd-gain inverse in `arithmetic/fields/two_adic.py`
covers normalized Collatz, total Antihydra arithmetic and the centered Mahler
source with distinct branch laws. It decodes a bounded byte stream once,
avoiding a full integer shift for each supplied symbol. The Collatz germ
helper validates cursor fields at use, masks before shifting, handles width
zero and the pending odd phase, and records demanded precision/inverse work.
It grants no source authority and supplies no physical exterior predicate.

Power-of-two public Collatz limb queries now make one guarded modular
projection instead of up to 63 binary projections. Their cache binds radix,
position, source owner and action program. Warm hits validate the live source,
action and image record plus the root's source/action/extent binding. The
original root handles are pinned, so even a coherent alternate source/image
in the same workspace cannot authorize a cached value. The width bound is
pinned to the original source extent, calculated and charged once. Point
queries no longer recompute `seed + 2`, which copied the complete input integer
on every demand.

**Independent review.** Review found alternate-root-image and coherent-root
replacement holes, repeated width-bound allocation and mutable bound metadata.
After the repairs, read-only review found no residual concrete defect in those
changes. Regressions retain disposed, forged and
changed-source rejection, distinguish partial limbs from blank, poison
per-bit limb expansion and compare independent literal physical trajectories.

**Exact scope.** At phase zero a bit at position `p` requires `p+1` Q symbols.
At pending phase one the low bit is zero and higher bits use the shifted tail.
Sources 1 and 33 demonstrate that equal low germs do not decide blank versus
active zero. Antihydra uses gains `(3,3)` and offsets `(0,-1)`, while centered
Mahler uses `(3,3)` and `(0,1)`; neither inherits Collatz's popcount inverse or
its physical two-tick suspension unchanged.

**Remaining obligation.** The CLI still constructs the complete admitted
balanced source image. No authenticated producer of the shifted Q cursor and
exterior guard with a better construction bound has been supplied. Generating
that cursor through scalar parity replay is explicitly excluded. The modular
inverse loop and its source-word equations are now checked; cursor admission,
output activity, runtime refinement and safety transport
remain separate proof obligations; finite germ inversion alone proves no global
Collatz, Mahler or Antihydra safety claim.

Frozen authored source:
`fb6ece37a8b85b55f34514249233f688bcdf2fdd3750fb1c7acbf26fc0b6f98a`.
Local evidence lives under `results/current/parity-germ-projection/`; these are
local evidence stems, not portable downloads. The proof-to-runtime mapping
lists explicit modular-unit assumptions and unverified Python operations.
No new axioms, skipped proofs or theorem oracles were introduced.

The 105 samples cover horizons 16–1024, five trials and limb widths 4/32/63.
Each row creates fresh terms with process reuse bypassed, compares independent
literal output, and records construction separately from cold/warm projection.
Median whole-limb projection versus binary assembly was 46.50/121.46 µs,
47.42/736.75 µs and 48.62/1426.71 µs respectively. This establishes one radix
projection instead of 4/32/63 point projections on those demands. It is not an
end-to-end CLI timing or a constructor-complexity improvement. Warm projections
perform zero additional modular operand work but still validate authority.

Reproduce the projection measurement:

```console
python -m devtools.benchmarks.collatz_temporal_power_probe --limb-projection --indices 16 32 64 128 256 512 1024 --trials 5 --limb-widths 4 32 63
```

| Validation on frozen source | Result | Local evidence |
| --- | --- | --- |
| Focused parity, limbs, authority, resource and shared-image regressions | 134 PASS | `focused-frozen` |
| Strict mypy, Ruff, formatting, policy, docs and proof inventory | PASS; 1,503 Python files; 21 sessions / 118 theories | `quality-final.json`, `proof-index-final.json` |
| Affected Isabelle session | PASS, 22.38 s / 1,272,483,680 sampled bytes | `proofs-v32` |
| All registered Isabelle sessions | Checked after two 60-second timeouts and a 15.14-second incremental completion; aggregate rebuild deadline remains failed | `isabelle-all-final`, `isabelle-all-resume`, `isabelle-all-resume2` |
| Fresh wheel and installed CLI | PASS; 15 fresh-process contract cases plus limb-path poison smoke | `wheel-build-final`, `installed-final`; 11.46 s / 117,966,912 sampled bytes |
| Projection measurements | All 105 samples complete; exact literal agreement; construction separately reported | `limb-probe-final.json`, `limb-summary-final.json` |
| Full unit selection | 6,776 PASS / same 42 FAIL; 17 added tests, no removed tests or changed failing IDs | `unit-final`, `unit-comparison.json`; 219.53 s / 810,206,312 sampled bytes under 300 s / 1 GiB |
| Explicit P0 selection | Same 13 PASS / 50 FAIL; identical selection and failing IDs | `p0-final`, `p0-comparison.json` |
| Independent review | Accepted for finite arithmetic, projections and cache-binding scope | `independent-review.json` |

Limits and positive release assertions are unchanged. No release hold closes
from these projection timings. The exact source-to-cursor/exterior constructor,
existing reverse/add and special-number obligations, full Python refinement
and global safety remain open. Interim failed proof attempts remain local and
are not release evidence.

</details>

### Powered boundary germ audit

Record period: 2026-09-23. This is a new finite audit and proof increment,
not a production cutover or a minimality certificate.

<details>
<summary>Candidate, exact counterexamples, measured work and proof scope</summary>

**Input provenance.** The supplied
`/Users/john/Downloads/196_temporal_boundary_frobenius_candidate.md` has SHA-256
`17751bcf4045ee8a77c8b334559fe5ea3a35da435b12e28e2392ac8281c36cfc`.
It supplies a candidate and finite doubled-clock evidence, not an executable
complete-transformer patch or a universal closure proof.

**Reverse/add findings.** The new `temporal_boundary_germ` experiment preserves
coupled Q95 cells, distinct absent-cell markers, reflected coordinate order
and exclusively LSD-to-MSD physical carry. All 95 cells and both incoming
carries are checked. Default seed-196 runs through index 256 give:

| Half horizon | Checked occurrences | Repeated keys | Singleton keys | Differing doubled germs | Differing doubled clocks |
| --- | --- | --- | --- | --- | --- |
| D4 | 249 | 1 | 247 | 1 | 0 |
| D8 | 241 | 2 | 237 | 2 | 0 |
| D16 | 225 | 0 | 225 | 0 | 0 |
| D32 | 193 | 0 | 193 | 0 | 0 |
| D64 | 129 | 0 | 129 | 0 | 0 |

D4 starts 77 and 86 have identical key
`(q mod 4=2, r=2, (21,25,26), (21,25,26))`. Their doubled clocks both equal
`(1,3)`, but their doubled low germs are `(82,94,41)` and `(82,94,34)`.
Independent literal reverse/add verifies the source terms used by the witness.
This refutes a standalone key-to-next-germ table. It does **not** refute an
action applied to distinct recursive source occurrences. Consequently neither
erasing `pair_steps` nor introducing a finite transition table is authorized
by these data. D16 and larger zero-conflict rows have no repeated-key evidence.

**Dyadic findings.** The `powered_boundary_germs` experiment applies the actual
production balanced constructor at D2, D4, D8, D16, D32 and D64, including
non-root, random and high-fiber occurrences. It checks full transfer
composition, branch concatenation, odd counts, delta and minimum prefixes.
At D16 the Collatz sample has 384 occurrences and 299 complete retained-effect
classes; Antihydra has 377 and 329 respectively. Each has 68 conflicts when
only counts, minimum and three branch bits at each edge predict the scalar
effect. For example, Collatz sources 983252 and 15912724 share that edge key
but have offsets 19744 and 18208; Antihydra sources 49 and 8141841 have offsets
-37172081 and -37128017. These are insufficient-observer witnesses, not a
counterexample to the complete source-bound cylinder.

The tested dyadic edge key is deliberately a separate candidate; it is not
the decimal Q95 germ or a transported F5/F2 rule. In production, exact residue
is a source-cylinder binding, skew is the output function, and counts and
minimum prefixes are derived consumer summaries. Retained branch support
serves demanded chronology. This audit gives no reason to conflate those
roles or discard authority fields. F5/F2 and harmonic projection equality
has not been promoted to a successor identity.

The Mahler test obtains its action from the admitted Antihydra image and
compares it to an independent literal source-8/Fraction fold. It preserves the
distinction between Mahler margin positivity and Antihydra ledger safety.

**Rejected optimization.** Physical Collatz admits redundant source bits:
an odd `3*x+1` step does not consume precision. However, a leaf-only sample of
128 random sources and 2,048 D64 leaf requests found zero exact repeats and
zero additional verified reduced-domain aliases. An unindexed search would
add 15,360 comparisons. The sample does not model parent publications or FIFO
eviction. Production memo keys, budgets and source authorities remain unchanged;
the experiment does not prove that every possible memo improvement is useless.

**Checked proofs.** `Reverse_Boundary_Germ_Local` checks local Q95, blank,
equality, reflection and symbol-complement laws plus a conditional successor
factorization criterion. Its total mathematical edge extractor includes the
empty list; the Python observer admits only nonempty words. The standalone
pair-field witness is not claimed to be a temporal source constructor.
`Collatz_Reduced_Precision` proves the upward high-fiber identity at
`p=min(n,even_count+1)` for the actual physical law, including complete effect
and safety fields. Arbitrary congruent-peer tests are finite evidence beyond
that theorem's upward-lift statement. Neither proof claims runtime memo
canonicalization, arbitrary-horizon compression, or global safety.

Reproduction commands:

```console
python -m devtools.experiments.reverse_add.temporal_boundary_germ
python -m devtools.experiments.collatz.powered_boundary_germs
python -m pytest -q -o addopts='' tests/validation/proofs/reverse_add/test_temporal_boundary_germ.py tests/hashlife/execution/test_powered_boundary_germs.py
isabelle build -d devtools/proofs/isabelle -j 1 -o threads=1 -o parallel_proofs=0 Reverse_Residuals Balanced_Dyadic_Integration
```

Raw evidence remains local under `results/current/powered-boundary-germs/`;
it is not a portable download. Frozen authored-source fingerprint:
`d6cfd866933125aee9ec6f2226e0ea9289843dd2483dc8ca74dd10337d937b90`.
Independent peer findings and their disposition are in `independent-review.json`.

| Validation | Result | Evidence and scope |
| --- | --- | --- |
| Focused new/dependent checks | 111 PASS | `focused.xml`; all 14 new tests plus retained local/dyadic/Mahler coverage |
| Default units | 6,759 PASS / same 42 FAIL | `unit.xml`, `unit-comparison.json`; seven new ordinary tests, zero removed tests, identical failing IDs; 214.753 s / 830,653,544 sampled bytes under 300 s / 1 GiB |
| Explicit P0 selection | Same 13 PASS / 50 FAIL | `p0.xml`, `p0-comparison.json`; identical 63-case selection and failing IDs |
| Strict quality | PASS | `quality-final.json`; mypy/Ruff/format cover 1,503 Python files; policy, docs and 21-session/116-theory inventory pass |
| New local Isabelle theory | PASS | `isabelle-local-v2`; registered `Reverse_Residuals`, 27.082 s / 1,269,222,736 sampled bytes |
| New dyadic precision theory | PASS | `isabelle-dyadic-v2`; registered `Balanced_Dyadic_Integration`, 17.656 s / 1,229,180,744 sampled bytes |
| Bounded experiments | PASS | `reverse-audit-final.json`, `dyadic-audit-final.jsonl`; 0.543 s and 2.023 s under separate 35 s / 1 GiB guards |

Failed initial proof attempts remain in the local evidence; the repaired
theories pass without skipped proofs or new axioms/oracles. Final registered
session recheck is `isabelle-final`. The 60 s / 4 GiB guard is unchanged.
No production Python changed in this increment, so new wheel, aggregate
Isabelle and five-trial growth claims are not made. Existing positive release
assertions remain active and the release remains blocked.

</details>

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


## Balanced dyadic temporal cutover

Objective: apply the downloaded Collatz temporal/performance patches to the
shared production constructor and transfer the applicable balanced composition
to Antihydra/Mahler while preserving their distinct retained consumers.

| Input | SHA256 / scope |
| --- | --- |
| Baseline commit | `fda53bddbc2167c651fe7f88059e0d6cfc1193ed` |
| `collatz_generic_temporal_cutover_fix.patch` | `760bebe8228656e2eca54a2420ea5bc83834fac337c21772b607ad9602938529` |
| `collatz_digit_temporal_performance_fix.patch` | `2856a962c6ab4cd880e1e9325677afab7c4c042db05a0d59786edca879bee1ed` |

Downloaded reports are research inputs, not evidence for the live tree.
The performance delta targets the generic patch's left-deep affine accumulation.
An independent baseline checkout at `fda53bd` already showed roughly doubling
aggregate charged operand-bit work at random-source horizons 128–1024:
25,885 / 55,875 / 110,496 / 237,868. It is therefore incorrect to label that
live baseline's measured total work quadratic. Its retained ledger nodes were
620 / 1,370 / 2,868 / 5,862; source authority and support remain separately
accounted from semantic action interning.

Implementation and adversarial scope:

- The existing scheduler owns direct composed application to an admitted
  recursive source. The shared constructor uses balanced low-residue transport.
- Collatz digit-only requests avoid compatibility power compilation and publish
  a saturated root. Explicit support demands preserve branch semantics.
- Antihydra retains chronological support for guarded TM and first-failure
  consumers. Mahler reuses its source image; neither the Collatz recurrence nor
  its nonnegative safety weights are substituted for Antihydra's law.
- Audit found the supplied saturation patch replayed whole trajectories during
  full Python payload/metrics audits and broke branch observers. These were
  implementation defects, not evidence that a new semantic variable is needed.
  The current CLI metrics collector was already read-only; full audits are a
  separate measured and charged operation.
- The supplied normalized parity-bijection argument does not apply verbatim to
  physical indexing. Tests already distinguish normalized words from physical
  no-`11` words. No finite F5 exact-endpoint closure is inferred here.
- Existing Isabelle source transport, low-residue lift, affine composition,
  cycle and minimum-prefix lemmas are reused as semantic specifications. Full
  executable constructor and asymptotic cost refinement remains a separate
  obligation; no duplicate selector-only theorem was added as a substitute.

Frozen authored source: `91edc25e7d990807835db367d20ca58801712d76faf04f5070686aa33c278d5e`.
Local raw evidence stays under `results/current/collatz-balanced-cutover/`;
these are local evidence stems, not portable downloads.

The shared constructor's exact memo is local to one pinned law and retention
mode, keyed by `(span, residue)`, bounded to 64 entries and ledger-charged.
It is released before publication. Lookup/hash operand sizes, publications,
hits and eviction are separate from semantic-action interning. Independent
review checked source authority, cycle phases, changed demands, shared support
IDs and failed-publication cleanup on this fingerprint.

The installed positive reuse gate checks source `2^4096` at physical index
1,024: exact value `2^3072`, positive memo hits, at least 960 reused steps,
at most 64 classified steps and zero scheduler primitive applications. Four
hits were measured. Retained-support mode further reduces classifications to
four via the existing bounded leaf algebra. This is exact low-cylinder reuse,
not a claimed F5 merge of unequal future continuations.

Assertion-to-replacement mapping:

| Previous private contract | Retained production assertion |
| --- | --- |
| A chronological second-child source must exist | Direct publication has no second-child source; altered root residue, foreign source and stale image handles are rejected |
| Tile/field parent counters establish Collatz execution | Source-image publication, action work and exact-cycle compression establish the active owner; exact outputs and resource ceilings remain |
| Radix conversion builds an old power program/tile observation | Scoped source-image atom owns binary and radix-3 queries; compatibility power and tile observation remain absent |
| Installed reuse invokes `transport_reuse` | Public CLI meets the exact reuse/classification bound above through the balanced memo |
| Full metrics validate the live endpoint by demanding it again | Independent sealed-fiber validation charges audit work without endpoint or aggregate demands |

Positive `bounded_temporal_runtime_cutover_complete` assertions, reverse/add
construction assertions and special-number resolution assertions remain active.
No skips or expected failures were introduced.

Five-trial median construction **plus exact endpoint demand**, in a warm
interpreter with API/process caches bypassed (milliseconds):

| Collatz seeded random source bits / physical steps | Baseline `fda53bd` | Current | Baseline retained ledger nodes | Current nodes |
| --- | ---: | ---: | ---: | ---: |
| 128 / 128 | 2.541 | 1.122 | 620 | 246 |
| 1,024 / 1,024 | 22.965 | 2.733 | 5,862 | 252 |
| 8,192 / 8,192 | 199.181 | 17.846 | 47,756 | 258 |

The deterministic random and repeating-bit inputs use the same benchmark
harness against both trees. At 8,192 the repeating-bit case measured 1.282 ms
and 12 exact memo hits. Explicit decimal conversion and full payload audit
are timed separately. Cumulative operand counters now include newly charged
memo hashing and independent audit work; raw totals are not a like-for-like
work-saving comparison against the baseline's narrower instrumentation.

All 210 five-trial growth samples completed over 16–1,024, with separate
cold, repeated and cache-bypassed modes for Collatz and Antihydra. Antihydra
samples also request Mahler from the same support. Another 70 current-tree
queries cover random/repeating Collatz inputs through 8,192; the same 70
baseline queries completed. Every endpoint is checked against a bounded
independent recurrence. These finite measurements do not prove an arbitrary
source construction bound or Python integer-multiplication complexity.

| Validation | Result | Local evidence |
| --- | --- | --- |
| Focused semantic, authority, rollback, laziness and reuse checks | 224 PASS | `focused-final` |
| Six growth modes and two larger workloads | All samples complete under 35 s / 1 GiB per probe | `growth-*`, `large-*`, `measurement-summary.json` |
| Original temporal probe | PASS; unresolved proof flags remain false | `original-probe-final` |
| Clean installed wheel | PASS; 15 fresh-process CLI cases, package inventory and traced reuse/Mahler checks | `installed-final` |
| Strict mypy, Ruff, formatting, policy, docs, proof index | PASS; 1,498 Python files, 20 sessions / 109 theories | `quality-final.json`, `quality-*` |
| Registered Isabelle aggregate | PASS, 12.18 s / 1,730,514,160 sampled bytes under 60 s / 4 GiB | `isabelle-final`; existing statements only |
| Explicit P0 selection | 13 PASS / same 50 FAIL; no new failing test IDs | `p0-final`, `p0-comparison.json` |
| Final full unit selection | 6,716 PASS / same 42 FAIL, no new failing test IDs; 232.34 s / 804,930,688 sampled bytes under 300 s / 1 GiB | `unit-final`, `unit-comparison.json` |

Reproduce the measured public query workload:

```console
python -m devtools.benchmarks.collatz_temporal_power_probe --balanced-scaling --family collatz --mode bypass --indices 128 256 512 1024 2048 4096 8192 --trials 5
python -m devtools.benchmarks.collatz_temporal_power_probe --balanced-scaling --family antihydra --mode cold --mahler --indices 16 32 64 128 256 512 1024 --trials 5
python -m pytest -q tests/hashlife/execution/test_dyadic_effect_reuse.py tests/sequences/collatz/test_temporal_patch_adversarial.py tests/sequences/collatz/test_temporal_budget_rollback.py
```

Release remains blocked by the existing constructor/proof obligations. Cold
noncycle discovery still consumes required source bits; Antihydra retains
chronological support for guarded consumers. No global Collatz convergence,
Mahler safety or Antihydra non-halting theorem is claimed.

## Balanced dyadic executable and finite safety refinement

- **Objective:** connect the balanced production constructor to an executable
  Isabelle worklist, then derive finite Collatz, Antihydra and Mahler results
  from that same arithmetic owner.
- **Changes:** added deterministic postorder execution, the actual split rule,
  bounded branch leaves, transported right-child residues, exact memo lookup,
  FIFO eviction before optional cache admission, and early completion. The
  recursive specification and work potential are proof objects, never execution
  oracles. Added 36 independent differential cases and registered the new
  downstream family session in the existing proof inventory.
- **Established results:** numerical constructor correctness for arbitrary
  finite horizons; exact high-fiber endpoints; Antihydra finite ledger guards;
  chronological support-summary descent; Mahler action equality for the actual
  source-8 centered branch fold. Its cap is nonpositive exactly at horizons
  at least two, with first failure at one-based return two. This does not imply
  Antihydra ledger failure or TM halting.
- **Rejected shortcuts:** supplied branch itineraries as source proofs,
  recursive specifications as executable constructors, unbounded memo tables,
  discarded cache entries surviving a failed reservation, and semantic-cycle
  theorems presented as verification of Python cycle admission.
- **Remaining work:** Python image/support-ID publication and allocator
  refinement, complete bit/storage construction bounds, the existing reverse
  and special-number constructors, and source-global mathematical obligations.
  The worklist's linear abstract control bound is not an integer-arithmetic or
  arbitrary-source sublinear runtime bound.

Frozen authored source:
`a28ef398fb9d4744a30d8e21a795a48918c9560c5729d95d8b144d8b8a934a81`.
Local evidence is under `results/current/balanced-proof-refinement/`; these are
local evidence stems, not portable download links. The maintained
[refinement map](../../../docs/proofs/balanced-dyadic-refinement.md) separates
checked statements, Python counterparts and unresolved publication/cost work.
The earlier timing measurements retain their own `91edc25e7d99` fingerprint;
this proof pass changes no production Python execution path.

Independent review checked the actual source/parity binding, absence of
execution oracles, memo eviction/refusal, and theorem scope. It found and
corrected an overstatement about runtime cycle admission in the mapping
document. The added eviction regression forces optional cache refusal
immediately after removing the oldest entry from a full 64-entry memo.

The pre-layout family build (`9454a8f4daee`, `families-v39`) passed in
17.001 seconds / 1,256,967,576 sampled bytes. Policy then caught the worklist
at 1,065 lines against the existing 1,000-line limit. Its unchanged split
arithmetic moved into the existing `Dyadic_Source_Lift` owner, leaving 902
worklist lines and 494 source-lift lines, without an exception or new fragment
theory. The final fingerprint above includes that move.

The affected-session rebuild hit the unchanged 60-second limit after the
shared and family theories passed (`isabelle-refreeze`). An incremental
aggregate continuation checked the remaining sessions in 27.686 seconds /
1,240,665,952 sampled bytes (`isabelle-resume`). Thus all registered sessions
are checked, but a one-invocation rebuild of all affected sessions missed the
deadline. The initial default-heap development build also exceeded 4 GiB;
subsequent checks used smaller JVM/PolyML heaps under the same guard. Failed
development logs remain local.

Reproduce the guarded aggregate with the normal Isabelle installation path:

```console
python -m devtools.checks.process_guard --timeout 60 --memory-mib 4096 --output /tmp/balanced-isabelle.log --report /tmp/balanced-isabelle-guard.json -- isabelle env 'ML_OPTIONS=--minheap 256 --maxheap 1600' 'ISABELLE_TOOL_JAVA_OPTIONS=-Djava.awt.headless=true -Xms256m -Xmx1024m -Xss16m' isabelle build -D devtools/proofs/isabelle -j 1 -o threads=1 -o parallel_proofs=0
python -m pytest -q tests/hashlife/execution/test_balanced_proof_refinement.py
```


| Validation on final fingerprint | Result | Local evidence |
| --- | --- | --- |
| Focused arithmetic, authority, memo and safety checks | 260 PASS, including 36 new differential cases | `focused-final` |
| Strict mypy, Ruff, formatting, policy, docs and proof inventory | PASS; 1,499 Python files; 21 registered sessions / 114 theories | `quality-final.json`, `quality-*`, `proof-index.json` |
| All registered Isabelle sessions | Checked after incremental continuation; affected-session one-invocation rebuild exceeded 60 s | `isabelle-refreeze`, `isabelle-resume`; limits unchanged |
| Fresh isolated wheel and CLI | PASS; 15 fresh-process cases and package/source equality | `wheel-build-isolated`, `installed-final`; 10.080 s / 116,983,848 sampled bytes |
| Explicit P0 selection | Same 13 PASS / 50 FAIL; no added or removed failing IDs | `p0-final`, `p0-comparison.json` |
| Full unit selection | 6,752 PASS / same 42 FAIL; no added or removed failing IDs | `unit-final`, `unit-comparison.json`; 214.379 s / 829,883,544 sampled bytes under 300 s / 1 GiB |
| Independent review | Accepted for numerical constructor and finite safety scope | `independent-review.json` |

No release gate was skipped or weakened. Existing reverse/add and F4 unit
failures remain active, as do the broader architectural/primality P0 failures.
The release hold also retains the affected-session rebuild deadline failure.
This work finishes the shared numerical constructor and finite-safety bridge;
it does not certify all Python objects, global non-halting, or arbitrary cold
construction complexity.

## Comma boundary quotient

The 2026-09-23 cutover work targets the boundary state
`(N/Z,a,p mod 924)`, with the actual exponent and literal-term weights retained
outside the shared phase identity. Its acceptance target is polylogarithmic
construction/selection in the term index; integer arithmetic and rendering are
reported separately. This is not a claim of linear bit complexity.

### Changes and scope

- Added symbolic boundary macros with exact affine weights, both fork children,
  landmine outcomes and indexed fragment prefixes. A partial term demand uses
  binary prefix descent and at most one bounded decimal phase.
- Added chronological weighted returns through the shared skew-transfer owner,
  with capped geometric repetition through shared binary powering. Arithmetic
  descriptors cannot authorize infinite-branch selection.
- Added a development lifting checker for every affine sector/guard predicate,
  residue-fixed floor division, complete child alternatives and weighted prefix.
  It checks the entire exponent ray, rather than testing only two exponents.
  Its Isabelle refinement remains an independent gate.
- Removed certificate file access and SHA256 work before authenticated memo/cache
  hits. Cold misses still run the existing finite-forest verifier. The auditor
  caught a reset race; shared local hits now validate a generation-bound lease.
- Rejected forged negative/nonintegral return weights, incomplete child coverage,
  altered cycle phases/guards and sample-only weight substitutions. Production
  still uses the certified prefix until lifting, the finite instance and the
  scheduler/consumer refinement are checked.
- The independent follow-up audit found and fixed zero literal progress paired
  with positive exponent transport, and stale local retention after a reset
  during publication. Failed local publication now removes its memo entry.
  Bit-work admission precedes large power allocations.
- Moved the now-checked large-sector child rule into the existing arithmetic
  owner. Production and symbolic macro construction share it; only startup
  values below 100 perform nine leading-digit checks. Independent literal tests
  cover all values 100 through 10,000, both sides of seams and candidate-search
  poisoning. This local integration does not choose infinite fork branches.
- Repeated-return selection builds capped geometric summaries and descends their
  binary levels. It handles negative affine offsets and exact endpoint equality;
  tests include a trillion repetitions with oversized powers poisoned. This is
  arithmetic support for future scheduler integration, not branch admission.

### Quotient reproduction

The symbolic checker was run over every boundary state in 16 serialized shards
of 924 states, each under 35 seconds / 1 GiB. The full finite graph has 14,470
losing states, maximum losing rank 136, and 314 surviving states on one cycle.
Every cycle state has exactly one surviving child; the accumulated exponent
gain is 924. These are executable whole-ray checks and finite enumeration,
not a kernel-checked graph certificate.

`python -m devtools.experiments.comma.boundary_quotient_audit --start 0 --stop 924`
produces the first shard; successive disjoint intervals cover all 14,784 states.
`--merge PATHS --weighted-return` rejects incomplete/duplicate state coverage
and malformed alternatives, then reconstructs and rechecks all 314 cycle macros
before composing their exact weight. The composed denominator is 721080360;
its numerator offset is 107598294880. Full coefficients and constructor counters
are retained in local JSON evidence. Checker work is explicitly excluded from
those constructor counters; wall time includes it.

The reported cycle choice prefix begins **after** the initial choice at the
first root-20 fork. Prepend that initial zero when comparing it with A399179.

### Remaining cutover obligations

1. Complete the repeated maximum-guard/floor-count result and prove the
   executable affine-ray fragment checker refines exact-length unique-child
   paths, including partial selection. The local seam, sign, displacement,
   unique-edge and period-transport ingredients are now kernel-checked.
2. Check the losing-rank and unique winning-cycle instance in Isabelle, including
   the source-20 prelude and exclusion of smaller initial values.
3. Publish those admitted weighted returns through `TileScheduler`, implement
   weighted cycle/fragment descent, and connect API/CLI admission together.
4. Validate cold/warm/bypassed production costs before removing the forest asset,
   runtime verifier and finite-prefix boundary. Existing cross-family holds stay.

Raw evidence is local under `results/current/comma-boundary-quotient/`.

The full table contains 1,965,763 fragments (maximum 1,188 per macro). This
identifies a concrete checking-cost concern; it is not a timed impossibility
result. The planned finite certificate must tie every child/gain row to the
HOL evaluator, then check losing ranks and the winning cycle. Merely importing
the Python edge table as a premise would leave the main theorem unproved.

### Frozen validation and disposition

Final authored-source fingerprint:
`af813617bfaebf9de84c91ed6782c6cf921844d5a2f3779cea1e051dbfa33d9f`.
All evidence below is local under `results/current/comma-boundary-quotient/`.
The full plan remains incomplete; this checkpoint does not enable an unbounded
comma prefix or remove the runtime forest.

| Check | Result and scope | Evidence stem |
| --- | --- | --- |
| Focused comma/API checks | 207 PASS; four explicit validation cases separately PASS | `focused-final`, `cli-validation-final` |
| Full default unit selection | 6,827 PASS / same 42 FAIL; 51 added passing tests, no removed tests or new failing IDs; 243.29 s / 812,745,856 sampled bytes under 300 s / 1 GiB | `unit-final`, `unit-comparison.json` |
| Explicit P0 selection | Same 13 PASS / 50 FAIL; identical test and failing-ID sets | `p0-final`, `p0-comparison.json` |
| Strict quality | Mypy, Ruff, formatting, repository policy, docs and proof inventory PASS; 1,511 Python files | `quality-*` |
| Isabelle | Five new local theories pass with oracle audits; focused rebuild 31.44 s / 1.21 GB. All 21 sessions / 123 theories pass the incremental aggregate in 10.74 s; existing heaps reused | `proof-v38`, `isabelle-all-final`, `proof-index-final.json` |
| Clean installed wheel | PASS; 18 fresh CLI cases include comma startup, last admitted index and first unresolved index; 21.10 s under 35 s / 1 GiB | `wheel-build-isolated`, `installed-final` |
| Entire quotient and weighted return | All 14,784 macros pass the executable whole-ray checker; counts reproduce 14,470 losing / 314 winning / rank 136 / exponent gain 924 | `final-shard-00` through `final-shard-15`, `quotient-weighted-final.json` |
| Production prefix measurements | 135 samples: five trials for nine indices in each cold/repeat/bypass mode. One initial five-trial bypass-16 probe timed out at 35.03 s; the same workload's retry passed at 26.34 s | `probe-*`, `measurement-summary.json` |
| Independent review | Literal alternatives, weighted descent, affine guards, source binding, memo generation and rollback reviewed; full quotient theorem/cutover excluded | `independent-review.json` |

The initial non-isolated wheel build lacked `setuptools.build_meta` in the
validation environment. The isolated build succeeded; no dependency or source
change was needed. Both attempts remain recorded.

The timing inputs are `16,32,64,128,256,512,1024,20000,412987860`. Reproduce each
five-trial packet with the canonical probe, wrapped in the unchanged guard:

```console
python -m devtools.checks.process_guard --timeout 35 --memory-mib 1024 --output /tmp/comma-probe.json --report /tmp/comma-guard.json -- python -m devtools.benchmarks.production_p0_probe --family a367620 --mode cold --trials 5 --indices 1024
```

Use `repeat` and `bypass` for their respective modes. The interpreter is warm;
cold mode clears shared caches, repeat retains the owner, and bypass disables
process/API reuse while retaining normal within-request memoization. Installed
fresh-process CLI measurements are separate.

## Comma executable refinement and runtime audit

**Objective:** replace forest-backed prefix admission with the complete weighted
boundary quotient. **Disposition: incomplete; no global CLI cutover or forest
deletion.** Source fingerprint for this increment:
`02e9e3612534a4dbf3881a3755c9c27fffb437f171de0e0ca205d03444f566ee`.
The preceding checkpoint retains its own fingerprint and measurements.

### Established results

- The repeated strict cycle guard and maximal floor/clamp count are checked.
  The new executable macro induction proves exact literal transition weight,
  terminal chart and complete ordered children **conditional on a successful
  HOL macro return**. It does not discharge fuel totality.
- The finite transition model has checked modular headroom, delta/phase
  transport and a checked 92-position trace from `N(2,10)` to the next fork at
  `(7,12)`. These are abstract positions, not 92 literal transitions. The
  14,784-state cardinality is proved; the complete rank/cycle instance is not.
- Certificate reporting is read-only. It neither verifies nor hashes the asset;
  a query that has not admitted its value reports `runtime_verified=false`.
  Cold value admission still uses the forest. Warm admission checks memo
  authority before asset hashing.
- Interior-cycle transport rebinds the receiving source and index. Weighted
  boundary fragments support charged partial selection, but cross-exponent
  publication remains refused until its lifting proof is complete.
- Decimal streaming uses the shared balanced radix conversion with charged
  workspace and cleanup. Admission occurs at the first pull; reset during a
  stream rejects the next emission. No separate decimal conversion owner was
  introduced.
- Boundary templates now have ledger-owned immutable component snapshots.
  An adversarial nested-payload mutation exposed insufficient validation;
  header checks and demanded component checks now reject it. Sealing failures
  roll back retained stores. Actual scalar transitions are counted separately
  from represented transitions, including on cache hits.

### Assertion mapping and independent review

No genuine construction assertion was removed or weakened. The reporting test
now expects an unverified metadata snapshot and poisons asset access, hashing
and verification. Budget-refusal checks invoke value admission rather than the
read-only reporter. Phase-enumeration counters were replaced by charged closed
cycle-rule evaluations. Two poison hooks moved to their canonical owner in
`action_arena.py`; their assertions remain unchanged. The rejected-prefix test
charges its one performed admission operation rather than an absent second
verification call.

The independent HOL/Python audit found no local arithmetic counterexample. It
identified the exact remaining bridge: the finite Entry/Near model omits
literal weights and landmine endpoints, while production retains affine
weighted fragments and a partial selector. Their equality, all-state totality
and exponent-shifted execution are not established by the local periodic law.
The initial N-boundary tick must be included in that bridge.

### Validation and remaining work

Raw evidence is local under
`results/current/comma-boundary-quotient/cutover-2026-09-23/`; these paths are not
portable artifact links. Failed builds and timeouts are retained there.
Runs 47, 52 and 57 temporarily excluded the finite-transition theory for
diagnostics; they are not aggregate acceptance. Run 64 includes every
registered comma theory with the complete session list restored.

| Check | Result and scope | Evidence |
| --- | --- | --- |
| Focused runtime checks | 345 PASS, 4 separately selected validation cases excluded; 32.39 s / 99.1 MB under 35 s / 1 GiB | `comma-cutover-focused-verified.*` |
| Full default units | 6,849 PASS / same 42 FAIL; 22 added passing tests, no removed tests or new failing IDs; 249.55 s / 811.6 MB under 300 s / 1 GiB; identical before/after source fingerprint | `comma-cutover-unit.*`, `unit-comparison.json` |
| Explicit P0 selection | Same 13 PASS / 50 FAIL, identical selection and failing IDs; 2.49 s / 88.7 MB | `comma-cutover-p0.*`, `p0-comparison.json` |
| Registered comma Isabelle session | PASS, 21.36 s / 1.21 GB, with oracle audits; checked parent heap reused | `comma-cutover-isabelle-64.*` |
| Repository aggregate Isabelle | All 22 registered sessions PASS, 11.18 s / 1.17 GB, incremental checked-heap reuse | `comma-cutover-isabelle-repository.*` |
| Arithmetic parent | PASS including finite-period laws; the combined parent/child invocation hit 60 s before child completion | `comma-cutover-isabelle-54.*` |
| Installed wheel | 18 CLI cases PASS, 21.38 s / 117.4 MB; runtime files match frozen source; forest module and asset still present | `comma-cutover-installed.*`, `wheel-source-inventory.json` |
| Strict quality | PASS: mypy, Ruff and format checks on 1,516 Python files; policy, docs and proof inventory; 11.23 s / 631.4 MB | `comma-cutover-quality-final.*`, `comma-cutover-proof-index.json` |
| Targeted production latency | Five trials each at index 1,024 in cold/repeat/bypass modes; all guarded packets completed | `comma-cutover-probe-*`, `targeted-latency-summary.json` |

An earlier `-a` aggregate command unintentionally selected Isabelle's entire
distribution, including Codegen, and timed out at 60 seconds. It is retained as
`comma-cutover-isabelle-all.*`, not counted as repository aggregate evidence.
The corrected command obtains all 22 names from the shared ROOT parser.

At index 1,024, median cold admission was 5.095 s and arithmetic construction
41.19 ms. Warm admission was 34.12 microseconds; cache-bypassed admission was
5.077 s with 40.92 ms construction. These 15 samples isolate the remaining
forest cost; they do not replace the full growth manifest or prove an
asymptotic bound. A preliminary quality invocation supplied its script through
stdin, which the process guard deliberately closes; its empty log is not
validation evidence. The recorded final quality invocation passes the script
as an explicit argument and requires output from every check.

Still required: total boundary construction within its bound; equality between
the finite and weighted constructors; checked losing classification, winning
cycle and repeating literal path; source-20/prelude and earlier-root exclusion;
partial weighted-selection and scheduler refinement; then global CLI admission
and deletion of the forest. The untrusted generated rank candidate remains
outside the repository and outside Isabelle admission. No new public branch
decision was taken from it. The full new growth/cross-fork acceptance run is
not claimed while this construction gate remains open.

At index 16, median cold certificate admission was 4.97 s, compared with
40.8 microseconds for repeated admission; each cold request reread 813,641
certificate bytes and each measured repeated request reread zero. At the
certified boundary, cold construction after admission was 0.184 s. These are
measured mode differences, not a proved constructor speedup or an asymptotic
bound. The initial timeout remains a performance hold, and cold forest removal
still depends on the missing global proof and production cutover.

## Affine point-germ consumers

**Objective:** selectively integrate the corrected downloaded alphabets and
cursors without installing exponentially growing flat future automata.
**Implemented:** shared spatial affine point normalization and pullback,
Collatz/Antihydra admitted-image point consumers, and lazy Antihydra CLI values.
**Still open:** recursive future-demand construction/closure, reverse temporal
cutover, and a checked Isabelle refinement of the imported point normalizer.
No current-output equivalence is used as successor authority or a safety proof.

### Input disposition

| Downloaded input | SHA-256 | Disposition |
| --- | --- | --- |
| `number-compiler-main-collatz-future-demand-research.zip` | `5300828f44a744befb607efc10bc424ee406faac9d6527dd34eb2ad26cccc156` | Selected point-germ arithmetic ported to the shared arithmetic owner. The independent scalar cold cursor and alphabet enumerators are not production executors. |
| `collatz_cold_cursor_minimal_germ.patch` | `cdee2da67405252825698c17cf5e644a31df2355537f1d02976daf7912d70c5c` | Reference for the periodic bit/blank semantics. Existing scheduler source admission is retained. |
| `collatz_future_demand_quotient.patch` | `08f1ab3d429c77040e51916185bf924756184d37dbc092e6d68a49e168ac1ade` | Flat future-reader compilation is not imported as a performance optimization. Current-point collision retained as a regression. |
| `196_future_response_quotient_search.zip` | `32be2736cf37244103f204384b78865d6e37a61ffae9fb75e8736be2758b85e0` | Bounded future-response reference. Its D4 interior reader has 45,592 minimized states; it does not supply the missing compact source-relative recursive constructor. |
| `196_future_response_quotient_search.patch` | `dbcf30e87362610c4ab071f5d4cf28602c66b43c1fb60f18ba3ab01d2b3910f2` | No production cutover or weakening of reverse positive assertions. |

The two pasted corrections propose recursive affine/branch residuals and
source-relative reverse responses. Neither includes a completed closure or
construction-bound proof. A finite leaf alphabet is not a finite temporal
state set. Their rejected flat representations are not counterexamples to
the proposed recursive grammar.

### Changes and scope

- One `AffinePointGerm` implements exact even-factor reduction, reflection
  normalization, positive affine spatial pullback and threshold transport.
  Evaluation masks the high coordinate before multiplication; no truth table
  or alphabet enumeration runs in production.
- The shared dyadic point consumer authenticates source/action/image bindings,
  reduces the affine numerator before multiplication and retains the exterior
  cutoff independently. Remote exterior queries compare bit lengths before
  constructing a power. Zero retains its canonical single zero digit.
- Collatz retains its existing demanded microblock cache and whole-limb path.
  Antihydra point requests no longer call `result()`; they reuse the arithmetic
  image without endpoint construction, physical roofs or first-failure descent.
  Antihydra ordinary CLI values similarly do not request the safety result.
- Mahler still consumes the same exact Antihydra support. Its positivity
  predicate and the physical ledger are unchanged. No finite point quotient
  substitutes for their source-dependent safety information.
- New work is counted under family-prefixed `point_germ_*` counters. There is
  no new retained germ cache or global DFA. Descriptor bit counts measure
  summed construction work, not retained storage or saved work.

### Validation scope

The focused consumer checks poison endpoint and safety evaluation, test public
CLI value laziness, compare both laws against independent bounded recurrences,
check warm discovery reuse, foreign/disposed authority and huge exterior
coordinates, and retain the equal-point/different-future witness. Exhaustive
normalization checks cover widths one through five, not every temporal action.

Five-trial paired request measurements at 16–1,024 returns compare the old
Antihydra `result().h` point consumer with the admitted germ consumer. Cold
construction remains approximately unchanged; at 1,024 returns the initial
run measured about 5 ms for both. Warm point demand dropped from roughly
0.16 ms to 0.014 ms. These are same-process demand measurements, not evidence
of a new cold temporal bound or faster full-output conversion. Raw input
manifest, guarded tests and measurements are local under
`results/current/point-germ-integration-2026-09-23/`; they are not portable
artifact links. Final frozen-source results follow below.

### New recursive archive audit

During integration, `number-compiler-main-collatz-recursive-future-quotient.zip`
arrived with SHA-256
`5bd6d2a95cabac66d480173752ceda7c99fa0eacd8dacf112d96dcb4931e3bf1`.
Its `future_recursive.py` has no flat source DFA. The valid local affine
pullback is already represented by the shared `AffinePointGerm.pullback` port.
The complete proposed CLI replacement was not accepted:

- **Exact API counterexample:**
  `RecursivePointDemand.initial(0).source_digit(0).advance(CollatzFutureTimeAction(1)).at_high(0)`
  returns `1`. The specialized source is `x=1+2Y`; at `Y=0`, one physical
  Collatz tick gives `4`, whose bit zero is `0`. Terminal normalization erased
  the source occurrence, so later `advance` applies time to the wrong object.
  Appending time belongs to the source-bound action owner, not a saturated
  point leaf. This witness does not refute recursive source grammar closure.
- **Demand cost:** instrumenting `_source_step` shows 901 scalar tail steps
  for source `931386509544713451`, horizon 1,000, bit zero. Source 27 at
  horizon `10^12` takes 100 scalar tail steps before the cycle shortcut.
  A one-node duration descriptor does not eliminate this charged discovery.
- **Other integration hazards:** unbounded global `lru_cache` alphabet tables,
  a new point-specific authority token disconnected from the admitted image,
  and per-bit limb traversal conflict with the live bounded caches, shared
  scheduler authority and batched limb implementation.

The imported production consumer keeps source/action/image authority separate
from the point germ and exposes no operation for advancing a saturated leaf.
The archive's independent scalar executor and eager alphabet-ID tables are
not imported. Generalizing its scalar continuation to Antihydra/Mahler would
still require their distinct recurrence and safety laws; it supplies no
reverse/add complete-return constructor. The all-family future-quotient
cutover is therefore incomplete. The exact reproduction and counted tails
are retained in the local input-audit evidence directory above.

### Frozen-source validation

Final source fingerprint:
`6101fa556de9250f7277ec31dbdd4031709ba9c8159b353cb2ea29d1b17ef2d7`.

| Check | Result | Scope/evidence |
| --- | --- | --- |
| Focused consumer, Antihydra/Mahler and Collatz checks | 147 PASS, 1.20 s | Exact output, poison guards, safety separation, shared discovery and lifecycle |
| Full default units | 6,867 PASS / same 42 FAIL; 255.44 s / 816.7 MB | `accepted-unit.*`; 18 added passing tests, no removed tests or new failing IDs; identical before/after fingerprint |
| Explicit P0 selection | Same 13 PASS / 50 FAIL; 3.70 s / 88.1 MB | `p0-final.*`; identical selected and failing IDs |
| Strict quality | mypy, Ruff and formatting PASS on 1,518 Python files | No new suppressions or exclusions |
| Clean installed wheel | 18 CLI cases PASS; 22.43 s / 115.8 MB | `installed-final.*`; changed packaged modules match frozen source byte-for-byte |
| Existing dyadic Isabelle integration | PASS, incremental checked-heap reuse; 5.85 s / 1.22 GB | `isabelle-existing.*`; unchanged numeric/safety theories, not a proof of the newly imported normalizer |
| Five-trial demand probes | Cold discovery unchanged within these samples; at 1,024 returns median warm demand 0.157 ms via `result().h`, 0.021 ms via point germ | `benchmark-final.*`, `point-germ-bench.json`; same-process fresh/repeated requests, not fresh-process latency or an asymptotic constructor proof |

The initial full suite found two extra failures because the new binary consumer
bypassed the canonical summary hook. That boundary was restored; assertions
were unchanged. A later in-progress run was deliberately interrupted to add
the same exact-tree guard to direct Antihydra term points. Both runs remain in
the raw evidence; neither is final acceptance. The replacement wheel was
rebuilt after the guard fix. No Isabelle theory was changed, and the spatial
normalizer's executable proof remains a separate obligation.


## Comma chart unification

**Objective.** Replace the divergent finite and sampled-integer boundary
constructors with one Entry/Near transition owner, retaining the proof gates
required before deleting forest-backed production admission.

**Changes and assertion mapping.**

- Corrected the formal N-boundary origin to `Near(a−1,0,1)`; the old
  92-position checked trace remains an Entry suffix, and the complete trace
  has 93 positions. The first edge contributes one literal tick.
- The weighted chart transition is the canonical constructor in Python and
  HOL. Finite control erases its weight; it has no independent transition
  semantics. Entry moves emit `(L*10^(p+delta)-L*(x+h))/P`, Near moves emit one
  tick, and terminal moves retain the exact chart. The macro builder consumes
  emitted weights; a poison test rejects an altered weight instead of silently
  recomputing it. Entry guard/count arithmetic reuses the existing cycle laws.
- Python macro control no longer builds a representative `10**p` or evaluates
  sampled endpoints. The rank-candidate generator's duplicate transition
  implementation was removed. Literal values and charts share the arithmetic
  owner's complete child-alternative classifier.
- Replaced the obsolete test requiring one representative power allocation
  with a poison test requiring zero such allocations. Existing output,
  weighted-selection, authority, budget and branch assertions remain active.
- Independent review found and repaired unbounded forged Near inputs and
  missing operand-size charges during prefix-index construction. The exact
  local headroom cap is 540; this is not an all-state termination proof.
- Fixed the independent phase oracle at source `199079`: a second nominal
  phase crosses the fork at `199918`, whose children are `199999,200000`.
  The oracle now checks the final proposed phase by bounded literal enumeration.
- Warm certificate admission no longer imports the forest verifier; it still
  validates generation-bound authority before reuse. Cold verification and
  the existing finite prefix remain until replacement safety is established.

**Initial measurements (before the short-period integration).** The finite Python audit reproduces 14,784 states, 14,470
losing states, 314 survivors, maximum rank 136, and the 314-fork/+924 return.
Maximum observed chart moves are 1,189; maximum reachable headroom is 519.
These are experiment results, not kernel-checked totality or cycle instances.
A five-trial comparison on 32 boundary states produced identical complete
weighted templates; median constructor batch time fell from 166 ms to 89 ms.
This is neither an end-to-end CLI measurement nor proof of global admission.

Raw commands, failed proof attempts, test output and measurements remain local
under `results/current/comma-chart-unification-2026-09-23/`. Individual guard reports record the checked scope and failures. A complete
frozen-source release validation has not yet passed for this work.

**Remaining release boundary.** Prove every admitted macro completes; connect
all Entry/Near transitions and partial selection to literal paths; kernel-check
the losing-rank and winning-cycle instances; prove source-20 entry and earlier
root exclusion; then enable weighted scheduler admission and delete the forest.
No forest deletion or unconditional repeating-branch theorem is claimed here.

### Independent forest-cutover review

The supplied review dated 2026-09-23 has SHA-256
`8b67af10662119f7cb761a32665302a1c32b4ff7879510a5341070a167acf9c7`.
Its attachment is a local external input, not portable release evidence.

- **Accepted finding:** successful fuelled evaluation implies soundness; it
  does not prove that every admitted boundary state successfully evaluates.
  Local lemmas and finite Python enumeration cannot certify the cutover.
- **Implemented response:** Entry uses a catalog-specific power period at
  most 28, reducing the modular exponent to 5–32. The Python constructor and
  HOL headroom definition share this reduction. The standalone theorem
  `comma_power_residue_correct` was kernel-checked without oracle dependencies;
  registered integration validation is recorded separately.
- **Next proof gate:** a total weighted boundary macro, including every
  partial literal prefix, with no successful-run/fuel premise. Internal fuel
  is permitted only after a sufficient bound is proved for all inputs.
- **Subsequent gates:** shared suffix evaluation, checked losing ranks, the
  314-fork/+924 winning return, source-20 entry and earlier-root exclusion.
  The finite graph must erase the weights of that same constructor.
- **Additional independent finding, fixed:** a terminal move could forge or
  erase its fork label while preserving weight and endpoint. Publication now
  checks the complete terminal alternatives through the shared arithmetic
  classifier, with charged validation and explicit forged-child tests.
- **Admission decision:** forest-backed prefix admission remains in production.
  No rank table, sampled trajectory or local residue theorem replaces the
  missing unconditional repeating-branch theorem.

The earlier integrated attempt (`isabelle-47-bridge`) exhausted its
60-second limit rebuilding prerequisites, before the literal bridge ran.
It is not evidence that the bridge or the complete proof chain passed.

### Weighted proof ownership and follow-up review

The two follow-up attachment hashes are
`e6f353024988ecf7fa6f8b569521911b5f61306effeab4cc1e236e1b5663b37c`
and `2f135adfaeaf4d3b5603e25bb6fd6a2202cf7187ea10271b45e1d4f31e937123`.
They are external review inputs, not checked evidence.

- Moved boundary definitions and literal-path lemmas into neutral theories.
  The weighted constructor no longer imports the scalar macro implementation.
  Removed the superseded `Comma_Macro_Refinement` wrapper after moving its
  retained lemmas. A parser-based ancestry test protects this separation.
- Isolated the forest and scalar reference in sibling sessions. The source-20
  numeric prelude still uses the scalar reference and remains an obligation;
  it is not smuggled into the weighted model's prerequisites.
- Removed the 17 duplicate exponent-929 computations. The same 924-period
  statement now follows from the checked short-period laws and divisibility.
  The universal Entry headroom bridge uses proved modular identities opaquely.
- Reused the closed period refinement to establish sector displacement sets,
  eliminating the second set of semantic phase-sum reductions. The preserved
  catalog statements now live with their arithmetic refinement in
  `Comma_Finite_Period`.
- Saved prerequisite heaps with `build -b`; generated proof-index commands
  now do the same. This avoids rebuilding an already checked focused parent.
- Added the whole-macro selection development above the fragment proof,
  explicitly covering zero, terminal weight and an interior fragment. Its
  closed point expression matches cycle displacement plus a bounded phase
  remainder. Registration is not evidence that this new development builds.
- The proposed exact normalized-suffix memo does not provide the hoped-for
  reduction in the finite sizing experiment: 14,784 starts visit 1,980,547
  distinct chart states (415,800 Entry and 1,564,747 Near evaluations), with
  maximum depth 1,189. This is local Python evidence, not a totality proof.
  It rejects that cache-reuse argument, not the finite boundary quotient.

Build `isabelle-63-neutral` hit the unchanged 4-GiB cap. With smaller internal
JVM/ML heaps and sequential proof execution, `isabelle-64-neutral` passed in
58.02 seconds at 1,219,596,944 sampled bytes under the same 60-second/4-GiB
guard. The failed attempt remains recorded. This checks the reordered neutral
arithmetic only; downstream validation is separate.

After catalog consolidation, `isabelle-67-neutral` passed in 57.13 seconds
at 1,205,637,776 sampled bytes. These two single runs do not establish a
statistically significant latency improvement. The structural result is the
removal of redundant evaluation with the same theorem statements.
The independent changed-path audit found no further authority defect. It
confirmed that warm certificate hits remain generation-bound and avoid the
verifier import, while cold forest admission remains. Modular powering charges
operand-bit work with an executable exponent bounded by 32; its internal
multiplies are not separate `comma_work` operations.

The reordered core passed again (`isabelle-68-core`, 35.58 seconds / 1.17 GB).
Both relocated reference sessions passed together (`isabelle-69-references`,
22.89 seconds / 1.17 GB). In `isabelle-71-bridge`, Entry/Near refinement and
its oracle audit completed (29.49 seconds theory time), before a proof
application error in weighted selection failed the session. Entry now proves
the actual emitted descriptor and divisibility, not a recomputed weight.
No complete literal-bridge or global branch-safety pass is claimed.

### Scalar-free cutover refinement, September 24

The next external review has SHA-256
`afe49ea02797342536aa6a1a90f51122e5f68e90f57763377ad72981c07af871`.
It identifies five remaining acceptance steps: total weighted construction,
runtime partial selection, concrete ranks, the lifted winning return, and
source-20 entry without scalar/forest ancestry.

- Moved every first-winning-trace fixture, its chunk checks and 92/93/4096
  examples to `Comma_Trace_Regression`. Their assertions are preserved in a
  separate registered regression session. Core now has 630 lines and passed
  `isabelle-76-core` in 27.52 seconds / 1.17 GB.
- Extended ancestry tests to exclude both legacy execution and numeric trace
  fixtures from the canonical proof chain.
- Stopped optimizing the scalar prelude after two 60-second timeouts
  (`isabelle-73-prelude`, `isabelle-75-prelude`). Independent review then
  confirmed that this unbuilt draft had no importing theory or checked result.
  Deleted its 42 scalar checkpoint rows and session. Its path-to-fork and
  complete-child assertions remain obligations in `Comma_Source_Entry`;
  deleting the draft does not establish them. The already-checked scalar
  reference and forest sessions remain separate.
- Added a local-edge totality checker using the already-proved control erasure
  to avoid computing representative literal weights. Sixteen slice obligations
  cover all 14,784 starts. Checker soundness and a one-state cost probe are
  separate from an all-state instance; no total constructor or fuel removal is
  claimed from those definitions.
- Weighted selection progressed through partial Entry refinement. Subsequent
  errors in prefix-index proof syntax and its missing executable list scan are
  being corrected. Whole-macro/CLI refinement remains unaccepted until the
  complete session builds.

The local-edge witness refinement has SHA-256
`5b9e80e7d9c62f4e1a73983de311fc77c83cbbab3f82302e3eb78cba563832b9`.
It changes the evaluation boundary, not the accepted graph:

- The control trace checker and its generic soundness theorem have one owner
  in `Comma_Finite_Transition`. Regression fixtures consume that owner; they
  do not supply premises to totality.
- Retired recursive-run simplification probes timed out under the original
  60-second limit. Their exact 93/4096 semantic assertions remain in the
  checked regression session. No failed attempt is counted as proof evidence.
- The replacement totality development checks exact-depth witnesses and
  derives a common maximum bound. A checked covering instance is still needed
  before removing fuel from semantic admission.
- Partial Python selection now uses the bounded phase-residue sum instead of
  reclassifying full decimal endpoints. The focused boundary tests pass
  (`python-phase-selection`, 26 cases), and the broader comma/inventory check
  passes (`python-chart-final`, 278 cases). These intermediate runs precede the
  final proof-source freeze.
- Independent review caught a scope gap in source entry: a literal path does
  not establish absence of earlier forks. The draft path theorem is therefore
  named `comma_source20_to_fork`; unbranched-prefix safety remains explicit.

Local-edge evaluation now passes its bounded probe (`isabelle-118-totality`,
12.74 seconds / 1.17 GB sampled process-group footprint). The 12-position
`Z(7,5)` witness is stored once, checked against canonical moves, and tested
against wrong-start and truncated inputs. The original regression assertions
also pass (`isabelle-114-regression`, 17.49 seconds / 1.18 GB). These are
focused builds with saved parent heaps, not complete release acceptance or
an all-state classification instance. The failed recursive evaluations remain
in the evidence directory.

The normalized-control commuting law and oracle audit pass in
`isabelle-125-core` (54.76 seconds / 1.20 GB sampled group footprint).
Normalization retains the local residue phase and explicitly forgets absolute
exponent gain; it must not authorize copying weights between exponents.
This build does not show a core latency improvement over the earlier focused
builds. The proof adds the requested semantic connection.

The existing rank-candidate tool now also streams untrusted witness slices;
`--witness-only` avoids full rank discovery and keeps one macro in memory.
All 16 slices generated in 4.44 seconds / 16,859,640 sampled bytes, with
14,784 starts, 1,980,547 position rows and maximum depth 1,189. The 36.6-MB
JSONL candidates remain ignored local evidence, not versioned theory tables
or accepted certificate instances. Six focused generator tests pass, including
wrong-content rejection and rank-construction poisoning.

Independent cache review also found the read-only certificate observer still
bypassed malformed-marker validation. Admission and reporting now share an
exact-type, bounded-length, ASCII check before constant-time comparison.
Non-ASCII and oversized forged markers must raise the intended rejection
without asset access; cold forest verification is unchanged.

The complete conditional selection session passes `isabelle-132-selection`
(19.64 seconds / 1.18 GB sampled group footprint), including zero, terminal
weight and every interior selected fragment. The formula consumed by partial
Python selection is the checked cycle-count/remainder expression. Successful
canonical trace construction remains a premise; this pass does not remove
fuel or authorize the global CLI route.

### Decimal-round totality refinement

External review SHA-256
`a3662a51b907252b9b73a9183f6ed9dca2df0c4da46be456f71e268995f9dbde`
replaces the proposed full trace bundle with a derived decimal-round closure.
Its 84,084-state claim is reproduced by the canonical Python chart owner,
not yet by a checked Isabelle instance. A round stops at a fork, landmine or 9-to-1 crossing;
Near headroom decreases inside a sector, and other crossings advance the
sector. The proposed well-founded measure uses sector spacing 1,024, which
also dominates the Entry offset 600 (merely exceeding 540 is insufficient).
The constructor's decade rank must remain separate from the boundary
losing rank used to justify sibling pruning. The older local trace checker
retains its soundness/regression role, without becoming the all-state artifact.

The convention matters: terminal states have rank zero, so the measured maximum
rank is **26**, representing **27 round evaluations including the terminal
round**. The first maximum chain starts at `(42,68)` and terminates at the fork
from `(68,10)`. Generation checked every successor/rank equation and emitted a
193,394-byte phase/rank candidate in 6.65 seconds, with 38.3 MB sampled footprint.
This compact candidate replaces the proposed 36.6 MB trace bundle as research
input; neither artifact authorizes production admission. Reproduction:
`python -m devtools.experiments.comma.generate_rank_candidate --decade-rank-only --decade-rank-output PATH`.
Ignored local evidence: `comma-chart-unification-2026-09-23/decade-ranks.{log,json}`
and `decade-rank-candidate.jsonl` (relative to `results/current`).

Builds 137 and 139 exhausted the source-entry budget at the first 37-edge
trace chunk, using broad simplification and then `code_simp`, respectively.
They provide no source-entry theorem. Round builds 138 and 140 reached further
into the well-founded definition but failed on explicit proof/type obligations;
they do not certify the full round theory. Failed build records remain in the
same ignored evidence directory.

`isabelle-144-round` passes in 25.46 seconds / 1.17 GB sampled footprint:
`comma_round_close` is a well-founded HOL function with no fuel parameter,
and `comma_round_close_refines_trace` connects it to canonical chart edges.
Fork, landmine and crossing results preserve their exact finite-prefix meaning.
This is a **single-round** theorem; admissible-input validity, repeated-round
rank checking, winning-cycle safety and production fuel removal remain separate.

The subsequent reviews (SHA-256
`cd85a031748ce051b870b3a7dc9b298ae5a118189cbd2e0c237136bcd11287ec`
and `1c324d7bc22cf7ac2204f31c0a7a17908fde7723a4c2d80a1b6f99609c941f59`)
separate chart-operation counts from literal term weights. Cross witnesses now
retain the pre-crossing Near chart as terminal and the new Entry chart as target.
The normalized successor/rank table is unchanged by this witness correction.

`isabelle-163-decade` passes in 41.89 seconds / 1.15 GB sampled footprint.
It checks admitted-round validity, phase normalization, source-exponent transport,
crossing closure and the generic decreasing-rank implication. Semantic decade
control returns only the outcome; chart-operation diagnostics have a separate
function. The concrete 84,084-state instance remains unchecked. The source-entry
draft's presence in an upload is not evidence of a successful local build.

Source-entry builds 149 and 155 exposed broad simplification of recursive gcd
and symbolic nested-let arithmetic. Closed gcd equations and staged substitution
let build 161 check the first 37-edge chunk without the previous timeout.
It then failed on an inapplicable intermediate rewrite for a Near-only seam;
the final numeric check remains mandatory. A repository policy check now rejects
direct global `gcd_nat.simps [simp]` registration and simp aliases to that rule,
while allowing closed local proofs. It uses the shared Isabelle source lexer.

`isabelle-166-round-weights` passes in 15.63 seconds / 1.17 GB sampled footprint.
It proves weighted-prefix existence through canonical erasure, crossing weight
`+1`, and zero literal weight for terminal fork/landmine inspections. Weights
remain outside the control constructor and rank checker. Source-entry build 165
checks all 230 edges and six weight chunks, then fails on final concatenated
`butlast` sum rewriting; it is not a completed source-entry session.

### Review follow-through: control counts and literal indices

The latest review's changes are separated from the global cutover gate:

- The Python crossing witness retains the pre-crossing Near chart and the
  distinct Entry target. A forged `terminal=target` witness is rejected.
- Semantic decade control returns only its outcome. Internal edge counts and
  terminal inspections remain separate diagnostics, never literal indices.
- Build `isabelle-170-entry-witness` checks the 230 source-tail positions and
  six weight chunks in 39.26 seconds / 1.12 GB. Its saved parent heap avoids
  repeating that evaluation during downstream source-entry repairs.
- Build `isabelle-178-round-weights` checks the literal-path bridge in
  15.35 seconds / 1.17 GB: admitted source, exponent at least five, and matching
  residue/exponent phase are explicit assumptions. Crossing adds one literal
  transition; fork/landmine inspection adds zero.
- Adversarial review invalidated the interpretation of build 175's smoke as
  an unconditional round result: its Boolean elimination could leave a premise.
  Build `isabelle-182-round-witness` passes the repaired elimination and explicit
  zero-premise/zero-hypothesis checks at every memo insertion and publication
  (13.82 seconds / 1.17 GB). It covers one state, not all 84,084 states.

The shared Isabelle lexer now rejects direct and aliased global recursive gcd
simplifier registrations, while allowing local closed arithmetic proofs.
The focused review selection passes 51 tests with validation markers enabled;
all 255 comma sequence tests pass in 23.80 seconds. Strict mypy checks 1,522
files; authored-code Ruff and formatting checks pass. Repository-wide Ruff also
required formatting the existing point-germ benchmark script; its computation
and workloads are unchanged.

Source-entry build 181 checks the small-exponent prefix but fails its generic
terminal trace lemma. Build 183 times out while repairing that lemma; neither
certifies the full source-entry theorem. The concrete 84,084-state rank,
14,470/314 future-safety classification, infinite return and CLI forest removal
remain uncompleted obligations. The Python rank experiment does not replace
those proofs. All referenced build records are ignored local evidence under
`results/current/comma-chart-unification-2026-09-23`, not portable artifacts.

### Proof-history reliability and short-phase reuse

The September 26 reviews narrow the optimization to proof construction and
memoization. They do not supply a checked global rank instance.

| Review | SHA-256 | Applied scope |
| --- | --- | --- |
| Constructor history erasure | `4ad0d70f6bd533ebdc7225598313846cced9d5022c137e67848ee63010445e90` | Normalized control congruence; absolute gains and weights remain occurrence data |
| Short-period compilation | `d38c0534f24175b0ed267dc67949f8ad39a0ed3f1fbc7acf46a7491f7f6ec356` | Checked period/power facts and persistent Entry representatives |
| Memo lookup and proof dependency costs | `955fbbdc48b661afb6744533407ea98bd44e61d2323b5d9a1080e38ca228f64b` | Incremental dependency auditing and lookup-before-normalization review |

Established results:

- `isabelle-187-source-entry` checks the source-20 path to the first fork;
  `isabelle-201-source-unique` checks uniqueness of every preceding edge
  (18.70 seconds / 1.17 GB). The exact total is 412,987,858 transitions, with
  terminal children 19,999,999,999 and 20,000,000,000. There are no remaining
  premises on these concrete prefix theorems.
- `isabelle-195-short-phase` checks Entry phase transport (12.90 seconds /
  1.13 GB). Its key uses `(r+delta) mod T`; the power table separately uses the
  rotated index `(r+delta+919) mod T`.
- `isabelle-196-decade-future` checks history congruence (45.07 seconds /
  1.16 GB). Raw fork/landmine gains are **not** equated: outcomes are compared
  after normalization to the terminal residue phase.
- `isabelle-204-round-weights` rebuilds the weighted literal bridge against
  that checked parent (15.91 seconds / 1.14 GB).
- The compiled arithmetic contains 90 period equations, 17 short periods
  and 116 exact modular-power equations. Build `isabelle-202-compiled-entry`
  checks compilation and the local witness smoke (17.90 seconds / 1.17 GB).

The first 91-offset baseline, `isabelle-184-round-phase-five`, passed in
52.39 seconds overall, with 39.664 seconds of theory evaluation. The initial
short-phase integration, `isabelle-199-short-phase-slice`, timed out under the
unchanged session limit; its source fingerprints matched. It is retained as a
failed optimization attempt.

Independent inspection of Isabelle's `Thm_Deps.all_oracles` showed that each
call starts a fresh dependency traversal. The evaluator now certifies
immutable proof-node serials locally, checking every root's direct oracles and
every theorem's premises/hypotheses on each insertion. It commits audited node
identities only after successful traversal. A final built-in oracle audit
remains mandatory. The cache is not transferable between unrelated heaps and
is never keyed by proposition equality.

With that change, `isabelle-203-short-phase-slice` passes in 42.60 seconds /
1.19 GB, with 28.808 seconds of theory evaluation. Before/after authored-source
fingerprints both equal
`45bf5bd2d904da8f26d51949e2b74d0955c69859a4cebfd59450d64eca90579e`.
Exported evaluator measurements record 423 Entry representatives, 1,095 Near
and sector facts, and 846 round results. Incremental oracle checking used
188 ms over 6,870 calls and 26,928 distinct dependency nodes. This single-run
comparison is not an all-state throughput or release-performance result.

The shared process guard now optionally records before/after authored-source
fingerprints with `--source-root`. A changed fingerprint invalidates an
otherwise successful run. This checks the two snapshots; it does not claim to
detect mutations reverted before the final snapshot. No production asset
hashing was introduced.

The remaining totality interface must consume certified round equations into
rank-decrease statements, cover every index below 84,084, and prove the rank
bound 26 before deriving the 27-round bound. Complete round equalities are a
bounded regression artifact, not the intended full-rank output. The separate
14,784-state branch classification, winning return and public forest/fuel
cutover remain unproved. Entry and history results do not close them.

The follow-up memo review found that representative lookup still followed
normalization. Entry now reads the numeric right-hand sides of the checked
period facts to choose `(f,x,k)` first. This ML key is untrusted: a certified
phase reduction must equal it, and the cached equation must compose back to
the exact requesting source. On a hit, no headroom or power conversion runs;
`comma_shift_move` restores the requesting exponent gain. Independent review
checked that `+919` occurs only in power evaluation, never in this Entry key.

Build `isabelle-205-key-first-entry` passes the repaired owner and negative
certifier tests (17.57 seconds / 1.17 GB). A theorem with an open premise and
a theorem with a hidden hypothesis are both rejected without changing the
certificate cache; `TrueI` is accepted. A request shifted from phase 5 to 929
retains its exact source equation, increases representative hits, and performs
no additional representative construction or power evaluation.

Build `isabelle-206-key-first-slice` passes in 39.03 seconds, with 25.544 seconds
of theory evaluation. Its counters included inherited parent setup; the final
report corrects that scope. Build `isabelle-207-final-slice` passes in
**38.01 seconds / 1.18 GB**, with **24.818 seconds** of theory evaluation.
Both source snapshots equal
`f1e661a69943b51ac1e35c25c11021d5a7cf0f5a8a223aa4b1110ca36c2f44ef`.

| Final slice measurement | Value | Scope |
| --- | --- | --- |
| Evaluator plus final oracle audit | 22,785 ms | Child session only; whole guarded build reported above |
| Entry representatives | 9 initially; 423 finally | Parent setup retained explicitly |
| Representative hits / misses | 9 / 414 | New child work; 414 power conversions, exactly one per miss |
| Near / sector facts | 28 initially; 1,095 finally | Retained proof structure, not temporal rank coverage |
| Sector hits / misses | 54 / 1,067 | New child work |
| Short-key reduction / composition | 1,475 / 700 ms | Child work, distinct from full evaluation |
| Incremental / final oracle audit | 115 / 49 ms | Full final built-in audit retained |
| Audited dependency nodes | 26,815 initially; 26,928 finally | Immutable proof identities; root oracles still checked on every call |

The plain `key=value` export is available from the session database:

```console
isabelle export -n -d devtools/proofs/isabelle -O OUTPUT -x '*:comma-phase-metrics.txt' Comma_Round_Phase_Slice
```

These are recorded individual runs, not five-trial performance acceptance or
evidence that all-state evaluation fits the same limit. The optimized slice
still exports only 91 exact equations. No rank coverage or global safety
assertion has been weakened or replaced by a successful refusal.

Final frozen validation on `f1e661a69943`:

- `final-history-tests`: 74 passed, 14.96 seconds; guard 15.34 seconds /
  62.2 MB, with matching source snapshots.
- `final-comma-tests`: 255 passed; guard 22.56 seconds / 88.5 MB, with matching
  source snapshots. Both selections explicitly include validation markers.
- Strict mypy: 1,523 files passed. Ruff, formatting, repository policy,
  documentation links and the proof inventory (37 sessions / 147 theories)
  passed. The generated 91-row regression fixture reproduces exactly.
- The final built-in oracle audit remains enabled. No skipped proof, new
  axiom or theorem oracle was introduced. Independent review checked the
  incremental audit's node identity and transaction semantics and the Entry
  transport's source/gain preservation.

No full-unit, P0, installed-wheel, aggregate Isabelle or growth acceptance was
rerun for this proof-checker increment. Their historical failures and scope
remain recorded in the release ledger.

## September 26 — adversarial shared-owner and memo audit

**Objective.** Remove duplicated arithmetic and authority encodings without
merging source occurrences, weakening admission, or claiming temporal grammar
closure. Three read-only explorers reviewed shared mathematics, proof ownership,
and memo/grammar identity. The coordinator implemented and validated changes.

**Changes and established scope.**

- `consumer_pullback.compose_prefix_safety_values` owns the ALL/min join used by
  `PrefixSafety` and all dyadic image, transport, support and cycle-tail joins.
  Image and support publication reuse one computed summary. Family branch laws
  and ledger charges are unchanged.
- Antihydra's admitted-word and discovered-word constructors use one bounded
  arithmetic scan. Supplied words are retained directly; the review caught and
  removed an intermediate version that rebuilt them unnecessarily. Physical
  roofs remain optional and mathematically distinct.
- The three finite-output blank predicates use one admitted Boolean circuit in
  `semantic_bit_transforms`. Output signatures, validity and ledger publication
  are unchanged; no input-domain table is introduced.
- Tile publication and validation share the neutral record snapshot owner.
  Memo modules no longer import private serializers from the causal executor.
  Antihydra's eleven-field projection-key snapshot has one owner rather than
  three. Mutation tests retain independent forged-record encodings.
- Higher-record audit helpers share a read-only interner check, preserving the
  identity fallback on corrupted keys and each caller's separate ownership
  checks.
- `Hensel_Cylinders` moved unchanged to `Shared_S_Arithmetic`. Collatz no longer
  inherits the reverse/add session solely to import it. The unused
  `collatz_one_cycle_returning_action` alias was removed; its exact canonical
  theorem, `collatz_cycle_chunks`, remains checked and documented.
- The live `Reverse_Two_Cell_Equations` helper is now registered and explicitly
  audits all three exported theorem groups. Proof inventory checks cover
  reachable helpers, including unregistered imports, and reject local session
  dependency cycles without rejecting external Isabelle parents.

**Audit conclusions.** No current stale integer-ID or changed-consumer memo
failure was reproduced in the reviewed production paths. Demand-specific
construction currently publishes complete images for all reviewed families.
The adapter documentation incorrectly suggested that sufficiency for one demand
was enough; the contract now states that later projections, actions and failure
descent must remain supported. Both demand orders are regression-tested. Demand
was deliberately not added to application keys, which would fragment valid
source/action reuse. Projection equality still cannot authorize source merging.

The audit did not merge full-polynomial arithmetic with truncated primary jets,
or streaming carry normalization with APIs retaining complete carry boundaries.
Those representations have different contracts. A fixed leaf alphabet and
matching formulas remain insufficient to justify complete future-action
identity, so no new grammar merge or speed bound was asserted.

**Evidence location.** Commands, bounded output and guard reports are local
under `results/current/shared-owner-audit-2026-09-26/`. The initial snapshots
selection contained a nonexistent test path and was corrected; its failed log
is retained. The first shared-math selection exposed an obsolete test fixture
that supplied an unaudited helper; the fixture now supplies a real audit and a
separate negative test enforces rejection. No positive production assertion was
removed or weakened.

**Independent review.** The proof explorer checked import ancestry and unchanged
theorem statements. The math explorer checked the safety join, supplied-word
semantics and exact Boolean circuit ownership. The memo explorer checked every
snapshot field, ledger-local identity, corruption fallback and demand-order
reuse. These reviews do not certify all repository paths or complete executable
refinement of Python.

**Validation and provenance.** Final authored-source fingerprint:
`32e6212b1c5c9459409ff8316bf643d9a60ae05ebac15ae4735f67cdec445ad5`.
Documentation is outside this fingerprint and checked separately.

| Evidence | Result and scope | Guard elapsed / sampled peak |
| --- | --- | --- |
| `snapshots-2` | 53 authority and memo tests passed | 1.94 s / approximately 80 MB |
| `antihydra-seals` | 60 projection/cache tests passed | 2.40 s / approximately 60 MB |
| `shared-math-2` | 169 arithmetic, family and proof-inventory tests passed | 9.45 s / 70,156,888 bytes |
| `shared-interfaces` | 191 interface, mutation and lifecycle tests passed | 3.75 s / 93,356,632 bytes |
| `shared-proof` | `Shared_S_Arithmetic` built, including moved Hensel theory | 26.43 s / 1,219,235,128 bytes |
| `collatz-proof` | `Collatz_Cylinder_Refinement` built with shared parent | 15.78 s / 1,203,703,552 bytes |
| `reverse-proof` | `Reverse_Residuals` built with helper oracle audit | 38.61 s / 1,265,553,128 bytes |
| `dyadic-integration-proof` | `Balanced_Dyadic_Integration` built | 24.81 s / 1,267,043,640 bytes |
| `temporal-integration-proof` | Downstream `Temporal_Clock_Jumps` built on final fingerprint | 36.66 s / 1,274,744,480 bytes |
| `full-unit` | 6,942 passed, 43 failed; 42 exact historical failures plus one introduced test-file line-cap violation | 249.25 s / 825,345,176 bytes |
| `repair-tests-2` | All 80 scheduler and repository-policy checks passed after repair | 6.09 s / 657,163,224 bytes |
| `quality-final` | Strict mypy (1,523 files), Ruff, formatting, policy, docs and proof index (37 sessions / 147 theories) passed | 10.15 s / 633,619,872 bytes |
| `p0` | 13 passed, 50 failed; exact failure set matches the previous selection | 2.17 s / 89,129,584 bytes |
| `wheel-build`, `installed-wheel` | Clean isolated build and installed CLI/authority checks passed | 2.65 s / 96,027,680 bytes; 20.89 s / 115,476,568 bytes |

The full-unit run used `261d1ea48034`, before the test-only line-cap repair. Its
new two-order regression was folded into the existing complete-image test;
original output, child-poison, publication and zero-primitive assertions remain.
The demanded branch uses its correctly named demanded-composite counter. The
final file meets the unchanged 1,000-line cap. Full units were not repeated after
this test-only consolidation; `repair-tests-2`, quality, P0 and installed-wheel
checks carry matching final source snapshots. The first wheel attempt lacked a
local setuptools backend; normal isolated build dependencies resolved it.

`failure-disposition.json` maps every full-unit failure against
`results/current/point-germ-integration-2026-09-23/accepted-unit.xml`;
`p0-disposition.json` compares the exact previous P0 selection. The only new
full-unit failure was the repaired file-size violation. The 41 existing
reverse/add unit obligations, one F4 unit obligation and 50 P0 failures remain
active. No skips, expected failures or success-on-refusal replacements were
introduced. All five Isabelle builds kept the existing theorem statements,
explicit oracle audits and 60-second/4-GiB limits.

**Remaining work.** This audit supplies shared owners and checked session
boundaries, not a general temporal grammar, its construction bound, an étale
terminal extractor, or a source-global safety proof. The comma all-state rank,
winning return and forest/fuel cutover remain separate obligations. All-session
Isabelle and the five-trial growth manifest were not rerun for this cleanup;
their recorded release holds remain in force.

## Root-shell and consumer-relative Moore integration

**Objective (September 26).** Audit the downloaded compiler3 Collatz patches and
root-shell notes, reuse finite algebra through the existing source owner, and
separate observable-state reduction from source construction cost.

**Implemented.** The shared consumer-pullback module now owns canonical exact
half-open guards and guarded affine composition. Research Mahler source blocks
reuse this owner instead of defining another interval algebra. Their root chart
is `theta=2t=r²`; coefficients and guards remain rational. The existing production
`antihydra --info mahler` projection reports signed radicand coefficients and the
complete root guard from its admitted source image. It performs no new source
scan, segment fold, physical-roof request or floating-point square root. Schema
8 reports root-projection calls and operand bits; absent measurements remain
null. The private packet formatter is not a source-admission API.

**Checked mathematics.** `Mahler_Source_Event_Safety` now transports actual
source-cylinder endpoint and guard composition into the root chart. It proves
the source-selected event law and exact interval `1 ≤ (3/2)^q theta < 3/2`,
including intermediate safety. The source-7 first guard is `[2/3,1)` and every
prefix of length at least two has an empty guard. This is Mahler fractional
safety, not Antihydra ledger halting. The same session's oracle audit covers the
new results. These real-valued theorems plus independent rational differential
checks are not a completed extraction/refinement proof of the Python scheduler.

**Selective patch integration.** Iterative decision-terminal relabeling and
structural metrics share the existing decision arena. The bounded Collatz
experiment can request support, endpoint-plus-clock or endpoint observations,
then independently minimize their derivatives. Derivatives honor the declared
coordinate order. Projection construction is capped at 12 bits and uses a
conservative aggregate retention preflight; derivative certificates have an
explicit state budget. Failed publication retains no new cached projection.
Full support validation remains in `bind/select`; weaker observer equality
cannot identify authenticated source occurrences.

| Source bits / physical ticks | Support DAG | Endpoint + clock DAG | Endpoint DAG | Explicit Moore states, same order |
| --- | ---: | ---: | ---: | --- |
| 5 / 16 | 61 | 32 | 29 | 62 / 35 / 32 |
| 8 / 16 | 511 | 250 | 235 | 511 / 250 / 236 |
| 5 / 1024 | 61 | 28 | 21 | 62 / 31 / 24 |

The one-shot local construction times were approximately 0.009, 0.023 and
0.080 seconds. They are reproduction measurements, not five-trial performance
gates. DAG and explicit Moore counts differ because the latter consumes every
source position, including skipped coordinates. The 1024-tick experiment still
reports 471 endpoint consumptions and 972 constant bindings: projection size
must not conceal that discovery work.

**Independent findings.** The imported Hensel cursor is disconnected from the
production scheduler and performs full-width modular updates per source bit
without corresponding operand accounting. It also introduces a 16,384-bit cap
and inconsistent budget-exception handling. It was not enabled in production.
The old Moore patch weakened support validation in `bind`, had unbounded
projection retention, and assumed identity variable order; this integration
preserves validation and corrects the latter two issues. No action/source memo
collision was reproduced in the reviewed cursor. The root review confirmed
coordinate scaling and identified an ambiguous offset name; the public field
is now explicitly the signed `radicand_offset` in `A*r²+B`.

**Pinned input checksums (SHA-256).** Files remain external research inputs.

| Download | SHA-256 |
| --- | --- |
| `collatz_compiler3_moore_quotient.patch` | `0d8d2d6acba595cf625c618f29da8638bf219dfa066a644cac7bf6f2890b995e` |
| `collatz_compiler3_hensel_temporal_quotient.patch` | `de75fd3781ce76c2fbd446d104810d7415b42e0edff9727c2907cb13c9e1c31a` |
| `collatz_compiler3_frobenius_occurrence_fix.patch` | `d0c1f18c37509dfa9c0e97a3ea09c887a9ad162da9fe9efbd0b9b64d6a3f8139` |
| `collatz_compiler3_moore_quotient_report.md` | `c4d48c6bbc7ec1e2b545addaa5b8ab6676cae514b289778db94344bf2f22f30d` |

**Remaining obligation.** Root/Vieta/tropical projection has not supplied an
algebraic source constructor with a proved construction bound. The full Hensel
source owner remains distinct from a selected observer's minimal machine.
Neither a repeating future quotient nor global Collatz/Mahler safety or
Antihydra non-halting follows from this integration. Existing reverse/add,
Fermat/Mersenne and comma forest/fuel release holds remain unchanged.


**Validation and provenance.** Final authored-source fingerprint:
`d350d0399a9ac725fdd416ba636ee851bad58b7ec2140bfdd2c4e3646367cd01`.
Local raw evidence is under `results/current/root-shell-moore-2026-09-26/`.

| Evidence | Result | Guard elapsed / sampled peak |
| --- | --- | --- |
| `focused-final-2` | 207 arithmetic, observer, source-guard and Moore tests passed; before final diagnostics fields at `1f0a479f798f` | 2.2 s / under 80 MB |
| `family-regressions-2` | 1,614 passed, five historical reverse/add constructor failures, 50 deselected | 31.20 s / 132,612,768 bytes |
| `isabelle-final` | Clean `Mahler_Source_Transport` session build; seven added root-chart theorems in the oracle audit | 13.56 s / 1,192,709,768 bytes |
| `quality-final` | Strict mypy on 1,524 files, Ruff, formatting, policy, proof inventory and docs passed | 13.76 s / 634,357,176 bytes |
| `wheel-build-2` | Isolated wheel build passed | 2.46 s / 96,388,152 bytes |
| `installed-wheel` | Existing CLI checks plus signed root radicand, guard, shared source and lazy accounting passed | 20.96 s / 118,261,896 bytes |

The five selected failures are matched by exact test name against the earlier
`point-germ-integration-2026-09-23/accepted-unit.xml` in local
`failure-disposition.json`; every one is historical and reaches the existing
reverse/add powered-constructor refusal. No positive assertion was weakened.
The broad family tests, proof rebuild, wheel and final quality share the final
fingerprint. Full units, P0, all-session Isabelle and the growth manifest were
not rerun; their historical failures and release holds remain in force.

Failed exploratory runs are retained: an unavailable build frontend was replaced
by the existing pip wheel workflow; a nonexistent Antihydra test directory was
replaced with its actual API test files; proof syntax errors were repaired before
the checked build. One new test initially confused a 29-node reduced DAG with
its 32-state explicit Moore machine; the final test checks both independently.
The node retention limit bounds the bounded research projection structure, not
all referenced terminal bytes. It is not a production memory certificate.

## Comma chart germs and proof-generation ownership

**Objective.** Replace eager round-proof reconstruction with exact local run,
chart and weighted-germ composition under the existing 60-second/4-GiB guard.
Constructor totality, future branch safety and CLI cutover remain separate
acceptance gates.

**Established local mathematics.** The neutral `Prefix_Effect` theory now owns
the generic signed-prefix lemmas reused by dyadic and comma proofs. A Near
germ retains its internal unit count and terminal headroom; its actual
headroom summary is `(t-h,t-h)`, not minus the unit count. The checked chart
action retains decimal rebasing and ordered, relation-preserving guard
pullback. Terminal-event lemmas prove the complete child set and exact zero
or unit literal weight. Landmine admission is the conjunction of its two
walls. Control-round construction refines the canonical round and uses at
most nine sector calls. Its sector-control view is definitionally projected
from the weighted sector owner, with the old case equation retained only as
a derived theorem.

**Rejected simplifications.** Headroom cannot be added across chart seams:
`199991 → 200003` changes 9 to 99997, not -3. Positive headroom does not exclude
a fork. Control equality cannot erase actual exponent gain or evaluated
weight. A guard true at one bound source is not a complete admission
equivalence. No whole-round scalar tropical reduction or normalized future
merge is authorized by these local results.

**Timeout diagnosis.** The first new witness build spent about 30.8 seconds
reproving decade control, then rebuilt weights and run germs before reaching
its evaluator; it timed out. Changing its heap parent first to `Comma_Run_Germ`, then to the checked
`Comma_Weighted_Round`, avoids those repeated proofs. Chart and terminal sessions are separately
cached so terminal repairs do not reprove the checked chart algebra. Focused
session reuse does not replace aggregate release validation.

**Evidence ownership.** Each guarded source-bound run receives a fresh proof
generation associated with its authored-source fingerprint. The shared source
inventory also supplies file and directory revision checks. These reject
changed/restored bytes and transient source creation/deletion, even if final
content hashes agree. The child receives the generation token and disables
bytecode writes; output directories are created before binding. Checks occur
at evidence boundaries, never by hashing files on a theorem memo hit.
The evaluator owner becomes permanently invalid after a token mismatch;
restoring the token cannot revive it. A fresh owner has separate theorem and
oracle-audit caches. The token alone does not watch the filesystem: acceptance
depends on the external source-revision envelope.

The independent cache review did not reproduce a wrong short-phase memo hit.
It confirmed that successful transport must restore the exact requested chart,
and that actual exponent gain cannot be reused as a residue-only output.
Certification precedes memo insertion. Smoke-test owners are now local ML
bindings, so their tables do not remain in the saved theory heap. The phase
slice creates its own owner rather than borrowing a smoke-test closure.

The old evaluator's two-pass structure was reproduced directly: after proving
local sectors it timed out in the whole control-round conversion. The replacement composes weighted payloads and a first-event frontier in one
pass. Publication retains a closed all-exponent occurrence certificate, exact
source and symbolic literal weight. The separate complete-round theorem also
connects the constructor to literal execution for admitted exponents at least
five; this is stronger than merely evaluating a record. Terminal payload reuse keeps the actual exponent gain and
derives crossing from the same complete event. These are distinct from the
still-required global rank and branch-safety instances.

An independent simplifier audit found an actual self-loop hazard: using
terminal phase erasure as a general rewrite can rewrite phase zero to itself.
The evaluator now unfolds the payload, erases phase and applies the cached
canonical payload with three one-shot checked conversions. Its key preserves
actual exponent gain. This fix removed the observed timeout at that stage;
no timeout or oracle-audit limit was raised.

**Follow-up review.** The first checked one-pass evaluator still normalized
its growing weighted record after every append, and the rank slice discarded
most of that result. Its source-bound smoke passed at fingerprint
`74b928d78a2cb602e17856c9491e7d0377ec7e458efeaa2bc9f1fcadfe172600`
(`final-witness`: 28.86 s / 1,054,461,168 bytes), but that does not establish
rank-evaluation performance. The subsequent refinement separates the demanded
control observation from the full weighted payload while keeping both tied to
the same proved constructor. It also replaces repeated prefix normalization
with symbolic composition and moves finite cycle-length arithmetic out of the
instance evaluator. Final evidence below must distinguish these revisions.

The first projected slice (`observation-slice-1`, fingerprint
`04054f8b82154a4bffde167dbb500f3b55afd1c2776a08ed91070f2d849c576a`)
checked all 91 unchanged count/chart/event equations in 46.83 guarded seconds,
with 1,210,650,872 sampled peak bytes. Its inner observation work was 28.66 s:
754 sectors, 1,326 lightweight links, 423 Entry misses/331 hits and 1,095 Near
germ misses/376 hits. Weighted exports, terminal payload construction, full
weighted normalization, field projections and weighted compatibility work
were all measured zero. Observation normalization took 484 ms, phase-key
reduction 3,239 ms and incremental proof-node auditing 318 ms. Thus removing
eager weighted proof construction did not make the remaining arithmetic and first-use
Near-class discovery negligible. This slice is not an 84,084-state performance
certificate. It explicitly retains 91 diagnostic equations; the eventual rank
instance must stream compact rank evidence instead.

**Production scope.** Boundary-macro construction aggregates deterministic
Near moves and evaluates periodic displacement with quotient/remainder
arithmetic. Constant affine weights avoid constructing an unnecessary power
of ten; identity composition still checks bindings and budgets. Independent
tests retain every canonical endpoint and reject hidden crossings. These
private boundary actions are not yet the public `CommaTerm._resolve` owner,
so no public CLI speedup or forest removal follows from this change.

**Final validation scope.** Authored-source fingerprint:
`fd9753f0a088342fda226a643bb771eeabe63dbd13dd2cf04a8f67c1bc7f1438`.
Local evidence is under `results/current/comma-run-germ-2026-09-26/`.
Source-bound guards verify both content and revision stability; each run has
its own generation. Earlier failed and successful exploratory runs retain
their original scope.

| Evidence | Result | Guard elapsed / sampled peak |
| --- | --- | --- |
| `final-observation-witness` | Full symbolic-action and lightweight-observation smoke checks, source/delta transport, failed publication and owner invalidation PASS | 25.77 s / 1,155,583,168 bytes |
| `final-observation-slice` | All 91 exact control-count/chart/event equations and oracle audit PASS; eager weighted-work assertions remain zero | 48.62 s / 1,157,074,112 bytes |
| `final-focused` | 343 comma arithmetic, API, cache, source-generation and evidence tests PASS | 37.96 s / 89,883,248 bytes |
| `final-quality` | Strict mypy (1,524 files), Ruff, formatting, policy, documentation, proof inventory (43 sessions/153 theories) and diff checks PASS | 12.14 s / 636,814,752 bytes |

The final slice measured 8,851 ms in 423 Entry conversions, 15,017 ms in
1,095 Near conversions, 3,017 ms in short-key reduction, 599 ms in observation
normalization and 320 ms in incremental proof-node auditing. The timing
categories are diagnostic and may nest; they must not be summed as disjoint
wall-clock work. The exported generation matches the accepted guard report.
These measurements isolate finite arithmetic/first-use discovery as the
remaining dominant work, rather than full weighted-record normalization.

Full weighted joins propagate cached source/target equations with single
selector rewrites and use theorem transitivity for compatibility. They retain
symbolic composition; only a demanded terminal consumer traverses the composed
controls or weights. Independent review found no per-append accumulated-record
simplification. This is not a constant-time bound for kernel term construction
or an asymptotic theorem for arbitrary longer compositions.

The complete 84,084-state rank instance still needs a streamed checked
implementation and acceptable measurements. The boundary losing/winning
instance, infinite return, fuel removal and public forest cutover remain open.
No Python oracle result is promoted to a checked instance. Full units, P0,
all-session Isabelle, installed-wheel and growth validation were not rerun
for this proof/evaluator increment; existing release holds remain active.

## Comma canonical rank checking and bounded sector reuse

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


## Shared finite-cylinder block integration

**2026-09-27. Objective:** reuse the downloaded Collatz block-selector work
through the existing production scheduler for Collatz and Antihydra, with
Mahler consuming Antihydra's admitted support. This increment does not close
arbitrary-source pumping or all-time safety.

### Changes and independent review

- Two independent explorers audited the downloaded implementation and the live
  shared constructor. The downloaded ordinary CLI route bypasses scheduler
  publication and uses unregistered run/table storage. Its zero fallback count
  is not an instrumented proof of ownership. Its root-semifield consumer is
  outside that constructor, and its run grammar is discarded after summary.
- Ported the useful finite-cylinder arithmetic into
  `dyadic_return_transport.py`, `dyadic_return_images.py` and
  `dyadic_return_composite.py`; no new scheduler or source owner. Cold atoms
  classify at most four branches. Chronological composition builds eight-bit
  effects; bounded leaves and the existing balanced outer constructor reuse
  them. The complete effect preserves affine transfer, branch word, odd count,
  signed delta and minimum prefix.
- The existing ledger-owned macro store holds at most 256 effects. Keys include
  owner, full law descriptor, width and residue. Construction transactions
  share the memo across bounded cycle discovery and the balanced tail; finally
  cleanup releases all entries. Direct helpers also clean up. Optional cache
  reservation failure does not defeat a valid stricter-budget computation.
- A separate final explorer found no production blocker in authority, law
  binding, safety composition or normal/failure cleanup. The memo is strictly
  construction-private; it is not an externally authenticated source store.
- Schema eight adds shared `finite_block_*` counters for cold work and cache
  activity. Metrics do not evaluate a new observer. These hits are distinct
  from action, occurrence and outer balanced-effect reuse.

### Established mathematics and assertion mapping

`arithmetic_leaf_same_cylinder` proves complete finite-effect equality on one
low source cylinder. `arithmetic_leaf_block_compose` proves composition with
the right block using the transported left image. Both are audited for theorem
oracles and reuse the existing branch-law semantics. See the
[production refinement map](../../../docs/proofs/balanced-dyadic-refinement.md).
They do not prove Python cache authority, arbitrary-source grammar closure,
root-semifield successor congruence or global safety.

The high-entropy Collatz test formerly required exactly 4,096 cold scalar
classifications. Its replacement requires strictly fewer classifications,
matching the new cold-work counter, measured finite-cache hits and consistent
lookup totals. Its scheduler, composition/operand ceilings, single saturated
root and empty-stack assertions are preserved. No positive construction gate
was removed or converted to a refusal test.

New tests independently enumerate every residue at widths one through eight
for both family laws, including large high-fiber lifts and signed prefix
minima. Additional tests cover repeated blocks, foreign/law/disposed authority,
failed publication, cap saturation, eviction and exact reservation cleanup.

### Patch provenance and bounded measurements

| Input | SHA-256 | Disposition |
| --- | --- | --- |
| `number-compiler-main3-collatz-production-cli-block-quotient.zip` | `7357eb5b9f6e991255203b99cdeb6fe3b42da6496b3d0742e2db738aef67c07a` | Local reference only; alternate executor not imported |
| `collatz_compiler3_production_cli_block_quotient.patch` | `aa93637d0902f7e6f9ad64ebc051bb9ce99c24fb3e5cb5d35e5d839f9af98055` | Finite-block idea selectively integrated into shared owner |

Five-trial medians below call the actual CLI parser/executor in a warm Python
interpreter, clearing the process cache before each query. They include JSON
value and metrics output, exclude interpreter startup, and are finite timing
observations, not asymptotic or paired-baseline release closure.

| Query | Before ms | After ms |
| --- | ---: | ---: |
| Collatz seed `931386509544713451`, 256 physical ticks | 2.495 | 2.490 |
| Same seed, 1,000 ticks | 3.805 | 3.674 |
| Deterministic 4,096-bit source, 4,096 ticks | 12.017 | 8.176 |
| Collatz seed 27, 10,000 ticks | 2.204 | 2.145 |
| Antihydra source 8, 256 returns | 3.022 | 2.715 |
| Antihydra source 8, 1,024 returns | 6.618 | 4.925 |

Before fingerprint: `a8cf618a84a53929fc7cef687bee86bb662a40c2ff648cd65d525781857bd23b`.
After timing fingerprint: `d423e508d613601928f32c67f19c3bc56b7010aa2f589cb3813675f7644d5ac1`.
Later changes add tests and metric assertions, plus formatting; production
arithmetic is unchanged. An initial implementation regressed the 1,000-tick
query to 5.073 ms by clearing the cache between bounded discovery chunks; the
transaction-wide lifetime fixes that regression. All compared values agree.

Raw evidence is local under `results/current/collatz-block-quotient-2026-09-27/`;
the downloaded reference is outside the checkout and timing scripts remain local artifacts. The
canonical growth tool is `devtools.benchmarks.collatz_temporal_power_probe`.
With `--balanced-scaling --trials 5`, all seven horizons 16–1,024 passed in
cold/repeat/bypass modes for Collatz, Antihydra and Antihydra `--mahler`: 315
samples, independent literal references and full accounting audits. Each job
used 35 seconds/1 GiB. Work, rendering, reporting and full audit are separate.
At the 1,024-step cold sample, Collatz records 64 cold branch classifications
and 216 finite-block hits; Antihydra/Mahler records 64 and 209 respectively.
Transport, larger compositions and observer work are still charged separately:
these counts do not mean the complete query costs 64 operations.
These samples use public queries in a warm interpreter; installed-process
checks are recorded separately.

At `e8736ec57e5e9942257a91f4531c04c2cdb75f4109ba518d861145252c744328`:

- Focused tests: 843 PASS, three existing reverse/add construction failures;
  47 validation-marked tests deselected by the standard unit selection.
- Explicit relevant validation: 40 PASS, one missing source-seven non-halting
  certificate failure, two non-validation tests deselected.
- `Balanced_Dyadic_Integration` and its dependencies: PASS, 33.214 seconds,
  sampled peak 1,264,962,992 bytes within 60 seconds/4 GiB. The shared session
  had separately passed in 29.986 seconds. These are incremental builds.
- Strict mypy and Ruff passed; formatting found one test-only layout issue,
  subsequently corrected. Policy, docs and proof inventory passed.

The four focused failures remain active. Their exact cases are
`test_query_eviction_does_not_replay_bounded_primitive_kernel[<lambda>-3]`,
`test_public_point_never_creates_lowering_capability[reverse]`,
`test_certified_powered_observation_poison_generic_state_codec[<lambda>-0-8]`,
and `test_source7_has_installed_cli_nonhalting_certificate`.

Remaining obligations: general cold source discovery, authenticated parametric
pumping/right-congruence, complete Python publication/cost refinement, and the
existing reverse, special-number, comma and source-global safety gates.

Final validation fingerprint (test-formatting repair only):
`f20f067bc79f4a3aff7480f483fdd7614b594da6d541ebd49782b3e3dcc83c04`.
The clean staged wheel build and isolated installation passed in 25.627 seconds
with sampled peak 127,027,792 bytes; this includes separate CLI processes and
Mahler composed-image verification, not a cold-process speedup comparison.
The explicit unchanged P0 selection has 13 PASS / 50 FAIL; exact failure IDs
match the prior balanced-refinement baseline.

The first full-unit attempt hit the 1-GiB guard at 176.012 seconds, without a
complete JUnit result. Collection-order alignment puts its last output at the
repository call-graph policy check. The downloaded reference had been extracted
under `results/`; that checker traverses the directory despite Git ignoring it,
so it was parsing a second codebase. The reference was moved outside the
checkout without changing the checker, assertions or resource limit; the full
suite was rerun. The failed attempt remains local evidence as `full-unit`.

### Local-output tracking repair

The old `.gitignore` re-included every Markdown and Python file anywhere below
`results/`. Replaced those broad exceptions with the policy README and weekly
`results/current/YYYY-Www/README.md` summaries only. Git had one tracked local
benchmark, `point-germ-bench.py`; it was removed from the index while preserving
its existing working copy and edits. No history rewrite, commit, push or upload
was performed. `git ls-files results` now contains only four reviewed documents.
`git check-ignore --no-index` verifies local Markdown, Python and JSON stay
ignored even inside a weekly directory; the policy and next-week summary remain
eligible. Raw run evidence remains local and no longer appears as candidate
source changes because of its extension.

After moving the external reference, the complete standard unit command finished
at the final fingerprint: **6,971 PASS / the same 42 FAIL**, 1,928 validation
cases deselected by the unchanged default. Guard: 290.528 seconds / sampled
peak 832,423,064 bytes under 300 seconds/1 GiB. Exact failing node IDs match
`balanced-proof-refinement/unit-final.xml`; no new unit failure was found.
This successful completion supersedes the incomplete first attempt, without
turning those 42 failures green.

Final strict mypy, Ruff, formatting (1,525 files), policy, documentation,
proof inventory (47 sessions/160 theories) and diff checks all PASS at the
final fingerprint in 11.793 seconds / 638,240,112 sampled bytes. Ignore-rule
verification and the preserved local benchmark were checked separately because
Git tracking policy is outside the authored-source fingerprint.
