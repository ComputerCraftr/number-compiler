# Collatz physical time, events, and Hensel cylinders

Status: **finite physical/event refinements and source lifts are checked; the
remaining compact publication and growth gates are not implied by them**.

The CLI's `--nth` counts ordinary Collatz iterations. Accelerated events are a
separate coordinate. A valid cylinder therefore records both physical tick
count and event count rather than identifying them.

## Reading guide

- **Definitions:** physical iteration applies `T(x)=x/2` for even `x` and `T(x)=3*x+1` for odd `x`; an accelerated event groups a different number of those ticks.
- **Checked theorem:** finite source cylinders, Hensel transport and physical/event refinements use the specified source, precision and action.
- **Implemented construction:** physical terms and event observations consume authenticated source images.
- **Open obligation:** exact finite output does not establish convergence or cheap construction at arbitrary horizons.

## Exact source and clock laws

[`Collatz_Cylinder_Constructor.thy`](../../devtools/proofs/isabelle/temporal_collatz/Collatz_Cylinder_Constructor.thy)
proves exact dyadic source splitting, block composition, physical-tick
composition, and embedding of events in physical time. The constructor
evaluation theorem applies to the defined finite cylinder; the explicit
`phase_neutrality_does_not_fix_cylinder_action` lemma records why phase alone is
not a quotient.

[`Collatz_Physical_Cylinder_Lift.thy`](../../devtools/proofs/isabelle/temporal_collatz/Collatz_Physical_Cylinder_Lift.thy)
proves branch words are dyadic source words and gives exact-precision affine and
low-residue lifts. Its selector split and affine-leaf division assume the
admitted branch/source construction.

[`Collatz_Clock_Jumps.thy`](../../devtools/proofs/isabelle/temporal_collatz/Collatz_Clock_Jumps.thy)
proves block composition, inverse-three conjugacy, Hensel prefix skips, mismatch
death, one-hot radix-64 curvature, and normalized jet composition. A matching
prefix permits the stated skip; a mismatch kills that forcing branch. Neither
claim proves all future branches absent.

The physical bound consumer in
[`Physical_Collatz_Bound_Consumer.thy`](../../devtools/proofs/isabelle/etale/Physical_Collatz_Bound_Consumer.thy)
assigns odd-event ownership to the low boundary under its finite state cases and
proves the compiled publisher/pullback refines that emission. The support theory
[`Physical_Collatz_Support.thy`](../../devtools/proofs/isabelle/etale/Physical_Collatz_Support.thy)
exhibits sources with equal normalization but different offsets, proving that
endpoint and weight do not determine support.

## Production and resource boundary

### Carry/F5 directional integration (2026-09-21)

- **Canonical projection:**
  [collatz_binary_forcing.py](../../src/number_compiler/arithmetic/carry/collatz_binary_forcing.py)
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
  [collatz_f5_quotient.py](../../src/number_compiler/arithmetic/carry/collatz_f5_quotient.py)
  partitions rows and columns of the exact join observation. Left/right class
  counts for shifts 0–5 are `(15,1)`, `(12,2)`, `(10,4)`, `(8,8)`, `(4,9)` and
  `(2,13)`. Distinct rows/columns supply distinguishing contexts, proving
  minimality among independent one-sided response partitions for this fixed
  consumer. This does not prove closure under repeated temporal application.
- **HashLife arithmetic consumer:**
  [CollatzOutputMorphism](../../src/number_compiler/sequences/collatz/output_morphism.py)
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

### Cross-family work and cache measurements

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

### Downloaded spatial-grammar patch

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
[radix5_future_grammar.py](../../devtools/experiments/collatz/radix5_future_grammar.py)
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

## Shared temporal effect reuse

The production [dyadic scheduler adapter](../../src/number_compiler/hashlife/execution/dyadic_return_images.py)
now uses [admitted-cylinder reuse](../../src/number_compiler/hashlife/execution/dyadic_return_reuse.py).
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

## Five-multiplication primary-jet reduction

- **Implemented algebra:**
  [PrimaryJetAffineMorphism.binary_event](../../src/number_compiler/arithmetic/polynomials/primary_jet.py)
  is the single owner of `J ↦ z^(-e)(yJ+B)`, modulo `y^5` and the coefficient
  modulus. The research port and probe now use this owner. A right action
  with zero kernel discards the earlier kernel and offset before multiplying;
  it keeps the chronological step extent and validates compatible rings.
- **Checked theorem:** `last_five_births_erase_earlier_jet` in
  [Collatz_Harmonic_Ports](../../devtools/proofs/isabelle/Collatz_Harmonic_Ports.thy)
  derives suffix reduction from the existing same-birth source-independence
  theorem. The last five births are supplied, potentially source-dependent.
  They are not computed by the nilpotence theorem.
- **Finite census:** all 32,768 positive odd 16-bit sources reproduce inherited
  kernel class counts 16, 18, 2 at D1/D2/D4, and the single zero kernel at
  D8/D16/D32/D64. Tests separately check exact chronological composition and
  show different new births retain different offsets after source death.
- **Antihydra/Mahler scope:** bounded admitted Antihydra centered macros agree
  with the same kernel, with `e=1` and incoming bit `D mod 2`. Its accelerated
  centered odd event of gap `a` contains **a** multiplications by three;
  ordinary Collatz's accelerated odd event contains one. Physical even
  Collatz divisions contain none. The finite primary jet is not Mahler's
  ordered affine safety predicate, the Antihydra ledger, or its halting guard.
- **Open integration:** neither the inherited kernel nor the additive F5
  spatial phase supplies the future birth grammar. The canonical source
  occurrence still owns its exact endpoint and branch admission. This change
  does not claim fewer source-discovery steps for unmatched CLI cylinders.

Reproduce the finite census and cross-family transport checks:

```console
python -m pytest -q -o addopts='' tests/sequences/collatz/test_harmonic_ports.py tests/arithmetic/polynomials/test_primary_jet.py tests/validation/proofs/test_mahler_f5_production_bridge.py
isabelle build -d devtools/proofs/isabelle -j 1 -o threads=1 -o parallel_proofs=0 Reverse_Residuals
```

## Generator macros, spatial phase and birth emissions

The corrected September 22 generator report separates reusable operations from
occurrence emissions. The independent local census reproduces 15 leaf rules,
33 complete three-input primary birth responses, 55 individual jets, and 9
leaf rules with multiple responses (maximum five). Births remain outside the
`CollatzF5SpatialAction` identity. An exact current occurrence is still needed
to select those emissions.

**Implemented spatial macros.** The canonical
[carry/F5 owner](../../src/number_compiler/arithmetic/carry/collatz_f5_quotient.py)
now answers exact-length alphabet queries without the research tool's repeated
Cartesian-product language powers. Length one has 15 effects. Every length
at least two has 17 effects, but their identities depend on length modulo five:
the nonconstant lower boundary action has that phase. Radix-5 regions of
lengths 5, 25, 125, ... use the same phase-zero 17-action alphabet. Across all
length phases the union has 21 actions. Equal cardinality alone does not
justify substituting one length alphabet for another.

The existing finite-observer minimizer checks the complete two-sided spatial
macro graph. Its 17 states are already minimal when both the carry response
and additive phase are observable. This is not minimization of recursive
current occurrences under a temporal Collatz successor.

`repeat(n)` exploits idempotence of the five carry actions and returns phase
`n*phase mod 5`, without composing once per represented block or constructing
a binary power worklist. Positive count is required; the empty interval uses
its separate identity. Tests compare literal and binary repetition, poison
composition on huge counts, and reuse this law in the bounded Antihydra/Mahler
spatial bridge. Integer input size is still real work. The rule cannot repeat
source-dependent emissions or skip temporal source discovery.

**Proof owner.** `carry_then` and `carry_then_apply` now live once in
[Reverse_Residuals](../../devtools/proofs/isabelle/Reverse_Residuals.thy), imported
by the reverse/add and Collatz branches. The Collatz harmonic theory proves
nonempty-generator idempotence, spatial length-phase transport, cardinality 17,
phase-zero closure, and the exact repetition formula. These are spatial laws;
source occurrence admission, Hensel gap selection and Mahler's ordered guard
remain separate consumers.

Reproduce the finite closure, minimality, census and shared-consumer checks:

```console
python -m pytest -q -o addopts='' tests/sequences/collatz/test_f5_directional_quotient.py tests/validation/research/collatz/test_radix5_future_grammar.py tests/validation/proofs/test_mahler_f5_production_bridge.py
```

## Counterexample scope

Equal endpoint/weight examples refute that compressed key only. They do not
refute a cylinder carrying support offsets. Event-clock and ordinary-time
comparisons must use the same counting convention. Bounded orbit comparisons
validate implementation but do not establish the Collatz conjecture.

## Source-only dyadic macro construction

The shared production
[dyadic return constructor](../../src/number_compiler/hashlife/execution/dyadic_return_transport.py)
now builds bounded macros with an explicit postorder arithmetic stack. A
width-one cylinder selects a pinned generator; each larger macro transports
the left cylinder through its skew transfer to obtain the right source residue.
Composition preserves the affine return, ordered branch word, odd count,
ledger delta and minimum prefix. Collatz physical queries and Antihydra
arithmetic queries use this same owner. Mahler observes the admitted Antihydra
support and retains its separate safety predicate.

- D4 memo keys contain the complete low source residue and precision, under a
  validated law. They are not F5/carry projection keys.
- Memo and stack reservations are ledger-owned and transaction-local; success
  and failure clear them. Larger intermediate trees are discarded after
  normalization, preserving the existing retained-support budget.
- Bounded adversarial tests disable scalar endpoint access, compare D4/D8/D16
  across 256 low residues and large high fibers, and verify right-half
  transport, branch labels, first-failure minima and cleanup.
- `source_macro_correct` in `Dyadic_Source_Lift` proves finite dyadic endpoint,
  gain and label-word semantics for the recursive arithmetic construction.
  Python worklist publication, memo lifecycle and costs still require their
  own refinement; the theorem does not assert a finite future quotient.

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

## Production and reproduction

- **Implemented owner:** [sequences/collatz/physical_images.py](../../src/number_compiler/sequences/collatz/physical_images.py).
- **Checked theorem:** the named Isabelle results above apply with their explicit premises; use the [proof index](../proofs.md) for source statements, sessions and oracle audits.
- **Finite experiment:** bounded test comparisons establish only the tested sources and horizons.
- **Construction-cost status:** Admitted cycle compression bounds repeated-cycle work. General source discovery, event projections and output-sensitive rendering have separate costs.

Run the exact executable checks (including validation-marked assertions):

```console
python -m pytest -o addopts='' tests/hashlife/execution/test_collatz_tile_cycle.py tests/projection/test_collatz_binary_radix_limbs.py
```

## Joint-adic endpoint projection and source admission

The September 22 reports distinguish a fixed six-step centered `3/2` block
from six accelerated odd Collatz events. In the first case the source stride
is 64 and target gain is 729. In the second, total division exponent `E`
varies with the source; the odd-source cylinder has stride `2^(E+1)` and
its target stride is 1458. Source 1 has `E=12` after six accelerated events.
Confusing these clocks changes the source cylinder.

- **Implemented arithmetic:** `integer_dyadic_fiber_action` in
  [skew_transfer.py](../../src/number_compiler/arithmetic/fields/skew_transfer.py)
  derives the exact integer action on the high fiber from an integral skew,
  canonical residue and precision. It checks origin and stride divisibility.
- **Production consumer:** the shared dyadic endpoint observer now evaluates
  that action against the retained source fiber. Both Collatz and Antihydra
  use it. This consumer neither reconstructs the full input nor reads a branch
  itinerary. Construction still discovers source branches and retains bounded
  support leaves for consumers that need them.
- **Checked mathematical scope:** `shared_integer_fiber_rebase` gives the
  integral rechart equation. `source_macro_projection_correct` proves the
  executable endpoint/gain projection without constructing a label list.
  These are arithmetic/finite-recursion theorems, not a proof of the Python
  admission seals, scheduler or a cheap source constructor.
- **Adversarial patch finding:** the supplied joint-adic patch can admit the
  claimed six-event target 729 on source cylinder `(residue=1, precision=7)`.
  The skew `(729,45927,64)` satisfies its affine checks, but the actual six-event
  target of 1 is 1. Arithmetic consistency therefore cannot replace source
  admission. Its recursive constructor also invokes the scalar six-event
  constructor for every block. That code was not installed as a production
  shortcut.
- **Open obligation:** the fixed parity alphabet and finite observation classes
  do not construct the source-selected future. Arbitrary depth-k binary words
  still have `2^k` possibilities; modular forgetting does not bound the retained
  Archimedean high fiber or establish convergence.

Independent regression checks are in
[test_integer_cylinder_chart.py](../../tests/arithmetic/fields/test_integer_cylinder_chart.py).
They include variable clocks, forged skews, a singleton cycle with enormous
precision, and poisoned input reconstruction/history readers. The supplied
`collatz_joint_adic_quotient_report.md`, `collatz_future_grammar_closure_report.md`
and patch remain external research inputs; their experiment claims are not
current-source release evidence.
