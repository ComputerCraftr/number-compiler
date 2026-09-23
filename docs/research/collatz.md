# Collatz physical time, events, and Hensel cylinders

Status: **Finite physical/event laws are checked; general source-discovery and
executable refinement bounds remain open.**

## Reading guide

- **Definitions:** physical iteration applies `T(x)=x/2` for even `x` and `T(x)=3*x+1` for odd `x`; an accelerated event groups a different number of those ticks.
- **Checked theorem:** finite source cylinders, Hensel transport and physical/event refinements use the specified source, precision and action.
- **Implemented construction:** physical terms and event observations consume authenticated source images.
- **Open obligation:** exact finite output does not establish convergence or cheap construction at arbitrary horizons.

## Saturated finite safety and source binding

The finite action combines an exact skew endpoint with a positive-affine
[threshold envelope](../../src/number_compiler/arithmetic/fields/threshold_envelope.py).
For chronological blocks A then B, its threshold is
`max(F_A(T), endpoint_A^-1(F_B(T)))`; source admission intersects A's cylinder
with the pullback of B's cylinder. Empty prefixes have no descent, and equality
at a threshold is not strict descent.

**Implemented:** [saturated_future.py](../../src/number_compiler/sequences/collatz/saturated_future.py)
binds this arithmetic to the Hensel cylinder and event count.
`collatz --events N --info safety` consumes the authenticated event publication
and reports `all_time_claim: false`. The value is not an authority token.

**Finite evidence:** all `6^6` valuation words over 1..6 give 46,625 cylinders
with descent for every natural high fiber, 30 with no descent in the block,
and one with only the origin safe, `(2,2,2,2,2,2)`. This is a branch census,
not coverage of one source's infinite trajectory.

**Open:** binding still performs per-event radix-64 transport. No cheap
source-application bound or complete Python worklist refinement follows from
removing retained history. See the [proof scope](../proofs.md#finite-saturated-threshold-actions).

[Implementation and validation record](../../results/current/2026-W39/README.md#saturated-finite-safety-and-source-binding).

## Shared branch observers and joint experiment

The shared [branch quotient owner](../../src/number_compiler/arithmetic/fields/branch_quotients.py)
provides bounded suffixes, prime possibility partitions and phase laws.
Collatz uses `3/2^q`; Mahler uses `(3/2)^q`. Their source exponents are separately
bound. The 55 and 67 bucket totals sum individual prime partitions; neither
is the size of an exact joint successor alphabet.

A suffix records at most six sibling choices among three admitted branches,
not an unbounded event exponent. The 64-sheet/729-chart experiment found no
repeated full keys among 32,768 positive odd 16-bit Collatz sources. Absence
of conflicts without reuse does not establish closure. See the
[Mahler joint-observer scope](antihydra-mahler.md#joint-future-observer-experiment).

[Implementation and validation record](../../results/current/2026-W39/README.md#shared-branch-observers-and-joint-experiment).

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

<a id="carryf5-directional-integration-2026-09-21"></a>

### Directional carry/F5 quotient

The canonical [carry/F5 owner](../../src/number_compiler/arithmetic/carry/collatz_f5_quotient.py)
derives directional response partitions from `binary_carry_birth` and
`radix64_phi5`. F5 fibers have sizes `(28,16,4,7,9)`; carry/phase has 15 leaf
classes. Left/right response counts for shifts 0–5 are `(15,1)`, `(12,2)`,
`(10,4)`, `(8,8)`, `(4,9)`, `(2,13)`, minimal for that fixed join observation.

Sources 67 and 75 have the same two-cell class word and Hensel gap one but
produce 101 and 113, with different low-cell classes. The directional response
resolves this missing context. This refutes the leaf projection as a successor
identity, not the full cylinder. Production output morphisms consume the
reduced ports lazily; repeated temporal closure remains unproved.

[Implementation and validation record](../../results/current/2026-W39/README.md#carryf5-directional-integration-2026-09-21).

<a id="cross-family-work-and-cache-measurements"></a>

### Cost and reuse boundary

Local F5 operator hits and authenticated temporal-image hits are distinct.
The measured CLI digit path did not consume the new F5 observer, so those
benchmarks cannot attribute a CLI speedup to it. Reverse/add construction
refusals supply no successful-work samples.

[Implementation and validation record](../../results/current/2026-W39/README.md#cross-family-work-and-cache-measurements).

<a id="downloaded-spatial-grammar-patch"></a>

### Spatial observer composition

`CollatzF5SpatialAction` composes carry maps in physical order and sums
leaf F5 phases. That additive phase is not the whole-word binary forcing jet.
The exact spatial language and its length dependence are specified under
[generator macros](#generator-macros-spatial-phase-and-birth-emissions).
A fixed spatial alphabet does not establish reuse of complete future regions.

[Implementation and validation record](../../results/current/2026-W39/README.md#downloaded-spatial-grammar-patch).

## Shared temporal effect reuse

The [dyadic reuse adapter](../../src/number_compiler/hashlife/execution/dyadic_return_reuse.py)
shares complete skew, branch support, weights and minimum prefixes for the
same admitted action/residue/precision, while issuing distinct occurrence
handles. Exact singleton cycle shortcuts retain the high fiber.

`exact_precision_source_lift`, `dyadic_source_orbit_lower_bound` and
`dyadic_high_fiber_excludes_small_states` justify branch transport and the
stated cycle-exclusion condition for nonnegative offsets. They do not refine
the Python cache or construct a quotient across different residue clauses.
Aligned-source reuse and unmatched-source discovery have different costs.

[Implementation and validation record](../../results/current/2026-W39/README.md#shared-temporal-effect-reuse).

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

**Construction boundary:** cold work remains proportional to unmatched source
extent. The bounded comparison regressed latency; generator reuse alone is
not a successful performance gate.

[Dated evidence](../../results/current/2026-W39/README.md#source-only-macro-construction-measurements).

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

<a id="updated-saturated-publication-patch"></a>

## Authenticated aggregate publication

The authenticated `DyadicAggregateSummary` exposes affine action, extent,
aggregate clock, minimum prefix and cycle metadata. Scheduler-owned support
remains available for first-failure descent; every demand revalidates authority.
Its current finite safety consumer is described [above](#saturated-finite-safety-and-source-binding).

Arithmetic consistency of a supplied action/cylinder pair is insufficient
admission. The downloaded scalar-leaf constructor and unchecked summary cache
were not accepted as replacements for the source-bound scheduler.

[Implementation and validation record](../../results/current/2026-W39/README.md#updated-saturated-publication-patch).

## Shared safety transformers and exact cycle acceleration

- **Implemented construction:** `PrefixSafety(delta, minimum)` in
  [consumer_pullback.py](../../src/number_compiler/arithmetic/fields/consumer_pullback.py)
  composes as `(d+e, min(m,d+n))`. For `k>0`, repetition is
  `(k*d, m+min(0,(k-1)*d))`. Both the shared dyadic cycle executor and
  Antihydra block composition consume this same implementation.
- **Guarded demand:** negative-drift cycles retain their exact minimum.
  First-failure descent computes the first potentially unsafe repetition,
  then inspects at most one cycle. Total arithmetic may continue beyond a
  ledger failure; a physical safety predicate may not.
- **Public CLI:** exact entry into the validated `1,4,2` cycle allows Collatz
  to skip arbitrarily many repetitions. Admission still checks the exact
  source and law. Sources with the same low residue cannot borrow this
  singleton result. This shortcut existed before this change; the shared
  safety transformer now handles both signs of ledger drift.
- **Reduced work:** low-residue transport uses a short exact numerator directly
  when its bit bound fits the demanded modulus. A trillion-bit requested
  precision no longer forces construction of that modulus for a tiny
  numerator. Wide and signed numerators retain the modular path.
- **Finite algebra:** [threshold_envelope.py](../../src/number_compiler/arithmetic/fields/threshold_envelope.py)
  normalizes exact upper hulls of positive affine inverse-threshold maps and
  composes `max(F_A, P_A(F_B))`. Its domain is all real thresholds. The
  rational inverse is shared with Mahler's production saturating action;
  a single saturated action uses the inverse directly without rebuilding a
  hull. Empty envelopes have no event and zero-slope singleton summaries
  cannot be inverted as cylinders. This utility is not a source constructor.
- **Checked theorem:** `inverse_affine_max`, `prefix_safety_chronological`
  and `repeated_prefix_minimum_closed` in
  [Associated_Action_Pullback.thy](../../devtools/proofs/isabelle/integration/Associated_Action_Pullback.thy)
  establish inverse/max transport, chronological safety and the repetition
  formula by induction. The same theory passes an isolated HOL-based build
  with its oracle audit. The full integration build remains blocked by the
  35-second parent-session rebuild. These algebraic statements do not prove
  the Python hull algorithm, source admission or first-failure worklist.
- **Open scope:** neither finite threshold reduction nor exact cycle skipping
  proves that every Collatz source reaches a cycle, or supplies a general
  sublinear cold source-discovery bound. Generic reverse D4+ and global
  Mahler/Antihydra safety remain independent obligations.

Reproduce the public path, exact admission, negative drift and short-operand
regressions:

```console
python -m pytest -q tests/api/test_shared_skew_cli.py tests/resources/test_dyadic_return_audit.py tests/hashlife/execution/test_dyadic_effect_reuse.py tests/arithmetic/fields/test_threshold_envelope.py
python -m number_compiler collatz --seed 27 --nth 1000000000000
```

The final command emits `4`. It does not request optional observers.

Cycle-specific measurements confirm bounded primitive discovery after exact
cycle entry, with logarithmic scheduler overhead. They are not a general
source-discovery bound or the complete release growth manifest.

[Dated evidence](../../results/current/2026-W39/README.md#exact-cycle-acceleration-measurements).
