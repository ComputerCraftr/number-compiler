# Collatz Hensel cylinders and live suffix occurrences

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

September 10, 2026. This checkpoint implements the finite forcing quotient and
the bounded exact occurrence carrier. It does not establish a bounded or
polylogarithmic collection of live slabs for arbitrary powered Collatz blocks,
and does not admit a new production temporal-cache identity.

## Implemented semantics

`HenselCylinder(q,r)` retains exactly the residue class modulo `2^q`.
`from_root(q,h,c)` computes `r=-c*3^(-h) mod 2^q` using the finite unit clock;
neither the raw clock nor the constant survives in cylinder identity. The
existing `RationalPadicRootGerm.root_residue` delegates to this owner, preserving
its established precision limits. Matching input consumes six live bits;
mismatch emits the exact local valuation and kills the atom. Exhausting finite
precision does not invent a complete valuation. The `j=0` dyadic-clock exception
is tested explicitly.

`CollatzHenselOccurrenceCarrier` shares `CollatzHenselAction(a,h,b)` while keeping
the canonical radix-4 suffix and logical occurrence time. Its successor calls
the existing affine suffix/root/angular owners, preserving the raw action even
when the surviving suffix is zero. It keeps `a` in `{1,2}` and increments `h`.
Direct second imaging uses the shared frame normalizer and one root-boundary
query, without constructing a first-successor word. The duplicated boundary
query discovered during implementation was removed.

The 129/385 witness is retained explicitly: second images share `36M+1` with
`M=2,6`; two further successors share `162M+83` with `M=0,1`. Their common root
cylinder is `C(6,49)`, and the next valuations are 1 and 5, yielding 125 and 23.
The old scalar ActionID counterexamples remain valid; they cannot identify
whole occurrences.

`HenselSlabArena` canonicalizes labelled cylinder unions by subsumption and
sibling reduction, with the shared decision arena owning DAG reduction. Its
affine pullback includes integrality, even for precision zero. Composition
unions the first slab with the pulled-back second slab, composes transport, and
retains the intersection of the two exact branch domains. `domain=None` is
empty, not universal. Labels denote idempotent set-valued observations, not an
ordered itinerary. Transport and branch admissibility cannot be discarded.

The new sparse prefix constructor avoids converting prefixes into full-width
Cartesian boxes. A regression compares its exact canonical root with the
generic builder, including reordered variables, overlapping prefixes, and
subsumption in either insertion order.

Temporal composition also normalizes the union before interning the pulled
forcing. The fixed-branch control previously retained 1,091 DAG nodes and 11
slab IDs for an eight-node result. Fusing pullback with union reduces those
counts to eight nodes and one ID. A poison regression prevents reintroducing
the temporary-slab constructor.

## Validation scope

- All 32,768 odd 16-bit seeds: direct `U^2` image plus eight further successors;
  262,144 additional symbolic valuations and targets agree with the independent
  accelerated Collatz oracle.
- 1,048,576 input/block/target pullback comparisons cover all 16-bit inputs,
  including nonintegral branches and precision-zero targets.
- At six-bit precision, 1,024 clock/constant representatives project to 64
  cylinders, with every fiber of size 16. Existing carry-domain fibers remain
  `21/1/20/1/21`. Different raw representatives at precisions 6,12,18,24,30
  have identical consumption results for all 64 input symbols.
- All six root phases settle after at most one radix-64 digit. One through four
  matching root digits drop 3,6,9,12 radix-4 quarters, preserving the normalized
  root, live suffix, and angular action; dropped depth remains valuation weight.
- The 95/104 reverse-add control drops 12 of 20 rows to the same eight-row live
  itinerary and remains identical for twelve subsequent advances.
- Direct second imaging poisons primitive successor and frame-factorization
  APIs. Block squaring poisons primitive construction, concrete affine
  evaluation, slab evaluation, and the existing occurrence successor.

The occurrence implementation retains existing bounds (`h <= 40`, bounded
root constants and coefficients); exhaustive testing is not an unbounded
Isabelle proof of that Python implementation. The new arenas remain guarded
endpoint/research machinery with explicit resource limits.

## Powered controls and negative control

The fixed valuation-one Collatz branch and the modular unit-clock control
reach 1,024 composed events with one primitive construction and ten squarings.
The fixed branch retains one forcing atom and eight reachable DAG nodes, but
its exact admitted cylinder has 1,025 bits. Its transport also grows. Counting
only forcing nodes would conceal these costs.

The dyadic halving stress is an affine-algebra control, not an accelerated odd
Collatz itinerary. Its forcing union is `v2(x)<N`, with exactly `N` maximal
cylinders. The original generic-box conversion reached 128 events in 24.38
seconds and timed out at the unchanged 35-second guard while doubling to 256.
Direct prefix construction reaches 512 in approximately 0.24 seconds (0.14
seconds after fusing temporal union); doubling
to 1,024 fails explicitly at the unchanged normalization work budget. This is
evidence of removed construction overhead and of linear forcing growth in this
control, not a general asymptotic speedup.

## Proof and evidence

`devtools/proofs/isabelle/Hensel_Cylinders.thy` proves cylinder congruence,
precision-zero integrality, sibling union, affine pullback distribution, and
exact affine composition retaining midpoint integrality. The single-cylinder
pullback theorem states its inverse/cancellation hypothesis explicitly. It does
not prove modular inverse existence or the entire Python occurrence algorithm.
The exact shifted-tail law and its matching-digit corollary also pass: consuming
`d=r mod 64` changes the surviving cylinder to `C(q-6,r div 64)`. The full
installed Isabelle2025-2 session passes with no theorem oracle dependencies
(`isabelle-eighth.log`, 10.42 seconds including the guard).

The guard logs retain failed proof attempts, the original construction timeout,
and the corrected probes. No failed attempt is counted as a passing gate.
Frozen authored-source fingerprint:
`8bc754a8b1cae75b88edef1c5ced6d5fd7d46db2a27eeec9eb407855a3f42ec8`.

Final serial checks:

- `unit-fused-final`: **4,312 passed, 994 validation tests deselected**, 281.46
  pytest seconds; guard 282.39 seconds, sampled peak 606,192,528 bytes. The
  existing 300-second / 1-GiB guard was unchanged. JUnit classifies this as
  `serial-unit`; both source fingerprints match the frozen source.
- `validation-fused-final`: **24 passed**, 13.73 pytest seconds, covering the
  complete new occurrence and cylinder-pullback enumerations. Both JUnit source
  fingerprints match. This is selected validation, not the full validation
  partition or an unfiltered release run.
- Strict nonincremental mypy, repository-wide Ruff, and formatting of all 15
  changed Python files pass. Repository structural policy is included in the
  passing ordinary suite. The full Isabelle session passes as described above.

The earlier ordinary checkpoint took 290.97 seconds; this single run at 281.46
seconds does not establish a sustained unit-suite speedup. The measured
construction improvements above are specific to the slab probes.

The earlier `unit-final` invocation was deliberately stopped after about 59
seconds to remove the temporary-slab retention; its terminated result is not a
unit-suite failure or a passing run. The subsequent fused-source evidence is
the release-check reference.

| Control | Events | Atoms | Reachable / retained DAG nodes | Slab IDs | Admitted precision | Primitive constructions |
|---|---:|---:|---:|---:|---:|---:|
| Fixed valuation-one branch | 1,024 | 1 | 8 / 8 | 1 | 1,025 | 1 |
| Modular unit clock | 1,024 | 2 | 4 / 32 | 5 | 0 | 1 |
| Halving stress | 512 | 512 | 514 / 1,025 | 10 | 512 | 1 |

Rows come from the `*-fused.log` probes. The fixed branch's offset occupies
1,624 bits; the table's forcing counts are not a total storage bound.

## Entry points

The implementation owners are:

- `src/number_compiler/sequences/collatz/hensel_cylinders.py`: finite projection,
  consumption, and affine cylinder pullback.
- `src/number_compiler/sequences/collatz/hensel_occurrence.py`: shared action plus
  live suffix, direct second imaging, and exact bounded successor.
- `src/number_compiler/sequences/collatz/hensel_slabs.py`: labelled forcing
  functions and composition of caller-admitted affine branches.
- `src/number_compiler/arithmetic/functions/decision.py`: canonical sparse
  prefix-DAG construction, shared with the general decision arena.

Use these research entry points under the existing `exact_oracle()` context.
For example, `carrier.image_second(129)` yields action `36M+1`, suffix `M=2`,
and value 73; `carrier.next_step(occurrence)` yields the next accelerated step.
The successor operates on the suffix germ; `.value` is an explicitly bounded
endpoint observation for checking or exporting the result.

A slab block is a known affine branch, not a branch-discovery algorithm.
`arena.compose(before, after)` pulls back the second branch's admission as well
as its forcing. `arena.evaluate(slab, x)` observes the unbound forcing function;
using it as a block observation also requires checking the block's domain.
Two equal forcing slabs therefore do not imply equal full temporal actions.
