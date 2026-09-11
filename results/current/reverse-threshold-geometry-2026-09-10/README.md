# Reverse/add threshold geometry experiment

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

The proposed direction removes the previous A8 construction failure in a
bounded research implementation. A source-independent capacity-seven action
reaches A8 with **3,088 retained expression nodes**, and a capacity-nine action
reaches A16 with **9,007**, under a 30,000-node cap. Both are checked on seed
196 after construction. Primitive successor construction, point evaluation,
and general Boolean substitution are poisoned during every squaring.

This does **not** complete the successor-closed nonlinear quotient. The new
IDs reduce arithmetic expressions and spatial geometry, but do not decide
full extensional equality of arbitrary contextual expressions. Unresolved
threshold consumers still grow linearly in these probes. The capacity-sixteen
action reaches A16 and fails while constructing A32 at 30,000 nodes. The code
therefore remains in `devtools/proofs`; no production route or cache admission
has changed.

## What was implemented

`threshold_expressions.py` retains modular affine arithmetic and local finite
consumers as a shared expression DAG. Same-modulus affine terms flatten and
cancel, unary consumer tables compose exactly, equal selection branches merge,
and sound finite range bounds eliminate constant outputs. Temporal substitution
rewrites all output and admission expressions simultaneously. It does not
insert opaque calls to a primitive or defer a loop over primitive successors.

`reverse_threshold_geometry.py` constructs recursive spatial cells. Before
subdivision, summed lower/upper bounds can prove an entire interval LT, EQ, or
GT. Only unresolved cells split; local decimal sums use the existing scalar
carry-domain law. Identical resulting expression words share the existing
canonical-word representation. A `10^100`-position test merges different value
expressions into one LT cell with the comparator constructor poisoned.

`reverse_geometry_context.py` retains separate domain, F5, and parity input
coordinates, aliases symmetric positions, and preserves width, padding,
odd-center parity, and capacity-overflow predicates. No reconstructed 19-symbol
source field is stored. A local CRT decimal residue is only a bounded operand
of the threshold consumer. Growth uses reflection of the extended normalized
digit word; it retains the reflected carry and the new edge digit one.

The action's `ThresholdGeometryID` is not the whole action. Exact value
expressions and admission remain necessary for future consumers. In particular,
structural equality of this IR is a sufficient equality proof, not the complete
contextual syntactic quotient requested for production.

## Harmonic result reproduced, with its scope retained

The independent harmonic probe advances the exact oracle through 1,024 events.
It compares sequential accumulation against a balanced composition of the same
chronological event blocks using the existing symmetry-innovation owner. Every
dyadic checkpoint agrees, and the harmonic projection remains 18 bits:

| Events | Growths | `(parity,r0,r1,q0,slope)` |
|---:|---:|---|
| 1 | 0 | `(1,10,1,0,0)` |
| 4 | 2 | `(1,16,11,8,0)` |
| 8 | 4 | `(1,6,4,2,2)` |
| 64 | 28 | `(1,0,9,5,1)` |
| 256 | 110 | `(1,8,9,1,7)` |
| 1,024 | 418 | `(1,16,14,3,6)` |

These reproduce the supplied results. Composition of two already-known
chronological halves does not supply the unknown forcing of a second future
half. The harmonic probe reports all 1,024 oracle primitive successors.

The hidden kernel cannot be dropped when asking pointwise threshold questions.
The valid symmetric pair fields `8^9` and `(9,10,10,10,10,10,10,10,9)` have the
same low harmonic germ but different threshold geometry and successors. Their
difference is the coefficient field of `P8(x)*x*(x-2)`. This regression uses the
existing projection owner to check equality, rather than assuming a harmonic
reconstruction formula.

Consequently the experiment retains exact arithmetic residuals. It does not
replace pointwise forcing by the five harmonic coordinates or claim to have
isolated a complete hidden-P8 quotient. The harmonic summary remains an
independent compositional control, not a lossy operand of `ThresholdNF`.

## Powering measurements and remaining costs

With capacity nine held fixed:

| Power | Width for 196 | Retained expression nodes | All unresolved unary consumers | Primitive constructions |
|---:|---:|---:|---:|---:|
| 1 | 3 | 599 | 119 | 1 |
| 2 | 4 | 1,161 | 234 | 1 |
| 4 | 5 | 2,283 | 464 | 1 |
| 8 | 7 | 4,525 | 924 | 1 |
| 16 | 9 | 9,007 | 1,844 | 1 |

Unary consumers include threshold, CRT, carry, and extent queries. The probe
also reports decimal-threshold consumers separately, retained argument edges,
table entries, range atoms, and the actual expression/table evaluations needed
for indexed observation. The counter `primitive_successors=1` does not erase
that evaluation work. The expression graph retains linearly many unresolved
generation-dependent queries even though no primitive routine is replayed.

The old and new 30,000-node limits count different node representations. These
results demonstrate avoidance of Boolean truth-function expansion; they are
not a matched per-node memory benchmark or a production compiler speedup.

Larger capacity attempts use the exact widths needed by the 196 endpoints:

| Requested horizon | Capacity | Last completed power | Failure while building |
|---:|---:|---:|---:|
| 32 | 16 | 16 | A32 |
| 64 | 31 | 4 | A8 |
| 128 | 58 | 1 | A2 |
| 256 | 113 | none | A1 |
| 512 | 222 | none | A1 |
| 1,024 | 421 | none | A1 |

All fail explicitly at the node cap and finish within the unchanged 35-second
and 1-GiB process guard. No larger powered result is claimed. Two limitations
remain visible: linear unresolved threshold work and the capacity-wide extent
interface. Whole-cell pruning does not by itself construct an unbounded
recursive contextual action.

## Validation and proof scope

- All **209,960** admissible symmetric fields through width eight agree with the
  exact pair-step oracle, in 44 separately guarded partitions. The nine JUnit
  reports have no duplicated partitions and match the frozen source before and
  after execution; aggregate JUnit time is 92.709 seconds.
- The same composed actions are checked against every admissible symmetric
  field through width three at powers 1,2,4,8, including eventual overflow.
- A16 is observed under independent bindings, including maximum-width fields
  and an immediate growth-to-capacity boundary. Incorrect EQ coordinates are
  rejected through composition. Exhaustive work remains in validation, not the
  ordinary test partition.
- Isabelle proves whole-cell LT/EQ/GT range pruning over arbitrary index sets,
  and threshold agreement under spatial restriction and union. The installed
  full session passes without oracle dependencies. These are pruning laws, not
  a verified Python circuit compiler or a compact powered-196 closure theorem.
- Adversarial review checked simultaneous substitution, overflow and padding,
  the harmonic kernel, and resource guards. Work charges reject negative counts.

Frozen source fingerprint:
`802d2bcabbac4111f8ee5e6cab07a907dda7708bcef5848c9c5981dd9981db45`.
At that fingerprint, the ordinary suite passed **4,318 tests**, with 1,038
validation tests deselected, in 293.52 seconds under the existing 300-second
guard. Both JUnit fingerprints match; see `unit-final.xml` and
`unit-final.guard.json`. A subsequent mypy run found an annotation issue in
the added multi-binding test, which was fixed before the
[consumer-schema audit](../reverse-consumer-schema-audit-2026-09-10/README.md).
That audit records the newer source and validation. The measurements above
remain the historical pre-schema-storage checkpoint; they have not been
relabeled as results from the newer source.
