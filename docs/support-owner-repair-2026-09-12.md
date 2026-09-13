# Ordered support repair and remaining production obligations

Release remains **BLOCKED**. This change repairs support erasure in the
free-cylinder research constructor. It does not install that constructor in
the production tile scheduler or complete the four family release gates.

## The concrete normalization defect

On the three-bit source chart, eight physical Collatz ticks give:

| Source | Ordered ticks | Endpoint | Odd/even ticks | Offset at s=1, z=2 |
| ---: | --- | ---: | --- | ---: |
| 4 | EEOEEOEE | 1 | 2 / 6 | 20 |
| 5 | OEEEEOEE | 1 | 2 / 6 | 17 |

Previously both selected constant consumers were represented by the same
output, event count and duration. Their support was lost. The simpler
three-tick EEO/OEE example has offsets z² and 1, but one consumer on this
chart still has an affine output; the eight-tick example demonstrates the
actual constant-consumer collision.

This is a defect of that implementation's normalization, **not** a
counterexample to the proposed common shadow cylinder. The original source
binding remains necessary and is separate from a reusable support program.

## Repair

[`physical_support.py`](../devtools/experiments/collatz/physical_support.py)
retains an interned program of identity, even, odd and chronological
concatenation. Guard consumption preserves its handle, including when an
affine output becomes constant. Consumer composition concatenates the support
programs. Event count and duration are derived from those programs.

The program supports weighted physical-tick selection and demanded finite-ring
evaluation. It does not lower a full affine integer or retain an expanded
coefficient word. Observer coefficients and precision are absent from its
identity. A demanded observation cannot insert support nodes. Node, join,
duration and coefficient bounds are checked; fabricated handles fail admission.

The existing production `CollatzEventArena` and this research arena use one
[`word_concatenation.py`](../src/number_compiler/arithmetic/functions/word_concatenation.py)
implementation of their existing largest-dyadic-prefix reassociation. They keep
their distinct atom semantics: accelerated events versus physical ticks.
This shared normalization helper is the production code change here; it is
not a production source-to-support constructor.

Output-only and output-plus-clock class counts remain separate **projections**.
Their previous assertions are unchanged. New metrics report actual support
classes, retained support nodes and interning work. On fresh five-bit charts:

| Ticks | Output classes | Output/clock classes | Support programs | Retained support nodes | Future endpoint consumptions |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 16 | 8 | 10 | 31 | 99 | 0 |
| 1024 | 3 | 7 | 31 | 303 | 471 |

The last column remains nonzero. Retaining support does not remove scalar
future discovery or make the reachable-image construction gate pass.

## Isabelle scope

[`Physical_Collatz_Support.thy`](../devtools/proofs/isabelle/etale/Physical_Collatz_Support.thy)
defines the ordered support language, proves its coefficient-semiring mapping
and reassociation laws, and connects source-generated support to the existing
source-generated physical matrix. It proves both concrete examples above.
The session checks theorem oracle dependencies.

These are semantic support theorems. They do not verify the Python interner,
iterative normalizer, guard-trie constructor, production scheduler or all six
specific observer codomains. Python differential tests check the implemented
constructor against independently generated physical paths through 1,024
ticks, source binding, association, precision-independent handles, and bounded
queries on a 2^100-tick shared program. These tests are not an Isabelle
refinement theorem for Python.

## Integration points still missing

* **Collatz:** construct the second action on the reachable image before
  expanding its predicates; retain its source guards and support; publish the
  resulting lazy output through `PoweredResultKey` and the normal result
  arena. Whole-output, point, width and observer demands need this same owner
  before their causal fallback. `complete_clock` currently handles only the
  admitted root/cycle sectors.
* **196:** provide the source-restricted two-port future publisher and prove
  both port pullbacks through powered composition. A Collatz affine leaf is
  not its decimal reverse-add law.
* **Fermat/Mersenne:** bind the ring/circle square actions to candidate-derived
  terminal constructions and prove their family-specific terminal/root and
  observer refinements. Supplied étale-root observations cannot establish this
  bridge. Checked proper factors remain printable when available.
* **Views and proofs:** specify each demanded directional, frontier, Hasse,
  cyclic, negacyclic and Newton observation on the retained program and prove
  its actual composition operation. A generic coefficient homomorphism theorem
  alone does not prove every named observation or handle cancellation in every
  signed family algebra.
* **Release evidence:** complete the unchanged CLI performance gates and full
  release suite. The general powered constructor, full production refinement
  and performance obligations remain P0.

Validation logs and machine-readable status are recorded in
[`results/current/support-owner-repair-2026-09-12`](../results/current/support-owner-repair-2026-09-12).

The final component selections pass **180 tests**, with eight opt-in tests
excluded from the two default selections. Strict mypy passes for 1,251 files;
Ruff and the repository line/recursion policy pass. `Etale_Primary_Carry`
builds with oracle checking in 20.64 guarded seconds and a sampled 3.70 GB
peak, below the unchanged 4 GiB Isabelle limit.

A broader combined selection including deep validation tests timed out at the
unchanged 35-second gate. That failure is retained separately and is not
superseded by the component passes. The full 300-second release suite was not
rerun; its earlier failure and the open production performance gates remain.
