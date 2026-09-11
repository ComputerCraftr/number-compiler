# Geometry-derived carry ports: implementation and evidence

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

Current carries are derived from exact domain geometry through the existing
carry monoid. This checkpoint makes that operation explicit in the research
expression algebra, shares it with Collatz's two wires, and corrects the prior
wording that suggested a missing pointwise carry residual. See the
[implementation note](../../../docs/geometry-derived-carry.md) and
[Collatz harmonic proof](../../../docs/collatz-harmonic-port-actions.md).

## Implementation and audit

- `ThresholdExpressions` owns native carry composition/application nodes.
  Evaluation uses the canonical `CarryFn` owner; simultaneous substitution
  rebuilds these nodes with their complete argument dependencies.
- `ThresholdGeometry` owns prefix derivation over its canonical domain word.
  Counted runs exploit monoid idempotence. Prefix queries use shared subtree
  summaries and never export a complete carry field.
- `ReverseGeometryContext` derives carry/growth/normalization operands from
  one source geometry root. This replaces EQ/GT table tests and selections,
  not independent source variables: none of its original inputs was a carry.
- `CollatzDomainGeometry` derives both wire geometries from the existing five
  domain actions and reuses the same prefix implementation. It is a research
  adapter; existing production directed transducers already derive their
  carries from source tile roots.

Adversarial review found an initially unbudgeted prefix-summary cache. The
fix charges each entry against the same expression/schema node ceiling and
retires it when its weakly referenced geometry word dies, or when the geometry
owner is released. Tests cover both lifetimes and budget exhaustion. Invalid
incoming expressions are rejected before prefix traversal. Native carry nodes
remain ordinary counted expression nodes, not hidden semantic ports.

## A16 and A32

The old capacity-nine interface contains **one width, five domain, five F5,
and five parity variables**. It has zero independent carry/border/harmonic
inputs. The old 1,300 binding count was for unary-table operands.

| A16 metric | Prior checkpoint | Derived geometry |
|---|---:|---:|
| Unary-table occurrences | 1,844 | 1,556 |
| Unique unary-table bindings | 1,300 | 1,156 |
| Reachable unary schemas | 41 | 40 |
| Retained expression/schema nodes | 9,049 | 8,953 |
| Reachable native carry nodes | 0 | 336 |

The native carry nodes are included in the 8,953 total. Fewer table bindings
are not a claim that all expression bindings disappeared. A8 still has 780
tables and 168 native carry nodes, versus 1,556 and 336 at A16. The remaining
temporal construction grows roughly linearly.

The capacity-sixteen A32 probe still reports `budget_exceeded` at the unchanged
30,000-node limit after reaching A16. The process guard itself completes; that
does not count as a successful A32 action. This checkpoint neither completes
successor closure nor establishes a production runtime speedup.

The `*.before.txt` files preserve the exact four research-module inputs to the
change. Prior A16 counts come from the
[schema checkpoint](../reverse-consumer-schema-audit-2026-09-10/README.md).
Exploratory `a16-first` and `a32-first` logs predate the cache-accounting fix;
final probes and fingerprints are recorded below.

## Formal proof

The complete installed Isabelle2025-2 session passes in **14.84 seconds**,
with sampled peak footprint **446,843,880 bytes**, under the unchanged
35-second / 1-GiB guard (`isabelle-third.log`, `.guard.json`). It uses the
existing bounded `number-compiler-ports-proof` profile. Two unsuccessful
proof attempts remain recorded separately.

The laws establish Boolean prefix composition, all-EQ preservation,
last-decisive LT/GT determination, exact Collatz wire-word composition and
prefix projection, spatial harmonic projection, and conditional linear source
death. The oracle-dependency audit is empty. They do not establish nonlinear
temporal closure or a five-round Hensel-refinement bound.

## Final validation

Final authored-source fingerprint:
`26257fefdc724c218dc34ee128f93e0634f0e3f5b77d563312c1de48050a44a8`.

All 14 final test runs have matching before/after/current fingerprints, unique
test manifests, no failures/errors/skips, and successful unchanged process
guards. `validation-summary.json` verifies the complete selected manifests.

| Selected checks | Passed | Aggregate JUnit time |
|---|---:|---:|
| Ordinary focused, dependency and repository-policy tests | 109 | 7.482 s |
| Collatz harmonic and existing Hensel validation | 29 | 23.706 s |
| Reverse/add exhaustive partitions | 44 | 90.296 s |

The 44 reverse/add partitions cover **209,960** admissible symmetric fields
through width eight with exact successor agreement. Collatz covers **32,768**
odd original 16-bit sources: **32,766** nonempty normalized tails, **two** empty
tails, and **518** even normalized tails, with all phases 0..5 exercised. The
other Collatz checks include 29,655 spatial generator transitions, 7,776 linear
death phase sequences, and the exact seven-conflict refinement fixture.

The ordinary selected run deselects one existing validation-marked test;
the long new sweeps are likewise opt-in validation. No full ordinary or
unfiltered release-suite result is claimed. Strict nonincremental mypy passes
all **1,157** authored Python files (`mypy-final-2.log`); Ruff and formatting
of all 13 changed Python files pass. The initial typing/format failures are
retained separately from final passing evidence.

`a16-final.log` reproduces the table above after the cache fix. Its 1,156 table
bindings comprise **7** depending only on initial geometry/width and **1,149**
with initial value dependencies. Those seven are derived expressions too,
not seven independent carry variables. `a32-final.log` records the unchanged
budget failure. Both probes account for auxiliary cache entries; none remain
retained at the final A16 checkpoint after the source geometry is released.

The checked theory's SHA-256 is
`6835d834bb0be07055305aa1e01253f0d849135e7584eed9d40b71a3d586fb56`.
`source-freeze.json` records it independently of later Python validation.
`research-provenance.json` identifies the three supplied research attachments.
The complete Isabelle build predates the final Python-only corrections;
the verified theory content is unchanged.
