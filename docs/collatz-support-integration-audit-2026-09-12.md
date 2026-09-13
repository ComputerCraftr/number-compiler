# Collatz physical-support integration audit — 2026-09-12

Release status: **BLOCKED**. The repository now retains an ordered physical
support program and proves its core algebra, but the other production cylinder
observers still do not consume that program. A successful physical-clock query
therefore does not establish the requested common shadow-cylinder integration.

## Delivered component

[`PhysicalSupportArena`](../src/number_compiler/sequences/collatz/physical_support.py)
hash-conses identity, even, odd and chronological concatenation nodes. Program
identity is determined by atom and child handles; endpoint, tick counts and
ring specializations are not keys. [`primitive_physical_support`,
`spatial_physical_support` and
`temporal_physical_support`](../src/number_compiler/hashlife/execution/tile_physical_support.py)
attach and compose this support on completed physical-Collatz tile results.
Cross-arena handles are rejected, temporal composition preserves chronological
order, and the spatial join selects the one low-boundary owner. A spatial child
may legitimately carry zero ticks while its enclosing tile has nonzero
duration; exact tick-count equality belongs at the published, bound whole-source
root.

[`PoweredCollatzTerm.s_arithmetic_clock`](../src/number_compiler/sequences/collatz/block_power.py)
reads the bound result's `direct_physical_support()` and derives odd/even counts
from it. The Isabelle theory
[`Physical_Collatz_Support.thy`](../devtools/proofs/isabelle/etale/Physical_Collatz_Support.thy)
proves chronological evaluation and reassociation, semiring mapping under its
stated homomorphism assumptions, equality with the source-generated physical
matrix at `s=3,z=2`, and the exact source 4/5 support discrepancy at three and
eight ticks. The full `Etale_Primary_Carry` session and its oracle audit passed
for this theory.

These results establish the ordered support representation. They do not prove
that the Python interner refines the Isabelle datatype, that the powered
constructor publishes support before causal expansion, or that each requested
observer is a homomorphic image of this production owner.

## Adversarial findings

| Severity | Finding and exact owner | Release condition |
| --- | --- | --- |
| **P0** | Support is currently an annotation assembled during primitive, spatial, temporal and root completion in [`tile_physical_support.py`](../src/number_compiler/hashlife/execution/tile_physical_support.py), [`tile_kernel.py`](../src/number_compiler/hashlife/execution/tile_kernel.py), [`tile_causal_interface_step.py`](../src/number_compiler/hashlife/execution/tile_causal_interface_step.py), and [`tile_collatz_root_completion.py`](../src/number_compiler/hashlife/execution/tile_collatz_root_completion.py). A cold `direct_physical_support()` query can still enter `TileApplication.interface()` and causal interface construction. The support is not yet the source-image-restricted powered action that drives predicate expansion. | Construct and bind the second powered action on the first action's reachable source image. Publish that action/support handle through the normal result authority before causal leaf expansion, and make whole-output, point, width and observer queries reuse it. |
| **P0** | The production observer path in [`observe_collatz`](../src/number_compiler/api/cylinder_observation.py) separately discovers accelerated events with `accelerated_collatz_sentinel_step_digits`, builds a [`CollatzEventArena`](../src/number_compiler/sequences/collatz/power.py), and sends it to [`CollatzClockObservers`](../src/number_compiler/sequences/collatz/clock_observers.py). Its own module contract says it consumes supplied valuation actions. `twisted`, `hasse`, `hensel`, `tropical`, `factor`, and the cyclic/negacyclic polynomial lanes therefore remain disconnected from `PhysicalSupport`. | Make every named Collatz projection consume the bound physical support/action owner. Poison accelerated discovery and the old event arena in integration tests while checking directional moments/arches, Hasse derivatives, both cylinder signs, Hensel pullback, tropical hull and factor output. |
| **P0** | `physical_ticks` and `event_weight` remain independently propagated scalar result fields throughout causal interfaces and completed-result records. Validation compares them with support only when support is present and nonempty. This leaves two semantic authorities even though the support node caches derived counts. | At the published whole-source boundary, make these values derived fields of the same support scope, absent from action identity and normalization keys. Keep the empty-support spatial-child exception local and prove the boundary invariant. |
| **P0** | The added support construction and causal attachment add retained nodes and work to ordinary physical-Collatz queries. Current component checks do not establish the unchanged CLI time, memory and retention gates, and the support query can still pay causal construction before returning a projection. | Pass the unchanged cold/warm CLI gates at the release widths, with counters showing work bounded by the reachable support DAG rather than physical ticks or replayed causal leaves. Preserve failing measurements in the release record. |

## Adversarial hardening completed during the audit

Three executable defects found during review were repaired before this report
was frozen:

* [`PhysicalSupportArena._join`](../src/number_compiler/sequences/collatz/physical_support.py)
  now releases its atomic node and join reservations if node construction
  fails; `concat` also releases excess normalization reservations.
* Production [`PhysicalSupport.specialize`](../src/number_compiler/sequences/collatz/physical_support.py)
  now fails closed until a charged traversal workspace is supplied. Unmetered
  specialization remains available only in the research arena with no ledger.
* The public, generally unsafe `power` operation was removed. The private
  `_proved_collatz_cycle_prefix` and `_proved_collatz_power_two_tail` are used
  only by the checked `1 -> 4 -> 2 -> 1` shortcut in
  [`tile_collatz_cycle.py`](../src/number_compiler/hashlife/execution/tile_collatz_cycle.py).

Arena validation now checks atom semantics or canonical join children, counts
and parity in constant time. Tick and research specialization validate every
traversed node, and cached snapshots include parity and child identities. The
dedicated
[`physical_support_payload_audit.py`](../src/number_compiler/resources/physical_support_payload_audit.py)
checks the exact scheduler root, ledger/store roles, node semantics and join and
concatenation keys; only handles issued through that audit are approved. New
adversarial tests cover forged handles, cross-scheduler handles, direct mutation
and retained-ledger reconciliation after an unbalanced concatenation. Demanded
metrics require zero forbidden, unknown and mismatch objects and one completed
payload audit. These repairs close the individual accounting and admission
defects; they do not close the P0 architecture, observer or performance rows
above.

The full unit run exposed seven additional support integration regressions.
Repeated general concatenation exhausted the existing node budget on
trillion-tick proved cycles; the replacement constructs three rotated dyadic
cycle blocks per level and a single canonical boundary spine for the even
entry prefix. An intermediate arbitrary-seam join was rejected during review
because the general concatenator requires canonical inputs. The final bounded
tests match exact atom-by-atom interned nodes and remain identical after a
later temporal append. No budget was raised.

Persistent stores now always come from ledger factories, including a private
ledger for research-only arenas. Production audit authenticates the store
ledger alias and rejects redirection. The two live physical-output work
counters are forwarded from the captured work snapshot. These fixes restore
the supported cycle/resource contracts; general source-image powering and the
unchanged full-suite performance gate remain separate obligations.

## Required proof boundary

The generic semiring-map theorem is a reusable algebraic lemma. It does not by
itself prove the concrete directional `L/RL/R` moments, support/frontier arches,
Hasse derivatives, cyclic `z^m-1` lanes, negacyclic `z^m+1` lanes, Hensel
pullbacks, or tropical/Newton hulls. Each consumer needs a definition on the
ordered support program, its actual composition law, and a refinement theorem
from the bound production handle. Signed and tropical codomains also need their
own cancellation and normalization arguments.

The eight-tick source-4/source-5 collision is evidence that endpoint plus
odd/even weight erases support. It is not a counterexample to a common shadow
cylinder: the retained words `EEOEEOEE` and `OEEEEOEE` remain distinct and
specialize to offsets 20 and 17 at `s=1,z=2`.

## Release acceptance

The Collatz portion can leave P0 only when one candidate/source-bound powered
owner is constructed before expansion, all CLI cylinder views are projections
of that owner, its Python construction is connected to the Isabelle support
semantics, and the unchanged resource gates pass. The current physical-clock
consumer and support proofs are a completed component of that work; they are
not the completed production quotient.
