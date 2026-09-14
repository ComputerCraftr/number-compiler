# Reverse/add source-publisher production audit — 2026-09-12

**Historical checkpoint, superseded by the September 13
[adversarial follow-up](adversarial-release-audit-2026-09-13.md).** The production
router now constructs `ReversePublisherProjection`, which uses the higher
publisher and recursive coordinate outputs. The disconnection described below
was repaired. Higher-continuation image construction and its powered refinement
still block cutover; the old measurements below are not current CLI timings.

## Earlier disconnected implementation

The 196 powered constructor remains a P0 release blocker.  The live public
path is source-authenticated and exact, but it does not consume the repository's
source-bound publisher objects.  Its cold completed-result population fails the
existing release envelope before the N64 performance case.

## Live path

`ReverseAddPoweredTerm._point_index()` constructs a `HashLifeBlockIndex` from
the exact symmetric pair field and the binary-composed temporal effect.
`build_bounded_application()` admits the reverse/add family certificate, but
`build_certified_field_application()` routes it back to
`build_tile_projection()`.  That builder constructs `TileScheduler` and its
`CausalTileEngine` execution path.

A demanded point descends spatially in `tile_causal_point.point_step`.  Before
returning the scalar it also requests `promote_midpoint`.  Temporal composition
in `cached_midpoint_step` consumes or constructs an exact first output tile,
derives the second action's boundary state from that output, and publishes an
exact completed second output.  This is why removal of the old scalar temporal
interpreter did not close cold construction.

The source-bound objects that could represent a publisher without an exact
future tile are currently disconnected from that path:

- `RecursiveFieldImageExecutor` and `FieldTransferExecutor` have no production
  instantiation;
- `HigherSpatialMacroComposer` and `RecursiveCoordinateMorphismArena` are
  exercised by unit tests but not constructed by a production family router;
- `ReversePoweredLocalCodec` is an exact spatial action on a scoped source
  cell or forest, but its own contract correctly excludes temporal
  substitution of output, growth, extent, and halo channels;
- `FactoredTemporalPower.block()` constructs the concrete midpoint before its
  second half and is not a source-bound replacement.

This is a production-disconnection result obtained from constructor and caller
searches, not from an observer-only quotient or a carry-domain collision.

## Existing release gate

The unchanged `reverse_temporal_power_probe._doubling_envelope` permits, for
each doubling, at most twice the previous measurement plus the fixed N16
bootstrap.  Running its production rows at N16 and N32 on the same checkout
reported:

| Generation | Projection seconds | Completed results | Ledger entries | Ledger nodes | Internal action work |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 16 | 1.130 | 597 | 8,600 | 11,021 | 18,913 |
| 32 | 3.706 | 2,305 | 29,477 | 26,468 | 51,337 |

The report is `RED` with
`completed_result_entries_exceeds_doubling_envelope` and
`resource_ledger_entries_exceeds_doubling_envelope`.  For completed results the
existing N32 ceiling is `2 * 597 + 597 = 1,791`; the observed value is 2,305.
The same run reports zero higher semantic task frames, zero temporal leaf
diamond descents, and zero higher action continuation requests.  Therefore the
current blocker is exact completed-result construction and retention, rather
than a hidden scalar replay loop.

The retained process-guard report completed with child return code zero in
8.067 seconds and sampled an 85,918,200-byte physical footprint under the
35-second, 1-GiB gate.

The command used for the smallest gate was:

```sh
PYTHONPATH=src:. python3 - <<'PY'
import devtools.benchmarks.reverse_temporal_power_probe as probe
probe.CONSTRUCTION_INDICES = (16, 32)
probe.PROJECTION_INDICES = (16, 32)
result = probe.run_probe()
print(result["status"], result["release_blockers"])
for row in result["projection"]:
    print(row["generation"], row["completed_result_entries"],
          row["resource_ledger_entries"])
PY
```

## Missing production construction law

Let `D` be the admitted source support, `A` the first temporal action, and `B`
the second.  A live source-bound publisher must construct the reachable image
`I_A(D)`, including active frontier, extent, growth seam, mirror orientation,
and both boundary ports.  Only then may it construct the second publisher on
that image.  In operational form the required construction is

```text
publish(B o A, D) = compose(publish(A, D), publish(B, I_A(D))).
```

The missing statement is stronger than associativity of functions.  It must
show that the concrete reverse/add image summary supplies every source and
boundary distinction used by `B`, that its coordinate output morphism agrees
with the exact digit kernel, and that composing summaries does not enumerate
the intermediate image.  It must also prove a first-use work and retention
bound for binary powers.

No current Isabelle theorem proves those obligations.  In particular,
`Decimal_Publisher_Constructor` proves local normalization and consumer
pullback laws, then explicitly leaves future growth/birth itinerary discovery
and first-use publisher DAG work open.  `Reverse_Contextual_Fixed_Point` proves
all-continuation equivalence only under a caller-supplied stability premise.
Neither theorem instantiates the live `TileScheduler` result key or a concrete
production `FieldImageAdapter`.

## Required integration point

The next implementation must add a concrete reverse/add source-bound adapter
and make `build_certified_field_application()` select it for the reverse/add
certificate.  The returned application must implement point, active-width,
and mirror-obstruction queries from one authenticated source-bound publisher.
The release gate must then show exact agreement while the two existing
doubling-envelope blockers disappear.  Merely exposing another source tuple,
renaming the current carry geometry, or proving the abstract composition law
without this live consumer would leave the production disconnection intact.
