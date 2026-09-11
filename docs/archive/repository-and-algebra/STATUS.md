# Current status

The **linear bisimulation checkpoint is complete**. Certified decimal reverse/add
and physical Collatz public terms no longer enter their sequential generation/event
adapters on the bounded route. They execute verified minimized T^2 / C^4 finite
bimachine rungs through `ExtensionalFamilyApplication`; the recursive radix replay
backend is removed and final exact observations are restricted to the shared capped
microblock cache. Wider/unadmitted sources fail over to the shared quotient diamond,
never to a sequential family fallback.

Fresh checkpoint evidence: `results/linear_bisimulation_checkpoint_v1.json`. The
N=16/32/64/128/256 gate records zero sequential-generation advances, zero spatial
occurrence-history bindings, zero forbidden future payloads, and bounded retained
entries. The complete pytest suite passes **2,862/2,862** on the final source tree.

This checkpoint restores a **linear temporal-machine floor**, not final logarithmic
HashLife. Repeated low-power rungs still scan the bounded transient working word.
Higher-rung bisimulation closure remains the next performance milestone: compose a
powered machine, refine by complete output + successor behavior, and publish the
canonical parent only when minimization closes within the fixed resource gate.

See [LINEAR_BISIMULATION_CHECKPOINT.md](LINEAR_BISIMULATION_CHECKPOINT.md) for the
checkpoint contract and [DIAMOND_IMPLEMENTATION_STATUS.md](../hashlife/DIAMOND_IMPLEMENTATION_STATUS.md)
for the remaining higher-rung work.

The remainder is a preserved historical v0.59.9 snapshot. Its H=20 packed-cut
claims and counter values describe a superseded representation, not the current
production architecture or an accepted exception to the checkpoint contract.

## Historical v0.59.9 status

## HashLife bounded temporal application

The production reverse/add and physical-Collatz nth-term paths now use family-specific bounded temporal quotients rather than the generic `_RecursiveResidualAction` occurrence forest.

### Reverse/add 196, N=256

```text
literal seed root                 3 canonical tiles
compiled F^N description        45 nodes
bounded temporal state/action    2 / 2
generic recursive app nodes      0
raw temporal length/span fields  0 / 0
exact spatial occurrences        236
symbolic spatial action nodes    10,567
binary jump entries              464
primitive forcing evaluations    255
primitive tail exponent          1.006
```

Temporal-history growth is closed: the bounded carry-cut interface is generation-independent. The remaining release blocker is cold spatial forcing-action composition; it is still approximately linear in N.

### Collatz 27, N=256

```text
literal seed root                 5 canonical tiles
compiled F^N description        181 nodes
bounded temporal state/action    3 / 3
generic recursive app nodes      0
raw temporal length/span fields  0 / 0
exact spatial occurrences        41
symbolic spatial action nodes    122
binary jump entries              161
primitive evaluations            42
residual physical steps          1
primitive tail exponent          -0.034
```

Seed 27 saturates under the measured bounded quotient on the final doubling. This is representative evidence only; arbitrary-source logarithmic physical-Collatz projection is not claimed.

### Removed runtime debt

- raw `SpacetimeBoundary` temporal carrier deleted;
- scalar recursive residual `length`/`depth`/`anchor_before` identity deleted;
- reverse/add uses fixed H=20 carry-cut state;
- Collatz uses bounded residue/local phase plus symbolic event transport;
- exact pair/tail spans are arena-owned spatial payload, not temporal keys;
- diagnostic `node_id` is no longer a semantic/work key in core quadtree/action traversal;
- generic macro/residual production counters are zero by construction for these two families;
- compiler and query activity are phase-separated in public metrics.

## Verification

Current targeted suite: **135/135 passing**.

Current temporal probes: reverse/add `PASS` with logarithmic closure false because spatial forcing work remains open; Collatz `PASS`, representative seed-tail sublinear true, arbitrary-source logarithmic closure false.

See `HASHLIFE_STATE_ACTION_GROWTH_RESULTS.md`, `HASHLIFE_METRICS_INTEGRITY_RESULTS.md`, and `RELEASE_BLOCKERS.md`.
