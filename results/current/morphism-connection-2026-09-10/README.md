# Connected output-to-carry morphisms — September 10, 2026

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

The public causal executor now uses a bound output morphism followed by a
parametric next-carry projection for decimal primitive producer/consumer
edges. This removes fused-interface construction on those edges and avoids
producer exit scans for a single covered source interval. Compositions are
shared by next-carry functions; source bindings are cleared before query tile
leases retire. No exact producer successor tiles are constructed on this path.

The [architecture contract](../../../docs/architecture/reverse-coordinate-morphisms.md)
describes the admitted consumer and its limits. This patch follows the
[local coordinate-morphism checkpoint](../coordinate-morphisms-2026-09-10/README.md).

## Verification

The unprofiled **serial unit gate passes 4,135 tests in 284.30 seconds**, with
918 validation tests deselected. The unchanged 300-second guard completes in
285.27 seconds, with 618,562,472 bytes (approximately 590 MiB) sampled peak
physical footprint. `unit.log`, `unit.guard.json` and `unit.xml` retain the
evidence. Before, after and current authored-source fingerprints match:

```
588654b6fa3e08956824c41f681fd3949ba044f364f99060ede2ca8fa6482e96
```

The preceding unit checkpoint took 282.81 seconds. This change does not
establish a unit-suite speedup. No existing tests were removed, reclassified
or reduced, and no resource or runtime gate was raised.

The focused suite passes **92 tests in 7.77 seconds**, including exhaustive
20 × 43 × 5 local output laws, both live causal directions with fused/exact
construction poisoned, all next-consumer carry states on selected producer
bindings, cancellation and carry-distinction witnesses, budget cleanup,
stale-source rejection and an independent payload audit that detects a
corrupted composition. See `focused.log` and `focused.guard.json`.

Strict nonincremental mypy passes for 1,084 files. Ruff check and formatting
pass. The structural policy reports no line-count, recursion or package
violations. Their logs and guard reports are retained alongside this document.
`changes.patch` records the implementation, tests and contract changes relative
to the preceding checkpoint. `manifest.json` records source and evidence hashes.

## Public point-query comparison

Each measurement starts a fresh process and queries digit zero of
`ReverseAddPoweredTerm(196, N)`. The baseline substitutes only the preceding
checkpoint's `finite_pair_transfer` function into the current tree; it keeps
the same surrounding code. The current run uses ordinary production routing.
`probe-command.txt` records the exact Python command body, and
`baseline-finite-pair-transfer.txt` preserves the baseline function. The probe
originally loaded that file from the pre-change tar checkpoint in `/tmp`.
Each individual process runs under the default 35-second, 1 GiB guard.

| N | Digit, both routes | Old seconds | Connected seconds | Old fused frames | Connected fused frames | Causal frames, both |
| --- | --- | --- | --- | --- | --- | --- |
| 32 | 8 | 4.2074 | 4.0555 | 842 | 0 | 53,396 |
| 64 | 8 | 14.6600 | 14.3711 | 2,314 | 0 | 184,754 |

The connected N=32/64 runs serve 3,439/16,263 carry observations using
373/1,066 output bindings and 137/370 distinct spatial compositions.
Logs retain the full counters. Sampled peak physical footprint is
58,753,480/91,898,336 bytes for the connected runs, versus
62,439,904/96,305,632 bytes for the baseline.

These are single-run timings, not a statistically established speedup.
Eliminated traversal work is directly measured; unchanged causal-frame counts
show that the larger scaling problem remains. The connection does not admit
active whole-state future classes, discharge arbitrary composed consumers,
or wire F5 temporal transport into arbitrary reverse/add squaring. The full
release and N=16…1024 cold-scaling obligations remain open.

## Diagnostic corrections

The initial focused run found that separately valid source/port binding keys
were being aggregated as an untyped numeric payload. The independent binding
audit now recognizes each checked key. The corruption regression still rejects
an issued but incorrect carry function. The initial type run found a reused
loop variable with incompatible key types; distinct variables corrected it.
The initial failed logs remain here as diagnostic history, not passing evidence.
