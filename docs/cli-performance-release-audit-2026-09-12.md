# CLI performance release audit — September 12

The CLI now avoids loading unrequested family runtimes, observation handlers and
large metrics schemas. Antihydra projections consume retained branch support,
and the 196 publisher caches validated composition edges. These repairs reduce
measured CLI latency. **Release remains blocked** by the outstanding powered
construction and refinement obligations.

Final validation on September 13 has 5,002 passing unit tests and the same four
baseline failures. The preserved 22-assertion release selection has 15 failures
and seven passes, improving by the Antihydra no-rediscovery assertion. Installed
wheel, typing, package ownership and structural-policy checks pass.

## Installed CLI measurements

Each measurement includes startup, imports, construction, requested observation
and JSON rendering in a fresh process from an isolated installed wheel. The
table gives medians of three runs, with normal filesystem caches. Both wheels
produce matching requested semantic output. These are finite measurements, not
asymptotic bounds or cold-disk measurements.

| Query | Before | After | Speedup |
| --- | ---: | ---: | ---: |
| `--list-families` | 434 ms | 75 ms | 5.77× |
| `196 --nth 8 --format json` | 519 ms | 234 ms | 2.21× |
| `collatz --nth 64 --seed 27 --format json` | 3.87 s | 3.71 s | 1.04× |
| `antihydra --nth 512 --info ledger --info clock --format json` | 490 ms | 79 ms | 6.18× |
| `fermat --nth 0 --no-value --info primality --format json` | 449 ms | 103 ms | 4.34× |
| `mersenne --nth 11 --no-value --info factor --format json` | 453 ms | 102 ms | 4.44× |

F0 is a cheap admitted control and M11 has a checked factor. Their timings do
not establish missing general Fermat/Mersenne primality coverage. Collatz's
ordinary physical publisher work still dominates its 64-step query.

## Repairs and adversarial checks

- Public package exports resolve lazily through one owner, retaining the same
  exported objects. Family dispatch imports only demanded implementations.
  Observation handlers and metrics schemas are loaded on demand. JSON integer
  conversion has a shared owner independent of Antihydra observers.
- Startup poison tests forbid unrequested runtime, metrics and observer imports
  in real CLI subprocesses. API tests poison the canonical evaluator functions,
  so moving imports cannot bypass the lazy-execution assertions.
- Repeated Antihydra execution on one engine now uses distinct charged result
  owners while reusing arithmetic memoization. Old and new publications retain
  their own authenticated support and pass the shared payload audit.
- Antihydra section projections fold the already-retained bounded parity words.
  They perform zero macro branch rediscovery. At most two demanded one-step
  physical roofs are constructed per fold; workspace is charged and released
  after success or failure. The fold still has one charged step per macro return.
- The 196 schema caches only immutable nonprimitive composition edges, charged
  to its resource ledger. Exact ID type and arena authority are checked before
  cache access. Read-only validation does not publish; rejected, identity and
  primitive inputs allocate nothing. A proposed mutable validation cache was
  rejected during audit because it violated these properties.

A preliminary 196 N=64 single-point profile before the final primitive-admission repair improves from 1.251 to 1.178 seconds of
CPU time, approximately 5.8%. It still performs 2,851 higher continuations and
9,776 concrete operations. This preliminary profile does not clear the powered
cutover gate. Retained Antihydra support folding alone improved 2.77× at N=512
and 1.88× at N=2048; those ratios are not whole-spacetime or whole-CLI speedups.

With warm imports, Antihydra N=512 execution takes 2.04 ms on a cold engine and
0.49 ms on the reused engine. The one-return reference with preconstructed atoms
takes 0.56 ms; cold construction is not faster than that reference at this size.
The warm run still charges its eight arithmetic block applications and 512
physical roof terms. The CLI gain above primarily comes from removed startup
overhead, and does not establish arbitrary-size source-discovery performance.

## Remaining release obligations

| Obligation | Remaining work |
| --- | --- |
| 196 powered publisher | Replace the cold higher-continuation evaluation with an admitted image construction and prove its production refinement. Caching schema edges does not reduce the counted continuation work. |
| Collatz physical and event construction | Complete the source-bound output publisher bridge and charged source-dependent discovery. Existing supported-sector shortcuts do not establish a general powered bound. |
| Antihydra powered projections | Compose demanded section images without a linear macro support fold, with complete literal/consumer refinement. The narrower no-rediscovery gate is now satisfied. |
| Fermat/Mersenne terminal recovery | Construct and refine the compact transverse unit/annihilator evaluator consumed by the CLI. UNKNOWN remains required when recovery is unavailable; no classical fallback was added. |
| Non-halting and full projection proofs | Supply the source-7 barrier instance and remaining executable/projection refinements. No new mathematical completion is claimed by this performance patch. |

The unchanged full-unit and explicit P0 results, installed-wheel checks, hashes,
timing samples and reproduction commands are in the
[performance evidence](../results/current/cli-performance-2026-09-12/README.md).
