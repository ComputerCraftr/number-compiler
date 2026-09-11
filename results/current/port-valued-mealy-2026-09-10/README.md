# Shared port-valued owner: proof and implementation evidence

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

The [implementation report](../../../docs/port-valued-mealy-actions.md) separates
the shared spatial owner, actual affine-occurrence cache normalization and the
remaining temporal execution boundary.

## Accepted evidence

* Final manifest (local artifact: `final/manifest.json`): **214 selected tests passed** on frozen
  source `39aa74cbd07b93899c08a8308f75bf96b4be155e11c3ab43809308ccc1e3b82b`.
  There are 86 owner tests, 66 dependency tests, three spatial validations,
  16 full odd-16-bit occurrence shards and 43 repository/proof-boundary checks.
  JUnit manifests record each group. This is not a full repository suite run.
* Isabelle session (local artifact: `isabelle-third.log`) and guard (local artifact: `isabelle-third.guard.json`):
  the complete `Reverse_Residuals` session passed, including the new generic
  Mealy theorem and oracle-dependency check. Guard time 18.80s, sampled peak
  463,424,056 bytes. Theory SHA-256:
  `ec03d370c780df87560726d2dcfece458a5fecfeb53f65da294894d21c71c0d8`.
  This proves the algebraic spatial laws, not extraction/correctness of the
  Python implementation or a general nonlinear temporal quotient.
* Actual occurrence interner (local artifact: `final/occurrence-interner.json`): 3,160 raw
  equivalent representations, 1,280 retained occurrences, 1,880 hits.
  All represented values are independently checked. The 864 distinct integer
  outputs are not cache identity. No physical scheduler hit gain is inferred.
* Public point cache probe (local artifact: `final/public-cache.json`): N8/16/32 exact indexed
  outputs and repeated warm queries remain correct. N32 completed entries
  remain 2,305 for 196 and 1,024 for physical Collatz.
* Strict mypy (local artifact: `final/mypy.log`): all 1,185 source files pass. Ruff passes across
  `src`, `devtools` and `tests`.

Each heavy subprocess uses the unchanged 35-second/1-GiB guard, and the driver
verifies the authored-source fingerprint after every command. Initial failed
Isabelle syntax/lookup attempts and the corrected development mypy failure
outside `final/` are not accepted proof/test evidence.

## What the tests establish

The decimal occupancy cylinder produces exact carry, reset, normalization and
physical forcing jets for every three-domain word through width five under
both input ports. Spatial squaring reaches width `2^80` with source constructors
poisoned. It stores no separate domain or clock field inside cylinder identity.

Collatz wire responses now store all-port rows; carry/affine coordinates are
derived views. All 64 leaves are checked against their five exact cylinder
classes before testing 25 representative products, replacing the redundant
4,096-pair threshold gate. The richer output-jet gate retains all 4,096 pairs.
The complete length-1…8 spatial response exploration and 6^5 homogeneous phase
control also pass through the shared composition owner.

The normalized Hensel carrier passes **all 32,768 odd 16-bit seeds**, starting
at the direct U-squared image and checking eight further valuations and exact
targets per seed. The counted-run normalizer preserves million-quarter inputs
without expanding runs. Exact zero extent and logical time remain explicit.

The temporal negative gate tests both ports, not just the realized birth:
`(4,4)` and `(8,8)` have identical current carry-derived cylinders yet their
successors have different carry domains. This does not reject the attachment's
exact spatial-image payload or a separately specified accumulated live eta.
It prevents treating current forcing projection as a complete temporal root.

The retained-image rebase and arbitrary dyadic temporal composition gates
remain open. None of the spatial proof, interner hit count or bounded
differential tests is reported as solving them.
