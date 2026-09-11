# Collatz carry/output quotient — September 10, 2026

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

Added the exact radix-64 17-class raw-output partition, the nine-valued carry
correction, a separate within-class affine value potential, symbolic shift
and carry composition, and the constrained LT growth edge. Canonical radix-64
sentinel execution now uses these laws. Finite event composition forwards
digits through the controllers without collecting intermediate words.

See the [architecture and proof scope](../../../docs/architecture/collatz-carry-output-quotients.md).
The patch is relative to the preceding
[morphism-connection checkpoint](../morphism-connection-2026-09-10/README.md).

## Verification

The unprofiled **serial unit suite passes 4,148 tests in 287.16 seconds**, with
918 validation tests deselected. Its unchanged 300-second guard completes in
288.04 seconds with 570,377,080 bytes (approximately 544 MiB) sampled peak
physical footprint. `unit.log`, `unit.guard.json` and `unit.xml` preserve the
run. Before, after and current authored-source fingerprints match:

```
a97f1d07274943c5630277cff97f0563209977279b65ef07bfa9698b8878a473
```

The preceding unit checkpoint took 284.30 seconds; this addition does not
establish a unit-suite speedup. The two selected validation passes below do
not constitute complete release-validation evidence.

The focused arithmetic, Collatz and finite-function suite passes **91 tests
in 2.51 seconds**, with five validation tests deselected. Its default guard
completed in 3.03 seconds with 86,688,272 bytes sampled peak physical footprint.
Two existing sentinel validation tests also pass in 0.56 seconds, covering
500 random sources across each of four radices for each differential law.
Their logs and guard reports are retained here.

Strict nonincremental mypy passes for 1,089 files. Ruff check and formatting
pass for the final tree. Structural policy reports no line-count, recursion
or package violations. No existing tests, parameters, markers or gates were
weakened. All expensive checks ran sequentially under the existing process
guard; the default probe limit is 35 seconds and 1 GiB.
`changes.patch` contains the implementation, tests and documentation changes;
`manifest.json` records the changed-file and evidence hashes.

## What was proved and connected

* The 17 classes agree exactly with the declared raw carry/output observation
  signature, checked across every pair of primitive digits.
* All 192 digit/carry inputs reconstruct their exact raw value from the class
  representative and the separate affine offset.
* Four different three-cell carry-domain geometries share canonical complete
  carry/correction functions for all three incoming carries.
* All 24,576 adjacent raw-digit/phase assignments satisfy the shift wiring;
  all 18 terminal carry/phase cases satisfy the restricted growth rule.
* Symbolic local temporal composition preserves exact outputs and downstream
  carry guards, without enumerating composed register valuations.
* The live radix-64 evaluator passes with its previous redundant-field
  builder poisoned. Streaming one-, two- and four-event targets and weights
  match independent arithmetic through 2,048-bit deterministic random inputs.
* Two-event streaming matches all 2,048 positive odd sources below 4,096,
  covering every residual phase. The frame-translation witness preserves the
  final target and exit frame while exact accumulated valuation changes by 1152.
* Invalid phases, sorts, source boundaries and event/publication budgets fail
  closed. Independent ownership and payload audits report no violations for
  the retained symbolic functions.

The negative witnesses remain explicit: an old EQ source cannot emit raw EQ,
but a non-EQ source can; and equal raw classes can produce different shifted
carry domains. The compiler retains the value information needed to distinguish
those outputs.

## Limits

This does not reproduce or certify the supplied 89/1,636-state machines,
41-valued two-event potential, or three-digit terminal halo. The primitive
offset added here is at most six source units (18 raw-output units), with its
exact meaning checked exhaustively.

The finite-function arena reduces symbolic local compositions. The streaming
event pipeline itself is linear in event count and is not a universal temporal
minimizer or a logarithmic powered controller. Its default 64-event allocation
budget is checked before source consumption. It collects only an explicitly
requested final endpoint, and is not retained as a lazy future summary.

The existing binary powered Collatz kernel is unchanged. Universal register
updates, Frobenius reduction through repeated temporal squaring, and the full
release/scaling obligations remain open. No public powered-query or unit-suite
speedup is claimed.

Earlier focused logs show passing intermediate checks. `types-initial.log`
records a test-only optional-value indexing error corrected before the final
strict typing run; it is diagnostic history, not passing evidence.
