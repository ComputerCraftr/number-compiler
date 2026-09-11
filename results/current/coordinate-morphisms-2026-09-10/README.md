# Coordinate morphisms — September 10, 2026

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

Added an executable local `ReverseActiveOutputArena`, shared bounded unary
function composition, and centered F5 Frobenius transport. The arithmetic
functions combine output contributions before output-ID interning. Existing
blank-only future certificates and public scheduler admission remain unchanged.

See [the implementation contract](../../../docs/architecture/reverse-coordinate-morphisms.md)
for exact scope and outstanding release obligations. This checkpoint follows
the [quotient reuse checkpoint](../quotient-reuse-2026-09-10/README.md); its patch
is relative to that already-modified tree, not to the original September 10
upload.

## Verification

The focused arithmetic, symbolic composition and local output suite passes
**71 tests in 3.28 seconds**. Its 35-second guard completed with approximately
77 MiB sampled peak physical footprint. Evidence: `focused.log` and
`focused.guard.json`.

The unprofiled **serial unit gate passes 4,127 tests in 282.81 seconds**, with
918 validation tests deselected. The unchanged 300-second guard completed in
283.56 seconds, with 623,313,832 bytes (approximately 594 MiB) sampled peak
physical footprint. `unit.log`, `unit.guard.json` and `unit.xml` record the run.
The before/after/current authored-source fingerprint matches:

```
104169e88dc5f0ea7c87e047c2723373be256413e79ffc48631ebad75ebdea21
```

Strict nonincremental mypy passes for 1,080 files (`types.log`); Ruff check
and format pass (`ruff.log`, `format.log`); repository policy reports no source
size, recursion or package violations (`policy.log`). A fresh independent
ownership/payload audit of a symbolic output, its projections and derived
carry action reports no violations (`ownership.log`). Expensive checks have
their adjacent guard reports. `changes.patch` contains the implementation,
tests and contract changes relative to the preceding checkpoint.

The prior unit run took 278.27 seconds; this run does not establish a test
speedup. No existing tests were removed, reclassified or reduced. No full
release, active-future-closure or cold-scaling pass is claimed.

## What the new evidence establishes

* All 1,444 local decimal pair/carry assignments agree with the scalar law.
* F5 output construction agrees with transport plus carry births and cancels
  before interning the combined coordinate function.
* Both supplied witnesses merge at each observed output coordinate with exact
  tile construction poisoned. No whole-row or active future ID is asserted.
* Equal F5 output observations can retain different next carry actions.
* All 361 symmetric width-three blocks agree with the oracle when carry
  prefixes and growth remain symbolic.
* Local symbolic squaring and spatial carry composition agree with independent
  laws. These are not arbitrary reverse/add temporal squares.
* Centered coefficient queries and composition agree with direct binomial
  coefficients and Laurent convolution. Huge sparse exponents stay sparse;
  dense expansions fail before consulting source functions.
* Invalid domains, foreign handles and output publication budgets fail closed.

The new arena is not wired into the public executor. The earlier N=32/64
scaling evidence is therefore still the relevant public baseline; no new
performance gain is attributed to these local morphisms.
