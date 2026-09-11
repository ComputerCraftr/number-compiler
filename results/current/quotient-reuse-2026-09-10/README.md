# Bounded quotient reuse and unit runtime — September 10, 2026

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

This change connects already compiled parametric interfaces to directed transfer
requests and removes unnecessary one-symbol tile construction. It does **not**
implement active successor-closed future classes for arbitrary composed
reverse/add consumers. The release remains blocked on that work and its scaling
and full-suite acceptance gates.

## Production changes

- A directed transfer first probes its existing concrete result, then an
  already published parametric parent interface before descending. The latter
  covers all incoming states and both directions; the normal validating lookup
  and atomic result publication remain in use. No new persistent cache or
  uncharged behavior store is introduced.
- A primitive causal `advance_symbol` executes the admitted finite transition
  directly. Composite states keep their existing typed causal-prefix route.
  Direct transitions are counted, including repeated evaluations previously
  hidden behind the one-symbol directed memo.
- Semantic identity validation traverses container DAGs while checking scalar
  table cells in place. Cycle rejection, bounded integers, forbidden-payload
  checks, canonical digests and structural equality remain intact.
- Port assignment validation avoids allocating a new `PortVariable` per
  decision bit. Coordinate validation still runs through its canonical owner,
  whose scalar checks no longer allocate a generator.
- The optional timing trace now retains at most 32,768 phase records, within
  the unchanged 8 MiB cap. The previous 8,192 cap truncated before the unit
  suite's slow tail. No test selection, assertion, runtime budget or watchdog
  has been relaxed.

The source edits are available as a reviewable patch (local artifact: `changes.patch`).

## Cold cancellation and negative control

The two supplied cancellation witnesses now have cold regressions for one- and
two-step producers followed by a primitive carry observer. Neither producer's
exact successor is prepared. The tests prohibit `scheduler.complete`,
`_complete_direct`, and successor leaf construction, and assert zero completed
result publications and exact boundary-output completions. Original-source
interfaces and retention of an existing blank padding leaf are permitted;
original-source boundary geometry may still be normalized.

The resulting `ReverseBoundOutput` values compare equal despite different
source sector summaries. These are bounded observation values, not newly
certified `FutureBehaviorClassID` values. A two-step **producer** followed by a
primitive observer does not prove a composed downstream consumer's closure.

The negative control compares 32 active 4s with
`(5, 4×14, 3, 3, 4×14, 5)`. Their polynomial difference is
`(1-z^16)(1-z^15)`, which vanishes in all four fixed source sectors. Their
current carry summaries also agree, but the next carry observations differ.
The production observation preserves that distinction with exact successor
construction poisoned. Sector or current-carry equality therefore cannot be
used as future-behavior authority.

## Cold work measurements

Fresh processes queried decimal 196 digit zero. The previous column is the
historical September 10 single-process diagnostic; the new column is this
change's public-path single-process measurement. Times are engineering samples,
not repeated release statistics.

| Metric | N=32 previous | N=32 new | N=64 previous | N=64 new |
|---|---:|---:|---:|---:|
| Query seconds | 4.4505 | 4.0143 | 15.8317 | 14.7675 |
| Directed leaf evaluations | 188 | 35 | 379 | 40 |
| Directed parent compositions | 409 | 341 | 1,209 | 1,003 |
| Parametric interface transfer hits | 0 | 221 | 0 | 545 |
| Primitive transition evaluations | 1,255 | 1,606 | 1,446 | 2,367 |
| Causal frames | 53,396 | 53,396 | 184,754 | 184,754 |
| Peak canonical tiles | 956 | 956 | 3,841 | 3,841 |

Replacing memoized one-symbol tile transfers with direct finite operations
increases the counted primitive transitions while reducing allocation and
validation overhead. The unchanged causal-frame and tile curves remain
superlinear over this doubling. This is a constant-factor improvement, not
composed-consumer discharge or sublinear execution.

The public32 (local artifact: `diagnostics/public32.log`) and
public64 (local artifact: `diagnostics/public64.log`) records retain every counter. Separate
`cold_row` benchmark records use that benchmark's own action construction and
are preserved as diagnostics; their different frame counts are not substituted
for the public-path comparison above.

## Validation

The baseline serial unit attempt timed out at 300.05 seconds, with a sampled
peak footprint of 554,795,896 bytes. Its optional phase trace is explicitly
truncated and cannot establish complete coverage.

The first modified diagnostic run completed: **4,110 passed, 918 deselected in
288.87 seconds**, with a sampled peak footprint of 559,022,968 bytes. Its 12,330
phase records are complete. This precedes the last port-coordinate adjustment
and the five new cold cancellation cases; final validation is recorded below.

- Focused causal boundary and ownership regressions: 106 passed in 3.31 seconds.
- Cold cancellation and equal-sector negative control: 5 passed in 1.53 seconds.
- Strict nonincremental mypy: 1,076 source files clean.
- Ruff: checks pass; 1,204 files formatted.
- Repository policy: no line-count, recursion or package violations.

All runtime probes use one guarded worker group at a time, a 1 GiB sampled
physical-footprint limit, and the existing deadlines. Unit evidence remains
separate from exhaustive validation and the full release manifest.

### Final frozen unit result

The final unprofiled serial unit run passes **4,115 tests in 278.27 seconds**,
with 918 validation tests deselected. The guard completed in 279.28 seconds
and sampled a peak physical footprint of 566,297,464 bytes (about 540 MiB).
The unchanged 300-second deadline therefore passes with roughly 21 seconds
of process-level margin; this remains a substantial unit runtime.

JUnit evidence (local artifact: `unit.xml`) records `serial-unit`, exactly 4,115 selected node
IDs, zero failures/errors, and matching before/after/current source fingerprint:

`df562a845115fb4adadb36dc3232730d1a82b3c88fbee3eb5740bed0c661d78c`

The guard record (local artifact: `unit.guard.json`) and unit log (local artifact: `unit.log`) retain the timing,
resource measurement and slowest tests. No full unfiltered release run or
N=128…1024 scaling acceptance is claimed.
