# Exact factored 196 carrier

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

The new endpoint carrier stores independent LT/EQ/GT, F5, and Boolean-half
grammar roots. Its primitive successor derives carries from the domain
grammar, updates the three channels, and never constructs a decimal digit
word or a 19-symbol pair field. The [architecture contract](../../../docs/architecture/reverse-factored-carrier.md)
describes the APIs, equality, ownership, and remaining admission requirements.

This completes the proposed exact primitive carrier and its requested
measurements. It does **not** complete a compact powered 196 quotient or
establish a public compiler speedup. Source-bound nonlinear forcing still
requires primitive evolution, and the carrier has not been admitted to the
public point-query cache.

## Exactness and symbolic controls

The first exhaustive sweep checked all **209,960** admissible symmetric pair
fields of widths one through eight. Counts by width are 10, 19, 190, 361,
3,610, 6,859, 68,590, and 130,321. Every result and growth bit matched the
independent `pair_step` oracle, with pair decoding/re-encoding poisoned during
the successor. The final frozen-source pytest replay is recorded separately
as `final-exhaustive-*.xml`; these validation tests are excluded from the
ordinary unit selection.

The final replay passes all 44 partition tests on the frozen source
fingerprint. Their aggregate pytest time is 424.284 seconds; the largest
guarded group takes 25.649 seconds and the largest sampled footprint is
67,961,360 bytes. This is exhaustive subsystem evidence, not a complete
unfiltered release-suite run. `exhaustive-summary.json` records coverage and
the matching before/after source identities.

Ordinary regressions additionally poison pair/digit import and decoding,
the coordinate decoder, and expanded word construction; counted leaves may
contain only atoms below five. They advance
`2^L -> 4^L -> 8^L -> 16^L -> 7 14^(L-1) 7` at lengths 1, 4, one million,
and `10^100`. The three initial planes each have one node. After growth each
plane has at most four distinct nodes, including its concat structure.
The notation denotes repeated pair coefficients, not exponentiation.

`uniform-million.log` and `uniform-huge.log` preserve additional symbolic
measurements. At length one the two equal growth edges coalesce. The unit
tests also find distinct source carriers with identical canonical output
planes, proving that output identity does not require equality of input IDs.

## Plane measurements for seed 196

Every one of 1,024 primitive successors agrees with the independent oracle.
The following are distinct nodes in each plane, not reconstructed pair-word
runs and not certified finite temporal quotient classes.

| Events | Width | Domain nodes | F5 nodes | Boolean nodes | Combined macrocell residuals |
|---:|---:|---:|---:|---:|---:|
| 16 | 9 | 4 | 12 | 4 | 13 |
| 32 | 16 | 14 | 15 | 9 | 20 |
| 64 | 31 | 26 | 17 | 16 | 36 |
| 128 | 58 | 35 | 51 | 22 | 71 |
| 256 | 113 | 55 | 86 | 48 | 125 |
| 512 | 222 | 113 | 145 | 76 | 220 |
| 1024 | 421 | 158 | 236 | 124 | 384 |

The combined count interns aligned interval triples while walking the three
grammars. It never constructs a 19-symbol grammar. Independently counted
plane nodes can share underlying canonical-word nodes; their sum is not a
measurement of exclusive memory ownership.

The F5 plane has the largest node count at 1,024 events. This does not support
assuming the Boolean plane is already the dominant source of fragmentation.
Neither these counts nor the modest observed grammar reuse establish an
entropy lower bound or an asymptotic compression guarantee.

The 1,024-event result used successive endpoint checkpoints at 512, 640, 768,
896, and 1,024. Each archive stores three coordinate DAG roots, never a joint
pair field. Each resumed state is independently checked against the original
seed's oracle orbit before continuing. Cumulative measured execution was
**72.983 seconds**, excluding process starts and resume verification. This is
not a single run passing the 35-second guard.

## Temporal composition

`FactoredTemporalPower` composes exact source-bound segment actions. Its F5
action is `(A, f)`, with composition `(A2*A1, A2*f1+f2)`. It pads earlier
forcing and the segment source to the final growth width, applies the
cumulative operator through Frobenius factors, and requires equality with
the primitive endpoint before accepting the composed F5 plane.

Checkpoints 1, 2, 4, 8, 16, 32, 64, and 128 agree with the oracle. The
128-event homogeneous action has 55 growths, represented by Frobenius
factors `(5,1)` and `(25,2)`: three shift/add factors. Its forcing plane has
44 nodes. This is actual cumulative F5 application in the temporal executor,
not merely a standalone polynomial test.

The run still performs **128 primitive successors**, because domain/Boolean
forcing is unresolved. Its measured 1.331 seconds does not improve on the
ordinary 128-event trajectory's 0.968 seconds. A separately tested
`(I+S)^(5^40)` homogeneous action uses one shift/add without enumerating its
power. Neither result makes dynamic forcing disappear.

## Isabelle scope

`isabelle-ground.log` is the successful complete session build: 9.52 seconds
under the unchanged 35-second/1 GiB outer guard and 20-second session timeout.
The new theory checks transitive oracle dependencies with
`quick_and_dirty = false`.

It proves the exact normalization gates, XOR/majority gates, normalized-digit
full adder, reconstructed carry domain, and the factored arbitrary-length
four-event uniform result. The last result transports the existing proved
uniform-run theorem into the factored coordinates. It does not formally
verify the Python grammar implementation, arbitrary-field carrier transport,
output minimization, or a compact closed temporal representation for 196.

Earlier Isabelle logs retain an unavailable tactic error, a missing natural
type annotation, and a finite-discharge timeout. Explicit ground case
discharge fixed the last issue without increasing resource limits. Authored
`.thy` files now share the repository's 1,000-line source cap; Python recursion
analysis remains restricted to Python source.

## Memory correction and failed probes

Weak memo values were insufficient to retire rope-operation keys when their
operand died but a shared result remained live. `prune_stale_program_word_memos`
now removes keys with expired operands while retaining live hits. Endpoint
observations also release their independent temporary work on success/error.

The pre-pruning longer probe reached approximately 693 MB sampled peak.
Pruning reduced the comparable timed-out probe to approximately 58 MB. The
successful segmented continuation remained below 64 MB sampled group
footprint. These are sampled physical-footprint measurements, not hard caps.

`trajectory1024.guard.json`, `trajectory1024-retry.guard.json`, and
`trajectory1024-pruned.guard.json` preserve the failed 35-second probes. They
are not successful release/scaling evidence. The segmented result is reported
separately above.

## Final ordinary unit gate

The complete serial unit selection passes **4,247 tests in 269.00 seconds**,
with 970 validation tests deselected. The unchanged 300-second guard finishes
in 269.627 seconds at 628,556,712 bytes sampled peak footprint. The 24 new
arithmetic/carrier test cases account for 0.328 seconds of summed testcase
time; that sum excludes session/collection overhead. One additional regression
covers the Isabelle source-size policy.

The unit and all 44 exhaustive partition reports have matching before/after
and current source fingerprints:
`2bd6ff615ac9d53630bc3d6ebd9105882461f4677bd5b03d6ad24117e5dc3e17`.
Strict nonincremental mypy passes for 1,112 Python files; repository-wide Ruff,
changed-file formatting, and structural policy pass. The previous unit run
took 276.75 seconds. This single comparison does not establish a sustained
speedup. No full unfiltered release-suite result is claimed.

## Reproduction commands

Run one guarded process group at a time and use fresh output paths:

```bash
.venv/bin/python -m devtools.checks.process_guard \
  --output /tmp/factored-width8.log --report /tmp/factored-width8.guard.json -- \
  .venv/bin/python -m pytest -m validation -q \
  'tests/validation/proofs/reverse_add/test_factored_carrier_exhaustive.py::test_factored_successor_all_symmetric_fields[8-0]'

.venv/bin/python -m devtools.checks.process_guard \
  --output /tmp/factored-power.log --report /tmp/factored-power.guard.json -- \
  .venv/bin/python -m devtools.proofs.reverse_factored_carrier \
  trajectory --steps 128 --squaring

.venv/bin/python -m devtools.checks.process_guard \
  --output /tmp/factored-isabelle.log --report /tmp/factored-isabelle.guard.json -- \
  /Applications/Isabelle2025-2.app/bin/isabelle env \
  'ISABELLE_TOOL_JAVA_OPTIONS=-Xms64m -Xmx256m -Xss4m' \
  'ML_OPTIONS32=--minheap 100 --maxheap 450' \
  /Applications/Isabelle2025-2.app/bin/isabelle build \
  -v -j 1 -o timeout=20 -D devtools/proofs/isabelle
```

The width-eight example is one of nineteen partitions. The complete sweep
also includes the other first coefficients and widths one through seven.
The manifest records the final test and source identities; earlier probe
results remain diagnostic evidence for their recorded stages.
