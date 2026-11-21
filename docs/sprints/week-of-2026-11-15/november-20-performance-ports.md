# November 20 carry and scheduler performance ports

Period: 2026-11-15 through 2026-11-21 (Sunday–Saturday).

[Week index](README.md)

## Objective

The development checkout was based on Git `df533a4b45acf41a6df307998e0d8be38ed30956`
with the reversal sprint already in progress. The downloaded patches used
several distinct predecessors. The objective was to port their bounded
carry and scheduler improvements into the existing query owners.

## Changes

### NC41 reconciliation

The port starts from `02fefff9`. The guarded baseline selection recorded
1,585 passes and two existing compact comma admission failures. Performance
comparisons use the same baseline source and exact receiving queries.

- The C0 and upper-band donors overlap on reflected-H transport. Reversal
  keeps the latest packed producer and admits the palindrome scan only on
  event demand. Reusable Q19 checkpoints retain exact source-qualified
  continuations under the receiving owner's scratch budget.
- The Antihydra nonretaining leaf combines the live repeat probe with the
  bounded eight-step sheet. The upper affine action projects the value.
  Its lower support graph still owns source admission and ordered safety.
  The NC31 donor contributes a finite guard projection through the existing
  arithmetic owner. An unavailable fractional guard remains incomplete.
- The Collatz donors contribute bounded cyclic rows before scalar discovery
  and a single demanded carry evaluator for the simultaneous event. Complete
  repeat copies use the defect certificate. The exact executor handles the
  remaining ticks.
- Prime retains the short-relative scan and reduces progression rank only
  over its certified consecutive prime prefix. The power-number consumers
  share an ordered affine response and retain their distinct source guards.
- The CLI registry groups residue, clock, accumulator and closed-form
  results by view. The 2rev10 residue, period and Laurent views share one
  issued source action when the selected endpoint agrees. A residue-only
  request builds neither the period walk nor the accumulator.

### NC41 validation and measured work

These are development runs against Git `02fefff9` with the integration
changes in the working tree. The guarded default suite
`results/nc41-final-units` completed in 230.05 seconds under the 300-second
limit. Collection took 13.94 seconds. Peak aggregate memory was 465.8 MiB
and descendant cleanup was confirmed. The suite
recorded 13,049 passes and six failures from missing global comma admission.
The affected-family selection
`20261121T034922Z-8054e1e0f74341bc86a747d32261dee1` passed all 3,575 tests.
The guarded P0 run `20261121T034027Z-4bd8d3cb89774cf39626e5f85d9a3d56`
recorded 75 passes and 15 failures across comma admission, Antihydra
non-halting, and the Fermat and Mersenne prime-bit obligations. The same
15 cases failed in the fresh detached baseline at `02fefff9`.

Strict Pyright covered all 2,572 maintained Python files in 103 serial
batches with zero diagnostics. Strict mypy, Ruff, formatting,
dependency consistency, source policy, and documentation checks passed.
The built wheel passed independent installed CLI checks for prime,
2rev10, Collatz, and Antihydra. The official package gate still requires
the admitted global comma future. The proof index still reports an
unsupported comma dependency-audit invocation.

The combined native run `20261121T033725Z-26d18c69ed454452bdeed65358e7c8ef`
rebuilt `Temporal_Clock_Jumps` in 39 seconds. The Fermat affine row and
Mersenne two-child lift passed with the theorem-oracle audit active. The
combined run reused the other requested heaps. Earlier focused builds rebuilt
`Double_Reverse_Temporal_Refinement` in 199 seconds,
`Collatz_Cylinder_Refinement` in 41 seconds, `Antihydra` in 25 seconds, and
`Prime_Selection_Initialization` in 8 seconds.

Five interleaved matched trials compared identical successful results with
the baseline. The performance claims apply to these receiving workloads.

| Workload | Baseline median | Integrated median | Executed work |
| --- | ---: | ---: | --- |
| Q19 receiving horizon 532 after priming 1,024 | 1.65 ms | 0.12 ms | 520 → 8 physical transitions |
| Prime progression through 1,000,000, modulus 16 and residue 3 | 171.64 ms | 78.11 ms | 42,071 → 16,634 memo states |
| Mersenne exponent 31, 128 trace ticks, decimal place 8 | 9.19 ms | 7.28 ms | 18 → 11 trace power calls |
| Collatz simultaneous carry event, odd headroom 128 | 0.95 ms | 0.28 ms | One ordered source fold, earliest hit 128 |
| Antihydra return 3,072, embedded cache bypass | 6.78 ms | 3.52 ms | Exact value matched the warmed query |
| 2rev10 generation 512 with residue, period and accumulator | 168.77 ms | 162.20 ms | One shared source admission |

Ordinary fresh CLI results matched across all six measured families. Their
query CPU medians were within 3.3 ms of the baseline with variable startup
times. The Q19 and prime progression results measure specific reuse and
rank paths.

### Guarded carry and checkpoint follow-up

The live Fermat matrix authenticates its source once per ordered batch,
checks the CRT and radial ports at each checkpoint, and reuses the matrix's
computed endpoint residues. The binary SLP join folds the signed high and
low components in one pass and keeps the canonical minus-one residue.
`Temporal_Clock_Jumps` rebuilt in 38 seconds with the source, congruence and
canonical-range theorems. The matched nine-checkpoint probe cut source
authentications from 18 to one and the median from 70.79 ms to 3.95 ms.
At width 1,024, 300 signed joins took 0.321 ms with the generic fold and
0.255 ms with the direct fold.

The bounded Fermat fixed-multiplier halo now publishes through
`temporal.matrix` with kind `negacyclic`. It authenticates the selected
exact exponent root, then computes the endpoint residue and wrap quotient
bits together. `results/nc41-phase3-fermat-proof-8` rebuilt
`Temporal_Clock_Jumps` in 63 seconds with the packed quotient, signed inlet
and source endpoint theorems. The guarded `results/nc41-phase3-cli-focused`
development run passed 159 tests, including the public 4,096-tick endpoint
and the lazy ordinary-matrix and metrics routes. The wrap is relative to the
canonical source residue. Raw unreduced carry, cyclic motif discovery and
primality remain separate obligations.

The reflected SLP publisher now searches the demanded zero edges without
walking a nonzero grammar interior. The even `2rev10` emission uses both
edge counts for a single slice before the final multiply. The registered
`Double_Reverse_Temporal_Refinement` session passed in 169 seconds in
`results/nc41-reflected-native-endpoints-2`. It checked decimal inlet packing,
ordered carry seams, padding normalization, and the exact odd and even
physical endpoints for both multipliers. Five interleaved fresh-process
trials per workload matched all endpoint hashes and widths. The SLP
publisher was 2–47% slower on the measured 3-, 135- and 800-digit sources at
128–257 ticks. Automatic dispatch retains the existing publisher.

The `5rev10` adapter uses packed pairs from the authenticated receiving value
for spans of at least 1,024 ticks on uncapped ledgers, after the padded-cone
selection. It checks the original state-bit bound at each physical tick and
reports executed pairs separately from logical digit counts. The registered
`Five_Reverse` build in `results/nc41-packed-five-native-budget-final`
finished in 126 seconds. It checked the whole-word masks, normalization,
pair result, first refusal, BCD preservation, bit-width bounds and physical
odd reflection. Differential tests cover the runtime's lexicographic prefix
check using the proved interval bounds. The guarded
`results/nc41-packed-live-adversarial.log` matched 6,012 exact values, first
refusals and work-counter cases against literal stepping.

Five-trial public query comparisons matched all 150 CLI values at 16, 64,
256, 1,024 and 4,096 ticks on seeds 73 and 196. At 4,096 ticks, cold medians
fell from 166.40 to 133.25 ms and from 161.74 to 135.10 ms. Warm and cache
bypass medians fell by about 84%. At 1,024 ticks, warm and bypass medians
fell by about 60% and cold medians were within 0.4% of baseline. The short
requests still use the scalar route.

The broader `results/nc41-reversal-fermat-guarded` selection passed 1,286
tests in 23.43 seconds under the guard. This covered the shared carry
arithmetic, both reversal families, local reflected transitions and the
Fermat CLI.

After the packed CLI cutover, the guarded default suite
`results/nc41-packed-live-full-units` finished in 236.77 seconds, including
14.24 seconds of collection, with 457.0 MiB peak aggregate memory and
confirmed descendant cleanup. It recorded 13,198 passes. The six failed
test nodes matched the prior missing-global-comma failures exactly.
Strict mypy, the affected Pyright batch, Ruff, formatting, source policy,
documentation and dependency checks passed. An isolated wheel installation
matched the packed `5rev10` value and counters and the Fermat halo output in
`results/nc41-packed-live-installed-final.log`. The full wheel gate still
requires the global comma future asset.

`temporal.carry-bellman` now reports the corrected Collatz ×3 lane alongside
the homogeneous event. The same ordered fold serves both result fields.
The exact dyadic headroom determines the correction to the carry at each
cut. The terminal numerator retains the moving subtraction. The physical
endpoint and carry theorems rebuilt in `Collatz_Cylinder_Refinement` in
27 seconds. A cold query-CPU probe against `02fefff9` measured 196 ms
before and 209 ms with the additional corrected result.

The demanded Antihydra ledger guard now returns the exact empty fractional
interval for every authenticated source-7 horizon of at least two. The
two-step interval collapse removes the need to replay a longer source.
`Mahler_Source_Transport` rebuilt in 11 seconds, after its safety
prerequisite rebuilt. The arithmetic first-failure calculation still
describes the physical ledger.

The guarded affected-family selection in `results/nc41-phase2-affected`
passed all 2,272 tests. It includes the corrected carry event at the
function and CLI boundaries, the complete longer fractional guard, and
the checkpoint and signed-phase regression suites.
The earlier P0 run reproduced the baseline's 75 passes and 15 failures.
Strict mypy,
four serial changed-file Pyright batches, Ruff, formatting, source
policy and documentation passed.

### Earlier ports in the same sprint

- Shared dyadic carry observations transport the full inlet through disjoint
  intervals, then reduce at the requested cuts. A single subtraction provides
  the internal borrow bits. The highest outlet uses the full-window underflow.
  Compact ordinary ×3 ports fold the ×2, ×3 and ×6 streams in digit order.
- The two padded reversal kernels use a small finite lookup derived from the
  predecessor ports. Tight scratch budgets can use the original cell law.
  Reverse/add can continue from the farthest completed Q19 image, and double
  reverse can reuse the already-issued C0 entry past the short probe.
- Antihydra checks whether its source admits at least three copies of an
  eight-step or four-step block. The four-step candidate reuses the midpoint
  of the eight-step probe when both are tried. Repeat powering preserves the
  safety prefix and ledger. Mixed-word Mahler recovery assigns each innovation
  its final chronological weight as it is emitted.
- The Collatz carry observation uses the selected query's normalized endpoint
  and checks the entire odd suffix before testing joint homogeneous carry
  parity. Its stopping conditions are the first joint hit, the requested
  horizon and a complete phase period. Ordinary term queries do no such work.
- Prime phase-block powering sums one finite rotation orbit. Short relative
  prime queries scan the coprime residue classes modulo 210 before building a
  rank interval or XOR image. Each batch uses the already-admitted prime
  prefix through the square root of its largest candidate. The progression
  count handles factors shared with the modulus without modular inverses.
- The residue audit found duplicated work in 2rev10 and Antihydra/Mahler.
  2rev10 derives the reported mod-18 fields from the corresponding mod-90
  orientations and uses one mod-198 value per SLP node. The mixed-adic
  observer reuses its mod-1980 projection and checks field returns in the
  states that determine the orientations. Mahler folds each exterior once
  modulo 198 and projects modulo 99. Its halving step retains source
  precision modulo 396. Combined Antihydra tape and factor observations
  share one typed projection and one assembly of its reporting fields. The
  factor calculation runs only when requested.

## Established results

The carry scans preserve repeated and out-of-order demands and the exact
terminal borrow. The Q19 frontier resumes growth from an authenticated
completed image. The all-odd Collatz guard and the Antihydra repeated
endpoint have executable producer tests and kernel theorems. Literal
Antihydra comparisons cover all 16 four-step parity phases. Independent
sieve comparisons cover the short relative prime selection.

## Matched measurements

The timing rows below compare exact equal outputs. CLI calls in a live process
include query and rendering work. Kernel rows measure the indicated producer
without interpreter startup.

| Workload | Prior median | Updated median |
| --- | ---: | ---: |
| Embedded CLI, 5rev10 seed 73 at 1,024 ticks | 33.59 ms | 3.89 ms |
| Embedded CLI, 5rev10 seed 73 at 2,048 ticks | 153.05 ms | 9.75 ms |
| Embedded CLI, reverse/add seed 196 at 4,096 ticks after 1,024 and 2,048 | 60.04 ms | 50.72 ms |
| Cache-bypassed embedded CLI, reverse/add seed 196 at 4,096 ticks | 66.65 ms | 57.80 ms |
| Prime successor kernel at 10,000,000, shared cache bypassed | 118.95 ms | 108.32 ms |
| Prime phase block with 257 lanes raised to the power 10⁴⁰ | 20.75 ms | 0.099 ms |
| Antihydra 128-step admitted repeated word, punctured scheduler method | 105.58 µs | 4.83 µs |
| Dyadic carry frontier with 4,097 requested cuts | 5.37 ms | 2.83 ms |
| Dyadic borrow frontier with 4,097 requested cuts | 6.36 ms | 5.18 ms |
| Compact ordinary ×3 ports with 64 decimal places | 66.75 µs | 40.00 µs |
| ×2 reflected-H endpoint kernel on a 144-digit seed at 256 ticks | 7.74 ms | 6.96 ms |
| ×5 reflected-H endpoint kernel on a 144-digit seed at 1,024 ticks | 65.37 ms | 53.57 ms |

Extending the Q19 requests at 2,048 and 4,096 ticks executed 1,024 and 2,048
successor steps instead of 2,035 and 4,083. The Antihydra scheduler joined 65
segments into one. Its benchmark source is the 128-bit residue of
`(3**8 * 39 - 256 * h8) / (3**8 - 256)`, with division interpreted in
`Z/(2**128)` and `h8` the result of eight physical steps from 39.

### Four-step Antihydra and relative prime scan

The follow-up compared five interleaved fresh processes per CLI workload
against the preceding sprint build. Independent arithmetic checked each
output. Charged work is the runtime counter for the reported prime query.

| Prime start | Index | Prior median | Updated median | Charged work before → after |
| ---: | ---: | ---: | ---: | ---: |
| 10,000,000 | 0 | 242.24 ms | 129.00 ms | 391,564 → 10,505 |
| 1,000,000 | 20 | 171.98 ms | 125.81 ms | 120,185 → 6,578 |
| 1,000,000 | 0 | 155.76 ms | 128.68 ms | 63,794 → 2,664 |
| 100,000 | 128 | 148.74 ms | 135.47 ms | 62,346 → 11,813 |
| 10,000 | 0 | 133.53 ms | 130.80 ms | 2,849 → 203 |

The two start-2 rank controls performed identical charged work. Their
medians moved from 151.07 to 142.76 ms at index 1,000 and from 159.32 to
164.28 ms at index 3,000. The Antihydra scheduler emitted 40 segments instead
of 48 from source 7,058 over 128 physical ticks. Its method median across nine
warm samples fell from 72.12 to 59.42 μs. The default Antihydra CLI source
showed no consistent speedup across indices 128, 1,024 and 3,072.

## Rejected approaches

The earliest-hit carry query can settle from the first certified period and
returns as soon as the event is found. Compiling the whole period into a DAG
for this single demand would visit additional phases.

One wide, 1,024-tick 5rev10 source still favored the scalar constructor in a
fresh-process comparison. The wide-source HashLife admission continues to
provide an endpoint without chronological advancement. The 5rev10 seed-73
results above measure the bounded scalar decimal conversion route.

The Antihydra archive builds a motif catalogue on top of a carry table. The
current scheduler already captures the needed four-step summary during its
eight-step source probe. The short relative prime scan consumes the committed
coverage certificate, so a separate rank query at the same square-root
boundary would repeat work. The superseded XOR route was removed from ordinary
prime selection, and the explicit XOR arithmetic retains its own checks.

## Validation provenance

The integrated Python selection
`20261120T230213Z-777d54017ac04d32b8cf2d7607979935` passed all 302 tests, including
the 20,000 independently checked reflected local transitions, the 8,256-tick
Q19 producer, the bounded prime selector, Antihydra repeat and budget cases,
and the public Collatz observer.

The native run `20261120T231310Z-2ff7eaff20a14dd2a019cec68962405d` passed the
combined session selection. It rebuilt Antihydra in 30 seconds,
Collatz_Cylinder_Refinement in 33 seconds, and Reverse_Growth_Admission in
18 seconds. The shared, double-reverse, five-reverse and prime heaps were
reused. In the preceding run the shared carry session rebuilt in 46 seconds,
double reverse in 126 seconds, and five reverse in 122 seconds. The prime
wheel bridge rebuilt in 8 seconds during the earlier focused proof wave.
Run `20261120T231929Z-a333f3f9a2b744efa4fd29b8b6428667` then rebuilt
Reverse_Growth_Admission in 17 seconds with the exact packed expression
used by the production radix-64 carry sweep.

The follow-up Antihydra run
`20261121T000936Z-57da5014e6cb45589f02ea724e1eebb0` rebuilt in 22 seconds.
It checked repeat endpoint transport, ordered rotated corrections and prefix
minima, and the original-source guard pullback with the rotated seam and an
explicit modular inverse. The prime run
`20261121T000815Z-50c57c1291744092bcf4b81c0313b01c` rebuilt
Prime_Wheel_Bridge in 10 seconds, Prime_Deterministic_Refinement in 13 seconds,
and Prime_Selection_Initialization in 7 seconds. The prime proof equates the
covered wheel filter with the ordered prime subsequence. The executable tests
exercise candidate enumeration, batch boundaries and source authentication.

The guarded Antihydra, prime and CLI selection
`20261121T001011Z-2fc96403630b4cf8b8fd634bc62ecbb0` passed all 767 tests.
It covered all four-step parity phases, source guard and prefix safety,
prime square boundaries, retained source authority and refusal budgets.

The guarded P0 selection `20261120T232003Z-8ee16b79b26340f8866605b044c71d0e`
passed 48 tests. A clean installation of the built wheel matched five exact
CLI checks for reverse/add, five reverse, Antihydra, prime and the Collatz
carry observation. Whole-tree mypy, Ruff, formatting, source policy and the
documentation index passed. The affected strict Pyright batches produced
zero diagnostics.

The focused parser and Collatz observer run
`20261120T232431Z-1dde640b22814977acbc8f75af2e0498` passed all 47 tests.

Both selected Antihydra P0 runtime tests passed in
`20261121T001704Z-18f09a460f994f0fbcedf0e267018160`. A fresh installation of
the rebuilt wheel matched the exact prime and Antihydra CLI values. The
repository proof-index check still rejects the comma dependency-audit
invocation in `Comma_Continue_Frontier24_Source_Bridge`. The full packaging
gate requires the absent global comma future asset.

The residue follow-up rebuilt Double_Reverse_Temporal_Refinement in 125
seconds under the four-thread guard in
`20261121T002124Z-88a54c5630cf4606a1f52b960b93f546`. The new consumer
corollary projects mod 18 from the existing mod-90 word theorem using the
shared divisibility law.

The guarded audit selection
`20261121T002702Z-163a583a5e5c4577ab5fb1e4a56b6d1e` passed all 1,712 tests
in 32.47 seconds. The regressions count one orientation construction per
field, one mod-198 fold per Mahler exterior segment, and one Antihydra tape
projection and field assembly per combined request.

The earlier default unit run
`20261121T002919Z-7628ca3afc754936a14668cef46d59dd` completed in 235.60 seconds
under the guard and peaked at 439.7 MiB. It recorded 12,913 passes and the six
existing global comma admission failures. Strict mypy, the affected Pyright
batch, Ruff, formatting, source policy and documentation checks passed.

The guarded 2rev10 work-counter regression now exercises both the certified
low-band digit and an interior stencil digit. Its previous coordinate was
served by the low-band projection and could not measure stencil publication.

## Remaining work

The accepted Antihydra inductions establish the conditional repeated
physical endpoint and geometric gain. The source prefilter has its own
modular transport theorem. The complete refinement from valuation-selected
capacity and every repeated prefix minimum remains open.

The Collatz observation takes one homogeneous same-time event demand and
stops scanning as soon as the answer is settled. A reusable corrected
mixed-parity carry DAG still needs source and clock authority. The full
Antihydra three-ID quotient, prime XOR first-birth theorem and prime
circular-histogram power theorem also remain open.
