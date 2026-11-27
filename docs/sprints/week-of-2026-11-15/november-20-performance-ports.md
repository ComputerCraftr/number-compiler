# November 20 carry and scheduler performance ports

Period: 2026-11-15 through 2026-11-21 (Sunday–Saturday).

[Week index](README.md)

## Objective

The development checkout was based on Git `df533a4b45acf41a6df307998e0d8be38ed30956`
with the reversal sprint already in progress. The downloaded patches used
several distinct predecessors. The objective was to port their bounded
carry and scheduler improvements into the existing query owners.

## Changes

### Bounded CF and reversal delivery on local main

The eight-row CF terminal (`36d3226c`) passed all 57,600 lift and clip
comparisons. The two installed band controls used lifts 370 and 1099.
The five-inlet trial stays outside dispatch on `15,4,1,14`. It increased
median owner time from 12.16 to 22.33 µs and peak ledger nodes from 168
to 944. Reciprocal CF source authentication landed in `500cba34`.

The optional C++ wheel builds one bounded reflected ×2 kernel with
`NUMBER_COMPILER_BUILD_REFLECTED_MULTIPLY=1`. On that wheel,
`NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY=1` opts into eligible C0
actions. Python remains the default. With seed 73 at 1,024 ticks the
installed CLI entered the kernel three times and matched the literal
endpoint. The same wheel made zero native calls with the opt-in disabled
and zero on the enabled 16-tick request. Five alternating cold pairs at
1,024 ticks measured medians of 250.15 ms for Python and 253.93 ms with
the kernel enabled. On the combined wheel from `5d964b18`, five fresh
pairs measured 186.70 ms and 181.63 ms respectively. The 16-tick
control, which takes the Python route in both modes, measured 161.02 ms
and 161.37 ms. Automatic dispatch remains disabled.

Both the pure and opt-in wheels built from `5d964b18` passed fresh
installed console-script checks on macOS and Linux ARM64. The cylinder
used 540 coefficients at horizon 4,096. The multiplier and reverse/add
checks compared physical endpoints against literal decimal arithmetic.
The combined changed Python test selection passed 219 tests. The
registered `Mahler_Source_Transport` build passed in 148.58 seconds on
the combined CF proof tree.

### November 27 production CLI follow-up

The receiving revision was `a6ad6056`. The default CF cylinder now issues
settled actions through the fifth power of five. At horizon 64 this
eliminated all five spatial trace calls. At 4,096 the count fell from
eleven to nine. The wider reciprocal route and all new native routes
are opt-in. Limited CF ledgers retain the pointed fallback.

| Installed query | Verified execution | Matched medians |
| --- | --- | --- |
| CF at 4,096 ticks (`c5e657c1`, `a907a69b`) | The reciprocal owner used 40 cuts and eliminated 34 spatial rows and 14 leaf builds. Both packets selected 540 coefficients. | Cold CLI 124.68 → 123.02 ms. |
| Native CF at 4,096 ticks (`1161479f`, `aa839254`) | 20 native calls replaced 203 individual digit factors with 97 two-digit actions and nine leading digits. Ten calls qualified for two-lane Arm NEON. At 63 ticks the CLI made zero native calls. | Native scalar → SIMD cold CLI 129.89 → 128.61 ms on the quiet confirmation, 141.56 → 147.67 ms under load. |
| Wide non-C0 `2rev10`, 153 digits, 4,096 ticks (`2eafa4c8`, `30bc7d69`) | 1,273,772 Python primitive transitions → 535,711 native tile lookups and 4,710 fringe gates. | Cold CLI 955.70 ms Python, 199.32 ms native scalar, 191.92 ms Arm NEON. |
| `2rev10`, framed period-13 source, 128 ticks (`470ff98f`) | A source-side two-tick check reduced interior tile lookups from 16,513 to 4,439 and fringe gates from 6,011 to 1,694. | Kernel 40.09 → 19.83 µs. Cold CLI 173.22 → 174.36 ms. |
| `5rev10`, seed 73, 1,024 ticks (`67cd2185`) | 512 Python packed pairs → 13,803 native tiles and 486 fringe gates. | Owner 1.057 → 0.456 ms. Cold CLI 113.35 → 114.63 ms. At 512 ticks cold CLI was 113.06 → 121.35 ms. |
| `reverse-add`, seed 196 (`4846844e`, `8e7e2145`, `3e2ff847`) | H12 supplied the first 12 carry-window ticks. At 1,024 the continuation issued 506 native causal bands. Q19 now packs both receiving paths through the same streaming function. | Warm extension from 1,024 to 2,048 ticks 11.56 → 7.20 ms. |

Build the general reversal extension with `NUMBER_COMPILER_BUILD_NATIVE_REVERSE=1`
and enable it with `NUMBER_COMPILER_ENABLE_NATIVE_REVERSE=1`. For native
CF, build with `NUMBER_COMPILER_BUILD_CF_CONTINUANT=1` and set both
`NUMBER_COMPILER_ENABLE_CF_RECIPROCAL=1` and
`NUMBER_COMPILER_ENABLE_CF_CONTINUANT=1`. The reciprocal option alone
works with the pure wheel. The 800-byte native CF table preserves MSD
order and leading zeros. Widths 4–9 qualify for NEON, and 10–16 use
64-bit scalar arithmetic.

The registered Isabelle builds completed in 58 s for the final shared-carry
audit, 189.5 s for double reverse, 124.3 s for five reverse, 98.8 s for
Mahler source transport and 154.9 s for reverse growth admission.
The checked relative-interior and packed-complement lemmas cover the
algebra used by the kernel. The binaries were tested against literal
arithmetic. A full source-to-four-tick folded Q19 slab, general spatial
reuse on changing CF upper bands, and end-to-end asymptotic bounds remain open.

Fresh pure and three-extension wheels at `3e2ff847` passed installed
console checks on macOS ARM64 and Linux ARM64. The checks compared
complete packets and counted actual C++ calls, including zero on
refusal. They covered nine CF horizons from 20 to 4,096, wide ×2 at
511/513/4,096 ticks, ×5 and reverse/add at 16/1,024, and the period-13
fixture. The combined guarded selection passed 331 tests. Strict mypy,
Pyright (25 files then two), Ruff and the guarded Clang checks passed.

The full default suite passed 14,058 tests in 225.07 s. All six failures
were Comma admission tests and reproduced on the receiving baseline.
Canonical P0 matched the receiving baseline by test ID, with 77 passes
and 13 failures in Comma admission, Antihydra non-halting and prime
certificates. The source-policy scan cleared the Q19 packing duplicate
and found zero recursion cycles and package violations. Its remaining
finding is the pre-existing 1,017-line double-reverse ring theory. The
global proof index still reports inherited audit and Comma authority gaps.

### Fractional branch intervals and the quiet Q19 trial after `a8755047`

On `877637fc` the finite CF cylinder selects a reusable eight-tick affine action from
40 disjoint half-open inlet intervals. Each action carries its accumulated
innovation and complete guard. Selection uses the lower inlet, then checks
both ends before composing with the receiving physical action. An upper
endpoint at a boundary is admissible. An interval straddling that boundary
returns to the exact scalar rule to find the first undecided branch.
The fixed chart is built on first admitted use, after reserving 16 KiB
of scratch. Each extension releases its optional charge before the next
source block. In `4e01c9e5`, `mahler_cf_guard_compose_exact` proves
that composition preserves both boundaries, and
`mahler_cf_chart_source_action` connects a physically admitted source
to the selected word and endpoint. The registered
`Mahler_Source_Transport` build passed in 134.17 s, including the oracle
and skipped-proof checks.

At horizon 4,096 the installed default CLI took 498 chart actions (3,984
ticks) and 50 scalar probes, down from 1,586. With a coefficient cap of
539 it stopped at physical tick 4,095 and returned `unknown` with exit
code 3. Cap 540 gave the exact full packet. Ten interleaved warm and five
cold whole-request pairs took 9.225 → 6.525 ms warm and 124.078 →
121.757 ms cold. The reciprocal opt-in used 496 chart actions and took
9.145 → 6.484 ms warm. At horizon 512 the default took 2.184 →
2.114 ms warm. A separate 40-pair timing isolated the eleven branch
extensions at horizon 4,096 and measured 5.674 → 2.936 ms per request.
Horizon 63 and caps 1, 7, and 32 used the scalar route.

A separate folded Q19 prototype recognized the four-tick `0000` clock
on perturbation 47 of the physical collar fixture. At 1,024 ticks it
entered that slab and an existing three-birth slab, covering 875 core
columns. Folded joins fell from 329,168 to 326,987, while probes rose
by 1,633 and collar-cell visits by 1,378. Sixteen interleaved batches
of ten complete native calls took 1.455 → 1.445 ms per call on the
authenticated field after the 12-tick prefix. The 0.7% improvement
missed the 5% target. Installed cold medians were 281.15 → 278.22 ms
and warm medians were 28.57 → 28.95 ms. Seed 196 retained zero slabs
and 55,857 folded joins. The existing Isabelle seam requires a first-tick
birth. The prototype stays outside production.

Fresh pure and native wheels on macOS ARM64 and Linux ARM64 under
Colima matched all 16 reference CLI packets and exit codes. The default
and reciprocal dispatch counts agreed across all four installations.
All 44 matched finite-budget checks returned the original outcome and
released their reservations. Strict mypy and Pyright, Ruff, documentation
and source policy passed. The default suite passed 14,086 tests and
retained the same six baseline failures. P0 passed 77 with the same
13 failing test IDs.

### CF acquisition and the one-birth Q19 slab after `146aa973`

On `efdfaaed`, the opt-in CF cylinder takes the first native head product
directly by left identity. The 4,096-tick packet kept 540 coefficients
and used 63 matrix joins, down from 68. All 11 acquisitions and six
clip requests together took 309.71 → 309.59 µs over 25 warm pairs.
Five installed CLI pairs took 126.97 → 127.81 ms cold and 7.30 → 7.23 ms
warm. In a separate 100-query profile, acquisition took 79 ms, including
22 ms in reservation scopes. Extending the fractional path took 641 ms.

The ordinary cylinder ends at physical width 28. The installed explicit
band `57,40,33,3` returned 99 coefficients from 33-digit heads. Both
end clips returned 66 and a fourth row refused with exit code 3.
`mahler_cf_band_selected_source_refinement` covers the moving cut,
significant width and ordered product. Advancing the installed reciprocal
owner to exponents 57–58 also issued 34- and 35-digit irregular heads
through the exact fallback. All 3,321 nonempty clips matched literal
continuants, and the ledger closed empty.

The opt-in folded Q19 kernel on `03189f14` accepts `1000` under its
checked collars. The source-clock theorem in `2509d2e8` proves the
four-tick ordered field, center, and one-digit width increase.
At 1,024 ticks, perturbation 18 of the collar fixture entered one
one-birth slab followed by one two-birth slab. Together they covered
874 core columns. Folded joins fell from 329,326 to 327,149, with
543 extra probes and 570 extra collar visits. Seed 196 at 1,024 and
the new source at 16 entered zero slabs. Two five-pair cold comparisons
gave 278.66 → 289.41 ms and 280.69 → 277.68 ms. Warm comparisons gave
28.86 → 28.70 ms and 29.04 → 28.98 ms. The confirmation's native folded
control took 278.39 ms cold and 28.63 ms warm. These measurements
support the opt-in work reduction and leave default dispatch unchanged.

On the integrated runtime, pure and native wheels passed the installed
packet and dispatch checks on macOS ARM64 and Linux ARM64 under Colima.
The registered Isabelle sessions passed (`Reverse_Growth_Admission`
26 s, `Mahler_Source_Transport` 117 s). Native Clang checks, changed-file
strict typing, Ruff, and repository source policy passed. The default
suite passed 14,079 tests and failed the same six Comma tests as the
baseline. P0 passed 77 and retained the same 13 failing test IDs.

### Final reciprocal tile and two-birth Q19 slabs after `cf8547fd`

At horizon 4,096 the opt-in reciprocal cylinder retains the first 14
ordered head prefixes of the final row plus the identity in a 480-byte
native buffer. The tile authenticates the buffer and reserves up to 105
ledger slots. Its six reads of the 22-digit irregular head became one
read at acquisition and five clipped actions during descent. The complete
540-coefficient packet matched. The existing settled suffix handles the
last six digits. Capped requests can take the previous exact route.

On the installed wheel at `40a76e15`, median final-tile acquisition
took 24.83 to 30.33 μs. The six checked segment requests, including
the first-row boundary, took 16.58 to 11.33 μs. Median combined owner
time was 41.71 to 41.92 μs. Five paired cold/warm trials took
125.37 to 125.82 ms and 7.269 to 7.253 ms. A second installed comparison
gave 128.19 to 128.10 ms and 7.221 to 7.239 ms. The registered
`Mahler_Source_Transport` theorem recovers the physical clip from the
ordered prefix matrices and their determinant signs. Dispatch is limited
to an admitted complete two-row tile with a 28–32-digit second row.

For the opt-in Q19 four-tick action, `Reverse_Growth_Admission` checked
the complete pair field, both collars, center digit and exact width
increase for chronological clocks 1010, 1001 and 1100. The compact
outer-collar clock also establishes the initial birth when the outer
pair sum is nine. The previous three-birth clocks retain their own guard.
Installed 1010 and 1100 CLI fixtures each entered a two-birth slab and
matched literal 1,024-step endpoints. On 1010 the slab consumed 437
core columns, made 544 admission probes and visited 484 collar cells.
Joins fell from 329,398 to 328,308. Five cold pairs took 275.05 to
271.99 ms. Seven same-owner pairs took 6.841 to 6.851 ms for the first
publication and 0.01183 to 0.01154 ms for a completed hit.

Seed 196 reached clocks 1010 and 0101 at generations 1,023 and 1,024.
Its longest protected folded run through generation 4,096 was eight. The
installed CLI used its folded fallback. The 1000 clock remains outside
slab dispatch. A side-four reflected trial at 4,096 ticks on the
153-digit source cut tile lookups from 535,711 to 301,530 and increased
setup from 500 to 5,000 table entries. Cold CLI rose from 188.12 to
189.61 ms and warm from 34.78 to 36.29 ms. The receiving reflected
selection remains in use.

The CF execution and proof landed in `6316930` and `40a76e15`.
The Q19 changes landed in `22d82383`, `9d4fff64` and `2e270d5b`.
Pure-Python and native wheels passed installed CLI checks on macOS and
Linux. The focused installed selection passed 51 tests. The default
suite on `c0f42c0f` passed 14,077 tests and reproduced all six baseline
failures by test ID. P0 passed 77 and reproduced its thirteen baseline
failures.

### Changing CF clips and short reflected admission after `e826457a`

The 4,096-tick reciprocal cylinder issued eleven tiles. Only the last
retained a standalone first-row product, so no later tile could consume
it. The independent six-clip displacement fixture used three shears to
recover `(5692378,1638537,927557,266995)`. Cross-exponent transport
stays outside dispatch. At the live leading cut, `0c1915a1` elides
the decimal modulus when the exact carried value already fits. The
installed cylinder skipped 29 reductions in 36 cuts and returned the same
540-coefficient packet. Five matched trials took 123.91 to 124.02 ms
cold and 7.063 to 7.032 ms warm.

The Q19 collar scan (`43a8c381`) refuses a start as soon as fewer than
64 cells remain for its protected run. This also prevents unsigned
subtraction of an exhausted candidate's endpoints. At 1,024 ticks the
installed CLI on the seed formed by repeating `809` 47 times made nine
probes, issued zero slabs, and returned the exact folded endpoint.

The existing opt-in native `5rev10` endpoint (`ec5a1789`) admits
64–127 ticks up to 512 source bits. At 64 ticks on seed 73 the installed
CLI replaced 32 packed updates with 85 tiles and 42 fringe operations,
including a 1,000-entry table setup. Five paired trials took 111.33 to
111.22 ms cold and 0.778 to 0.710 ms warm. The 153-digit fixture took
111.64 to 114.64 ms cold and 0.936 to 0.903 ms warm. The tests observed
actual native entry on admission and exact fallback at 63 ticks and
above the short band's width or budget limits.

### Irregular CF heads and wide reflected endpoints after `8fa3153f`

The opt-in reciprocal CF cylinder now sends 17–32-digit upper heads to
the bounded native continuant (`bb7adcd4`). It takes the carry from the
original inlet at the requested cut, preserves zeros at the split, and
composes the two-digit actions in coefficient order. At horizon 4,096
all 36 upper intervals were distinct. Reuse across rows occurred at the
two-digit action. Native calls rose from 21 to 33, Python digit folds
fell from 168 to 21, and cross-row repeated pair lookups rose from 33
to 82. The complete 540-coefficient packet agreed. Five paired trials
took 172.37 → 175.19 ms cold and 8.272 → 8.245 ms warm.

Wide non-C0 `2rev10` can use the existing opt-in word-RAM kernel from
256 ticks (`16fe50ac`). On the 153-digit installed CLI fixture at 256,
16,234 Python cell transitions gave way to 6,111 tile lookups and 870
fringe gates. Five paired trials took 176.45 → 171.05 ms cold and
24.97 → 11.60 ms warm. At 511 ticks the medians were 191.84 → 167.14 ms
and 38.47 → 13.11 ms. The installed CLI also checked the exact refusal
at 255 and native admission at 257. Both integrations preserve the
existing default dispatch. Isabelle checked the physical high-16 cut,
padded remainder and ordered product in `Mahler_Source_Transport`
(`51a73428`). The shared integer matrix product (`eadb93f5`) removed a
duplicate caught by the source-policy scan. The revised scan found zero
duplicates and recursion cycles. At horizon 4,096 the final refactor
took 124.81 → 125.42 ms cold and 7.240 → 7.261 ms warm on five matched
pairs, with the same cuts and the same 33 native calls.

The opt-in folded Q19 action (`96ab70d1`) now applies a four-tick
binomial core with two authenticated collars. The source determines
the four ordered physical birth flags (`44343958`). The registered
`Reverse_Growth_Admission` build accepted the full ordered pair field,
three births and physical center-digit readout (`0fee9f01`). The
guarded run took 95.03 s including prerequisites. The independent
compiled-hinge refinements cover the two-tick singleton response,
the height-one append for both inlets (`84fce845`), and the height-two
compiler's transport to its successor half-word (`79697379`). The
source inlet laws (`f88d2935`) and physical-prefix induction close the
two-tick clock in `d6aaab26`. For arbitrary folded halves, the compiled
column pull returns each physical birth in order and their sum gives the
exact width change. The final registered build took 152.55 s including
prerequisites and passed the oracle and skipped-proof checks.

On the 1,085-digit source at 1,024 ticks, the installed CLI used one
joint action over 439 core columns, made 544 admission probes, visited
478 collar cells, and reduced ordered joins from 330,144 to 329,053.
Seed 196 took the folded fallback. Five paired cold trials measured
273.40 → 274.25 ms on macOS and 247.01 → 244.95 ms on Linux. First
publication in the same owner took 6.672 → 6.599 ms and a completed
endpoint hit took 0.01525 → 0.01438 ms. The guarded selection passed
46 tests. Pure and native installed wheels matched literal endpoints
and full packets on both platforms. The tests observed native entry,
source refusal, and zero native entry on a short request.
The full default run at `96ab70d1` passed 14,072 tests and reproduced
the six baseline Comma failures by test ID. Canonical P0 passed 77 and
reproduced its 13 baseline failures.

### CF continuation and folded reversal after `907aa90e`

The reciprocal cylinder selects a carry-preserving binary cut from the
original inlet and jumps the cursor directly to the last issued row
(`d3d13444`). It retains the exact first-row action on sealed two-row
tiles for prefix descent (`12925b30`). Five- and six-column suffixes
now share 8 and 16 phase actions respectively (`5aef32e6`). The
operator is selected before the irregular upper digits are read.
The source binding retains the physical exponent, width, clip and ledger
owner. Irregular upper digits still require exact bounded evaluation.

The default spatial source keeps its inlet numeric through exponent eight
and packs once on handoff (`fa91a331`). At horizon 128 this removed both
spatial issues and all ten packing calls. At 4,096, nine spatial issues
and four packs became eight and one. Five interleaved fresh installed CLI
pairs at 4,096 took 130.72 → 125.91 ms on default and 124.86 → 130.57 ms
with reciprocal enabled. Fifteen warm invocations of each installed entry
point took 9.15 → 9.22 ms and 9.66 → 9.62 ms respectively. Both returned
the same complete 540-coefficient packet. On the reciprocal path, head
intervals fell from 40 to 36 and head digits from 465 to 376. Thirty head
source multiplications disappeared and noninitial cursor products fell
from 28 to 10. Clipped right-adjugate transport saved some reads but
slowed the tested two- and three-digit clips. A phase-and-clip cache had
zero cold hits across the tested horizons. The live routes retain the
direct exact clip.

The folded Q19 continuation (`506850f9`, `24264d6b`) takes one half
field and its center through the opt-in C++ publisher. At seed 196 and
1,024 ticks, 506 bands required 55,857 pair joins and 4,037 hinge cells,
compared with 112,969 pair joins on the full field. The native table
peak increased from 361,172 to 425,940 bytes. Five interleaved installed
CLI pairs took 243.61 → 242.76 ms cold. Extending a warm owner to 2,048
ticks took 6.76 → 6.14 ms, with 326,691 → 162,705 joins. The two-pass source theorem (`9765ed99`) proves the ordered physical
birth bits, width and endpoint. It distinguishes `[18]` and `[9,9]`,
whose birth counts agree. The later `d6aaab26` and `0fee9f01` refinements cover the compiled
hinge clock and the protected four-tick slab, respectively.

The opt-in `5rev10` word-RAM route now admits eligible requests from
128 ticks (`3e040acc`). The 153-digit, 128-tick fixture replaced 64
packed pairs with 2,335 tile lookups and 888 fringe gates. The warm
owner median changed from 0.596 to 0.520 ms. Cold timings were more
variable (122.73 → 125.98 ms quiet and 162.80 → 176.35 ms under load).
The installed CLI entered the kernel once at 128 ticks and zero times
at 127. Automatic reflected dispatch has its own outstanding gate.

Fresh pure-Python and native wheels at `fa91a331` passed on macOS ARM64
and Linux ARM64 under Colima. Installed console probes observed the
folded C++ entry at 1,024 and 2,048 ticks and pure fallback at 16.
The CF native continuant ran 21 times at 4,096 ticks and zero times at
63. The combined Mahler build passed in 166.76 seconds. The registered
double-reverse build passed in 181.42 seconds after the two source
composition laws moved next to the decimal recurrence (`2aa83138`).
The registered reverse residuals build accepted the ordered two-pass
theorem with its oracle and skipped-proof checks. The full default
selection passed 14,071 tests and reproduced the same six Comma
admission failures. Canonical P0 passed 77 and reproduced all 13
baseline failures by test ID.

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

## November 21 source-certified ports

The clean baseline was Git `f55418a7cd18a01e9570f4f3d24c59726c2ece5b`.
The guarded default suite took 247.09 seconds and peaked at 441.4 MiB.
It recorded 13,198 passes and six existing comma admission failures.

- The reflected SLP compiler uses aligned children and composes a repeated
  inlet from its leading, interior, seam and trailing responses. Bounded
  unaligned inlets use a single ledgered walk. The decimal publisher folds
  multiplication carry and emission together while preserving the even
  2rev10 normalization.
- 5rev10 uses the packed decimal path from 64 ticks when its source and
  resource bounds permit it. Short and capped requests retain the exact
  scalar route. The padded-H publisher remains available explicitly.
- Reverse/add retains up to 64 completed Q19 landmarks in the receiving
  owner and selects the farthest valid preceding entry. A guarded extension
  resumes a guarded entry at its pre-emission clock. The frontier and
  occurrence rollback paths attempt each independent cleanup.
- The Collatz carry observer omits cuts at or below the admitted dyadic
  valuation and preserves the moving correction. The Antihydra transient
  leaf emits the exact fixed-point safety summary directly. The general
  issued SLP carry action and wider cyclic valuation issuer remain open.
- The prime candidate uses signed cutoff rows, the existing wheel and
  consecutive factor authority, singleton remainder checks and optional
  basis-bounded masks. The initial port kept the candidate internal pending
  the source-count refinement and rollout checks.
- Isabelle checks Fermat checkpoint squaring, ordered joins and the
  source-residue refinement. The tested ladder missed the performance
  threshold and the selected matrix compiler retains its existing
  checkpoint evaluation. The rotational wrap cutover remains open.

### Matched measurements

Each row uses five interleaved samples with equal successful outputs.
The embedded CLI trials bypass shared caches. The Q19 rows measure endpoint
construction in one receiving owner.

| Workload | Baseline median | Candidate median | Executed work or scope |
| --- | ---: | ---: | --- |
| Q19 seed 196 at 4,096 after 2,048 | 35.21 ms | 29.22 ms | 4,095 → 2,048 physical steps |
| Guarded Q19 at 2,048 after 1,024 and 4,096 | 12.97 ms | 11.99 ms | 2,047 → 1,024 physical steps |
| Reflected ×2 SLP, 128 copies of a 128-cell motif | 41.52 ms | 11.95 ms | Aligned 64-tick cone |
| Reflected ×5 SLP, same motif and horizon | 42.39 ms | 12.23 ms | Aligned 64-tick cone |
| 5rev10 seed 73 at 64 | 1.75 ms | 1.65 ms | Scalar → 32 packed pairs |
| 5rev10 seed 73 at 512 | 2.93 ms | 1.84 ms | Scalar → 256 packed pairs |
| Collatz signal with all cuts below headroom | 22.60 µs | 14.58 µs | No phase walk |
| Antihydra fixed-point transient leaf at 128 | 14.23 µs | 4.98 µs | No carry-sheet folds |
| Weighted prime start 150,000, index 200 | 26.70 ms | 8.57 ms | Internal candidate |
| Weighted prime start 1,000,000, index 200 | 78.42 ms | 15.45 ms | Internal candidate |
| Fused masks over weighted rank at start 1,000,000, index 200 | 15.81 ms | 12.77 ms | Internal candidate |
| Fermat F5 at 4,096, decimal position 8 | 11.59 ms | 11.29 ms | Authenticated matrix phase, ladder withheld |

The measured 5rev10 cutoff bands improved the embedded CLI median by
5.1–57.8%. The largest cold median increase across those pairs was 4.5%.
The six ordinary cold CLI controls agreed exactly, with a maximum median
increase of 1.5%. The warm 153-digit 5rev10 request at 512 ticks went from
23.16 to 2.23 ms.
The weighted prime boundary at start 16,777,215 and index 200 produced
a value where the baseline exhausted its default work budget. That case
was excluded from the successful timing comparison.

Development evidence is in the `results/nc41-source-macros-*` run
directories. The proof logs identify rebuilt sessions and reused heaps.

### Guarded verification

The reviewed runtime tree was
`3788a34f3f58a5efbb3cdba102c0081dec3f2f56` on the baseline revision above.
The final default suite recorded 13,252 passes in 228.33 seconds and peaked
at 446.1 MiB. Collection took 14.19 seconds, compared with 14.74 seconds on
the baseline. The six failing test identities matched the baseline.
The guarded P0 selection recorded 75 passes and the same 15 failures as
the clean baseline, covering the existing comma, non-halting and prime-bit
release holds.

The native selection passed all seven requested sessions. Its final run
rebuilt `Prime_Deterministic_Refinement` in 13 seconds and
`Prime_Selection_Initialization` in seven seconds. The other six requested
heaps were reused. Earlier runs rebuilt the changed double-reversal,
reverse/add, Collatz, Antihydra and Fermat sessions under the same limits.
The accepted prime lemmas cover signed arithmetic, strictly decreasing
quotient bounds and prefix-mask interval counts. The executable worklist
and fused consumer refinements remain open.

Strict mypy, Ruff, formatting, source policy and documentation passed.
Whole-tree Pyright checked 2,581 files in 104 serial batches with zero
diagnostics. The follow-up batch after consolidating the adjacent-cell fold
and Antihydra assertions also had zero diagnostics. The built wheel passed
six isolated exact CLI smoke cases. Full packaging remains blocked by the
missing global comma artifact. The proof-index checker still rejects the
existing comma dependency-audit invocation.

### Guarded prime cutover

The public selector uses weighted counting for zero-based indices
200–4,096 with starts below 16,777,216 and the standard rank limits.
Fused masks apply to starts in [131,072, 2,097,152) with verified basis
coverage and the existing mask cap. Guarded pivots apply to eligible
weighted starts below 2,097,152. The short wheel scan and small brackets
retain their existing precedence.

Each pivot comes from the exact containing bracket. The density and
interpolation estimates choose a probe. The certified interval count
chooses the next bracket. A midpoint is forced every fifth round.
At start 9,948,560 and index 200, interpolation reduced the number of
count queries from 13 to 12 but increased factor probes from 28,211 to
31,278 on the unmasked weighted path. That range keeps midpoint selection.

Completed weighted interval counts are published in the existing
issuer-qualified process lease. The receiving request rechecks source
coverage and admits the record under the standard budget policy before
reading it. Same-request warm probes exercise the interval hit before
weighted child discovery. The selected nth result remains query-local.

The follow-up also removes duplicate construction of the issued Collatz
F5 motif grammar and skips the Antihydra carry sheet for an admitted
all-even cylinder. The Fermat radial checkpoints compare integer prefixes
and render only the guaranteed digits. A checked quotient supplies the
decimal width even when the initial estimate needs correction. The
issued F5 prefix step at 4,096 ticks took 35.5 µs, compared with 109.3 µs.
General Collatz SLP/AVL consumption, broader cyclic Antihydra powering,
and Fermat rotational reuse remain open.

The guarded Isabelle sessions checked signed weighted expansion over
`numerical_Phi`, rank-bracket preservation and strict descent from an
exact odd-window probe, and the Antihydra and Fermat refinements.
Executable checks exercise the Python worklist, basis masks, warm reuse
and rollout boundaries.

Five interleaved trials per workload compared the production CLI against
the earlier reviewed tree `3788a34f3f58a5efbb3cdba102c0081dec3f2f56`.
The paired outputs agreed exactly. Times are medians in milliseconds.

| Prime start and index | Cold before → after | Warm before → after | Shared cache bypass before → after |
| --- | ---: | ---: | ---: |
| 0, 1,000 | 139.33 → 131.94 | 4.83 → 0.67 | 9.00 → 1.70 |
| 150,000, 200 | 156.99 → 135.26 | 5.82 → 0.78 | 26.20 → 5.13 |
| 1,000,000, 200 | 211.44 → 140.87 | 6.29 → 1.12 | 79.59 → 10.49 |
| 9,948,560, 200 | 466.30 → 161.52 | 12.60 → 2.79 | 327.14 → 30.76 |
| 0, 4,096 | 150.80 → 137.75 | 6.73 → 0.68 | 19.55 → 6.88 |

The largest cold increase among the three out-of-cohort controls was
1.1%. In the warm 9,948,560 request, 13 issued interval hits eliminated
weighted refolding. Raw evidence is in `results/nc41-rank-pivot-*`.

At the combined upper boundary, start 16,777,215 and index 4,096
returned 16,844,827 under the default work limit. An independent
segmented sieve confirmed the value. The baseline exhausted its budget,
so this pair is excluded from the timing comparison. Increasing either
coordinate by one kept the existing refusal under that budget.

The final runtime verification used tree
`381ba8a78fc13349838bb2140e329681f66c6c48` on `f55418a7`. The guarded
focused selection passed 468 tests, including affected validation cases.
The default suite recorded 13,275 passes in 225.82 seconds, with
14.02 seconds of collection and 454.4 MiB peak memory. The six failing
comma test identities matched the baseline. P0 recorded 75 passes and
the same 15 failures in comma admission, Antihydra non-halting, and
Fermat and Mersenne prime-bit release checks.

The final Isabelle selection rebuilt `Prime_Deterministic_Refinement`
in 14 seconds and `Prime_Selection_Initialization` in seven seconds.
It reused the Antihydra and temporal-clock heaps rebuilt earlier in
the tranche. Strict mypy, bounded Pyright batches for affected files,
Ruff, formatting, source policy, and documentation passed. The built
wheel passed six isolated CLI smoke checks. The packaging release
check still requires the missing admitted global comma future.

### Comma quotient cutover

The direct Bellman publisher now builds and checks a selector chart before
binding its children. Entries with the same core, shift and supported labels
share the chart. The concrete proposal used nine charts across 869 applications.
The release dependency scan excludes the old priority replay from both the
B1 and Future instances. The independent smoke owner retains that comparison.

The Future replay compares one ordered control and child tuple per source
root and checks class bounds separately. The shift and weight encoding share
one replay. The rank checker binds every row to the checked table and shares
closed arithmetic proofs by the three rank values involved. The independent
finite model matched all 14,784 source positions and rejected a child swap
that satisfied the rank check.

Python now checks for sealed phase and cycle actions before reconstructing
their effects. Entry consumes its phase-selected Near operator while retaining
the exact Entry clock and displacement in the occurrence. Repeated boundary
weight checks share a scalar inside a single receipt transaction. A failed
transaction drops that scalar. The guarded comma runtime and source-audit
selection passed 1,440 tests in 113.49 seconds. Separate CLI acceptance
recorded 120 passes and the same eight missing-admission failures as the
combined earlier unit and P0 selections.
Strict mypy, bounded Pyright, Ruff, and repository source policy passed.
The full proof index still reports reachable theories without declared
audit entries, separately from the scoped release dependency scan.

The generic B1 and Future libraries rebuilt in 121 and 26 seconds. The final
native smoke session passed in 88 seconds, including guarded chart bindings,
nonzero phase and fallback outputs, rejected foreign roots, and forged rank
checks. Its reviewed source tree was
`f343c7f57fc591d866481ec6218c064ee7e270e8` on `f55418a7`.

The concrete B1 baseline failed on an unimported shifted-value theorem. The
repaired build reached Entry 10 before the 300-second watchdog stopped it.
That run spent about 134 seconds building the first program relation before
checking the projected selector and bind. The follow-up shares proved
dependency visits within the program owner and retains the aggregate native
dependency audit at publication. The evidence directories are
`results/nc-comma-cutover-native-rollout`, `results/nc-comma-final-smoke`,
and `results/nc-comma-cutover-reuse-audit`.

The follow-up reduced first-program certification from about 134 seconds to
55.5 seconds. It checked 33,350 dependency nodes in 179 ms of local audit
time. Concrete B1 still reached the 300-second limit, with 2.40 GiB peak
memory. Its last recorded checkpoints were 128 completed MDD application
proofs and 1,792 checked bind states. The first large bind alone took about
67 seconds after its selector chart was ready. The full Bellman theorem,
exact B32 consumer, global Future instance, and native export remain
unaccepted. The admission registry remains empty, and the positive public
CLI assertions still require the matching kernel artifact.

### November 21 comma proof benchmarks

The starting checkout was `f55418a7` with local changes. The guarded
baseline used detached snapshot `397e78908ceef78f56c5b7428591e75321fca674`,
tree `43371d6bb2a480b954b0e47df9c0ae32e36d291b`. The first program proof
took 56.0 seconds, including 30.4 seconds in exact Entry-key rewrites and
6.8 seconds in representative action certification. The first selector
chart took 30.0 seconds and the subsequent bind took 65.3 seconds.
Concrete B1 timed out with a 2.85 GiB sampled aggregate peak. The last
completed bind checkpoint recorded 1,792 states. B32 and the concrete
Future instance had no accepted result in that run.

The guarded Python Future benchmark derived 304 class-and-shift requests
from exact boundary returns. Its three routes agreed for every phase,
with 280,896 direct comparisons per route. Over five interleaved trials,
the split, fused, and node-period models made 121,807, 118,745, and 23,082
cold node visits, with median construction times of 134.9, 129.3, and
74.3 milliseconds. The split model skips shift zero and shares its
construction cache across the derived requests. Those times measure
Python construction only.

Run the source-derived replay with the guarded module
`devtools.benchmarks.comma_mdd_shift`. A profiled concrete B1 build also
exports the first Entry bind's compact operands and expected output beside
its profile log. Pass that trace to the guarded module
`devtools.benchmarks.comma_mdd_bind` to check all 924 phases against a
direct pointwise interpretation and compare the two traversal counts.
The trace carries no runtime or release authority.

The raw baseline evidence is in `results/nc-comma-nov21-profiled-baseline`.

The Entry lookup confirmed 3,455 proposals and 1,529 action constructions
in native replay. The proposal pass took about 20 milliseconds. Exact
source-key rewrites remained the larger part of first-program work.
The isolated affine-interval trial was stopped after its first symbolic
tree proof ran for over a minute. The measured bind revision uses the
established row proof.

The timed Entry and bind snapshot `c4dddb2ed30c00862bb7070176bc2c3aa451f6e2`
completed the first Entry bind in 18.9 seconds. The preceding chart took
29.3 seconds. This is one matched native comparison. The witness
producer and receiving proof check the selected target or fallback on
all-leaf branches. Mixed branches still check ordered cofactor rows,
with the row premises bundled into a single theorem.

The Python replay of those exact frozen operands compared every output
phase against direct pointwise selection. Across five interleaved
trials, the selected path reduced cold bind keys from 544 to 100 and
cofactor calls from 13,464 to 3,300. The run exercised 924 selected
slots. Median replay time was 8.03 milliseconds for eager construction
and 2.27 milliseconds for selected construction.

The timed native bind build still reached the 300-second concrete B1
limit at 2.97 GiB sampled aggregate peak. It completed the checkpoint
for 192 application proofs, up from 128 in the baseline. At the last
bind checkpoint it had checked 2,412 selected rows, skipped 344 identity
restrictions, and introduced 453 direct branch shapes. B32, global
Future, native export, and positive installed-wheel admission therefore
remain open. The native profile and exact first-bind trace are in
`results/nc-comma-nov21-entry-bind`.

The separate native certificate smoke build on the same snapshot passed
in 100 seconds, reusing the generic B1 and Future heaps. It exercised
duplicate Entry keys, mapped and fallback selection, ordered children,
and warm replay. The focused Python source-contract selection passed
38 tests. Both benchmark modules passed strict mypy, the guarded
Pyright batch, and Ruff.

The integrated snapshot `1b99f1565a768b7ed715e4ad3433da41ed3adea6`
rebuilt generic B1 in 134 seconds, generic Future in 28 seconds, and
certificate smoke in 98 seconds. The build sampled a 3.21 GiB aggregate
peak. The smoke checked nonzero original shifts, nested periods, a
shared-factor radix example, mapped aliases, distinct encoders, and
repeated selected-cofactor proofs in the receiving store. Future replay
uses normalized keys with checked transport of the full shift in the
consumer theorem. The live class path pairs its existing +1 encoding
with the normalized shift. The weight path retains its separate fused
+10 law.

Five guarded native proposal trials used the same 304 requests and
verified all 924 phases in each route and trial. Split, fused, and
node-period construction visited 121,807, 118,745, and 23,082 cold
nodes, with medians of 312, 345, and 239 milliseconds. The guarded run
sampled a 2.11 GiB aggregate peak. This timed the arena and verified
its proposed outputs. The joined Future release proof was outside the
benchmark. Raw results are in
`results/nc-comma-nov21-native-future-proposal.log`.

Five additional interleaved kernel bind trials used the frozen first
Entry trace and a fresh replay owner for each measurement. They shared
the frozen store and checked the same closed proposition. The
selected-cofactor memo reduced median certification time from 17.92
to 14.84 seconds, with a 2.18 GiB sampled aggregate peak. Raw results
are in `results/nc-comma-nov21-native-bind-pairs.log`.

The transport trial `3bb32c3106755662e83b2a309e972d9dac49f7db`
passed certificate smoke. Its first concrete bind took 15.03 seconds.
The Entry lift quotient was proved 116 times for 2,167 source-key
requests, with 2,051 reuse hits. The full key phase took 31.96 seconds
versus 30.39 seconds in the frozen baseline. This trial established
quotient reuse and preserved the exact source keys, with no measured
improvement in key certification. Concrete B1 reached 320 completed
application proofs and the 1,024-bind checkpoint before the 300-second
timeout. It sampled a 2.60 GiB aggregate peak. Evidence is in
`results/nc-comma-nov21-transport-release`.

The returning class-0 program proof was sampled with Isabelle2026's
`ML_Profiling.profile_time_thread`. The proof closed and its native
dependency audit passed. Poly/ML attributed all 11,025 samples to
`UNKNOWN`. A named-loop calibration also produced only `UNKNOWN`,
with 31 thread samples and 18 process-wide samples. Source-level timers
placed about 35 seconds in Entry-key certification during this replay.
The matching uninstrumented program proof took 61.58 seconds.
Hoisting static Entry contexts reduced duplicate-rule warnings from
1,780 to 150 and took 60.74 seconds in one uninstrumented comparison.
The sample report is in `results/nc-comma-nov21-entry-cpu-samples.log`.

A second matched uninstrumented comparison used the established key
evaluator in both arms. `semantic_direct_entry_bindings.ML` moved the
static support, uniqueness, admission, and product-case contexts
outside its per-Entry proof. `semantic_direct_entry_row_plan.ML`
rewrote the already-checked key argument directly, then normalized the
result in a shared product-case context. These changes retained the
exact class-0 theorem and reduced duplicate-rule warnings from 1,780
to 150. Certification took 59.52 seconds before and 58.50 seconds after
in the matched run. Scalar key certification remained about 32.7
seconds. The lift memo was left out of the retained path after its
matched workload failed to show a key-certification improvement.

The retained source snapshot `58568405e24a5799cd39b59603992b27d5c1c34d`
rebuilt certificate smoke in 89 seconds with generic B1 and Future
reused. In the guarded concrete run, the first selector chart took
27.62 seconds and the first bind took 15.40 seconds. Concrete B1 timed
out at 300 seconds with a 2.61 GiB sampled peak after the 320-application
and 1,024-bind checkpoints. At those checkpoints, mapping-root family
construction in `crt_mdd_bind_replay.ML` accounted for 44.7 seconds
across 242 builds, indexed-slot assembly for 21.1 seconds, and the
class-0 scalar key evaluator for 30.8 seconds. The proof-operation
timers are inclusive.

No completed concrete B1 theorem was available to B32, the global
Future producer, or the native writer. The public CLI admission gate
therefore still lacks its kernel artifact. Final logs are in
`results/nc-comma-nov21-retained-smoke` and
`results/nc-comma-nov21-retained-release`.

### Mixed mapping families and ordered Entry charts

The follow-up starts from `58568405e24a5799cd39b59603992b27d5c1c34d`.
The reachable Bellman proposal had 869 applications, 430 ordered Entry
bind requests, and 12,774 reachable operand and result nodes. The
independent Python bind model reproduced all captured output roots.
It found 1,355 distinct mixed mapping families. Removing labels from
the ordered key left 1,355 families, and sorting and deduplicating the
roots left 1,342. Ordered suffix sharing would reduce 20,297 assembly
steps to 18,822. Those counts led to retaining the ordered mapping
key and changing how its proof is constructed.
The direct action proposal already interns structural expression
bodies. Its program and source theorems still bind the exact action to
that body. In the existing owner, each input determines its expression,
so removing the expression field from those caches would leave their
cardinalities unchanged.

The root cofactor proof already has a store-scoped identity given by
axis and frozen root. Replay now composes those checked theorems over
the ordered mapping-root vector. The kernel transports that vector
proof through the exact labeled mapping and checks the final proposition.
Repeated roots reuse the same checked fact. The mapping proof retains
the original labels and placement. The receiving bind still checks its
source, fallback, result and ordered slots.

Five alternating native pairs certified the same 48
captured mixed mapping families, covering 1,006 mapping rows. Each
trial used a fresh replay owner and shared the frozen store. Both
routes produced identical closed propositions and built 338 root
cofactor certificates and 48 mapping certificates. The median
certification fell from 11.688 to 0.578 seconds. The mapping-root
assembly timer fell from 11.314 to 0.227 seconds. The mixed regression
exercises repeated target roots and rejects agreement with the
original result after a target changes. Raw evidence is in
`results/nc-comma-nov21-b1-workload-analysis.log` and
`results/nc-comma-nov21-mapping-family-pairs.log`.
Two further alternating pairs without phase instrumentation took
11.742 and 11.741 seconds for the former proof and 0.620 and 0.622
seconds for the replacement. Those runs also checked exact proposition
equality. See `results/nc-comma-nov21-mapping-uninstrumented.log`.

The ordered-mapping proof snapshot
`0d5cad12617b93725c433c797a33aad60fc9f331` passed the registered smoke
build. It rebuilt generic B1 in 117 seconds, generic Future in 26
seconds, and certificate smoke in 89 seconds. The remaining dependency
heaps were reused. The build exercised the mixed mapping, selected
target and fallback, changed phase, and foreign-root regressions.

On the matched first class, scalar Entry key certification took
33.110 seconds across 2,167 row transports. The chart trial checked
17 reusable lift vectors and 430 exact source normalizations, and
derived each key by selecting its ordered row from the checked chart.
Preparation plus certification took 46.751 seconds versus 62.973
seconds for the scalar path. Both runs certified the same closed
class-0 theorem and passed its native dependency audit. The chart time
includes the trial's up-front preparation for all 430 sources. In the
production design, preparation retains only the reusable lift vectors
across programs. Each receiving program owns its checked source chart.
See `results/nc-comma-nov21-entry-chart-baseline.log` and
`results/nc-comma-nov21-entry-chart-unary.log`.
The program-local trial used 327 source charts for the matched class,
covering the same 2,167 transports. It took 43.880 seconds including
preparation and passed the same theorem and dependency checks. The
lift-vector count stayed at 17. See
`results/nc-comma-nov21-entry-chart-program-local.log`.
Prewarming just the 17 source-independent vectors before program
certification took 43.920 seconds including preparation. The chart
accounted for 13.940 seconds while the same 1,051 distinct
representative actions were certified through the existing rule. See
`results/nc-comma-nov21-entry-chart-prewarm.log`.

The integrated code was tested at
`a7e84be49a24f1e6a6c27a0afa96c6b6a97aeb43`. Generic B1 and Future were
rebuilt in 119 and 26 seconds on the preceding snapshot with identical
producer sources. The final run rebuilt certificate smoke in 92
seconds and reused its 23 dependency heaps. It checked foreign source
offsets, swapped wanted rows, changed actions, and shared-vector reuse.
All 57 focused source and documentation tests passed.

The concrete release build reproduced the 46 Bellman proposal roots
and reduced class-0 program certification from 55.481 to 35.801
seconds at the same checkpoint. It reached 384 logged application
proofs and 1,536 checked bind states before the 300-second watchdog
stopped the session, with a sampled peak of 2.59 GiB. At the last bind
checkpoint, mapping-root family assembly took 1.142 seconds for 335
builds. Indexed slot assembly took 34.906 seconds, including 31.413
seconds of slot normalization. Selected cofactor rows took 27.530
seconds. The counters are inclusive.

The incomplete concrete B1 session left B32, global Future and
release export without an accepted concrete theorem. CLI admission
remains blocked. The final records are in
`results/nc-comma-nov21-ordered-entry-smoke-final`,
`results/nc-comma-nov21-ordered-entry-release-final`, and
`results/nc-comma-nov21-ordered-entry-source-tests`.

### Small-period CRT selector

The isolated phase-chart trial shared one base for each of the six
periods. The kernel checked 92 bounded phase points across those bases,
then transported each ordered relabel table at its exact receiving
core and support. The real fallback and the absolute application
shift remain in the checked conclusion.

One matched native pair reproduced all 46 candidate roots across 869
applications and 430 Entry requests. The nine selector certificates
took 22.741 seconds with shared period charts, compared with 57.744
seconds for the Boolean guard construction. The checked bind count for
these selectors fell from 185 to 24 and the mixed mapping-family count
from 68 to 5. Boolean guard proofs fell from 75 to zero. Store freezing
took 28.314 seconds versus 29.462 seconds. The candidate rejected a
substituted core and swapped slots, and preserved default output for
incomplete support. Shifts 0 and 924 reused the selector while the
Fork and Landmine application proofs remained distinct. See
`results/nc-comma-nov21-phase-selector-baseline.log` and
`results/nc-comma-nov21-phase-selector-candidate-14.log`.

### Period-one Entry forwarding

The paired alias trial kept the checked period selector in both arms.
It found 103 eligible zero-shift Gotos and reproduced all 46 Bellman
roots. On 12 matched typed projection requests it certified 162
applications and 225 bind states, compared with 174 and 238 for the
selector alone. The 13 saved binds include the 12 skipped Entry binds
and one selector bind that became unnecessary in this selection.
Certification took 26.333 versus 26.485 seconds. The single timing
pair establishes the work reduction and leaves the wall-clock effect
uncertain.

The isolated receiver fixture rejected wrong children, foreign
roots, and a changed absolute shift even when the chart period would
admit reuse. The guarded continuation selection passed 21 tests,
including both construction orders for the 3,334-versus-2-tick
Entry/Near pair. See
`results/nc-comma-nov21-alias-selector-baseline.log`,
`results/nc-comma-nov21-alias-selector-candidate.log`,
`results/nc-comma-nov21-period-one-receiver-2.log`, and
`results/nc-comma-nov21-near-entry-regressions`.

The receiving law combines the existing physical period-one Goto
theorem with the authenticated source-to-program binding and the
checked child projection. It keeps the source observation and its
elapsed weight under the source owner. The projected Entry reuses the
child theorem at the unchanged application shift. The combined
diagnostic exercised both period-one cores, ineligible Fork and
nonzero-Goto rows, missing and duplicate support, and the phase
selector's corruption cases. See
`results/nc-comma-nov21-period-one-source-refinement-2.log` and
`results/nc-comma-nov21-combined-selector-diagnostic.log`.

The combined snapshot `ba2aa31eb566fde84aa32b3d74c8ce8076bd10ec`
rebuilt generic B1 in 118 seconds, generic Future in 26 seconds, and
registered certificate smoke in 89 seconds. It reused 21 dependency
heaps. The 78 focused tests passed. In the concrete build the first
Entry selector took 7.690 seconds, versus 26.887 seconds on the
preceding snapshot. Its subsequent Entry bind took 13.635 seconds,
compared with 13.412 seconds.

The proposal retained all 46 Bellman roots with 766 applications,
eight selectors and six period bases. Concrete B1 hit the unchanged
300-second watchdog after logging 384 application proofs and 1,792
checked bind states, with a sampled peak of 2.70 GiB. At that checkpoint
indexed slot assembly accounted for 48.280 seconds, including 43.803
seconds of slot normalization, and selected cofactor rows took
40.703 seconds. The concrete B32, global Future, export and installed
CLI gates continue to require the complete B1 theorem. See
`results/nc-comma-nov21-phase-alias-smoke`,
`results/nc-comma-nov21-phase-alias-release`, and
`results/nc-comma-nov21-phase-alias-source-tests`.

### Behavior-first construction census

The isolated census visits the actual ordered expression graph before
creating selectors or MDD roots. Its proposal uses aligned core
periods, ordered child descriptors, exact terminal arguments and
absolute shifts. Every one of the 46 class roots retained a distinct
descriptor. The 869 raw application keys produced 384 collision
groups, all involving zero-shift Goto wrappers. There were zero
Entry-to-Entry collisions and zero pairs of distinct program terms
with the same expression. These counts establish the observed work
distribution in this graph. See
`results/nc-comma-nov21-behavior-census-refined.log`.

The matched census restricted to the retained proposal's reachable
requests found 485 descriptors among 766 applications. All 281
remaining collision groups involve Goto wrappers. The independent
ordered child-chart transport and exact Entry-program transport
theorems passed in isolated native checks.

The conditional Goto issuer trial shared one theorem across distinct
authenticated source bindings in each arrival order. The class-0
production-shaped comparison certified the identical theorem in
39.120 seconds with the current issuer and 39.851 seconds with the
candidate. The candidate built 326 conditional Goto certificates with
zero hits on that workload. Its cache remains isolated. See
`results/nc-comma-nov21-goto-behavior-native-2.log`,
`results/nc-comma-nov21-goto-class0-baseline.log`, and
`results/nc-comma-nov21-goto-class0-candidate.log`.

Five guarded Python trials in each arrival order measured 253 cold
raw-action evaluations and zero additional evaluations for the
equivalent receiving chart. The cold medians were 7.52–7.85 ms and
the receiving medians were 0.021–0.028 ms. The fixed-sector trial
reached 600020 in 3,334, 3,332 and 2 ticks from the two Entry offsets
and the Near source respectively. The checked physical crossing adds
one to the trial value and publishes 600021. These are separate physical
occurrence measurements. See
`results/nc-comma-nov21-behavior-python-pair-final.log`.

### Isolated proof-debt review

Snapshot `e5385f1a1752aa1fdc6859815d677cefa7ab5875` changes two
sparse-base files, with five lines added and seventeen removed.
`Comma_Sparse_Base_Instance` still feeds `Comma_Sparse_Power_Instance`,
the native summary and future proofs, and `Comma_Global_Future_Safety`.
The checked all-powers theorem now uses the canonical row directly.
The constructor retains its exact root check and returns the value
and refinement consumed by callers. The 278-template match remains
in the sparse-base theory.

`Comma_Fast_Totality` retains its documented finite canonical-rank
claim. `Comma_Branch_Period_Instance` retains its independent branch
result and its tested session registration and parent. The audit
checked the repository's registrations, theory and ML loads, theorem
references, proof policy, tests and developer tools. It also checked
local result sources and manifests up to 5 MiB and the two November 21
benchmark bundles for references to the removed alias. The review
scope was limited to files available locally.

Registered certificate smoke passed in 88 seconds on the isolated
revision. The changed and baseline revisions both exhausted the
300-second sparse-base session limit inside the same `local_setup`
constructor, before the changed all-powers theorem. The candidate
passed 166 focused tests. The one proof-inventory failure reported
the same 27 missing oracle audits as the baseline. The source-policy
reports also matched byte for byte. The sparse-base cleanup remains
isolated pending a build that reaches its changed theorem. See
`results/nc-comma-nov21-debt-proof-gates`,
`results/nc-comma-nov21-debt-baseline-native`,
`results/nc-comma-nov21-debt-source-tests`,
`results/nc-comma-nov21-debt-baseline-inventory`, and
`results/nc-comma-nov21-debt-baseline-policy.log`.

### Fused Entry-to-Near trial

The isolated runtime and proof revision `e3fd49f2712f52cd606b758578396b0757fa9ba3`
reuses the Entry cycle in the authenticated boundary-template producer
and projects decisive endpoints without constructing a second Near
occurrence. The semantic continuation owner probes the same residual
operator for Entry and Near before evaluating the bounded physical
prefix. The exact source clock and Entry weight remain separate from
the shared operator. Both arrival orders exercise reuse with prefix
construction disabled on the receiving side.

The independent literal audit matched 2,565 cases at exponents 2–4
and 27 cases at exponent 5. The runtime tests keep settled-clock
admission at exponent 5 and check `1991 → 2003` as a Near crossing.
All 145 tests in the final candidate-root selection passed. Ruff,
formatting, strict mypy and the eight-file strict Pyright batch passed.

Five interleaved trials matched complete boundary templates for 128
requests, 720 endpoint results, and semantic continuation results for
18 roots. Median cold template construction went from 376.3 to
356.4 ms. Decisive endpoints went from 58.8 to 33.8 ms and semantic
construction from 51.6 to 34.5 ms. Charged template work rose from
253,406 to 256,001 while charged operand bits fell from 61,618,554 to
60,594,536. These timings measure Python construction. See
`results/nc-comma-nov21-fused-final-matched.log` and
`results/nc-comma-nov21-fused-final-units`.

The isolated Isabelle check accepted the bounded prefix threshold,
the Entry and Near physical clocks, and the successful and terminal
high-wire quotient differences. In particular the successful quotient
formula covers sector-nine rollover. The check preserves absolute
source and clock data, including the distinct cost of a terminal fork
versus a successful crossing. The whole physical C1 composition and
concrete B1 publication remain separate consumers. See
`results/nc-comma-nov21-fused-native-lean-7.log`.

The registered `Comma_C1_Occurrence` session completed in 78 seconds,
including the fused refinement. Registered certificate smoke completed
in 88 seconds. Concrete B1 reached 1,792 completed bind states before
the 300-second watchdog fired. See
`results/nc-comma-nov21-fused-registered`,
`results/nc-comma-nov21-fused-registered-smoke`, and
`results/nc-comma-nov21-fused-concrete-b1`.

### Bounded Entry response reuse

Revision `254d105def3ff87060547839c66b7acc88e06b6f` reuses only the
bounded seam at `(f, h)` and the power residue at `(P, phase)`.
The phase includes the receiving width delta and is reduced by the
period for that displacement. The authenticated callers still derive
the exact source weight, carry, and child order outside the memo.
An ordinary first template and an exact parent hit allocate no
response tables. A second distinct template can allocate them through
the query ledger. Required template publication can evict the memo
and retry its reservation. An earlier eager allocation increased the
one-template median from 1.073 to 1.192 ms.

Five interleaved trials reproduced all 6,840 endpoint outputs and
128 complete templates. With setup and cleanup included, the endpoint
median fell from 319.0 to 282.3 ms. The same candidate bypassing the
memo took 320.4 ms. The batch built 116 residue entries and 1,560 seam
entries. The authenticated template median was 353.7 versus 355.0 ms,
with charged work falling from 256,001 to 248,387. The one-template
control was 1.059 versus 1.063 ms. The guarded selection passed 165
tests, including malformed owners, width shifts, saved child seams,
eviction, tight publication budgets, and cleanup on exceptions. Ruff,
formatting, strict mypy, and the ten-file strict Pyright batch passed.
See `results/nc-comma-nov21-entry-cache-deferred-units` and
`results/nc-comma-nov21-entry-cache-deferred-matched.log`.

### Direct indexed bind slots

Revision `6413fd7a386efd687e1d2644e491ebedb1fc4dcd` adapts checked
slot proofs with kernel beta conversion and selected list equations.
Mixed branches prepare their literal cofactor vectors once for the
frozen Store. The adapter checks each closed slot proposition before
assembling the ordered row. Source admission and theorem publication
are separate operations. The new fixture rejected wrong slots,
children, labels, and a nominally identical foreign Store.

Five alternating native trials used one frozen Store, the same
ordered mapping and default, and identical closed bind conclusions.
Median cold certification went from 13.144 to 9.959 seconds. Both warm
public lookups took less than one millisecond. Each cold candidate
adapted 1,023 slots without generic per-slot rewrites. Baseline indexed
normalization took 3.174 seconds, within 3.456 seconds for assembly.
The candidate spent 337 ms preparing 23 vectors, 46 ms adapting
slots, and 118 ms assembling rows. Selected cofactor row certification
took 3.476 versus 3.510 seconds. Median admission and publication
were below one millisecond and one millisecond respectively. See
`results/nc-comma-nov21-direct-slot-pairs.log` and
`results/nc-comma-nov21-direct-slot-pairs-profile.log`.

The registered certificate smoke session passed in 88 seconds on
the direct-slot revision. It exercised the same implementation and
the exact proposition checks in the new corruption fixture. See
`results/nc-comma-nov21-direct-slot-native-smoke`.

The uninstrumented concrete B1 session reached the 300-second watchdog
in the Frontier24 source bridge's `local_setup`, with a sampled peak
of 2.61 GiB and confirmed process cleanup. B32, global Future, and CLI
admission still require the concrete theorem. See
`results/nc-comma-nov21-direct-slot-concrete-b1`.

### Selected-row kernel composition

The Frontier24 branch composes the selected source, leaf, and target
facts directly in Isabelle and transports the result through the
checked ordered slots. Five matched cold pairs on the same frozen
Entry bind, each with fresh Store preparation, proved identical
closed conclusions. The median fell from 14.754 to 10.808 seconds
at `34ac811`. The selected-row and follow-up proof-stage changes
remain branch-only. The concrete B1 gate at `322ea184` still
timed out at 300 seconds. The diagnostic run logged the first
Bellman root and bind checkpoint 3,584. Comma CLI admission
stays fail-closed.

The independent fold-type fix from `ea0d8af` is in local main's
unstaged working tree. It specializes the HOL fold to the mask
action type at both the row issuer and the publisher.

### Independently validated comma ports

Local main includes the Store-owned width proof reuse from
`f9e848a`, the ordered Future rank derivation from `fe98c3bd`,
and the fused Entry and first-sector proofs from `e3fd49` and
`da81efa`. The width change reduced median frozen 46-root replay
from 21.233 to 4.174 seconds in five matched pairs. The registered
source-entry build checked the 4,113-step seed-20 fixture.

The profiling flag is `ISABELLE_PROOF_PROFILE_LOG`. Records carry
their family label. The uninstrumented B1 gate at `f9e848a` timed out
at 300 seconds. A matched diagnostic completed nine of 46 roots
and stopped during class 9 payload set inclusion. See
`results/nc-comma-mapped-action/b1-merged-profile.log`.

On the same frozen Store, the native payload-bound fixture took
47.714 seconds for full covers on the first nine roots,
44.659 seconds with unordered child evidence deduplicated, and
0.580 seconds for the direct bound. The direct bound checked all
46 roots in 3.380 seconds, rejected a reachable 243, and preserved
the exact ordered Store equations. The issuer replacement at
`9a192b2` remains branch-only. Its uninstrumented concrete B1
build timed out at 300.022 seconds during certificate checking.
The registered certificate smoke passed at `28ed9ab`, including
foreign, post-freeze, and tighter-cap rejection. Live B32, Future,
and CLI admission remain gated. See
`results/nc-comma-mapped-action/cover-pair-profile.log` and
`results/nc-comma-cutover-removal-queue.md`.

The typed B32 bridge at `333fdc5` passed generic B1. Two isolated
phase barriers checked Continue-only well-foundedness on the admitted
quotient and exact typed B32 Stop at phase five. The phase-five
provider probe checked all 46 typed lookup rules. The all-phase
height check and ordered Future liveness remain open. The matched
uninstrumented concrete B1 run timed out at 300.044 seconds.
See `results/nc-comma-first-sector/phase-five-typed-provider-v3.log`
and `results/nc-comma-first-sector/b1-typed-stop-concrete-gate`.

`comma_first_hit` checked qualitative Continue-only well-foundedness
from the phase-134 barrier by infinite-chain contradiction. Direct
well-founded induction also checked the typed physical Stop from
admission and well-foundedness. The dependency audits exclude the
old LEAST measure and bounded typed-stop authorities. The exact
B32 projection requires height below 32. The legacy encoder's
height-26 bound is stronger. Isabelle checked this separation in
registered generic B1 at `18844e7` in 126.961 seconds. The proof
is unstaged on local main. The all-phase projection still needs
a checked bound in the registered dependency chain. See
`results/nc-comma-first-sector/generic-qualitative-stop-v1.log`
and `results/nc-comma-first-sector/b1-b32-bound-native-v1`.

The shared class-step conversion from `357feee` passed registered
generic B1 and Future and is unstaged on local main. The typed
phase-five port at `6cbf62e` compiled the root consumer and checked
all 91 lookup results from 46 typed class proofs. Ordered Future
liveness still requires the registered concrete chain. See
`results/nc-comma-first-sector/phase-five-source-smoke-v4.log`.

Registered generic Future at `2326e91` checked the shared class-step
owner and phase-134 barrier over all 46 roots. It checked 132 action
proposals and rejected a forged terminal. The generic ordered-liveness
theorem also passed. The follow-on at `13c3768` checked the qualitative
typed physical Stop using the barrier and an infinite-chain contradiction.
It leaves the independent all-phase B32 height bound open. The registered
follow-on at `0ca5193` checked the generic rank-free finite-order and
unique ordered live successor rules. The authored graph proposal covers
4,402 finite rows and 314 uniquely continuing rows. Its finite witness
and exact source-to-ordered-edge equality still need kernel acceptance.
The v3 export still authenticates numeric ranks. The combined proof port
remains isolated because its Class_Rank hunk overlaps local main. See
`results/nc-comma-first-sector/future-shared-native-v4` and
`results/nc-comma-first-sector/future-rankfree-native-v1`.

The isolated `6279018` registered Future and certificate smoke
checked the provider-parametric typed source-to-ordered-row bridge
and bitmap rules. The two-file source and class bridge is unstaged on
local main. The witness passed proposal preflight. The physical class
joins and the full finite/live kernel certificate remain open.
See `results/nc-comma-first-sector/combined-certificate-smoke-v4`.
The next bounded smoke stopped at the concrete Z7 fixture before
checking the finite-order table chunks. The isolated `bf373b4` fix
composes three sector summaries and projects the physical exact result
from the existing typed phase-five owner. The registered Future parent
and bounded Z7 theory passed, with the fixture taking 78.51 seconds.
Isabelle checked Fork 4 and the physical N/Z children in order. The
class-row proof still requires the table row and both class joins.
Local main lacks the phase-five provider files needed to port the fix
independently. See
`results/nc-comma-first-sector/z7-bf373b4-fixture-v1.log`.
The bounded rank-free class bridge passed against the same Future
parent. It uses row geometry for the typed join, with numeric ranks
confined to the legacy caller. See
`results/nc-comma-first-sector/rank-free-class-bf373b4-fixture-v1.log`.
The isolated concrete Z7 join passed in 89.075 seconds. It checked
the authored selector paths and the Fork 4 row with ordered child
classes `[777, 1]`. Exact proposition validation rejected a swapped-arm
theorem. This authenticates one source in that fixture. See
`results/nc-comma-first-sector/z7-ordered-bf373b4-v8.log`.
The bounded Z7 and Z8 fixture passed in 92.804 seconds. For `(Z,8,4)`
it checked Fork 7 and distinct physical N and Z arms at phase 11.
Both map to class 1 from source class 31. Isabelle checked the
rank-free graph join and rejected reversed physical arms and swapped
slot evidence even when the projected classes coincide. See
`results/nc-comma-first-sector/z7-z8-equal-arms-bf373b4-v1.log`.
`comma_first_hit` extended the isolated source join to `(Z,9,4)`.
The 96.110-second guarded fixture checked rollover to phase five at
offset 57, the typed Landmine after two further decade crossings, and the
class-1 terminal with empty children. It rejected a forged Fork and
retained the Z7/Z8 order checks. See
`results/nc-comma-first-sector/z7-z8-z9-landmine-bf373b4-v1.log`.
The source-bound B32 fixture passed in 72.572 seconds. A checked dyadic
Stop at phase five and offset 27 determines the typed Fork, terminal
width and ordered literal children. The physical lift keeps elapsed
time as a witness and has no Bellman-code premise. See
`results/nc-comma-first-sector/b32-source-bound-bf373b4-v1.log`.
The 73.344-second elapsed check used one checked 217-cycle Entry packet
and one Near step. Isabelle certified source 100027, terminal 199918
at 2,171 physical ticks, and ordered children `[199999, 200000]`. It
rejected the off-by-one outcome and reversed children. The general
source-wide Stop and elapsed certificates remain open. See
`results/nc-comma-first-sector/b32-source-elapsed-bf373b4-v3.log`.
The receiving Future session checked the generic bitmap-coverage
theorem for exactly one ordered live child. The isolated three-row
fixture passed registered certificate smoke. It checked exact table
selection, ordered chunks and bitmap coverage and rejected reversed
children, a foreign row, a terminal claimed live and equal live
children. The full graph check and physical source-to-table joins
remain open. See
`results/nc-comma-first-sector/bitmap-receiving-smoke-typed-union`.
The separate 33-row two-chunk fixture timed out at 300.150 seconds
against the prebuilt Future heap. The file-backed diagnostic completed
selector and readiness checks for the first 32 rows and timed out in
the closed mask fold. Replacing aggregate code simplification with
checked binary OR rewrites and a checked index-one bit rule let the
same fixture finish in 20.997 seconds. It checked both chunks, their
join, and the rejection cases. The isolated Future checker now uses
the same rules and passed the bounded fixture in 21.468 seconds.
The full graph remains unverified. See
`results/nc-comma-first-sector/bitmap-33-bf373b4-durable-v1.progress`
and `results/nc-comma-first-sector/bitmap-33-bf373b4-ported-v1.json`.
The sparse fixture uses 65 selected classes in a 1,025-row toy table.
It checked three chunks through bit 1,024, two balanced joins, and
the finite/live and rejection cases. The second join previously
expanded a checked inner append. Direct theorem composition closed
the same propositions in the 37.299-second guarded fixture. The isolated
Future checker passed the same fixture in 36.820 seconds after the port.
See `results/nc-comma-first-sector/bitmap-sparse65-bf373b4-ported-v1.json`.
`comma_future_reach` extended the isolated check to the first 128
proposed finite IDs in the authored 4,716-row table. The registered
`bf373b4` Future parent passed. The baseline fixture published the
ordered table and checked two complete chunks plus the third chunk's
readiness. It timed out at 300.181 seconds during the third bitmap fold.
See `results/nc-comma-first-sector/bitmap-real128-bf373b4-v1.progress`.
The same 128-class fixture passed in 167.050 seconds after keeping
`set_bit` updates symbolic during readiness and reusing checked incoming
bit facts. The second chunk's readiness fell from 93.462 to 5.213 seconds
against the checked-bit trial that still expanded updates. The revised
bit-proof setup took 31 ms for that chunk. All four folds, three joins,
and swapped-child, foreign-row and early-Fork rejection checks passed.
The checked classes include ID 4,255. Full graph coverage and the
remaining physical source joins are open. See
`results/nc-comma-first-sector/bitmap-real128-ordinal-bf373b4-v1.progress`.
The 84.105-second source-live fixture applies the new selection theorem
to the checked Z7 crossing under a synthetic three-row live graph. It
rejects a forged phase and reversed arms and preserves the authored Z8
finite equal-class arms. The authored global source joins and release
export remain open. See
`results/nc-comma-first-sector/source-live-consumer-bf373b4-v2.log`.
The isolated v4 candidate writer, parser and provider select ordered
live children from explicit finite/live dispositions. The 72-test
selection passed, including finite cycles, both-live forks and live
Landmines. The isolated native writer draft requires the exact checked
live bitmap, ordered source joins and global release theorem. The current
loader and release still depend on rank publication. See
`results/nc-comma-first-sector/future-v4-unit-v2`.

`comma_future_reach` validated the complete-receipt receiver on an
authored admitted provider. The compact proof uses the existing
transaction-owned receipt and checks ordered N/Z, source and elapsed
extent. Its 65 focused tests also passed against the exact receiving
tree. The receiver and the tested release of checked seam objects
before generator suspension are unstaged on local main. The
compact producer remains isolated because its scratch reservation
omits simultaneously live carry-power records. The public comma P0
selection passed 14 checks and failed the six positive admission
checks after the CID and C1 seam changes. See
`results/nc-comma-future-source-reach/current-main-comma-p0`.

The streamed seam checker now takes displacement, carry count and
headroom from the same guarded C1 arithmetic without issuing a retained
power or recalculating displacement. The 45-test receiving selection
passed, including a test that forbids power issuance. The seam change
is unstaged on local main. The complete-return producer still has a
separate scratch gate. See
`results/nc-comma-future-source-reach/value-only-c1-receiving-unit-v2`.

The value-only C1 caller now shares the return arithmetic before
publication and avoids the temporary `C1Return` and its witness.
The 79-test receiving selection forbids either power record and
passed. This change is unstaged on local main. The isolated complete
producer adds a tracked reservation for the nested Near C1 check.
It passed 92 tests, including refusal before and after reservation
charges. The outer producer scratch bound is still open. See
`results/nc-comma-future-source-reach/c1-scratch-projection-unit` and
`results/nc-comma-future-source-reach/c1-scratch-held-unit`.
The isolated producer now reserves the ordered children, selected
action and prepublication receipt records before constructing the action.
It holds the reservation through publication. The 94-test guarded run
passed, including refusals before and after each scratch charge and
checks that the scratch owner releases its charges and issues no receipt
after refusal. Full producer accounting and production admission remain
open. See
`results/nc-comma-future-source-reach/c1-selection-scratch-held-unit`.
The weighted repeat locator now bounds its scratch ladder by copies
that can fit the requested elapsed weight, including signed affine
offsets. Over five interleaved arithmetic trials, 182 exact offsets
matched. Charged work fell from 12,742 to 1,032 per trial and the median
fell from 394.970 to 36.947 ms. The two verified files are unstaged on
local main. The weighted 314-edge CLI application still needs a checked
export binding the physical weights and ordered cycle to its source.
See `results/nc-comma-future-source-reach/repeat-ladder-matched.log` and
`results/nc-comma-future-source-reach/cycle-scratch-bound-exact-unit`.
Under synthetic test admission, both existing arithmetic routes agreed
on all 314 ordered arcs and the +924 exponent gain. Compiling normalized
equations took a median 0.505 seconds versus 1.745 seconds for indexed
literal occurrences over five trials. See
`results/nc-comma-future-source-reach/weighted-cycle-existing-producer.log`.
Cancellation after writing the occurrence seal exposed an uncharged
entry in each store. The publisher now restores the journaled sizes
before releasing the charges. The receiving tree passed 281 tests,
including cancellation after either write and exact retry. See
`results/nc-comma-future-source-reach/cycle-publication-receiving`.
The isolated lifetime follow-on drops spent chart and affine records
before the next move and closes the verifier even if priming fails.
All 92 focused tests passed. The selection stage still needs its own
live-record bound, including the provider selection retained by the
receipt. See
`results/nc-comma-future-source-reach/held-return-lifetimes-unit`.
The receipt store now charges the retained provider selection alongside
the receipt and releases that charge on rollback. This separable change
is unstaged on local main. The capacity and rollback fixture and the
83-test receiving selection passed, as did scoped Pyright and Ruff.
An injected failure immediately before receipt insertion also released
the full receipt and seal charges.
The isolated compact path also reuses its admitted source occurrence
and passed 92 focused tests. Its transient selection bound remains open.
See `results/nc-comma-future-source-reach/main-selection-accounting-unit`
and `results/nc-comma-future-source-reach/held-selection-accounting-unit`.

The receipt path now consumes the provider's sealed source CID and
checks both ordered N/Z children. The classifier snapshots its phase
before charging work, and the issuer rejects a changed source. The
receiving-tree fixture observed one source walk and two ordered child
walks per return. All 86 selected tests and scoped typing, lint and
format passed. The change is unstaged on local main. See
`results/nc-comma-future-source-reach/source-cid-reuse-unit-v2`.

`comma_mdd_action` checked the same 46 theorem conclusions with
off, coarse and detailed modes on a prebuilt parent. Coarse and
detailed each emitted 186 complete structured records. Detailed
mode also emitted its optional profile log. The registered concrete
B1 run at `ce15010` timed out at 300.020 seconds after completing 22
of 46 roots. Its durable checkpoint identified projected evaluation
at zero-based root 22. At the 20-root checkpoint, cofactor and family
proofs accounted for 82.523 seconds, including 72.722 seconds for
35,184 cold selected cofactors. The remaining direct MDD work took
82.291 seconds and ordered slots took 43.443 seconds. The same-source
uninstrumented run timed out in the Frontier24 source bridge at 300.029
seconds. That version of the structured progress port stayed isolated
because the runner and B1 issuer edits overlapped local main. See
`results/nc-comma-mapped-action/progress-b1-detailed-ce15010` and
`results/nc-comma-mapped-action/progress-b1-off-ce15010`.

On `8be533f`, the operand proof keeps the original ordered bind
conclusion and combines a checked numeric ceiling with one Store
bound. Registered generic B1 passed. Across five alternating pairs
on the same 2,266-node bind, median operand time fell from 374 to
185 ms, cold bind from 4.125 to 3.979 seconds, and total including
Store preparation from 8.677 to 8.498 seconds. Checked Store-bound
queries fell from 4,993 to 3,749. The fixture checked exact
propositions and rejected malformed operands and a foreign Store.
Registered certificate smoke passed. The uninstrumented concrete B1
gate timed out in Frontier24 at 300.054 seconds. The candidate remains
isolated and its certificate-theory hunk conflicts with local main.
See `results/nc-comma-mapped-action/operand-bound-five.log` and
`results/nc-comma-mapped-action/operand-bound-b1-8be533f`.

The receiving-tree port passed registered generic B1 and a native
compile of the 24 adapted producer ML files. In one first-bind pair
over the same frozen Store, operand time fell from 369 to 183 ms,
cold bind from 13.085 to 12.830 seconds, and checked Store-bound
queries from 4,993 to 3,749. The exact theorem and malformed and
foreign operand checks passed. Receiving certificate smoke passed,
and the two-file ceiling change is unstaged on local main. See
`results/nc-comma-mapped-action/receiving-operand-first.log`.

The full receiving-tree detailed run hit the concrete B1 limit at
300.020 seconds. The structured watchdog recovered zero-based root 0
in projected evaluation after its program action completed. It reported
no rejected or partial progress records. The completion checkpoint
for bind start ordinal 2,048 recorded 50.749 seconds of indexed-slot
normalization. That ordinal counts starts, and recursive bind proofs
can finish out of order.
The same-source uninstrumented run timed out at 300.038 seconds. Its
reporter was off. The tested receiving reporter is unstaged on local
main and preserves fail-closed admission. The typed JSON boundary and
watchdog follow-on passed 45 guarded runner tests and scoped Pyright,
mypy and Ruff. See
`results/nc-comma-mapped-action/receiving-progress-operand-b1-detailed`
and `results/nc-comma-mapped-action/receiving-progress-operand-b1-off`.

On the working tree at `f55418a7`, guarded proofs now enable coarse
checkpoints by default. A fresh unflagged Isabelle probe emitted all four
expected records with detailed profiling off. A separate native timeout
probe retained `verify-input` as the last completed scope and `await-timeout`
as active. The SIGTERM regression confirmed that late failure records leave
that snapshot intact. The receiving runner selection and first-arc arithmetic
fixture passed 49 tests, and the five changed Python files passed strict
Pyright. See
`results/nc-comma-progress-default/` for the probe and runner evidence.

On the `bf373b4` proof parent, a 19.402-second guarded fixture checked a
source-wide typed Stop with fewer than 930 crossings, its ordered physical
transport and the conditional B32 rule for empty Continue32 support. The
32-step catalogue support certificate remains open. See
`results/nc-comma-first-sector/typed-stop-support-bf373b4-v3.log`.
On the same parent, an 84.613-second fixture checked the ordered Z7,
Z8 and Z9 source joins and rank-free finite derivations for six authored
classes. It rejected a forged phase and swapped physical arms. These
bounded proof changes remain isolated. See
`results/nc-comma-first-sector/real-finite-source-bf373b4-v3.log`.

The isolated v4 receiving candidate now checks the finite partition with
an iterative traversal before decoding the immutable source MDD. The two
scratch allocations have disjoint lifetimes. The authored candidate fits
the existing 131,072-node budget, and the guarded 113-test selection covers
codec parity, a deep cycle, provider reuse, corruption and empty-registry
refusals. See `results/nc-comma-next-replacements/v4-receiving-final/`.

On the same `bf373b4` parent, the checked bitmap walk supplied exact
geometry for 32 authored classes in 24.909 seconds. A 19.886-second
synthetic fixture checked the combined finite and live geometry issuer,
including wrong-mask and ordered-child refusals. The B32 prerequisites
checked exact class bindings for 0, 1 and 19 and, separately, ordered MDD
composition with distinct Continue, terminal and unresolved results.
A bounded sparse-live fixture also checked the exact mask support before
selecting rows and rejected a missing support ID. Four authored live rows
passed their ordered checks. The all-314 authored trial hit the 300-second
guard during numeric support normalization, before selecting rows.
Local main carries the
independently checked class-binding correction. It normalizes closed
decoded arithmetic before the existing exact program check.
The 191.896-second shared fixture checked the real transition
`0@5 → 19@6 → 29@7` in one frozen store and rejected the wrong root and
unshifted child. Its checked typed roots used 718 direct MDD applications,
compared with 1,239 in the separate-root trial. Catalogue-wide Continue32
support remains open. See `results/nc-comma-first-sector/` for the guarded
fixture logs.

The registered grouped first-arc fixture passed in 19.960 seconds using
three checked round packets. It establishes the unique prefix, the exact
ordered fork and 143,298,005,693 physical ticks to either child. A separate
16.470-second build checked the same packet for admitted exponents in
phase 10, with symbolic elapsed weight and a two-digit width increase.
The selection theorem for the weighted cycle remains open. See
`results/nc-comma-mapped-action/weighted-anchor-grouped-v8/build.log`.

The combined eight-file strict Pyright batch and documentation index
passed on local main. The comma P0 selection passed 14 checks. Six
positive admission assertions still fail because the packaged global
artifact is absent. See
`results/nc-comma-future-source-reach/main-reporter-c1-comma-p0`.

The checked indexed conversion and selected-row composition replace
per-slot simplification in the receiving bind replay. Five alternating
pairs on one 2,266-node frozen Store checked the same closed theorem.
Median cold bind fell from 13.994 to 6.401 seconds after 4.916 seconds
of shared Store preparation. Each pair replaced 1,023 generic slot
rewrites with direct conversions. The fixture rejected a wrong slot,
child, label, foreign Store and malformed operands. Registered
certificate smoke passed, including exact fallback and order checks.
The five verified files are unstaged on local main. See
`results/nc-comma-mapped-action/current-main-indexed-five.log` and
`results/nc-comma-mapped-action/receiving-indexed-smoke`.
The receiving candidate based on `f55418a7` had proof-source
fingerprint `97cbe2e7028b` for its uninstrumented concrete B1 run.
It timed out at 300.057 seconds in the Frontier24 source bridge. See
`results/nc-comma-mapped-action/receiving-indexed-b1-off`.
The detailed run on that same 765-file proof source timed out at
300.040 seconds. It completed root 0 and root 1's program action. The
active scope was root 1 projected evaluation. The last sampled bind
completion was the call with start ordinal 3,328, by which point 3,335
binds had started. At that checkpoint selected cofactor calls accounted
for 73.662 seconds, with 20,562 builds and 29,698 hits. These scope
timers describe recorded calls and can overlap. See
`results/nc-comma-mapped-action/receiving-indexed-b1-detailed`.
The direct selected-child rule passed five alternating pairs on the same
frozen Store. Equal-output slots still require different indexed
equations. The fixture rejected wrong slot, root, axis and foreign
Store evidence. Median cold bind fell from 6.645 to 3.900 seconds.
Shared Store preparation took 4.900 seconds and median replay setup
took 4 ms in both arms. See
`results/nc-comma-mapped-action/selected-branch-five.log`.
The production-form certificate smoke passed. The two verified proof
files are unstaged on local main. See
`results/nc-comma-mapped-action/selected-branch-production-smoke`.
The changed concrete B1 build at proof fingerprint `16142e94066d`
timed out at 300.000 seconds. It completed roots 0–6 and stopped in
root 7 payload cover. The trace recovered the active scope without
rejecting or truncating records. Selected cofactor calls totaled
10.143 seconds at the sampled completion of bind start ordinal 4,096.
The same checkpoint recorded 30,629 selected-target proof builds in
50.715 seconds and 757 indexed vector preparations in 14.401 seconds.
These timings are separate from payload cover, which took 5.542 seconds
for class 0. The receiving issuer still calls the full cover checker at
each root in that run.
See `results/nc-comma-mapped-action/selected-branch-production-detailed`.
`comma_mdd_action` ported the reachable payload cap to that receiving
proof source. Registered smoke passed the reachable-243, tighter-cap,
foreign-root and stale-root checks. Five alternating native trials on
root 199 of the same frozen first-bind Store measured 4.306 seconds for
cover and 0.073 seconds for cap. Both produced closed, audited native
certificates. A separate one-pair check derived identical conditional
evaluation bounds from both. The four verified files are unstaged on
local main. The uninstrumented concrete run at proof fingerprint
`47dbea66e70c` entered the source-bridge construction and timed out at
300.065 seconds. The source bridge's `local_setup` was the last recorded
checkpoint. See
`results/nc-comma-mapped-action/selected-cap-matched.log`,
`results/nc-comma-mapped-action/selected-cap-equality-result2.log`,
`results/nc-comma-mapped-action/selected-cap-smoke` and
`results/nc-comma-mapped-action/selected-cap-production-off`.
Two stale source assertions failed before and after the cap port. They
now check the actual miss-only witness admission and checked issuer
publication. All 48 receiving source checks passed. See
`results/nc-comma-mapped-action/selected-cap-receiving-source-checks`.
The isolated support-first mixed-branch rule and replay passed the
registered generic B1 build. The focused fixture rejected foreign Store,
changed target and same-child wrong-slot evidence and passed with
irrelevant projections poisoned. Five interleaved cold replays on the
same frozen Store took 3.521 seconds for direct cofactor replay and
3.802 seconds for support-first. Both arms shared 4.536 seconds of
source and Store preparation and proved equal conclusions. The
candidate remains isolated and the concrete B1 gate was skipped.
See `results/nc-comma-mapped-action/support-replay-matched-five.log`
and `results/nc-comma-mapped-action/support-replay-mixed-retry.log`.


### November 22 symbolic comma release check

On the receiving tree based on `f55418a7`, the independent symbolic
run proposed zero Continue32 support for all 46 classes and checked
the frozen 51,716-node Store. The 300-second guard stopped the first
structural replay layer after the sampled completion at bind 512.
The generic bridge from exact checked roots to source-bound typed B32
Stop passed natively in an isolated fixture. It still requires the
concrete root equalities. The bounded Future support fixture passed
separately. Source-wide ordered N/Z authentication and the weighted
cycle receipt remain open.

The isolated v4 wheel installed cleanly. Both comma requests at indices
1 and 412,987,861 refused with the unresolved-boundary result. The
positive release check found no admitted v4 artifact. Local main
retired the two unreferenced Direct Trial and Checked Instance leaf
sessions, retaining their shared theories. The 79 default proof-index
tests passed. The exhaustive index still reports 25 pre-existing
oracle-audit gaps. Guard logs and the Direct Trial local-edit recovery
patch are in `results/nc-comma-symbolic-cutover`.

The follow-up on proof parent `bf373b4a` checked the typed one-step
root-to-span bridge. On the same real class-0/class-19 input, omitting
the unused support projection preserved the bind and shift propositions
and skipped 94 mapped certificates. The replay scope took 6.722 seconds
versus 7.398 seconds. Both arms built 977 cofactors and took about 196
seconds under the guard.

Across all 46 classes and five layers, the proposal comparison matched
212,520 values and still proposed zero final support. Deferring support
construction reduced Store nodes from 51,716 to 47,510. The changed
structural run checked the Store in 147.4 seconds versus 164.1, then
timed out at 300.178 seconds in the first replay layer. The last sampled
completion was bind start ordinal 768, versus 512 in the baseline.
At the matched 512 checkpoint both built 8,168 selected cofactors.
See `results/nc-comma-symbolic-cutover/authored32-action-profile.log`.

The bounded Future selection receipt checked the Z7 physical crossing
with fixture liveness and rejected a wrong slot, child or phase.
A separate bounded graph checked finite/live coverage from exact
disjointness and size, rejecting a missing class and overlapping lists.
See `results/nc-comma-first-sector/source-selection-receipt-bf373b4-v1.log`.

The next B32 candidate uses one checked source vector per same-axis
branch while preserving per-slot target and ordered witnesses. The
matched real fixture reduced selected cofactor builds from 977 to 53
and replay from 6.722 to 4.582 seconds, including rejection of
same-child wrong-slot, wrong-root and wrong-shift evidence. Guarded
totals, including setup, were 195.390 and 192.259 seconds. On all
classes it reduced selected cofactor builds at checkpoint 512 from
8,168 to 3,471. The changed run timed out at 300.205 seconds in the
first replay layer, with bind 1,024 the last sampled completion.
See `results/nc-comma-symbolic-cutover/authored32-source-family-profile.log`.

The authored Future graph partition passed in 32.435 seconds.
Successor-first replay checked all 4,402 finite classes and symbolic
support checked all 314 live classes. Numeric rank fields were cleared
before publication. The physical source-wide ordered morphism and
writer authority remain open. See
`results/nc-comma-first-sector/authored-live314-partition-bf373b4-v1.log`.
A 32.101-second bounded build joined the checked weighted N2 phase-10
anchor to the exact authored class points, Fork7 row and ordered
phase-12 children. It checked North as the live arm for that row and
143,298,005,693 physical steps to either child, rejecting a wrong
phase, swapped order and wrong elapsed weight. This covers one arc.
See `results/nc-comma-symbolic-cutover/anchor-weighted-receipt-v3-build.log`.

On receiving revision `b68468f9`, the release gate now checks the symbolic
authorities through production theory imports, attached ML resources, and
native theorem dependencies. A guarded native fixture rejected retired
Bellman authority reached through an intermediate theorem. The installed
release gate requires the v4 asset and compares its bytes with the export
from the guarded build. The production dependency regression is red while
the legacy B32, rank, and writer authorities remain. The guarded receiving
selection passed 180 checks alongside that failure, and strict mypy and
Pyright passed for the changed Python files.

The registered `Comma_Semantic_B1` build passed in 216 seconds after
checking the phase-134 termination proof and the source-bound typed Stop
provider. Its proof dependency audit excludes packed termination authority.
The registered `Comma_C1_Occurrence` build passed in 87 seconds and
checked exact elapsed time and earliest crossing within one sector.
The receiving `Comma_Semantic_Future` session passed in 30 seconds on
warm parents. Its typed provider and ordered-child theorem use the
authenticated crossing seam. Explicit induction replaced a uniqueness
proof that exceeded the memory guard. Exact B32 coverage and source-wide
elapsed transport remain open.

The isolated rank-free Future graph checked all 4,716 class rows in a
25.279-second guarded registered build. The issuer discarded the proposed
rank fields before proof construction. It still needs source-wide physical
ordering before it can authorize release. A separate 10.270-second guarded
fixture checked writer composition and demanded cuts for already admitted
adjacent actions. A second native fixture checked the direct Entry cut from
a period quotient and bounded remainder, together with both literal paths
at every cut through the Near seam. A 12.407-second guarded fixture on
warm parents checked the direct Near cut and its composition with Entry
through the first-sector preterminal. The concrete ordered cycle, exact
weights, width transport, and v4 export are still required. See
`results/nc-comma-production-cutover`.

### November 22 quotient-first family ports

The receiving baseline was `b68468f9f944d6a332aad75a8ea3b367b2faa598`.
The four donor patches target different predecessors. The receiving tree
uses its existing source, action and publication owners.

- The reflected H compiler evaluates one inlet per reached block phase
  in certified repeated SLP regions and preserves both finite seams.
  The 5rev10 terminal transfer uses the issued source action and requests
  a chronological history only for a trace.
- The Collatz cyclic action projects an admitted partial motif alongside
  the complete repeats, sharing its source endpoint across consumers.
  An explicit boundary witness retains the existing packet and position
  harmonics.
- The Mahler root action uses the existing transfer's safety evidence.
  An empty real guard stops further rational guard pullback.
- Fermat compiles a requested power as one final source-bound span.
  Its matrix compiler shares dyadic checkpoint factors and uses a signed
  positional bank where it covers the requested modulus.

The donor cyclic carry-sheet and Fermat wrapped-product engines have no
live counterpart on this baseline. The scope here is the authenticated
paths exposed by the receiving tree.

The guarded family and CLI selection passed 3,272 tests in 50.75 seconds,
with 140 validation cases deselected. The registered Isabelle sessions
for Double Reverse, Five Reverse, Collatz, Mahler and Étale passed.
The complete Collatz source-wide partial-tail refinement remains open.

Five interleaved trials on identical inputs matched every compared packet.
Median time for the pre-issued Fermat power fell from 445.15 to 16.06 ms,
with checkpoint batches reduced from 12 to one. The reflected H compiler
published five blocks instead of 1,537 and took 3.93 ms for ×2 and 3.41 ms
for ×5, down from 13.47 and 12.86 ms. The 5rev10 terminal observer fell
from 8.17 to 2.82 ms. The Collatz combined compiler fell from 9.52 to
7.74 ms on seed 1486 at 24 ticks. The Mahler observer published one source
projection instead of two. Cold process medians across the five CLI
controls changed by less than 5%.

Strict typing and Ruff passed for the changed family files. A freshly
installed wheel returned all six checked family results and shared one
Mahler source projection across combined observations. The complete
wheel release gate still requires the admitted Comma v4 artifact.

### November 23 production quotient ports

The receiving revision was `b68468f9f944d6a332aad75a8ea3b367b2faa598`.
The isolated receiving snapshot `35d77a91` includes the unstaged November 22
ports. Its guarded CLI baseline passed 124 tests. The six donor patches
were reconciled against the snapshot's existing consumers.

- Direct Fermat matrix requests omit the unused Moore periods. Explicit
  phase requests retain them. The conditional affine row shares the
  existing exact low endpoint and checkpoint authority.
- Collatz conditional snapshots reuse the sealed tape action and retain
  the shape check. Issued cyclic prefixes support exact suffix and
  moving-cut transport. The stamped boundary candidate changed the public
  observation packet on source 352164 at tick 30, so the existing path
  remains selected for that demand.
- Repeated Mahler associated-action requests reuse a charged, evictable
  response after authenticating the receiving source. On the 1,024-return
  benchmark, composed-image reads fell from 26 to one and the warm median
  fell from 0.543 to 0.470 ms. The matched cold controls stayed within 0.5%.
- Repeated Q19 fields reuse an ordered base-64 motif and remainder. The
  owner binds cached numeric responses to the receiving occurrence.
  Source-qualified physical landmarks publish as one charged bundle.
  The reverse/add modular observation keeps its existing no-term path.

The 4,096-tick F5 direct matrix matched every packet in five paired trials.
Cold CLI median fell from 213.17 to 173.40 ms and the in-process request
from 75.45 to 34.30 ms. Cache bypass fell from 111.39 to 67.21 ms. The
baseline built 490 orbit observers per demand and the replacement built
zero. The matched Collatz snapshot fell from 0.585 to 0.053 ms and removed
all 25 redundant tape folds while preserving the checked snapshot.

Repeated Q19 publication and recovery fell from 38.03 to 28.26 ms on
the 2,048-digit repeated source. The warm H12 request from generation 108
to 64 fell from 0.218 to 0.105 ms and skipped all 52 remaining physical
callbacks. Cache bypass still performed 64 callbacks in both arms. The
dense seed-196 owner median rose from 9.30 to 9.90 ms with the same 511
successors. All six matched cold CLI controls stayed within 1%.

The guarded family unit selection passed 4,426 cases and the applicable
P0 selection passed 32. The exhaustive selection passed 104 cases with
one retained route-counter failure, reproduced at the same assertion on
the receiving baseline. The registered Reverse, Collatz, Étale and Mahler
sessions passed. The Reverse build checked the exact geometric division
used for the packed repeat and the H12 physical seam. The Collatz build
checked the moving-cut numerator and retains the existing midpoint
composition theorem for typed suffix transport.

The lower 5rev10 adapter bands failed the performance gate. Matched
medians rose from 1.24 to 1.72 ms at 1,536 bits and 32 ticks, and from
1.96 to 2.28 ms at 3,072 bits and 16 ticks. The 64-tick cutoff stays.
The Antihydra cyclic trial also missed the gate across the tested
authenticated 8-bit classes. The existing transient owner remains in use.
Strict mypy, two serial Pyright batches, Ruff, formatting, and docs passed
for the changed sources. The fresh wheel matched seven family CLI
requests. Full package admission still requires the Comma v4 artifact.
Source policy reported the existing Comma findings. Evidence is in
`results/nc41-nov23-integration`.

### November 23 cyclic diagonal follow-up

The guard runs compared the dirty receiving tree at `b68468f9` with
the frozen receiving snapshot `f1573456`. The Collatz scheduler now
selects primitive ordered rotations and uses their source defect to
compute the exact extent and Laurent fields. The diagonal CLI reads
low bits of the already-issued normalized endpoint. It keeps the
physical half-step and source checks. Antihydra's existing repeat
producer folds a final incomplete motif into the admitted action
with its exact ledger minimum and elapsed weight. The shared upper
port reduces wide coefficients before multiplying at the demanded
precision.

Five paired trials preserved the exact outputs. Collatz cyclic
field construction fell from 0.066 to 0.011 ms on the seed-1486
fixture. The certified 127-tick Antihydra action fell from five
pieces to one and from 0.0111 to 0.0067 ms. The narrow shared cut
fell from 0.044 to 0.032 ms. Final cold CLI medians stayed within
1% on all five controls. The Collatz diagonal CLI median changed from
2.82 to 2.76 ms warm and 2.84 to 2.77 ms with shared-cache bypass.

The native Shared Carry Dynamics, Collatz Cylinder Refinement, and
Antihydra sessions checked the modular cut, rotated source defect,
and ordered partial-repeat seam. The guarded checks passed 1,929
affected units, 181 validation cases, and eight P0 cases. Strict typing,
Ruff, formatting, and docs passed for the changed sources. Four
installed-wheel CLI packets matched. Repository-wide source policy
still reports the existing Comma findings. The graph and continued-fraction
patches require source owners absent from this checkout. The live
Mahler matrix request retains its direct constructor. Whole-package
release still requires Comma v4 admission. Evidence is in
`results/nc41-diagonal-followup`.

### November 23 Mahler finite quotient integration

The receiving HEAD was `b68468f9` and the isolated dirty-source snapshot
was `0881877d`. The donor dependency chain supplied the compact arithmetic
laws. The installed CLI uses the existing registry and arithmetic result
owner. Finite safety and graph actions share the selected centered source
and an exact fractional tail. The graph catalogue covers the two rotations
of the 60/40 row. The independent ×5 diagonal band shares the existing
ordered matrix algebra and charges its result through the query scope.

Five matched construction trials measured 0.654 to 0.315 ms for an
80-copy rational safety run and 1.584 to 0.116 ms for 128 checked graph
row joins. The six-row CF band at exponent 1530 took 0.096 to 0.024 ms.
These are component timings. The final ordinary CLI comparison used five
interleaved windows of three fresh process pairs. All four outputs matched
and their median wall times were within 3%. Width-one CF bands at exponent
1024 or higher and at least six rows use the compact action. Other admitted
bands use the exact ordered row fold.

The registered Mahler source session checks the finite failure boundary,
ordered graph source and rotation, and the exact CF lift, width, split,
and repetition. Guarded checks passed 600 affected units and 170 validation
cases. Five fresh-wheel queries matched. Strict typing, Ruff, formatting,
and documentation passed. Source policy reports the existing Comma findings.
The P0 selection has the same source-7
certificate failure as its receiving baseline. The whole-wheel admission
gate still requires Comma v4.

### November 23 finite continued-fraction cylinder

The receiving HEAD was `b68468f9` and the isolated dirty-source snapshot
was `9d321dc0`. The existing continued-fraction observation accepts a
finite physical horizon. Its ×5 publisher advances the shared grammar
with the reached inlet, compacts obsolete roots, and reuses the bounded
low suffix at an authenticated cut. The cylinder preserves the ordered
continuant and retains the first decisive prefix. Multi-tick temporal
tiles stayed experimental after their longer-row trials regressed.

`Mahler_Source_Transport` rebuilt in 19 seconds under the standard
guard. It checked the carry-selected publisher, low-period transport,
and midpoint refinement on the canonical ×5 stream. The guarded
selections passed 503 units and 189 validation cases. Five fresh-wheel
queries matched, including coefficient exhaustion and the full
4,096-tick result. The latter uses 540 coefficients. The preceding
prefix fails the independent rational check. Ruff, formatting, strict
mypy, and Pyright passed on the changed sources.

Five matched construction trials measured 14.5 to 11.6 ms at 512 ticks
and 839 to 621 ms at 4,096 ticks. At 20 ticks the authenticated setup
added about 0.18 ms. The largest median change on ordinary cold controls
was under 4%. Source-7 non-halting and Comma v4 package admission remain
separate holds. Evidence is in `results/nc41-cf-cylinder`.

### November 23 wide continued-fraction tiles

The receiving HEAD was `b68468f9` and the isolated snapshot was
`acac507b`. The shared one-tick tile engine now streams a dense inlet
once through its charged grammar iterator. At source exponent 512 the
profile found 360 interval walks and 129,236 length callbacks. Five
matched tile trials including halo trim and cleanup took 31.28 to
6.32 ms median. Source preparation was measured separately.

The continued-fraction band CLI uses the existing ordered split on
admitted wide requests with 16–128 digits per row and at least 1,024
digits in the band. It preserves the direct admission budget and keeps
the receiving phase in the ordered product. Both phases of the 6/3
repeat match independent physical digits and give different matrices.
With the default 10,000-node cap, three wide fixtures took 1.93 to 1.70,
1.88 to 1.63, and 1.89 to 1.58 ms in the matrix phase. Cold CLI packets
matched across five paired trials. The largest median increases were
1.6% on a wide band and 2.4% on an ordinary control.

`Mahler_Source_Transport` rebuilt in 33 seconds. It checked the dyadic
tile output through both zero halos, exact high trim, physical exponent,
and ordered CF slice.
Ordinary cylinder rows still favor the pointed source, and the existing
modular lift wins on a one-row band. The whole-row multi-tick CLI
dispatch remains held on those performance results.

The guarded affected sweep passed 1,327 tests, followed by 123 focused
checks of the final runtime and tests. Six fresh-wheel packets matched.
Strict typing and pinned lint passed for the four changed Python files.
The existing Comma v4 package admission hold remains. Evidence is in
`results/nc41-cf-tiles`.

### November 23 ordered ×5 cylinder

The receiving HEAD was `b68468f9` and the isolated snapshot was
`c530515d`. The existing finite CF CLI admits bounded packed ×5 blocks.
Each block folds all intervening rows in physical order into one content
grammar. The consumer extends its affine guard once per block and searches
within the first decisive block. Tight remaining ledgers select the pointed
source before allocating packed staging.

The independent 4,096-tick fixture forces the horizon at coefficient 540.
Coefficient 539 is insufficient. The production query issued 11 blocks and
bounded final-block lookahead to 24 additional coefficients. The 54 matched
budget cases preserved exact answers and refusals. Peak ledger charges for
the full fixture were 5,420 nodes on the pointed source and 8,779 on packed
staging under the standard 10,000-node cap.

Five interleaved cold CLI trials gave 166 to 143 ms at 20 ticks, 188 to
171 ms at 512 ticks, and 897 to 162 ms at 4,096 ticks. All packets and exits
matched, as did ordinary term and help output. The largest increase on a
control was 4.4%. These measurements cover the geometric packed producer
and the lean guard together. The separate spatial tile replay trial was
9–31% slower when it retained all intermediate rows.


The 39-row source-and-continuant phase took 15.63 to 6.25 ms. Genuine
bypass took 6.34 ms. Repeated partial-prefix projections took 11 µs
median with the issued content map and 81 µs with bypass.

The guarded `Mahler_Source_Transport` build passed in 31.9 seconds. Both
new theories passed the oracle and skipped-proof audits. The checked
producer compiles the three guarded batch forms into the exact physical
clock, affine action and half-open guard. A stalled earlier block cannot
contain that completed guard. The binary consumer selects the least
prefix of the canonical ordered rows that does contain it.

The affected selection passed 783 tests. Ruff, formatting, strict mypy
and Pyright passed for the changed Python files. Nine fresh-wheel checks
matched, including the coefficient-539 refusal. The repository's Comma
v4 admission and baseline source-policy findings remain separate holds.
Evidence is in `results/nc41-cf-ordered`.

### Spatial ×5 rows for CF cylinders

The follow-up against receiving snapshot `daa73c8efd51` uses the spatial
producer for admitted horizons from 64 through 4,096 physical ticks.
Earlier horizons use geometric rows. The whole-inlet convolution, halo
and ordered byte continuant retain their checked laws. Fixed lane masks
are reused, the zero-run test cancels a common factor of two, and the
final residue powers the inverse of 3 modulo the physical dyadic modulus.

The shared-cache query phase fell from 0.589 to 0.213 ms at 64 ticks and
from 9.391 to 7.372 ms at 4,096. With the same compact publisher at 4,096,
geometric and spatial totals were 7.610 and 7.557 ms, and spatial source
construction took 0.357 ms against 0.416 ms for geometric. Cold CLI
medians across both matched samples were 132.91 to 131.93 ms at 64 ticks
and 147.78 to 142.31 ms at 4,096. The first 1,024-tick cold sample rose
5.8 percent. Its paired confirmation and pooled comparison gave
143.77 to 130.35 ms and 133.66 to 133.59 ms respectively. All packets and
exit statuses matched.

The registered `Mahler_Source_Transport` build passed in
84.4 seconds, including the endpoint cancellation
and inverse-power checks. The affected guarded selection passed 798
tests, including cutoff and lane boundaries. Evidence is in
`results/nc41-cf-tuning`.

### Shared ordered bands and guarded row rotation

The receiving HEAD was `b68468f9`, with dirty-tree snapshot `140d8006`.
The shared matrix owner now compiles shifted decimal bands, fixed-width
rows, and ordered decimal words. The CF band and block publishers consume
these operations. The existing reverse/add and 2rev10 digit-band publisher
and the 5rev10 digit-band producer share the same continuant, with their
respective digit orders.

Across five exact-output pairs, CF width-16 and width-32 band construction
took 1.854 to 0.690 ms and 1.845 to 0.603 ms. The 5rev10 band used
1,056 products instead of 2,048 and its construction took 2.831 to
1.867 ms. Its cold CLI median was 141.57 to 133.30 ms. Reverse/add's
cross-center Q19 guard shared one admitted grammar fold across rotations,
reducing visits from 108 to 54 and taking 0.120 to 0.081 ms. Collatz
shared the primitive-word rotation and checked binary content on cache
misses. The 510-word construction median fell from 2.029 to 1.846 ms.

The adaptive CF trial preserved the 540-coefficient result and reduced
spatial leaf evaluations from 16 to 14 at 4,096 ticks. The tuned
block-construction median was 377.9 to 377.2 µs with sharing. The
canonical workload supplied zero reusable entries to the selector probes.
The adaptive path missed the 5% speed gate. The existing 64-tick spatial
policy stays in production. Antihydra graph actions and Fermat/Mersenne
rotation reuse still need checked receiving seams.

The registered shared carry, 2rev10, 5rev10, Collatz, Mahler, and reverse/add
sessions passed under the native guard. The new rotation, source transport, and modular band facts passed their
local oracle audits. The guarded selection passed 841 tests and 35 P0
checks. Strict mypy, Pyright, Ruff and formatting passed for the 15
changed Python files. Seventeen fresh-wheel comparisons matched. The
repository source and proof-index diagnostics match the receiving tree.
The package release check remains blocked on Comma admission.

The cold requests above the 5% threshold got one five-pair confirmation.
Both samples are retained. The last column uses the median relative
change across the ten matched pairs.

| Request | First cold medians, ms | Confirmation, ms | Matched change |
| --- | ---: | ---: | ---: |
| CF 63 ticks | 124.50 → 132.61 | 131.38 → 133.23 | +1.25% |
| CF 128 ticks | 123.25 → 130.41 | 123.61 → 124.75 | +1.42% |
| CF band | 136.86 → 161.47 | 116.28 → 113.98 | −0.95% |
| Help | 77.43 → 87.44 | 71.60 → 70.98 | +1.47% |
| Collatz term | 314.78 → 342.35 | 264.98 → 265.08 | +1.10% |

Evidence against the snapshot is in `results/nc-cf-band`.

### Source-qualified CF band reuse and cold audit

The live diagonal band publisher uses the existing process lease before
building the lift. Its binding records the diagonal origin, width, and final
cut. The issued payload retains the exact continuant and the lifted value
required by the CLI packet. An identical warm request does no row decoding
or matrix joins. A one-row advance with the same endpoint shifts the lift
by one bit and cancels the first row using its signed adjugate. The registered
`Mahler_Source_Transport` build checked the preserved significant-width
guard and exact chronological tail.

Five matched trials put eligible repeated producer calls at 0.038–0.042 ms,
down from 0.50–4.78 ms. The three eligible shifted cases went from
2.09–4.79 ms to 0.063–0.071 ms. Fresh CLI band and ordinary controls stayed
within the 5% limit, with equal packets. The regressions poison lift and
recursive band construction, count the one boundary join, and exercise
changed origins, endpoints, widths, and reduced budgets.

The spatial CF cylinder remains on the 64-tick policy. A census of 4,033
default-cap horizons found zero repeated root or leaf keys across 32,300
spatial issues and 15,706 split-leaf lookups. The 56 clipped cases also
found zero hits. A separate same-owner tile fixture showed a root hit
at 0.67 µs against 13.71 µs with bypass. The 4,096-tick cylinder selector
trial went from 7.71 to 7.65 ms. Fractional guard extension accounted
for about 71% of the profiled current call.

The `pow5q` donor's floor sum counts complete rows. At horizon 64 those
rows have 1,485 coefficients, while the live cylinder certifies its physical
horizon at coefficient 10. A lower dyadic phase alone also leaves full-row
weights undetermined. For example, powers 40 and 48 have the same residue
1 modulo 32 and widths 28 and 34. Cold CF and Collatz carry-event powering
still need an ordered source-bound action in the requested ring. The
donor supplies a cold-linear hold and no native proof of that action.

That audit held Mahler graph rotation pending an admitted adjoining source
and ordered safety transport. Centered source 16 returns to its displayed port at 36
with a different mod-80 admission. Fermat and Mersenne still need complete
signed or borrow-puncture seams. Their existing exact adjacent joins
already share the ordered row helpers.

The audit repaired transactional cache recency, null-target conflict
detection, and CF and Bellman reservation cleanup. The affected guarded
selection passed 742 tests and 35 P0 checks. Fresh-wheel cold, warm, and
shifted band checks matched. The package-wide Comma admission hold
continues. Evidence is in `results/nc-cf-band/reuse-audit`.

### November 24 bounded CF and rotation seams

The receiving snapshot `2e095975` captures dirty `main` at `b68468f9`.
The tested candidate is `d0209743`. Four bounded changes reached the
existing production callers.

| Consumer | Admitted reuse | Matched targeted median |
| --- | --- | --- |
| Exact CF diagonal band | Issued following cut with the same origin, width and endpoint, within existing cache limits. Recover one lift bit and prepend one ordered row. | 0.527→0.064 ms, 0.740→0.085 ms, and 1.534→0.063 ms |
| Mahler graph | Complete adjoining copies of the 60/40 row with checked source valuation and fractional guard. The shared zero-run action supplies the closed form and preserves ordered safety. | 19.97→11.46 µs at two copies and 102.88→17.00 µs at 128 copies |
| Collatz carry event | Every demanded cut is within the admitted centered valuation. Phase construction is deferred and the first positive hit and moving correction remain exact. | 15.88→12.87 µs |
| Mersenne trace matrix | Positive position with zero gradient in the first two trace phases. Reuse the authenticated endpoint for every conditional high digit. | 0.769→0.255 ms for pointed and conditional powers at exponent 44, with calls reduced from three to one |

The CF result retains its exact lifted value and the forward adjugate
transport. Identical warm, bypass, and cold producer controls held steady,
with the same retained cache bytes. Five interleaved fresh-process trials
matched the CLI packets. The initial power-number cold controls exceeded
5%. A confirmation with bytecode prepared in both trees stayed within
2.42%. CF cold controls stayed within 2.6%, and the final radial controls
stayed within 1.67% regression.

The registered `Collatz_Cylinder_Refinement`, `Temporal_Clock_Jumps`, and
`Mahler_Source_Transport` sessions passed in 28, 56, and 115 seconds
respectively, including the affected oracle and skipped-proof audits.
The guarded affected selection passed 1,129 tests. Strict mypy, changed-file
strict Pyright, Ruff, formatting and docs checks passed. The P0 selection
reproduced the baseline's nine non-halting and primality failures with
13 passing checks. The source-policy report matched the baseline and the
broader proof index still has inherited failures. The graph theory now
has an oracle audit.

The fresh wheel matched the twelve affected CLI fixtures. The package-wide
check remains held on Comma admission. The 64-tick CF cylinder policy
continues. The transient four/eight-step action needs an admission path
that reaches reuse affordably before the parity probe. The Fermat
wrapped-product seam still lacks a checked receiving CLI consumer, and
the larger Mersenne trace rotation needs checked source-local period
transport. Evidence is in `results/nc-bounded-seams/2e095975`.

### November 24 NC43 production repairs

The receiving checkout was clean at `af2000d338`. The isolated runtime
candidate is `03328a90`, with the final fixture typing check at
`8960cb53`. The five donor patches were checked individually and
reconciled at their live producers and proof owners.

| Consumer | Validated scope |
| --- | --- |
| CF diagonal band | A complete lifted overlap admits the primitive product. The ordered compiler probes completed children before period discovery, uses an exact rotated product and remainder, and retains both cache-cut directions. |
| Antihydra/Mahler | The nonretaining scheduler accepts a complete or majority four/eight-step source period before descending. A single bounded response supplies the guard and arithmetic. Ordered minima and first-failure descent retain their physical coverage. |
| Collatz | The first physical boundary stamp precedes the cyclic suffix. The issued action preserves the source, clock, phase, and weighted carry. Binary and decimal moving cuts remain bounded by the admitted action. |
| Fermat | The signed binomial certificate proves F5 composite with proper divisor 641. Either theorem demand order can reuse the issued witness with a zero ring-product budget. Harmonic matrix verification compares the issued structure without producing a second token stream. |

Five interleaved matched trials measured the 1,024-row CF band at 3.51 to
0.31 ms and a warm repeated request at roughly 0.04 ms in both trees. Both
cache-cut directions kept their retained bytes and results. The Antihydra
full and partial 1,024-tick effects went from 94.0 to 34.2 µs and 154.5 to
93.5 µs. The ordinary arithmetic controls cost about 13% more in that
producer. Their fresh CLI and safety controls stayed within 1%. For Collatz
seed 352164 at 30 ticks, the exact guarded work dropped from three actions
to two and from 2.62 to 1.85 ms. The innovation packet's executed 6305R count
dropped by one with the endpoint and projections equal. The Fermat F5
matrix went from 162.2 to 150.7 ms in fresh processes. Its source-matrix
phase went from 32.2 to 20.9 ms.

The registered `Collatz_Cylinder_Refinement`, `Mahler_Source_Transport`,
and `Etale_Primary_Carry` sessions checked the consumer refinements with
oracle and skipped-proof auditing. Their changed builds took 24, 45, and
94 seconds respectively.

The default selection finished in 218.80 seconds with 13,812 passing
tests and seven inherited failures. All three Antihydra puncture
regressions closed. The affected exhaustive selection passed 5,087 tests
with the same two Q19 failures. Canonical P0 moved from 75 to 77 passing
checks and from 15 to 13 failures. The two F5 checks closed, and there
were no new failing IDs in any selection. The final focused recheck
passed 100 tests.

Strict mypy, Pyright across 2,617 files in 105 guarded batches, pinned
Ruff, formatting, and docs checks passed. Source policy and the broad
proof index reproduced the baseline findings. The fresh wheel matched
eleven family CLI packets and returned the new F5 result with zero
charged products. The installed API reused the same witness in both
demand orders at product budget zero. The package-wide admission check
still lacks the accepted Comma future.

The reciprocal CF cylinder missed the 5% gate at longer horizons. The
64-tick receiving policy stays in use. The Q19 rotation improved 2.5%
and the protected stencil regressed 6%. The reflected publisher improved
on the standalone 129-generation case, but its live 256-tick CLI
request regressed 30.5%. The traced publisher time was 27.4 to 110.5 ms,
including a 0.14-ms admission probe. The reversal candidates and the
lower packed `5rev10` cutoffs were held. No additional wrapped-product
consumer had a complete checked receiving seam. Comma admission,
source-7 non-halting, unrestricted future closure, F4/F6 and unresolved
Mersenne primality remain separate obligations.

Evidence is in `results/nc43-production-af2000d3`.

### November 24 Comma cutover integration and source repair

The receiving source matched `8b06f497` over the affected paths. The isolated
runtime and quality candidate `73001f83` aligned the packaged and runtime
v4 filename and preserved the distinct native export name. Its wheel fixture
checks the real package manifest with temporary, untrusted bytes. Global
admission still requires the symbolic v4 codec, checked liveness and writer,
and the exact native export.

The Comma diagnostic bind and shift walkers and the explicit Mahler Pow5
trace now use iterative traversal. The tests check ordered mappings at all
924 phases, the true fallback, and preservation of an issued trace when a
later tile fails. The direct Mahler cylinder and band regressions passed.
The CRT replay support moved to its own file and compiled in the 148-second
native B1 build. The native dependency smoke rejected a hidden retired rank
theorem through a wrapper. The repository-policy scan reported zero findings.
The integrated selection passed 194 tests, and the receiving Mahler,
Antihydra, and audit selection passed 1,054. The full guarded default suite
finished in 220 seconds with 13,826 passes and six Comma admission failures.
The clean baseline had ten failures. The three Antihydra failures and the
dependency-audit test failure were resolved. Canonical P0 retained the same
13 failure IDs as the preceding candidate. Strict mypy, changed-file
Pyright, Ruff, formatting, and documentation checks passed.

On isolated revision `4b53bdc6`, the decade-summary producer uses the
source-bound symbolic Stop. Native B1, C1, and Future sessions passed in
161, 83, and 30 seconds. The source provider excludes packed Stop and rank
authority, and the first-sector bridge checks the ordered physical crossing.

The revised Future session passed in 31 seconds at `14a10b9f`. The
rank-free graph checked 4,402 finite and 314 live classes in 18 seconds.
That graph proof covers the ordered candidate table. At `76fcad10`, the
first-sector writer passed in eight seconds. It checks the source-bound
duration, exact selected cut, and ordered Fork, Landmine, or Continue result
for one Entry/Near sector. The existing Entry-open publisher still uses
the removed packed summary equation. Release needs an authenticated physical
correspondence for all sixteen roots, the weighted cycle writer, and a checked
v4 export and decoder. The symbolic proof candidate remains isolated. Public
`a367620 --nth 1` returns status 3 because global admission is empty.

Evidence is in `results/nc43-symbolic-integration` and
`results/comma-nc43-production-proof-integration`.

### November 25 reversal integration

The clean receiving baseline was `7f2d3db5`. At `3fcd9478`, the guarded
default suite finished in 227 seconds with 13,978 passes and the same six
Comma admission failures. P0 retained thirteen baseline failure IDs. The
459-test affected selection passed, including 20,000 local H-cell cases
across ×2 and ×5. The two long Q19 regression tests now check the issued
broadword route, projection reuse, and the original poisoned routes. The
short punctured test still admits and counts its T2 action.

The shared decimal SLP compiler stores one reset word per node and
publishes inlet variants at the root. Its action checks exact immutable
source and result nodes across unrelated suffix rollback. Signed mod-32
cuts use the existing cyclotomic owner. At `056396af`, the boundary fast
path uses a canonical one-hot phase only for an unfactored power-one
cyclotomic quotient. Arbitrary factors and jets retain exact boundary
projection. The updated cut and carry selection passed 435 tests.
Reverse/add batches the admitted carry-free prefix cases and handles zero
without constructing a carry slab. Its supplied-row fold validates the
schedule before discarding extinct coefficient work. The live H12
endpoint still advances nonlinear carries without constructing a carry
trace.

Five interleaved target trials matched exact output and measured SLP
compilation at 8.24 to 4.04 ms, the order-257 signed cut at 14.33 to 8.72 ms,
and 400 zero Q19 images at 3.38 to 0.09 ms. Six ordinary cold CLI controls
stayed within 0.4% of baseline after equalizing prepared bytecode caches.
The initial full-component cut and unequal-cache CLI timings remain in
the evidence and are excluded from the accepted comparisons.

For the gated 153-digit `2rev10` fixture at 4,096 ticks, the cold CLI
medians were 1,062 and 315 ms. For seed 196 at 16,384 ticks, the consolidated
`5rev10` bitplane candidate measured 190 to 171 ms cold and 41.82 to
22.71 ms for materialization with both owner and process caches bypassed.
Cold 4,096-tick bitplane medians were flat. Warm queries reused the same
owner. The long fixtures used extended explicit bounds and identical
outputs. Automatic selection remains gated.

The optional C++20 wheels provide bounded diagonal and causal kernels.
The scalable word-RAM model uses `O(nN/b²)` interior lookups for reflected
squares with side `b = Θ(log N)`, plus table setup, source, and fringe work.
The two-pass reverse/add model retains a `log log N` factor in its
interior time. The wheels use fixed shapes.

The signed finite-cut and quiet-suffix theorems passed Isabelle. Checked
bitplane lemmas cover the local carry truth table, ordered decimal word,
and the clock under explicit transport laws. The packed shift and
normalization connection, the complete physical periodic halo, and the
C++ source-to-endpoint refinements remain open. The short-ring proof hit
the unchanged 300-second gate, and its finite-table successor hit
theory errors. The proof drafts are retained at `aa8d6828`; the active
sessions exclude those drafts.

The curated source at `78ae566b` passed strict mypy, both changed-file
Pyright batches, Ruff, source policy, documentation, Homebrew clang-format
and clang-tidy, and the guarded registered Isabelle build. The Colima
Linux aarch64 default suite finished in 256 seconds with 13,981 passes and
the same six Comma admission failures. Pure-Python and native builds on
macOS and Colima returned matching installed CLI smoke outputs for all
three reversal families. Each platform passed four guarded native-wheel
tests.

Evidence is in `results/nc43-reversal-7f2d3db5`.

### November 25 diagonal and EQ follow-up

The receiving snapshot was `97e7fec3`. Runtime validation used `82fd54ae`,
and the wheel-verifier follow-up used `4d62df88`. The live Mahler cylinder
retains the rejected lower-prefix product and projects only the adjacent
authenticated segment. The 64-tick policy still selects the source route.
At 4,096 ticks, the exact 540-coefficient result required 54 projected
coefficients in the final descent, down from 198. Five matched trials
and a confirmation measured a 5.5% median descent improvement. The
512- and 2,048-tick cases improved by 21% and 33%, while the 1,024-tick
case improved by 4.6%. Fresh installed CLI packets matched at every tested
horizon, with the largest median control increase at 0.41%.

The optional extension shares the checked pair digit and carry response
across both native executors. The guard compiles only the atoms reachable
from the selected root and transfers each completed child directly to its
ordered parent slot. On the 16- and 17-return fixtures, node counts fell
from 1,404 and 1,682 to 1,275 and 1,548. Both guard medians increased by
less than 4%. The seed-196 causal kernel improved by 7.3% at 1,024 ticks.
Guarded Clang formatting, warnings and tidy passed. The Colima GCC check
passed with eight unavailable Clang diagnostics reported explicitly.

Isabelle accepted the Mahler prefix composition and the source-bound
reverse/add half-kick, quiet EQ and reset bridge. Both reflected family
sessions completed. The affected selection passed 1,487 tests. The full
default suite passed 13,985 tests in 225 seconds and retained the same
six Comma failure IDs as the frozen baseline. P0 retained the same
13 failures and 77 passes. Strict mypy, changed-file Pyright, Ruff,
source policy and documentation checks passed. The aggregate proof-index
failure matched the baseline exactly.

The wheel verifier now treats C++ sources as build inputs and requires
the specific extension ABI for an opt-in wheel. The packaging selection
passed 24 tests. Fresh macOS and Colima pure and native wheels returned
matching family smoke packets. Both standard package variants passed
content validation before the existing Comma artifact gate.

The reciprocal cylinder remains held on its width and ordered-repeat
refinement and speed gate. The compressed guard prototype matched the
two 28,014-digit source fixtures, with 107 grammar nodes and 314 export
work units. The source-to-mask induction, general collar transport,
folded Q19 hinge and joint slab proofs remain open, along with automatic
selection of the staged reflected routes.

Evidence is in `results/nc43-diagonal-eq-20261125`.

### Follow-up source and native proof gates

The receiving snapshot used `7f2d3db5` with the existing unstaged changes.
`Reverse_Residuals` checked folded endpoint reconstruction, center parity,
physical width, and the local slab carry-clock law in 109 seconds. The
checked theory files are on local main. The compiled hinge and the source
coverage for the four-tick slab still govern native publication.
The isolated native drivers matched 1,280 folded endpoints and 160
admitted slab endpoints. Five receiving-owner tests passed after fixing
the folded eligibility check for the Boolean cache policy.

`Reverse_Growth_Admission` checked ordered EQ grammar composition, the
physical quiet-cell mask, reset clipping, and the first birth cell in
47 seconds. This theory is on local main. The isolated issuer's 28,014-digit
case agrees on the `1010` growth word. Its full native return-mask coverage
and structural work gate remain open.

`Five_Reverse` checked the concrete bitwise lane and first-sheet source
equations in 196 seconds. The checked theories are on local main. Automatic
selection still depends on the complete two-sheet and publisher refinement.
`Double_Reverse_Temporal_Refinement` hit the 300-second limit before
reaching the changed H2 theorem.

`Mahler_Source_Transport` checked exact width, ordered repetition with
the remainder, and the clipped earliest prefix in 68 seconds. The live
CF cylinder on local main selects source-bound reciprocal blocks for
positive horizons below 64 ticks when capacity permits. It keeps the
existing route from 64 ticks and the exact pointed fallback for tight
budgets. The final trial passed 86 focused checks, including cancellation
and cleanup. Five interleaved comparisons reduced fresh-owner producer
medians by 70.8% at 20 ticks and 69.8% at 63. Installed wheels emitted
identical packets across all eight horizons, with a largest cold median
increase of 0.56%. The 4,096-tick control still returned 540 coefficients.
It exercised no dyadic period or matrix power. The guarded default suite
passed 14,012 tests and P0 passed 77. The six default and thirteen P0
failure IDs matched the receiving baseline.

Evidence is in `results/nc43-proof-gates-20261125`.

### Native reversal proof follow-up

The receiving snapshot used `7f2d3db5` with the unstaged reversal work.
`Reverse_Residuals` checked that each admitted 8/17/18 reset makes the
following carry independent of the remote physical prefix. The 256-source
literal clock selection passed. The isolated native Q19 owner also
published the exact four-tick slab continuation from a 1,400-digit all-nine
source with chronological continuation disabled. Five interleaved owner
comparisons measured 20.143 ms for the exact route and 20.028 ms for the
native trial, including construction, publication, and cleanup. This
missed the 5% gate. The uniform four-tick Isabelle proof still has open
carry-fold and pair reconstruction goals.

`Reverse_Growth_Admission` checked quiet and growth EQ observations at
the physical clock in 19.5 seconds after its prerequisites. The theorem
preserves both outer sums after the two-tick return from outer sum 17.
The native guard still needs physical-response inclusion in its terminal
mask and separate accounting for live capacity and traversal work.
Six focused source tests passed. A bounded search of 3,000 sources found
no case where the native fallback resolved an ambiguous receiving frontier.

A guarded endpoint-only Isabelle build checked the exact odd reflected
value for both multipliers and each even value with its own inlet. It
used the receiving endpoint theory and its imports. Full registered
validation and the bridge to the live Python SLP writer and its
intermediate budget checks remain release requirements. Registered
`Five_Reverse` accepted the whole-word first and second sheets, their
terminal carries, and the normalization cut derived from nonzero plane
support in 114 seconds. The new theory replaces the separately checked
second-sheet proof. The live odd-width readout and budget publication
remain open.

`Shared_Carry_Dynamics` accepted the reflected diagonal table theory in
50 seconds. It checks one-cell digit and port transport, parity
transposition, complementation, the quinary inverse, mixed-radix rank
splits, ordered quarter assembly, zero tiles, and numerical trailing-zero
restoration. The guarded table proof is on local main. Mapping the
compiled wavefront and physical fringe to these equations remains the
native endpoint gate.

The bounded word-RAM trial checked 300 exact endpoints across both
multipliers, tile sides 3–7, and two kernel variants. On the 153-digit
`2rev10` source at 4,096 ticks, side four reduced the median kernel
time from 0.743 to 0.441 ms including table construction. On `5rev10`
seed 196 at 16,384 ticks, side five reduced it from 3.088 to 2.480 ms.
The phase-hoisting trial regressed on the `2rev10` controls. The
measurements cover the C++ kernel and leave CLI dispatch unchanged.

### November 26 downloaded quotient ports

On the unstaged receiving tree at `7f2d3db5`, the ordered CF band compiler
now searches the full half-band for ordinary returns from 128 rows. A
packed binary comparison proposes the lag. The complete lifted congruence
checks the odd coordinate before the compiler powers the ordered body and
appends the remainder. The CLI keeps its existing source and size bounds.

A 148-row physical fixture with period 37 compiled in 16.02 µs median,
down from 24.70 µs over five paired trials. With cache bypass the same
comparison was 14.98 versus 41.01 µs. The large exponent in this fixture
is admitted by the arithmetic API. All six in-range installed CLI band
controls emitted identical packets. Their largest cold median increase was
4.0% across shared and bypass modes. The focused band selection passed
45 tests. Strict mypy, Pyright, Ruff and formatting passed on the four
shared arithmetic and suffix implementation/test files.

The settled one- through four-column CF suffix actions and their Moore
separation theorem are on local main. Both phases reuse the same ordered
product for `25`. Selecting the three-column suffix across 1,024 sources
fell from 4,460 to 712 ns per call, including the scratch charge. The
registered `Mahler_Source_Transport` build checked the physical width
clock, clipped prefix and suffix products in 53.68 seconds under the guard.
The short reciprocal cylinder on local main now consumes these actions
before decoding the upper digits, including a cut on the tens digit.
Its cursor authenticates exponent, width and the next decimal threshold.
Across 91 public CLI queries all packets matched a literal row fold with
settled suffix decoding disabled. The focused run passed 35 tests.
At horizons 20 and 63 the producer fell from 46.38 to 43.79 µs and from
78.96 to 72.71 µs respectively. On four cold CLI controls across the
64-tick selector boundary the largest increase was 3.1%.

The registered `Shared_Carry_Dynamics` build checked the protected
two-tick interval by induction and its odd ordered gate in 56.02 seconds
under the guard (2.38 GB sampled peak). The checked theory is on local
main. A second registered build (55.79 seconds) connected this interval
to the repeated H digit function at the same coordinates. A separate
55.52-second build checked exact ordered rectangle transposition for
both multipliers, including empty and one-column boundaries.

The registered `Reverse_Growth_Admission` session checked the four-state
ordered inverse-EQ walk, its physical mirrored carries, and the exact
two-tick endpoint. Its proof is on local main. The isolated H12 publisher
saved two physical calls on the admitted 512-digit fixture, but five cold
trials including source construction and rendering rose from 12.05 to
12.48 ms median. Seed 196 had no qualifying 64-cell slab core through
2,048 frames. The exact receiving publisher remains active.

The isolated native reversal wheel passed the authored LLVM checks. The
153-digit `2rev10` case at 4,096 ticks took 208.38 ms cold versus
967.53 ms on the receiving wheel. For `5rev10`, seed 196 at 16,384 ticks
took 135.04 versus 170.86 ms. Seed 73 at 1,024 ticks was essentially flat
for both multipliers. An exhaustive native comparison checked 444,440 ordered
table outputs across both phases, multipliers and tile sides one to five.
Pure and native Linux ARM64 wheels returned identical installed CLI output
for seed 73 at 1,024 ticks. The native wheel also passed eight independent
literal endpoint checks.
Automatic native dispatch still depends on physical readout and fringe
stitching. The registered shared proof checked prefix and suffix crop
coordinates with zero extension and the alternating two-gate clock in
56.53 seconds. The isolated native entry matched
literal period-13 endpoints for both multipliers at 64 and 65 ticks.

The isolated reciprocal cylinder with adaptive lookahead reached the exact
540 coefficients at 4,096 ticks. Five interleaved installed-wheel trials
reduced producer time from 372.42 to 333.05 µs with the shared cache and
from 368.75 to 335.79 µs with bypass. Whole cold CLI time was 134.63
versus 138.11 ms with sharing. The receiving cylinder keeps its spatial
selector from 64 ticks. The isolated spatial variant passed 32 checks including unforced CLI
packets at 64, 65 and 128 ticks. At 4,096 ticks its producer took
432.67 µs versus 349.50 µs. A second implementation emitted only the
upper lanes and supplied the two fixed digits as the stencil halo. It
passed 35 guarded tests, including spans one through four and complete
default CLI packets. Its 4,096-tick producer took 446.08 versus 353.46 µs
with sharing and 441.50 versus 350.54 µs with bypass. The five-trial cold
CLI medians with sharing were 126.41 versus 126.59 ms. Both spatial
replacements remain isolated. The registered Mahler proof (64.47 s) now derives
the physical upper recurrence `u → 5u + 1` at every admitted tick from
`x = 100u + 25`. The spatial leaf's packed output still requires its
source-to-projection refinement.

The staged protected period-13 grammar matched all 164 literal two-step
frames across the four border phases with chronological stepping disabled.
A mutated digit inside each causal halo refused admission. The registered
double-reverse session checked the finite-cone induction in 126.82 s.
Given the complete one-step stencil miter and source halo, it proves the
shifted digit after every admitted two-step update. The staged modulo-25
Hasse filter has a collision on `(0,9,3)` and its successor `(1,7,4)`;
the exact ordered miter rejects that rotation. The local Q19
pair-four regression exercises both physical carry inlets and the next
row's bilinear carry. A 57.47-second `Reverse_Residuals` build checked
the physical one-step cell, including EQ propagation, and the conditional
four-tick interior formulas for schedules `1011` and `1110`. The separate
source-clock build (131.86 s including prerequisites) checked the physical
`1110` branch and the first three bits of `1011`. The November 27 registered growth build (130.38 s)
checked the index-one source transport and forced the fourth carry for
the same admitted source with a quiet second tick. This completes its
physical `1011` clock and excludes `1010`. A further 29.52-second build
checked that every admitted `18 # c # rest` source selects one of the two
schedules. A complete
source-to-collar and folded-center proof still gates the live slab issuer.
Installed reverse/add returned eight exact physical
endpoints over the four inlet pairs. The staged protected grammar passed
42 tests. Its five-trial cold medians at 82 and 162 physical ticks improved
by 1.4% against the same grammar with bounded literal discovery. The
period-13 dispatcher remains isolated.

The November 27 source-DAG candidate intersects three exact digit-equality
bits and checks at most two crossing triples per join, with cyclic wrap at
the root. Both multipliers passed all 2,000 local cases together and the
four period-26 controls. The four compressed controls of length
`9 × 10^100 + 9` passed without motif expansion. The exact digit checks
reject the false right shifts of `02925` and `00792`. Only the isolated
`2rev10` protected bank consumes this admission. Five interleaved
installed-wheel trials returned identical complete grammar packets across
four border phases. At 82 and 162 physical ticks, median cold CLI times
were 154.44 → 158.24 ms and 154.88 → 158.16 ms. At 82 ticks repeated
same-owner issuance took 459.83 → 520.52 µs; first issuance in fresh
processes took 622.42 → 3,769.08 µs. The candidate misses the target-phase
speed gate. The final registered Python selection passed 56 tests. The
registered double-reverse build (130.94 s) kernel-checked concatenation
and the repeated-word seam for ordered triple predicates, including the
two-tick digit specialization. The constant-work repeat implementation,
root wrap and physical `5rev10` fringe and publisher still need their
consumer refinements.

The next registered `Reverse_Growth_Admission` build (147.09 s)
checked the first physical birth at a specified split of the same valid
source. Its global carry and two adjacent reset coefficients determine the
new cell at that split. The theorem includes wrong-inlet and EQ-9 cases;
two swapped inlets can give the same sum. Transport across the remaining
three rows still gates four-tick Q19 endpoint publication.

On the unstaged `7f2d3db5` receiver, the reverse/add source-transfer
matrix now requests the conditioned carry at a Q19 growth interior
before expanding the next cell. The registered `Reverse_Residuals`
session checked the decimal selection rule and the radix-dependent
cubic laws in 60.19 s. Fresh Linux wheels under Colima returned the
same complete packets for seeds 196, 190999 and 9999. Each called
the new guard; foreign ownership and forged width were rejected.
On the matched reuse fixture, source lookups fell from four to one
and median guard time from 172.67 to 26.74 µs. Across five interleaved
macOS trials, cold installed CLI medians for the two growth requests
went from 283.56 to 283.38 ms and 284.92 to 283.25 ms. The ordinary
control went from 247.41 to 251.27 ms. This change covers a single
next-carry observation. The multi-tick EQ mask and whole folded
endpoint still require successor and width transport.

The live `2rev10` F-port leaf now selects among ten distinct response
rows and three right-inlet classes. The receiving
`Double_Reverse_Temporal_Refinement` session checked the equivalence
for adjacent outputs in 127.86 s. Across five matched trials the
leaf median fell from 162.04 to 108.65 ns. Seed 73 at 1,024 ticks
used the leaf 1,348 times and produced the same packet; its cold CLI
median went from 187.02 to 188.07 ms. This measurement covers the
local table change. Dense endpoint dispatch still uses its existing route.
The shared session also checked disjoint 16-bit lane packing, transpose
and reflected half-table indexing in 61.75 s. The lookup theorem still
requires the rectangle complement law for the supplied table. The
registered wave source, interior and fringe equations passed with that
table in 58.98 s. Runtime frontier and endpoint dispatch remain separate
proof obligations.

An isolated CF handoff retired the spatial workspace on commit and
produced all 540 coefficients at horizon 4,096 within the 10,000-node
fixture. It reduced the shared producer median from 351.46 to 316.50 µs
there but increased it from 91.00 to 99.38 µs at horizon 64. It also
still folded the changing upper digits. The candidate remains isolated.

The isolated four-tick Q19 proof derives the fourth cell from a physical
reset collar, the actual birth clock and both inlets. The guarded
`Reverse_Growth_Admission` run finished in 156.07 s. Separately, a native
interval prototype matched folded endpoints and birth counts every four
ticks for seeds 196, 190999, 98 and 108900989. For seed 196 from tick
1,024 to 2,048, five paired kernel trials gave medians of 5.71 ms for
packed advancement and 1.73 ms for the prototype, including conversion.
On the isolated installed wheels, cold CLI medians were 268.56 to
279.38 ms at tick 1,024 and 281.15 to 276.66 ms at tick 2,048. All
packets matched. The ordinary 20-tick control went from 254.98 to
256.79 ms. An installed, same-process request for 2,048 after 1,024
fell from 24.27 to 19.46 ms. Disabling process cache retrieval and
publication gave 192.47 and 191.13 ms. Whole-endpoint authority and
native dispatch remain open.

The November 27 Hasse/Hermite patch targets the downloaded quotient-first
source. On the receiving CF cylinder, 315 requests at horizons 1–63 made
201 reciprocal interval reads, all at row zero. Skipping multiplication by
the initial power of five reduced median interval time from 120.56 to
108.64 ns. Fresh wheels produced identical packets at 20, 63, 64 and
4,096 ticks. At 20 and 63 ticks their cold CLI medians were 121.39 to
123.13 ms and 122.48 to 124.33 ms. The two longer requests took the
spatial route. The initial-row specialization is live on the unstaged
receiver. Its `Mahler_Source_Transport` build passed in 104.29 s, and
fresh Colima installs matched all four packets. The focused receiving
selection passed 21 tests. The bounded exponent trial passed 33 tests.
Its high-bit Hasse branch exceeds the public exponent limit.

The registered Mahler session passed in 97.73 s and checked a sufficient
physical half-shift condition for every fixed width from three upward.
It established the exact guards at widths three and four, the two singleton restrictions and complete
$25$ product with the live digit-plus-one convention. These theorems
are on the unstaged receiver. A 38-test receiving selection passed,
including the modulus-125 raw-digit counterexample, both clipped
stops, and reference public packets.

An isolated spatial range action for the settled suffix uses the same
matrix for $25$ in $125$ and $625$ and restricts it to either singleton
at a cut. The interval tests stop after $12$ and $125$ for targets $2/5$
and $10/23$ in the cylinder's reciprocal coordinates. All eight matched
fresh-wheel packets agreed. At 4,096 ticks generic continuant input fell
from 618 digits to 540, while continuant calls rose from 17 to 44.
Both paths still issued 39 packed rows of total width 564. Median
shared-cache cylinder time was 14.01 to 13.87 ms, and bypass time was
13.82 to 14.18 ms. This candidate remains outside default dispatch.

The November 27 four-column spatial patch was tested separately against
the receiving phase table. Sixty guarded tests passed. Five fresh-wheel
pairs at each of eight horizons returned identical complete packets.
At 64, 512 and 4,096 ticks, shared-cache cylinder construction rose from
6.87 to 7.79 ms, 6.90 to 8.01 ms and 14.00 to 15.62 ms, respectively.
The four-column dispatcher remains isolated.

The receiving table now derives the three leading-digit half-turns by
adding five times the lower matrix row to the upper row. It preserves
the shared $25$ product. Median table initialization and first selection,
with dependencies loaded, fell from 12.56 to 9.70 microseconds over five
paired batches. All eight installed CLI controls returned identical
packets, with cold medians between 2.3% faster and 1.7% slower.

Two bounded one-column CF actions were tested on the unstaged
`7f2d3db5` receiver. The eight-row terminal uses a 10 KiB fixed
alphabet and reserves 24 KiB for simultaneous construction and output.
All 57,600 lift and clip combinations agreed with literal digit products.
The registered `Mahler_Source_Transport` build on the receiving tree
passed in 95.52 s including prerequisites, with a 3.38 GiB peak. It
checked the arbitrary-lift clip theorem, five-inlet source transfer and
ordered square.
The audit found zero oracle or skipped-proof dependencies.
The installed CLI invoked the terminal for lifts 370 and 1099. Across five
interleaved pairs, their warmed owner medians fell from 31.79 to 30.17 µs
and 46.75 to 45.04 µs. Cold CLI medians rose from 116.55 to 118.37 ms
and 115.05 to 116.73 ms. Both ledgers released their reservations.

The five-inlet parity action admitted `15,4,1,14` with lift 43338 and
parity period five. Its decimal letters have no admitted repeat. Building
the five inlet responses with probe and action storage charged raised
median owner time from 12.16 to 22.33 µs and peak ledger nodes from 168
to 944. Cold CLI time rose from 119.98 to 121.24 ms over seven matched
pairs. Both returned the existing packets. The eight-row terminal landed on
main in `36d3226c`. The five-inlet candidate remains outside dispatch.

The reflected donor adds a scalar miter table. An isolated port retained
the existing NEON loop and used the table for the scalar fallback and
tail. All 2,000 local masks and 24 physical endpoints matched. Five
paired installed CLI trials on the 8,584-digit source gave medians of
357.91 and 356.87 ms. The table remains isolated. At generation 82 the
source-issued CRT bank cut counting from 0.319 to 0.157 ms, while its
complete bank request rose from 7.620 to 8.076 ms. The isolated bank
passed 44 guarded tests, including partial CRT wraps and long returns.
The registered Five_Reverse build passed on the receiving fringe theories
in 205.24 s including prerequisites. The new readout theorem recovers
the physical orbit for either parity from the checked diagonal inlet
and cell equations. Native dispatch still requires the C++ wavefront
to satisfy those premises.

The receiving `Reverse_Growth_Admission` build checked four physical
updates for a selected interior coefficient. From an admitted outer-18
source and its eight-position collar, the theorem derives the coefficient
and a width increase of three under the source's 1011 or 1110 carry clock.
The guarded build took 161.75 s including prerequisites (2.40 GiB peak).
Whole-slab publication still requires coverage of the hinge and fringes.

The reverse/add weighted bulk port required the predecessor's Laurent
publisher and conditional guard translation unit. It passed 320 literal
projection cases and 140 bulk cases. Six paired installed CLI trials
on 10,000 nines reduced median time from 147.0 to 112.6 ms with the
interpreter's decimal conversion limit disabled. At the 512-tick native
threshold, bulk admission needs at least 8,224 source digits. The default
CLI rejects this input. Seed 196 at 1,025 ticks admitted zero relative
actions and rose from 122.6 to 129.9 ms. An isolated earlier admission
reached the contraction under default parser limits. Matched installed
CLI medians were 117.56 to 117.08 ms at 128 ticks. Moving the width
check ahead of the native import gave 124.70 to 118.54 ms at 240 ticks
on 4,000 nines. Both requests returned the same matrix as the receiving
route. At 240 ticks the source owner took 13.64 to 8.23 ms and one
contraction removed 1,512 pairs. The seed-196 owner control took
9.07 to 9.56 ms. The weighted source-to-output proof remains open.
The trial excluded the slower weighted inverse-EQ terminal.

After the reciprocal-port change, 14,027 default tests passed in 243.55 s
and 77 P0 tests passed. The six default failures and thirteen P0 failures
matched the preceding snapshot by test ID. All six default failures
exercise global Comma admission.

## Cross-family ownership review

The consolidation from `62cbc714760a6f074f5a955f0efeac6afa1e5e27`
is in local main's unstaged working tree. It replaces duplicated
digit-band construction, one reversal forwarding
function, one Isabelle reversal body, and duplicate retained-cost
arithmetic. Its production and theory diff adds 83 lines and deletes
76, including the new proof boundary examples. The regressions add
50 test lines. The changes preserve the existing certificate issuers.

| Area | Canonical owner, migrated consumers, and retained distinctions |
| --- | --- |
| Carry logic and ports | `carry_monoid.CarryFn`, `apply_carry_fn`, and `compose_carry_fn` already serve reverse Q19, reflected temporal ports, and downstream carry consumers. Isabelle's `Shared_Carry_Domain` and `Shared_Carry_Tape` supply the shared Boolean laws. The Q19 left/right port bindings, Collatz transition kernel, ordered tripling, and signed wide borrow have different transition and admission rules. |
| Band construction and transport | `ordered_band.ordered_digit_band_frame` now serves `source_issued_ordered_digit_band` in reverse/add and 2rev10. Their source readers keep separate Q19 and SLP authority. The helper explicitly starts its index at the least-significant digit and emits padded MSD-first frames. `five_reverse.term._ordered_output_reserved` retains its single LSD-first channel and different clock. `Ordered_Matrix_Program_Algebra` already shares the chronological composition laws. |
| Pascal permutations | `PascalWordMoments` and Isabelle's `Pascal_Word_Moments.fpm_reflect` describe reflected finite carry words and their moments. Prime's exact reference and bounded mod-\(2^n\) binomial row transports use different coefficient arithmetic. Q19's binary parity lanes have a different observation contract. The audit found no equivalent production bodies to replace across these uses. |
| Digit reversal | The 2rev10 Laurent producer now calls `arithmetic.fields.radix.reverse_radix_integer` directly. The 5rev10 Isabelle border consumer uses `Shared_Decimal_Reversal.decimal_reverse_block3` after its three-digit admission, with the same four source-bound outcomes. The variable-width padded reversal and physical zero trimming retain their separate laws. |
| SLP packing | `slp_walks.iter_symbols`, `slp_interval.fold_slp_dag`, and `decimal_slp_action.multiply_decimal_slp` already supply shared traversal and emission. The reflected nibble windows, 5rev10 physical BCD state, and Q19 pair sums have different halo, order, and trim contracts. `payload_cost.aggregate_integer_limb_units` now owns the identical aggregate charge used by `ResidueCarrySLPProjector` and `SymbolicInnovationArena`. Independent payload audits retain their own calculation. |

Five interleaved trials kept the same guarded source, emitted packets,
and source-letter counts. The median for eight 2rev10 band constructions
was 94.45 to 93.72 ms and the reverse/add median was 308.69 to 309.37 ms.
These differences are within trial variability. The retained-cost
comparison matched the full carry output and counters at 30 derived
nodes for an 84-symbol source and the innovation ledger at 24 entries
and 14 nodes. The guarded selection passed 264 tests. Ruff and format,
strict mypy, and the ten-file strict Pyright batch passed. See
`results/nc-cross-family-debt-units`,
`results/nc-cross-family-debt-bands.log`, and
`results/nc-cross-family-debt-packing.log`.

The registered `Five_Reverse` session completed in 113 seconds on
the cross-family revision. It checked the migrated window consumer,
its four-stage source outcomes, and the new padding and admission
examples. See `results/nc-cross-family-debt-native`.
