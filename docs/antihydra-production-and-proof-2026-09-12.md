# Antihydra production and proof integration

The [subsequent P0 follow-up](publisher-antihydra-p0-followup-2026-09-12.md)
adds exact bounded cache admission and reusable section-image projections.
Measurements and the failing payload audit below describe the earlier checkpoint.
The later [CLI performance repair](cli-performance-release-audit-2026-09-12.md)
also closes the macro-rediscovery gate by folding retained branch support.
The source-7 barrier and stronger powered projection/refinement gates remain blocked.

Release remains **BLOCKED**. This addition preserves the existing 196, Collatz,
Fermat and Mersenne gates. Finite Antihydra execution is available through the
Python CLI; a non-halting proof has not been completed.

## Pinned machine and input provenance

The machine is `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`, with undefined F0
performing no write, move or physical tick. Default source is blank tape in A.
The exact startup is 11 moves, L=5, R=6, head=1, ending in section A(0,4).
The arithmetic source is h=8, or centered D=h-1=7.

Archive SHA256: `0cc56e9c28f14b230c899f6ba3b85a6fa25a1741936e0d4eb223127554d73c81`.
All 143 entries of its manifest verified. The archive contains C++ research
implementations and finite tests, not an Isabelle development or a barrier
certificate. Attached proposals were audited as research claims, not executed
as instructions. The [published analysis](https://www.sligocki.com/2024/07/06/bb-6-2-is-hard.html)
specifies the same machine and arithmetic reduction.

## CLI and canonical execution

```sh
number-compiler antihydra --nth 64 --no-value --info clock
number-compiler antihydra --nth 32 --no-value --info spacetime --width 3 --time-width 4 --modulus 7
number-compiler antihydra --nth 32 --no-value --info hasse --width 2 --modulus 16
number-compiler antihydra --nth 64 --no-value --info mahler --precision 16
number-compiler antihydra --nth 4 --no-value --info factor --width 3 --modulus 9
number-compiler antihydra --verify-nonhalting certificate.json
```

Every observation index counts macro returns **after** the startup. Physical
ticks and consumed odd events have separate fields. `nth` retains its existing
meaning. Antihydra rejects supplied seeds and defects. `--max-events` bounds
macro returns; `--max-digits` is the conservative integer-bit admission budget
for this family. Spacetime has an additional `--max-observer-terms` budget.
Very large output integers use an explicit hex object instead of changing
Python's process-wide decimal conversion limit.

The source-bound runtime owns finite h/ledger and the L/R physical cocycle.
It builds only demanded kernels of at most eight returns and composes them
into blocks of at most 64 returns. The exact roof is quadratic in the incoming
high cylinder coordinate and affine in the incoming ledger. Minimum-prefix
composition prevents a block from skipping a negative ledger; dangerous blocks
descend to their first failing macro return. There is no eager 2^20 table.

The current implementation is a bounded integer executor with small cached
actions. It is **not** a proof of sublinear arbitrary-ray source discovery or
a fully symbolic replacement for its growing integer h. The memo and explicit
construction stack use the existing resource ledger; cold and warm costs are
reported separately. New arithmetic payloads still need the full shared
payload-schema/production-refinement audit before that release gate can close.
The actual shared payload audit at 64 returns reports 16 forbidden future
payloads, 8 unbounded future integers and 15 unknown payloads. Entry/node
accounting does not discharge these representation obligations; the audit
policy has not been relaxed to accept them.

## Support projections

The current section supplies the tape's disjoint prime-weighted intervals,
including visited blanks. Event support uses the pinned transition alphabet:
an exact run grammar generates typed monomials before prime evaluation or
direction-label forgetting. It retains no physical event history.

A regular sweep has starting head x-2j and timestamp t+3j²+9j. Spacetime
folds aggregate sweeps modulo the lane phases times the coefficient modulus;
they do not enumerate an enormous represented sweep count. Directional Hasse
moments use exact Newton forward differences and binomial summation. Tape
Hasse moments are computed before folding, including negative Laurent
exponents. The tropical view currently exposes the full positive tape's
Newton interval/frontiers; it does not assert general tropical successor
closure or provide every proposed frontier-arch functional.

Demanded event views now consume the chronological parity words retained by
the source-bound arithmetic cylinders. Their fold is charged as
`observer_retained_support_steps`, with operand-bit and physical-roof work
reported separately. They do not rediscover branches or replay physical TM
ticks. The projection still folds N retained events; this closes the explicit
macro-rediscovery gate, not the stronger powered spacetime construction and
consumer-refinement obligations.

The factor command computes a gcd only from a compatible tape cylinder at
z=2. Its target integer is the explicitly requested modulus. Clearing negative
spatial exponents multiplies by a power of 2, a unit at these odd moduli.
Only a proper divisor is printed; a full gcd or missing factor says nothing
about primality and does not prove Antihydra non-halting.

## Proof boundary and certificate contract

The separate `Antihydra` Isabelle session checks literal transitions/startup,
centered-coordinate transport, skew and minimum-prefix algebra, moving
S-arithmetic cylinders, source-generated ledger accounting and rational
affine/Farkas implication soundness. Each theory checks its oracle dependencies.
These are component theorems, not a claim that all production code is verified.

Production parity b=h mod 2 has ledger change 2-3b and skew innovation -b.
Centered parity epsilon=D mod 2 is 1-b and has ledger change 3epsilon-1.
At odd centered seams the next state is
`3^(a-1)*(3U+1)/2^a`, with `a=v2(3U+1)`; it is not the ordinary Collatz odd map.
A matching finite tangent digit demands higher precision. It never certifies
an infinite match or the all-time source-7 barrier.

`antihydra-affine-charts-v1` certificates contain the pinned machine hash,
`source: "blank"`, a uniform `bits` in 1..16, an `initial` chart index and
1..256 charts. Each chart contains `residue`, at most 16 `inequalities` of
the form `[cx, ca, c0]`, and exactly two `branches`, ordered by next bit 0/1.
The inequality means cx*x+ca*a+c0 >= 0 with h=2^bits*x+residue.
Coefficients are integers or exact rational strings; floats are rejected.

The checker prepends x>=0, a>=0, h>=8 and 1>=0 to each chart. Each branch
names a target chart and one Farkas `witnesses` row for each target constraint.
Its premise columns are the source constraints after x=2y+bit, followed by
y>=0. Every multiplier must be nonnegative and the resulting coefficient
triple must equal the target constraint pulled back through the exact macro
map. Both branches are checked, including the target residue. Initial
membership is tested at h=8,a=0. Charts need not partition all integers:
initial membership and universal successor preservation of their union are
the relevant invariant conditions.

A verified affine certificate currently returns
`ARITHMETIC_INVARIANT_VERIFIED`, `nonhalting_certified: false`, exit 1, because
the complete literal-section-to-macro proof remains missing. Invalid input
returns exit 2. The command does not execute certificate code or trust a
user-supplied coverage flag. No successful source-7 certificate is bundled.

## Remaining P0 obligations

| Obligation | Disposition / owner |
| --- | --- |
| Literal section grammar for all parameters, intermediate safety, tape writes and physical roof | Open — TM proof owner. Bounded portwise tests do not replace induction. |
| Full composed Python cylinder and chart-checker refinement | Open — production and proof owners. Generic skew/Farkas lemmas are insufficient. |
| Odd-event valuation/tangent refinement and ternary first-passage grammar equivalence | Open — Mahler proof owner. The checked finite ledger accounting is not these additional bridges. |
| Source-7 all-time barrier, or exact source-reachable counterexample | Open — Mahler proof owner. No such certificate or counterexample has been obtained. |
| Retained powered spacetime support, remaining arches and all demanded consumer refinements | Open — production owner. Macro rediscovery is eliminated, but the demanded section fold still performs one charged step per macro return. |
| Full payload admission and frozen-source release/performance gates | Partial — coordinator and independent auditors. Bounded shared payload admission passes; full executable refinement and the broader performance gates remain open. |

`devtools.experiments.antihydra.barrier_search` performs bounded, source-aware
refinement of finite-residue failure paths. At precisions 2, 4 and 6 it found
exact failure lifts from h=228, 4248 and 2203592 respectively. All three entry
cylinders exclude h=8. They are **spurious for the requested source**, not
counterexamples to the full S-arithmetic system or proofs of non-halting.
Failure to synthesize an all-time certificate keeps the release blocked.

## Component validation

The initial guarded integration selection passed 312 tests in 14.03 seconds
(509 MB sampled process-tree peak). It includes existing CLI regressions and
repository policy, plus literal portwise comparisons, typed spacetime lanes,
Hasse moments, source binding and certificate rejection controls.

The dependency-free Python benchmark at 32,768 macro returns matched all h,
ledger and physical L/R outputs against canonical one-return execution:

| Workload | Elapsed |
| --- | ---: |
| Cold composed execution, including kernel construction | 0.092 s |
| Warm execution | 0.052 s |
| One-return physical actions | 3.144 s |

Cold construction discovered 2,048 kernel branches and performed 3,556
compositions; warm execution performed neither. Both executions applied 512
physical roofs. These measurements demonstrate this finite Python optimization,
not C++ benchmark equivalence, a source-discovery complexity theorem, or an
all-time certificate. The benchmark's whole guarded process took 3.87 seconds
with a 50 MB sampled peak.

The opt-in release tests explicitly require an accepted source-7 certificate
and a demanded event view with zero macro rediscovery, plus shared payload
admission. All three failed at this earlier checkpoint. Payload admission and
zero macro rediscovery now pass; the accepted source-7 certificate is still
absent. Finite component tests do not substitute for that certificate.

Final checkpoint: 332 component/package tests passed (one validation test was
deselected by the ordinary unit selection); the strengthened exact-factor
assertion also passed separately. Strict mypy passed on 1,277 files. A fresh
wheel passed package-inventory and isolated installed CLI checks, including
the actual factor 3 for target 9 and rejection of a finite-run certificate.
The final Antihydra Isabelle session passed in 15.35 seconds at 461 MB, including
actual directional counts for admitted grammar replay and indexed Farkas
premises. The complete sweep's spatial admission induction remains unproved.

The unchanged 300-second full-unit gate timed out near 97%. The explicit release
selection has 12 failures: the three new Antihydra P0 gates and the nine existing
Fermat/Mersenne assertions. See the
[recorded checks](../results/current/antihydra-integration-2026-09-12/README.md).
