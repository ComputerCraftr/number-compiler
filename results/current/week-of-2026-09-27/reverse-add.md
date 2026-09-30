# Reverse/add

[Week of 2026-09-27](README.md) · [Documentation index](../../../docs/index.md)

## Records

- [Demanded reverse carry regions](#demanded-reverse-carry-regions)

## Provenance

Original records and caveats follow. Their evidence certifies only its recorded
source and scope. Records without a precise day retain their original weekly
context; listing order is not evidence of execution order.

## Demanded reverse carry regions

**Objective (September 27).** Test the proposed run-level regional boundary
against the live Q95 grammar without restoring universal boundary products,
higher-order continuation trees or a production midpoint evaluator.

**Finding and change.** `PlaneAlgebra.carry_prefix` eagerly constructed both
incoming-carry output trees at every spatial region even though its caller
requested entry zero. It now evaluates only demanded `(canonical region,
incoming carry)` responses. Right-region admission uses the left exit. A
constant-domain run constructs its first incoming bit and one repeated tail;
the existing three-state carry owner supplies the arithmetic. Requests, hits
and publications are counted separately, including memo lookup work. No
production executor, semantic `ActionID` or temporal admission was added.

**Checked mathematics.** `Reverse_Uniform_Runs` proves `region_carry_run_output`,
`region_carry_run_exit`, `region_carry_spatial_join` and
`region_carry_emission_refinement`. These preserve both ordered incoming cases
without a second physical carry direction. The existing `Reverse_Residuals`
session and oracle audit pass: 34.54 seconds / 987,597,656 bytes within
60 seconds / 4 GiB. The results concern spatial application to supplied domain
regions, not temporal composition of complete output/admission functions.

**Paired measurement.** Five trials per D4/D8/D16/D32/D64/D128 compared the
historical carry method from Git with the demanded method in the same
research constructor. Both outputs matched an independent decimal oracle.

| Power | Old/new carry run calls | Old/new carry concatenation calls | Old/new median milliseconds | Actual successors, both methods |
| --- | --- | --- | --- | --- |
| D4 | 29 / 16 | 18 / 9 | 3.52 / 3.46 | 4 |
| D8 | 68 / 38 | 48 / 24 | 8.61 / 8.01 | 8 |
| D16 | 161 / 96 | 132 / 70 | 20.19 / 19.43 | 16 |
| D32 | 420 / 249 | 358 / 190 | 61.77 / 57.65 | 32 |
| D64 | 1,131 / 664 | 1,214 / 640 | 221.00 / 213.92 | 64 |
| D128 | 3,609 / 2,128 | 4,108 / 2,182 | 877.63 / 867.94 | 128 |

The port-output allocation reduction is real, but it does not remove the
near-quadratic temporal trend. Work counters increased because the new driver
charges dependent stack stages and memo hits explicitly; they are not
presented as a speedup. The method remains a research reference rather than a
new production route. A failed gate here is not a counterexample to the full
cylinder proposal: its required non-midpoint normalizer is still unconstructed.

**Provenance.** Source fingerprint
`1f9705f53e4650eb8f86910fcde726b22dc6ec5772d38b62868a8ff3f7c474d9`.
Raw local evidence stays ignored under
`results/current/reverse-run-demand-2026-09-27/`: `paired.json` and its guard
(13.39 seconds / 22,495,760 bytes), `proof.log`, `focused.log` and
`validation.log`. The paired probe has 60 samples, not a production growth
acceptance result. Tests cover exhaustive five-cell domain words with both
entry bits, repeated regions under different entries, foreign handles,
non-bit rejection and a run of length `10^100` with expansion poisoned.
The broader focused selection has **58 PASS**. Strict mypy, Ruff, formatting,
repository policy, proof inventory and documentation checks pass. Full-unit,
installed-wheel and aggregate release gates were not rerun for this research-only
change; their preceding evidence retains its original fingerprint and scope.

**Research-input correction.** The newly downloaded
`collatz_compiler4_mahler_run_complexity_audit_fix_report.md` explicitly states
that maximal-run pumping has only `R <= N <= T` uniformly, and alternating
normalized words have `2k` runs in `3k` physical ticks. Its included theory
source was not built by that report's author. It cannot be cited as a proved
uniform temporal compression theorem for 196. Root/Vieta remains an optional
anonymous-fiber observer; no tropical search was added to admission.

**Remaining gate.** Construct `NF(A_B composed with A_A)` on complete regional
output/admission functions and apply it to the original source with midpoint
grammar construction and temporal child descent poisoned. The current
`FactoredTemporalPower` fails that architectural requirement by construction.
The CLI remains unchanged, with generic 196 temporal admission still blocked;
none of its positive release assertions were weakened.
