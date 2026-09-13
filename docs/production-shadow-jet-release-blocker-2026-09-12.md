# Production recurrence removal and shadow-jet release gate

**Release remains BLOCKED.** Pépin and Lucas–Lehmer no longer supply production
classification. This removes the prohibited fallback; it does not implement
the missing candidate-derived mod-16 shadow-cylinder recovery.

## Completed changes

The production `power_numbers/classical_ceiling.py` and `digit_power.py` modules
have been removed. Their bounded recurrence implementations live under
`devtools/proofs/oracles`, for research and differential tests only. Production
has no import of those oracles. Generic square, trace-square and cyclotomic
arithmetic remain: those operations have no primality seed/horizon/acceptance
contract and are needed by the arithmetic construction itself.

The CLI rejects `--allow-classical-ceiling` and `--max-classical-squarings`.
The Python compatibility keyword defaults to `False`; `True` raises before
cache lookup or even a structural small-case decision. Unavailable terminal
recovery returns UNKNOWN, with no target-depth certificate and
`scalable_construction=False`. Independently established small cases and
composite-exponent decisions are preserved.

An explicit `--factor` request may still run the existing, budgeted additive
étale coefficient probe. A checked proper divisor establishes compositeness
without a primality recurrence. A non-splitting result cannot establish
primality. M11 produces factor 23 with 21 quadratic products; M131 produces
263 with 261. This extra coefficient construction is metered and is **not**
the missing mod-16 recovery. An already available factor is reusable at zero
new-product budget. No-split results are also cached without replay.

## Unfinished proof and production construction

The production mod-16 key currently comes from a supplied arithmetic/root
state. The required release path must construct the relevant admitted shadow
action from the candidate, recover its jet, and prove that the recovered
Boolean section equals the all-local primality bit. The existing all-local
threshold equivalence does not construct that bit, and the supplied-root
zero-section theorem does not bind it to the candidate.

Full support injectivity is unnecessary for primality. The required Boolean
criterion, exact source binding, runtime refinement, and powered construction
cost are still missing. Available proper annihilators may print checked factors
without requiring universal factor recovery. None of these missing theorems
was replaced with a new assumption or an assertion of completion.

## Validation and release status

Two component selections pass: 84 tests in the classification/layout group,
and 135 in the compiler/quotient/cache/repository-policy group. These selections
overlap; their counts are not a distinct-test total. Strict mypy passes for
1,254 files; Ruff and `git diff --check` pass.

The new executable P0 gate is
[`test_shadow_jet_primality_release.py`](../tests/validation/proofs/test_shadow_jet_primality_release.py).
Its **four cases fail** on F4, F5, M11 and M13 because default candidate-derived
classification is still unresolved. It has no xfail or skip. Failure-handling
unit tests that correctly expect UNKNOWN do not satisfy this release gate.
This is necessary decision evidence, not a complete mod-16 refinement proof.

No Isabelle sources changed in this removal. Earlier component theorem builds
do not prove the missing recovery. The existing 196/Collatz and full-suite
performance blockers also remain open. Current evidence is recorded in
[`results/current/no-classical-production-2026-09-12`](../results/current/no-classical-production-2026-09-12).

## Subsequent candidate admission and proof audit

The shared candidate admission now checks an explicit `max_candidate_bits`
budget before theorem APIs allocate a Fermat width, construct constraint state,
or enter the exponent predicate. The CLI forwards its admitted budget to the
same owner. Raw symbolic source compilation remains independent of this
classification request. Direct Mersenne certificates no longer fall through
to an unbounded factor search above the deterministic exponent predicate.

The API and CLI release gate now has eight cases, all failing on the same four
unresolved candidates. The new M11 Isabelle theorem checks the exact normalized
zero-root key and compositeness. It does not construct or disprove the missing
terminal publisher. Details are in the
[candidate recovery audit](candidate-shadow-recovery-audit-2026-09-12.md) and
[component evidence](../results/current/shadow-recovery-audit-2026-09-12/README.md).
