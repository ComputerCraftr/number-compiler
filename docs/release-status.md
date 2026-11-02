# Current release gates

Version **0.60.0 is prepared; release remains blocked**.
Reviewed 2026-11-02. This is the current disposition, not a run log.
The bounded NC19/NC26 integration and adversarial authority/lifecycle repairs
based on `b2878647` pass native runtime, quality and applicable family kernel
sessions. The follow-up rejects forged accumulator fields, incompatible warm
actions and mutated results, and repairs exception cleanup accounting.
[Current integration gates](sprints/week-of-2026-10-25/carry-period-cli.md)
record the new runtime, proof and performance results.
The [Antihydra carry repair](sprints/week-of-2026-11-01/antihydra-carry-morphism.md)
adds the source-bound diagonal consumer and accepted multiplication/carry
refinements, preserves the balanced construction bounds, and fixes root-source
reuse and failed-work reporting. It does not establish an additional general
CLI speedup or a non-halting certificate.
The [diagonal and modular follow-up](sprints/week-of-2026-11-01/diagonal-modular-cli.md)
connects issued Collatz windows, shared reverse carry projections and 2rev10
endpoint reuse to their CLI consumers. Its Python, quality and applicable P0
checks pass, with measured cold improvements on eligible demands. Its concrete
reverse/add carry producer and modular observer bridge also pass kernel checking.
Its finite ordinary-nth follow-up reduces intermediate reverse/add publication
and uses a bounded packed diagonal evaluator inside issued 2rev10 actions.
Fresh complete-suite, quality and CLI comparisons pass. The finite-native
reverse/add and packed-nibble refinements are accepted under the standard
session limits.
The [prime rank and effective-return follow-up](sprints/week-of-2026-11-01/prime-rank-effective-returns.md)
adds bounded prime rank reuse and lazy scalar CLI consumption, shares affine
congruence arithmetic with Collatz, and corrects the bounded 2rev10 return audit.
Prime CLI comparisons improve; the prime refinement chain and corrected 2rev10
counterexample pass kernel checking. Finite return diagnostics do not establish
infinite source closure.
Current integration evidence is scoped development evidence from a dirty
checkout based on Git `b2878647196227365a754212ac56cfdf5aed9923`; it does not
certify a release commit. Earlier evidence remains scoped to its linked source.

| Gate | Current disposition | Evidence owner / next requirement |
| --- | --- | --- |
| Strict mypy, Ruff, Pyright and formatting | PASS with zero findings across the complete maintained Python tree | [Current whole-tree quality evidence](sprints/week-of-2026-11-01/prime-rank-effective-returns.md#validation-provenance) |
| Repository source policy | PASS, including duplicate bodies, dependency direction and guarded launch paths | [Current validation](sprints/week-of-2026-11-01/prime-rank-effective-returns.md#validation-provenance) and [authority audit](sprints/week-of-2026-10-25/carry-period-cli.md#source-seam-and-resource-audit) |
| Pylance | Editor-specific review remains separate from the guarded Pyright batch | [October 25 evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#current-status--2026-10-26) |
| Installed wheel and minimum Python | Fresh native wheel passes; the prior Python 3.11 smoke check remains separately recorded | [Current wheel evidence](sprints/week-of-2026-11-01/prime-rank-effective-returns.md#validation-provenance) and [minimum-version evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#runtime-and-diagnostic-evidence) |
| Complete default Python suite | PASS natively within the 300-second limit. Colima evidence predates this integration | [Current full-suite evidence](sprints/week-of-2026-11-01/prime-rank-effective-returns.md#validation-provenance) and [prior Colima evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#adversarial-identity-lifecycle-and-source-analysis-audit--2026-10-26) |
| P0 release assertions | Applicable reverse/add and Collatz selection passes; source-7 non-halting and candidate prime-bit holds remain | [Current P0 evidence](sprints/week-of-2026-11-01/prime-rank-effective-returns.md#validation-provenance) |
| Bounded prime rank and scalar CLI | Source-prefix and signed rank refinements pass; eligible cold CLI requests improve with bounded retained storage. Packed Python boundary encoding has independent executable coverage, not a kernel extraction theorem | [Current proof and performance scope](sprints/week-of-2026-11-01/prime-rank-effective-returns.md#established-results) |
| Shared carry, reverse and double-reverse refinements | Concrete reverse half-run successor/carry-mask/modular projection, mod-99 rank-one power, double-reverse mod-90/990 and Collatz source-window refinements pass. Unrestricted selection and full polynomial/signed-cut refinements stay open | [Current kernel evidence and scope](sprints/week-of-2026-11-01/diagonal-modular-cli.md#established-results) |
| Antihydra/Mahler cold integration | Source-bound carry and demanded diagonal integration pass finite runtime/kernel checks without the archive's quadratic left fold. The current comparison does not establish an extra general CLI or cold matrix-constructor speedup | [Current carry/CLI evidence](sprints/week-of-2026-11-01/antihydra-carry-morphism.md#validation-provenance) and [earlier observer improvement](sprints/week-of-2026-10-25/carry-period-cli.md#measured-cli-performance) |
| Powered CLI integration and performance | Cold reverse modular, 2rev10 seed-morphism and guarded Collatz requests improve. The finite ordinary-nth follow-up also measures fewer reverse/add publications and faster reverse/add and 2rev10 decimal CLI requests. Both finite reverse/add and packed-nibble refinements are accepted. No comma speedup or unrestricted logarithmic full-word construction is established | [Current CLI evidence](sprints/week-of-2026-11-01/diagonal-modular-cli.md#finite-ordinary-nth-follow-up) |
| 2rev10 bounded temporal carry square | Bounded cone/worklist, exact source seams and finite scalar-weight refinements pass; cold/warm CLI improvements are measured. Unrestricted future closure remains open | [Current integration evidence](sprints/week-of-2026-10-25/carry-period-cli.md#measured-cli-performance) |
| Standalone 2rev10 macro summary | Open: no term-owned published occurrence cursor; explicit matrix traces are available | [Demand-laziness boundary](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#remaining-work) |
| Comma B1/B32/global and forest/fuel retirement | Graph instance and native reuse fixtures pass. Concrete B1 advances farther but exhausts its unchanged action/proof arena before completion. B32/global remain unaccepted; the cutover patch is unapplied and the artifact registry empty | [Current proof and retention evidence](sprints/week-of-2026-10-18/strict-toolchain-macro-identities.md#comma-near-reuse-and-crt-retention-repair--2026-10-26) and [pending patch](../devtools/cutovers/README.md) |
| Unrestricted constructors, primality and global non-halting | Open mathematical/production obligations | [Research scope](index.md#research-syntheses) and [formal proof index](proofs.md) |

Validation uses the [shared execution policy](development.md#reproducible-release-commands).
Release acceptance requires a clean committed source, the isolated acceptance
worktree, complete required selections and their applicable kernel builds.

Run counts, timings and run identifiers belong only in the linked sprint record.
Superseded dispositions are recoverable through Git; they are not active gates.
