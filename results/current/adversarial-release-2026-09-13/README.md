# Adversarial release evidence — September 13

**Release remains blocked.** The [audit](../../../docs/adversarial-release-audit-2026-09-13.md)
records the reproduced defects, repairs and remaining construction/proof gaps.
No acceptance assertion, resource limit or unresolved decision was weakened.

## Independent audits and repairs

- `cli_performance_audit` traced the production routes and the missing compact
  Fermat/Mersenne evaluator. Its final review reproduced the 196 identity-action
  substitution: generation 8, coordinate 0 changed from 9 to 7. It independently
  retested rejection after repair and found the reporting/certificate asymmetry
  that was subsequently repaired in the shared validator.
- `support_semantics_proof` implemented the lazy 196 image, preserving the
  independent primitive-port comparison at first output demand. It then repaired
  canonical action/schema/certificate authority. The root shared that validator
  with reporting and added coordinated-mutation tests.
- `antihydra_support_repair` closed direct-observer and cached-physical acceptance
  of mutated retained arithmetic support. Its canonical constructor is shared
  with runtime admission. The root also rejected Boolean segment coordinates
  in both runtime and payload audit.

## Validation

The `.log` files contain child output; corresponding `.json` files contain
guard status, elapsed time, sampled peak physical memory and limits.

| Evidence | Outcome |
| --- | --- |
| `antihydra-support` | Strict typing, Ruff and 167 focused tests pass after canonical-owner refactor. |
| `antihydra-final` | 168 tests pass after exact segment-coordinate admission; 3.90 s guard, 59 MB peak. |
| `publisher-authority-agent` | 62 publisher/correspondence/admission tests pass; 5.45 s, 81 MB. |
| `publisher-cli-final` | 91 publisher/CLI/admission tests pass after sharing action validation; 8.19 s, 85 MB. |
| `cli-policy-focused` | 98 CLI, publisher and repository-policy tests pass at the earlier lazy-image checkpoint. |
| `typing-final` | Strict mypy passes 1,296 files after final production edits. |
| `p0-final` | **15 fail, 7 pass** in 3.77 s, 91 MB; same 22 release assertions. |
| `full-unit-incomplete` | Initial run terminated at 300 s / 1 GiB; progress reached 87%. Incomplete, not a pass. |
| `full-unit-final` | **5,032 pass, 4 fail, 1,277 deselected**; 290.64 s guard, 634 MB peak under the unchanged 300 s / 1 GiB limit. |
| `installed-wheel` | Source/package byte equality, public API, resources and 8 family-first contract cases pass; 5.18 s, 117 MB. |
| `isabelle-combined-incomplete` | Combined four-session check hits the unchanged 35 s / 4 GiB guard while building `Reverse_Residuals`; incomplete. |
| `isabelle-antihydra` | Separate incremental `Antihydra` session check passes; 5.46 s, 1.34 GB. |
| `isabelle-etale` | Separate incremental `Etale_Primary_Carry` check passes; 7.83 s, 1.44 GB. |

Ruff and `git diff --check` also pass. The earlier unit timeout is preserved.

The four final ordinary-unit failures are the existing 196 clock-key/cutover
assertion, special-number source-compiler assertion, reverse runtime-class
assertion and reverse source-publisher cutover assertion. The final run has no
new failing test compared with the preceding audit. It remains a failing
release gate, not a green unit result.

No Isabelle source was changed by this follow-up. The separate successful
checks confirm the existing component sessions are current; they do not add
the missing source-7 invariant or executable powered-constructor refinement.
The combined command was `isabelle build -j 1 -d devtools/proofs/isabelle
Reverse_Residuals Temporal_Clock_Jumps Etale_Primary_Carry Antihydra`.
Reverse/temporal session verification remains incomplete in this run. Its
timeout is retained and is not counted as proof success.

The fifteen explicit P0 failures comprise five reverse/add image/cutover
assertions, nine special-number recovery assertions and the absent Antihydra
source-7 certificate. The broader common-support/Collatz/projection obligations
are tracked separately; this selection does not exhaust them.

## Installed timing

`installed-timing.log/json` compares three fresh processes per wheel and
request, including imports and requested construction/output. The output
semantics match exactly. Filesystem caches remain enabled.

| Request | Previous wheel median | Repaired wheel median |
| --- | ---: | ---: |
| `196 --nth 8 --format json` | 0.2151 s | 0.2227 s |
| `antihydra --nth 512 --info ledger --info clock --format json` | 0.07651 s | 0.07682 s |

The repair adds validation; these samples do not establish an end-to-end
speedup. They also do not prove a bound for arbitrary powered source discovery.

Previous wheel SHA256:
`e64d8f8b944fd1c8de869c853c77eb1093bd45fd2deab030f3bf4a69ece5320f`.
Repaired wheel SHA256:
`8ccf371071621efa99c73a26e7ba8540845a8eb55b6c5765b404541c1260cd31`.
The wheel was built in an isolated build environment. The initial attempt
without build isolation could not import `setuptools.build_meta` and did not
produce a wheel.

`antihydra-validation-cost.log/json` measures repeated source admission:
64 returns / 1 segment costs 12 microseconds; 512 / 8 costs 110 microseconds;
2048 / 32 costs 443 microseconds. Clock, Mahler and tape at N=512 perform one,
two and three admissions respectively. These remain charged linear checks.

## Rejected optimization

`rejected-ledger-read.log/json`, `.patch` and `-probe.py.txt` preserve a removed
experiment. Direct backing-table membership/get looked cheaper in isolation,
but the real fresh Collatz seed-27/N=64 output benchmark measured a median
4.919 s versus 3.833 s for the original Mapping methods. Output, retained
nodes/entries and selected real-work counters matched. The patch was removed;
`resources/stores.py` retains its prior implementation. The probe text is
historical evidence, not a supported production benchmark against the repaired
tree.
