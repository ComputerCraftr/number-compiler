# Documentation migration and provenance

This is the single old-path map for superseded authored prose. The six
[research syntheses](index.md#research-syntheses) preserve the mathematical
assumptions and claim boundaries; weekly records preserve implementation
status. The complete per-report evidence inventory and 206-node baseline
failure disposition are in [repository hygiene evidence](sprints/history/hygiene-disposition-2026-09-20.md).
Redirect stubs were deliberately not created.

Raw logs, JSON, profiles, patches, and machine-readable fingerprints were not
bulk deleted. Externally supplied decimal pair research remains verbatim at
[`DECIMAL_PAIR_QUOTIENT_RESEARCH.md`](archive/reverse-add/DECIMAL_PAIR_QUOTIENT_RESEARCH.md)
with SHA-256
`023599ebc89d1f17601bb84f4fda49c2daaff3308a39e3a7179630cd41683cbe`.

## September 27 Sunday-start sprint correction

Sprint folders now use their Sunday start date and cover Sunday–Saturday.
The former W39 file had accumulated more than 5,000 lines; its implementation
records are now categorized under the September 20 and September 27 weeks.
September 20 records formerly filed in W38 belong to the September 20 week.
The September 26–27 comma rank record is retained once in its completion week,
with the original two-day scope explicit.

The older September 7–13 and September 14–20 aggregate syntheses cannot be
reliably split into daily events. They remain cross-week retrospectives under
`docs/sprints/history/`; Sunday-start weekly indexes link to them without claiming
new dates. Section links and catalog destinations were updated. Original
fingerprints, measurements and raw evidence paths remain unchanged; no raw
evidence or external archive was moved. This edit does not validate production.

## September 22 research/sprint separation

Thirty-four implementation and evidence records were moved out of the shared,
Collatz, Antihydra/Mahler and reverse/add papers. Their mathematical definitions,
assumptions, scoped counterexamples and current obligations remain in those
papers, with links to the dated records. No external archive was edited.

| Original material | Preserved destination | Scope |
| --- | --- | --- |
| September 20 reverse/add carry recovery, spatial grammar, slab comparison and failed cutover measurements | [September 20 evidence](sprints/week-of-2026-09-20/README.md#additional-dated-evidence) | Original commands, missing-evidence qualifications and fingerprints retained |
| September 20 Mahler proof builds, fractional census, reachable grammar and event pruning | [September 20 evidence](sprints/week-of-2026-09-20/README.md#additional-dated-evidence) | Finite validation remains separate from source-global claims |
| September 21–22 shared audits and family integrations | [September 20–26 topic records](sprints/week-of-2026-09-20/README.md#provenance-and-reading-guide) | Original implementation snapshots and their later supersession remain explicit |
| Collatz source-macro and cycle measurements | [September 21–22 evidence](sprints/week-of-2026-09-20/README.md#additional-dated-evidence) | Construction boundaries and cold/warm qualifications retained |

This is a documentation reorganization, not new code or proof validation.
Historical artifact paths remain local evidence references. The
[placement guide](development.md#documentation-placement) governs future updates.

## Checkpoint evidence capsules

The archive was not an external-source collection.  Most entries were authored
research or implementation checkpoints.  Ten redundant repository-status
reports were removed after the following evidence was retained.  `Document
SHA-256` fingerprints the exact removed Markdown.  “Not recorded” means that
the checkpoint did not contain that evidence; it must not be inferred from a
later run.

| Removed checkpoint | Document SHA-256 | Source and recorded outcome | Command / limits | Review scope | Preserved destination |
| --- | --- | --- | --- | --- | --- |
| `docs/archive/repository-and-algebra/CLEANUP_RESULTS.md` | `45ea0bf75a9148d331ae587ad733ef333312910ade63577fc282a1a9114b7d81` | No source fingerprint or independent result; five-line pointer to the canonical cleanup report | Not recorded | Not recorded | [shared synthesis](research/shared.md) and retained `CANONICAL_CLEANUP_RESULTS.md` |
| `docs/archive/repository-and-algebra/COMPILER_DEBT_RESULTS.md` | `6f6811c6f8fe86f99649f58b0562b54802e1433ad14bb2d51f079fd05e6e1c1d` | No source fingerprint; inventory of consolidation and dead-code changes | Not recorded | Self-report only | [shared synthesis](research/shared.md) |
| `docs/archive/repository-and-algebra/EARLY_CANONICAL_RELEASE_RESULTS.md` | `a8793133bb27b2c134eb6ec61ee4c83f75de8741d9ac988ff2eb0b25e09c7cf2` | No source fingerprint; early canonical-runtime measurements, superseded by later bounded metrics | Commands were named in prose; no durable resource guard | Self-report only | retained `CANONICAL_CLEANUP_RESULTS.md` and `HASHLIFE_METRICS_INTEGRITY_RESULTS.md` |
| `docs/archive/repository-and-algebra/EARLY_CANONICAL_RESULTS.md` | `78cdbc3e016d74e8c09e7dd1ea9b51c4dbb35ce4287c212fc6951d1f6eab0fc3` | No source fingerprint; earlier canonicalization measurements | No durable command/guard record | Self-report only | retained `CANONICAL_CLEANUP_RESULTS.md` |
| `docs/archive/repository-and-algebra/ITERATIVE_REPOSITORY_CLEANUP_RESULTS.md` | `4022ea69e5fc29219d23aa07e4fbfcf3cd11499b275bb77b2cf6754e4b6393c0` | No source fingerprint; records recursion removal and policy coverage, with no complete gate outcome | Named policy test only; no resource guard | Self-report only | [development](development.md) and [shared synthesis](research/shared.md) |
| `docs/archive/repository-and-algebra/RELEASE_RESULTS.md` | `cb482cb8b6f085fbed965f5f115779f20a53911eb153289966508c9285edcca2` | Source `994fa53f9182`: 4,348 passed, 10 unchanged absorption failures, 380.09 s; Ruff, strict mypy, and structural checks reported passing | Exact invocations and resource limits not recorded | Self-report; no independent reviewer identified | this table and retained raw historical evidence where present |
| `docs/archive/repository-and-algebra/REPO_LAYOUT.md` | `f1884b21c4f39c1b5452418a861fd0790f90f7467e5a706afaeb934b2e8ae632` | No source fingerprint or validation outcome; obsolete ownership map | Not applicable | Not recorded | [architecture](architecture.md) |
| `docs/archive/repository-and-algebra/STATUS.md` | `9d77f422399ca408012991870e5deef578e0ccf1e2487638d079b420af71d1b3` | No source fingerprint; reported 2,862/2,862 tests at an unidentified old checkout | Exact invocation and limits not recorded | Self-report only | this table; superseded by [release status](release-status.md) |
| `docs/archive/repository-and-algebra/TECH_DEBT_CLEANUP_RESULTS.md` | `3a14d4339f902712b7ea81217c2da208f4012285ea132658a7e99a02ba1d352b` | No source fingerprint; implementation cleanup inventory, no complete gate outcome | Not recorded | Self-report only | [development](development.md) and [shared synthesis](research/shared.md) |
| `docs/archive/repository-and-algebra/TEST_RESULTS.md` | `4d3076fa812f747bb19a91da97ad99ba321237dc61bca304e68b9388a602130d` | Source `994fa53f9182`: 4,348 passed / 10 failed in 380.09 s. Source `64244f87626f`: 4,324 passed / 10 failed in 386.08 s. An earlier unidentified tree reported 1,901 passed in 519.85 s. | Serial, unfiltered suite was stated for `64244f87626f`; exact command, memory limit, and tool versions not recorded | No independent reviewer identified; targeted checks were author-run | this table and retained topic reports |

For the removed ISO-week result prose, the path map below preserves scope and
destination.  Raw JSON/log evidence remains at the old result directory when
it existed.  Those files are authoritative for their own source fingerprint,
return code, elapsed time, memory limit, peak sample, and output.  Some ignored
Markdown summaries had no recoverable baseline copy after consolidation; this
is recorded as a provenance limitation rather than silently inventing their
commands or review conclusions.  The repository-hygiene baseline is retained
at `results/current/repository-hygiene-2026-09-20/`.

## Superseded authored paths

| Former path | Weekly record | Maintained research |
| --- | --- | --- |
| `docs/adversarial-release-audit-2026-09-13.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/antihydra-production-and-proof-2026-09-12.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [antihydra-mahler](research/antihydra-mahler.md) |
| `docs/associated-action-integration-2026-09-14.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `docs/candidate-shadow-recovery-audit-2026-09-12.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [fermat-mersenne](research/fermat-mersenne.md) |
| `docs/carry-harmonic-port-actions.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `docs/cli-clock-cylinder-cleanup.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/cli-performance-release-audit-2026-09-12.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/clock-coordinate-growth-audit.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/clock-quotient-growth-audit.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/collatz-free-consumer-growth.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [collatz](research/collatz.md) |
| `docs/collatz-harmonic-port-actions.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [collatz](research/collatz.md) |
| `docs/collatz-support-integration-audit-2026-09-12.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [collatz](research/collatz.md) |
| `docs/constructor-quotient-proof-audit.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/continuation-growth-audit.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/cylinder-cli-adversarial-audit-2026-09-12.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/cylinder-cli-release-fixes-2026-09-12.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/cylinder-collapse-audit.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/cylinder-helix-rays.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/cylinder-p0-release-gates-2026-09-12.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/cylinder-skew-observers.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/digit-cli-cutover-priority-2026-09-14.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `docs/endpoint-seam-powering-audit.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/future-consumer-cleanup.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/geometry-derived-carry.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `docs/growth-coboundary-directional-quotients.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/mirror-pair-residue-quotient.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `docs/mod9-skew-state-removal.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/performance-agent-closure-2026-09-13.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/physical-bound-clock-refinement-2026-09-12.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/port-valued-mealy-actions.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/prime-clock-owner-audit-2026-09-13.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [primes-goldbach](research/primes-goldbach.md) |
| `docs/prime-source-rank-release-2026-09-13.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [primes-goldbach](research/primes-goldbach.md) |
| `docs/production-p0-followup.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/production-p0-integration.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/production-shadow-jet-release-blocker-2026-09-12.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [fermat-mersenne](research/fermat-mersenne.md) |
| `docs/publisher-antihydra-p0-followup-2026-09-12.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [antihydra-mahler](research/antihydra-mahler.md) |
| `docs/research/power-numbers/GEOMETRY_FIRST_ETALE_TILE_APPLICABILITY.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [fermat-mersenne](research/fermat-mersenne.md) |
| `docs/research/power-numbers/etale-isabelle-proof.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [fermat-mersenne](research/fermat-mersenne.md) |
| `docs/research/power-numbers/five-bit-folded-square.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [fermat-mersenne](research/fermat-mersenne.md) |
| `docs/research/power-numbers/multiplication-consumer-congruence.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/research/power-numbers/primary-carry-jet-restoration.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `docs/research/power-numbers/radix64-mirror-refinement.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/research/power-numbers/square-consumer-congruence.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [fermat-mersenne](research/fermat-mersenne.md) |
| `docs/research/power-numbers/square-forcing-lifetime.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [fermat-mersenne](research/fermat-mersenne.md) |
| `docs/research/reverse-add/decimal-pair-algebra.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `docs/reverse-add-source-publisher-audit-2026-09-12.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `docs/reverse-forcing-alphabet-transducer.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `docs/reverse-radial-hypergeometric-elimination.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `docs/shadow-cylinder-proof-contract-2026-09-12.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [fermat-mersenne](research/fermat-mersenne.md) |
| `docs/shared-action-adversarial-audit-2026-09-14.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `docs/shared-action-cleanup-2026-09-14.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `docs/skew-cylinder-return-owner-2026-09-19.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `docs/skew-scheduler-unification-2026-09-13.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/source-chart-selector-fusion-2026-09-19.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `docs/support-owner-repair-2026-09-12.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `docs/temporal-clock-jump-proofs.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/behavior-reuse-5a9490c69f221f08/REPORT.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/behavior-reuse-9d08662e4491d83c/REPORT.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/causal-reuse-7c150a182c8ff17e/REPORT.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/196-bilateral-cascade-2026-09-19/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-bilateral-cascade-2026-09-19/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-bilateral-residual-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-carry-length-2026-09-19/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-centered-events-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-centered-jump-proof-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-centered-residual-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-cli-admission-2026-09-19/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-cli-admission-2026-09-19/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-cocycle-owner-cleanup-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-composed-ports-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-cylinder-arrow-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-cylinder-carry-admission-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-cylinder-carry-admission-2026-09-20/grammar-audit.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-cylinder-range-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-forcing-slp-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-forcing-slp-2026-09-20/frozen/independent-audit.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-four-step-regions-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-growth-consumer-research-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-growth-pullback-2026-09-19/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-hypergeometric-crt-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-interface-normalization-2026-09-19/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-interface-normalization-2026-09-19/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-lacunary-production-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-lacunary-production-2026-09-20/audit.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-live-forcing-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-mealy-construction-attempt-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-no-growth-cylinder-2026-09-19/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-nth20-diagnosis-2026-09-19/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-parameter-region-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-pumped-grammar-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-pumped-grammar-2026-09-20/adversarial-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-radial-clock-cleanup-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-radial-sections-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-source-coboundary-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-source-ray-correction-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-source-scheduler-cutover-2026-09-19/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-symbolic-local-channels-2026-09-20/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-temporal-transform-2026-09-19/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/196-temporal-transform-2026-09-19/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/active-behavior-release-blockers-2026-09-09/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/adversarial-quotient-audit-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/adversarial-quotient-fixes-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/adversarial-release-2026-09-13/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/antihydra-integration-2026-09-12/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [antihydra-mahler](research/antihydra-mahler.md) |
| `results/current/associated-action-integration-2026-09-14/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/admission-selection-followup/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/admission-selection-followup/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/audit-expansion-final/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/audit-expansion-final/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/audit-expansion-followup/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/audit-expansion-followup/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/construction-followup/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/construction-followup/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/diagnostics/cli-output-path-audit.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/diagnostics/cold-path-audit.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/diagnostics/fixed-width-growth-audit.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/diagnostics/reverse-temporal-constructor-audit.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/associated-action-integration-2026-09-14/followup-before-combined-diagnostic-fix/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/followup-before-combined-diagnostic-fix/extractor-construction-audit.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/followup-before-combined-diagnostic-fix/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/followup-before-observer-root-fix/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/followup-before-signature-diagnostic-fix/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/followup-before-signature-diagnostic-fix/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/followup/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/followup/extractor-construction-audit.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/followup/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/occurrence-prefix-followup/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/occurrence-prefix-followup/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/prefix-admission-followup/196-validation-audit.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/associated-action-integration-2026-09-14/prefix-admission-followup/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/prefix-admission-followup/development/earlier-causal-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/prefix-admission-followup/development/earlier-prefix-fragment-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/prefix-admission-followup/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/prefix-admission-followup/prime-proof-scope.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [primes-goldbach](research/primes-goldbach.md) |
| `results/current/associated-action-integration-2026-09-14/prime-initialization-followup/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [primes-goldbach](research/primes-goldbach.md) |
| `results/current/associated-action-integration-2026-09-14/prime-initialization-followup/development/validation-attempt-1/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [primes-goldbach](research/primes-goldbach.md) |
| `results/current/associated-action-integration-2026-09-14/prime-initialization-followup/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [primes-goldbach](research/primes-goldbach.md) |
| `results/current/associated-action-integration-2026-09-14/scheduler-demand-followup/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/scheduler-demand-followup/construction-frontier.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/associated-action-integration-2026-09-14/scheduler-demand-followup/independent-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/bounded-interface-2026-09-08/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/canonical-reuse-2026-09-09/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/carry-domain-cleanup-2026-09-09/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/carry-domain-reuse-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/carry-harmonic-ports-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/cli-clock-deck-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/cli-performance-2026-09-12/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/clock-coordinate-growth-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/clock-quotient-growth-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/collatz-directional-views-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [collatz](research/collatz.md) |
| `results/current/collatz-harmonic-ports-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [collatz](research/collatz.md) |
| `results/current/collatz-hensel-cylinders-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [collatz](research/collatz.md) |
| `results/current/collatz-hensel-validation-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [collatz](research/collatz.md) |
| `results/current/collatz-output-budget-2026-09-19/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [collatz](research/collatz.md) |
| `results/current/collatz-output-budget-2026-09-19/independent-signoff.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [collatz](research/collatz.md) |
| `results/current/collatz-output-budget-2026-09-19/remaining-family-construction-audit.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [collatz](research/collatz.md) |
| `results/current/collatz-output-quotient-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [collatz](research/collatz.md) |
| `results/current/continuation-growth-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/continuation-growth-2026-09-10/collatz-README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [collatz](research/collatz.md) |
| `results/current/coordinate-morphisms-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/cylinder-p0-release-2026-09-12/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/cylinder-ray-restoration-2026-09-12/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/cylinder-skew-observers-2026-09-12/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/disconnected-quotient-audit-2026-09-09/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/endpoint-seam-powering-2026-09-11/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/family-first-cli-2026-09-12/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/future-consumer-cleanup-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/geometry-derived-carry-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/growth-coboundary-directional-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/memory-incident-2026-09-08.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/mirror-pair-quotient-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/morphism-connection-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/no-classical-production-2026-09-12/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/performance-agent-closure-2026-09-13/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/port-valued-mealy-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/prime-source-rank-2026-09-13/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [primes-goldbach](research/primes-goldbach.md) |
| `results/current/prime-wheel-owner-2026-09-13/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [primes-goldbach](research/primes-goldbach.md) |
| `results/current/production-p0-2026-09-11/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/publisher-antihydra-p0-2026-09-12/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [antihydra-mahler](research/antihydra-mahler.md) |
| `results/current/python-quality-cleanup-2026-09-14/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/quotient-integration-2026-09-09/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/quotient-reuse-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/reverse-consumer-schema-audit-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/reverse-contextual-residuals-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/reverse-executor-cutover-2026-09-14/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/reverse-factored-carrier-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/reverse-isabelle-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/reverse-quotients-2026-09-08/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/reverse-run-controls-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/reverse-threshold-cocycle-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/reverse-threshold-geometry-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/shadow-recovery-audit-2026-09-12/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [fermat-mersenne](research/fermat-mersenne.md) |
| `results/current/shared-action-adversarial-audit-2026-09-14/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/shared-action-cleanup-2026-09-14/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/skew-cylinder-return-owner-2026-09-19/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/skew-scheduler-unification-2026-09-13/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/skew-scheduler-unification-2026-09-13/independent-review.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/skew-state-removal-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/source-chart-selector-fusion-2026-09-19/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/source-image-construction-2026-09-19/196-temporal-constructor-frontier.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [reverse-add](research/reverse-add.md) |
| `results/current/source-image-construction-2026-09-19/README.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/source-image-construction-2026-09-19/independent-arithmetic-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/source-image-construction-2026-09-19/independent-cross-family-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/source-image-construction-2026-09-19/performance-frontier-review.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/source-image-construction-2026-09-19/proof-scope.md` | [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md) | [shared](research/shared.md) |
| `results/current/temporal-clock-proofs-2026-09-10/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/current/unit-suite-cleanup-2026-09-09/README.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |
| `results/tile-complete-output-90326adda1b0373b/PROFILE.md` | [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md) | [shared](research/shared.md) |

## Evidence rule

A durable checkpoint records source fingerprint or commit, command and resource
guard, tool versions, every pass/fail/timeout/unrun outcome, theorem assumptions,
oracle status, artifact hashes or stable locations, independent review scope,
and supersession. A later fingerprint never inherits an earlier pass.

Reviewed prose is consolidated once per ISO week. Generated evidence stays in
ignored result directories and is not a maintained navigation target.
