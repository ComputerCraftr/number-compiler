# Temporal clock proof checkpoint

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

See the [theorem and execution-scope report](../../../docs/temporal-clock-jump-proofs.md).

The accepted checkpoint is `final2/`; the preceding `final/` pass found a
new-test tuple annotation error after its proof/test jobs passed. That error
is corrected before the new frozen run.

**Validation:** 80 selected Python tests passed, strict mypy checked 1,189
source files, and Ruff passed. The clean four-theory Isabelle session completed
in 8.73 seconds with a sampled peak of 446,352,552 bytes.

The accepted final checkpoint is recorded in the manifest (local artifact: `final2/manifest.json`).
It freezes authored source and hashes each new Isabelle theory, then verifies
that the source fingerprint remains unchanged after every guarded command.
The clean child-session build rechecks all four new theories against the
validated `Reverse_Residuals` parent heap. Every new theory rejects oracle
dependencies; no `sorry` or quick-and-dirty proof is used.

* Clean Isabelle build (local artifact: `final2/isabelle.log`), guard (local artifact: `final2/isabelle.guard.json`).
* Executable jumps (local artifact: `final2/jumps.log`), JUnit (local artifact: `final2/jumps.junit.xml`): finite
  terminal-deck A1…A1024 with primitive evaluation poisoned; supplied affine
  powers; every nine-event decimal transport itinerary and an eight-event
  survivor; known-order jumps of duration `10^100+17`.
* Dependency checks (local artifact: `final2/dependencies.log`): current cylinder and Hensel
  occurrence controls, including future distinctions that must survive.
* Repository policy and proof boundary (local artifact: `final2/policy.log`).
* Strict typing (local artifact: `final2/mypy.log`) and Ruff (local artifact: `final2/ruff.log`).

The finite-table tests charge full-ring compilation separately. They do not
claim that compilation of arbitrary-width full-germ quotients is logarithmic.
The known-order tests verify their annihilating orders before reducing temporal
exponents and never construct the giant integer `2^(10^100+17)`.

All heavy jobs run serially under the unchanged 35-second/1-GiB guard.
The Isabelle profile uses `ISABELLE_IDENTIFIER=number-compiler-ports-proof`,
whose Java heap is 64–256 MiB and Poly/ML heap 100–450 MiB. This reduces runtime
allocation rather than raising the guard. Early directory/syntax/proof failures
and the default-profile memory-limit failure remain outside `final2/`; none is
credited as an accepted build. Build 19 first accepted the combined theories;
the clean final build is the frozen-source release evidence.
