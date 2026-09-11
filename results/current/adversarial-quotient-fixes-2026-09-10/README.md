# Adversarial audit fixes — September 10, 2026

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

This checkpoint fixes the concrete correctness and redundant-work findings in
the [preceding audit](../adversarial-quotient-audit-2026-09-10/README.md).
It does not promote the unfinished reverse/add or Collatz temporal quotients.

## Changes

- **Power-of-two radix limbs:** a shared binary point helper preserves the
  kernel's explicit blank symbol. Public binary digits still reject blank
  coordinates. Radix projection treats high blanks inside a valid limb as
  zero padding and rejects an entirely exterior limb. It neither forces exact
  width nor catches arbitrary `IndexError` exceptions from the executor.
- **Reverse transfer setup:** primitive-law eligibility reads each child once;
  the selected law also constructs the morphism. Wiring and initial ports are
  obtained only for the fallback that consumes them.
- **Unused exterior transfers:** multi-chunk execution computes only interior
  producer endpoints. The final left exit and final right exit did not feed
  any chunk binding. This applies to both morphism and finite-interface paths.
- **Duplicate validation:** the scheduler uses the canonical adapter's checked
  child accessor without validating the same parent immediately beforehand.
  Generic adapters retain their explicit validation. Child checks, action
  publication checks, and adversarial in-place mutation rejection remain.
  No persistent validation cache or unchecked action capability was added.
- **Dead code/state:** removed the unreferenced internal Collatz
  `boundary_proofs.py` module and the write-only `_eviction_occurred` flag.
  The removed module had no imports, documentation references, tests, or
  package re-exports in the repository. External direct imports of that
  orphan submodule, if any, will no longer work.

The legacy completion branches remain because `TileScheduler` supports generic
adapters that still exercise them. Their absence from the canonical hot path
does not make the generic implementation removable. Tested research codecs
also remain. Neither the finite Hensel refinement nor the incomplete 196
context graph is a safe substitute for production successor identity.

## Verification

The new radix matrix checks nine seed/depth combinations at radix 4, radix 64,
and radix `2**63`, with complete width/materialization methods poisoned. It
covers partial and full limbs, interior zero digits, exterior rejection, and
unchanged binary behavior. Separate tests preserve internal point failures
and reject invalid kernel symbols.

The morphism regression now covers single- and multi-chunk views in both
directions with fallback metadata and output construction poisoned. Transfer
tests cover widths 3/4/7, both directions, bases 2/3/10, and reverse/normalizing
consumers, using independent scans. Ownership and payload audits still pass.

Focused results: 45 radix/morphism/Frobenius tests, 155 scheduler/result tests,
63 Collatz/dependency tests (20 validation cases deselected), and 46 final
transfer tests. These groups overlap and must not be added into a unique-test
count. Strict nonincremental mypy passes for 1,102 source files; Ruff and
format checks pass for all changed files.

The initial multi-chunk regression poisoned wiring during both execution and
the later independent payload audit. That audit legitimately uses wiring to
validate retained metadata. The test now restores methods after execution and
before auditing. Both directions then pass without weakening audit assertions;
the original failed log is retained.

The first full serial run had 4,221 passes and one line-cap failure: the added
scheduler import/comment put that module above 1,000 lines. The final import is
shorter, the redundant comment is removed, and the module is exactly 1,000
lines. The subsequent policy/scheduler check passes. The first failed run and
an intermediate 1,001-line check are retained; the limit was not raised.

The final serial unit suite passes **4,222 tests in 276.75 seconds**, with
926 validation cases deselected and no failures, errors, or skips. Its before,
after, and current source fingerprints match. The unchanged 300-second guard
completes in 277.48 seconds at 571,327,328 bytes sampled peak footprint. The
final 57-test policy/scheduler check also passes. See `unit-final.xml`,
`unit-final.guard.json`, and `manifest.json`.

## Measured effect and remaining cost

The same cold `ReverseAddPoweredTerm(196, 32).digit(0)` probe checks its result
against exact arithmetic after timing. Construction is excluded in both runs.

| Measurement | Before | After |
| --- | ---: | ---: |
| Unprofiled query, seconds | 3.700 | 3.782 |
| Instrumented query, seconds | 13.661 | 13.560 |
| Instrumented Python calls | 42,624,691 | 41,203,191 |
| Action validations | 166,896 | 159,842 |
| Primitive directed advances | 7,823 | 5,865 |
| Causal frame publications | 65,333 | 63,035 |

This removes **7,054 validations** and **1,958 directed advances** in the
measured query. The single-trial wall times do not establish a speedup.
The 53,396 processed causal frames and 1,362 exact fallback requests remain;
these local fixes do not solve the larger successor-quotient workload.
Remaining action validations still check mutation-sensitive state.
These probes preceded the final scheduler import/comment cleanup; their source
fingerprint is recorded separately from the final unit-tested fingerprint.

Parent-run heavy checks ran serially under the repository process guard, using its normal
35-second/1 GiB limits for focused work and its existing 300-second limit for
the serial unit suite. No gate, test selection policy, or performance assertion
was weakened. No broad exhaustive-validation or new Isabelle result is claimed.

A process audit found an explorer's unguarded probe still running; the explorer
confirmed ownership and terminated it. Another Python worker could not be
attributed to this task and was left alone. Consequently these wall timings
are observations on a shared host, not isolated comparative benchmarks. The
guarded test results and deterministic call-count reductions remain the evidence.

`fixes.patch` contains the source/test changes, `before.json` preserves their
prior contents, and `manifest.json` records source and evidence hashes.
