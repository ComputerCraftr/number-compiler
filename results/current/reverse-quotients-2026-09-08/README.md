# Reverse quotient checkpoint — 2026-09-08

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

## Status

**Release status: RED.** This checkpoint validates the three-layer ownership
boundary and a focused set of semantic/accounting changes. It does not validate
sublinear reverse execution, the N=16…1024 scaling series, or the five-minute
serial-suite gate.

The serial-run checkpoint source fingerprint is
`d4185ef2f1093dbdfaedca22bbccb16e78d5fe48e2f6f4be3665b548477d52a4`.
Results from an interrupted command are retained as failure evidence and are
not treated as partial passes. Later focused repairs changed the source and do
not inherit this fingerprint.

The final focused validation used fingerprint
`7fad3e40b722d17d061f7706913e2ef47b465c461074fa55bdae509fd0290d80`,
verified unchanged before and after execution. It passed **281 tests in 15.01
seconds**, with sampled process-group footprint 87,982,608 bytes. Ruff formatting
and lint passed; whole-tree strict mypy passed for 1,041 files, including a
nonincremental run; recursive policy reported no violations. These are focused
validation results, not the full serial release gate.

The final runtime N=64 point probe still timed out at 35.0865 seconds, with
sampled footprint 128,008,768 bytes. The later source edits before the final
fingerprint were test annotations only. No higher-N scaling samples were
claimed after this failed gate. All guarded workers exited or were terminated
and reaped; the final process inspection found no remaining test/probe worker.

## What is implemented

Reverse execution now has three explicitly separate representation layers:

1. **Algebraic sector metadata.** A production `ReverseFrobeniusPlan` records
   the certified branch-independent source-coefficient death lower bound for
   decimal homogeneous powers, for sectors `m = 1, 2, 4, 8` at precision 5.
   Plans compose with temporal actions and are retained, charged, and audited
   as part of those actions.
2. **Bounded local behavior.** The executable local law retains mixed-radix
   output distinctions, LT/EQ/GT carry behavior, normalization, and the bounded
   interface required by the tile scheduler.
3. **Exact spatial results.** Canonical source/future tiles and completed
   results preserve exact content and outgoing semantics. Source bindings are
   not removed merely because one algebraic sector has reached its death bound.

The first layer is deliberately narrower than the full algebra developed in
proof and research code. `ReverseFrobeniusSectorProduct.atom` takes executed
growth and forcing observations, derives its unit component, and composes the
resulting sector product. Production has no general scheduler consumer that
derives and advances that complete product.
Consequently, the current runtime plan is a sector-local source-death
certificate. It is not the live `(unit, valuation, B)` product, not a complete
future-behavior quotient, and not evidence that exact causal construction was
avoided.

Compiler counters preserve this distinction. Plan compositions and legacy
`*_source_annihilation_derivations` are compiler facts. They do not increment
the executed `source_annihilations` counter or claim runtime work savings.

## Recorded evidence

| Check | Result | Interpretation |
| --- | ---: | --- |
| Focused reverse/quotient tests | 218 passed in 10.66 s | The selected semantic, ownership, and accounting regressions passed. |
| Whole-tree strict typing | 1,041 files clean | The recorded strict check completed successfully. |
| Recursive repository policy | clean | No source-length, package-boundary, or recursion violations were reported. |
| Reverse N=32 point probe | passed in 20.34 s | One point completed within the probe deadline. |
| Reverse N=64 point probe | timed out at 35.0658 s, sampled peak about 115 MB | The next temporal size did not complete; no doubling ratio or exponent is available. |
| Serial unfiltered suite | timed out at 300.1069 s, sampled peak about 539 MB | About 30% completed and nine then-visible test failures were recorded. Those tests were subsequently migrated, but this artifact contains no completed validating rerun. |

After that frozen checkpoint, a broader 280-test checkpoint passed in 14.87
seconds (15.42 seconds including the guard, sampled peak 83,182,096 bytes). It
includes the focused semantic transaction/admissibility coverage and the 31
migrated tile-runtime audit, atomic-accounting, and ring tests that separately passed
in 6.65 seconds. These focused results validate the named repairs only; they are
not a replacement for a new frozen full-suite run.

The direct decimal leaf comparison verified 4,300 assignments and published
1,005 semantic nodes. Its single trial measured 0.09816 s for the factored path
and 0.10297 s for the comparison path. This small single-run difference is not
a speed claim and says nothing about parent macrocell scaling.

The process guard used a 1 GiB group-footprint ceiling and measured macOS
physical footprint. The N=64 and serial-suite terminations were timeouts rather
than memory-limit terminations.

The final warm-validation change removes fresh alphabet allocation and nested
plan/sector validator calls. It still checks all live handles, semantic fields,
and sector formulas on each request. A mutated retained-sector regression
passes. This bounded overhead reduction did not make N=64 meet its deadline.

## Remaining technical blockers

1. **The full sector action is not executable in production.** Temporal
   composition needs symbolic unit/valuation/innovation components whose
   bounded dependencies the scheduler can resolve and reuse. The action's
   exponent alone cannot determine numerical branch counts or forcing. The
   current source-bound plan cannot discharge those dependencies; deriving an
   innovation from an already completed output would not accelerate its
   construction.
2. **Active future behavior does not yet discharge enough causal work.** Where
   the bounded consumer profile cannot answer a dependency, the scheduler must
   construct exact causal tiles. N=64 timing shows that current reuse is not
   sufficient to meet the probe envelope. A useful behavioral alias must be
   successor-closed for the actual consumer observations; carry or mod-32
   agreement alone cannot merge distinct exact outputs.
3. **No completed scaling series exists.** With N=64 timed out, neither total
   work, new macrocell population, repeated causal coverage, retention, nor
   effective exponents can establish linear or sublinear growth. N=16…1024 must
   complete with acceleration disabled before such a claim is possible.
4. **The five-minute suite gate is unmet.** The serial run timed out and its
   failures were migrated after the recorded fingerprint. A fresh frozen-tree
   run must pass completely in under 300 seconds.

The semantic scratch issues found during review were repaired after the serial
checkpoint. Admissibility construction now uses a bottom-up two-threshold
`O(bits)` representation with four charged references, and publication rolls
back node, key, and memo insertion if final commit fails. The focused semantic
group and injected commit rollback regression passed. These repairs close the
specific ownership defects; they do not change the unresolved runtime sector
and causal-work blockers above.

## Ownership and acceptance boundary

`ReverseFrobeniusPlan` and its sectors are retained inline with canonical
temporal actions and must remain included in action-container node counts,
payload admission, and allocation reconciliation. Exact source tiles remain
owned by the tile application. A sector death result may remove only that
sector's source coefficient; it cannot erase the application source binding,
the exact output morphism, another live sector, or completed-result semantics.

Completion requires a new frozen fingerprint with a complete serial run under
300 seconds, successful N=16…1024 probes, measured causal-work and retention
envelopes, and runtime counters showing actual sector operations and behavioral
discharge. Compiler plan counts, a leaf-level microbenchmark, and a timed-out
partial suite cannot satisfy those gates.

## Artifacts

- `reverse-three-layer-final-tests.log/json`: focused test gate
- `reverse-three-layer-final-strict.log/json`: strict typing gate
- `final-policy.log/json`: recursive repository policy
- `reverse-three-layer-32.log/json`: N=32 point probe
- `reverse-three-layer-64.log/json`: N=64 timeout
- `serial-pytest.log/json`: incomplete serial suite
- `decimal-compiler-final.log/json`: direct decimal leaf comparison
- `serial-source-fingerprint.txt`: frozen source identity
- `reverse-three-layer-final-validation.log/json`: final 281-test validation
- `reverse-three-layer-final-source-before.txt` and `reverse-three-layer-final-source-after.txt`: matching final fingerprints
- `reverse-three-layer-frozen-64.log/json`: final runtime N=64 timeout
- `reverse-three-layer-final-cold-strict.log/json`: nonincremental strict typing
- `reverse-three-layer-final-policy-2.log/json`: final recursive structural checks
