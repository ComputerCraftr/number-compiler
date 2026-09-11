# Carry-domain leaf reuse checkpoint

Status: **incomplete; the production HashLife cutover is not implemented**.

Frozen source:
`e7586f01a01659fbc703f4eedc54a1eb19ca8da5f64e141199e54ce00201fc6e`.
The earlier two-sided checkpoint and historical measurements remain unchanged.

## Retained changes

- Carry composition uses the exact reset law: `after ∘ before` is `before`
  when `after` is identity, otherwise `after`. It no longer evaluates both
  Boolean inputs to rediscover a known monoid member.
- Carry APIs reject noninteger numeric aliases and non-`CarryFn` operands.
  Exhaustive composition-order, associativity, identity and alias tests cover
  the change. A poisoned evaluator verifies composition executes no inputs.
- Direct and fused primitive leaf compilation now probe the same semantic
  `(kernel ID, signature ID, symbol)` binding before constructing functions.
  The existing adapter leaf store owns both this binding and the reverse
  interface admission. No executor, occurrence cache or tile arena was added.
- The key contains a bounded kernel literal, not a coordinate or producing
  action. The value is the complete local interface, including its output law.
  Equal carry exits alone are not used as output equivalence.
- Leaf reuse survives source-tile retirement. Cold binding reservations happen
  before kernel work, and local binding publication failures release their
  reservations. This does **not** establish transactional rollback across all
  semantic child arenas after a later construction failure.
- Independent inventory checks both directions of the leaf store, rejects
  orphan reverse admissions, and validates the admitted kernel/signature and
  full port declaration without executing semantic functions.
- Schema 6 forwards separate real leaf-product requests, early hits,
  evaluations, publications and late aliases. Source-interface bindings remain
  separately counted. Reporting remains read-only.

## Validation

The final serial unfiltered run produced **4,389 passed, ten failed, no skipped
tests or errors**. Pytest reports **513.18 seconds**; the JUnit suite reports
513.44 seconds and the enclosing command took 515.53 seconds. Source
fingerprints before and after match. The five-minute gate fails.

- Ruff passes over `src`, `tests` and `bench`.
- Strict mypy passes over 608 source files.
- Recursive structural, package, source-size and recursion checks pass in the
  full run.
- All ten failures remain in `tests/test_powered_output_absorption.py`; that
  file remains byte-for-byte unchanged, SHA-256
  `e26bd38d306b0a3165beceb9374250f1a7168d010f0f66f4a72f54c19817745a`.
- The fixed five-process radix regression passes: cold median 0.0001423 seconds,
  repeat median 0.0000762 seconds. This is narrow regression evidence, not
  evidence of powered radix cutover.

Evidence:

- `results/carry_leaf_reuse_e7586f01a016.json`, `.xml` and `.log`
- `results/field_carry_leaf_e7586f01a016.json`
- `results/radix_carry_leaf_e7586f01a016.json`

The earlier `carry_leaf_reuse_cbadc175359f` run was interrupted to repair the
orphan-admission audit finding. Its record explicitly marks the run incomplete;
its elapsed duration is not a passing full-suite measurement.

## Cold execution remains red

Acceleration is disabled in the fresh-process field probes.

| N | Reverse 196 cold seconds | Collatz 27 cold seconds |
|---|---:|---:|
| 16 | 0.1643 | 0.1713 |
| 32 | 0.2048 | 0.1724 |
| 64 | 0.3877 | 0.2063 |
| 128 | 1.0213 | 0.3194 |
| 256 | 3.4203 | 0.5553 |
| 512 | 13.3601 | 0.9328 |
| 1024 | 35-second watchdog timeout | 1.9403 |

Public deep queries still report zero canonical tile nodes and zero absorbed
temporal span. Reverse N=512 still performs 164,720 higher continuation
requests and 2,504,109 internal operations, retaining 1,237,159 ledger entries
and 332,255 nodes: exactly the preceding checkpoint's counts. These changes
therefore establish no improvement to that algorithm or its growth envelope.

The arbitrary-depth composed fused transfer, real branch-dependent reverse
algebra, production family/radix routing, complete symmetry normalization and
cross-arena atomic publication remain unfinished. No primitive depth guard was
removed, no retired evaluator was renamed, and no fixture, trace, budget or
watchdog was weakened to conceal those missing pieces.
