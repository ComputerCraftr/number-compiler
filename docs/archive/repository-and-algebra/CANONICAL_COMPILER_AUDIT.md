# Canonical compiler audit — concise summary

## Result

- Overall: **PASS**.
- Checks passed: **133/133**.
- Production modules scanned: **111**.
- Modules reachable from `sequence_compiler`: **63**.
- The exhaustive check map and primitive-definition counts are stored in `results/compiler_audit_metrics.json`; Markdown does not duplicate that table.

## Canonical ownership

- Shared binary powering definitions: `['morphism_core.py:89']`.
- Shared affine cocycle definitions: `['morphism_core.py:140']`.
- Shared dyadic-affine cocycle definitions: `['morphism_core.py:176']`.
- Shared quadratic-power definitions: `['morphism_core.py:235']`.
- Shared positive/nonzero 2-adic valuation definitions: `['two_adic.py:11']` / `['two_adic.py:19']`.
- Shared interned effect-node definitions: `['morphism_core.py:29']`.
- Shared special compilation container: `['sequence_types.py:322']`.
- Shared bimachine transform result: `['transducer.py:129']`.
- Canonical source-digit cyclotomic blocks: `['digit_cyclotomic.py:51']`.
- Canonical Collatz rational-root germs: `['collatz_frame.py:175']`.
- Canonical quotient synthesizers: `['quotient_synthesis.py:504']`.
- Numeric `node_id` values are arena-local only; cross-operator/state caches use semantic type-tagged keys.

## Legacy/duplicate guards

- Legacy special power effects/nodes/arenas: `[]` / `[]` / `[]`.
- Legacy quadratic-unit state: `[]`.
- Legacy Fermat/Mersenne square-field states: `[]` / `[]`.
- Legacy special order-depth / cyclotomic-character states: `[]` / `[]`.
- Legacy `_bits` helpers: `[]`.

## Failures

- None.

## Reproduce

- Run `PYTHONPATH=src:. python bench/compiler_audit.py`.
- Inspect `results/compiler_audit_metrics.json` for every individual check and count.
