# v0.53.5 tech-debt cleanup — concise summary

## Duplicate code/state removed

- One shared `two_adic.py` now owns positive/nonzero 2-adic valuation; repeated Collatz/cyclotomic/research helper bodies were removed.
- `InternedEffectNode` is the single two-field hash-consed effect-node carrier used by Collatz and unary quotient arenas.
- `SpecialCompilation` is the single Fermat/Mersenne `(spec, terms)` runtime container; public family spellings are compatibility type aliases.
- `BimachineTransformResult` is the single `(machine, metrics)` transform-result carrier used by composition and minimization.
- The rejected BSGS canonical-coefficient/Taylor transport cache was deleted; only canonical shape identity plus honest absolute-coordinate coefficient lowering remain.
- The superseded one-line `special_lazy_hotpath_probe.py` compatibility wrapper was deleted.

## Audit/tooling cleanup

- `compiler_audit_helpers` caches parsed ASTs and builds its definition index once instead of reparsing every production file for each primitive check.
- The canonical audit includes guards for the new shared 2-adic helpers and shared runtime carriers.
- The Markdown audit report is concise; the exhaustive check map remains in `results/compiler_audit_metrics.json`.

## Documentation cleanup

- Markdown lines: **9,631 -> 4,172** (56.7% reduction).
- Files over 150 lines: **18 -> 0**.
- Long historical/research narratives were replaced by bullet summaries that retain closed results, rejected shortcuts, frontiers, and evidence pointers.
- `README.md` now describes the current architecture and CLI instead of embedding the full version-by-version research history.

## Semantic status

- This release is intended to be behavior-preserving cleanup only.
- BSGS first unseen coefficient/support evaluation remains separately charged; no new polylogarithmic claim is made.
- Collatz genuinely new future normalized frame states remain an open behavioral quotient; no arbitrary-horizon logarithmic claim is made.
- Fermat/Mersenne production remains theorem-lazy with the exact classical Pépin/LL ceiling.
