# Cylinder-ray restoration validation, September 12

Independent decimal-digit replay of 20,000 transitions from 196 reproduced the
supplied counts exactly. The final number has 8,296 digits.

| Observation | Count |
| --- | ---: |
| Root CONST0 / no growth | 11,707 |
| Root CONST1 / growth | 8,293 |
| Root ID | 0 |
| No growth with a real carry | 11,707 |
| No growth without a real carry | 0 |
| Growth first mismatch E0 | 8,077 |
| Growth first mismatch E1 | 186 |
| Growth first mismatch E2 | 30 |
| Palindromes | 0 |

The deepest shells `(S0,S1,S2)` and counts are `(11,0,4):4`, `(11,0,5):4`,
`(11,0,6):1`, `(11,0,7):5`, `(11,0,9):3`, `(11,0,15):3`, `(11,0,16):8`,
`(11,0,17):2`.

Reproduce with:

```
python3 -m devtools.proofs.reverse_add_cylinder_ray_probe --steps 20000 \
  --output results/current/cylinder-ray-restoration-2026-09-12/196-ray.json
```

The JSON is generated evidence and stays local under the repository's existing
ignore policy. The audit deliberately uses an independent direct digit loop;
it is not called by production and is not evidence of an all-future theorem.

The restored production étale probe reproduces M11→23, M23→47, M83→167,
M131→263 without factor enumeration. Public classification of M131 with
`--allow-classical-ceiling --factor --format json` returns composite, factor 263,
129 classical squarings and 261 additional quadratic-ring multiplications.

The helix regression instruments actual root evaluations: all 64 child-digit
queries use one base-root evaluation, and centered digit queries use none.
Results are checked against independent modular inverse powers at q=6,7,12,18,30.

## Test outcome

- Final focused integration and repository-policy run: **152 passed**.
- Explicit terminal-étale and classical-ceiling validation selection: **14 passed**.
- Full ordinary suite: **4,668 passed, 4 failed, 1,254 deselected** (309 seconds).
  All four failures also reproduce with source and tests extracted from unchanged
  HEAD `92afb957c54689fc004982a1a0f4bb132a18697a`:
  two `test_identical_warm_point_bypasses_evaluator_and_retains_one_response`
  parameter cases disagree with existing port-validation accounting, and two
  `test_primitive_wiring_rejects_uncertified_automorphism_before_lookup` cases
  reach the memo before the expected validation rejection. These existing
  scheduler assertions were not weakened or changed by this restoration.
- `mypy src tests devtools`: **1,234 source files passed**.
- `ruff check src tests devtools` and `git diff --check`: passed.
  The broader `ruff check .` also sees three existing E701 violations in
  `results/current/cli-clock-deck-2026-09-10/measurement.py`.

The full run preceded the final extra cache/CLI/deck regressions; the final
152-test run includes those additions and all final edits to affected paths.

## Isabelle follow-up

The `Etale_Primary_Carry` session builds with Isabelle2025-2 and
`quick_and_dirty=false`. Each new theory rejects oracle dependencies in the
exported theorems. The formalization covers exact carry/jet algebra, the two
all-local primality thresholds, factor output from a nontrivial quadratic
root, and the odd-width Mersenne zero-section through the actual folded-square
coefficient word and canonical normalization. See the
[theorem and premise record](../../../docs/research/power-numbers/etale-isabelle-proof.md).

The user's clarification identified the 320 rows as factor-backed root-variety
orientations followed by one family square. There was no terminal-clock
construction or temporal admission rule. No terminal extractor or Fermat
separation theorem is claimed by this follow-up.

The production follow-up exposes the one-step key on `ArithmeticTile`, separates
its input sign bit from the signed output chart, and adds checked root-to-factor
output. The final affected-path selection has **109 passing tests**, including
independent exhaustive small fold/carry checks, odd-width Mersenne root controls,
nontrivial root factor output, tile regressions, public factor classification,
helix/palindrome optimizations, and repository policy. Ruff and mypy remain clean.
The earlier full-suite baseline failures above are unchanged; that full run was
not repeated after this formalization follow-up.
