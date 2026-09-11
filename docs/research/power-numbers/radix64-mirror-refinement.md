# Radix-64 mirror quotient refinement — September 11, 2026

The production arithmetic tile now exposes `folded_fifth_residue()`, backed by
seven radix-64 leaf actions and sixteen canonical additive mirror actions.
The augmented 72-sheet audit reproduces the supplied refinement: the old
five-bit packet has one false positive, while `r5 mod 16` has none. This is an
exact arithmetic API and a bounded support experiment. Zero is not promoted
to an unrestricted support or primality certificate.

## Owned arithmetic and compact composition

For a binary orientation-defect polynomial of width `w >= 6`, write
`c_k = sum_(i+j=k) x_i*x_j`. The demanded output is

```
r5 = c5 + sign*c(w+5)                 (mod 16)
c(w+5) = sum_(u=0..w-7) x[u+6]*x[w-1-u]
sign = -1 for Fermat, +1 for Mersenne
```

The Lucas correction changes only coefficient zero. After dropping six source
bits, the left stream and phase-correct reflected right stream form aligned
six-bit pairs. A final partial pair is zero-padded identically on both sides.
Each pair contributes `popcount(left & right)`, which has exactly seven values.
Composition adds contributions modulo sixteen.

The canonical owner is
`src/number_compiler/arithmetic/polynomials/radix64_mirror.py`:

- `mirror_leaf_action(left, right)` consumes one aligned pair.
- `compose_mirror_pairs(pairs)` consumes a stream without retaining its leaves.
- `MirrorCorrActionID.then` composes canonical translations modulo sixteen.
- `MirrorCorrActionID.power(copies)` repeats an already known spatial action
  using `(action * (copies mod 16)) mod 16`, without expanding source leaves.
- `folded_mirror_residue(low, mirror, sign=...)` consumes the low coefficient
  port and fold sign after mirror reduction.
- `ArithmeticTile.folded_fifth_residue()` validates and aligns an existing
  binary coefficient chart, then calls these same owners.

Only the additive residue belongs to `MirrorCorrActionID`. Source alignment,
fold geometry and the low boundary port remain caller context. Work counters
are separate projection fields. No support sheet, factorization, source word
or temporal history is appended to an action identity. Existing temporal keys
are unchanged. Repetition of a known spatial action is not a theorem that
successive temporal orientation defects induce that same action.

## Reproduced support sheets

The research owner is
`devtools/experiments/power_numbers/radix64_mirror_refinement.py`. It reuses the
existing supplied factor tables and CRT constructor: 60 complete sheets,
four partial-modulus F9 sheets and all eight M53 sheets. F9 is not represented
as a complete factorization. Factor truth is confined to research.

| Control | Sheets | Old false positives | Refined classes | Aliases |
| --- | ---: | ---: | ---: | ---: |
| F4 | 2 | 0 | 2 | 0 |
| F5 | 4 | 0 | 4 | 0 |
| F6 | 4 | 0 | 3 | 1 |
| F7 | 4 | 0 | 4 | 0 |
| F9 partial | 4 | 0 | 4 | 0 |
| M11 | 4 | 0 | 4 | 0 |
| M13 | 2 | 0 | 2 | 0 |
| M17 | 2 | 0 | 2 | 0 |
| M19 | 2 | 0 | 2 | 0 |
| M23 | 4 | 0 | 3 | 1 |
| M29 | 8 | 0 | 6 | 2 |
| M31 | 2 | 0 | 2 | 0 |
| M37 | 4 | 0 | 4 | 0 |
| M43 | 8 | 0 | 8 | 0 |
| M47 | 8 | 0 | 6 | 2 |
| M61 | 2 | 0 | 2 | 0 |
| M53 | 8 | 1 | 7 | 1 |

Refined false positives and false negatives are zero in every row. All 72
projections agree with coefficients from the existing full convolution and
fold. The sixteen possible residues all occur across the corpus. Within-family
collisions remain, so the observer does not reconstruct the support sheet.

The M53 orientation `(+,+,-)` has defect `4573151866567653`, old packet `(0,0)`
and refined residue `13`. Its local depths `(1,0,0)` exclude that orientation
from the common-level temporal filtration. It is tested as a CRT adversary,
not claimed as a state on the actual M53 filtration.

The independent single-coefficient search tests positions **0 through 10** and
power-of-two moduli with **1 through 12 bits**. Within that explicit search,
four bits is minimal and `(position 5, modulus 16)` is the unique minimum.
Each candidate is tested alone, without conjoining the old five-bit packet.
This is not a minimum theorem over every possible coefficient or observer.

## Existing temporal filtrations

| Control | Local depths | True and observed first hole | Levels checked |
| --- | --- | ---: | ---: |
| F4 | (11) | 12 | 14 |
| F5 | (1,1) | 2 | 4 |
| F9 partial | (6,1) | 2 | 9 |
| M11 | (0,0) | 1 | 3 |
| M13 | (11) | 12 | 14 |
| M29 | (0,0,1) | 1 | 4 |

At every tested level, the new zero observation equals the common-depth
full-support predicate and the arithmetic matches the full folded square.
These tests do not add a new powered temporal constructor or establish a
global zero-packet converse.

## Construction cost and reuse boundary

The dense API reads each coefficient once for validation and packing of the
low port, then twice per reflected position. Its exact read count is `3w-12`.
It evaluates `ceil(w/6)` leaf pairs, including the low boundary leaf.

| Width | Coefficient reads | Six-bit leaf pairs | Possible aggregate IDs |
| ---: | ---: | ---: | ---: |
| 16 | 36 | 3 | 16 |
| 32 | 84 | 6 | 16 |
| 64 | 180 | 11 | 16 |
| 128 | 372 | 22 | 16 |
| 512 | 1,524 | 86 | 16 |

The producer accepts an already aligned pair stream, so a compact cylinder
owner can compose child actions directly. Counted repetition of a known action
also avoids re-extraction. These interfaces remove pair provenance from the
aggregate identity, but do not provide an arbitrary candidate-to-paired-cylinder
constructor. The dense adapter remains linear. Sixteen interned enum values
are not evidence of a measured scheduler cache-hit improvement; no such
improvement is claimed by this audit.

## Isabelle scope and promotion boundary

`devtools/proofs/isabelle/temporal_clocks/Radix64_Mirror_Correlation.thy` is
registered in `Temporal_Clock_Jumps`. It proves the exact finite-sum reindexing
at displacement six, the coefficient-five fold projection, the seven-value
Boolean leaf range, the sixteen-element aggregate carrier and its associative
composition. Chunk concatenation preserves the reduced aggregate.
The replicated-sum theorem also proves the counted spatial action formula
`sum(replicate(copies, a)) mod 16 = (a * (copies mod 16)) mod 16`.

The zero source has zero folded output. Conversely, a nonzero output modulo
sixteen implies a nonzero source coefficient. With an independently admitted
orientation-defect chart whose full-support section is zero, this supplies a
sound failure witness. The proof deliberately contains no unrestricted
`r5 == 0 implies full support` theorem, candidate injection theorem or
logarithmic source-lowering bound.

The old arithmetic observer remains available under its explicit two-coefficient
contract and as the M53 negative control. The corrected observer does not change
CLI acceptance or the existing certificate/fallback policy. See the
[previous five-bit report](five-bit-folded-square.md) for that admission history.

## Validation

The focused production, research and CLI selection passes **72 tests in 0.80
seconds**. Coverage includes all 4,096 radix-64 pairs, all 256 binary action
compositions, associativity on all aggregate triples, exhaustive binary widths
six through ten for both fold signs, and all partial-leaf phases. Poison tests
exclude full squaring, source-integer reconstruction and repeated source-leaf
extraction for counted known actions. The eight research tests cover the
72-sheet corpus, bounded minimum search and all six temporal filtrations.

The complete `Temporal_Clock_Jumps` Isabelle session passes in **9.47 seconds**
with a sampled peak of **461,195,568 bytes**, including the explicit no-oracle
dependency check. Repository policy and production-boundary checks pass
**42 tests in 6.82 seconds**; one separately marked validation test is deselected
and is not counted. Strict mypy passes all **1,227 Python files**. Changed-file
Ruff and `git diff --check` pass. These are focused checks, not a full-suite run.

Generated logs and resource reports stay in `/tmp`, outside version control.
