# Current release status — incomplete

Latest checkpoint: [two-sided tile execution](../hashlife/HASHLIFE_TWO_SIDED_CHECKPOINT.md),
source `994fa53f9182`: **4,348 passed, ten unchanged absorption failures, 380.09 s**.
Ruff, strict mypy and structural checks pass. Deep absorption, production cutover
and the serial 300-second release gate remain incomplete. Earlier checkpoints
below are historical evidence.


The sections below are historical, not current production-routing claims.
The [2026-09-05 checkpoint](../hashlife/HASHLIFE_BOUNDARY_QUOTIENT_CHECKPOINT.md) reports
4,324 passes, ten absorption failures, and 386.08 seconds. Deep reverse/Collatz
queries still use continuation execution. Canonical future tile and primitive
quotient component work does not complete the production release.

---

# v0.59.9 release results — bounded temporal HashLife application

Production reverse/add and physical Collatz now keep temporal state in family-specific bounded quotients and keep exact growing digits/tails only as dyadic spatial payload.

## Closed release defects

- raw `SpacetimeBoundary` temporal carrier deleted;
- scalar recursive residual length/depth/anchor identity deleted;
- production reverse/add/Collatz allocate zero generic recursive application nodes;
- construction-order `node_id` removed from core semantic/work traversal keys;
- compiler/query and global/per-index metrics separated;
- reverse/add H=20 carry cut is production state;
- Collatz bounded residue/local phase + symbolic event/affine quotient is production state.

## N=256 representative state

| metric | reverse/add 196 | Collatz 27 |
|---|---:|---:|
| seed tiles | 3 | 5 |
| compiled `F^N` nodes | 45 | 181 |
| bounded state/action classes | 2 / 2 | 3 / 3 |
| generic recursive application nodes | 0 | 0 |
| exact spatial occurrences | 236 | 41 |
| symbolic spatial actions | 10,567 | 122 |
| primitive evaluations | 255 | 42 |
| generic macro entries | 0 | 0 |

Reverse/add temporal closure is complete, but its spatial forcing-action evaluator remains approximately linear and is the remaining HashLife release blocker. Collatz seed 27 saturates on the measured tail; arbitrary-source logarithmic closure is not claimed.

Current targeted validation: **135/135 passing**.
