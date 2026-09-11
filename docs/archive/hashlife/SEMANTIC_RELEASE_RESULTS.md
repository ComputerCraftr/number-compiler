# Semantic release-candidate results

This directory is the finished hardened release candidate for the canonical formula-state
reverse/add implementation.

## Completed release-blocker work

- Production semantic state is `FormulaRoot(planes)` only.
- Powered jumps are hard-guarded against successor replay, growth/carry queries,
  point evaluation, materialization, and summary synthesis by positional probing.
- Constant-size `BlockSummary` metadata is compiler-only and may be read only when already
  propagated.
- The Cartesian `CompactOutputGrid` residual minimizer has been deleted.
- Exact output residuals are represented once as a reduced multi-terminal decision DAG;
  canonical cofactors drive Myhill--Nerode refinement.
- Tropical/projective signatures are filters only; exact residual identity is mandatory.
- Exact bimachine projection over balanced hash-consed SLP/RLSLP nodes is implemented
  without decompressing the input word.
- Cascade, residual-decision, SLP, tropical, and formula-DAG complexity are all charged by
  the release certification gate.
- Proper left/right earliest-output (LCP/output-pushing) minimization was tested exactly;
  it did not reduce T1/T2 state counts and remains research-only.

## Verified metrics

- Tests: 32 passing.
- `selftest.py`: pass.
- `compileall`: pass.
- Runtime/compiler source: 17 modules, 3,685 lines; largest file 619 lines.
- Exact T1: 86/12 -> 50/6 left/right states.
- Exact T2: 690/91 -> 688/91 left/right states.
- T2 has 1,381,380 possible output contexts but its exact output relation factors to
  2,310 MTDD decision nodes / 21,342 dependency groups.
- No Cartesian residual output grid remains in production code.

## Full-J release gate

The exact full-state `J_0/J_1 : FormulaRoot -> FormulaRoot` backend is still not known.
`require_full_jump_release()` therefore intentionally fails closed.  The remaining blocker
is powered nonlinear residual/operator-section complexity, not unfinished state plumbing,
position scanning, output-table materialization, or an unimplemented minimizer.
