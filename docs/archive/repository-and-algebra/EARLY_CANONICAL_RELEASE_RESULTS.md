# Early-canonical powered-operator release results

This pass moves the remaining late cache hits to canonical semantic representations before
powered composition can expand their Cartesian members.

## Completed production changes

1. **Quotient-before-determinize T^2 compiler**
   - Primitive witnesses are refined by exact transition/output congruence first.
   - Determinization operates on semantic witness classes, not raw witness triples.
   - Exact T^2 reaches 688 left / 91 right states with **zero downstream state merges**.

2. **Canonical output relation from generator boxes**
   - Compatible semantic witness classes emit labeled Cartesian selector boxes.
   - Same-label regions are normalized before the output decision DAG is built.
   - T^2 no longer scans the 1,377,376 possible `(left,symbol,right)` contexts.
   - Only 87,235 primitive compatibility/output probes are required (~15.8x fewer).
   - The authoritative T^2 output relation is 310 MTDD internal nodes; tuple cache size is zero.

3. **MTDD regions are reusable compiler primitives**
   - `CanonicalOutputRelation.iter_boxes()` exposes exact disjoint semantic regions without
     evaluating Cartesian leaves.
   - Grouped cascade transitions intersect those regions directly with dependency boxes and
     apply deterministic DFA images as bitsets.
   - This removes the old per-left/per-right state loops from the T^4 cascade kernel.

4. **No raw primitive fallback beyond T^2**
   - `ResidualPowerTable` may use the exact quotient-first primitive compiler for T^2.
   - T^4 and higher are compiled only through the canonical grouped dependency cascade.
   - If that cascade does not close within the complexity budget, powering fails closed.
   - There is deliberately no fallback to raw Cartesian primitive triples or a per-context
     output resolver/cache.

5. **Regression tests**
   - A monkey-patched adversarial test proves T^4 powering does not call the raw primitive
     composer.
   - Exact sampled reconstruction from MTDD boxes proves the canonical output regions agree
     with the T^2 bimachine and leave the tuple cache empty.

## Exact decimal measurements

### T^1 / T^2

- T^1: **50 left / 6 right states** after exact minimization.
- T^2: **688 left / 91 right states**.
- primitive T^2 witnesses: 2,609 left / 378 right -> 1,857 / 150 semantic classes.
- possible final T^2 output contexts: 1,377,376.
- primitive compatibility/output probes: **87,235**.
- labeled semantic generator boxes: **40,111**.
- normalized canonical output regions: **3,485**.
- authoritative output MTDD: **310 internal nodes**.
- per-context output-cache entries: **0**.
- downstream exact minimizer late merges: **0 / 0**.

### T^4 canonical-cascade probe

With a 500-state cap on each context side:

- left: 500 canonical relation states, 985 dependency nodes, 1,592 dependency groups,
  35,955 description bits, representing 44,412 primitive tuples in about 0.18 s;
- right: 500 canonical relation states, 10,830 dependency nodes, 27,286 dependency groups,
  3,032,599 description bits, representing 342,315 primitive tuples in about 4.5 s.

The cap is reached before closure.  Importantly, this is now **canonical relation-state
complexity**, not the former >100k raw primitive-triple construction.

## Verification

- **37 tests pass**.
- `selftest.py` passes.
- `compileall` passes.
- no Cartesian residual output grid is present;
- no raw primitive-triple fallback is reachable from the production T^4 power-table path.

## Full-J release status

The engineering regression requested by this pass is closed: semantic equivalences that are
known at the witness/output-region level are now canonical before their Cartesian members are
generated, and higher powers cannot fall back to the old late-cache representation.

The full exact `J_0/J_1 : FormulaRoot -> FormulaRoot` backend is still **not certified**.
The remaining blocker is that the exact T^4 canonical dependency relation itself still has
many distinct sections, especially on the right/look-ahead factor.  The release gate remains
fail-closed until those canonical sections admit a bit-length-polynomial powered quotient.
