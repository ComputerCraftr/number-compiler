# v0.53.7 digit-generation performance — concise results

## Closed eager-work bugs

- `ProjectedNumberTerm.digit(i)` evaluates one formula/source digit without calling `materialize_values()` on the complete word.
- Fermat digits are direct sparse-descriptor queries: only positions `0` and `2^n` are `1`.
- Mersenne digits are direct interval-descriptor queries: every position `0 <= i < p` is `1`.
- `NumberCompiler.project_digit(...)` exposes the single-coordinate path without requiring a materialized integer.
- Reverse/add growth now has a first-class `ReverseAddGrowthState(boundary_offset, relation)` observer.
- The 196 growth/length branch uses only the radial boundary order and sign; it does not construct a carry field or successor formula.

## BSGS support/GCD extraction

- The final unit/nonunit decision uses one support GCD and stops there when no factor witness is requested.
- `FULL` support no longer forces proper-factor extraction for digit/theorem observers that only need the support bit.
- Proper-factor / first-bend localization uses a balanced modular support-product tree instead of a linear scan over all baby blocks.
- A small constant prefix preserves the common early-bend fast path; the remaining search is logarithmic in the number of support leaves.
- The generic support tree lives in `research/support_product_tree.py`; the BSGS evaluator no longer carries duplicate locator machinery.
- Production-like memoized support/bend packets disable the bounded linear direct-interval differential. Direct replay remains available only to explicit audit calls.

## Character handling

- No character phase is used to prune a composite arithmetic-progression slot before support is known; that would be unsound.
- A local Fermat/Mersenne Dirichlet/Jacobi phase is attached only after the first supported slot has emitted an exact local GCD packet.
- Aggregate character cancellation is therefore not reintroduced into the support decision.

## Reproducible controls

- F20: arbitrary binary digits, including the endpoint at position `1,048,576`, are returned without full-word materialization.
- M100000: digit `99,999` is returned directly from the source descriptor.
- Reverse/add seed 196: forcing state is `(boundary_offset=0, relation=-1, growth=0)` without carry/successor construction.
- M29 support-only window: one final support GCD, zero split-descent GCDs, and no linear direct-control replay.
- F6 span 1200: first bend is slot `1071`, GCD `274177`; product-tree localization uses 12 block + 13 leaf GCD probes versus an old 69-entry block/atom linear upper bound.

## Complexity boundary

- The GCD **localization** phase is no longer linear in the BSGS support leaves.
- Repeated support observers reuse the memoized fixed-window packet.
- The first unseen BSGS polynomial/multipoint evaluation remains sublinear Strassen/Karatsuba-scale, not polylogarithmic.
- Raw Fermat/Mersenne digit generation never enters BSGS or primality machinery at all.

See `results/digit_generation_performance_metrics.json` for machine-readable measurements.
