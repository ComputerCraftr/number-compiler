# Dyadic difference-germ research — condensed summary

## Key findings

- Quadratic left/right germ transport is exact and binary-jumpable for any fixed set of formal symmetric moments.
- Left/right root sign is redundant on the Fermat prime-domain controls: both signs have the same next quadratic-residue status.
- Unweighted moment recurrences are too universal to classify the candidate; they reproduce the same formal branch tree on passing and failing support.
- The useful hidden state is the **local 2-primary depth/support distribution**, not the exponentially branching root tree.
- Quartic/Gaussian reciprocity transcripts and aggregate character vectors do not provide the missing support selector.
- The first Fermat lift has an exact relative-norm formulation; later lifts become fixed Kummer/cyclotomic norm equations.
- Sparse candidate formulas and fixed-trace sections can produce exact positive witnesses on bounded levels without materializing the entire tower.
- Section misses are not negative certificates, so the production API remains fail-closed.
- Current bounded terminal levels are `1,4,11,26` for `F2,F3,F4,F5`; only F2 is decided by the present surface.

## Remaining theorem

- The unresolved classifier is the support-sensitive predicate: every prime ideal supporting `1 - 2*zeta_(2^(n+1))` must split through the required remaining Kummer/cyclotomic tower.
- Evaluating that predicate exactly is itself a Fermat primality test; the quotient removes representation cost but does not yet provide a cheaper injector.
- Global Frobenius values and finite aggregate character vectors remain rejected unless they preserve local support.

## Evidence

- Research implementation: `research/dyadic_difference_germ*.py`.
- Regression tests: `tests/test_dyadic_difference_germ*.py` and neighboring two-primary/special-number tests.
- Production behavior remains fail-closed; no research-only support oracle is reachable from the sequence compiler.
