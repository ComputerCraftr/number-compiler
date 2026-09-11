# Residue-refined bend / Fitting batch research — condensed summary

## Key findings

- A point bend is easy: one candidate-ring GCD detects whether a progression value is a nonunit.
- The bend locus has an exact Fitting/annihilator interpretation over the composite candidate ring.
- Fast factor-free multipoint evaluation batches many bend tests without first factoring the candidate.
- With Karatsuba multiplication the asymptotic batch bound is roughly `O(l^0.7925 log l)`: genuinely sublinear in the window length, but still far from polylogarithmic.
- The current Python implementation has large addition/constants and is slower than the direct linear product on the bounded release controls; this result is asymptotic research, not a production speed claim.
- Canonical progression-product morphisms now separate predictable algebraic shape from absolute coordinate lowering, so repeated structural work is shared early.
- Once multipoint support values exist, v0.53.7 uses a balanced support-product tree for logarithmic GCD localization; support-only observers stop after one final GCD and skip the linear direct differential.

## Frontier

- Collapse the special-form bend/support aggregate to polylogarithmic total work, not merely a smaller descriptor or one-level BSGS batch.
- Production source projection remains unresolved and does not call this research path as a theorem fallback.
