# Arithmetic Stokes / ghost-flux research — condensed summary

## Closed results

- The arithmetic line integral / Wilson-line product identity is exact.
- The unit connection is flat, but flat boundary data does not determine interior divisor support.
- Ordinary complex analysis misses the arithmetic nonunit singularity.
- Rising-factorial/Gamma notation is algebraically equivalent to the path product; it is not a cheaper evaluator by itself.
- Finite-difference/Newton boundary jets require order growing with the interval and therefore do not give a bounded exact state.
- Linear resultant/norm formulations are exact but compute the same product information.
- Fermat power-of-two binomial recursion still exposes full branch growth rather than a constant-rank collapse.
- Exact delta/Fourier support is dense on the controls.
- Baby/giant evaluation reduces explicit state to roughly square-root scale but is not polylogarithmic total work.

## Rejected shortcuts

- `unit boundary -> interior divisor flux` from a bounded local state.
- Bounded-order exact Newton jet.
- Treating `Gamma`/resultant notation as a new algorithm.
- Sparse exact Fourier support.
- Calling a square-root-state baby/giant evaluator a release-scale theorem.

## Remaining target

- Evaluate the exact divisor/support flux of a compact affine interval descriptor `(N,C,a,l)` with polylogarithmic state **and** charged work, without hidden factorial, multipoint, factorization, CRT, Pépin, or LL work.
- Production remains unchanged and fail-closed.
