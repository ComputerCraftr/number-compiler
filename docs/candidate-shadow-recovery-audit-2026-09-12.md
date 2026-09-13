# Candidate shadow recovery audit

> Latest transverse-germ correction: the requested semantic target is now
> explicit: `H=product(1+C*m) mod N` through the admitted square-root window,
> with **prime iff gcd(H,N)=1**. Its enumerative research owner already exists.
> The remaining construction gap is the compact cylinder-to-transverse-support
> pullback, not an undefined primality formula. The `E` packet and conditional
> theorem audited below have different gcd polarity and are auxiliary; they
> must not be substituted for the restored `H` criterion. See the
> [current P0 ledger](cylinder-p0-release-gates-2026-09-12.md).

**Release remains blocked.** Production has the local quotient, the carry-jet
observer, and the all-local-to-primality theorem. It does not have the
candidate-derived support publisher connecting those objects.

The restored H criterion is now checked in Isabelle:
[`Transverse_Frobenius_Holonomy.thy`](../devtools/proofs/isabelle/etale/Transverse_Frobenius_Holonomy.thy)
proves the exact indexed-product prime-bit criteria for Fermat n>=2 and odd
prime Mersenne exponents, with family progression admission discharged by
[`Special_Factor_Progressions.thy`](../devtools/proofs/isabelle/etale/Special_Factor_Progressions.thy).
It also proves the nonzero ring annihilator `N div gcd(N,H)` for nonunit H.
The combined session passes with oracle-dependency checks. No compact
evaluator, same-owner runtime refinement or construction-cost bound follows
from these semantic theorems alone.

## Exact production boundary

[`terminal_threshold_probe`](../src/number_compiler/sequences/power_numbers/terminal_threshold.py)
now builds
[`CompactTransverseHolonomyPullback`](../src/number_compiler/sequences/power_numbers/transverse_pullback.py).
Its `SpecialTransverseWindow` is the exact symbolic progression
`q_m=1+C*m` below the square-root frontier.  Window membership is decided from
the bit length of `q_m^2`, so constructing the request does not materialize the
candidate or enumerate the window.  The descriptor cannot accept a caller
supplied unit bit or annihilator and records zero atom evaluations, zero ring
multiplications, and zero factor enumeration.  Until an issued evaluator is
proved, the terminal probe returns `UNKNOWN` with method
`transverse-holonomy-pullback-unresolved`.

The older [`build_special_germ_plan`](../src/number_compiler/sequences/power_numbers/germ.py)
and its `SquareTileAction` remain local algebra.  They no longer own the live
terminal query, because an unconstrained zero-section defect has the opposite
gcd polarity from the transverse holonomy and cannot supply its unit bit.

## Adversarial constructor audit for the restored target

The canonical `special_transverse_jet.py` has the exact interval law
`B(a,l+r)=B(a,l)*B(a+l,r) mod N`. This costs one multiplication **after both
children have been constructed**. Its current constructor evaluates W atoms
and performs W-1 multiplications. Product-tree depth does not bound that work.

For the symbolic polynomial `P_l(X)=product(X+C*j, j=0..l-1)`, the actual
target is `H=P_W(1+C)`, and doubling satisfies
`P_(2l)(X)=P_l(X)*P_l(X+C*l)`. Evaluating one child at one point does not
produce the translated sibling evaluation. A one-slot rolling formula can
cancel the outgoing term only when it is a unit; this cancellation fails at
the nonunit support being sought. An equal-span sibling shift has no overlap.

No current production owner implements a charged compact evaluator for this
translated polynomial action or directly for its unit/annihilator. Fixed
primary carry emissions, folded square-word coefficients and supplied defect
gcds do not define that operation. An explicit coefficient vector for P_l has
l+1 coefficients; it is not the requested compact implementation either.
These are limits of the current constructors, not an impossibility theorem or
a counterexample to the full transverse germ. The release proof must exhibit
the compact action, its source admission, its translation/composition law, and
the work and retained-state bound for the implementation used by the CLI.

## Auxiliary defect route, retained for comparison

For a local prime component, write

```text
q = epsilon + m*k,       rho = k mod 2^r.
```

[`folded_x_coefficient_from_stride_residue`](../src/number_compiler/sequences/power_numbers/frobenius_chunk.py)
proves the local folded coefficient in
`X^(m*2^(r-1))+1` is `+1` exactly when `rho=0`, `-1` at the top residue, and
zero otherwise. The normalized local defect is `folded_coefficient-1`.
[`SpecialFrobeniusDefectPacket`](../src/number_compiler/sequences/power_numbers/frobenius_chunk.py)
then classifies an already constructed candidate-ring defect `E` by
`gcd(E,N)`: `N` is all-pass, `1` is all-fail, and a proper gcd is split support.

The smallest unresolved production chunks are:

| candidate | start | span | base stride v2 | required v2 |
| --- | ---: | ---: | ---: | ---: |
| F4 | 2 | 2 | 6 | 8 |
| F5 | 2 | 9 | 7 | 16 |
| M11 | 1 | 2 | 2 | 4 |
| M13 | 1 | 3 | 2 | 5 |

The auxiliary defect bridge would require one source-bound `E_N` without
factoring the candidate and, for every prime component `q | N`,

```text
E_N mod q = 0    iff    rho_q = 0,
E_N mod q is a unit otherwise.
```

The primary production target is now more direct: evaluate the unit or
annihilator of `H=product(q_m) mod N` from the compact transverse pullback,
without expanding the symbolic window.  It must additionally prove that this
powered construction and the production mod-16 shadow observation refine the
same support-bearing action.  This is the unavailable source-to-terminal
theorem.

## Why the current carry jet cannot fill the gap

[`ArithmeticTile.step_with_primary_carry_jet`](../src/number_compiler/arithmetic/polynomials/arithmetic_tile.py)
observes one square or trace-square of an already supplied input word.
[`observe_etale_root`](../src/number_compiler/api/cylinder_observation.py)
requires a supplied `D` and checks `D*(D+2)=0 mod N` before constructing that
key. It does not derive `D` from the terminal clock.

The actual zero input demonstrates the missing binding. For Fermat widths 16
and 32, corresponding to F4 and F5, the production observer returns the same
key `(deck=0,seam=0,jet=(0,0))`. F4 is prime and F5 is composite. Thus the
existing supplied-root key is not itself a candidate primality selector. This
does not refute a future terminal publisher; it proves that its source binding
is a necessary premise.

The factor-backed 320-row experiment constructs every CRT orientation first
and then applies the one-step observer. Its results test separation after the
missing section has been supplied. They do not implement that section.

## Research audit

[`terminal_frobenius_chunk.py`](../devtools/experiments/power_numbers/terminal_frobenius_chunk.py)
constructs global defect controls only from complete supplied factorizations
and marks them as truth audits. [`special_germ_descent.py`](../devtools/experiments/power_numbers/special_germ_descent.py)
shows why the polynomial germ does not manufacture orientation: the invariant
algebra factors through `P(e)=e*(e+2)`, while the anti-invariant coordinate is
`e+1` with `(e+1)^2=P(e)+1`, requiring the missing quadratic section.
[`terminal_divisor_norm.py`](../devtools/experiments/power_numbers/terminal_divisor_norm.py)
records the same algorithmic boundary for divisor norms: aggregate characters
can cancel and fixed linear Fitting data is insensitive to the semilinear
Frobenius support.

No recurrence oracle, factor table, supplied CRT orientation, zero-root choice,
or unproved assertion may replace this constructor. Until it exists and its
refinement theorem is checked, F4, F5, M11, and M13 remain executable failing
release-gate cases rather than green production classifications.

The canonical research differential evaluates the whole progression and
charges its exact cost.  It returns F4 `CLEAR` after 3 atoms and 2 products,
F5 `SPLIT(641)` after 511 atoms and 510 products, M11 `SPLIT(23)` after 2 atoms
and 1 product, and M13 `CLEAR` after 3 atoms and 2 products.  M29 is the
adversarial full-gcd case: 399 atoms contain factors 233, 1103, and 2089, so
the root gcd equals `N=536870911`; interval descent is required before printing
the proper factor 233.  These are exact semantic controls, not production work
or evidence of logarithmic construction.

Direct certificate APIs now reject candidate sizes beyond an explicit bit
budget before lowering a Fermat dyadic width or entering an exponent predicate.
For an admitted Mersenne exponent above the deterministic 64-bit predicate,
only immediate 2/3 factors are decided; all other cases return
`exponent-gate-budget` without unbounded factor search.

## Checked conditional production-packet theorem

[`Special_Frobenius_Defect_Bridge.thy`](../devtools/proofs/isabelle/etale/Special_Frobenius_Defect_Bridge.thy)
now proves the Fermat and Mersenne implications from the local support
invariant above to `prime N iff N divides E iff gcd(N,E)=N`. A proper gcd also
prints an exact factor and cofactor. The theory passed `Etale_Primary_Carry`
with oracle checks enabled. The constructor and its local refinement remain
explicit premises to discharge; this conditional bridge is not full coverage.

[`Mersenne_Zero_Key_Counterexample.thy`](../devtools/proofs/isabelle/etale/Mersenne_Zero_Key_Counterexample.thy)
separately proves the exact M11 cyclic normalization and numeric zero-root key
`(False,-1,(14,5))` on composite 2047. It addresses only the missing logical
binding, not the correctness of any candidate-derived terminal publisher.

The theorem parameters are `B=2^(2^(n-1))` for Fermat indices `n>=1`, and
`C=2^((p-1)/2)` for odd Mersenne exponents `p>=3`. The exceptional F0/M2 small
cases remain explicit production decisions. These parameter identities do not
supply the defect or its local support invariant.
