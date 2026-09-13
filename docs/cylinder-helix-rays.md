# Recursive 196 cylinders and the Collatz clock helix

The September 12 research distinguishes reusable cylinder actions from exact
source occurrences. Growth and finite mirror tests are output demands on an
occurrence, not replacement temporal states. The production additions follow
that boundary.

## The observed 196 safety tube

Write `X_n=(phase_n,C_n[O_n])` for the recursive cylinder occurrence and
`X_(n+1)=J(X_n)`. An independent 20,000-transition replay in this restoration matches the supplied
run exactly: root carry responses
11,707 CONST0, 8,293 CONST1, and zero ID. Every no-growth point has a real carry.
Of the growth targets, the first failed shifted target-mirror comparison is E0
8,077 times, E1 186 times, and E2 30 times. None survives all three comparisons. See the [reproduction record](../results/current/cylinder-ray-restoration-2026-09-12/README.md).

The no-growth exclusion has a direct proof. Let the symmetric source pair field
be s, incoming carries c_i in {0,1}, c_0=c_L=0, and normalized digits
`r_i=s_i+c_i-b*c_(i+1)`. If r were symmetric, subtraction at mirrored positions
would give

```
c_i-c_(L-1-i) = b*(c_(i+1)-c_(L-i)).
```

The left side is in {-1,0,1}; for b>=2 this forces both sides to zero.
Combining the two equalities propagates c_0=0 through every carry. Thus a real
carry with no final growth excludes a palindrome. If there is no carry, r=s is
symmetric. With growth, the target has width L+1 and the comparison must shift
to that target midpoint.

The candidate finite safety predicate is therefore:

```
no growth: AnyCarry
   growth: not(E0 and E1 and E2).
```

In the 30 reported deepest growth cases, S0=11 and S1=0. Surviving E2 would
require S2 in {0,1,10,11}, whereas the observed S2 values are
{4,5,6,7,9,15,16,17}. These are finite observations, not universal constraints.
The supplied flat-shell closure has 20,970 states, including 1,870 not certified
by the safety predicate. Those closure counts have not been independently
reconstructed here. They prevent treating the outer shell and a finite middle
carry label as a proved successor state.

The all-future proof target is an invariant subset of the safe recursive
occurrences, containing X196 and closed under J, equivalently membership in
`nu R.{X : Safe(X) and J(X) in R}`. Defining that greatest fixed point does not
prove membership. Safety alone has not been proved inductive.

Production now provides `next_result_is_palindrome(arena,pair_root,spec)` on the
existing symmetric pair occurrence interface. No-growth queries use the carry
exclusion before constructing target digit formulas; growth queries stop at the
first exact shifted target-mirror mismatch. A surviving shell continues with
full exact comparison. `ReverseAddPoweredTerm.is_palindrome()` requests only
necessary mirrored output digits through the production point projector. These
are output-demand optimizations; they do not skip unproved temporal steps or
claim that 196 never reaches a palindrome. Large no-growth queries may still
need an interior search for AnyCarry; a compact recursive pullback is not claimed.

## Universal inverse-three clock and its source-dependent sampling

For accelerated odd Collatz `x_(n+1)=(3*x_n+1)/2^k`, normalize
`W_n=3^(-n)*x_n`. With `rho_t=-3^(-t)` in the 2-adic integers,

```
W_n = rho_(n+1) + 2^k * W_(n+1).
```

At q>=3 bits, the order of 3 modulo 2^q is exactly `P_q=2^(q-2)`.
At radix-64 depth d, time has the mixed-radix expansion
`t=sigma+16*(a0+64*a1+...)`, with sigma in 0..15 and ai in 0..63.
Only sigma and a0 through a_(d-2) affect the finite root at precision 64^d.
For positive t, the exact finite series is

```
rho_t mod 64^d = (-1)^(t+1) * sum(j=0..3d-1) binom(t+j-1,j)*4^j mod 64^d.
```

It follows from `3=-(1-4)` and the negative binomial expansion. This describes
the clock, not the unknown future valuations of a positive integer.

The radix-64 helix identity, already implemented before this restoration, is

```
R_(q+6)(t+a*P_q) = R_(q+6)(t)*(1+lambda*a*2^q) mod 2^(q+6)
lambda = 35 at q=6; lambda = 3 at q>=7.
```

The centered next digit is `lambda*a*(R_q(t) mod 64) mod 64`, a bijection of all
64 digits because the slope is odd. `InverseThreeClock.centered_lift_digit`
now exposes that calculation without a wide root. Repeated absolute child-digit
queries reuse one cached base root per clock, replacing 64 identical base-root
calculations with one when all children are demanded. The cache is derived
metadata and is excluded from clock equality and its canonical key. It does not
retain an itinerary or change any source-dependent valuation guard.

For future valuations k_j>=1, let K0=0 and Kj=sum(i=1..j) k_i. Substitution gives

```
W0 = sum(j=1..N) 2^K_(j-1)*rho_j + 2^K_N*W_N
   = -sum(j>=1) 2^K_(j-1)/3^j                      in Z_2.
```

The tail tends to zero since W_N is 2-adically integral and K_N tends to infinity.
The accelerated fixed point 1 has constant gaps k_j=2. A periodic valuation word
of length m and total K forces the rational cycle candidate

```
x = sum(j=1..m) 2^K_(j-1)*3^(m-j) / (2^K-3^m).
```

An integral positive candidate and its exact valuation guards must still be
checked. The clock identity proves no eventual gap-2 theorem. Universal Collatz
convergence would require a global argument about the positive-integer sampling
rays; finite phase repetition alone cannot provide it.

The new tests compare every child of several q-bit clocks against independent
modular inverse powers, count wide-root calls, verify cache identity, check the
palindrome theorem across five radices, and test both early mismatches and shells
that survive three comparisons but fail deeper inside.
