# Cyclotomic / Fermat / Mersenne / binary-prime results — v0.17.0

This pass asks whether the digit fields already used by reverse-add, Collatz, and the prime projector hide a stronger cyclotomic or automatic quotient. The new objects remain derived compiler/research interfaces; they do not replace the canonical reverse-add state.

## 1. Reverse-add cyclotomic theorem

For power-of-two `m`, `z^m+1 = Phi_(2m)(z)`. For `m>=2`, `(1+z)^m = 2 U_m(z)` in that quotient and `U_m` is a 2-adic unit. Therefore the exact coefficient-content valuation is `q + floor(r/m)` for `2^q(1+z)^r`. The earlier negacyclic kernel expansion is retained as the independent differential path, while the production annihilation query now consumes the closed valuation theorem.

| m | cyclotomic order | decimal modulus | Fermat index at radix 2 | avg horizon | max horizon |
|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 11 | 0 | 1.807 | 5 |
| 2 | 4 | 101 | 1 | 6.599 | 7 |
| 4 | 8 | 10001 | 2 | 7.807 | 9 |
| 8 | 16 | 100000001 | 3 | 8.412 | 10 |
| 16 | 32 | 10000000000000001 | 4 | 8.412 | 10 |

The norm classification also explains why this family is special: `abs(Phi_n(-1))` is even only on the 2-power cyclotomic orders (apart from the exact `Phi_2` zero channel). Odd Mersenne-like cyclotomic orders make `1+z` a 2-adic unit, so growth cannot erase them by itself.

## 2. The Collatz k*2^(k/2) observation becomes a symbolic construction

For output bit `t`, after assigning `l` low parity bits the residual `Q_k^-1` function is determined by only `(prefix popcount, truncated affine residue)`. Its exact frontier is bounded by `min(2^l,(l+1)2^(t+1-l))`. Splitting at the meet-in-the-middle point gives an `O(sqrt(k) 2^(k/2))` upper bound for the whole shared LSB decision construction. This is stronger than the earlier empirical `k*2^(k/2)` fit and avoids the `2^k` truth table entirely.

| k | avoided truth rows | shared nodes | symbolic states | finite state bound |
|---:|---:|---:|---:|---:|
| 12 | 4,096 | 604 | 1,046 | 1,622 |
| 16 | 65,536 | 3,280 | 4,489 | 7,918 |
| 20 | 1,048,576 | 15,112 | 17,804 | 35,782 |
| 22 | 4,194,304 | 31,077 | 34,882 | 75,110 |
| 24 | 16,777,216 | 62,874 | 68,049 | 156,926 |
| 26 | 67,108,864 | 126,074 | 132,899 | 326,798 |
| 28 | 268,435,456 | 250,474 | 259,308 | 674,838 |
| 30 | 1,073,741,824 | 494,118 | 505,440 | 1,387,414 |
| 32 | 4,294,967,296 | 971,238 | 985,562 | 2,845,454 |

## 3. Fermat and Mersenne are native cyclotomic stress tests

`F_n = Phi_(2^(n+1))(2)` is exactly the radix-2 evaluation of the same power-of-two negacyclic family. Subtracting one gives the pure squaring coordinate `F_n-1=2^(2^n)`, so generation is exponent doubling. Pepin primality remains a projection requiring `2^n-1` modular squarings.

For prime exponent `p`, `M_p = Phi_p(2)`. Composite exponents are rejected before any Lucas-Lehmer work because `M_d | M_n` whenever `d|n`; more generally `gcd(M_a,M_b)=M_gcd(a,b)`. Lucas-Lehmer's nonlinear recurrence `s->s^2-2` has the quadratic-unit conjugacy `s_j = alpha^(2^j)+alpha^(-2^j)` with `alpha=2+sqrt(3)`, so its time operator is again exponent doubling while modular projection remains charged.

The raw multiplication digit fields expose the expected cyclotomic convolution: Mersenne squaring is cyclic autocorrelation modulo `z^p-1`; Fermat squaring is negacyclic autocorrelation modulo `z^(2^n)+1 = Phi_(2^(n+1))(z)`. These fields are exact, but the measured raw rows are nearly all distinct, so they are testbeds/conjugacies rather than a newly compressed primality state.

Fermat factor lanes also inherit a strong hyperbolic restriction: for `F_5`, only 511 numbers of the form `1 mod 128` lie below `sqrt(F_5)`, and both known factors satisfy it. Mersenne factors analogously lie in `1 mod 2p`.

## 4. Direct binary prime automata do not collapse

The natural base-2 set morphisms are the 2-kernel maps `P(n) -> P(2^e n+r)`. A finite LSB-first automaton would have to merge many odd residue prefixes. On an exact 256-sample residual vector (`tail_bits=8`), every odd prefix through ten bits has a distinct residual prime vector:

| prefix bits | odd prefixes | distinct residuals |
|---:|---:|---:|
| 1 | 1 | 1 |
| 2 | 2 | 2 |
| 3 | 4 | 4 |
| 4 | 8 | 8 |
| 5 | 16 | 16 |
| 6 | 32 | 32 |
| 7 | 64 | 64 |
| 8 | 128 | 128 |
| 9 | 256 | 256 |
| 10 | 512 | 512 |

The finite odd-prime block also rejects an affine Boolean model: at 4096 candidates the algebraic normal form has full degree 12 with 2,060 monomials, and none of its 12 coordinate derivatives is constant (their disagreement densities lie between 22.02% and 23.29%).

Cyclotomic grouping does not rescue the raw binary wheel either: the 446 odd generators through 3163 occupy 413 exact `ord_q(2)` channels, or 387 channels after identifying +/- periods. That is far worse than the existing 78 bounded-word packed groups.

Binary remains the best *implementation radix* found for the factor/wheel projector, but the raw prime Boolean vector does not reveal a small universal automaton. The useful automaton is still the factored packed wheel, whose state is the product of small congruence automata rather than prime bits themselves.

## 5. Architectural consequence

The reusable pattern is now clearer: use cyclotomic decomposition to identify nilpotent/ramified theorem channels, use coordinate conjugacies to power time (Collatz parity shift, Fermat squaring, Lucas-Lehmer quadratic-unit doubling), and keep primality/event projection separately charged. No result here proves a polylog temporal successor quotient for the current finite 196 defect-domain morphism.
