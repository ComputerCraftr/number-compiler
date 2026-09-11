# Cross-domain itinerary / residue / pair-field results

This probe applies the newer Collatz/prime quotient ideas back to reverse-and-add, and the reverse-and-add pair/carry machinery back to Collatz. Every compact result is charged separately from the work needed to derive it.

## Reverse-and-add: carry/event itinerary

A raw transpose of the 20-row carry slab is **not** a finite-small alphabet on the decimal-196 trace: across 16,832 sampled spacetime columns it realizes **15,579** distinct 20-bit carry histories (15,703 including active-domain history). This rejects the naive `20-bit vertical symbol -> finite automaton` idea.

The exact threshold itinerary `LOW / NEUTRAL / HIGH` is a last-event monoid, but neutral `S_i=9` positions are only **9.80%** of the sampled pair field. Encoding only non-neutral reset positions would therefore retain **90.20%** of positions before even charging their indices, so it is rejected as the primary spatial carrier.

### No-growth epoch coordinate

The branch itinerary has a useful bounded radix: completed growth runs have lengths {0: 93, 1: 189, 2: 3, 3: 8}, with maximum **3**. A no-growth epoch is therefore one radix-4 symbol `r in {0,1,2,3}` with physical duration `r+1`. Over the first 512 transitions the completed epochs average **1.747 physical steps/symbol**. This is an exact weighted-time coordinate, but it only gives a constant-factor reduction until the macro-event generator itself is quotiented.

### Self-pruning live carry itinerary

The fixed H=20 theorem contains a stronger source-specialized quotient. Once an old event has five later no-growth doublings, its transported contribution is identically zero mod 32 and that row can be discarded forever. Seeded once from an ordinary 20-row certificate, the `LiveCarryItinerary` reconstructs the exact pair from only its surviving carry suffix, generates the next carry, appends it, and prunes itself again. Over 512 advances it retains **8.406 rows on average** (6..11) and charges **42.61%** as many carry bits as the fixed 20-row window. This is an exact temporal-history quotient, but it does not by itself quotient the repeated nonlinear action used by powering.

### Macro-event generator audit

Collapsing each radix-4 growth run into one no-growth-terminated macro event does **not** reveal a small event alphabet. The exact macro forcing row is `F_r=S_out-2(1+z)^r S_in`:

| r | epochs | unique rows | coefficient alphabet | support fraction |
|---:|---:|---:|---:|---:|
| 0 | 93 | 92 | 7 | 0.855 |
| 1 | 189 | 189 | 19 | 0.953 |
| 2 | 3 | 3 | 42 | 0.997 |
| 3 | 8 | 8 | 96 | 1.000 |

The rows are nearly unique and become dense as `r` grows, so a direct four-symbol macro-event alphabet is rejected. The growth-run itinerary is useful control information, not a replacement for the nonlinear event generator.

### Additive hyperbolic fiber is already quotiented

The prime factor surface `n=q*r` has an additive digit analogue `s=a+b`. But the canonical pair field has already performed exactly that quotient: carry/event evolution depends on `s` and never on the individual `(a,b)`. Across the sampled trajectory, one pair field represents an average of about **2^134.06** fixed-width source digit assignments (maximum **2^298.69**). Reintroducing left/right digit lanes would therefore reverse a large existing canonicalization.

### Polynomial/cyclotomic event memory

For the cyclic quotient `z^m=1` modulo 32, the old-state transport is `2^q(1+z)^r`. The measured exact dependency horizons on the same trajectory are:

| classes m | average horizon | maximum |
|---:|---:|---:|
| 1 | 5.000 | 5 |
| 2 | 6.000 | 6 |
| 4 | 7.809 | 9 |
| 8 | 8.410 | 10 |
| 16 | 8.410 | 10 |

The `m=2` quotient is especially strong: `I+shift` has rank one over odd prime fields; over `F_2` its square is zero. Thus the alternating (`z=-1`) channel is reset by one growth step, while the full two-class old-state operator dies after at most six recent steps mod 32 on branch-count combinations sufficient for annihilation.

### Prime-polynomial audit and the stronger `(z+1)`-primary coordinate

Generic irreducible/prime polynomials do not give the desired forgetting. In `F_p[z]/(f)`, multiplication by `1+z` is a unit whenever irreducible `f != z+1`. The executable rank audit keeps full rank for `z^2+z+1` over F2 (`[2, 2, 2, 2, 2, 2, 2, 2]`) and `z^2+1` over F3 (`[2, 2, 2, 2, 2, 2, 2, 2]`). Rank loss appears only in the `z+1` primary component.

Writing `y=z+1` makes that useful component explicit: modulo `(y^k,32)`, a growth step is **literal multiplication by y**, while a no-growth step is multiplication by 2. Hence old state dies exactly when either five no-growths or `k` growths have occurred. Measured horizons are:

| jet degree k | average horizon | maximum |
|---:|---:|---:|
| 1 | 1.803 | 5 |
| 2 | 4.059 | 6 |
| 4 | 7.627 | 8 |
| 8 | 8.410 | 10 |
| 16 | 8.410 | 10 |

This is the cleanest polynomial itinerary coordinate found: it is a nilpotent shift conjugacy for the linear transport. It remains a theorem-interface projection because a small jet is not injective enough to reconstruct every local pair coefficient/carry.

### Negacyclic / `b^m+1` residues

The complementary quotient `z^m=-1` corresponds to radix residues of the `b^m+1` family. For `m=2`, `(1+z)^2=2z`, so **two growths buy one full 2-adic decay factor**. Modulo 32 the exact kernel is `(0, 2)`. The measured dependency horizons are:

| m | average horizon | maximum |
|---:|---:|---:|
| 1 | 1.803 | 5 |
| 2 | 6.600 | 7 |
| 4 | 7.809 | 9 |
| 8 | 8.410 | 10 |

This explains why arbitrary modulus search is less useful than choosing a polynomial factor where the transport itself acquires 2-adic valuation.

### mod 99 / z+1 factor

For decimal reversal, modulo 9 the transition is always doubling. Modulo 11, an even-width source maps to zero because a palindromic pair polynomial of even width has the exact factor `z+1`; zero is absorbing thereafter. Decimal 196 first enters that channel at step 3 and from then on its mod-99 residue is the exact six-cycle

`[11, 22, 44, 88, 77, 55]`.

All **255 / 255** sampled even-width pair fields satisfy the exact `z+1` factor identity. This is a useful theorem-interface/residue quotient, but it is not injective enough to replace the carry slab.

### Rejected five-bucket event regrouping

Grouping event memory by the five powers of two would use **25 coefficient bitplanes** instead of 20 binary carry rows, and every bucket reaches the full 32-value alphabet (`[32, 32, 32, 32, 32]`). Once the existing prefix-domain metadata is charged correctly this is not a smaller canonical carrier, so it is **not retained as semantic state**.

## Collatz: reverse-and-add pair/carry machinery

For an odd decimal step, the raw digit field is `R_i=3*d_i+[i=0]`, whose largest possible component is **28**. After the LSD the carry alphabet is exactly `{0,1,2}`; the ordinary decimal digits induce the closed five-element transfer monoid

`[(0, 0, 0), (0, 1, 1), (1, 1, 1), (1, 1, 2), (2, 2, 2)]`.

So `3*n+1` has a native five-element spatial carry scan rather than a generic multiplication transducer.

The prime-style divisor quotient is even cleaner. The nested lanes `2^k | 3*n+1` canonicalize by tropical **max** to the single value `v2(3*n+1)`. For seed 27, **70 normalized parity steps** become **41 valuation symbols** (max valuation 5), a **1.707x** run-length reduction. Their native affine slab is `(width=70, ones=41)` and maps 27 directly to **1**.

This valuation symbol also completely determines the next accelerated odd state modulo 3: `target mod 3 = 2^(-v) mod 3 = (-1)^v`. The old odd-state residue disappears, so mod 3 is derived directly from the tropical itinerary rather than stored as another channel.

Odd-modulus / prime-field projection of that entire slab is one affine map `x -> a*x+b`; this commutes with slab composition, so prime residues are theorem-interface projections and do not require replaying the Collatz orbit. Mod 99, the whole seed-27 valuation slab is the single affine map `x -> 36*x+19` and sends 27 to 1.

## Net result

The cross-domain transfer now separates the remaining problem more sharply. Reverse-and-add gains an exact self-pruning live carry itinerary and a `(z+1)`-primary nilpotent transport coordinate; Collatz gains the five-element decimal `3*n+1` carry monoid and tropical valuation itinerary. Generic prime-polynomial quotients, raw vertical histories, threshold-reset positions, and direct macro-event alphabets all fail the charged compression test.

It still does **not** produce an injective finite/polylog quotient of the full powered reverse-and-add nonlinear action. The next target should combine the live-suffix certificate with primary-jet theorem interfaces so equivalent nonlinear slab actions can canonicalize **before** composition; merely packing the surviving rows or their macro events would only be another representation cleanup.
