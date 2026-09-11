# Special-number finite quotient binary jump — v0.43.0

This probe uses the same architectural rule as the reverse-add/Collatz powered stacks: first prove a finite semantic quotient, then binary-compose the quotient transition by extensional behavior. No source orbit/itinerary is retained, and specialization at the requested horizon performs no raw Pepin/Lucas--Lehmer squarings.

v0.41 leaves the composite-safe jump semantics unchanged while deleting the obsolete parallel order-character compiler state. The prime-conditional group-depth theorem is now the sole special depth semantics: image ranks, Moore=image-depth, and target distance are derived algebraically, while carry histories remain downstream research witnesses only. The public composite-safe builders still prove their quotient machines by complete bounded-domain construction, so `scalable_construction` remains false. The group-depth theorem is not promoted into the builder until purity can be established without the long order test or hidden factorization.

## Exact powered quotients

| family | parameter | raw states | carrier classes | minimized classes | state bits | retained transition bits | observer offset | target N | quotient steps | binary compositions | specialization raw squarings |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| fermat | 2 | 17 | 3 | 2 | 1 | 2 | 3 | 3 | 0 | 0 | 0 |
| fermat | 3 | 257 | 17 | 5 | 3 | 15 | 4 | 7 | 3 | 3 | 0 |
| fermat | 4 | 65,537 | 2,049 | 12 | 4 | 48 | 5 | 15 | 10 | 5 | 0 |
| mersenne | 5 | 31 | 16 | 5 | 3 | 15 | 0 | 3 | 3 | 3 | 0 |
| mersenne | 7 | 127 | 64 | 7 | 3 | 21 | 0 | 5 | 5 | 4 | 0 |
| mersenne | 11 | 2,047 | 1,024 | 3 | 2 | 6 | 0 | 9 | 9 | 5 | 0 |
| mersenne | 13 | 8,191 | 4,096 | 13 | 4 | 52 | 0 | 11 | 11 | 6 | 0 |

### Mersenne carrier

The carrier is the existing whole `Phi_p mod 2` digit component. It is theorem-equivalent to the exact sign quotient `x ~ -x`, because `Phi_p(2)=2^p-1` and Lucas--Lehmer satisfies `T(-x)=T(x)`. The carrier is therefore directly injectable by canonical sign representative, successor-closed, and target-separating. Exact Moore minimization gives 5/7/13 classes for prime M5/M7/M13, matching the prime-domain group-depth theorem; composite M11 instead collapses to 3 exact ring-safe classes. Binary powering acts only on this minimized transition table.

### Fermat carrier

The carrier is a new exact radix/cyclotomic orbit quotient. Since `2^(2^n) == -1 mod F_n`, the radix-root element 2 has exact order `2^(n+1)` modulo every `F_n`, prime or composite. Multiplication by its powers is a negacyclic digit rotation/sign action, and squaring maps every actual residue orbit to a residue orbit. The bounded builder enumerates those actual orbits rather than assuming every residue has the full group-orbit size. The current target `-1` is not separated on that carrier, so the observer is delayed by `n+1` squarings; at that point every radix phase is annihilated. Moore minimization of the delayed machine gives 2/5/12 states for F2/F3/F4.

## Construction charge / remaining blocker

| family | parameter | proof states examined | construction raw squarings | radix shifts | exhaustive | scalable |
|---|---:|---:|---:|---:|---|---|
| fermat | 2 | 17 | 12 | 40 | True | False |
| fermat | 3 | 257 | 85 | 528 | True | False |
| fermat | 4 | 65,537 | 12,294 | 131,104 | True | False |
| mersenne | 5 | 16 | 16 | 0 | True | False |
| mersenne | 7 | 64 | 64 | 0 | True | False |
| mersenne | 11 | 1,024 | 1,024 | 0 | True | False |
| mersenne | 13 | 4,096 | 4,096 | 0 | True | False |

The binary jump is therefore **real after quotient construction**: target specialization performs zero recurrence squarings and `O(log N)` extensional map compositions. But quotient construction is still exhaustive in the bounded implementation. The remaining special-number theorem is now sharper: construct/inject the same small quotient from symbolic radix/cyclotomic data without enumerating the ambient carrier/raw state space.

No full Hensel/CRT reconstruction, caller certificate, saved itinerary, or deferred exponent token is credited as a solution.
