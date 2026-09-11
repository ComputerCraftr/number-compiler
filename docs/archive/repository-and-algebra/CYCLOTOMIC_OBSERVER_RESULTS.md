# Cyclotomic-jet / normalization-observer results

This pass treats carry structure as an exact normalization **defect algebra**, not as
another retained carry encoding.  If raw coefficients `A(z)`, normalized digits `D(z)`,
and carry boundaries `c_0..c_L` obey `a_i+c_i=d_i+b*c_(i+1)`, then with
`Q(z)=sum_i c_(i+1) z^i` the canonical finite identity is

```text
A(z)-D(z) = (b-z) Q(z) - c_0 + c_L z^L.
```

The boundary term vanishes literally for a zero-ended finite normalization and vanishes
in the quotient ring for cyclic/negacyclic end-around normalization.  Therefore every
cyclotomic projection of a carry row is a projection of one exact normalization theorem.

## One canonical cyclotomic jet

The new `CyclotomicDigitBlock(order, power, modulus)` is reduction modulo
`(Phi_order(z)^power, modulus)`.  It subsumes the previously separate local channels:

- `Phi_1^(r)` local coefficients equal the binomial moments: **True**;
- `Phi_2^(r)` local coefficients equal the primary `z+1` jet: **True**;
- `power=1` is the existing cyclotomic-residue channel.

Legacy `CyclotomicJetBlock` / `CyclotomicProjectionBlock` names are absent;
`CyclotomicDigitBlock` is the sole canonical implementation and cache identity.

## Exact normalization-defect audit

| family/path | exact cases |
|---|---:|
| reverse-add 196 finite blocks | 64 |
| reverse-add zero-boundary padded blocks | 64 |
| Collatz multiply-3/add-1 fields (radices 4/10/16) | 123 |
| Mersenne cyclic states (M5 ring) | 31 |
| Fermat negacyclic states (width 4 ring) | 17 |

All boundary-aware identities and selected quotient-ring projections agree: **True**.

## Reverse-add: explain the 196 collision, then reject fake closure

The first exact same-action/different-successor collision remains steps **10** and **11**.
Their complete carry rows are equal: **True**.  The existing
base-`(b-1)` source residue separates them as **4 vs 8 (mod 9)**.
That is exactly the `Phi_1`/digit-sum coordinate already represented in the canonical
residue interface, so no duplicate jet identity is retained for it.

A bounded search tested **128** single cyclotomic jets (`Phi_1..Phi_12`,
powers 1..3 where degree <=12, coefficient moduli 2/4/8/16) together with the carry action.
**101** are conflict-free on the single 196 orbit, but
**0** are non-injective.  The minimum closed
candidate still has **256 classes for 256 transitions**:
the apparent solutions reconstructed the trajectory rather than finding a quotient.

The existing small residue channels also fail cross-seed closure:
base-`(b-1)` gives **19** conflicts and
base-`(b-1)` + base-`(b+1)` gives **12** on seeds 190..202.

### Finite-memory test

Across seeds 1..300 for 32 steps, short histories reduce
conflicts but do not close:

| history | base-(b-1) classes | conflicts | base±1 classes | conflicts |
|---:|---:|---:|---:|---:|
| 1 | 840 | 958 | 1,060 | 677 |
| 2 | 984 | 307 | 1,146 | 180 |
| 3 | 1,021 | 155 | 1,146 | 82 |

An apparent higher-order winner, `Phi_11 mod 16` + carry action,
has **0 conflicts** on seeds 1..300 for 64 steps
(2,057 observed classes) but fails with **1** conflict on the
disjoint seeds 10000..10350 for 32 steps.
It is therefore kept as research evidence of overfitting, not promoted into canonical state.

## Special-number square-sign quotient

Both special recurrences square before their next observation, so `x` and `-x` have the
same successor.  For Mersenne width `p`, the binary digit polynomial modulo `Phi_p` over
`F_2` has kernel exactly the all-ones word; hence its equivalence classes are exactly
bitwise complements, i.e. `x ~ -x mod (2^p-1)`.  This turns the earlier M5 empirical
carry bridge into a family-level algebraic quotient:

| p | states | Phi_p mod 2 classes | sign classes | same partition | target? | next-closed? |
|---:|---:|---:|---:|---:|---:|---:|
| 5 | 31 | 16 | 16 | True | True | True |
| 7 | 127 | 64 | 64 | True | True | True |
| 11 | 2,047 | 1,024 | 1,024 | True | True | True |
| 13 | 8,191 | 4,096 | 4,096 | True | True | True |

Pepin squaring has the same sign-erasure property modulo `2^(2^n)+1`; because its current
target is `-1` while `+1` is sign-equivalent, the safe observer is `(current_target_bit,
sign_representative)` rather than the representative alone.

| family | parameter | source states | sign-quotient classes | target? | next-closed? |
|---|---:|---:|---:|---:|---:|
| mersenne | 5 | 31 | 16 | True | True |
| mersenne | 7 | 127 | 64 | True | True |
| mersenne | 11 | 2,047 | 1,024 | True | True |
| mersenne | 13 | 8,191 | 4,096 | True | True |
| fermat | 2 | 17 | 10 | True | True |
| fermat | 3 | 257 | 130 | True | True |

These are exact observer theorems for the tested prime moduli, not lookup-table labels.
Composite Mersenne moduli are intentionally excluded from the prime-group theorem.

## Production work reduction from sign canonicalization

The special digit-field projector now canonicalizes each squaring input to the sparser of
`x` and `-x` before convolution.  This preserves the exact recurrence result and reduces
actual digit-product work without retaining a parallel sign state:

| family | parameter | scalar products old -> new | reduction | coefficient adds old -> new | reduction | changed steps | nonzero digits saved |
|---|---:|---:|---:|---:|---:|---:|---:|
| mersenne | 31 | 5,469 -> 4,446 | 18.71% | 4,235 -> 3,268 | 22.83% | 9 | 33 |
| fermat | 5 | 6,812 -> 5,696 | 16.38% | 5,336 -> 4,271 | 19.96% | 11 | 34 |

## Architectural conclusion

- normalization carries now have one exact boundary-aware defect theorem;
- primary jets, binomial moments, and cyclotomic residues share one generalized jet algebra;
- legacy projection-only cyclotomic names are absent rather than parallel state identities;
- reverse-add candidate features must pass cross-seed closure and non-injectivity before promotion;
- special-number squaring uses an algebraically proved sign quotient before convolution;
- the small prime Fermat/Mersenne Moore observers now have direct group-theoretic descriptions;
- derived carry/radix helpers remain outside production compiler reachability.

The remaining reverse-add problem is therefore narrower: find a source observer smaller than
the pair field that survives the cross-seed closure tests.  More current-row factorization or
longer histories of the existing base±1 residues are now experimentally ruled out as the next
generic solution on the bounded adversarial sets used here.
