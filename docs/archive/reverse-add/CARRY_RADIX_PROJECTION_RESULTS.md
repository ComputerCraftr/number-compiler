# Padded carry-radix / cyclotomic projection results

A fixed-width carry word `d_0...d_(L-1)` is treated as the polynomial
`W(z)=sum_i d_i z^(L-1-i)`.  Evaluating at a radix `b` gives the ordinary
base-`b` integer `W(b)`.  The pair `(L,W(b))` is lossless for binary words,
because `L` restores leading-zero padding.  More importantly, an exact
factor `Phi_m(z) | W(z)` implies `Phi_m(b) | W(b)` for every integer `b`.
Therefore bases 3/5/7/10 are theorem instantiations of one polynomial
factorization, not four independent sources of information.

## Reverse-add 196

Across 256 current carry rows, **95** rows have at least one
bounded exact cyclotomic factor and **26** rows are monomial x cyclotomic
with no nontrivial residual.  The factors cover **440/13864 = 3.17%** of active polynomial degree.

| charge | bits |
|---|---:|
| raw padded binary planes | 16,555 |
| factor every row losslessly | 22,378 |
| choose cheaper of raw/factor per row | 16,530 |
| rows where exact factorization wins | 4 |

So the structure is genuine but sparse globally: bounded factorization is not a
replacement encoding for every row.  It is useful as an optional theorem/compression
channel on selected rows.

Representative exact factors:

| step | factors | base-3 | base-5 | base-7 | base-10 |
|---:|---|---:|---:|---:|---:|
| 10 | `Phi_2 Phi_10` | 732 | 15,630 | 117,656 | 1,000,010 |
| 40 | `Phi_2 Phi_6 Phi_10 Phi_30` | 129,140,172 | 762,939,453,150 | 232,630,513,987,256 | 100,000,000,000,000,100 |
| 55 | `Phi_5 Phi_25` | 1,270,932,914,163 | 372,529,029,846,191,405 | 1,564,580,056,274,625,717,607 | 11,111,111,111,111,111,111,111,110 |
| 93 | `Phi_2 Phi_3 Phi_6 Phi_18 Phi_54` | 216,803,362,095,693,828 | 18,044,374,883,174,896,242,656,250 | 3,084,666,494,163,270,365,130,747,610,344 | 1,110,000,000,000,000,000,000,000,001,110,000,000 |

The exact current carry field still has **255** classes,
**1** repeat, and **1**
same-current/different-next conflict.  The compact factor-only feature has
**254** classes and **2** next conflicts.
Because the step-10/11 collision is already an equality of the *entire* carry row,
no lossless radix evaluation or factorization of that row can make it Markov.

## Collatz multiply-by-3 carry planes

The synthesized carries are ternary (`0..2`).  Each row is reversibly represented
for analysis as one scalar offset plus binary bit planes; those planes are not retained
by the canonical compiler.

| seed | source radix | rows | factor-degree coverage | raw plane bits | factor-all bits | exact factor wins |
|---:|---:|---:|---:|---:|---:|---:|
| 27 | 4 | 41 | 79.38% | 622 | 1,368 | 0 |
| 27 | 10 | 41 | 100.00% | 409 | 1,009 | 0 |
| 27 | 16 | 41 | 100.00% | 345 | 918 | 0 |
| 6171 | 4 | 96 | 49.78% | 1,826 | 3,640 | 0 |
| 6171 | 10 | 96 | 75.84% | 1,206 | 2,785 | 0 |
| 6171 | 16 | 96 | 93.33% | 1,049 | 2,511 | 0 |
| 837799 | 4 | 195 | 26.39% | 5,734 | 9,747 | 1 |
| 837799 | 10 | 195 | 46.42% | 3,946 | 7,471 | 0 |
| 837799 | 16 | 195 | 58.10% | 3,384 | 6,831 | 0 |

Cyclotomic degree coverage is often strong, especially in larger source radices, but
the explicit factor metadata/residual is usually more expensive than the small carry
plane itself.  The existing Collatz valuation/sentinel quotient therefore remains the
canonical representation; carry-plane factors are useful derived certificates and may
be more valuable when composed temporally rather than encoded row-by-row.

## Fermat / Mersenne normalization-carry planes

The production special-number arithmetic retains one scalar end-around boundary carry.
The complete internal signed/multi-valued carry row is reconstructed on demand, converted
losslessly to offset + bit planes, and discarded after measurement.

| family | parameter | rows | carry range | max planes | factor-degree coverage | raw plane bits | selective bits |
|---|---:|---:|---|---:|---:|---:|---:|
| fermat | 3 | 7 | -4..2 | 3 | 41.03% | 182 | 182 |
| fermat | 4 | 15 | -12..10 | 5 | 19.94% | 836 | 833 |
| fermat | 5 | 31 | -12..12 | 5 | 10.45% | 4,992 | 4,729 |
| mersenne | 11 | 9 | -1..5 | 2 | 22.58% | 272 | 272 |
| mersenne | 19 | 17 | -1..17 | 3 | 8.63% | 825 | 821 |
| mersenne | 31 | 29 | -1..14 | 3 | 5.44% | 2,926 | 2,834 |

The factor coverage drops as the tested Fermat/Mersenne widths grow.  Local rows can
still compress, but this is not evidence of a bounded full-state quotient.

### Exhaustive closure check

| family | parameter | states | exact carry classes | exact target? | exact next? | factor classes | factor target? | factor next? |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| fermat | 1 | 5 | 2 | False | True | 2 | False | True |
| fermat | 2 | 17 | 13 | False | True | 13 | False | True |
| fermat | 3 | 257 | 246 | False | False | 216 | False | False |
| mersenne | 3 | 7 | 7 | True | True | 7 | True | True |
| mersenne | 5 | 31 | 25 | True | False | 25 | True | False |
| mersenne | 7 | 127 | 112 | True | False | 91 | True | False |

### Does carry structure help a lossy digit channel?

The strongest test combines one deliberately small current-digit channel (`Phi_2` modulo 4)
with the lossy carry-factor feature, then checks target separation and exact successor closure.

| family | parameter | states | combined classes | target? | next? | minimized observer classes |
|---|---:|---:|---:|---:|---:|---:|
| fermat | 3 | 257 | 240 | False | False | - |
| mersenne | 5 | 31 | 29 | True | True | 5 |
| mersenne | 7 | 127 | 103 | True | False | - |
| mersenne | 11 | 2047 | 1554 | True | False | - |
| mersenne | 13 | 8191 | 5723 | True | False | - |

There is one genuine small positive: for M5, `Phi_2 mod 4 + carry factors` gives a non-injective
29-class closed refinement, and exact unary Moore minimization of that quotient recovers the known
**5 observer classes**.  But it does not generalize: M7, M11 and M13 remain non-next-closed, and
F3 still fails target separation.  A broader single-channel search over `Phi_2..Phi_16` and
coefficient moduli 2/4/8/16/32 found no non-injective closed combination for F3 or M7.

This is the decisive negative result for the special-number carry hypothesis as a general solution.  For F3,
even the complete internal carry row fails both target separation and next closure.  For
M5/M7 it separates the current target but is not next-closed.  A lossless alternate-radix
reinterpretation of exactly that row cannot improve either fact.  The remaining Fermat/
Mersenne task is still extraction of the small Moore observer from the modular digit field,
not reconstruction of a larger carry vector.

## Architectural conclusion

The padded-radix idea is retained as a **derived projection algebra**, not parallel state:

- exact width + radix evaluation provides reversible leading-zero-safe integer coordinates;
- exact cyclotomic factors are base-independent polynomial facts and can be evaluated in any radix;
- ternary/signed carry fields share one reversible offset+bit-plane adapter;
- lossless factorization always retains an explicit residual;
- canonical Collatz and special-number compiler state remains unchanged.

The most promising next experiment is temporal composition of the short factor/order
spectra (plus width/growth) and testing whether that history can supply the missing small
reverse-add hidden-source observer.  For special numbers, the M5 bridge suggests searching
direct synthesis maps from digit/carry theorem channels to Moore classes, but the M7+ closure
failures show that row-wise factorization alone is not a scalable solution.
