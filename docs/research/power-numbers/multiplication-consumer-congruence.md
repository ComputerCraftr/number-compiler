# Multiplication consumer congruence

The binary generalization of the carry consumer must start from an operation
that is already defined on the source carrier.  The bounded Fermat radix-orbit
carrier and Mersenne sign carrier both satisfy this condition for
multiplication:

```text
x ~ x' and y ~ y'  =>  xy ~ x'y'.
```

They do not satisfy it for addition.  Independent radix rotations or sign
choices change the relative phase of a sum.  The executable audit retains a
concrete addition counterexample for every F2/F3/M5/M7 control.  Consequently
these carriers cannot yet support the `A0^2 + 2 A0 A1 + A1^2` block combine,
even when a multiplication quotient exists.

For each complete bounded carrier, the experiment builds the initial partition
from the actual shared square tile's demanded carry action and order-4 harmonic
transducer.  It then refines classes by their complete multiplication rows.
At the fixed point it verifies every pair of classes has one target class.  A
`mulQ` table and its diagonal `squareQ` are published only when this stable
partition remains noninjective.  If refinement reconstructs every carrier
state, the row is reported as an injective failure and no quotient table is
published.

The complete results are:

| carrier | source classes | initial consumer classes | conflicts | stable classes |
|---|---:|---:|---:|---:|
| F2 | 3 | 3 | 0 | 3 |
| F3 | 17 | 13 | 4 | 17 |
| M5 | 16 | 15 | 1 | 16 |
| M7 | 64 | 52 | 12 | 64 |

Thus F2 is already pointwise at this boundary, while every initially
noninjective F3/M5/M7 consumer partition reconstructs the complete carrier
after one multiplication-refinement round.  No `mulQ` or `squareQ` table is
published for these rows: a table is not described as a quotient when its
stable classes equal its source classes.

The construction is deliberately limited to F2, F3, M5, and M7.  These are
complete finite carriers, rather than trajectory samples, and keep the
Cartesian multiplication proof bounded.  Larger leaf/block boundaries need a
symbolic or recursively factored multiplication-row representation before the
same test can scale.

A preflight row is still emitted for F4, M11, and M13.  Multiplicative closure
is discharged algebraically by the radix-orbit or sign-orbit identity, and an
explicit addition witness is retained.  Their prospective Cartesian cell
counts exceed the fixed 4,096-cell research budget, so refinement stops before
allocating a multiplication table.  The admitted rows report table cells,
refinement signature cells, rounds, and quotient-verification cells explicitly.
The rejected counts are 4,198,401 for F4, 1,048,576 for M11, and 16,777,216
for M13.

No row admits the tile scheduler.  Scheduler admission additionally requires
an additive/fold congruence, a compositional interface proof, and separation of
the demanded terminal observer.  The terminal prime bit remains outside the
arithmetic action.
