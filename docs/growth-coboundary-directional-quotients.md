# Growth coboundaries and directional value consumers

This update separates geometry needed to derive carries from value information
needed by the next consumer. The new reductions have different integration
status in reverse/add, Collatz, and the power-number families.

## Reverse/add growth

For an admitted symmetric growth source, the geometry-derived carry field has
`C[0]=0` and `C[L]=1`. Define

```
q[i] = S[i] - 9*C[i+1] = ((S[i] mod 10) + C[i+1]) mod 10
delta[i] = C[L-i] - C[i+1]
```

The independent half uses twelve symbols: `(0,0)` through `(9,0)`, `(0,-1)`,
and `(9,1)`. Nonzero delta is possible only at EQ. The quotient does not retain
the original domain label or decode the original 19-valued source.

The exact output follows from the radius-one law:

```
edge     = q[0] + delta[0]
interior = q[i] + q[i-1] + delta[i] - 10*delta[i-1]
center   = 2*q[last]                 # even source width
```

[`Reverse_Growth_Coboundary.thy`](../devtools/proofs/isabelle/Reverse_Growth_Coboundary.thy)
proves these laws under valid carries and source symmetry. The center carry
equality is derived from carry idempotence, not assumed independently. The
theory proves forward congruence; it does not prove the empirical converse
that equal outputs always determine the same quotient.

`GrowthCoboundaryHalf` records the output-facing occurrence. In particular,
the four width-six sources with outer values 10 and either 1 or 10 in each
inner mirror orbit all become `(1,1,1)` in this symbol alphabet and produce
`(1,2,2,2,2,2,1)`. The native expression chart also fuses existing one-variable
value/carry tables: a varying LT-1/GT-10 source choice becomes a constant
symbol before publication. That is a local table composition, not enumeration
of complete source contexts.

`ReverseGeometryContext(..., growth_quotient=True)` integrates this chart before
the growth output projections. Native domain and F5/F2 emissions avoid a
19-valued pair-sum node. The F5/F2 emitters fuse their fixed linear radius-one
transport with the quotient views; they are not a new extensional normalizer
for arbitrary affine expressions. Invalid independent symbol combinations have
explicit total circuit extensions; only the admitted geometry/source predicate
licenses the exact reconstruction theorem.

The new path remains an explicit research mode. The first separate-view
lowering retained 8,855 A16 nodes, and the fused emitter reduced that to 8,085,
still above the preceding residue lowering's 7,784. Both paths reach the A32
node ceiling. The default keeps the residue lowering rather than adopting a
measured storage regression. Removing unused growth construction on the
capacity-overflow branch further reduces the default to 7,769 nodes.

This isolates a remaining compiler problem: the generic temporal action still
publishes complete endpoint planes for later substitution. A local quotient
and a genuine source collision do not establish zero intermediate plane
bindings across arbitrary powered growth blocks. No zero-publication metric
or complete temporal closure is claimed.

### Bounded successor image identity

After the source domain has supplied the carry field and branch, it is dead
provenance for an exact bound successor image.  The finite image audit therefore
interns only the canonical successor word.  It keeps source Gamma solely in a
separate negative-control occurrence key.  At width eight this gives
`65,161 -> 65,080` images on no growth and `65,160 -> 12,429` on growth, or
`130,321 -> 77,509` overall.  The growth sources `(10,0,0,10)` and
`(10,9,9,10)` have different source domains but share the exact image
`(1,1,0,1,1)`.

This bound image identity does not replace the input key used while executing
an occurrence.  It also does not identify free temporal functions: two actions
that agree at one bound source may disagree at another admitted source.  The
production recursive image arena follows this separation already.  Its request
binding contains action, source, geometry, and signature; its semantic image
key omits action and source.  Normalized geometry contains only spatial level,
orientation, phase, and halos, never source Gamma.  Parametric interfaces,
summaries, and child images remain in semantic identity because they describe
behavior still visible to an unbound consumer.

[`reverse_successor_image_audit.py`](../devtools/proofs/reverse_successor_image_audit.py)
and its exhaustive validation pin the finite counts without promoting them to
an A32 action quotient or a future-behavior class.

## Collatz directional streams

The source carry domain first supplies multiplication carry `c`. The value
view is then `n=(3*d+c) mod 64`. For residual phase `e`, exact quotient and
remainder streams are independent:

```
q[i] = n[i] >> e
r[i] = n[i] mod 2**e
target[i] = q[i] + 2**(6-e)*r[i+1]
```

The domain consumer reduces these streams independently to `L[i]` and `R[i]`
before pairing adjacent positions. Their class counts are `(5,1)`, `(5,2)`,
`(5,4)`, `(5,5)`, `(4,5)`, and `(2,5)`. The compiler never constructs an
inverse domain/harmonic/3-adic leaf to implement this consumer.

The fixed tables are generated from only 64 quotient/remainder combinations
per phase, not 4,096 redundant raw-digit pairs. Existing exact value output
remains separate from the domain view. The directional interface supports
substitution of already-composed streams; it does not certify bounded growth
under arbitrary temporal squaring.

The streaming `Radix64CollatzStage` uses the same geometry-first emission and
retains only the left quotient in its lookahead register. It consumes the next
remainder immediately; exact target digits are joined only when emitted.

## Fermat and Mersenne

The same separation applies to source closure geometry and powered angular
transport: Fermat is negacyclic and Mersenne cyclic. The unused per-level
Frobenius section controller was removed; the active path already uses a
whole-block `SpecialGermPlan`.

The demanded étale selector belongs outside action identity. It cannot yet
be admitted to the shared tile scheduler for general candidates: the code
lacks both a candidate-derived all-local selector proof and a power-family
temporal certificate. The applicability audit preserves that boundary.
See [the power-number audit](research/power-numbers/GEOMETRY_FIRST_ETALE_TILE_APPLICABILITY.md).

Final checks and measured costs are recorded in the
[dated evidence](../results/current/growth-coboundary-directional-2026-09-10/README.md).
