# Square-only carry and consumer congruence

The Fermat and Mersenne recurrence needs unary squaring, not a general ring
quotient.  The earlier multiplication audit remains a useful negative control:
its refinement asks every class to multiply every other class and therefore
retains distinctions that the production recurrences never consume.

The production digit kernel now evaluates a square through triangular leaves.
For a width `w` leaf it performs `w(w+1)/2` finite coefficient products rather
than `w^2` ordered products.  A diagonal term is emitted once; an off-diagonal
term is doubled and enters one level higher.  The doubling is charged as a
coefficient addition.  Recursive square blocks use

```text
(low + high)^2 - low^2 - high^2
```

and therefore call three smaller square blocks.  The cyclic or negacyclic fold
and `RadixCarryBlock` normalization are unchanged.  This is an exact reduction
of work on the actual `ArithmeticTile.step` path, including the bounded digit
projection used by Pépin and Lucas--Lehmer validation.  The native bigint
classical ceiling remains the faster backend for large unresolved candidates.

The bounded research audit uses every residue for F2, F3, M5, and M7.  For each
source it obtains the demanded carry and harmonic functions from the actual
shared arithmetic tile and includes the terminal observer after one square:

```text
Fermat:   [square(x) = -1]
Mersenne: [square(x) - 2 = 0]
```

It then applies the shared exact unary Moore minimizer.  This requires only
`x ~ y => S(x) ~ S(y)`.  Addition and arbitrary binary multiplication are not
part of the consumer contract.

The sign control is essential.  The square action and its pulled-back terminal
observer give identical responses for `x` and `-x`.  Pépin's current-value
observer still distinguishes `+1` from `-1`; retaining that current sign in
every earlier state would be redundant because the next square kills it.

The audit publishes no scheduler certificate.  Its universe is the complete
finite residue ring only for the listed small candidates.  A stable bounded
Moore partition neither proves that the number of classes stays bounded with
width nor authorizes the Fermat/Mersenne prime bit in `TileScheduler`.  The
Pépin `-1` and Lucas--Lehmer zero observers remain distinct external theorem
outputs, and no prime-modulus assumption is used.

## Final bounded measurements

The new unary audit uses the complete residue ring, unlike the earlier
Fermat radix-orbit multiplication audit. Their class counts are not directly
comparable.

| Candidate | Exact ring states | Initial demanded consumer classes | Stable unary classes | Sign classes |
|---|---:|---:|---:|---:|
| F2 | 17 | 9 | 9 | 9 |
| F3 | 257 | 95 | 129 | 129 |
| M5 | 31 | 15 | 16 | 16 |
| M7 | 127 | 52 | 64 | 64 |

Every refined machine has zero successor conflicts and preserves all sign
pairs, including the terminal observer pulled back through the square. For
these carry/harmonic consumers, refinement nevertheless restores every
remaining sign class: the square-only experiment has not demonstrated an
additional stable collapse beyond the existing sign symmetry. In particular,
M7 still refines 52→64 under the unary contract. The stronger multiplication
requirement was not the only reason that those observers needed refinement.

The exact ring payload remains necessary inside cross-products and folding;
the lossy sign action is not used as a general coefficient-ring value.
Triangular squaring does not itself bound accumulated coefficients. On an
actual shared-tile source with bit `i` set iff `i mod 3 != 0`, after canonical
sign normalization:

| Width | Largest absolute folded coefficient, both families | Fermat observed carry interval | Mersenne observed carry interval |
|---:|---:|---:|---:|
| 8 | 3 | −1…1 | −1…1 |
| 16 | 6 | −3…3 | 0…3 |
| 32 | 11 | −5…6 | 1…6 |
| 64 | 22 | −12…12 | 2…12 |
| 128 | 43 | −23…24 | 5…24 |
| 256 | 86 | −49…49 | 12…49 |

Each step still allocates a width-sized folded coefficient field before
end-around normalization. These intervals are observed on this pattern,
not a universal admitted carry bound. Thus the proposed normalization after
every bounded product/tile contribution is a remaining construction, not a
property established by the triangular kernel. The next spatial target is
that incremental fold/carry consumer; the next temporal target is composing
its demanded functions without executing every nonlinear square.

## Deck-first terminal partition

The terminal-only consumer admits a different exact partition from the richer
carry/harmonic consumer above. Mersenne retains the ordinary `x ~ -x` square
deck because its terminal value zero is fixed by sign. Fermat's terminal value
`-1` is paired with `+1` by the square deck, so that pair must split. The dead
tail states zero and one can instead merge: both are nonterminal and remain in
that merged class under every later square. The class count therefore remains
`(N+1)/2` rather than growing by one.

The complete rings F2, F3, F4, M5, M7, M11, and M13 verify this partition. In
every row the terminal observer is constant on classes and the class reached
after 1, 2, 4, 8, 16, and 32 squares has zero conflicts. This proves a bounded
unary terminal quotient. It does not say the partition is the minimal Moore
quotient; composite M11 can have extra square collisions beyond sign.

Direct `ArithmeticTile` checks show that Fermat zero and one have the same
currently implemented bounded carry action and order-4/mod-2 harmonic
transducer on their observed incoming interval `[0,0]`. This local check does
not establish equality on a full-ring carry-port interval or for the proposed
five-dimensional forcing germ. The audit does not construct that germ and
does not claim it is constant on zero and one. The exact ring
payload remains necessary for cross-products and folding before the tested
consumer is requested.

The existing `cyclotomic_binary_lift_marker(..., sign_invariant=True)` is the
appropriate Hensel-lift view for the Mersenne deck. It cannot be used unchanged
across Fermat's current `-1` observer, which deliberately separates a sign
pair. No lift marker or bounded deck result is promoted here to a general
prime-bit or scheduler certificate.

See the frozen unary and work evidence (local artifact: `../../../results/current/continuation-growth-2026-09-10/final2/square-consumers.json`)
and actual tile width probe (local artifact: `../../../results/current/continuation-growth-2026-09-10/final2/square-width-growth.json`).

The [temporal clock proof checkpoint](../../temporal-clock-jump-proofs.md) adds checked jump and rebase
laws, including supplied affine effects, matched Hensel prefixes and known-order
square/Lucas clocks. It distinguishes these exact skips from discovery of
unknown nonlinear births and the unresolved full-germ scheduler contract.
