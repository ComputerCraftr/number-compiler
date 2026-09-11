# Shared arithmetic square tiles

Fermat and Mersenne bounded digit recurrence execution shares one
`ArithmeticTile`.  The tile stores one canonical `CyclotomicDigitBlock` in the
full boundary quotient `X**w-sign`; family and width are its only independent
policy fields.  The minimal exact forward coefficient precision is derived:

| family | operation | boundary | angular order |
|---|---|---|---:|
| Fermat | `x -> x^2` | negacyclic, sign -1 | `2w` |
| Mersenne | `x -> x^2 - 2` | cyclic, sign +1 | `w` |

Each step sign-canonicalizes its input, calls the shared adaptive convolution,
reduces through the block's canonical quotient ring, signed-lifts the exact
folded coefficients, and calls the shared `RadixCarryBlock` end-around
normalizer.  The next canonical block is built directly from the normalized
digits.  The old family-specific cyclic and negacyclic projection entrypoints
are no longer on this execution path, and all convolution and carry work is
still charged.

The shared square convolution now has a square-specific triangular kernel.  A
leaf computes each unordered digit pair once, doubles cross terms, and charges
that doubling as an addition; recursive blocks use three subsquares.  It does
not route a square through the general two-input multiplication kernel.  This
reduces actual bounded digit-projection work while preserving the same fold,
carry normalization, and operation metrics.

`SquarePrecisionMap` represents forward coefficient precision.  It is a
separate type from the Collatz Hensel pullback and has no inverse-3 coordinate.
This prevents the common arithmetic interface from conflating square
precision with valuation-dependent Collatz division.

The canonical digit carrier is bounded to callers that requested the digit
projection.  The production `classical_ceiling` shares `SquareTileAction` but
applies it through native integer modular arithmetic: replacing its hard speed
ceiling with Python coefficient fields would make large unresolved candidates
slower.  Only the bounded diagnostic path has the canonical spatial tile and
detailed convolution accounting.

This does not claim compact temporal powering.  Squaring is nonlinear, and
the tile executes one primitive operation for each Pépin or Lucas--Lehmer
recurrence step.  Consequently:

- `arithmetic_tile_steps == iterations` for the bounded digit projection;
- `scheduler_compositions == 0`;
- no `TemporalFamilyCertificate` is issued for Fermat or Mersenne; and
- the terminal étale/prime bit remains an external output observer.

The deterministic terminal germ depth now uses the shared `SquareTileAction`.
It retains one `QuadraticPower`; `span` is derived from that power's depth
instead of being stored a second time.  Its binary composition count is
logarithmic, while `apply` remains truthful: Fermat uses the multiplicative
power operation and Mersenne trace application performs the represented
primitive trace squares.  This structural action is not a `TileScheduler`
certificate.

The shared `TileScheduler` can accept this arithmetic only after a
successor-congruent finite interface and a power-number family certificate are
proved.  Wrapping the primitive loop in a scheduler adapter would not reduce
work and would falsely imply that dyadic temporal composition is closed.

The tile does not contain the terminal prime bit.  Pépin's `-1` and
Lucas--Lehmer's zero test remain external output observers.  A finite étale
projection can justify an observer or an early structural result, but cannot
by itself decide primality over an unresolved composite modulus.

The persistent block's explicit factor is the full boundary polynomial.  It
must not be passed off as an irreducible étale factor.  When an angular or jet
consumer is demanded, `angular_view` reprojects the canonical digits into a
standard factor-free `CyclotomicDigitBlock`; finite-field primary splitting,
when valid, starts from that observer and is never stored back into the tile.

The [future-consumer audit](../future-consumer-cleanup.md) also requests
`step_with_harmonic_consumer` to compile a carry/cyclotomic action from the
actual transient folded product. `step_with_carry_interval` separately derives
admitted carry bounds when needed; ordinary steps do not perform that scan.
Neither observer is retained in the next tile. All measured bounded carry and
harmonic partitions still have successor conflicts.

The executable owners are
[`arithmetic_tile.py`](../../src/number_compiler/arithmetic/polynomials/arithmetic_tile.py),
[`digit_power.py`](../../src/number_compiler/sequences/power_numbers/digit_power.py),
with the separate native speed ceiling in
[`classical_ceiling.py`](../../src/number_compiler/sequences/power_numbers/classical_ceiling.py).
The bounded square-only congruence evidence is documented in
[`square-consumer-congruence.md`](../research/power-numbers/square-consumer-congruence.md).
