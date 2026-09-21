# Shared arithmetic square tiles

Fermat and Mersenne folded square arithmetic shares one
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

The canonical digit carrier is bounded to callers that request a digit
projection. Research-only recurrence runners use `SquareTileAction` through
native modular arithmetic or the diagnostic digit tile. They live under
`devtools/proofs/oracles`; production cannot import them or select them as a
fallback classifier.

One tile step is one primitive square or trace-square. It does not establish
compact temporal powering. The diagnostic runner charges every primitive
step, issues no `TemporalFamilyCertificate`, and performs no scheduler
composition.

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

The tile does not construct the terminal prime bit. Production classification
requires the candidate-derived admitted shadow action and a proved recovery
predicate. The supplied-root primary carry key alone does not provide that
binding. The missing recovery remains a
[Fermat/Mersenne release gate](../research/fermat-mersenne.md).

The persistent block's explicit factor is the full boundary polynomial.  It
must not be passed off as an irreducible étale factor.  When an angular or jet
consumer is demanded, `angular_view` reprojects the canonical digits into a
standard factor-free `CyclotomicDigitBlock`; finite-field primary splitting,
when valid, starts from that observer and is never stored back into the tile.

The [shared research synthesis](../research/shared.md) also records
`step_with_harmonic_consumer` to compile a carry/cyclotomic action from the
actual transient folded product. `step_with_carry_interval` separately derives
admitted carry bounds when needed; ordinary steps do not perform that scan.
Neither observer is retained in the next tile. All measured bounded carry and
harmonic partitions still have successor conflicts.

The arithmetic owner is
[`arithmetic_tile.py`](../../src/number_compiler/arithmetic/polynomials/arithmetic_tile.py).
The research-only runners are
[`special_digit_power.py`](../../devtools/proofs/oracles/special_digit_power.py)
and [`special_classical_ceiling.py`](../../devtools/proofs/oracles/special_classical_ceiling.py).
The bounded square-only congruence evidence is documented in
the [Fermat/Mersenne research synthesis](../research/fermat-mersenne.md).
