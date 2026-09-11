# Exact state reductions and cross-domain propagation (v0.43.0)

The release distinguishes exact local/action reductions from closed temporal quotients.
A compact current projection is never promoted to successor state unless its transition closes.

## Reverse-add growth: boundary valuation replaces the carry row

For symmetric pair polynomial `P`, let `R=P-(b-1)(1+z+...+z^(L-1))` and
`r=v_z(R)`.  The sign of the first nonzero coefficient of `R` is exactly the terminal
carry/growth bit because the final non-neutral reset is its symmetric mirror.

| base | width | symmetric pair states | growth states | source bits | reduced bits |
|---:|---:|---:|---:|---:|---:|
| 3 | 8 | 625 | 9 | 10 | 4 |
| 10 | 8 | 130,321 | 9 | 17 | 4 |
| 10 | 32 | 288,441,413,567,621,167,681 | 33 | 68 | 6 |
| 16 | 64 | 529,144,398,052,420,314,716,929,933,900,838,757,437,386,767,361 | 65 | 159 | 7 |

On 196/256 steps: max pair width **113**, max growth-state charge **15 bits**,
max full reset-signature charge **554 bits**, max canonical half-pair payload **285 bits**.
Growth differential exact: **True**.

The boundary state is intentionally not a full successor state.  Cross-seed closure gives
**8,178 conflicts** over 1000 seeds x 32 steps.

## Collatz: valuation is the exact accelerated action/position state

Across 32,768 odd sources through 65,535, only **16** valuation states occur
(maximum `k=16`; 5 charged value bits versus 16 source bits).
The same `k=v2(3n+1)` determines increase/nonincrease and every cyclotomic shift phase `k mod m`.
Action differential exact: **True**. It is not a closed orbit state: **28,669** next-valuation conflicts.

## v0.41 propagation audit

| domain | v0.40 work | v0.41 work | exact semantic result |
|---|---:|---:|---|
| 196 bootstrap carry normalization (64 transitions) | 128 scans | **64 scans** | unchanged |
| prime factor candidates (4,096 odd candidates) | 3,162 | **1,581** | 446 canonical lanes |
| prime factor-generator gcd calls | 18,635 | **17,054** | 503 primes, first offset 13 |
| Collatz nested divisibility/lane API | duplicate observer | **deleted** | canonical direct `v2(3n+1)` unchanged |

The Fermat/Mersenne group-depth theorem does **not** automatically transfer to 196 or Collatz:
their compact growth/valuation projections have successor conflicts, so replacing their real state with a saturated depth counter would be unsound.
For primes, the transferable idea is earlier quotienting of impossible divisor branches and residual-set actions; the odd-candidate parity branch is now removed before gcd work.

The bounded special-number carrier proof remains single-sourced in `devtools/proofs/oracles/special_binary_jump.py`; the obsolete over-refined special character state was deleted rather than propagated.
