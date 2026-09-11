# v0.53.6 Collatz lazy-character results

- **Growth observer:** for positive odd `n`, `chi4(n)=(-1/n)` is `-1` exactly when `n ≡ 3 (mod 4)`, hence exactly when `v2(3n+1)=1` and the accelerated step strictly increases.
- **No eager valuation for growth:** `CollatzSentinelBoundarySummary.accelerated_increases()` now reads the modulo-four source sector directly and never calls `power4_valuation()`.
- **Radial/cyclotomic observer:** `CollatzRadialCharacter(order, shift)` retains only `shift = v2(3n+1) mod order`; lane `j` uses exponent `-j*shift mod order`.
- **Compressed source path:** `collatz_radial_character_word()` scans canonical radix-`4^r` runs, accumulates sentinel contribution modulo the requested order, and inspects only the bounded first mismatch. It does not construct a successor, parity word, root germ, or retained full valuation state.
- **Multiple orders:** `collatz_radial_characters_word()` computes one character at the LCM of requested orders and quotients it to every divisor order, avoiding repeated source scans.
- **Exact successor unchanged:** when the caller genuinely needs the accelerated successor or exact `k`, the existing 2-adic root/germ path remains the fail-closed exact fallback.
- **Boundary:** a Jacobi/Dirichlet character does not magically recover arbitrary `v2`; only the one-bit growth predicate is a direct `chi4` character. Higher radial phases are finite cyclic-character projections of the valuation.
- Reproducible measurements: `bench/collatz_character_probe.py` and `results/collatz_character_metrics.json`.
