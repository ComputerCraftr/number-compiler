# Two-primary image filtration — v0.50.0

The canonical Fermat/Mersenne certificate state is now the **successor-image
filtration itself**, not a prime-only depth object plus a separate composite
fallback.

`TwoPrimaryImageFiltration` represents both cases:

- pure prime-style candidates: image depth is exactly the Moore/target quotient;
- composite candidates: the same object retains the stable residual and records
  that image depth is **not** the target quotient.

## Exact bounded controls

| family | parameter | image ranks | stable | Moore classes | depth classes | Moore=depth | status | bounded states examined |
|---|---:|---|---:|---:|---:|---|---|---:|
| Fermat | 4 | 2049,1025,513,257,129,65,33,17,9,5,3,2,2 | 2 | 12 | 12 | yes | prime | 65,537 |
| Mersenne | 11 | 1024,460,282,196,196 | 196 | 3 | 4 | **no** | composite | 1,024 |
| Mersenne | 13 | 4096,3072,2560,2304,2176,2112,2080,2064,2056,2052,2050,2049,2048,2048 | 2048 | 13 | 13 | yes | prime | 4,096 |

This locks the old M11 regression: a composite stable residual can no longer be
interpreted with the pure timestamp formula.

## Pure theorem specialization

`pure_two_primary_image_filtration()` returns the *same semantic object* from the
closed group theorem with **zero carrier enumeration**.  On F4/M13 its image
ranks, finite-depth strata and target depth match the independently constructed
bounded candidate exactly.

That theorem remains conditional: it describes the dynamics after the candidate
has established the pure two-primary shape; it is not a primality classifier.

## Scalable character boundary

The only currently proved scalable candidate query is the outer source boundary:

- Fermat: `Jacobi(3,F_n)=-1` proves the canonical source is not a square;
- Mersenne: the sign-invariant `Jacobi(6,M_p), Jacobi(-2,M_p)` boundary proves
  the trace source has no predecessor.

Both M11 **and** M13 satisfy that outer Mersenne boundary.  Therefore it cannot
classify prime vs composite candidates.

`higher_two_power_character(..., level>=2)` now raises
`HigherTwoPowerCharacterUnavailable`.  Production is forbidden from replacing
that missing reciprocity theorem by repeated squaring, carrier enumeration,
factor-backed CRT truth data, or a prime label while calling the result
"scalable".

The remaining theorem is therefore exact and narrow: construct deeper
candidate-derived image/residuosity characters (or an equivalent symbolic
stable-residual descriptor) without recurrence-equivalent work.  Until then,
bounded certificates stay exact and large certificates stay `unknown`.
