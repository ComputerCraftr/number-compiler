# Projection-field algebra results

v0.23 applies radix/cyclotomic/binomial algebra to projection **outputs**, not only source growth state.

## Reverse-add output closure

| seed | steps | exact current actions | repeats | different-next conflicts | transformed-feature conflicts |
|---:|---:|---:|---:|---:|---:|
| 195 | 256 | 256 | 0 | 0 | 0 |
| 196 | 256 | 255 | 1 | 1 | 1 |
| 197 | 256 | 256 | 0 | 0 | 0 |

Seed 196 supplies an exact counterexample to projection-only Markov closure: the same current carry-action projection occurs at consecutive steps but has different next projections.  Lossless re-encodings of that same output cannot fix the missing hidden-source information.

## Collatz valuation output

| seed | symbols | runs | sum(k) | raw bits | RLE bits | theorem bits | exact slab bits | slab comps |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 27 | 41 | 25 | 70 | 62 | 482 | 170 | 94 | 64 |
| 97 | 43 | 26 | 75 | 66 | 514 | 170 | 99 | 68 |
| 871 | 65 | 39 | 113 | 99 | 720 | 175 | 139 | 100 |
| 6171 | 96 | 58 | 165 | 145 | 1147 | 175 | 193 | 150 |
| 837799 | 195 | 111 | 329 | 290 | 2032 | 180 | 361 | 294 |

Equal valuation runs power in logarithmic composition depth and fixed odd-modulus affine projections are constant-size.  The exact slab payload still grows with independent itinerary information.

## Prime output fields emitted pre-bitmap

| candidates | primes | first | least-factor runs | least-factor RLE bits | Boolean theorem bits | theorem comps | decision nodes | charged research projection work |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 64 | 3 | 13 | 64 | 1412 | 175 | 336 | 9 | 22363 |
| 256 | 25 | 13 | 254 | 5944 | 185 | 1360 | 26 | 24286 |
| 1024 | 125 | 13 | 1012 | 21097 | 195 | 5280 | 53 | 31446 |
| 4096 | 503 | 13 | 4049 | 81415 | 205 | 21136 | 178 | 58901 |

The least-factor label field is nearly run-incompressible, while the prime Boolean primary/binomial/cyclotomic theorem channels remain small and can be emitted directly from the residual-divisor DAG.  They are optional because they add charged work when `(count, first)` alone is requested.

## Fermat / Mersenne projection-value closure

Small individual cyclotomic digit channels merge residue states, but they fail target separation or next-step closure.  On the bounded exact audits, combining enough primary/binomial/cyclotomic channels to make the target exact and next-closed becomes injective, reconstructing the full residue state.  The already-known Moore target observer remains small; extracting its class cheaply is the blocker.

