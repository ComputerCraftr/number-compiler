# v0.53.3 lazy morphism / event-stream cleanup

## Scope

This release is a structural cleanup. It removes two eager expand-then-quotient paths while keeping the previously measured asymptotic frontiers explicit.

### BSGS polynomial path

The special-number Strassen/Karatsuba bend evaluator now represents the predictable products

`P(a,s,n;X) = product_{j<n} (X-(a+j*s))`

as one canonical `ProgressionProductMorphism(modulus, root_start, root_step, count)`. Adjacent blocks compose exactly; a dyadic block is the same block followed by its translated copy. The baby rising factorial uses roots `0,-1,-2,...`; giant evaluation points use one arithmetic progression descriptor instead of a materialized root list.

`ProgressionProductArena` lowers coefficients only when a remainder/support observer requires them and interns every semantic split block. Newton inverse precision now uses an explicit `NewtonPrecisionMorphism` doubling schedule. Both polynomial coefficient lowering and Collatz affine lowering use the shared production `LazyLoweringCache` from `morphism_core.py`.

This does **not** claim the first BSGS evaluation is polylogarithmic. F5 still charges 5,440 measured ring operations on the bounded control and M29 4,749; the existing BSGS asymptotic frontier remains sublinear in slot span but exponential in candidate bit length. The cleanup removes predictable operator reconstruction and repeated fixed-window work, not the unresolved first-evaluation support injector.

Measured controls:

| control | span | baby width | giant blocks | baby descriptor | giant descriptor | root lists | support |
|---|---:|---:|---:|---:|---:|---|---:|
| F5 | 511 | 23 | 22 | 72 bits | 75 bits | none | 641 |
| M29 | 399 | 20 | 19 | 64 bits | 68 bits | none | 536870911 |

The fixed F5 window packet is still object-identical on reuse: one miss, then one hit.

### Collatz event path

The old source-independent `CollatzPowerArena` remains available for exact finite E/O branch programs. It is no longer the right consumer for valuations already proved by the 2-adic root/frame machinery.

`CollatzEventArena` is the new source-derived consumer. An event with valuation `k` is represented by one leaf whose semantic transport is

`n -> (3*n+1)/2**k`

and whose compact eager summary retains only `(events=1, physical_steps=k+1, shift=k)`. The event validity proof stays with `RationalPadicRootGerm` / `CollatzAffineSuffixGerm`; the event arena deliberately does not rebuild the equivalent `k+1`-bit residue certificate.

Concatenation is also lazy. A multi-event node stores two interned child morphisms and additive counters. The potentially large affine multiplier/addend carrier is materialized only through the explicit `materialize_cocycle()` lowering boundary and is memoized by `LazyLoweringCache`. Normal execution can use `apply_exact()` through event leaves without building that carrier.

`collatz_affine_suffix_event_power_word/value()` now streams the valuation generator directly into the event arena. It constructs no valuation tuple, parity word, E/O itinerary, dyadic residue certificate, or eager multi-event affine offset.

`CollatzValuationSchedule` similarly keeps one entry per accelerated odd event. One valuation `k` summarizes normalized parity run `1,0**(k-1)` and physical branch run `O,E**k`; `CollatzParityTimeOperator.apply_valuations()` locates physical time by binary search over event prefixes rather than by materializing the parity integer.

Measured controls:

- seed 27, 32 accelerated events: 76 expanded physical E/O symbols reduce to 32 event leaves; balanced event composition uses 31 compositions versus 75 branch compositions, with identical final target;
- valuation `k=1,000,000`: one event node, 41-bit operator summary, 1,000,001 represented physical steps, zero affine-cocycle materializations;
- a one-million-digit radix-4 sentinel source followed by digit 3: two root-germ events represent total dyadic shift 2,000,005 with three reachable operator nodes, 44-bit root summary, and zero affine-cocycle materializations;
- one-million valuation physical-time schedule: one event entry, 21-bit description, one binary-search comparison bound; no million-bit parity word exists.

## Honest frontier

This cleanup removes work proportional to **forced run length** that was being expanded and compressed again. It does not prove that arbitrary future Collatz valuation events can be synthesized in polylogarithmic event count, and it does not make the first unseen BSGS support packet polylogarithmic. Those remain separate research targets.

Production special-number theorem resolution remains bounded by the exact Pépin/Lucas--Lehmer ceiling from v0.53.0. No tropical factor-slot scan is reintroduced.
