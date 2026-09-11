# Temporal clock jump proofs — September 10

The [September 11 endpoint-seam extension](endpoint-seam-powering-audit.md)
now discharges the successor premise for exact endpoint images, adds the
nested-cylinder/depth-germ laws, and records fresh powered image and cache
measurements. The following sections retain the earlier checkpoint's scope.


This checkpoint formalizes the temporal composition laws separately from the
remaining nonlinear evaluator. It adds the `Temporal_Clock_Jumps` Isabelle
session and executable A1…A1024 checks using existing canonical composition
owners. No production scheduler certificate is changed.

The [clock-coordinate follow-up](clock-coordinate-growth-audit.md) extends this
session with normalized phase truncation, signed Collatz mismatch tangents,
the stable inverse-three radix-64 lift, and the corrected decimal growth-phase
rebase. The validation below records the original checkpoint; fresh evidence
for the extension is tracked separately.

## Proved interfaces and their premises

| Family/interface | New result | Information required before a jump |
|---|---|---|
| General clocked quotient | One-step congruence extends to every duration; phase readout commutes with iteration | A proved successor-respecting projection on the complete admitted state |
| Canonical rebase | Normalize at every temporal seam or only at the destination with the same result | `NF(step(NF(x))) = NF(step(x))`; idempotence alone is insufficient |
| 196 primary forcing | Exact affine squaring and source death after any nine growth/no-growth transports | The admitted forcing action or composed block effect, including its births |
| Collatz | Exact affine block composition, additive physical ticks, suffix rebase, matching Hensel-prefix skips | The branch valuation action/itinerary and the surviving spatial suffix |
| Fermat | Arbitrary-duration squaring equals the dyadic exponent clock; sign is dead after the first square | The ring value/action and correct placement of the current `-1` observation |
| Mersenne | Lucas trace iteration is the readout of a norm-one pair under dyadic powering | A norm-one lift in the admitted ring; construction of that lift is separate |

The new theories are in
[`devtools/proofs/isabelle/temporal_clocks`](../devtools/proofs/isabelle/temporal_clocks).
Each theory rejects oracle dependencies. They contain no admitted `sorry`
proofs. These formal statements are algebraic specifications, not a proof of
Python extraction or of the full carry/fold/Newton/Hasse consumer implementation.

## Exact skip law and representation

A supplied affine effect is represented by two ring elements `(A,B)` and acts
as `x ↦ A*x+B`. Chronological composition is

```text
(A1,B1) ; (A2,B2) = (A2*A1, A2*B1+B2).
```

`dyadic_effect_jump` proves that k shared squarings of this effect equal
`2^k` iterations. No midpoint germ or child effect is part of the result type.
`dyadic_compositions_exact` counts k squarings. The generic Python binary-power
owner additionally charges one identity composition, so the supplied-affine
regression expects k+1 calls rather than changing accounting to match a desired
number. Ring-element size and multiplication cost are separate from that count.

For a quotient, `quotient_jump` derives arbitrary-duration congruence from its
one-step homomorphism. This is the theorem needed once the all-port action has
been established. It does not assume that the proposed complete germ already
satisfies that premise. Likewise `normalize_at_every_seam` makes the missing
`ConsumeGeometry → Trop → Canon` obligation explicit rather than disguising it
as an unconditional theorem about an undefined normalizer.

The finite terminal-deck regression compiles F2/F3/M5/M7 once, then builds A1,
A2, A4, …, A1024 with exactly 0, 1, 2, …, 10 shared table compositions. Every
source residue agrees with the independent recurrence oracle. Point-action
application and the arithmetic tile primitive are poisoned during powering.
Each effect has exactly `|Q|` transition entries at every level; the arena has
at most 12 retained tables. This is genuine O(|Q| log N) table-composition work
after finite compilation. It is not an O(log N) construction of a quotient for
an arbitrary-width number. The ring-wide compilation cost is deliberately
outside, and reported separately from, the jump.

## Decimal spatial clock versus temporal clock

The implemented period 128 is the order of `z=y-1` in the local primary ring.
It reduces **spatial width** in `z^width`. Temporal transport instead uses 2
for no growth and y for growth. Consequently `N mod 128` cannot replace a
state-dependent temporal growth/birth action.

The neutral old-source multiplier after a growth itinerary is

```text
2^(number of no-growth events) * y^(number of growth events).
```

With `2^5=0` and `y^5=0`, every nine-event itinerary annihilates it. The eight
transports consisting of four no-growth and four growth events leave `16*y^4`,
which is nonzero in the implemented primary ring. This explains why the earlier
broad trajectory's evaluated eight-step death and a uniform operator theorem
are different statements. The full pair-field event-memory bound is also a
different carrier; its larger horizon is not contradicted by this jet theorem.

A killed old contribution can be discarded, but new births remain inputs.
Equal current carry cylinders with the same width and spatial phase are not a
complete temporal state: `(4,4)` and `(8,8)` have equal all-port cylinders but
successors `(8,8)` and `(16,16)` with different exits. This does not reject the
attachment's richer accumulated innovation and exact spatial-image payload.
It shows precisely why that payload or a successor-complete consumer of it
must discharge the quotient/rebase premise.

## Collatz clock and rebase

An admitted accelerated block is the relation

```text
3^h*x + C = 2^K*y.
```

The formal composition adds h and K and combines offsets as
`C = 3^h2*C1 + 2^K1*C2`. It preserves actual branch equations and adds physical
odd-plus-halving ticks. It does not infer that a chosen K is the true valuation;
that remains a property of the admitted input cylinder/action.

The suffix rebase theorem proves

```text
A*M+b = A0*((A div A0)*M + b div A0) + b mod A0
```

when `A0` divides A and is nonzero, with canonical remainder bounds for positive
A0. It consumes affine representation history without identifying distinct
suffix occurrences. The arbitrary-prefix theorem removes h matched bits in one cylinder
transformation; its radix-64 corollary removes k matching symbols and 6*k
precision bits. One- and two-symbol composition controls are retained, and
canonical mismatches have empty live cylinder intersection. These are exact
skips of an admitted matching prefix,
not a proof that future valuation symbols can be discovered without inspecting
the demanded occurrence.

The existing shared-root counterexample still matters: the same root action
with distinct suffixes can emit different valuations. The root alone is not
the spatial occurrence. Finite nilpotent forcing lifetime does not make that
valuation consumer constant.

## Power-number clocks and the cost distinction

Fermat has the exact ring identity `T^N(x)=x^(2^N)`. Lucas–Lehmer has
`T^N(u+v)=u^(2^N)+v^(2^N)` when `u*v=1`. The proof works in any admitted
commutative ring; it does not assume that every trace has a lift in the base
ring. A quadratic extension or an existing circle construction must supply it.
Fermat's current `-1` observer remains separate; its pulled-back observer after
a square is sign invariant.

Writing an exponent as `2^N` does not make its evaluation logarithmic in N:
ordinary modular exponentiation sees N+1 exponent bits and generally executes
N squarings. The existing trace evaluator also walks N nonlinear updates.
The new `dyadic_clock_known_order_reduce` theorem proves that, when a positive
period r satisfies `x^r=1`, the exponent can be reduced to `2^N mod r`. The
shared modular-power owner computes this with O(log N) compositions on bounded
mod-r values, without constructing `2^N`. The corresponding two-coordinate
theorem applies to the norm-one trace. Fresh controls use duration
`10^100+17`, with checked orders 256 modulo 257 and 7 modulo 127. Neither test
assumes an unproved primality result or claims to discover an unknown order.

A compact order-depth clock can avoid that work only after its terminal and
full demanded-consumer congruence has been proved. The finite deck-table jump
above supplies that guarantee for its stated bounded terminal consumers;
the full polynomial-germ quotient still needs the all-port rebase construction.

## Validation

The [evidence directory](../results/current/temporal-clock-proofs-2026-09-10/README.md)
records the accepted Isabelle session, oracle checks, frozen source/theory
hashes, guarded Python tests and repository checks. Failed development builds
are retained separately and are not credited as proofs. All heavy commands
use the unchanged 35-second/1-GiB guard.

Final validation: all four new theories pass the clean Isabelle session with
no oracle dependencies; 80 selected Python tests, strict mypy across 1,189
files and Ruff pass on the frozen source recorded in the manifest.
