# Collatz radix-64 carry/output quotients

The radix-64 sentinel evaluator derives multiplication carry from the five
carry domains, then exposes separate directional value views. Symbolic output
functions compose through the existing reduced finite-function arena. The
verified 17-class raw output partition remains a diagnostic observer; it is
excluded from action construction. These are quotients for declared local
observations. They are not a certificate
for the reported 89-state or 1,636-state universal temporal machines.

## Control and value have separate roles

For source digit `d` and incoming carry `c in {0,1,2}`, let

```
c' = floor((3*d+c)/64)
o  = 3*d + epsilon
epsilon = c - 64*c'
```

`collatz_output_quotient.py` uses the generic ternary digit carry law in
`collatz_carry_wires.py` as the canonical owner of dyadic action tables.
At radix64 this agrees with the existing two-wire factorization. Fixed
primitive tables contain no source bindings or temporal state. The nine
corrections are `-128,-127,-126,-64,-63,-62,0,1,2`.

Two digits share a raw class exactly when their current carry actions agree
and, for all three incoming carries, both their outgoing carry and their raw
output carry domain agree. This induces precisely these classes:

```
[0,6], {7}, [8,13], {14}, [15,20], {21},
[22,27], {28}, [29,34], {35}, [36,41], {42},
[43,48], {49}, [50,55], {56}, [57,63]
```

The separate value potential is `p=d-min(class)`, bounded by six. The exact
raw output is the representative output plus `3*p`. A class ID alone is not
an exact output value. This primitive offset is not the proposed, unverified
41-valued potential for a universal two-event machine.

`CollatzOutputMorphism` maps source functions to geometry-derived carry and
exact value functions. Requested correction and diagnostic class views are
separate observers. Directional domain consumers pair the generic left/right
actions as `R ∘ L` without constructing an exact joined digit. No possible
digit sets or enumeration of composed register valuations is used. Equality
is equality of canonical finite functions with the same signature and validity
domain; no active future-class ID is manufactured.

The [Collatz research synthesis](../research/collatz.md) records the
shared orientation maps, workbook collision regressions, and the scoped
normalized Hensel angular clock.

The four domain sequences `(000,111,011)`, `(000,112,011)`, `(000,111,112)` and
`(000,112,112)` produce the same complete carry/correction morphism for all
incoming carries. These aliases are checked using canonical function IDs.
They do not imply equal exact digits when the homogeneous source values differ.

## Shift and growth constraints

The residual shift `0 <= e < 6` is exactly

```
y_i = (o_i >> e) + ((o_(i+1) mod 2**e) << (6-e)).
```

The complete value functions must reach this wiring. Digits 0 and 5 share one
raw class, but with incoming carry 1 their raw values are 1 and 16. With adjacent
raw output 21 and shift 3, the results are 40 and 42, with different carry
domains. The two-event tests retain this distinction.

An EQ source digit (21 or 42) always emits non-EQ raw output. Other source
digits can create raw EQ: digit 7 with carry 0 emits 21. Consequently there is
no rewrite saying that all EQ is created only at shift seams, or that an EQ
source position cannot coincide with an EQ final target position.

The terminal carry is only 0, 1 or 2. An additional top digit is `carry >> e`:
at phase zero it can be 1 or 2, at phase one only 1, and at phases two through
five it is absent. Every nonempty growth edge has the LT carry domain. Its
value stays on the output wire; there is no generic 64-valued growth controller.

## Connected execution and temporal composition

For canonical radix-64 source words,
`accelerated_collatz_sentinel_step_digits(..., base=64)` now calls the new
streaming controller. The existing handling of other radices and noncanonical
zero-padded input remains available through the previous evaluator.

Each `Radix64CollatzStage` strips its low sentinel frame, determines the
residual phase, and consumes the raw quotient and value potential. Its value
lookahead is one digit. Finalization uses the restricted growth rule and
handles the all-sentinel source explicitly.

`compose_radix64_events(digits, events)` connects these stages with iterative
digit forwarding. It constructs no intermediate integer or digit collection;
only the requested final endpoint is collected. Sentinel cropping for each
following event happens as its input arrives. The default 64-event budget is
checked before reading the source or allocating stages. Stage instances are
transient execution state, not semantic cache keys or lazy result payloads.

Exact accumulated valuation `K`, input frame, residual phase and exit frame
are returned as metadata. For admissible framed sources
`n_q=64**q*m+(64**q-1)/3`, increasing `q` by 192 leaves the normalized target
unchanged and increases exact valuation by 1152. The two-event regression
checks this while preserving the exact weight difference.

This streaming pipeline uses one stage per requested event; it does not give
logarithmic powering or minimize the complete temporal controller. Symbolic
local composition reduces its functions, but does not certify whole-event
phase/extent admissibility. The existing public binary powered Collatz kernel
is not replaced by this radix-64 implementation.

## Evidence and remaining work

Tests prove the complete raw partition, exact affine reconstruction, every
primitive carry assignment, all 24,576 raw two-cell/phase shift assignments,
and all 18 growth cases. They check symbolic carry/correction aliases, local
temporal composition, invalid sorts and budgets, independent ownership and
payload audits, and live routing with the previous raw-field builder poisoned.

Streaming one-, two- and four-event results agree with independent arithmetic
on boundary witnesses and deterministic random sources through 2,048 bits.
Two-event execution also agrees for all 2,048 positive odd sources below 4,096,
covering all six residual phases. Existing sentinel differential tests provide
additional cross-radix validation.

Universal temporal minimization, an authenticated affine-register update law
for the claimed two-event potential, Frobenius reduction of that register,
and bounded growth through repeated temporal squaring remain open. The supplied
state counts and terminal-halo bounds are not compiler guarantees.

## Carry-domain and Hensel validation — September 10

The [September 7–13 retrospective validation checkpoint](../../results/history/2026-09-07--2026-09-13/README.md)
adds `tests/validation/research/collatz/test_carry_domain_hensel_quotient.py`.
It is research evidence only; no new production identity is admitted.

The five primitive carry actions have fibers `21/1/20/1/21` across the 64
digits. This `64 -> 5` current-domain partition is different from the
`64 -> 17` raw-output observation partition above. Factoring the divided
output domain through its two adjacent input positions gives left/right
class counts `(5,1), (5,2), (5,4), (5,5), (4,5), (2,5)` for phases zero
through five. Each complete primitive table is checked, not only its count.

The full EQ regression uses source 58723, with radix-64 digits `(35,21,14)`.
The accelerated output is `(21,32,21)` and the following frame crop removes
one low sentinel, leaving `(32,21)`. Position one is EQ both before the event
and after the crop. A raw-output-only EQ argument cannot authorize a rewrite
on the complete temporal path. The growth check covers every positive odd
16-bit source, including the empty normalized field of an all-sentinel input.

For normalized source m and residual phase e, the next valuation pulls back
exactly to `v2(9*m + 3 + 2**e) - e`. `RationalPadicRootGerm` obtains it from
the source radix-4 word while successor-word construction entry points are
poisoned. The finite refinement additionally records the angular germ's
multiplier and offset. Source values 15 and 19 share the domain-output key
but have next valuations 1 and 3. Nevertheless, 129 and 385 share the entire
refined key `(next valuation, multiplier, offset) = (2,36,1)` together with
the same domain-output record; their targets 97 and 289 have different keys.
This is an explicit successor-congruence failure.

With q=0 for all 1,984 current sources (positive odd integers below 4,096
whose low digit is not 21), the observations give:

| Observation | Classes | Sources in conflicted fibers | Conflicted classes |
|---|---:|---:|---:|
| Domain output | 792 | 1,707 | 522 |
| Domain output + finite Hensel/angular output | 1,024 | 1,476 | 524 |

The domain-output key includes the current geometry, all three carry-port
raw-domain outputs and carry exits, residual division phase, growth edge,
next frame crop and cropped successor geometry. Source frame depth stays
outside identity. Each of the six residual phases is also tested at frame
depths 1, 193 and 385: keys and exact targets agree while valuations differ
by 1152 between adjacent depths.

These results locate the remaining obligation at a recursive, self-advancing
value-output morphism and its complete context transition graph. Domain
geometry already determines the carries. One finite Hensel boundary
coordinate improves the observation partition but does not finish it.
