# Port-valued Mealy actions

The common spatial quotient for carry and harmonic forcing is a single Mealy
response

```text
incoming port -> (outgoing port, emission).
```

The outgoing carry is the endpoint projection of that response. It is not a
second state field beside the harmonic emission. For two adjacent blocks, the
right block consumes the endpoint produced by the left block, while its
emission is shifted by the left block's spatial span before addition.

The Isabelle theory `Port_Valued_Mealy` proves this semidirect composition is
associative whenever the external span shift is an additive action. It also
proves that forgetting emissions is a homomorphism onto endpoint composition,
and that applying the same external clock/germ shift commutes with spatial
composition. Thus changing or restricting a demanded emission view cannot
change the derived carry view.

For decimal reverse-and-add, a monotone Boolean endpoint has exactly the three
possible rows `00`, `01`, and `11`, corresponding to constant-zero, identity,
and constant-one carry behavior. The same generic endpoint projection supports
the three reachable Collatz ports `0,1,2`; a separate theorem proves that
composition preserves that admitted port set.

This is a spatial theorem only. The known `(4,4)` and `(8,8)` decimal pair
fields are an exact temporal warning: both incoming ports give the same current
carry tracks and hence the same carry-derived forcing cylinder, while their
successors have LT and GT exits respectively. Endpoint projection and spatial
Mealy composition therefore do not establish successor closure. A temporal
quotient must retain whatever richer value consumer separates that future
behavior, and its closure needs its own proof.

The formal checkpoint is
[`Port_Valued_Mealy.thy`](../devtools/proofs/isabelle/Port_Valued_Mealy.thy).

## Shared implementation

[`JetPortCylinder`](../src/number_compiler/arithmetic/carry/jet_cylinder.py)
owns port substitution and shifted jet addition. It stores only the modulus
and complete response rows. No independent domain, reset, predecessor word,
width or phase enters cylinder equality. Row counts support decimal Boolean
ports and Collatz's three ports. The carry monoid supplies the validated
`carry_fn_from_outputs` projection; its constant-size endpoint specialization
remains available when a consumer does not demand an emission.

Both Collatz harmonic implementations now use this composition owner.
`WireResponse` stores its two extensional rows; `fn`, `constant` and `linear`
are derived views. The bit-output action uses the same row owner and operation.
Their mod-8 and mod-4 clocks remain external context. The threshold test checks
all 64 leaves against five exact cylinders, then checks their 25 products
instead of repeating 4,096 digit pairs. The richer output-jet test retains all
4,096 pairs.

[`DecimalCarryJetBlock`](../src/number_compiler/arithmetic/carry/decimal_jet_cylinder.py)
binds spatial width to a two-port cylinder with occupancy emission
`P=J5(C[i])` modulo 32. Its following-carry jet is derived as

```text
J5(C[i+1]) = z^-1 (P - incoming + outgoing*z^L).
```

Reset is `J5(C[i+1])-P`; normalization forcing is `P-10*J5(C[i+1])`.
Reflection and the growth edge give the exact physical reverse/add forcing jet
without building a carry tape or forcing word. Growth is the incoming-zero
endpoint projection. Tests cover every word of the three carry classes through
width five under both ports, and spatial squaring to width `2^80` with source
constructors poisoned.

Internal boundary queries still need the admitted child occurrence/cylinder
tree: a finite root emission does not identify arbitrary child decompositions.
The temporal counterexample above applies to cylinders computed from **current
carry-derived forcing**. If a proposed live `eta` additionally contains
accumulated value-dependent forcing, its initialization and admitted temporal
substitution need their own exact definition and proof. The spatial theorem
does not reject that richer construction or the exact image payload proposed
in the attachment. It does prevent inferring temporal closure from endpoint
projection alone. General radix-dilation/germ pullbacks likewise are not proved
merely by the theorem for additive external shifts.

## Collatz occurrence normalization shares actual cache entries

The Hensel carrier now normalizes `2^a*3^h*M+b` to `2*3^h*M'+b'` before
interning and when publishing a successor:

```text
A = 2*3^h
b' = b mod A
M' = 2^(a-1)*M + floor(b/A).
```

A finite radix-four carry transducer updates counted runs without exporting
the endpoint integer. A million-quarter fixture remains two runs. Exact suffix
extent and logical time remain occurrence coordinates. The bounded adversarial
probe takes 3,160 equivalent raw representations to 1,280 retained occurrences
and **1,880 actual carrier interner hits**. Its 864 distinct integer values are
not keys; cross-h and exact-extent distinctions remain separate.

In the normalized h=2 chamber, the six U(9) states have the tested three-quarter
cycle with radix-64 symbols 7, 14, 28, 35, 49 and 56. Exact roots outside that
admitted chamber are not replaced by their mod-9 residues.

This normalization removes duplicate representations of the same affine
occurrence. It does not make first-use temporal discovery sublinear, reset h
to two after arbitrary powers, or install accelerated Hensel actions in the
physical CLI scheduler. Composed spatial-image publication/rebasing remains
a separate execution boundary. Stronger closure and resource gates remain.

See the [guarded proof and measurement evidence](../results/current/port-valued-mealy-2026-09-10/README.md).

## Broad phase-neutral decimal audit

`devtools.proofs.decimal_clock_cylinder_audit` composes this same neutral
operator across 96 exact transitions for every decimal seed from 176 through
216. It checks 88,930 source positions, 3,936 carry-owned forcing events and
84,994 internal spatial compositions against the independent pair-step and
primary-jet oracles. The seed-196 control separately checks 4,096 forcing
events. The decimal leaf alphabet still interns to three cylinder rows.

The audit keeps two death measurements separate. On these trajectories the
*evaluated contribution* of the original source jet vanishes within eight
steps. The phase-neutral affine operator's kernel can require nine steps to
become identically zero for every possible input jet. Binding the evaluated
five-component vector into cylinder identity would therefore turn external
clock context back into state and lose aliases. No orbit quotient for that
external context is asserted here.

The decimal clock now uses the exact 128-phase table rather than repeated
binary powering. See the [CLI and cross-family checkpoint](cli-clock-cylinder-cleanup.md)
for the new output paths, bounded deck audit and remaining growth locations.

The [temporal clock proof checkpoint](temporal-clock-jump-proofs.md) adds checked jump and rebase
laws, including supplied affine effects, matched Hensel prefixes and known-order
square/Lucas clocks. It distinguishes these exact skips from discovery of
unknown nonlinear births and the unresolved full-germ scheduler contract.
