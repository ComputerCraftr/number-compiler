# Carry-domain quotients

The reverse-add and Collatz carry summaries use small spatial actions rather
than materialized carry rows. This document records which reductions are exact,
which are projections, and which hypotheses consumers must authenticate.

## Reverse-add

For a pair symbol `s` in radix `b`, the carry action is `CONST0`, `ID`, or
`CONST1` according as `s` is less than, equal to, or greater than `b - 1`.
Spatial parents compose these actions in physical carry order. The exact local
output law remains separate: equal carry exits do not imply equal output digits
or equal future tiles.

The decimal F5/F2 factorization and mod-32 Frobenius sectors are bounded views
of that exact local law. Source annihilation is consumed only by the
authenticated symmetric, contiguous, initially zero-carry observation whose
padding and growth hypotheses establish it. Fixed-width symmetric pair fields
include active zero-valued cells; their counts are not counts of canonical
positive-integer decimal representations.

The [residue-consumer research lowering](../mirror-pair-residue-quotient.md)
uses geometry-derived carries to normalize through `S mod 10` on both
branches. Its no-growth domain observer has four response classes. Growth
uses adjacent normalized residues and affine F2 transport, retaining parity
where required while avoiding an intermediate 19-valued threshold input.
These consumer reductions do not identify complete source states or establish
bounded temporal closure.

The later [growth coboundary experiment](../growth-coboundary-directional-quotients.md)
jointly forgets source domain/value changes through twelve `(q,delta)` symbols.
Its exact forward reconstruction is proved, but its generic A16 circuit is
larger than the residue lowering and remains opt-in. Collatz's directional
left/right value consumers are integrated into symbolic output morphisms and
the streaming transducer; they do not certify a complete temporal quotient.

## Collatz two-wire carry

For radices `b >= 4` with `b == 1 (mod 3)`, write the reachable carry as

```text
u = [c >= 1]
v = [c == 2]
c = u + v, with v <= u.
```

For `R = 3*d`, the low wire compares `R` with `b - 1`, and the high wire
compares it with `2*(b - 1)`. Each wire therefore uses the same three-element
`CarryFn` algebra as reverse-add. The five actions produced by nonempty digit
intervals are

```text
000, 011, 111, 112, 222.
```

They form a closed semigroup. They are not a unital monoid: the empty interval
has the separate identity `012`, represented by `(ID, ID)`. The binary physical
kernel is unchanged. The existing metadata helper still rejects bases below 3;
other admitted radices outside `1 mod 3` retain its ordinary exact carry law.

The live `sequences.collatz.pair` metadata API uses this factorization for
eligible radices and avoids enumerating the radix alphabet when constructing
the five nonempty actions. The binary physical `C^N` tile executor does not yet
consume a two-wire future-behavior class, so this bounded metadata improvement
does not establish accelerated Collatz execution or scaling.

## Geometry, derivatives, and projected periods

For an odd source, a leading radix-4 sentinel frame can be removed from the
continuation state when the exact frame depth remains occurrence geometry and
physical-time weight. Removing that frame is a gauge normalization. It is not
the same claim as periodicity.

The reported `576` radix-4 and `1152` binary-valuation periods are periods of a
particular retained Frobenius/radial action after its mod-32 saturation. They
are not periods of exact Collatz states, exact output tiles, or arbitrary frame
positions. Any production consumer must validate the selected quotient rings,
phase, saturation, source chart, and frame cocycles before using them.

For a finite polynomial field `G`, the boundary derivative
`(1 - X)G` is exact and lossless once the finite interval boundary is known. It
becomes an information-losing quotient only after projection into a bounded
ring or jet. Sparse run boundaries alone therefore do not prove a finite future
behavior class.

## Output cancellation is the reverse quotient

The supplied decimal research uses `X = (S - 9) mod 20` and the coordinates
`a = X mod 5`, `T = -X mod 3`, and `lambda = [X >= 15]`. Those coordinates
reconstruct each bounded leaf symbol; they are not themselves a lossy quotient.
The proposed useful reduction occurs after transport and carry birth combine:

\[
S' = B_g(S) + E(C),\qquad
B_0(S)=2S,\qquad B_1(S)=(U^{-1}+U)S.
\]

The canonical result must identify the combined output, not independently key
the unreduced pair `(transport, birth)`. Internal algebra subexpressions may
still share. This is compatible with the current tile arena: exact output leaf
symbols and child TileIDs determine content identity; producing actions, carry
histories, and source provenance do not.

Two supplied fixed-width witnesses are now executable regression cases:

| Different source pair fields | Common successor pair field |
|---|---|
| `(10,0,0,10)` and `(10,9,9,10)` | `(1,1,0,1,1)` |
| `(0,9,9,10,10,9,9,0)` and `(0,14,14,0,0,14,14,0)` | `(1,9,9,1,1,9,9,1)` |

`test_transport_birth_aliases.py` verifies equal exact TileIDs and a subsequent
powered-consumer hit with child construction poisoned. This establishes reuse
for the witnesses, not a bound on cold macrocell population.

The attachment reports 209,960 fixed-width symmetric fields through width 8,
zero one-step mismatches, and the following exact successor-image counts:

| Width | Sources | T | T² | T⁴ | T⁸ |
|---|---:|---:|---:|---:|---:|
| 6 | 6,859 | 4,510 | 3,634 | 3,090 | 2,948 |
| 8 | 130,321 | 77,509 | 55,107 | 43,342 | 40,071 |

These exhaustive counts are supplied research results; this cleanup has not
reproduced that exhaustive experiment. Equal complete deterministic successors
necessarily have equal subsequent futures. That fact does not imply that a
bounded carry-exit or Frobenius observer alone has the same congruence.

## Carry-response jets and frame characters

For either Boolean carry wire, write its exit as `q_out = a*q_in + b` and its
emitted carry polynomial as `P(q,z) = B(z) + q*A(z)`. For adjacent intervals X,Y
of lengths Lx,Ly, the exact characteristic-two composition is

\[
\begin{aligned}
a_{XY}&=a_Ya_X,& b_{XY}&=b_Y+a_Yb_X,\\
A_{XY}&=A_X+z^{L_X}a_XA_Y,&
B_{XY}&=B_X+z^{L_X}(B_Y+b_XA_Y).
\end{aligned}
\]

Reduction into `F2[y]/(y^H)`, with `y=z+1`, preserves these spatial equations.
Squaring doubles y-adic valuation until truncation kills the component.
This is a spatial carry-response homomorphism. Exact next output remains a
separate local-law dependency; no temporal successor certificate is inferred
from the spatial equations alone. The current binary physical scheduler does
not publish such a jet as an output-complete future-behavior class.

The [Collatz harmonic proof update](../collatz-harmonic-port-actions.md)
reproduces the two-wire response hierarchy and proves carry projection and
conditional five-event linear source death in Isabelle. That death theorem
holds with the same forcing events; it does not establish a five-round bound
on nonlinear Hensel refinement. Spatial radix-64 and binary jet coordinates
are related by `z_cell = z_bit^6`, not by renaming their nilpotent variables.

All current carry boundaries are already derivable from exact domain geometry.
The [geometry-derived carry implementation](../geometry-derived-carry.md)
uses shared prefix monoid operations for reverse/add and both Collatz wires.
The harmonic observer's failure to answer a pointwise query is a projection
gap, not missing carry state. The remaining temporal dependency is the exact
geometry-conditioned value-to-next-threshold map.

For odd x with `3x+1 = 2^k*y`, y odd, write `k=2r+e`. Then

\[
x=\frac{4^r-1}{3}+4^r\frac{2^e y-1}{3}.
\]

This gives the radix-4 sentinel prefix `1^r` and its frame-free suffix. Initial
even divisions and removed frame lengths contribute exact occurrence weights;
they cannot be discarded from physical-time observations. The `+1` is the
incoming carry state `(u,v)=(1,0)`, not an extra coefficient-field rewrite.

The selected phase tuple in the attachment is

\[
\rho(K)=(z^K\bmod ((\mathbb Z/32)[y]/y^5),\;
2^K\bmod27,\;K\bmod16,\;K\bmod8,\;2^K\bmod32),\quad z=y-1.
\]

Its reported orders 128,18,16 give `lcm=1152` after `K>=5` kills the last
component. One radix-4 shift corresponds to two binary shifts, giving period
576. Additional channels require their own order check. This action-period
claim does not authorize merging arbitrary exact suffixes or removing exact
physical weights. The supplied broad phase and frame experiments remain
research evidence, not a new runtime certificate issued by these unit tests.

For a domain field G over a finite interval, the identity

\[
\partial G_{AB}=\partial G_A+X^{L_A}\partial G_B
\]

allows projected boundary summaries to compose over canonical children. A run
contributes `e_sigma*X^s*(1-X^length)`. Its long interior can therefore be
represented compactly, while exact geometry remains outside the projected
semantic class. Testing a finite corpus for successor agreement is useful for
finding counterexamples; publication of a reusable behavior class still requires
all obligations of its specified observation/continuation profile.

## Provenance and integration status

This summary incorporates three user-supplied research notes received on
September 10, 2026. Their SHA-256 content identities are:

- Frame/domain geometry and 576/1152 action: `b498adf52ea050590b830ec21c05ead31213bd7b92d8daa8965b819c74ca9df1`.
- Two-wire carry and Frobenius response: `866559371c478e836da5b5e3bbb4c9c7ef145499090bc78c025ea22eb63f0c5a`.
- Reverse transport/birth cancellation: `9829aece2b4b40c1f644b83503f8bf3d35aafc752c206facf0d02f9d1d4bd6ef`.

Implemented here: bounded two-wire carry metadata, constant-size eligible-radix
semigroup construction, exact successor-sharing regressions, and removal of
unused one-interval causal scans. Not established: arbitrary-depth active
consumer discharge, a complete Collatz domain/innovation quotient, or universal
sublinear cold execution. Release measurements must count remaining exact
causal construction alongside successful bounded-summary reuse.

All prefix, source-death, symmetry, and synchronizing-blank identities are
conditional certificates. Their consumers must check the kernel identity,
ports, orientation, geometry, padding, and observation profile. Frame gauge,
bounded phase action, local carry transfer, and exact output content remain
separate identities.
