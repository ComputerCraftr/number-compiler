# Port-conditioned alternating-radix carry harmonics

The [port-valued Mealy theorem](port-valued-mealy-actions.md) now proves the
shared spatial ownership law independently of finite-word enumeration.
The decimal five-component implementation derives carry, reset and forcing
views from one response. The distinct alternating-F5 observer and its stronger
negative controls below remain valid; a change of observer does not turn a
spatial theorem into a temporal closure theorem.

This September 10 research establishes an exact **spatial emitting carry
action** for alternating radix 2,3 over F5. It combines the carry boundary
function and its harmonic emissions into one denotation. Its border-flux
action is a projection, so storing both as independent quotient coordinates
would duplicate information.

It does not establish a temporal 196 quotient or an A32 improvement. Equal
spatial actions can have different next actions and different interior carry
positions. The exact value and threshold residuals remain necessary.

## Denotation and spatial composition

For a length-L domain word, use the existing `CarryFn` actions LT=K0, EQ=I,
GT=K1. For each incoming c, let C0=c and apply the domain at position i to
obtain C(i+1). The occupancy emission uses **incoming** boundaries C0..C(L-1):

\[
W_\Gamma(c)=(C_L,h_0,h_1),\qquad
h_0=\sum_{i=0}^{L-1}C_i(1,2)_{i\bmod2},\quad
h_1=\sum_{i=0}^{L-1}C_i(1,3)_{i\bmod2}\pmod5.
\]

Since 2·3=1 in F5, spatial translation by an odd length sends a pair of
emissions (r0,r1) to (2r1,3r0); an even translation leaves them unchanged.
To concatenate A then B, first select B's incoming port using A's outgoing
carry. Add B's translated emissions to A's emissions. This is exact port
substitution, not independent summaries of domain, border, and harmonics.

The reference implementation is
[`carry_harmonic_ports.py`](../devtools/proofs/carry_harmonic_ports.py). It
imports the existing carry monoid rather than defining another carry scan.
`CarryHarmonicPortAction` retains width and two output rows. Composition
uses only those rows and width parity. A regression squares an all-EQ action
to width 2^128 with leaf execution and field observation poisoned.

The existing mod-32 cyclotomic sector transfer remains a different observer.
This F5 observer is not silently substituted for those sectors or for exact
value fields, and it is not installed in `GeometryAction` by this update.

## The 501 bound is length-indexed

If the first decisive domain is at **zero-based index j**, the two incoming
carry paths differ on C0..Cj, a prefix of length **j+1**. They coalesce after
that domain and remain equal. The alternating prefix sums have period ten.
For a non-all-EQ word the full two-port emission is therefore encoded by

\[
(C_{out},\ (j+1)\bmod10,\ h_0^{(0)},\ h_1^{(0)}).
\]

Using j mod10 instead is an equivalent shifted convention. The code must not
mix the two conventions when reconstructing the incoming-one row. There are
at most 2·10·5·5=500 such codes.

At each fixed length there is one all-EQ action, giving the **501** bound.
However, all-EQ is only an identity *carry function*. Its incoming-one
harmonic output is the prefix sum for that length. In particular,

\[
W_{EQ^2}(1)=(1,3,4),\qquad W_{EQ^4}(1)=(1,1,3).
\]

Those words have the same width parity but different emissions. Therefore
an untyped global ID must not collapse them to a single identity emitter.
The complete generator exploration finds:

- **501** occupancy actions per fixed length, attained from L=18 onward;
- **510** distinct two-port emission functions across all lengths: 500
  coalescing actions plus ten all-EQ prefix emissions;
- **1,010** reachable `(length parity, emission function)` states, closed
  under all three domain generators, with all 3,030 outgoing edges checked.

A reduced code with one all-EQ tag remains valid when exact length is part of
the interface type and is used to recover the tag's actual emissions. The
implementation exposes `length_indexed_code` with that limitation explicit.
Exact width remains geometric metadata in the reference action; the finite
counts do not include all possible widths or authorize dropping output extent.

## Border flux is a projection

Recover the even and odd carry populations from the same row:

\[
O=h_1-h_0,\qquad E=3h_0-2h_1\pmod5.
\]

Let p=L mod2 and z=Cout. For signed borders Di=C(i+1)-Ci, their populations
are

\[
E_D=O-E+pz,\qquad O_D=E-O-c+(1-p)z.
\]

Applying (E+2O,E+3O) to these two populations gives both border harmonics,
without retaining a second action or scanning boundaries again.

For a decisive word, write f for the incoming-zero first border harmonic.
The other harmonic is 2f-z. The incoming-one row differs by the negative
weight at the decisive index: (-1,-1) if j is even, (-2,-3) if j is odd.
Thus the border action has the code `(z,j mod2,f)`, plus the all-EQ zero-flux
identity. This gives **21** border actions; width phase is still required
for spatial concatenation. Unlike occupancy, the all-EQ border emission is
zero at every length.

## Exact F5 forcing observation

For the complete symmetric decimal pair field, use the physical incoming
carry zero. Obtain (E,O) from its occupancy row. Reflection preserves these
populations for odd width and swaps them for even width.

With no growth, add the population pair to its width-L reflection. With
growth, first replace the initial zero carry by edge one, giving (E+1,O),
and add its reflection at output width L+1. Convert the resulting populations
back to the two harmonics. This exactly projects the existing signed forcing
law modulo five: its multiples of ten vanish, including the edge corrections.

The implementation's `forcing_harmonics()` computes this observation directly
from the action. The proof tests compare it to the repository's independent
`pair_step` and `forcing_event` outputs, including both growth branches.
The law applies to the whole symmetric field with incoming zero. Arbitrary
interior regions require their correct reflection alignment and boundary
context; this whole-field formula does not establish those conditions.

## What this can and cannot replace

The earlier low-harmonic collision is separated:

| Pair field | Incoming zero `(out,h0,h1)` | Incoming one |
|---|---|---|
| `8^9` | `(0,0,0)` | `(0,1,1)` |
| `(9,10,10,10,10,10,10,10,9)` | `(1,0,3)` | `(1,3,2)` |

This shows the new observer distinguishes that witness. It does not prove
that it captures every threshold-visible part of the old harmonic kernel.

For example, domain words `(GT,LT,LT,LT)` and `(LT,LT,GT,LT)` have identical
two-port occupancy actions but different C1 values. The shared action cannot
answer an arbitrary interior carry query. **That information is already in the
exact domain geometry**: C1 is 1 in the first word and 0 in the second. No new
carry residual or semantic coordinate is needed. `carryAt(G,i,c)` derives the
answer from the prefix monoid action of the same geometry root. Harmonic-only
consumers may use W; pointwise consumers use G. See the
[geometry-derived carry update](geometry-derived-carry.md).

The audited A16 interface has one width coordinate and five domain/F5/parity
triples, not sixteen independent carry inputs. Its table operand bindings
include value-dependent expressions. Replacing their expanded carry tests by
native monoid operations reduces intermediate consumers, while preserving all
exact value and threshold dependencies.

There is also a two-cell temporal counterexample: pair fields `(4,4)` and
`(8,8)` have identical current LT actions, but their successors `(8,8)` and
`(16,16)` have different actions. On the 1,024-transition 196 sample, 110 of
134 reached whole-state keys have multiple next keys. Spatial composition is
closed; temporal successor congruence is not.

The remaining temporal problem is the geometry-conditioned value-to-next-domain
map. Current carry boundaries, growth, and their harmonic projections are
derived from G; they are not missing state. Powered-output checks and complete
cost accounting still determine whether an implementation scales.

## Proof scope and reproducibility

[`Reverse_Carry_Harmonic_Ports.thy`](../devtools/proofs/isabelle/Reverse_Carry_Harmonic_Ports.thy)
formalizes emitting-action concatenation, carry coalescence, the j+1 prefix
difference, ten-periodicity, and population inversion. Its 501/21 cardinality
lemmas count the proposed code spaces; finite exploration separately supplies
attainability and saturation. It does not verify the Python implementation,
prove a pointwise replacement theorem, or establish temporal closure.

The executable probes reproduce spatial composition, the parameterization,
complete generator closure, and 196 measurements. The independent exhaustive
forcing check lives in validation, not the ordinary unit partition. See the
[dated evidence report](../results/current/carry-harmonic-ports-2026-09-10/README.md)
for exact counts, source fingerprints, commands, and build results.
