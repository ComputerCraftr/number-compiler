# Reflected decimal multiplication

The families `2rev10` and `5rev10` apply $T_m(x)=m\,\operatorname{rev}_{10}(x)$
for $m\in\{2,5\}$. A physical tick performs one reversal and multiplication.
The centered two-tick gate and a four-tick annular projection use different
clocks. The results below require the stated source, halo, carry and width
conditions. [Reverse/add](reverse-add.md) has its own pair-sum and width-birth
laws. [Current release gates](../release-status.md) own validation status.

## Cyclic relative returns for reflected multiplication

For a cyclic decimal word, let each digit triple test whether the two-tick
output equals its left, center or right input digit. Intersect the three
equality bits over the word. Concatenation needs only the two end digits
on each side of the join to check the crossing triples. Closing the word
adds the two wraparound triples, or one repeated triple for a singleton.

The center equality admits the uniform words on $0,3,6,9$. For the
nonconstant neighbor equalities, the table gives the blocks of the cyclic
language. Read a word up to rotation as a nonempty concatenation of blocks,
choosing $a,b\geq 0$ independently in each block.

| Multiplier | Output equals left input | Output equals right input |
| --- | --- | --- |
| 2 | $15\,3^a\,84\,6^b$ | $0\,3^a\,29\,6^b\,7$ |
| 5 | $51\,6^a\,48\,3^b$ | $07\,6^a\,92\,3^b$ |

Superscripts in the table repeat digits. The two-tick action shifts an
admitted word by one site, so a primitive nonconstant word of length $p$
first returns at even tick $2p$. An odd return would put the one-tick
image on the same rotation orbit. Reflection reverses the rotation, which
would make the two-tick image equal the original word. This contradicts
a one-site shift on that primitive word.

Digit equality includes the mixed carry terms. For example, reducing
digits modulo five accepts the proposed right shifts of both `02925` and
`00792`. Their actual two-tick cyclic images are `29700` for multiplier
two and `52920` for multiplier five. Transport to a finite decimal source
also requires its causal halo, physical carries, width changes and
normalized readout.

## Periods conditioned on the two upstream ports

Let $F$ be the centered two-tick gate. In either extreme moving frame
the downstream digit $x$ evolves by $F(a,b,x)$ or $F(x,a,b)$. Fixing
the ordered pair $(a,b)$ gives a map on ten digits with at most two
outputs, for either multiplier. Composing a nonempty word of these
maps preserves that bound. If $G$ is the response to one full period
of the two authenticated input streams, then $G^4(x)=G^2(x)$.
Indeed, among $G(x),G^2(x),G^3(x)$ two values coincide. After at most
two input periods the downstream digit therefore returns in one or
two input periods at the same phase. The upstream streams must cover
the entire requested cone. On a coupled two-cell ring, multiplier two
takes $11\to44\to77\to11$ in centered ticks, and multiplier five
traverses the same cycle in reverse.

## Ordered support at a moving cut

Pair projection can enlarge the language of a physical halo. At cut 383
of the seed-1 four-step chart anchored at generation 8192, the two
adjacent pair supports at positions 388–390 (counted from the units end)
contain `12` and `22`. The corresponding triple support is
`{123, 320, 322}`. Joining the pairs alone would also admit `122`.
Restricting the seven-digit inlet to the admitted triples before taking
its ordered image excludes this spurious case at both centered subphases.

Sheet phase and inlet carry have different roles. For a three-sheet
response on the nonzero elements of GF(4), write a binary channel as
$X(u)=a+\operatorname{Tr}(bu)$ and take $u\mapsto\omega u$ on return.
The shifted channel $Y(\omega u)$ has trace coefficient $\omega d$
when $Y(u)=c+\operatorname{Tr}(du)$. An ordered cross-return
correlation uses $X(u)Y(\omega u)$, even when an unshifted channel has the
same period.

At cut 415 of the seed-1 chart, the 216-block lower return can carry two
distinct sheets. With 18 open columns, an all-zero inlet and an inlet
pulsed at blocks 376, 383, 384, 387 and 388 first disagree in a seam
carry at block 575. The next digit is 5 on the former and 7 on the
latter. The 19-column closure uses the specified lower drive and
moving chart. Extending it to a receiving source requires exact inlet,
width and both centered carry transports.

## 2rev10 four-port successor and the mod-32 cut

For `2rev10`, the physical action is `2R`. The two-step action has four
incoming carry-port combinations. Concatenation transports the first carry
left to right and the second right to left. A repeated spatial
block uses binary action composition. Exact output also requires the source's
zero-suffix contraction, boundary births and output normalization. Spatial
REPEAT closure does not prove an all-depth temporal period.

The finite interior square uses a complete `4t`-digit halo. If `U_t`
returns the middle `2t` digits after `t` two-step updates, then for four equal
quarters `A,B,C,D`, put `u=U_s(AB)`, `v=U_s(BC)` and `w=U_s(CD)`. The
ordered result is `U_(2s)(ABCD)=U_s(uv) ++ U_s(vw)`. Source-issued growth
ports determine border births and phase. The
[`Double_Reverse_Spacetime_Carry_Square`](../../proofs/isabelle/families/double_reverse/temporal_double_reverse/Double_Reverse_Spacetime_Carry_Square.thy)
theory proves the finite-window law with its complete halo.

The base-`z` inverse modulo 32 specializes to source-selected doubling carries
and connects the two-pass row to the decimal stencil. The escaping carry term
remains in the finite-cut equation. A finite-quotient carry polynomial requires
the source seam and inlet word to determine subsequent digits. The refinement
is stated in
[`Double_Reverse_Group_Ring_Carry_Cut`](../../proofs/isabelle/families/double_reverse/temporal_double_reverse/Double_Reverse_Group_Ring_Carry_Cut.thy)
and
[`Double_Reverse_Group_Ring_Four_Port`](../../proofs/isabelle/families/double_reverse/temporal_double_reverse/Double_Reverse_Group_Ring_Four_Port.thy).

The two-bit outer port quotient uses canonical representatives `0/3` and
`0/5` for unshielded ports. A birth shields the corresponding port. Outer
admission requires the complete halo, odd-generation and pointed-source
conditions. Inner output digits retain their exact values.

The source-bound return period joins the border phase with the mod-99 and
mod-198 projections. One bounded mod-198 orbit supplies both residue lassos
without constructing the future digit word. Four physical ticks restore the
border phase and add two digits of width, so width drift is tracked separately.
The transient is an aligned upper bound in physical ticks, while the period is
exact for this projection. Residue values and lasso data are separate
observations, each limited to the admitted projection.

## Reflected multipliers and packed two-step actions

For `T_m(x)=m*reverse10(x)` with `m` equal to 2 or 5, a padded base-100
carry sheet represents finite dyadic segments. Its inlet includes the source
digits and its complete halo. Each stage normalizes the preceding word before
the next stage is applied. The
[`Double_Reverse_Reflected_SLP_Endpoint`](../../proofs/isabelle/families/double_reverse/temporal_double_reverse/Double_Reverse_Reflected_SLP_Endpoint.thy)
theory proves exact numerical endpoints for odd and even physical clocks,
including the two multipliers' different even inlets. The theorem preserves
padding equivalence and requires the stated decimal source assumptions. It
does not establish an unrestricted future period or a complexity bound.

For multiplier 5, encode least-significant-first decimal digits as nibbles in
`P`. Let `L` have one low bit in each nibble and set `U=14L`. The packed
ordinary product and reflected digit action are

```text
M(P) = 5*(P & L) + 8*(P & U)
E(P) = ((P & U) >> 1) + 80*(P & L)
```

Apply `M` to `E(P)` after removing its low zero nibbles. Decoding the
resulting word gives exactly two physical `5rev10` steps. This normalization
accounts for width changes caused by trailing zeros at the seam. The
[`Five_Reverse_Packed_Word_Consumer`](../../proofs/isabelle/families/five_reverse/five_reverse/Five_Reverse_Packed_Word_Consumer.thy)
theory establishes the word and first-refusal laws for valid packed decimal
digits.

## Threshold masks, glyphs and finite spatial seams

For the double-reverse recurrence `T(X)=2*reverse10(X)`, let `C`
be the decimal threshold mask of a canonical whole source: its digit at each
position is `[digit>=5]`. With nonzero source units, the four-port carry law
gives `T²(X)=4X-198*(C div 10)` when the units are below five, and
`T²(X)=40X-198*C` otherwise. The quotient branch needs the preceding
threshold bit to reconstruct its units digit; `C mod 70` alone does not supply
that bit. Zero-ending words require width-normalizing treatment. Applying
these equations to a spatial subinterval requires its actual exterior seam;
the subinterval residue is insufficient.

Digitwise doubling as decimal glyphs is a different morphism from normalized
multiplication: the glyph for six is `12`. Reflecting the source before that
morphism leaves this glyph `12`, whereas reflecting the glyph gives `21`.
Its length phase therefore includes the threshold count. A copy-count period
of a supplied spatial band is not a physical recurrence period. For a fixed
nonempty band, each mod-seven copy sum has ratio of order dividing six.
Its geometric sum repeats after six copies when the ratio differs from one,
or after seven copies when it equals one. Thus 42 is a common positive-copy
period for the joined word, threshold and glyph projections; the exact word
length still grows. This is a finite spatial algebra law, not a source-period
certificate. A strict-interior stencil needs its real exterior halo before
it can predict an embedded band's boundary outputs. These factors do not establish a
source-reachable all-future twisted return.

The bank-stencil refinement can be expressed without a second physical tape.
For a nonempty MSB-first band `W`, let `core(W)` emit only stencil cells whose
two neighbors lie inside `W`. For nonempty adjacent bands `U,V`, concatenate
`core(U)`, the cell `F(U[-2],U[-1],V[0])` when `len(U)>=2`, the cell
`F(U[-1],V[0],V[1])` when `len(V)>=2`, and `core(V)`, in that order.
This local seam law is associative. For `len(B)>=2` and positive `r`, it gives
`core(B^r)=core(B)*(seam(B,B)*core(B))^(r-1)`. Exterior digits, width birth
and leading-zero normalization remain separate source-bound obligations.
In the truncated Pascal ring over F11 through order `j`, choose the least
`e` with `11^e>j`. The substitution `z=-1-u` has multiplicative period
dividing `2*11^e`; eleven such cycles annihilate the additive copy sum.
Together with the mod-seven factors this gives the spatial-copy bound
`42*11^(e+1)`. Neither that bound nor the interior seam law authorizes an
all-future temporal return or a global mod-99/198 clock identification.

## Effective seam programs and finite period evidence

For `2rev10`, an effective seam gate records the phase and the two emitted
boundary digits. Inlets with the same gate produce the same retained bank
successor under the admitted stencil. A finite repeated gate program can
therefore have a conditional lasso on `(bank state, program position)`.
Powering that lasso proves behavior for the supplied program, not that the
original source supplies that program indefinitely. Independent source blocks
must still validate their bank states and gates. A matching finite window is
not an eventual-period certificate for the next inward layer.

The four-step affine coefficient 160 also does not establish a rotation of
the normalized mantissa: `168` reaches `16188` in four physical `2R` steps.
After the two-digit width shift, the ratio is `1349/1400`, rather than `8/5`
or its wrapped value `4/25`. The innovation correction must be retained.

## Centered harmonic projections

On the admitted four-physical-step `2rev10` growth sector `(1,0,0,1)`, the
right centered digit has the forced recurrence
`c' = 16*c + f (mod 10)`. For a finite issued interval of `k` blocks, its
weighted forcing is `c_end - 16^k*c_start (mod 10)`. Modulo five, the forcing
sum telescopes to `c_end-c_start`; modulo two, the last forcing equals
`c_end`. Both conditions are required for a digit return. Mod-five
cancellation alone does not establish an exact return.

Let `a` be the leading `ceil(w/2)` decimal digits and `b` the reversed trailing
`ceil(w/2)` digits. For `w=2h`, `a-b=(-1)^h X (mod 11)`; for `w=2h+1`, the
halves overlap at `c` and `a+b=c+(-1)^h X (mod 11)`. These are projections of
the existing whole-word clock and pointed center, not independent clocks or
half-word scans.

## Decimal multiplication carry sheet

For a reflected multiplier $m$ equal to 2 or 5, put $q=10/m$. In
multiplication-input order, digit $d$ with inlet $0\le c<m$ emits
$m(d\bmod q)+c$ and leaves carry $\lfloor d/q\rfloor$. The last digit
of any nonempty tile therefore fixes its exit carry. In a repeated tile the
first copy consumes the incoming seam. Every subsequent copy consumes the
exit of the preceding copy. Reading the other end of a word changes the input
order. Physical zero trimming occurs before the final multiplication, which
may itself produce a trailing zero.
