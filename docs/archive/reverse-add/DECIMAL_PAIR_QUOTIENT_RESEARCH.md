# 196 reverse/add: exact quotient mathematics and implementation plan

## Objective

Finish the production reverse/add powered path in `number-compiler` using the exact quotient algebra already available.

The target is **not** another carry-state search and not another whole-trajectory quotient.

For a generation/index request \(N\), the production architecture must be:

$$
\boxed{
\text{binary-powered FieldCellAction}
+
\text{canonical recursive source tile}
+
\text{bounded local interface}
\longrightarrow
\text{canonical future output}
}
$$

with temporal powers constructed by repeated squaring and without generation-by-generation output replay.

For point, width, compact-state, residue, and similar bounded observations, work should scale with the bit length of \(N\), apart from logarithmic spatial descent through the recursive tile.

Do **not** claim logarithmic time for materializing the entire decimal integer. If its output width is \(\Theta(N)\), emitting all of those digits has an unavoidable \(\Omega(N)\) output-size cost.

---

# 1. Preserve the semantic separations

These identities must remain distinct:

$$
\boxed{
\text{FieldCellActionID}
\neq
\text{LocalInterfaceID}
\neq
\text{FieldImageID / exact TileID}.
}
$$

They mean different things.

### `FieldCellActionID`

Source-independent powered temporal algebra:

* radial/Frobenius transport;
* bounded innovation;
* carry action;
* residual theorem data;
* coordinate-output action metadata;
* geometry/phase.

### `LocalInterfaceID`

A behavioral quotient.

Two local/macro states may share it only if **every admissible continuation** preserves:

* both directional boundaries;
* coordinate outputs;
* activity;
* first/last active;
* extent;
* halos;
* growth;
* termination;
* normalization;
* frame/cocycle observations;

and their successors remain equivalent.

### Exact `FieldImageID` / `TileID`

Exact recursive content.

Different exact interiors can have the same `LocalInterfaceID` while keeping distinct output tile IDs.

Never use the behavioral interface as exact content identity.

---

# 2. Exact decimal pair field

Let an integer have LSD-first decimal digits

$$
d_0,d_1,\ldots,d_{m-1}.
$$

Define the symmetric pair coefficient

$$
\boxed{
S_i=d_i+d_{m-1-i}
}
$$

so

$$
0\le S_i\le18,
\qquad
S_i=S_{m-1-i}.
$$

Reverse-and-add can be computed entirely from this pair field and one forward carry track.

Define

$$
C_0=0,
$$

$$
\boxed{
C_{i+1}=[S_i+C_i\ge10].
}
$$

The resulting decimal digit is

$$
\boxed{
y_i=S_i+C_i-10C_{i+1}
=(S_i+C_i)\bmod10.
}
$$

The width-growth bit is

$$
\boxed{g=C_m.}
$$

There is no need for a separate reverse carry state. Define only the reflected view

$$
\boxed{
R_i=C_{m-i}.
}
$$

It is a view of the same forward carry field.

---

# 3. Exact LT / EQ / GT carry quotient

The carry threshold is \(9=b-1\).

For any incoming carry \(c\in\{0,1\}\),

$$
C^+=[S+c\ge10].
$$

Therefore:

$$
S<9
\quad\Longrightarrow\quad
C^+=0,
$$

$$
S=9
\quad\Longrightarrow\quad
C^+=c,
$$

$$
S>9
\quad\Longrightarrow\quad
C^+=1.
$$

So each pair coefficient induces exactly one of three functions:

$$
\boxed{
\mathrm{CONST0},\qquad
\mathrm{ID},\qquad
\mathrm{CONST1}.
}
$$

Equivalently,

$$
\boxed{
\begin{array}{c|c}
\text{domain}&\text{carry action}\\
\hline
S<9&\mathrm{CONST0}\\
S=9&\mathrm{ID}\\
S>9&\mathrm{CONST1}
\end{array}}
$$

This is the actual non-injective carry quotient.

A carry is:

* **killed/reset to 0** by LT;
* **transmitted** by EQ;
* **born/reset to 1** by GT.

Do not represent carry-birth events separately. They are already the GT domain.

---

# 4. Signed defect / old \(X\) coordinate

Define the signed threshold defect

$$
\boxed{
\Delta=S-9
}
$$

with

$$
-9\le\Delta\le9.
$$

Then:

$$
\Delta<0\iff LT,
$$

$$
\Delta=0\iff EQ,
$$

$$
\Delta>0\iff GT.
$$

The previously discovered cyclic coordinate is

$$
\boxed{
X=(S-9)\bmod20.
}
$$

Because \(S=19\) is impossible,

$$
\boxed{
X\in\mathbf Z/20\mathbf Z\setminus\{10\}.
}
$$

The exact pair conjugacy

$$
S\mapsto18-S
$$

becomes simply

$$
\boxed{
X\mapsto-X\pmod{20}.
}
$$

Consequently LT and GT exchange, EQ remains fixed, and the carry monoid conjugates as

$$
\mathrm{CONST0}\leftrightarrow\mathrm{CONST1},
\qquad
\mathrm{ID}\leftrightarrow\mathrm{ID}.
$$

This is useful for certified conjugacy/mirror normalization.

---

# 5. Exact mixed-radix pair coordinates

For decimal, decompose every valid pair coefficient as

$$
\boxed{
S=\alpha+5\beta+10\nu
}
$$

where

$$
\boxed{
\alpha=S\bmod5\in F_5,
}
$$

$$
\boxed{
\beta=
\left\lfloor
\frac{S\bmod10}{5}
\right\rfloor
\in F_2,
}
$$

$$
\boxed{
\nu=
\left\lfloor
\frac S{10}
\right\rfloor
\in F_2.
}
$$

Thus the exact leaf carrier is

$$
\boxed{
Q_{\rm MR}
=
(\alpha,\beta,\nu)
\in
F_5\times F_2\times F_2
\setminus\{(4,1,1)\}.
}
$$

The excluded tuple would encode \(19\), which is not a valid decimal pair coefficient.

Important:

$$
\boxed{
Q_{\rm MR}\text{ is bijective to }S\in\{0,\ldots,18\}.
}
$$

Therefore this is an exact **factorization/conjugacy**, not by itself a state-reducing quotient.

Its value is that it exposes the arithmetic as a tiny \(F_5\) phase plus binary registers.

The old coordinate

$$
a=X\bmod5
$$

satisfies

$$
\boxed{
a=\alpha+1\pmod5.
}
$$

Hence the old exceptional phase \(a=0\) is exactly

$$
\alpha=4.
$$

---

# 6. Carry directly from the mixed-radix coordinates

Define

$$
\boxed{
w=[\alpha=4\land\beta=1].
}
$$

Because \((4,1,1)\) is excluded, \(w=1\) uniquely means

$$
S=9.
$$

Also

$$
\boxed{
\nu=[S>9].
}
$$

Therefore the complete carry law is

$$
\boxed{
c^+=
\begin{cases}
c,&w=1,\\
\nu,&w=0.
\end{cases}
}
$$

Equivalently:

$$
(\nu,w)=(0,0)\to\mathrm{CONST0},
$$

$$
(\nu,w)=(0,1)\to\mathrm{ID},
$$

$$
(\nu,w)=(1,0)\to\mathrm{CONST1}.
$$

Thus

$$
\boxed{
Q_{\rm carry}=(\nu,w)
}
$$

is the exact carry-action quotient.

Do not add:

* carry age;
* carry provenance;
* carry-birth position;
* event history;
* reverse carry;
* carry slab rows

to semantic state.

They are derived information.

---

# 7. Carry block monoid

A spatial block consists of the composition of its cell carry functions.

Let

$$
M=
\{
K_0,I,K_1
\}
$$

with

$$
K_0(c)=0,\qquad I(c)=c,\qquad K_1(c)=1.
$$

Spatial concatenation uses ordinary function composition.

The complete multiplication table, written as

$$
\text{after}\circ\text{before},
$$

is

$$
\boxed{
\begin{array}{c|ccc}
 &K_0&I&K_1\\
\hline
K_0&K_0&K_0&K_0\\
I&K_0&I&K_1\\
K_1&K_1&K_1&K_1
\end{array}}
$$

This is a three-element reset/last-reset monoid.

For a whole block:

$$
\boxed{
F_{\rm block}=I
}
$$

iff every cell is EQ.

Otherwise the block's outgoing action is determined solely by the **last non-EQ cell**:

* last reset LT \(\Rightarrow K_0\);
* last reset GT \(\Rightarrow K_1\).

This is why no carry row should ever be part of the block identity.

The repository already has this algebra in:

* `src/number_compiler/core/carry_monoid.py`
* `src/number_compiler/core/pair_algebra.py`
* `src/number_compiler/core/prefix_monoid.py`

Reuse it. Do not build a competing carry implementation.

---

# 8. Exact decimal digit normalization

Given a pair state

$$
q=(\alpha,\beta,\nu)
$$

and the incoming carry \(c\), define the base-5 wrap bit

$$
\boxed{
j=[\alpha=4\land c=1].
}
$$

Then

$$
\boxed{
\bar\alpha=(\alpha+c)\bmod5
}
$$

and

$$
\boxed{
\bar\beta=\beta\oplus j.
}
$$

The emitted decimal digit is

$$
\boxed{
d=\bar\alpha+5\bar\beta.
}
$$

This equals exactly

$$
(S+c)\bmod10.
$$

The important simplification is:

$$
\boxed{
\nu\text{ does not directly enter the emitted digit.}
}
$$

It affects the future only through its carry/reset role.

So \(\nu\) is a control/reset register, not direct digit payload.

---

# 9. Exact pair reconstruction is \(F_5\) addition plus one binary full adder

Take two normalized decimal digits represented as

$$
(\bar\alpha_1,\bar\beta_1),
\qquad
(\bar\alpha_2,\bar\beta_2).
$$

Let

$$
s=\bar\alpha_1+\bar\alpha_2.
$$

Then

$$
\boxed{
\alpha'=s\bmod5
}
$$

and define

$$
\boxed{
\delta=[s\ge5].
}
$$

Now form

$$
H=\bar\beta_1+\bar\beta_2+\delta.
$$

Then

$$
\boxed{
\beta'=H\bmod2
}
$$

and

$$
\boxed{
\nu'=[H\ge2].
}
$$

Therefore

$$
\boxed{
S'=\alpha'+5\beta'+10\nu'.
}
$$

This is an exact identity.

So the complete local decimal pair arithmetic is

$$
\boxed{
F_5\text{ addition}
\quad\longrightarrow\quad
1\text{-bit full adder}.
}
$$

No large carry transducer is hiding here.

---

# 10. One-step pair recurrence in ordinary coordinates

The existing pair recurrence should remain as a differential oracle and geometry reference.

For no growth,

$$
\boxed{
S'_i
=
2S_i+C_i+R_{i+1}
-
10(C_{i+1}+R_i).
}
$$

Recall

$$
R_i=C_{m-i}.
$$

For growth,

$$
\boxed{
S'_0=S_0+1-10C_1
}
$$

and by symmetry

$$
S'_m=S'_0.
$$

For

$$
1\le i<m,
$$

$$
\boxed{
S'_i
=
S_i+S_{i-1}+C_i+R_i
-
10(C_{i+1}+R_{i-1}).
}
$$

These formulas must agree exactly with the mixed-radix normalizer/full-adder implementation.

---

# 11. Same recurrence expressed through local digit pairing

This is the preferred implementation view.

Define

$$
N(q,c)
=
(\bar\alpha,\bar\beta)
$$

using the normalization law above, and define

$$
A(x,y)
$$

as the \(F_5+\)binary-full-adder pair combiner.

Then for no growth:

$$
\boxed{
q'_i
=
A\left(
N(q_i,C_i),
N(q_i,R_{i+1})
\right).
}
$$

For growth, the edge is

$$
\boxed{
q'_0
=
A\left(
N(q_0,0),
(1,0)
\right),
}
$$

where \((1,0)\) is decimal digit \(1\).

For an internal growth position,

$$
\boxed{
q'_i
=
A\left(
N(q_i,C_i),
N(q_{i-1},R_i)
\right),
\qquad1\le i<m.
}
$$

This cleanly separates:

$$
\boxed{
\text{geometry chooses the two source digits;}
\qquad
\text{the arithmetic law never changes.}
}
$$

Growth is therefore primarily a **source-coordinate rewiring** problem, not a different arithmetic system.

---

# 12. Binary shift-register structure

For a no-growth position, let the two incoming digit carries be

$$
c_L,c_R\in\{0,1\}
$$

and

$$
A=c_L+c_R\in\{0,1,2\}.
$$

Away from

$$
\alpha=4,
$$

there is no base-5 wrap in either digit.

Then

$$
\boxed{
\alpha'=(2\alpha+A)\bmod5,
}
$$

$$
\boxed{
\beta'=[2\alpha+A\ge5],
}
$$

$$
\boxed{
\nu'=\beta.
}
$$

Thus generically the binary planes behave as

$$
\boxed{
(\beta,\nu)\mapsto(\beta',\beta).
}
$$

They are a shift register driven by the \(F_5\) phase/carry sum.

The only exceptional phase is

$$
\boxed{\alpha=4.}
$$

At \(\alpha=4\):

### \(A=0\)

$$
\boxed{
\beta'=1,\qquad\nu'=\beta.
}
$$

### \(A=1\)

$$
\boxed{
\beta'=1,\qquad\nu'=0.
}
$$

### \(A=2\)

$$
\boxed{
\beta'=0,\qquad\nu'=1-\beta.
}
$$

The \(\alpha'\) equation

$$
\alpha'=(2\alpha+A)\bmod5
$$

still holds.

So an accurate structural summary is

$$
\boxed{
F_5\text{ phase dynamics}
+
\text{binary shift register}
+
\text{finite normalization defect at }\alpha=4.
}
$$

Do **not** reinterpret the \(\alpha=4\) phase as a new carry-event history. Carry itself is already determined by LT/EQ/GT.

For algebraic manipulation only, if

$$
a=\alpha+1\pmod5,
$$

then the indicator of the exceptional \(a=0\) phase is

$$
1-a^4
$$

over \(F_5\).

The EQ/wire indicator is

$$
\boxed{
w=\beta(1-a^4).
}
$$

This polynomial identity is optional implementation algebra, not additional semantic state.

---

# 13. Temporal-history quotient: H=20

Older research proved a separate but still useful theorem.

For general radix \(b\), define

$$
w=\operatorname{bit\_length}(2b-2).
$$

For decimal,

$$
w=\operatorname{bit\_length}(18)=5.
$$

The proved horizon is

$$
\boxed{
H=4w=20.
}
$$

The result is that every \(H\)-step interval contains enough source-annihilating no-growth doubling to remove dependence on pair history older than that bounded horizon modulo \(2^w\).

Because decimal pair coefficients satisfy

$$
0\le S_i\le18<32=2^5,
$$

the reconstructed endpoint is exact rather than merely a residue.

Historically this yielded a 20-row carry/forcing slab.

That slab is **not** the desired production representation anymore.

Interpret the theorem as:

$$
\boxed{
\text{temporal history older than H=20 is provably irrelevant}.
}
$$

Do not store 20 carry rows as identity.

The current carry-domain/prefix-monoid quotient is stronger spatially.

H=20 may remain:

* a theorem/interface invariant;
* an exactness certificate;
* an oracle/differential test;
* bounded bootstrap evidence.

It must not become a replay path or a persistent temporal tape.

---

# 14. Frobenius/radial affine quotient

The pair recurrence separates into a homogeneous spatial action and an additive innovation.

For one step,

$$
\boxed{
S_{t+1}=A_gS_t+E_t
}
$$

where

$$
\boxed{
A_0=2I
}
$$

for no growth and

$$
\boxed{
A_1=I+z
}
$$

in the uncentered shift convention for growth.

Therefore a block containing

* \(q\) no-growth transitions;
* \(r\) growth transitions

has homogeneous multiplier

$$
\boxed{
M_{q,r}=2^q(1+z)^r.
}
$$

The exact block is affine:

$$
\boxed{
S_{\rm out}
=
2^q(1+z)^rS_{\rm in}
+
B.
}
$$

For two affine blocks

$$
F_1(x)=M_1x+B_1
$$

and

$$
F_2(x)=M_2x+B_2,
$$

composition is

$$
\boxed{
F_2\circ F_1
=
(M_2M_1)x
+
(M_2B_1+B_2).
}
$$

This is the cocycle law the powered action should use.

The repository already implements this in:

* `src/number_compiler/core/radial_innovation.py`
* `src/number_compiler/core/cyclotomic_affine.py`
* `src/number_compiler/core/cyclotomic_transport.py`
* `src/number_compiler/families/reverse_field_action.py`

Do not duplicate it in the powered local codec.

---

# 15. Cyclotomic / 2-adic source annihilation

For a power-of-two cyclotomic sector

$$
\Phi_{2m}(z)=z^m+1,
$$

the existing radial quotient uses the identity

$$
\boxed{
(1+z)^m=2U_m(z)
\pmod{z^m+1}.
}
$$

Hence the 2-adic content valuation of

$$
2^q(1+z)^r
$$

contains

$$
\boxed{
q+\left\lfloor\frac rm\right\rfloor.
}
$$

Once that valuation reaches the decimal precision

$$
w=5,
$$

the old source contribution vanishes modulo \(32\).

Only the bounded transported innovation remains.

The current production `ReverseAddCyclotomicInnovationBlock` already represents exactly this pattern:

$$
\boxed{
\text{large radial multiplier represented by quotient parameters}
+
\text{bounded innovation}.
}
$$

Keep that code.

The local mixed-radix quotient and the radial/cyclotomic quotient solve different dimensions:

$$
\boxed{
Q_{\rm MR}
\text{ solves local digit/carry arithmetic;}
}
$$

$$
\boxed{
Q_{\rm radial}
\text{ solves large temporal linear transport.}
}
$$

They must be connected rather than replaced by each other.

---

# 16. What the old experiments established

Do not repeat these dead ends.

## A. Carry action alone is insufficient

Distinct pair values can share the same carry function while having different future output.

Example pattern:

$$
S=2,\quad S=4
$$

both induce `CONST0`, but obviously produce different digits and futures.

Therefore

$$
\boxed{
Q_{\rm carry}
}
$$

is a quotient of nonlinear **boundary carry behavior**, not complete exact output content.

The output morphism must remain separate.

## B. Old T² contextual boundary key was not successor-congruent

A historical key based approximately on

$$
(\text{left T² boundary behavior},
S,
\text{right T² boundary behavior})
$$

had successor conflicts.

Backward refinement approached exact trajectory identity.

Do not revive this key or append larger finite lookahead to it.

The problem was that it tried to make a flat contextual state stand in for exact recursive output behavior.

## C. Flat T⁴/T⁸/T¹⁶ continuation states exploded

Directly promoting composed higher continuation syntax to larger macro states recreated thousands of residuals.

Do not teach `semantic_state_codec` to understand arbitrarily large temporal continuations.

## D. The old H=20 lookup grammar was exact but spatially expensive

The old fixed carry-slab approach had bounded temporal height but still retained too much spatial forcing information.

Its charged description size was polynomial rather than polylogarithmic.

That result is evidence against the **slab representation**, not against the newer LT/EQ/GT + mixed-radix quotient.

## E. Compact temporal operator syntax already existed

Previous exact formula experiments had tiny binary operator DAGs while projection generated enormous left/right residual families.

That proves:

$$
\boxed{
\text{logarithmic action syntax alone is insufficient}.
}
$$

The output observer itself must respect the quotient.

The new mixed-radix digit/output law should now be installed exactly at that missing boundary.

---

# 17. Current implementation diagnosis

Work from the current canonical repository. Do not start a parallel implementation.

## `runtime/powered_local_codec.py`

This already declares the intended protocol:

```python
PoweredLocalEffect(
    interface: LocalInterfaceID,
    output: CoordinateOutputMorphismID,
)
```

and operations:

```python
leaf_interface(...)
compose_spatial(...)
compose_temporal(...)
transformed(...)
observe_output(...)
```

This is the correct seam.

## `families/reverse_powered_local_codec.py`

Current docstring explicitly says the codec is deliberately **spatial**.

It currently provides the exact directed finite spatial boundary actions and reflection canonicalization.

Preserve that work.

The missing work is to make this class fulfill the complete `PoweredLocalCodec` contract.

## `families/reverse_coordinate_program.py`

Current executable semantics are essentially:

```python
pair_steps: int
normalized: bool
```

Composition adds `pair_steps`.

Power multiplies `pair_steps`.

This is a compact temporal **description**, but it is not an observation algorithm.

Never execute

```python
for _ in range(pair_steps):
    ...
```

or an equivalent hidden continuation traversal.

`pair_steps` can remain source-free action metadata, but output observation must be provided by the powered quotient/tile algebra.

## `runtime/recursive_outputs.py`

`RecursiveOutputTemporal` currently records approximately

```python
provider
action
interface
```

but its own documentation admits that observation still calls the registered temporal evaluator and therefore does **not** prove output absorption.

This is exactly the incomplete seam.

## `families/reverse_recursive_image_runtime.py`

Current `_temporal_emit()` ultimately calls:

```python
evaluate_temporal_leaf(...)
```

That is the release blocker.

A compiled temporal parent must never return to that interpreter for point/width observation.

## `families/reverse_runtime.py`

The runtime already constructs

```python
ReversePoweredLocalCodec(...)
```

and compiles the immutable source through

```python
powered_local.source_action(source_binding)
```

once.

So the spatial half is already connected.

Finish this connection; do not build another backend beside it.

## `families/reverse_higher_interface.py`

The existing higher interface already enumerates the thirteen channels:

1. `boundary_left`
2. `boundary_right`
3. `output`
4. `activity`
5. `first_active`
6. `last_active`
7. `extent`
8. `halo_left`
9. `halo_right`
10. `growth`
11. `termination`
12. `normalization`
13. `frame`

The new codec must preserve all thirteen compositionally.

---

# 18. Implement one pure mixed-radix kernel first

Add only a small algebraic helper, not a new semantic state system.

Something equivalent to:

```python
@dataclass(frozen=True, slots=True)
class MRPair:
    alpha: int  # F5
    beta: int  # F2
    nu: int  # F2
```

with exact helpers:

```python
def decode_pair(S: int) -> MRPair:
    assert 0 <= S <= 18
    return MRPair(
        alpha=S % 5,
        beta=(S % 10) // 5,
        nu=S // 10,
    )
```

```python
def carry_fn(q: MRPair) -> CarryFn:
    wire = q.alpha == 4 and q.beta == 1
    if wire:
        return CarryFn.ID
    return CarryFn.CONST1 if q.nu else CarryFn.CONST0
```

```python
def normalize_digit(q: MRPair, carry: int) -> tuple[int, int]:
    wrap = int(q.alpha == 4 and carry == 1)
    return (
        (q.alpha + carry) % 5,
        q.beta ^ wrap,
    )
```

```python
def combine_digits(
    x: tuple[int, int],
    y: tuple[int, int],
) -> MRPair:
    s = x[0] + y[0]
    alpha = s % 5
    carry5 = int(s >= 5)

    h = x[1] + y[1] + carry5
    beta = h & 1
    nu = int(h >= 2)

    return MRPair(alpha, beta, nu)
```

These routines must be exhaustive-tested before any runtime modification.

They are formulas, not persistent semantic objects.

---

# 19. Exhaustive kernel tests

Before touching the scheduler, require:

### Pair encoding

For every

$$
S=0,\ldots,18,
$$

verify

$$
S=\alpha+5\beta+10\nu.
$$

Verify `(4,1,1)` is rejected.

### Carry

For all

$$
S=0,\ldots,18,
\qquad
c\in\{0,1\},
$$

verify

$$
\operatorname{apply}(\operatorname{carry\_fn}(Q(S)),c)
=
[S+c\ge10].
$$

### Digit normalization

For the same exhaustive domain verify

$$
\bar\alpha+5\bar\beta
=
(S+c)\bmod10.
$$

### Pair combination

For every valid normalized digit pair verify

$$
\alpha'+5\beta'+10\nu'
=
d_1+d_2.
$$

### Local no-growth transition

For every valid \(S\) and all four carry pairs

$$
(c_L,c_R)\in\{0,1\}^2,
$$

verify the mixed-radix result equals direct decimal reconstruction.

### Growth transition

Exhaustively compare the edge and shifted-interior formulas against the existing pair recurrence over small symmetric pair words.

No sampling is sufficient for the finite local algebra.

---

# 20. Make `ReversePoweredLocalCodec` output-complete

Refactor the existing class rather than replacing it.

It should continue to own/reuse:

* finite forward and reverse boundary actions;
* spatial action interning;
* reflection canonicalization;
* source recursive action compilation;
* semantic alias accounting.

Add the complete protocol operations.

## `validate_action`

Delegate to the authoritative `ReverseFieldActionArena`.

## `leaf_interface`

For one immutable source symbol and bounded left/right state:

1. decode \(S\to(\alpha,\beta,\nu)\);
2. derive the LT/EQ/GT carry action;
3. normalize the source digit(s);
4. compute the exact output pair/digit law;
5. publish the complete thirteen-channel interface;
6. publish its coordinate output morphism;
7. return

```python
PoweredLocalEffect(interface, output)
```

No source provenance belongs in the `LocalInterfaceID`.

## `compose_spatial`

Compose:

* left/right carry actions using the existing finite action arena;
* midpoint wiring;
* output morphisms as recursive branches;
* halos;
* activity/extent;
* growth;
* normalization;
* frame/cocycles.

Do not concatenate digit words.

Do not copy source children into semantic interface keys.

Exact output children remain recursive output identities.

## `compose_temporal`

This is the central release fix.

For

```python
compose_temporal(before, after, source, ...)
```

perform semantic substitution:

$$
\boxed{
\text{after}
\circ
\text{before}
}
$$

over the already-bounded interface/output algebra.

Do **not**:

* emit a midpoint image;
* call `evaluate_temporal_leaf`;
* enumerate all intermediate generations;
* expand `pair_steps`;
* build a continuation tape;
* construct the complete output word.

Use:

* `ReverseFieldActionArena.compose()` for the powered temporal action;
* the mixed-radix local laws for digit/carry substitution;
* recursive output composition for exact spatial content;
* existing interface composition for the thirteen channels.

After composition, intern/canonicalize immediately.

## `observe_output`

Observation must consume the already-published `PoweredLocalEffect`.

For a point query it may descend the canonical spatial output tree.

It may query bounded sibling boundary actions needed at each midpoint.

It must **not** descend temporal history.

---

# 21. Fix the source-bound recursive output representation

The current problematic form is conceptually:

```text
RecursiveOutputTemporal
    provider
    powered action
    interface
        ↓ observe
    temporal interpreter
```

Replace its execution semantics with:

```text
canonical source/output tile
    +
bounded powered local effect
        ↓
one spatial path / cached future tile
```

Two acceptable implementation shapes are possible.

## Preferred

At temporal composition time, publish an observation-complete recursive future-output morphism.

Then `observe()` only performs spatial descent.

## Acceptable transitional representation

Keep a normalized temporal output node carrying:

```text
provider + complete powered action + complete local interface
```

but its observer must invoke the new powered quotient evaluator directly.

It must never call:

* `evaluate_temporal_leaf`;
* `RuntimeValueArena.action_function`;
* `HigherSummaryArena.runtime_unary`;
* a generic continuation interpreter.

The key criterion is semantic execution, not the class name.

---

# 22. Do not flatten arbitrary temporal depth

The correct recursive law is not:

```text
T² state
→ larger T⁴ state
→ larger T⁸ state
→ larger T¹⁶ state
```

It is:

$$
\boxed{
\text{canonical recursive tile}
+
\text{bounded interface action}.
}
$$

If a temporal light cone becomes wider, move up the spatial macrocell hierarchy.

Do not increase the flat port/state dimension with temporal depth.

This is the HashLife mechanism.

---

# 23. Generalize the scheduler beyond primitive-pair fusion

The current checkpoint still contains a primitive-pair/fused-operation restriction.

Remove that only after exact higher powers pass.

Required direct executions include at least:

$$
P^2,\quad P^4,\quad P^8,\quad P^{16},\quad P^{32}.
$$

Exercise:

* both boundary directions;
* heterogeneous signatures;
* mirrored wiring;
* growth and no-growth geometry;
* odd/even widths;
* blank/halo boundaries.

The arbitrary binary action DAG must be iterative and memoized.

A parent formed from two already-composed children must be legal:

$$
\boxed{
(P^4)\circ(P^4)=P^8,
}
$$

not only

$$
P\circ P.
$$

---

# 24. Populate all thirteen channels from their natural source

Do not force every field through one giant semantic-state representation.

Use:

| Channel             | Source                                                 |
| ------------------- | ------------------------------------------------------ |
| boundary left/right | finite carry/local action codec                        |
| output              | mixed-radix coordinate morphism + recursive exact tile |
| activity            | output/nonblank law                                    |
| first/last active   | recursive child summaries                              |
| extent              | recursive activity summary                             |
| halo left/right     | symbolic geometry                                      |
| growth              | final carry / geometry                                 |
| termination         | blank/output predicate                                 |
| normalization       | exact mixed-radix digit normalization                  |
| frame               | existing phase/geometry cocycle                        |

This is a product of small algebras, not one flattened state set.

---

# 25. Keep the radial action in `ReverseFieldActionArena`

`ReverseFieldActionArena.power()` already performs binary exponentiation.

Do not move temporal powering into the local codec.

The desired division is:

```text
ReverseFieldActionArena.power(N)
        ↓
source-independent O(log N) action

canonical recursive source
        ↓
ReversePoweredLocalCodec

LocalInterfaceID
+
CoordinateOutputMorphismID
        ↓
recursive scheduler

point / width / future TileID
```

The codec applies the powered action to space.

It does not rediscover the power.

---

# 26. Do not misuse `pair_steps`

`ReverseCoordinateProgram(pair_steps=N)` can remain a canonical statement that the action represents \(N\) pair transitions.

But it must never mean:

```python
execute N pair transitions when somebody asks for a digit
```

After this fix, `pair_steps` is metadata/proof identity, not a replay recipe.

A useful structural guard is:

```python
if powered_observation_scope:
    forbid_iteration_over_pair_steps()
```

or an equivalent instrumentation gate.

---

# 27. Production cutover order

## Stage 1 — exact local algebra

Add exhaustive mixed-radix tests.

No public behavior change yet.

## Stage 2 — complete `ReversePoweredLocalCodec`

Implement:

```python
leaf_interface
compose_spatial
compose_temporal
transformed
observe_output
```

using existing arenas.

## Stage 3 — arbitrary-depth scheduler

Remove the primitive-pair admission limit after P⁴/P⁸+ tests succeed.

## Stage 4 — replace temporal observation

Remove the production dependency:

```text
ReverseRecursiveImageRuntime._temporal_emit
    → evaluate_temporal_leaf
```

for compiled powered parents.

## Stage 5 — public reverse path

Make `ReverseAddPoweredTerm` use only the new route.

## Stage 6 — delete obsolete competing execution

Only after poison tests pass, remove/dead-end the old production higher-continuation path.

Do not leave it as a fallback.

Reference/oracle code may remain explicitly isolated under test/oracle namespaces.

---

# 28. Mandatory unchanged absorption gate

Keep all ten existing tests in

```text
tests/test_powered_output_absorption.py
```

unchanged.

They cover:

$$
N=16,32,64,128,256
$$

times

```text
point
width
```

and deliberately poison the old temporal evaluator after parent compilation.

All ten must pass.

Do not change:

* the requested coordinates;
* cache disabling;
* poison points;
* expected scalar oracle;
* counter assertions.

A passing rewritten/weakened test is not acceptance.

---

# 29. Add stronger poison tests

After parent publication, poison all of:

```text
evaluate_temporal_leaf
RuntimeValueArena.action_function
HigherSummaryArena.runtime_unary
generic higher continuation execution
whole-word reverse successor
pair-step replay
old fixed-H slab successor
```

Then require exact:

* left point;
* center point;
* right point;
* width;
* growth;
* normalization.

A compiled parent must survive with all temporal replay routes unavailable.

---

# 30. Temporal composition algebra tests

Require exact identities such as

$$
\boxed{
\operatorname{compose}(P^a,P^b)=P^{a+b}
}
$$

for powers assembled by different trees.

Test associativity:

$$
(P^aP^b)P^c
=
P^a(P^bP^c)
$$

at the complete observable interface/output level.

Test mirror/conjugacy equivariance.

Test that identical carry interfaces with different exact output content do **not** alias output tile identity.

Test that distinct exact contents with identical complete future interface **can** share the `LocalInterfaceID`.

---

# 31. Differential tests against the integer oracle

For manageable horizons, compare:

```text
powered quotient implementation
vs
ordinary Python integer reverse-and-add
```

for:

* 196;
* small randomized decimal seeds;
* odd/even digit lengths;
* repeated growth;
* long threshold/equality runs;
* values containing many 9 pair coefficients.

Use the oracle only in tests.

Never call it from production.

---

# 32. Complexity/accounting gates

For cold powers

$$
N=16,32,64,128,256,512,1024,
$$

record independently:

* field-action nodes;
* field-action compositions;
* local-interface nodes;
* interface aliases;
* output-morphism nodes;
* future-tile entries;
* spatial descents;
* temporal descents;
* higher concrete evaluations;
* carry action operations;
* exact output reuse;
* successfully absorbed temporal span;
* retained nodes;
* peak workspace.

Required:

$$
\boxed{
\text{higher temporal interpreter calls after compilation}=0.
}
$$

Required:

$$
\boxed{
\text{temporal leaf descents after compilation}=0.
}
$$

Required:

$$
\boxed{
\text{successful absorbed span}\ge N-1
}
$$

for a generation-\(N\) reverse output where \(N-1\) pair transitions are expected.

Do not treat a small primitive fused span as evidence for the complete request.

---

# 33. Warm-reuse gate

For a repeated exact request:

* do not construct new children;
* do not execute reducers;
* do not execute higher continuations;
* do not reconstruct carry prefixes unnecessarily;
* do not regenerate the future tile.

A genuine cache hit must prevent semantic objects from being constructed, not deduplicate them afterward.

Late equality is an architecture failure to investigate.

---

# 34. Anti–fake-green rules

The release must fail if any of the following happens.

### Hidden linear replay

```python
for step in range(N):
```

or equivalent recursion through the temporal action tree.

### Hidden full-width sweep for point/width

A point observation cannot scan every pair/digit.

### Packed carry/event history

No H-row tape, event itinerary, or carry slab in production semantic identity.

### Injective re-encoding presented as compression

\(Q_{\rm MR}\) is bijective and must be described as such.

### Carry-only exact-output alias

`CONST0/ID/CONST1` is insufficient to identify exact output content.

### Opaque continuation declared a quotient

A recipe is not a `LocalInterfaceID`.

### Sampled equality used as proof

Interface equivalence requires complete admissible continuation semantics.

### Hard-coded release booleans

No flags such as:

```python
production_radix_carrier_aligned = True
```

may substitute for executable evidence.

### Old path retained as fallback

If the fast path fails, production must fail closed rather than silently replay.

---

# 35. Source files to modify/reuse

Primary implementation targets:

```text
src/number_compiler/runtime/powered_local_codec.py
src/number_compiler/families/reverse_powered_local_codec.py
src/number_compiler/families/reverse_coordinate_program.py
src/number_compiler/families/reverse_recursive_image_runtime.py
src/number_compiler/runtime/recursive_outputs.py
src/number_compiler/families/reverse_runtime.py
src/number_compiler/families/reverse_higher_interface.py
```

Reuse rather than duplicate:

```text
src/number_compiler/core/carry_monoid.py
src/number_compiler/core/pair_algebra.py
src/number_compiler/core/prefix_monoid.py
src/number_compiler/families/reverse_domain.py
src/number_compiler/core/radial_innovation.py
src/number_compiler/core/cyclotomic_affine.py
src/number_compiler/core/cyclotomic_transport.py
src/number_compiler/families/reverse_field_action.py
```

Scheduler/absorption work may additionally touch the existing shared tile scheduler and absorption machinery.

Do not create a second reverse state hierarchy.

---

# 36. Historical research files the agent should read before changing semantics

Read these as research evidence, not necessarily as production architecture to restore:

```text
GENERALIZED_POWER_RESULTS.md
ACTION_MORPHISM_RESULTS.md
RADIAL_INNOVATION_RESULTS.md
SHARED_DAG_POWER_RESULTS.md
HASHLIFE_STATE_ACTION_GROWTH_RESULTS.md
HASHLIFE_BOUNDARY_QUOTIENT_CHECKPOINT.md
HASHLIFE_CUTOVER_PLAN.md
POWERED_LOCAL_CODEC_MIGRATION.md
LINEAR_BISIMULATION_CHECKPOINT.md
```

Important historical patches/notes include:

```text
number_compiler_v0.59.1_successor_closure_contract.patch
number_compiler_v0.59.5_forcing_morphism_hashlife_cache.patch
number_compiler_v0.59.9_spacetime_macrocell_absorption.patch
reverse196_generalized_jump_v0.4.0.patch
reverse196_generalized_power_v0.4.0.patch
```

The purpose is to preserve proved invariants while avoiding the representations that previously exploded.

---

# 37. Correct interpretation of the research history

The progression is:

```text
raw reverse/add digits
    ↓
symmetric pair coefficients S
    ↓
LT/EQ/GT threshold carry quotient
    ↓
three-element reset monoid
    ↓
H=20 proves old temporal history dies
    ↓
cyclotomic/radial quotient powers linear bulk
    ↓
old slab/context representations still over-retained spatial/output syntax
    ↓
mixed-radix S = α + 5β + 10ν exposes exact local output arithmetic
    ↓
F5 addition + binary full adder
    ↓
remaining task = install this as output-complete PoweredLocalCodec semantics
```

The remaining release blocker should therefore **not** be described as:

```text
find the 196 carry quotient
```

or

```text
discover another finite carry state.
```

It is:

$$
\boxed{
\text{finish temporal/output composition of the already-known quotient algebra}.
}
$$

---

# 38. Stop condition for further quotient research

Do not search for another mathematical quotient unless the direct implementation above produces a concrete exact obstruction.

A valid obstruction must be something like:

```text
two states have identical proposed complete interface/output quotient
but one admissible continuation produces different observations
```

and must include the explicit distinguishing continuation.

Only then refine the quotient.

Do not infer a missing theorem merely because the old continuation evaluator grows.

First remove the old evaluator from the experiment.

---

# 39. Definition of done

The reverse release blocker is closed only when all of the following are true:

1. The mixed-radix kernel is exhaustive-exact.
2. LT/EQ/GT carry actions use the existing three-element monoid.
3. No carry/event history is semantic state.
4. `ReversePoweredLocalCodec` implements the complete powered-local protocol.
5. Temporal composition substitutes output semantics without a midpoint.
6. All thirteen macro channels remain exact.
7. Arbitrary-depth composed actions \(P^4,P^8,\ldots\) execute.
8. `evaluate_temporal_leaf` is unreachable after compiled-parent publication.
9. The ten existing powered-output-absorption tests pass unchanged.
10. Point/width remain exact with the old higher evaluator poisoned.
11. Cold \(N=16\ldots1024\) shows zero higher temporal replay.
12. Successful absorbed span covers the entire requested temporal span.
13. No generation loop or whole-word scan hides behind a cache.
14. Exact output tile identity remains separate from behavioral interface identity.
15. Ruff, strict mypy, structural gates, full pytest and the performance/watchdog gates pass.
16. Obsolete production continuation paths are removed rather than retained as fallback.

The implementation should continue through these gates rather than stopping after adding the formulas or making only the primitive-pair case green.
