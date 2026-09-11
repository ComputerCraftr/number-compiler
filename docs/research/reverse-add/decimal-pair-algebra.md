# Decimal pair algebra and its execution boundary

This summary integrates the supplied [research note](../../archive/reverse-add/DECIMAL_PAIR_QUOTIENT_RESEARCH.md)
into the current tile runtime. The original note is preserved verbatim; its
`core`, `families`, and `runtime` paths describe an older checkout. It is research
input, not a current execution or performance attestation. The implementation
sequence is maintained in the [cutover optimization plan](../../hashlife-optimization.md).

## Exact local laws

For LSD-first decimal digits, let `S_i = d_i + d_(m-1-i)`. The pair word is
symmetric, with `0 <= S_i <= 18`. One physical forward carry track suffices:

\[
C_0=0,\qquad C_{i+1}=[S_i+C_i\ge10],\qquad
y_i=S_i+C_i-10C_{i+1},\qquad g=C_m.
\]

The right-facing boundary is the reflected view `R_i = C_(m-i)`, not a second
independent physical carry. Reflection transports coordinates and interfaces;
physical carry still propagates toward the most significant digit.

The existing three-element monoid is the carry quotient:

| Pair coefficient | Carry function |
| --- | --- |
| `S < 9` | `CONST0` |
| `S = 9` | `ID` |
| `S > 9` | `CONST1` |

For `compose(after, before)`, a constant `after` absorbs `before`; identity
preserves it. Thus a spatial interval's exit is determined by its last non-EQ
cell in physical scan order, or by identity if all cells are EQ. A parent can
compose child transfer IDs without scanning a retained carry row.

The mixed-radix coordinates are

\[
S=\alpha+5\beta+10\nu,\quad
\alpha=S\bmod5,\quad \beta=\lfloor(S\bmod10)/5\rfloor,\quad
\nu=\lfloor S/10\rfloor.
\]

The domain is `F5 × F2 × F2` excluding `(4,1,1)`. It has 19 elements and is
**bijective** to the original pair alphabet. It is useful algebraic factoring,
not a 19-state compression. The smaller carry projection is
`(nu, w)` with `w = [alpha == 4 and beta == 1]`: transmit if `w`, otherwise
reset to `nu`. No age, provenance, birth position, or carry history is needed.

For incoming carry `c`, digit normalization uses

\[
\bar\alpha=(\alpha+c)\bmod5,\quad
\bar\beta=\beta\mathbin{\oplus}[\alpha=4\land c=1],\quad
y=\bar\alpha+5\bar\beta.
\]

To pair two normalized digits, put `s = alpha1 + alpha2` and
`h = beta1 + beta2 + [s >= 5]`. Their output is
`(s % 5, h % 2, [h >= 2])`. This is F₅ addition plus one Boolean full adder.
The reset register `nu` affects carry but does not directly enter the emitted
digit. This allows shared symbolic subfunctions without dropping exact output.

Geometry chooses which normalized digits are paired. With `N` denoting the
normalizer and `A` the digit combiner:

\[
q'_i=A(N(q_i,C_i),N(q_i,R_{i+1}))\quad(g=0),
\]

\[
q'_0=q'_m=A(N(q_0,0),(1,0)),\qquad
q'_i=A(N(q_i,C_i),N(q_{i-1},R_i))\quad(0<i<m,\ g=1).
\]

For no-growth cells outside `alpha=4`, writing `a=c_L+c_R` gives
`alpha'=(2*alpha+a)%5`, `beta'=[2*alpha+a>=5]`, `nu'=beta`.
At `alpha=4`, `(beta',nu')` is respectively `(1,beta)`, `(1,0)`, or
`(0,1-beta)` for `a=0,1,2`. This exception is a finite local normalization law,
not an event-history register.

## Temporal algebra and what it forgets

The exact branch-dependent affine law is

\[
S_{out}=2^q(1+z)^rS_{in}+B,\qquad q+r=N.
\]

Composing before `(M1,B1)` and after `(M2,B2)` gives
`(M2*M1, M2*B1+B2)`. Store exponent metadata and fixed-arity hash-consed
expressions. Resolving branch-dependent growth or forcing must execute local
interfaces; it cannot discover `q,r,B` through a generation itinerary or fill
them with neutral placeholders. Binary action syntax alone does not accelerate
that resolution.

The existing event-memory theorem applies to **base >= 3**. With
`w=bit_length(2b-2)` and `H=4w`, enough no-growth doublings annihilate the old
source modulo `2**w`. Decimal gives `w=5,H=20`. Reconstructing every endpoint
coefficient modulo 32 from the required forcing and geometry is exact because
each coefficient lies in `[0,18]`. This does **not** say a single finite
residue identifies an arbitrary complete future field. Base 2 retains its
separate kernel laws.

In a power-of-two cyclotomic factor `z**m+1`, the identity
`(1+z)**m = 2*U_m(z)` gives the sector's radial annihilation criterion.
For nondegenerate sectors the valuation includes `q + floor(r/m)`; the
`m=1` exact-zero case follows its existing implementation. Dropping source
dependence is justified only in that sector/modulus. A folded cyclotomic
residue cannot recover arbitrary spatial coefficients by itself. Preserve
every symbolic dependency still needed by exact coordinate output.

Before the branch is observed, `q+r=N` still gives the sharp uniform bound

\[
q+\lfloor r/m\rfloor\;\geq\;\lfloor N/m\rfloor.
\]

The symmetric outer-coefficient law gives a second, independent bound. Growth
requires the outer pair coefficient to be at least `b-1`; on a growth step that
coefficient follows `s -> 1+s-b*[s>=b]`. For `b>=3` its longest permitted chain
is `2b-2 -> b-1 -> b -> 1`, so four consecutive growths are impossible and
`q>=floor(N/4)`. The production plan carries an immutable certificate for this
finite kernel graph. Decimal therefore kills every old-source coefficient
modulo 32 after 20 steps, including the `m=8` sector.

The production temporal action may therefore carry a fixed-arity product of
these source-coefficient bounds.  It can mark one mod-32 sector independent of
the old source once that sector's bound reaches five.  The product does not
contain the branch-dependent unit or forcing term `B`, and it does not claim
that an output coordinate is resolved.  Those remain symbolic until the local
successor interfaces execute.  Composing two plans adds their exact step
metadata and recomputes the same bounds; it never invents `q` or `r`.

H=20 therefore supplies a theorem/interface bound. Production must not build
20 generations, exact carry rows, packed history columns, or a slab inverse
before applying it. Compose shared powers with `16+4` when that theorem action
is needed. The carry monoid, mixed-radix factorization, and radial quotient
address different parts of the problem and are not interchangeable.

## Executable spatial products

The decimal tile adapter now composes closed arithmetic port functions at
spatial parents. Its left transfer retains the finite carry/edge/blank state;
its right transfer retains two `CarryFn` values. Exact edge output keeps the
mixed-radix local law. Activity is one 43-bit predicate over the fixed left
port, independent of temporal depth. No parent substitution expands the
Cartesian port domain into a Boolean decision graph on this route.

`ReverseCarrySectorTransfer` additionally composes projected symbol sums and
incoming/outgoing carry sums for `m=1,2,4,8`. These are fixed mod-32 functions
of the two possible incoming carries, not spatial coefficient arrays or
temporal rows. Physical width and contiguous activity extent are geometry.
The carry exit determines growth; the projected carry differences determine
the forcing residues, including reflection and the growth displacement.
Neither growth nor the forcing event needs to be supplied by an orbit loop.

The authenticated tile-sector observation validates the original symmetric
pair field, initial contracts, and sufficient padding. Before certified source
death, it obtains the first and last primitive-input summaries from the tile
scheduler and computes each affine innovation as `S_out - M*S_in` in its
bounded ring. At H=20 and beyond, the issued decimal certificate eliminates
`M*S_in` in all four sectors: the observer reads the original contiguous extent
from its threshold summary and skips original-source sector compilation. The
final input interface is still required to obtain output forcing and the
growth cocycle. Exact output retains its original source binding.

The aligned interval observer separately consumes the local forcing law with
its physical reflected partner, incoming carries and, on growth, the required
predecessor halo. It rejects intervals crossing unsupported normalization
edges instead of substituting whole-field forcing for a child interval.
Neither observer builds a complete endpoint or accepts a caller-supplied event
vector. These connections make the sector product executable; they do not yet
discharge arbitrary composite temporal dependencies. Measure source elisions,
interval observations, final-interface work and exact causal work separately.

## Behavioral identity and symmetry

Keep action identity, exact TileID, local interface, and profile-bound future
behavior distinct. `S=2` and `S=4` share `CONST0` yet emit different digits.
They may alias for a certified carry consumer; they cannot share exact output
content or a profile admitting unrestricted identity-digit observations.

Myhill–Nerode/bisimulation reductions must preserve every observation and both
directional successors admitted by the consumer profile, including extent,
halos, normalization, growth and cocycles. Test spatial homomorphism and
successor congruence before publication. A repeated output recipe or equality
only on visited examples does not supply that certificate.

The signed defect `Delta=S-9` and cyclic coordinate `X=Delta mod20` make
pair conjugacy `S -> 18-S` become `X -> -X`. LT and GT exchange, EQ remains
fixed. This local identity is evidence for compiling a conjugacy law; request
normalization still needs the full certificate for both contracts, boundary
tiles, geometry, blank semantics and outgoing metadata. The certified commuting
mirror/conjugacy subgroup is not automatically the eight-element D4 group.
Carry resets are endomorphisms, not invertible symmetries.

## Canonical implementation owners

These links describe current responsibilities, not a handwritten source manifest:

| Algebra or execution | Existing owner |
| --- | --- |
| Carry function and composition | [carry_monoid.py](../../../src/number_compiler/arithmetic/carry/carry_monoid.py) |
| Shared spatial prefix algebra | [prefix_monoid.py](../../../src/number_compiler/arithmetic/carry/prefix_monoid.py) |
| Symbolic pair recurrence | [pair_algebra.py](../../../src/number_compiler/arithmetic/formula/pair_algebra.py) |
| Exact decimal pair coordinates | [decimal_pair_coordinates.py](../../../src/number_compiler/arithmetic/formula/decimal_pair_coordinates.py) |
| Factored primitive output compiler | [tile_decimal_functions.py](../../../src/number_compiler/hashlife/interfaces/tile_decimal_functions.py) |
| H theorem and exact proof reconstruction | [event_memory.py](../../../src/number_compiler/arithmetic/carry/event_memory.py) |
| Radial and affine sector laws | [radial_innovation.py](../../../src/number_compiler/arithmetic/fields/radial_innovation.py), [cyclotomic_affine.py](../../../src/number_compiler/arithmetic/polynomials/cyclotomic_affine.py), [cyclotomic_transport.py](../../../src/number_compiler/arithmetic/polynomials/cyclotomic_transport.py) |
| Reverse algebraic components | [field_action.py](../../../src/number_compiler/sequences/reverse_add/field_action.py) |
| Current public admission | [tile_projection.py](../../../src/number_compiler/hashlife/observation/tile_projection.py) |
| Execution and required causal dependencies | [tile_scheduler.py](../../../src/number_compiler/hashlife/execution/tile_scheduler.py), [tile_causal.py](../../../src/number_compiler/hashlife/execution/tile_causal.py) |

The old research proposal to extend `ReverseRecursiveImageRuntime` is superseded
by the public tile cutover. Port useful local equations into the existing
primitive/interface compiler; do not restore an image/provider executor or
create a second `MRPair` semantic arena. Any small mixed-radix helper is a pure
finite arithmetic component, validated exhaustively against the existing law.

The carry-sector record attached to a local interface is an internal bounded
summary, not an independently authenticated public result. Production width
uses it only when the issued tile application proves the decimal kernel,
initial two-sided ports, empty exterior boundary operands, matching spatial
level, and sufficient source padding. The higher-level sector-product observer
additionally proves one active prefix and exact mirror symmetry from canonical
source regions. The record's constructor currently validates its bounded shape
and leaf constraints; callers must not treat arbitrary constructed records as
proof of a whole-field occurrence. Likewise, radial annihilation means that an
old source term vanishes in the named mod-32 cyclotomic sector. It does not
authorize dropping the exact source binding used by tile output observations.

## Evidence boundaries

The [finite research regressions](../../../tests/arithmetic/formula/test_decimal_pair_coordinates.py)
check all 19 encodings, 38 carry/normalization cases, 100 digit pairs, 76 local
two-carry transitions, 760 symmetric words of widths 1–4, and the carry-conjugacy
and composition identities. The primitive base-ten tile interface now compiles
its exact output directly from the same `F5 x F2 x F2` local law into a reduced
decision function. It does not retain the old 43-by-5 joint output table or a
discarded arithmetic-expression DAG. A dedicated exhaustive runtime check
covers all 20 symbols and every admissible pair of boundary states. The developer
benchmark `python -m devtools.benchmarks.decimal_leaf_output_compiler` compares
both compilers on fresh arenas and reports construction time, semantic nodes,
workspace, and primitive operations.

This is a bounded primitive-interface integration. It neither merges distinct
exact outputs nor establishes a temporal complexity bound for decimal 196.

Local finite identities can be exhaustively checked. Their integration into
arbitrary-depth transfer/output composition, active successor-closed profiles,
and measured sublinear cold work are separate gates. Finite experiments cannot
prove universal logarithmic point or width complexity. Required causal regions
may span a sibling under the approved scheduler contract; constructing those
regions through canonical tiles must remain visible in total-work accounting.
Explicit endpoint emission has at least the cost of its output width.

Preserve the ten absorption cases and their coordinates, cache disabling,
budgets and semantic poison conditions. Their setup now uses the approved
`TileApplication` migration; the research note's obsolete private-type setup
does not reverse that decision. A warm completed parent must avoid descendants;
an unresolved cold dependency may execute bounded primitive laws. The prohibited
temporal-leaf counter is the retired continuation interpreter, not every
legitimate cold scheduler descent.
