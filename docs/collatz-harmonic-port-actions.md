# Collatz harmonic responses and geometry-derived carries

The [shared port-valued owner](port-valued-mealy-actions.md) now supplies both
harmonic composition paths. Carry exits and affine coefficients are views of
complete response rows. Its Isabelle theorem covers arbitrary spatial
composition; exact occurrence normalization separately produces real Hensel
carrier cache hits. Neither replaces the temporal closure gates below.

The reverse/add spatial projection proof transfers to Collatz's two Boolean
carry wires. The executable research controls also reproduce the seven
remaining harmonic-output conflicts. Neither result establishes a compact
successor-closed temporal quotient.

## One coupled response and its carry projection

Encode a carry c in {0,1,2} by u=[c>=1], v=[c=2]. Each radix-64 digit acts
through the existing `CollatzCarryWires` owner. The five nonempty output rows
are 000, 011, 111, 112, 222; the empty interval is the separate identity 012.

For each wire retain its exit function and incoming-carry occupancy emission:

\[
q_{out}=aq+b,\qquad P(q,z)=B(z)+qA(z)\quad\text{in }F_2[y]/y^5.
\]

The derived carry projection forgets the emissions. It commutes with spatial
composition, including every admitted incoming port. Domain action is not an
additional independent input or factor alongside this coupled denotation.
The exit function belongs to the denotation: the polynomial coefficients alone
are not claimed to recover it.

Complete generator exploration at word lengths 1 through 8 reproduces
5, 17, 53, 161, 485, 1,457, 3,752, 7,568 response functions. All project onto
the same five carry actions. Width/phase remains separate spatial geometry;
these are fixed-length counts, not temporal state counts.

Exact geometry supplies every interior carry by composing its prefix actions.
The [shared geometry operations](geometry-derived-carry.md) fill pointwise
gaps in a harmonic projection without retaining another carry state.

## Binary temporal transport and the precise death theorem

For a nonempty frame-normalized tail m, let e=v2(3m+1). An odd original
source may have an **even** normalized tail, so e=0 must be admitted. In
R=(Z/32)[y]/y^5 with z=y-1, the exact finite binary digit jet obeys

\[
J((3m+1)/2^e)=z^{-e}\bigl(yJ(m)+B_m\bigr).
\]

`binary_carry_birth` constructs B independently from redundant binary
coefficients a_i=d_i+d_(i-1). With C0=1 and the normalization recurrence,
B_i=C_i-2C_(i+1). Two zero top bits flush the carry. This is an exact
source-bound validation construction; it is not a source-independent forcing
quotient or a production successor shortcut.

Since z is a unit and y^5=0, any five homogeneous multipliers z^(-e_i)y
have zero product. Isabelle proves this for arbitrary exponents in a
commutative ring with y^5=0, and proves independence of the initial jet for
two runs with the **same event and birth list**. The finite phase control
checks all 6^5=7,776 sequences.

New births depend on the source. Actual five-event trajectories from 1 and 27
have zero homogeneous kernels but different accumulated offsets. Therefore
this theorem does not bound nonlinear refinement depth by five or prove
successor closure.

The spatial and temporal indeterminates must also stay distinct:
z_cell=z_bit^6. In F2[y_bit]/y_bit^5 this gives
y_cell=y_bit^2+y_bit^4, not y_cell=y_bit. The implementation tests this
substitution explicitly.

## Reproduced refinement and its remaining conflicts

On the existing 1,984-source fixture, the complete three-port **binary output
response** is (J(3m), J(3m+1), J(3m+2)) over F2. These rows include transported
source plus carry birth. They are not just the birth jet, nor the radix-64
wire occupancy response described above.

The executable research owner also represents the bounded response as a Mealy
action. Each incoming-carry row emits an outgoing carry and five coefficients
in `F2[y]/y^5`. Concatenation feeds the first outgoing carry into the second
row and translates the second jet by `z_bit^(6L)`. Since `z_bit^24=1` in this
quotient, action identity retains only `L mod 4`; exact extent remains
occurrence geometry. The separate radix-cell threshold-wire response uses a
cell coordinate and retains its distinct `L mod 8` phase. These clocks are not
interchangeable. The normalization produces real canonical aliases: the
one-zero-cell output action equals the five-zero-cell action, and the
one-zero-cell threshold action equals its nine-cell counterpart. An exact
extent field would prevent both canonical aliases. No production cache owns
these research actions yet, so this result does not claim a measured CLI hit
increase.

Across zero-run occurrence lengths 1 through 32, exact extent would create 32
keys. Phase-normalized identity yields 8 threshold-wire actions and 4 output
actions, exposing 24 and 28 potential interner reuses respectively. These are
measured action counts from the executable owner, not production cache-hit
counters.

Adding these output rows to the domain/Hensel key gives 1,977 classes and
exactly seven classes with different successor keys, containing 14 sources:

| Left | Right |
|---:|---:|
| 477 | 797 |
| 481 | 801 |
| 485 | 805 |
| 557 | 877 |
| 1853 | 2173 |
| 1929 | 2249 |
| 3209 | 3529 |

The digit-level Phi5 control is B_d's y_bit^2 coefficient over F5 at incoming
carry one. Its five fibers have sizes 28/16/4/7/9. The pointwise Phi5 word
separates all seven pairs, but the strengthened fixture has 1,984 singleton
classes. Zero conflicts there establish discrimination, not useful closure.
The six phase families retain equality across consumed frame depths 1,193,385.

The supplied 5,000-source, 240-digit relational decimation experiment is not
reproduced here: its named test module and exact corpus construction are absent
from this tree. The attachment reports 1,744 classes, 3,256 retained aliases
and 652 conflicts for schedule (2,3); these remain supplied research results.
The pointwise Phi5 control is not that relational experiment.

## Admitted continuations require labelled event semantics

A forcing root cylinder identifies matching symbols; it does not automatically
define the occurrence's legal input domain. For a precision-12 root under an
unrestricted occurrence domain, one radix-64 symbol matches and all 63 others
are valid dying valuation events. Deleting those mismatches as inadmissible
would create false closure.

Use the existing Hensel slab machinery's separate branch admission and labelled
forcing cylinders. Contextual refinement must retain each symbol's emitted
valuation, resulting admission, and successor class. An unordered set of
successor colors loses these labels and is not a congruence certificate.
Refine until the specified transition system stabilizes, or report a resource
limit; homogeneous five-event death supplies no five-round stopping rule.

## Proof and validation scope

[`Collatz_Harmonic_Ports.thy`](../devtools/proofs/isabelle/Collatz_Harmonic_Ports.thy)
proves carry projection, prefix composition, reachable ports, and conditional
linear source death. Python exact-oracle controls check the binary digit
identity, response counts, conflicts, and gauge families. The Isabelle theory
does not certify the Python implementation or the full nonlinear quotient.

See the [harmonic evidence report](../results/current/collatz-harmonic-ports-2026-09-10/README.md)
and [geometry derivation report](../results/current/geometry-derived-carry-2026-09-10/README.md).
The exhaustive controls are opt-in validation tests; ordinary unit runs keep
small algebraic and adversarial regressions.

The [temporal clock proof checkpoint](temporal-clock-jump-proofs.md) adds checked jump and rebase
laws, including supplied affine effects, matched Hensel prefixes and known-order
square/Lucas clocks. It distinguishes these exact skips from discovery of
unknown nonlinear births and the unresolved full-germ scheduler contract.
