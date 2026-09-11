# Geometry/mod9 and directional state removal

The subsequent [future-consumer cleanup](future-consumer-cleanup.md) records
the generic directional carry owner, workbook collision regressions, and
source-free successor-image audit across the four arithmetic families.

The September 10 replacement reverse/add research mode is selected with
`ReverseGeometryContext(capacity, value_quotient="mod9")`, or with
`python -m devtools.proofs.reverse_consumer_audit --mod9 --capacity 9 --steps 16`.
It uses width and one `(domain, S mod 9)` pair per reflected spatial orbit.
It does not add another coordinate to the previous F5/parity carrier. The
existing CRT and growth-coboundary modes remain available as comparisons.

For a source coefficient S and incoming carry c, the domain supplies K(c).
Writing u=S mod9, the consumed digit is

```
z = [u=0] AND (GT OR (EQ AND c=0))
rho = K(c)-c
D = u+9*z-rho
```

The domain consumer evaluates two such local views and emits only the next
ternary domain. The value consumer emits `u_a+u_b-rho_a-rho_b mod9` through the
existing affine expression owner. The same consumer handles no growth,
growth interiors, centers, and the growth edge, whose other operand is the
constant digit1. No q-view, decimal digit, or 19-valued pair is interned between
these consumers. Carries remain operations on the existing prefix monoid.

Admission preserves all 19 exact source symbols: LT has nine residues, EQ
requires residue zero, and GT has nine residues. Odd centers must decode to an
even coefficient. Padding and capacity overflow remain checked. In particular,
this is not a nine-state successor quotient, nor is structural expression
interning a complete extensional identity for nonlinear functions.

The audit counts q charts, mod10 value operations, independent carry/reset
inputs, and the two output planes. At capacity9, the extent coordinate itself
has ten elements; its explicit width-crop table is excluded from the mod10
value-view count. Derived carry operations are reported separately rather than
hidden behind the zero independent-carry count. `mod9_nodes` and `domain_nodes`
are reachable dependency counts; their shared dependencies must not be summed
as disjoint allocations.

`Reverse_Mod9_Skew.thy` connects the original decimal q definition to the
geometry-derived lift, proves digit reconstruction, and proves the shared
pair-value/residue/domain consumer and growth edge. These are forward local
factorization theorems, not a theorem of bounded temporal residual growth.

For Collatz, the left/right quotient tables now use the actual directional
alphabets of sizes `64>>e` and `2**e`, rather than repeated 64-entry raw-digit
maps. Their class counts remain `(5,1), (5,2), (5,4), (5,5), (4,5), (2,5)`.
The product counts `5,10,20,25,20,10` do not authorize dropping the shift or
identifying two different directional functions just because counts match.

The mismatch certificate now stores only exponent, matched-quarter count,
source digit, and the constant at mismatch. Root digit, local valuation, and
the constant after the root digit are derived from those fields. The germ
transition cache uses the same constructor, so it cannot retain independent
copies of those derived values.

The Hensel angular multiplier is derived from exponent h and mismatch parity:
`(4*3**h) >> (valuation & 1)`. It is no longer stored in the boundary germ.
The values36/18 apply when h=2. Matched prefix length remains emitted valuation
provenance, while the existing occurrence carrier interns the angular action
separately from its live suffix. A two-bit valuation change can preserve that
production action key without equating the complete boundary events.

At capacity9, A16 retains 5,736 total nodes versus 7,769 in the CRT mode.
At capacity16, A32 now fits the same 30,000-node limit with 28,690 total
nodes. This removes a previous budget failure, but consumer occurrences
still grow with the horizon. A32 completion is not an asymptotic bound.

Fermat/Mersenne now share the [square action and carry tile](architecture/arithmetic-square-tiles.md).
Their native classical fallback and terminal germ plan use the common action
owner; bounded digit projections use the canonical cyclotomic digit tile.
Angular/jet views are demanded projections, and arithmetic precision and
transport span are derived. Finite-interface TileScheduler admission is still
unproved, independently of the terminal prime-bit observer.

Final validation and measurement details are recorded in
[the evidence directory](../results/current/skew-state-removal-2026-09-10/README.md).
