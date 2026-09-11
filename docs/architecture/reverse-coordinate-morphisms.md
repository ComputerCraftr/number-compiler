# Executable local reverse/add morphisms

The September 10 output-morphism implementation supplies executable arithmetic
arrows for a bounded, declared coordinate-port profile. It does not establish
an active future-behavior quotient for 196. The public causal executor now
connects a decimal primitive producer's output to a decimal primitive
consumer's carry response through the bounded morphism described below.

The [contextual residual extension](reverse-contextual-residuals.md) now derives
carries from domain geometry and minimizes declared successor observations
together with their updated context. Its finite continuation certificate does
not discharge the whole-profile scheduler obligations listed below.

## Ownership and equality

`ReverseActiveOutputArena` in `sequences/reverse_add/active_output.py` owns
`CoordinateOutputMorphismID` values backed by reduced finite output functions.
The output at one coordinate is a function into pair symbols `0..18`; its
alpha, beta and nu projections are executable functions, as is its next
three-element carry action. A declared input port can name a relative
coordinate or a bounded carry cut. Translating the coordinate does not require
retaining an absolute origin in an output ID.

An ID contains no source tile, output row, temporal instruction count, sector
tuple, or separate transport/birth history. Function signatures and validity
predicates are part of identity. Equal functions on the **same declared port
profile** receive the same ID. This does not yet implement quotienting across
different profiles, coordinate reflection, unused-port removal, or geometric
admissibility conditions. The arena does not inspect port names to certify their
intended geometric meaning.

The existing `ReverseCoordinateProgramArena` still owns source-independent
temporal descriptions. Existing `FieldCellActionID`, `ReverseFrobeniusPlan`,
and quiescent `FutureBehaviorClassID` contracts are unchanged. An executable
local output function is not an admission certificate for a temporal program.

## Implemented arrows

* `pair` composes exact normalization with pair addition using bounded bit
  functions; it never constructs an exact output tile.
* `coordinates` and `from_coordinates` implement the exact F5 × F2 × F2
  correspondence. The forbidden triple `(4,1,1)` remains undefined, never
  silently interpreted as pair symbol 19 (the decimal blank).
* `carry_action`, `carry_then`, and `carry_apply` derive next thresholds and
  compose forward spatial carry responses. Reflection is applied to the
  normalized digit observations, not implemented as another causal scan.
* `substitute` composes symbolic output functions through existing reduced
  finite-function substitution. Intermediate functions are retained and
  accounted; there is no claim that their size stays bounded under arbitrary
  temporal squaring.
* `transported_alpha` applies centered F5 shifts to caller-supplied input
  functions, adds the birth function, and reduces the combined result.
  `from_coordinates` then interns the complete output function. The caller
  still has to supply the exact beta/nu functions and valid carry geometry.

The shared `BitFunctionArena.map_atoms` implementation composes a unary finite
law with a bit-factored function. It enumerates at most 64 primitive atoms,
never the Cartesian product of input ports. Existing invalid input predicates
survive even constant maps. Its decision nodes, workspace, and resulting
functions use the existing resource ledger.

## Connected primitive carry consumer

`finite_pair_transfer` routes decimal `BaseBlockEffect` producer/consumer
edges through `ReverseMorphismTransferArena`. Other effects and composed
consumers keep their existing execution paths. Public powered reverse/add
queries encounter these primitive edges inside the causal recurrence.

The original source carry domains determine the producer's spatial midpoint
ports. Known producer ports specialize `ReversePrimitiveOutputMorphism`
before decision-function construction, using the admitted primitive kernel
as the canonical scalar evaluator. Its result is a bounded local output
literal. The fully parametric local law is independently checked at all
20 × 43 × 5 symbol/port assignments, including blank and growth edges.

Local outputs map into `ReverseBoundOutput`: a function of **every** next
primitive consumer carry state. Spatial composition is memoized by these
carry functions, so equal next carry behavior shares composition even when
source tiles differ. The executor observes the requested consumer state from
that function. It builds neither the producer's exact successor tiles nor
the older 13-channel fused interface on this path. A single covered interval
also needs no producer exit scans merely to establish its exterior ports.

Source-to-function bindings remain query scoped and are cleared before their
tile leases retire. The retained composition memo contains bounded carry
functions, with no source tile references. Independent payload auditing checks
source controls, bound leaf outputs, child port routing and carry composition;
an issued but incorrect replacement function is rejected. These memos and
the iterative traversal workspace are charged to the existing resource ledger.

The connected projection intentionally forgets output information that its
primitive carry consumer cannot observe. It is not a whole-output or future
class: a composed consumer cannot use this projection as its complete input.
The F5 temporal transport below remains local algebra; this connection does
not establish arbitrary temporal squaring or whole-profile successor closure.

## Centered F5 transport

`CenteredF5Transport(q,r)` represents `2^q (U^-1 + U)^r`, where
`U f(x) = f(x+1)` and `x = 2i - (d-1)`. The caller supplies observed branch
counts; the operator does not predict growth. The no-growth count is reduced
modulo four, while the growth degree is exact.

For `r = sum(r_j 5^j)`, the factorization is

```
U^-r product_j (1 + U^(2*5^j))^r_j.
```

`coefficient(offset)` uses the base-five digits in O(log r) arithmetic steps.
`shifts(max_terms=...)` expands only nonzero coefficients and rejects an
oversized expansion before calling any source function. For example,
`r=5^40` has two shifts, whereas `r=5^40-1` fails the default 4,096-term budget.
The latter is a real limitation, not a performance claim hidden by caching.
The shift tuple is a homogeneous operator, not an output field. No F5 source
annihilation is inferred from the separate mod-32 sector certificate.

## Checked scope and remaining release obligations

The tests exhaust all 1,444 local symbol/carry combinations, check exact output
and threshold projections, and compare the combined F5 function with its
transport-plus-birth construction. They verify both supplied cancellation
witnesses **coordinate by coordinate** with tile construction poisoned. The
test-only witness oracle supplies original carry boundaries; it is not a new
production row scanner or a whole-row behavior ID.

All 361 symmetric width-three inputs also pass with symbolic forward prefix
actions and growth selection, including the next output carry action. Local
symbolic substitution agrees with direct composition. Homogeneous temporal
composition agrees with independent Laurent convolution. These checks are
distinct from executing arbitrary reverse/add temporal squares.

Still required before active whole-profile scheduler admission:

1. An authenticated profile for extent, frame, boundaries and observed
   coordinates, closed under the actual composed consumer.
2. A bounded successor rule deriving the entire required carry-domain geometry
   from that profile without retaining an exact future row under another ID.
3. Cold whole-profile cancellation and the negative sector witness at active
   future-class level, plus successor commutation across recursive blocks.
4. Actual reverse/add temporal squaring without exact midpoint construction,
   non-injectivity measurements over input bindings, and the public 196
   N=16 through 1024 scaling gate.

The connected carry projection does not manufacture an active
`FutureBehaviorClassID` from a finite output observation. Its elimination of
primitive-edge work does not establish a better asymptotic point-query scaling
curve; see the current morphism-connection checkpoint for measured work.
