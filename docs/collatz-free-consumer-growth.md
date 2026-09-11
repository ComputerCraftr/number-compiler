# Collatz free directional consumer and growth boundary

The radix-64 Collatz consumer has two different quotient boundaries.

After an occurrence binds multiplication carry `c` and residual shift `e`, its
directional value response has only `5, 10, 20, 25, 20, 10` classes for
`e=0..5`. These are useful dependent fibers. If every hypothetical `(c,e)` is
observed at once, the combined response distinguishes all 64 source digits.
That free table is therefore a consumer program, not a digit `ActionID`.

The common primitive is the ternary carry action

```text
C[b, x](c) = floor((3*x + c) / b), c in {0,1,2}.
```

At a shift seam the left action uses `b=2**(6-e)` and the right action uses
`b=2**e`. Thus `L[e]` and `R[6-e]` share one canonical width-indexed family.
The next radix-64 carry domain is their composition `R o L`; the domain
consumer does not need to reconstruct the joined digit.

`CollatzOutputMorphism.free_directional_actions` keeps the occurrence digit,
incoming carry, and root shift as typed free ports. It emits two IDs in the
shared eight-action ternary alphabet. Its construction does not call the bound
raw-digit, split-view, or point-domain methods. Each requested `(carry, shift)`
primitive row is built transiently from the generic carry owner; the module
does not retain the 1,152-row all-context leaf table. The exact digit remains
an occurrence payload and may be used by terminal output; it is not placed in
the consumer schema identity.

Growth has the same dependency order. `free_growth` consumes only carry and
root shift and emits `carry >> shift`. The complete table has the familiar
support: shift zero can emit one or two, shift one can emit one, and shifts two
through five emit no edge. No angular, harmonic, reset, or exact digit port is
part of this growth function.

The Hensel root boundary remains exact. For the normalized `h=2` chamber,
`constant mod 9` is one of `{1,2,4,5,7,8}` and a matching radix-four digit
advances it by multiplication by seven modulo nine. This is a derived observer
inside that chamber. Two roots whose constants agree modulo nine can demand
different next radix-four symbols, so this clock is not general root identity.

Exact accelerated occurrences now also use one affine section. A raw
`2^a*3^h*M+b`, with `a` one or two, is rebased to coefficient `2*3^h` by
reducing `b` modulo that coefficient and pushing the quotient and removed
factor into the counted radix-four suffix. The carry transducer operates on
runs, so a million equal quarters remain at most a few runs; it does not
construct the represented integer. Exact suffix extent and logical time remain
occurrence coordinates. This removes duplicate affine representations from
the occurrence interner, while preserving the suffix distinction that makes
129 and 385 diverge.

The seven workbook `domain_hensel_f2harm` collisions are regression witnesses
for the dependent consumer. For each source pair, the unresolved higher digit
differs by five and the three incoming-carry evaluations of `(L,R)` differ.
The test does not retain source, target, valuation-prefix, or finite `I3`
columns in semantic identity.

This closes the primitive free `(carry, shift)` selection and growth edge. It
does not establish a fixed point for arbitrary root-query continuations or
prove bounded A16/A32 temporal squaring. `BitFunctionArena.substitute` can
eliminate a supplied midpoint expression, but a recursive, branch-restricted
consumer residual still needs release evidence before it can replace the
existing exact root occurrence or powered Collatz action.

Rebasing one affine occurrence is not powered temporal closure. The current
transition cache can still discover a fresh successor chain one event at a
time. Publishing the completed spatial image and deriving a fresh bounded
Hensel occurrence from that image remains a separate scheduler theorem.

The public CLI uses the physical binary Collatz map rather than this
accelerated radix-64 event map. Its certified tile interface now applies the
same dependency order at the physical leaf: the six-state left port first
selects odd multiplication or even division, and the three-state right port is
consumed only by the division branch. The odd branch output is a function of
the left carry state alone. This factored function is what temporal tile
composition substitutes at later generations; no `6 x 3` leaf output table is
published. The physical path deliberately has no Hensel residual-shift port.

The measured primitive finite-function DAG has two outputs, external port
arity three, 76 factored nodes, and 1,963 Boolean nodes. The existing seed-27
streaming path was instrumented at 1, 2, 4, 8, 16, and 32 events. It creates
exactly that many stages and reaches the same number of simultaneously live
pending quotient values; feed calls are `1, 2, 4, 12, 28, 60`. Every target
and accumulated valuation agrees with the scalar oracle. The absence of
intermediate digit-word collections is a structural property of the pipeline,
while the stage, feed, finish, and pending counts are observed runtime values.
# Clock-normalized curvature and target seam

For one radix-64 source/root comparison, the demanded cylinder occupancy is
the seven-bit chain `O_0..O_6`, with `O_0=1` and each later bit saying that the
low `j` bits agree. Its differences `O_j-O_(j+1)` form one one-hot mismatch
packet, or the zero packet for a full match. The mismatch depth and branch
scale are derived from that packet. They are temporary consumer views rather
than additional temporal identity fields.

`NormalizedCylinderJet` represents `W+a=2^k*V` and delegates affine
composition to the shared `DyadicAffineCocycle` owner. Composition produces
the exact innovation `a1+2^k1*a2`; after the target is published, its normalized
Hasse jet is again the universal `(0,1)` schema.

The publication identity is `(exact accelerated tick, exact odd target)`.
The tick remains exact and only projects to `InverseThreeClock(q,tick)` when a
consumer requests precision `q`; retaining only a fixed-precision phase would
incorrectly alias temporal states that separate at higher precision. The odd
target is retained as the canonical spatial occurrence payload. Matched-run
counts, mismatch depth, curvature, angular data and transition offsets are
discarded only after that target has been constructed.

The research publication arena has an explicit 65,536-entry default budget.
That operational bound is outside semantic identity: an existing target still
hits when the arena is full, while a new target fails before publication.

The exhaustive endpoint audit gives 6,144 A1 classes from 8,192 odd 14-bit
sources and 24,576 A1 classes from 32,768 odd 16-bit sources. It also measures
A2, A4, A8 and A16 using exact endpoint frontiers and charges every cold
primitive successor and source-position visit. Exact endpoint identity makes
future deterministic images unambiguous, while the counters show that cold
first-use discovery still materializes intermediate endpoints. This is an
accelerated-event research seam; it is not the physical Collatz CLI clock and
does not certify sublinear first-use execution.
