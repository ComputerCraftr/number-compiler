# Carry ports derived from exact domain geometry

Every current carry boundary is already a function of the exact domain geometry
and the incoming port. The September 10 correction is implemented as a shared
prefix operation, removing expanded carry comparisons from the reverse/add
research action. The same operation supplies Collatz's two carry wires.

The subsequent [residue-consumer update](mirror-pair-residue-quotient.md)
uses these derived ports to remove duplicate value normalization on both
reverse/add branches and to emit growth domains without a 19-valued sum.
The measurements below describe the earlier geometry checkpoint.

## Geometry owns the answer

For LT=K0, EQ=I, GT=K1,

\[
C_i=(K_{\Gamma_{i-1}}\circ\cdots\circ K_{\Gamma_0})(C_0).
\]

The last non-EQ domain before i determines C_i; an all-EQ prefix preserves
the incoming bit. No carry history, birth-position array, or independent
`CarryQuery` input is required. Reflected queries change the index/alignment
on this same geometry; they do not require a second physical carry scan.

`ThresholdGeometry.prefix_action` descends the canonical geometry word and
reuses subtree monoid summaries. A counted run of any of the three actions is
idempotent, so even a run of length 10^100 needs one summary. After the needed
summaries exist, a prefix query follows one tree path. The first query may
visit all distinct nodes of the subtrees it summarizes; logarithmic lookup
assumes a balanced geometry and already-available summaries.

`carry_at(G,i,c)` applies that summary through the canonical carry monoid.
Summary caches and expression nodes are derived execution work, not extra
semantic inputs. Queries never export the geometry's coordinates or construct
a complete carry word. Costs still include summary creation, caches, and the
value expressions on which future domains depend.

Each live summary entry is charged to the same node budget as expressions and
schemas. Weak geometry references and owner finalization retire those entries;
a projection cache cannot grow as uncounted retained history.

For Collatz, the existing five radix-64 domain actions project onto two
Boolean wire geometries. Each wire uses the same prefix operation; the three
legal incoming ports are (0,0), (1,0), (1,1). Their sum gives the exact carry.
The carry-domain projection is not enough to determine the next value output;
exact value/threshold dependencies remain necessary.

## What was redundant in A16

The audited capacity-nine interface has 16 inputs: one width and five triples
of domain, F5 value, and parity. **None was an independent carry, reflected
carry, border, or harmonic input before this change.** The earlier 1,300
bindings counted operands of unary tables, not 1,300 missing carry variables.

There was nevertheless avoidable expression expansion. Each prefix carry was
encoded through separate EQ/GT tests and selection nodes. Native
`carry_compose` and `carry_apply` operations now derive it from the shared
geometry root. They use the existing monoid owner, reduce decisive resets and
identities, retain declared argument dependencies, and participate in exact
simultaneous temporal substitution. They do not defer an opaque primitive
successor or hide the expressions from resource accounting.

| Capacity-nine A16 measurement | Previous | Geometry-derived |
|---|---:|---:|
| Unary table occurrences | 1,844 | 1,556 |
| Unique table operand bindings | 1,300 | 1,156 |
| Reachable unary schemas | 41 | 40 |
| Retained expression and schema nodes | 9,049 | 8,953 |
| Independent carry/border/harmonic inputs | 0 | 0 |

There are 336 reachable derived carry operation nodes after the change; these
are counted in expression storage. Thus the reduction in table consumers is
larger than the reduction in total storage. It is not evidence of bounded
temporal complexity. The capacity-sixteen A32 probe still reaches the unchanged
30,000-node cap after A16. The exact value-to-next-threshold expressions remain
the principal unresolved growth.

The audit now reports declared source roles, derived carry operation counts,
summary-cache entries, and whether table bindings depend only on initial
geometry/width or also on initial value channels. Dependence on an intermediate
domain can include initial value dependencies; the latter counter does not
misclassify such a domain as an independent carry input.
At A16, seven table bindings depend only on initial geometry/width and 1,149
also depend on initial values. All remain derived expressions with explicit
arguments, rather than additional independently supplied state.

## Harmonic gaps are projection gaps

The words `(GT,LT,LT,LT)` and `(LT,LT,GT,LT)` have equal alternating F5
occupancy responses but different C1. The new regression answers C1 directly
from their geometry roots as 1 and 0, without introducing any variable.
That distinction was omitted by the harmonic observer, not absent from G.

The hierarchy is G → coupled carry/harmonic response → border projection.
Consumers of an aggregate harmonic can use that projection; pointwise consumers
query G. Carry summaries are derived from G, rather than included as separate
semantic factors in a Cartesian identity.

By contrast, `(4,4)` and `(8,8)` share LT geometry and the complete current
carry field, but their successors have LT and GT geometry. Resolving that
distinction needs the value channel. The remaining successor quotient concerns
`(G,V) → G'`, not discovery of today's carry positions.

## Scope and evidence

The implementation change is in the research expression/geometry cone, with
Collatz research adapters and formal laws. Existing production Collatz directed
transducers already derive carry projections from their tile roots; this audit
found no parallel production carry identity to remove. No production runtime
speedup or full successor closure is claimed.

Isabelle proves prefix composition, the all-EQ and last-decisive laws, and
Collatz's two-wire prefix projection. Tests cover exact indexed carries,
substitution, arbitrary incoming ports, huge counted runs with expansion
poisoned, and powered output against the independent oracle. Full measurements,
guard outcomes, fingerprints, and validation are in the
[evidence report](../results/current/geometry-derived-carry-2026-09-10/README.md).
