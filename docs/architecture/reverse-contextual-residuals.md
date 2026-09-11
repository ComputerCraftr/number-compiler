# Contextual reverse/add residuals

`ReverseContextualResidualArena` constructs consumer-relative residual functions
from the exact local reverse/add morphism. Carries are derived by composing
the existing domain actions with incoming carry zero. No independent carry
birth positions or carry history become state.

The three output stencils are no-growth same-coordinate response, the growth
edge with its structural digit one, and the staggered growth interior. They
reuse `ReverseActiveOutputArena`; this module introduces no second arithmetic
kernel. Each output can feed its next three-element `CarryFn` observation.

## What is minimized

A profile bundles the carry observation with the declared updated context,
including any needed neighbor, growth, extent or alignment observations. Its
admissibility predicate is part of its canonical finite-function identity.
The ordered field sorts are retained in the record's output sort, so an equal
bit encoding under another context layout cannot alias. Relative stencil roles
distinguish coordinate frames. Callers must supply the
complete context that their consumer needs; the arena does not authenticate
a whole-field geometry merely from a frame name.

For a profile F with primitive pair source S and remaining context c, the
residual of s is the canonical function `c -> F(s,c)`, including definedness.
Two source values merge exactly when these functions are equal. The compiler
constructs 19 primitive cofactors. It never enumerates the Cartesian product
of context valuations. This bound does not imply a bound on the decision DAG
for an arbitrarily complicated context; existing ledger budgets still apply.

`certify(F,G,S)` publishes a successor map only when equal F residuals imply
equal G residuals. G includes both next observation and updated context.
Profiles must have identical pulled-back input signatures and admissibility
domains. A conflicting source pair raises `ResidualSuccessorConflict` before
any successor mapping is published. An altered admissibility domain also
fails closed.

`refine` computes the joint cofactor partition needed by F and G, with maps
to both. Refinement happens before source binding; it cannot recover a
distinction from an already coarsened residual. It can legitimately produce
all 19 classes when the requested context observes the exact pair value.

`pullback` substitutes the next output and context simultaneously through
the existing canonical finite-function substitution. `compile_chain` closes
one to 64 explicitly supplied profiles by backward refinement. All must
already be pulled back to the same relative source/context ports and admitted
domain. This is a finite continuation contract, not discovery of an unbounded
growth-adjacency grammar or an infinite-future minimization theorem.

## Execution and ownership

After compilation and initial binding, `advance` accepts only profile handles,
the typed source port and the current residual function ID. It uses the
certified map without evaluating source arithmetic, scanning carries or
constructing output tiles. Missing or evicted mappings fail closed.

Maps are ledger-owned, evictable query memos. They retain canonical function
handles and typed finite ports, without source tiles or exact output fields.
Each batch is reserved before publication. The registered-payload audit
independently checks every map against the existing primitive constants and
the canonical read-only substitution checker. It checks complete coverage
of all 19 source atoms and rejects an issued but incorrect replacement ID.

## Evidence and limits

The unit tests compare the three stencils with the independent pair-step
oracle for all 361 symmetric width-four fields. They retain the no-growth
seven-band merge, reject the growth-interior 7/8 merge, and refine only the
distinctions required by that declared context. A context-only negative test
rejects merging even when the carry observation stays constant.

A complete two-event growth/alignment example merges five admitted one-cell
values into three residual classes. Both transitions execute with source
evaluation, cofactor construction and tile construction poisoned. Other tests
cover simultaneous pullback, invalid domains, budgets, foreign ownership and
corrupted retained mappings.

The supplied exhaustive width-eight counts remain research evidence; this
change does not reproduce that experiment. It supplies the contextual
factor-through mechanism, but does not yet generate and authenticate a
successor-closed context transition graph for the active 196 computation.
There is no new public powered-executor admission or scaling claim. Whole-field
closure, recursive temporal composition and the existing 196 scaling gates
remain required before calling the 196 carry-domain quotient complete.

## Formal validation and continuation counterexamples

The [Isabelle checkpoint](../../results/current/reverse-isabelle-2026-09-10/README.md)
now proves the carry law, the seven-band no-growth factorization, exact
pair-field invariant closure containing the 196 seed, and the generic
factor-through/iteration theorems without oracle dependencies. The generic
congruence premise remains unproved for a full active 196 quotient.

It also proves that the earlier five-source example requires all five
distinctions by the third event. The compiler regression rejects extending
the two-event merge and recompiles the longer continuation with five classes.
Thus the earlier three-class result is strictly a finite-consumer result.

For the two-cell family `[s,s]`, Isabelle proves that observing current and
next four domain/growth/width profiles separates all 19 values. The exhaustive
Python diagnostic similarly separates all 209,960 valid symmetric fields
through width eight within at most six successors. This does not establish
an impossibility theorem for all consumer-relative or 196-specific grammars,
but these merges cannot be promoted to an all-future domain-state quotient.

## Counted-run control and fixed-point refinement

The [positive-control checkpoint](../../results/current/reverse-run-controls-2026-09-10/README.md)
adds an exact counted-run successor that uses the existing decimal normalizer
and carry actions. It never expands a run or stores a carry track. This remains
an explicit reference endpoint representation, guarded by `exact_oracle()`;
it is not admitted as a production future ID. Seeds 1, 1111 and 196 each agree
with `pair_step` for 100 successors. Ordinary runs still fragment.

`Reverse_Uniform_Runs.thy` proves, for every positive length L,
`2^L -> 4^L -> 8^L -> 16^L -> 7 14^(L-1) 7`, where powers denote counted
pair coefficients. The domains are LT, LT, LT, GT. In particular decimal
digit 8 has pair coefficient 16, so it is GT. The theorem includes the
length-one case and requires no enumerated width bound.

The shared `minimize_finite_observer` now refines a caller-supplied finite
graph to a true fixed point. Ordered edge slots can include both next context
and next residual; forbidden ports participate in the initial partition.
The unary Moore minimizer delegates to the same owner. Tests preserve a valid
recurrent merge while splitting a delayed distinction, and independently
compare every small tested graph with continuation traces.

This helper rejects successor indices outside the supplied universe. It does
not certify that a caller supplied every arithmetic state or labeled forbidden
ports correctly. `compile_chain` retains its finite-continuation contract; it
does not silently gain an unbounded certificate from this helper.
`Reverse_Contextual_Fixed_Point.thy` proves that equality of stable signatures
preserves all finite admitted continuation observations, including next-context
and next-residual classes. The complete 196 graph and its stability premise
remain to be constructed and discharged.

An independent live tile-executor probe constructs uniform input by self-joins
in logarithmic space and requests four powered transitions. Width 8 passes;
width 1,048,576 exceeds the unchanged 35-second guard. Thus the successful
counted-run control does not establish powered-executor scaling. This exposes
a production execution obligation even before the fragmented 196 case.
