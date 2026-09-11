# Quotient-first canonicalization results

This pass moves semantic cache hits to canonical representations *before* powered
context determinization/output-table construction.

## Production changes

1. **Primitive semantic witness quotient before determinization**
   - Composition first constructs the exact bipartite primitive witness system.
   - A strong transition/output congruence jointly refines left/right primitive
     witnesses.
   - Only the resulting canonical witness classes are determinized.
   - For exact decimal `T^2` this changes the construction path from
     `2609/378 primitive witnesses -> 690/91 raw DFA -> 688/91 late quotient`
     to
     `2609/378 -> 1857/150 semantic witness classes -> 688/91 DFA`.
   - The downstream exact minimizer then reports **0 left / 0 right late merges**.

2. **Canonical output MTDD from labeled Cartesian generators**
   - Composition no longer probes every `(left,symbol,right)` output context.
   - Compatible primitive semantic classes emit labeled Cartesian selector boxes.
   - Equal-output boxes merge to a fixed point before the MTDD exists.
   - The canonical MTDD is installed on `LazyBimachine` as the authoritative
     output function; the tuple output cache remains empty.

3. **Deterministic residual quotient before MTDD construction**
   - Exact left/right residual observations are built as
     `output-word-id -> opposite-state-selector-mask` functions directly from
     semantic class membership.
   - Deterministic Myhill--Nerode refinement happens before output decision-DAG
     construction.
   - `ResidualPowerTable` therefore no longer calls the downstream residual
     minimizer after each square.  That minimizer remains an exact test oracle.

4. **Release regression guard**
   - `JumpAudit` now records canonical generator boxes/regions and late semantic
     merges.
   - Full-J certification fails immediately if any powered probe reports a
     semantic state merge discovered after canonical construction.
   - An adversarial test verifies this fail-closed behavior.

## Exact T2 metrics

| Metric | Previous semantic release | Quotient-first release |
|---|---:|---:|
| final left/right states | 688 / 91 | 688 / 91 |
| possible output contexts | 1,381,380 (old prequotient domains) | 1,377,376 |
| exact output probes | 1,381,380 | **87,235** |
| output probe reduction | — | **15.79x** |
| semantic generator boxes | — | **40,111** |
| normalized canonical regions | — | **3,485** |
| authoritative output MTDD internal nodes | 2,310 | **310** |
| per-context tuple cache entries | not authoritative | **0** |
| late left/right state merges | 2 / 0 in old construction path | **0 / 0** |
| power-table construction through T2 | ~5.67 s old compose+minimize baseline | **~1.82 s median** |
| measured hot-path speedup | — | **~3.11x** |

The final transduction remains exact; randomized two-step pair-half checks match
applying the one-step operator twice.

## Remaining blocker

This closes the *late semantic cache* regression.  It does **not** close full J.
When exact `T^2` is squared toward `T^4`, the current composer still constructs
raw primitive witness triples before the new semantic quotient can act.  A
100,000 primitive-state cap is exceeded in about 0.6 s in the current probe.

The next exact target is therefore narrower:

> represent and quotient the primitive bipartite witness relation itself as a
> canonical decision/cascade object, so `T^4` never enumerates the >100k raw
> primitive triples whose equivalence we now know how to quotient afterward.

The full-J release gate remains intentionally red until that powered primitive
relation also stays within the bit-length complexity budgets.
