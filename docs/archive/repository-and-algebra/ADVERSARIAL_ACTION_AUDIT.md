# Adversarial action, materialization, and cache audit

**Historical pre-fix audit.** The representation changes and current invariant gates are described in [REPRESENTATION_BOUNDARY_RESULTS.md](REPRESENTATION_BOUNDARY_RESULTS.md). The findings below preserve the original evidence; they do not describe the current production path.

Audit date: 2026-09-02. Three agents independently inspected reporting/accounting, materialization, and cache identities. The coordinating agent reran the principal counterexamples in fresh processes. Production code was not changed during this audit.

**The earlier assurances were too broad. Public metrics omit real work and retention; exact intermediate states are still materialized; integer-ID ownership and operator classification have demonstrated wrong-result bugs. Passing the existing test suite does not establish the requested architecture.**

The reproducible observations are in `results/action_morphism_adversarial_audit.json`. Run the audit from the repository root with:

```sh
PYTHONPATH=src python3 bench/action_morphism_adversarial_audit.py
```

Each case runs in a fresh interpreter. `--case NAME` selects one case. This script records counterexamples; a successful script exit does not mean that the implementation satisfies the audited invariants. Reference digits and fully expanded oracle coefficients are created after the measured production request.

## P1: public metrics report false zeros and omit active owners

For `ReverseAddPoweredTerm(196, 64).digit(0)`:

| Public field | Reported | Active engine |
|---|---:|---:|
| `spacetime_primitive_field_steps` | 0 | 20 |
| `spacetime_carry_projection_entries` | 0 | 135 |
| `spacetime_forcing_occurrences` | 0 | 2 |
| `spacetime_forcing_jump_entries` | 0 | 1 |

`reverse_power.py:481–506` fills these fields with positional zeros. `bench/shared_powering_probe.py:64` consumes them as observations. The old `hashlife_cache_entries` property also reports zero while the bounded adapter reports 1,641 retained entries.

The public HashLife schema does not expose the global modular-effect memo. It contains 5,654 entries at N=64 and 60,094 at N=256. Shared-global retention must be explicitly distinguished from per-index ownership; it cannot disappear from reporting merely because the arena is global.

An additional inventory at N=256 found 2,876 omitted engine-owned event-stencil cache entries and 691 omitted macro-action interner entries. Public retained totals were 13,443 cache entries plus 19,384 tile nodes. The root walk missed 17,807 distinct output roots retained by the global modular-effect memo. These quantities have different ownership scopes and are not a proposed additive replacement total.

Relevant locations: `reverse_action.py:30`, `semantic_action.py:515`, `_bounded_temporal_application.py:108`, `hashlife_projection.py:164` and `:599`.

**Required correction:** inventory every retained container and tile root once, with explicit ownership and overlap rules. Use that inventory for both reporting and resource limits. Forward active engine values rather than leaving compatibility fields at zero.

## P1: physical fallback fields disappear from occurrence accounting

`PoweredCollatzTerm(54, 64).digit(0)` reports zero bounded exact occurrences and zero endpoint entries, but retains:

- 64 physical transition records containing 65 distinct exact fields;
- 127 exact-state binary-lift entries;
- a physical-cache DAG of 72 tile nodes, 61 absent from the reported root graph.

The public retained tile count for that request is 23. `_CollatzBoundedApplication.retained_spans` includes the initial field, requested target and forcing payloads, but omits the fields in `_physical_advances`. The occurrence metric counts only the forcing interner.

Reverse small-request accounting has the analogous omission: N=16 reports zero bounded jumps/occurrences while `_lift` has 26 entries and `_advances` has 15 exact transitions. This bootstrap-sized work is not itself an asymptotic defect, but it must be counted.

Relevant locations: `_bounded_temporal_application.py:97`, `:132`, `:211`, `:239`.

## P1: reverse offsets contain exact intermediate pair fields

For the public request `ReverseAddPoweredTerm(196, 64).digit(0)`, 37 retained macro-action offset records match **34 distinct unrequested exact pair generations, 29 through 62**. The requested pair endpoint is generation 63. Only two forcing occurrence records are reported.

This is not an inference from a large allocation count. The audit compared each retained offset with an independently computed exact pair recurrence after production finished. When `q` reaches the pair-plane bit width `w`, the source term vanishes modulo `2**w`, so the offset `E` is literally the entire intermediate pair field. `_linear_tile` computes its coefficient leaves, and the action interner and global zip memo retain them.

Locations: `reverse_action.py:44`, `:117`, `:125`, `:143`; `reverse_spacetime.py:505–517`.

The carry quotient remains extensional for its incoming carry ports. That does not make a complete emitted carry track bounded in size, nor make its aliases closed under future time evolution. Reclassifying exact fields as action offsets does not satisfy the requested summaries-only constraint.

## P1: Collatz ports reconstruct full intermediate scalars and offsets

Let `y=(4**128-1)//3` and `seed=(2*y-1)//3`. During a two-event accelerated request, production residue reads at 256 and 320 bits equal the **entire 255-bit intermediate `y`**. The input has 254 bits. Increasing the construction parameter increases the required precision without a fixed bound.

For `q=129`, `y=(7*4**q-1)//3`, and `seed=(2*y-1)//3`, a five-event request caches exact **260-bit and 262-bit B offsets** for earlier three- and four-event prefixes, before endpoint projection begins.

Composition itself retains a symbolic DAG. Its evaluator computes `precision=bits+k`, packs source digits into scalar residues, evaluates numeric offset residues, and stores those residues. They can equal the full source, intermediate tail or B value. Fixed output-port width alone does not bound this work because `k` grows, and the valuation probe can enlarge the output port too.

Locations: `collatz_symbolic_action.py:155–160`, `:163–210`; `collatz_spacetime.py:699–716`.

Additionally, `collatz_symbolic_action.py:212–223` explicitly builds every radix-4 digit of each projected endpoint. Explicitly requested endpoint lowering is distinct from the hidden intermediate findings above, but a single public point query currently triggers whole-endpoint construction. The implementation cannot promise that quadtree leaves never contain eagerly computed digits.

## P1: public Collatz requests still use exact-field temporal lifting

The even-source branch and the remainder branch call the exact physical lift:

| Public request | Exact physical transitions | Lift entries |
|---|---:|---:|
| `PoweredCollatzTerm(54,64).digit(0)` | 64 | 127 |
| `PoweredCollatzTerm((4**128-1)//3,128).digit(0)` | 128 | 255 |

The latter input is odd. Its remainder before the next accelerated event is arbitrarily long as the parameter grows. “Bounded remainder” therefore does not mean a constant-size fallback. The lift keys contain exact physical field identities and retain concrete successor fields.

Locations: `collatz_spacetime.py:479–485`, `:512–521`, `:625–626`, `:656–657`.

## P1: reverse arena-local IDs can select the wrong source and endpoint

Two engines intern different first occurrences, `(2,)` and `(8,)`. Both receive occurrence ID `0`. The first arena reads the second arena's occurrence as `(2,)`. After warming the first engine, advancing the foreign occurrence returns **`(4,)` instead of `(16,)`**.

`ReverseAddForcingMorphismArena.pair_span` indexes `_payloads` by the integer ID without checking occurrence ownership. `advance_forcing_power` looks in its endpoint memo before any ownership validation. A same-base check does not establish arena ownership.

Locations: `forcing_morphism.py:177–180`, `reverse_spacetime.py:492–500`.

**Required correction:** validate membership before payload access and before endpoint cache lookup, or use scoped handles whose identities cannot collide across arenas. Collatz's tail accessor already performs an ownership check, and its accelerated API interns input fields into its own arena.

## P1: a normalization suffix is not proof of reverse/add identity

A valid identity `FiniteBlockEffect` followed by `DigitNormalizeBlockEffect` should emit `2` on source `(2,)`. The bounded adapter emits **`4`**. Evaluating the same operator through the generic implementation emits `2`.

Both `build_bounded_application` and `temporal_key` assume that any composite ending in digit normalization is a reverse/add power. Thus this identity composition also receives the same temporal key as genuine reverse/add followed by normalization, despite distinct operator keys.

Resolved: certified routing validates through the family executor, generic temporal identity uses the admitted compiler action, and the duplicate `_hashlife_cache_identity.py` helper has been deleted.

**Required correction:** require a verified arithmetic-family identity for the entire input operator before selecting the family-specific engine or reducing its cache key to base and exponent. The generic supported block API must remain exact.

## P1: budget checks occur after the work and retention

A public `HashLifeBlockIndex` for reverse196/N64 with `max_cache_entries=0` performs all 63 transitions, retains 1,641 reported adapter entries and stores the target, then raises `BlockContextBudgetExceeded`. Its engine has `max_context_nodes=None`.

Both adapters construct engines without propagating the index limits. The index checks its limits after `.point()` completes. This is a late rejection, not an allocation bound. Omitted caches further weaken the check.

Locations: `_bounded_temporal_application.py:69`, `:173`; `hashlife_projection.py:480–482`. `budgeted_cache_entries` also reads only old effect statistics at `:819`, while the guard measures additional adapter entries.

## P2: missing work fields, inconsistent definitions and non-independent checks

- Collatz27/N64 emits 218 symbolic port queries and maximum port precision 107 in the engine, but neither reaches the public bounded/HashLife report. This hides the very work that reconstructs large scalars.
- `action_compositions` means retained composition entries for reverse, but composition requests for Collatz. In that Collatz example, 158 requests produced 68 entries. Requests, hits, evaluated compositions and retained entries need separate fields.
- A first term's query allocation counter changes from 292 to 4,776 solely because an unrelated term is queried. `hashlife_projection.py:595` subtracts old global arena snapshots rather than accumulating only that index's operations. Its owned retained-node count stays 65.
- `spatial_occurrence_accounting_delta` is forced to zero when the adapter exists (`_hashlife_behavior_reporting.py:246`). It is not an independent reconciliation.
- `bounded_temporal_runtime_cutover_complete` only tests absence of the old generic residual nodes (`:228`); it does not establish complete action-only production powering.
- `eager_spatial_observer_fields` tests one literal slot name (`:163`), not eager materialization through offset trees, scalar arithmetic or fallback paths.
- `retained_cache_accounting_delta` and behavior-level memo totals audit old effect statistics, excluding significant new engine caches.

Existing growth/behavior assertions consume these fields as success conditions. They need independent inventories and adversarial negative controls, not assertions that a hard-coded zero remains zero.

## Additional cache-identity scope

The accelerated action-composition tables do use integer IDs, and tuple keys containing integer IDs are not inherently a defect. Exact occurrence keys are appropriate for separately scoped source-to-requested-endpoint memos. Spatial interners and projection tables still use several object or structured keys; a blanket “all caches use integer IDs” statement is false.

The cache agent also reproduced a generic finite-kernel identity weakness: `FiniteBlockEffect.canonical_key` (`_block_base.py:314–325`) includes a caller-provided name and dimensions but omits initial states and transition/output tables. `_finite_arena` (`hashlife_projection.py:259–266`) trusts that key. Same-name/same-shape custom kernels can share an arena despite different behavior. The built-in digest-checked singleton was not observed to collide. This is a generic-extension contract defect, distinct from the two independently reproduced wrong-result cases above.

## Validation and limits

The coordinating agent reran the public metric mismatch, hidden reverse offsets, physical fallback, full intermediate scalar, foreign-ID alias, incorrect operator dispatch, late budget rejection and interleaved metric contamination. The durable audit adds a probe for pre-endpoint full-B lowering.

Ruff passed for the audit script. The existing repository-policy, HashLife behavior, reverse-action and Collatz symbolic-action tests still pass: **47 passed**. That result demonstrates the coverage gap; it does not contradict the counterexamples. The previously reported full-suite result was 864 passes before this audit. No production fixes were made as part of this audit.

Correctness fixes should precede performance claims. Reporting then needs a shared ownership inventory and explicit work counters. Finally, removing exact intermediate offsets/scalars and physical fallback requires substantive execution changes, not metric renaming or suppressing the observed work.
