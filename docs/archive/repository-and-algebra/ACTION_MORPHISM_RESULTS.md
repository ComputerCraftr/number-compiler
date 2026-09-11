# Historical action-morphism implementation (superseded)

The current implementation and its verification scope are documented in [EARLY_CANONICAL_LOOKUP.md](EARLY_CANONICAL_LOOKUP.md). Public projection now uses source-backed lazy programs, scoped handles, and a per-index resource ledger. Exact slab/tape oracles require an explicit proof context. The sections below describe the earlier implementation and must not be read as claims about the current production path.

Current measured results are in results/lazy_resource_audit_v5.json (local artifact: `../../../results/lazy_resource_audit_v5.json`): each row uses a fresh process, compares its requested digit with an independent scalar oracle, reports actual retained containers, and separates bounded arithmetic work from retained program size. These measurements do not establish logarithmic cold execution; reverse/add still discovers nonlinear branches linearly in the sampled generations.

The original counterexamples remain in [ADVERSARIAL_ACTION_AUDIT.md](ADVERSARIAL_ACTION_AUDIT.md) and `results/action_morphism_adversarial_audit.json`. The current counterpart, `bench/action_morphism_adversarial_audit.py`, runs the corresponding regression assertions and rejects failures, missing tests, or skips. The expanded result is saved as `results/followup_representation_audit_v5.json`; its coverage and provenance are described in [EARLY_CANONICAL_LOOKUP.md](EARLY_CANONICAL_LOOKUP.md). The prior v2, v3, and v4 validation remains historical evidence.

The historical counters below omitted some retained work and state, and historical passing checks did not establish the requested representation guarantees.

## Reverse/add

`CarryActionQuotientArena` is now connected to production. An exact spatial tile maps to the complete emitted carry output for each of the two possible incoming carries. Output trees are hash-consed, and spatial concatenation composes integer action IDs. Different coefficient tiles with the same carry function therefore share the nonlinear action, including aliases caused by redundant resets.

That nonlinear image is combined with the exact affine offset. `ReverseAddMacroActionArena` represents the complete conditional map

```
S -> 2^q (1+z)^r S + E  (mod 2^w),  w = bit_length(2b-2).
```

The map includes its exact dyadic offset `E`; it is more than a boundary observer or a growth-bit class. Composition uses integer action IDs, canonical modular coefficient summaries, and balanced binary assembly. The source exponent saturates at `w`, where its contribution vanishes. For a certified physical itinerary, valid pair coefficients are smaller than `2^w`, so the modular endpoint is exact.

Future carry decisions are projected directly from the composed affine effect. The projection fuses modular addition with threshold evaluation and emits carry summaries, without constructing intermediate pair fields or applying the primitive pair-field operator. The combined action is applied once to construct the requested endpoint. The H-row bootstrap, carry-cut packing, validation, and reconstruction use structural dyadic operations rather than full digit or carry vectors. A request for an exact future slab advances actions to the start of its final H-row window, then constructs at most H carry rows; exact slabs are no longer binary-lift states. Requested forcing and slab endpoint memos honor `max_jump_entries`, including zero retention, and use least-recently-used eviction. Exact slab endpoint identity includes the old carry rows that survive the requested advance; equal reconstructed pairs never alias different surviving certificate rows. Erased history rows do not over-key the endpoint cache. The context budget includes owned action, composition, carry-port, and endpoint entries; shared global modular-effect memo entries are reported separately.

The branch itinerary still has to be discovered. Prefix action effects are retained during that discovery. Once the source term vanishes, an output-complete constant action can contain the same information as an exact endpoint field; calling it an action does not make that information bounded. The metrics below charge the retained trees and modular-effect memo accordingly.

### Cold reverse/add measurements

These measurements use seed 196 in base 10, a fresh interpreter for each requested generation, and `term_field(196, N)`. Generation N requires N-1 pair transitions before terminal normalization. The baseline handles requests shorter than the fixed H=20 bootstrap.

| N | Total primitive transitions | Post-bootstrap branches | Macro actions | Macro compositions | Endpoint applications | Exact occurrences | Endpoint memo entries | Global retained tiles | Modular-effect memo entries |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 295 | 0 |
| 32 | 31 | 11 | 26 | 18 | 1 | 2 | 1 | 1,802 | 1,674 |
| 64 | 63 | 43 | 119 | 82 | 1 | 2 | 1 | 4,443 | 5,654 |
| 128 | 127 | 107 | 309 | 210 | 1 | 2 | 1 | 13,315 | 17,627 |
| 256 | 255 | 235 | 691 | 466 | 1 | 2 | 1 | 49,312 | 60,094 |

Primitive pair-application memo entries remain at 185 after the bootstrap for N>=32. Carry-port action counts are 41, 147, 483, and 1,630 respectively. Machine-readable measurements are in `results/reverse_action_power_metrics.json`.

The requested elimination of the cold 15/31/63/127/255 work sequence is therefore **not achieved**. A successor-complete macrocell closure that avoids discovering each unseen branch remains necessary.

## Why carry-reset aliases cannot authorize temporal state aliases

The one-cell pair fields `(2,)` and `(4,)` in base 10 have the same constant-zero carry output and the same first affine action, `S -> 2S`. They nevertheless have different future branch itineraries:

```
(2,) -> (4,) -> (8,) -> (16,)
(4,) -> (8,) -> (16,) -> (7,7)
```

An action may be applied to both sources, but their future actions cannot be obtained by treating the sources as the same temporal state. The implementation retains this distinction and tests it explicitly. No sampled alias is promoted to a proof of successor closure.

The existing universal `power_block_effect` path does construct the complete nonlinear operator by binary composition. It does not resolve this gap: higher compositions fall back to exact residual forests keyed by previous residual and spatial tile, and evaluating a residual constructs first-child output tiles. Reusing that path would move the work into intermediate exact effects. The missing invariant is an output-complete equivalence over all admissible opposite ports and continuations that remains closed under both spatial and temporal composition, with a reduced representation that avoids those intermediate fields. The current implementation does not establish that invariant or a bound on its size; this is not an impossibility claim.

## Collatz

`CollatzSymbolicActionArena` stores canonical integer action IDs for affine maps with exponents `h` and `k`. Its offset is an implicit symbolic DAG. For an action followed by a second action, composition uses

```
B12 = 3^h2 B1 + 2^k1 B2.
```

The arena does not construct the full integers `3^h`, `2^k`, or `B` during composition. Requested modular ports are evaluated from the original normalized source tail. Branch discovery does not run the old primitive `3*x+1` target-field path, and the endpoint is constructed once. Normalized tails remain exact endpoint payloads; the finite 3-adic residue is not asserted to be an exact closed state quotient.

For seed 27 and 16/32/64/128/256 accelerated events, the measured endpoints are 593/3077/1/1/1, and cumulative binary shifts are 21/44/116/244/500. Nonlinear branch evaluations are 16/32/41/41/41, with zero primitive forcing-field transitions, two exact occurrences, and one endpoint memo entry per fresh request. Action counts are 29/72/106/111/114. Growth beyond 41 events uses a certified fixed-point shortcut; these figures do not establish sublinear branch discovery for a nonterminating or previously unseen itinerary.

## Verification scope

Reverse regression tests cover complete carry-output aliases, affine composition associativity, unequal futures under equal first actions, explicit branch accounting, endpoint-only occurrence retention, and cold powering with primitive pair application forbidden. Exhaustive small symmetric pair fields in bases 2, 3, 4, and 5 are checked against the independent pair recurrence. A separate guard forbids vector iteration during slab bootstrap and production forcing. Slab endpoint tests check the constant H-row reconstruction bound, and endpoint cache tests verify zero and one-entry capacities.

Collatz checks include exact endpoints and cocycles for randomized 4–160-bit sources, a cold 16-event run with scalar and primitive multiplication paths forbidden, and a billion-event fixed-point request without coefficient materialization.

Final stable-tree verification: `ruff check` passed; `mypy --strict src` passed for all 144 source files; `pytest -q` passed all 864 tests in 151.89 seconds. Passing those checks validates the implemented exactness and structural changes; it does not prove the missing logarithmic cold closure.

The structural policy has also been corrected: source files have one global cap of 1000 physical lines, with no smaller module-specific caps. Documentation and generated data have no line-count limit. The prohibition on direct and mutual Python recursion remains enforced.
