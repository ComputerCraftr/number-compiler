# Balanced dyadic return: executable refinement map

This map identifies the production objects modeled by the shared dyadic source,
skew, worklist and prefix-safety theories. Build evidence and its source
fingerprint belong in the weekly record. A checked executable Isabelle model
and a reviewed Python mapping are distinct from verification of Python itself.

## Production contract

- A `DyadicReturnLaw` pins the family, version, two integer branch maps
  `(gain * state + offset) // 2`, weights, and an optional checked exact cycle.
  The physical Collatz law is gains `(1, 6)`, offsets `(0, 2)`, weights `(0, 1)`.
  The Antihydra return law is gains `(3, 3)`, offsets `(0, -1)`, weights
  `(2, -1)`. A change of law invalidates an image; a matching low residue does
  not authorize a different source occurrence.
- `_balanced_residue_build(width, residue, retain)` requires an exact integer
  `0 <= residue < 2**width` and a positive width. It splits a span greater than
  64 at the largest power of two *strictly below* that span. The right child's
  low residue is `transport_low(left.transfer, parent_residue, right_span)`.
  This rule also covers unequal and non-power-of-two spans.
- A bounded leaf records chronological branch bits and the complete transfer
  `(upper, offset, lower)`, odd-bit count, weighted sum `delta`, and minimum
  prefix including the initial zero. A parent composes transfer left then
  right, adds counts and deltas, and sets its minimum to
  `min(left.minimum, left.delta + right.minimum)`. Production uses
  `consumer_pullback.compose_prefix_safety_values` for both object-level
  safety actions and the dyadic support/image joins.
- `retain=False` publishes no chronological support: the returned root is a
  saturated effect. `retain=True` publishes bounded leaf words and composed
  support nodes. The local `(span, residue)` memo reuses a semantic effect and,
  in retained mode, its support ID within **one** pinned-law construction. It
  has at most 64 entries, shares the ledger's transient stack owner, and is
  cleared on every return or exception. A memo hit does not merge source-image
  identities.
- Bounded leaves now share a finite arithmetic memo: cold atoms classify at
  most four branches, and chronological composition constructs effects of at
  most eight source bits. Keys include owner, the complete pinned law, width
  and residue. The existing ledger-owned macro store admits at most 256
  entries and clears at the end of each composite transaction (or failure).
  It is distinct from the outer 64-entry memo. Optional retention refusal
  preserves exact computation under stricter request limits.
- `complete_composite_candidate` checks the action, payload, identity-bound
  source, and exact source precision. It may consume a bounded exact prefix
  while seeking the law's pinned cycle; otherwise it applies the balanced
  constructor directly. Its published image binds the action and source to
  the summary and support. The Collatz adapter also has an admitted exact-cycle
  shortcut before this function. Antihydra has no cycle shortcut.

## Theorem-to-runtime map

| Runtime field or operation | Executable model / theorem | Scope of the Python mapping |
|---|---|---|
| Bounded leaf and high-fiber effect | `Dyadic_Balanced_Arithmetic.arithmetic_leaf_loop_correct`, `arithmetic_leaf_correct`, `construct_source_effect_endpoint` | Actual branch gains, offsets, physical odd-bit counts, signed delta and minimum match the Python fields. The mathematical leaf accumulator executes branches; a source word appears only in its specification. |
| Finite-cylinder memo and atom composition | `arithmetic_leaf_same_cylinder`, `arithmetic_leaf_block_compose` | Equal low cylinders give the complete arithmetic effect, including prefix safety; the right block consumes the transported first-block image. Cache authority, transaction lifetime and allocation are Python checks, not consequences of observer equality. |
| Right low-residue transport and chronological composition | `balanced_spec_source_effect`, `source_effect_reduced_numerator` | Exact non-power splits and transported right sources are modeled. The reduced-numerator equation justifies modular transport; Python's allocation shortcuts and bit charges are independently reviewed/tested. |
| Postorder execution and exact memo | `Dyadic_Balanced_Worklist.machine_step_preserves_invariant`, `execute_balanced_correct`, `machine_steps_memo_bound` | Models pinned functions, `(span,residue)` keys, duplicate no-op, oldest-entry eviction before optional reservation, and early completion. Numeric validity does not certify Python support IDs or ledger authority. |
| Antihydra `delta`, `minimum`, and guarded returns | `Balanced_Dyadic_Families.antihydra_balanced_finite_ledger`, `antihydra_constructed_guarded_finite_apply` | Applies the constructed source effect to the existing finite arithmetic/ledger semantics. Physical TM roofs and tape require their separate refinement. |
| First-failure descent | `Dyadic_Support_Descent.make_support_join_valid`, `support_first_failure_exact` | Smart chronological trees preserve cached summaries; descent returns the exact zero-based failing branch for an initially nonnegative balance. This does not prove the runtime retained-ID graph or cycle-compressed leaf mapping. |
| Collatz physical output and prefix safety | `collatz_balanced_constructed_endpoint`, `collatz_balanced_finite_minimum_zero`, `collatz_physical_first_negative_unreachable` | Applies to every finite physical horizon. Nonnegative bookkeeping weights do not prove convergence. |
| Mahler demanded associated action | `mahler_centered_source_fold_all_prefixes` | Binds the actual source-8 centered branch fold to coefficients from the constructed Antihydra transfer, including lengths zero and one. This is finite action equality, not all-time positivity or ledger safety. |
| Mahler finite cap and first failure | `mahler_constructed_source_eight_cap_failure_iff`, `mahler_source_eight_first_failure_index` | For the fixed source-8 consumer, a nonpositive cap occurs exactly at horizons at least two; the first failing one-based return is two. This is a different predicate from Antihydra's ledger and does not prove TM halting. |
| Exact cycle suffix | `Collatz_Physical_One_Cycle.collatz_physical_cycle_odd_count` and `collatz_cycle_chunks` | Prove the semantic `(1, 4, 2)` cycle and its odd-count law. Python exact-source admission, cached cycle IDs and cycle-compressed support descent are covered by runtime checks/tests; their executable refinement remains separate. |
| Control work and transient stack | `tree_nodes_linear_bound`, `machine_completes_within_work`, `reachable_stack_linear_bound` | At most a linear number of abstract transitions, a certified linear stack envelope, and at most 64 memo entries. These are not bounds on integer multiplication, retained bytes or wall time. |
| Support/image publication and resource ledger | Runtime authority checks and adversarial tests | Formal refinement of `ArenaHandle` ownership/generation, retained-ID publication, rollback and allocator charges remains separate from the numeric executor theorem. |

The worklist's public executable has a static fuel bound and returns early at
completion. It calls only its bounded leaf, transport and join operations;
neither the recursive specification nor its proof-only work potential is an
execution oracle. `cache_admit` abstracts optional cache reservation, so cache
refusal cannot change the numeric result. A request-wide budget failure in
Python still refuses the request rather than satisfying a success theorem.

Build the concrete bridge (which builds its registered dependencies) with:

```console
isabelle build -d devtools/proofs/isabelle -j 1 -o threads=1 -o parallel_proofs=0 Balanced_Dyadic_Integration
```

The new theories audit exported theorem dependencies for oracles. Session
registration disables quick-and-dirty proofs. The project guard remains
60 seconds / 4 GiB per Isabelle check.

The bounded differential checks in
[`test_balanced_proof_refinement.py`](../../tests/hashlife/execution/test_balanced_proof_refinement.py)
compare both laws, arbitrary split boundaries, high fibers, safety summaries,
retained branch support, exact memo reuse, eviction, and optional memo refusal
against an independent literal two-branch reference. Existing lifecycle and
authority tests in `test_dyadic_effect_reuse.py` cover constructor budget
rollback, stale/foreign handles, and exact-cycle high-fiber separation.
These tests can catch a bad refinement mapping; they do not turn Python into
verified code or establish global Collatz/Antihydra claims.

## Shifted parity arithmetic and its integration boundary

`Collatz_Parity_Shift_Germ` models normalized `H`, finite source Q-prefixes
and the two-phase physical suspension. Its semantic inverse is defined by
the unique residue with that prefix. This mathematical inverse alone is not
the executable loop in Python. `collatz_qprefix_bit_minimal_explicit` and
`collatz_phase1_positive_bit_minimal` state the differing-bit witnesses;
phase one's least significant bit is separately forced zero.
`Dyadic_Parity_Inverse_Arithmetic` separately
models that loop's modular unit product and accumulated residue, with branch
gains/offsets as parameters. `dyadic_generated_word_forward_equation` derives
the affine equation from the actual source itinerary, rather than assuming a
matching supplied word. `collatz_generated_inverse_residue` and
`antihydra_generated_inverse_residue` specialize the loop to their distinct
recurrences and return the original source modulo `2^n`, for positive `n`
and modular gain inverses satisfying the stated unit equations. They do not
construct a distant itinerary. Centered Mahler arithmetic is covered by the
generic signed-offset law and bounded differential tests; its source/safety
transport remains in the existing Mahler integration theories.

The numerical mapping excludes Python's byte
decoding, builtin modular inverse, object authority and resource ledger.
Independent bounded tests cover those arithmetic specializations; this is
not verification of Python execution itself.

The public point path still calls `_source_image()` and the admitted affine
threshold projection. Its power-of-two limb demand now evaluates the whole
limb once, with the same exterior guard and a live source/action/image binding.
`collatz_shifted_parity_residue` is a supplied-cursor arithmetic operation and
has no production cursor publisher. Replacing the constructor additionally
requires authenticated physical weighted selection, demanded Q precision,
exterior-cell admission and a construction-cost bound. A finite inverse or
a theorem about an already supplied cursor discharges none of those by itself.

The [weekly record](../../results/current/2026-W39/README.md#shifted-parity-germs-and-batched-limbs)
records exact build status and measured projection scope.

## Safety and cost scope

`Collatz_Reduced_Precision` additionally proves an upward high-fiber identity:
`source + 2^min(n,even_count(n,source)+1) * high` has the same complete finite
branch/effect as `source`. Its exported safety corollaries reuse that equality.
This theorem does not change Python's exact `(span,residue)` memo, prove an
arbitrary two-source canonical representative, or establish a speedup. The
[powered boundary audit](../../results/current/2026-W39/README.md#powered-boundary-germ-audit)
records the independent finite tests and rejected extra scan.

Collatz's physical weights are nonnegative, so its `minimum` cannot witness a
negative ledger prefix. Antihydra's weights `(2, -1)` can: the shared descent
returns the zero-based index of the branch whose **completed return** makes the
sum negative. The TM's physical tick and tape semantics are different demands.
Mahler's associated action uses centered `D = a - 1` bits; at source `a = 8`
its first two centered bits are `11`, while the physical `a` bits are `00`.
Those predicates must remain distinct in any consumer proof.

The runtime separately charges bounded leaf classifications, residue
transport, skew joins, memo lookups/publications/evictions, transient stack,
retained support, and later demanded expansion. The 64-entry memo can make a
homogeneous cylinder cheap; it cannot make an arbitrary high-entropy cold
source sublinear. Counted operand-bit growth, measured wall time, and a
successful-constructor asymptotic bound are three separate claims. No theorem
about a supplied branch word or generic associativity closes the latter two.
