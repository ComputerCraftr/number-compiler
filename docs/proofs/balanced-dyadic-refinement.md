# Balanced dyadic return: executable refinement map

This map identifies the production objects modeled by the shared dyadic source,
skew, worklist and prefix-safety theories. Build evidence and its Git provenance
belong in the weekly record. A checked executable Isabelle model
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

`Prefix_Effect.blank_ledger_word_append` and
`blank_ledger_repeat_closed_form` model the shared Python `BlankLedger`:
displacement, minimum prefix and maximum prefix, with chronological composition
and closed-form repetition. The lower lane uses the original displacement;
the upper lane uses its negation. The word and repetition theorems describe an
already authenticated sequence of displacements. They do not authorize repeating
a source action or merging occurrences that share a width summary.

The focused `Prefix_Effect_Core` build passed in 13 seconds under the standard
guard in development run `20261006T035426Z-fa2cefa96bee4de78ea54117a7525b42`.
This does not discharge the reverse successor constructor or global Comma
release obligations.

`Comma_C1_Borrow_Cocycle.comma_c1_borrow_ledger_append` applies this shared
composition to the native C1 one-step innovation word, transporting both source
phases at the split. Its delta theorem recovers the existing accumulated borrow
innovation; its one-step formula keeps phase admission and adjacent-sector
hypotheses. This session passed in 15 seconds in
`20261006T035905Z-35325afc192a4b918eebd4c9c1d1ff88`.

`Dyadic_Balanced_Arithmetic.source_effect_blank_ledger_projection` identifies
the shared lower/delta projection with the existing constructed source safety
summary. `source_effect_blank_ledger_append` composes the full summary across
source-word segments. The existing dyadic effect has no upper-extremum field;
the theorem does not invent that field. `Shared_S_Arithmetic` passed in 33
seconds in `20261006T035935Z-1828ec575bb341d88c6a447fa518590b`.
These bridges share the algebra without identifying Comma innovations with
Collatz width increments or Mahler safety predicates.

`Reverse_Threshold_Cocycle.native_source_width` proves that pair width is
source width plus `native_growth_count`, defined by producer growth flags along
actual successors rather than by subtracting endpoint lengths.
`native_source_growth_count_add` composes that count at the returned successor;
`native_terminal_output_length` keeps final digit carry separate. The
`Reverse_Residuals` session passed in 19 seconds in
`20261006T040930Z-d19d058fa0e5462786c4ee2ab8708476`. The model still uses exact
list successors; this proves the width equation, not a compressed temporal
transducer implementation or its cost.

`Maximal_Run_Arithmetic` models the homogeneous contractions used by
`collatz/temporal_run_quotient.py` and `antihydra/arithmetic_images.py`:

- `collatz_physical_odd_run` consumes `2k` physical ticks from
  `2^k*u-1`, with `u>0`, and returns `3^k*u-1`.
- `collatz_physical_even_run` removes a supplied dyadic factor in `k` ticks.
- `antihydra_centered_odd_run` and `antihydra_centered_even_run` establish
  both the endpoint and the source parity word for the two homogeneous cases.
  The source parity is the complement of the implementation's centered parity.
- `antihydra_centered_run_guards` gives the exact finite ledger condition;
  `antihydra_run_endpoint_parity` proves the parity switch when the residual
  factor is odd.
- `antihydra_punctured_event_bits`, `antihydra_punctured_event_endpoint` and
  `antihydra_punctured_event_ledger` contract `0^k1` in centered coordinates.
  From `D=2^k(2M+1)` the endpoint is `3^(k+1)M+(3^(k+1)+1)/2`, the ledger
  delta is `2-k` and its minimum is `-k`. These are the formulas used by
  `_punctured_steps` inside the existing bounded scheduler leaf.

These lemmas justify arithmetic within one admitted run. They do not prove the
Python run-discovery loop, routing heuristic, allocation bounds, anonymous
F5/root-fiber quotient, or a bound on the number of future runs. Production
retains balanced construction for wide mixed inputs because repeated full-width
run arithmetic can increase operand work quadratically. Exact singleton
Collatz endpoints do not represent the affine action on every residue lift.

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
.venv/bin/python -m devtools.checks.release --suite proofs --session Balanced_Dyadic_Integration
```

The new theories audit exported theorem dependencies for oracles. Session
registration disables quick-and-dirty proofs. The project guard remains
300 seconds per Isabelle session, 6 GiB across the process tree and four prover
threads, with one session building at a time.

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

The [weekly record](../sprints/week-of-2026-09-20/shared.md#shifted-parity-germs-and-batched-limbs)
records exact build status and measured projection scope.

## Safety and cost scope

The centered physical coordinate `Y = x - 1` has two checked affine fiber
rules in `Collatz_Parity_Shift_Germ`: `collatz_centered_odd_fiber` consumes
one tick on an odd centered fiber, while `collatz_centered_even_fiber`
consumes two ticks on an even centered fiber. The latter includes the forced
halving tick. `collatz_centered_source_restriction` transports a source bit
into the affine chart. These rules specify arithmetic after a branch has
been admitted; they do not construct the branch classifier or prove that
arbitrary temporal squares need bounded discovery.

`Mahler_Spatial_Carry_Pump` reuses the same radix-block conservation owner
for the nine carries of `9*M+c`. `radix_four_root_derivative_finite_port`
connects a matching root digit of `27*M+3*c+1` to that carry,
`radix_four_one_two_reset` proves the two-digit sentinel reset, and
`radix_four_one_run_conservation` pumps the remaining constant run.
`mahler_radix_four_reentry` binds the two-step source recurrence to `9*M+c`;
its four source residues yield ports `0,3,5,8`. These are spatial arithmetic
and source-reentry results, not an all-time safety theorem or refinement of
Python's source cursor and cache. The Python root-owner regression checks
the same nine-port identity against bounded independent integer arithmetic.

The same theory now defines an executable first-hole classifier on source
trees with authenticated cached extents. `radix_four_classifier_append`
proves chronological spatial composition;
`radix_four_source_classifier_refinement` connects the tree to the literal
digit specification, and `radix_four_source_classifier_early_exit` leaves the
right child undemanded after a left-hand hole. The cursor law
`radix_four_classifier_cursor_conservation` retains the original suffix with
its post-hole carry: the transformed high value is `9*suffix + carry`, not
the suffix alone. This is not yet a refinement of Python's run leaves,
authenticated cursor covers, memo lifecycle or resource ledger.

The positive odd-event consumer uses `mahler_maximal_odd_event_closed_scale`
in `Antihydra_Mahler_Associated_Action`: the word `1 0^(q-1)` has scale
`(3/2)^q`, offset minus that scale, and cap `min(9/4, scale/2)`. The
research `SourceSafetyWorkspace.odd_zero_observer` obtains `q` from the
shared source-root classifier before applying this observer formula. This
odd-then-zeros observation does not select the live zero-then-one source
safety event: at `D=1` its exponent is 2, while `source_event` selects 1.
Raw-source `-1/3` selection and transformed `9*M+c` selection remain distinct; neither
the formula nor the tree theorem authenticates arbitrary higher-half sources.

Run algebra has shared ownership: `Prefix_Effect` and
`Dyadic_Prefix_Summary` handle signed prefix totals for the dyadic families;
`Associated_Action_Pullback` handles chronological saturated affine actions.
Its `associated_action_dilation_tail` now supplies Mahler's expanding run law
under scale at least one and nonnegative cap. Comma's translation guard uses
the existing `repeated_prefix_minimum_closed` in that same theory. The
different family guards and source classifiers are not interchangeable.

The focused [comma ordered-root model](../../proofs/isabelle/families/comma/comma_vieta_root/Comma_Vieta_Root_Frame.thy)
uses the actual phase/displacement definitions. Its bounded selector refines
one local Near prefix, under explicit frame, alignment and headroom guards;
its row port permits two root crossings. Neither this local constructor nor
shared run algebra supplies the missing source-to-residual classifier,
weighted repeating return or global branch safety required for forest removal.

`Collatz_Reduced_Precision` additionally proves an upward high-fiber identity:
`source + 2^min(n,even_count(n,source)+1) * high` has the same complete finite
branch/effect as `source`. Its exported safety corollaries reuse that equality.
This theorem does not change Python's exact `(span,residue)` memo, prove an
arbitrary two-source canonical representative, or establish a speedup. The
[powered boundary audit](../sprints/week-of-2026-09-20/shared.md#powered-boundary-germ-audit)
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
retained support, and later demanded expansion. The balanced executor's
64-entry memo has no established arbitrary-source sublinear construction
bound. This describes the implemented owner, not a lower-bound theorem for
alternative cylinder constructors. The physical run path also has a separate,
lazy 256-row D8 table; its cold discovery and retention must be counted.
Counted operand-bit growth, measured wall time, and a
successful-constructor asymptotic bound are three separate claims. No theorem
about a supplied branch word or generic associativity closes the latter two.


### Finite D8 arithmetic specialization

`collatz_d8_all_source_fibers` in
[Dyadic_Parity_Inverse_Arithmetic](../../proofs/isabelle/integration/dyadic/integration_dyadic/Dyadic_Parity_Inverse_Arithmetic.thy)
proves `256 * H^8(x) = M(x mod 256) * x + B(x mod 256)`.
The executable forward-coefficient recurrence supplies `M,B`, and
`collatz_qprefix_low` establishes that every higher lift selects the same
normalized symbols. This is the arithmetic used by the lazy production D8
table. Independent finite tests check all 256 residues, several large lifts,
physical clocks, optional F5 transport and exact cycle entry.

The theorem is unconditional finite arithmetic. It does not certify Python
cache authority, prove the scheduler's publication code, or bound the number
of D8 sections for an arbitrary horizon. These claims remain separate from
the local coefficient equation. The focused `Balanced_Dyadic_Integration`
session includes the theorem in its oracle audit.

### Target-centered source sections

`Collatz_Parity_Shift_Germ.collatz_target_centered_source_lift` specializes the
shared `exact_precision_source_lift` to
`H^n(r + 2^n*u) = H^n(r) + 3^h*u`, where `h` counts odd symbols on the actual
source prefix. `collatz_centered_gain` proves the gain simplification. Python's
D8 table retains exactly `h` and `H^8(r)`; its source key supplies `r` and its
fixed width supplies eight. Application uses the same equation. Optional F5
transport rebases the origin using `2^8 = 1 (mod 5)`.

Antihydra already obtains the corresponding gain `3^n` from
`Antihydra_Arithmetic_Cylinder_Lift.antihydra_family_orbit_cylinder_transport`.
No new Collatz recurrence or endpoint-only safety quotient is introduced for
that family. Mahler's finite cap and Antihydra's ledger minimum are additional
consumers; target centering does not discard them. The ownership, guarded
publication and construction-cost obligations listed above are unchanged.

`collatz_d8_cylinder_transition` also proves the byte transition on an affine
frame: with `v = origin + gain*digit`, the next frame has origin
`H^8(v mod 256) + 3^h*(v div 256)` and gain `3^h*gain`. Its high continuation
stays symbolic. This proves local transition arithmetic; bounded batching,
source-window admission, allocation and physical weighted selection remain
runtime obligations, and it does not establish a finite transition quotient
closed under arbitrary temporal squaring.

### Cache consumption and focused proof ownership

[Source_Cache_Consumption](../../proofs/isabelle/integration/source_cache/integration_cache/Source_Cache_Consumption.thy)
connects the cached Collatz width, residue, odd count, target origin and gain to
the exact normalized orbit. `cached_occurrence_source_transport` proves
application to any matching high fiber; `cached_occurrence_physical_consumer`
proves its physical cost is width plus odd count. The record must satisfy the
constructor's semantic publication invariant. Merely validating a gain or
matching a finite quotient label does not discharge that invariant.

`admitted_parent_lookup_returns_without_descent` and
`admitted_root_hit_completes_in_two_control_steps` concern the existing
`Dyadic_Balanced_Worklist.machine_step` implementation. They show the control
work avoided by a valid memo hit. They do not erase key construction, admission,
integer arithmetic or Python storage validation.

The normalized parity germ has moved into the focused `Source_Cache_Integration`
session. It imports its actual physical-map and dyadic-source dependencies,
without the unused full physical-cylinder/balanced-family branch. The broader
session imports this canonical owner; no arithmetic was copied. Build with
`python -m devtools.checks.release --suite proofs --session Source_Cache_Integration`.
Whole-constructor refinement, generation-qualified Python cache lifecycle,
reverse output publication and cold construction bounds remain separate gates.
