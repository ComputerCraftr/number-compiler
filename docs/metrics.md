# Metrics reference

## Metrics schema 8

CLI
`--info metrics` emits a compact `execution_metrics` object with
`schema_version: 8`. The detailed Python ledger report remains available to
probes; its `metrics_schema_version` is also 8.

- `action`, `application` and `projection` keep separate reuse populations.
  Action counts describe the current admitted action arena; they do not certify
  a saturated extensional macrocell or count its semantic equivalence classes.
- `construction` reports scheduler operations; finite source discovery is
  reported separately under `family_work`.
- `family_work.finite_block_*` separates finite-cylinder lookups, hits, misses,
  publications, evictions and cold arithmetic (atoms and transitions) from
  action interning and the outer balanced-effect memo. These are read-only
  counters shared by Collatz and Antihydra; Mahler consumes the latter's support.
  Repeated finite-cylinder hits do not certify a temporal pumping theorem.
- `family_work.guarded_template_*` counts query-local exact guarded-action
  lookups, hits, misses, publications and capacity bypasses. These are separate
  from source-occurrence and innovation-observer reuse. A template hit still
  requires the receiving source's cylinder and physical-duration admission;
  it does not transfer another source's endpoint. Unused owners report `null`.
- `family_work.guarded_prefix_*` separates consumed macro requests, root and
  interval candidates, arithmetic operand bits, new root-checkpoint publications
  and budget bypasses. Interior interval joins retain the occurrence owner's
  counters; deriving a checkpoint is construction work, not an applied hit.
- `family_work.root_checkpoint_work` lists measured checkpoint construction
  counters from ordinary runs and D8 blocks: candidate/publication counts,
  bounded D8 transitions, frame materializations, operand-bit work and budget
  bypasses. Missing counters are omitted. These are auxiliary construction
  costs, not occurrence hits or represented transitions.
- `family_work.border_return_work` reports measured border selector checks,
  valuations and operand-bit work, together with separately named represented
  zero-tail symbols and admitted exit/reentry counts. Candidate work includes
  rejected attempts; represented symbols are not an execution-work estimate.
- `demand` and `stream` distinguish query counts, spatial visits and emitted
  symbols. A stream visit is not a temporal jump.
- `observations` exposes measured observer work; `resources` reports entries,
  nodes, peaks and accounting status.
- `null` means the exact counter is unavailable. Only an instrumented zero is
  emitted as `0`. Antihydra snapshot capture leaves `audit_complete=false`;
  unknown inventory comparisons remain `null`. No bootstrap bound or constructor success is inferred from
  missing counters, cache hits or a zero primitive count.

The `macrocells` rows, when instrumented, distinguish semantic interning from
source-qualified occurrence reuse. Each instrumented lane reports lookups, misses and publications.
`exact_hits` and `transported_hits` are disjoint retrieval outcomes;
`local_hits` and `process_hits` describe the separate storage-location axis.
`applied_hits` counts only admitted records actually consumed by execution, and
`applied_parent_hits` identifies applications that bypass child construction.
`rejected_fit` records a retrieved occurrence whose physical weight does not fit
the requested remainder. `admission_rejections` records present entries rejected
before an admitted retrieval; it is neither a hit nor a miss. Instrumented
lookups partition into hits, misses and admission rejections. Older producers without these distinctions expose
`unclassified_hits`; reporting does not relabel them as exact hits. A semantic
hit does not imply that construction was skipped. `max_level` uses absolute
depth in the row's explicit `index_unit`: D8 is level 3. Collatz macrocells
count normalized symbols, whereas the public nth index counts physical ticks.
Primitive discovery increments at evaluation, including a bounded root probe
whose action is not used; it is not delayed until successful run publication.
Merges, spatial leaf visits and operand-bit work retain their own units. Missing instrumentation
remains `null`; a family without this owner has no macrocell row.

Additional macrocell measurements distinguish consumed `applied_parent_hits`
from key construction (`key_operand_bits`), `cold_child_discoveries`, and
`coefficient_compositions`. `occurrence_frontier_joins` counts joins of already
observed adjacent block metadata; it is not a count of skipped transitions.
`capacity_bypasses` records optional cache admission failures, once per refused
publication or lease. For Mahler it sums the measured source-action and outer
observer lanes; Antihydra sums source-action and arithmetic-occurrence lanes.
Each lane retains its own `bypasses` total for instrumented reasons. Collatz
occurrence and Mahler outer-observer lanes additionally distinguish
`disabled_bypasses`, `policy_bypasses` and `capacity_bypasses`; disabling shared
reuse or choosing the small-action constructor does not imply a capacity
refusal. A local Collatz hit does not bypass a process lookup that was never
needed. Local occurrence root removals are counted as `evictions`. Output-region
visits, emitted digits and failed work remain nullable until their owners measure
them. Reading these columns does not run a constructor or a storage audit.

Comma's `macrocells` row uses `index_unit="oeis_transition"` and
`cache_scope="guarded_interior_cycle_action"`. Its semantic lane measures exact
complete-cycle action retrieval, followed by separately counted successful
scheduler application. Source value, absolute index and headroom are rebound
and checked at application. This is not a Q19/M111 future-branch quotient.
Complete-cycle arithmetic keys use `digit mod gcd(leading,10)`; the local
application retains its actual entering digit. A process hit across rotations
therefore shares an equal complete-cycle summary, not a partial phase prefix
or a different source endpoint. The extra key-normalization operation is charged.
Occurrence-lane and tree-depth measurements remain `null`; no depth or merge
count is inferred from a large represented duration. Explicit cache bypass is
reported in the semantic lane but does not count as a capacity refusal.

The optional `cellular` lane separates `2rev10` spatial transducer applications
and direct two-step squares from temporal HashLife
publications, cone misses and cone hits. `represented_two_step_steps` measures
the number of represented applications of the two-step rule, not executed
primitive transitions or work saved. `represented_growth_cells` counts output
growth represented by published actions, not executed seam operations.
Boundary classifications, boundary-node
visits and tile selections expose validation and spatial selection work even
when an action or cone is retrieved from a cache. Weighted carry, moment and affine port
publications count demanded observation construction. Uninstrumented fields are
`null`; the collector does not derive a count from temporal depth or render an
endpoint to fill a field.

Shared reuse is process-local: separate CLI processes start cold. Same-process
API requests may reuse compatible admitted germs; `shared_cache=False` bypasses
that reuse and `clear_shared_cache()` invalidates it. Full-output rendering and
cold discovery remain separately charged. `process_cache` reports aggregate
process retention and reuse, explicitly labeled `process_aggregate_not_query_work`;
reading it never creates the cache or a lease. Descriptor-era `shared_cache_*`
fields describe the prime query snapshot, not these later macrocell operations.

Public Python metric reports retain per-owner inventory and raw counters, but
do not initiate deep payload or ownership audits. Explicit
`collect_ledger_metrics(ledger)` remains the audit entry point; callers can use
`audit_payloads=False` to reuse only still-current audit evidence. Inventory
reporting is separate from the CLI snapshot collector, which never traverses
retained payloads.

Reverse completed-range validation counts `field_range_summary_validations`
and `field_range_summary_validation_expressions` at publication and recovery;
these are admission work, not cache hits. Explicit reverse payload audits charge
`reverse_payload_audit_identity_operand_bits` without changing execution-cache
counters or publishing semantic identities. Ordinary metric snapshots do not
perform this audit work.

Powered interface `requests`/`early_hits` measure lookups only.
`publication_requests`, successful `publications` and `late_aliases` are
separate; publishing an already-known interface is not an execution cache hit.
Reverse exact-width reuse is exposed in `observations` through
`reverse_recursive_pair_width_cache_hits`, `reverse_recursive_pair_width_cache_misses`,
`reverse_recursive_pair_width_publications`, `reverse_recursive_pair_width_descents`
and `reverse_recursive_pair_width_failures`. Lookup misses include failed searches;
publications count only completed searches. These are occurrence-bound observation
counters, not authenticated producer growth or temporal-construction savings.
Missing instrumentation remains null. Metric snapshots do not calculate width.
Reverse terminal growth reports `reverse_recursive_terminal_reset_prefix_symbols`,
`reverse_recursive_terminal_reset_hits` and `reverse_recursive_terminal_neutral_fields`.
These measure the symmetry-based first-reset consumer; they do not include or
replace separately charged higher temporal evaluation. `reverse_recursive_direct_carry_steps`
counts actual forward digit normalization, not a removed whole-word width fold.
Final digit-stream emissions include reverse/add's terminal carry. Underlying
recursive pair-symbol visits remain separate from final output. Stream requests,
emissions, cancellations and failures are charged at consumption, including
partial streams; unavailable measurements stay null. The separate `rendering`
record counts complete CLI render attempts, produced output digits, failures and
the bit sizes passed to integer-to-text conversion. It covers decimal conversion
that bypasses a native binary stream, without counting those two layers as the
same work. Native stream counts describe consumption at that producer boundary;
a reverse-order API adapter that first buffers the complete forward stream
therefore reports that complete native work. It does not claim that the caller
has already pulled every digit from the returned reversed iterator. CLI
converters close partially consumed native streams immediately on failure.
The legacy `bimachine_composition_certified` field checks the live registered
generic application and its ownership/lease binding. It is not an Isabelle
completion declaration or a certificate for a different family executor.


Comma metrics distinguish `cycle_rule_evaluations` (closed-form arithmetic)
from represented literal transitions, and boundary-template publications from
source-bound applications. `evaluated_transitions` counts actual scalar step
evaluations, including failed attempts; a powered application or relative cache
hit never increments it by its represented duration. `seam_predicate_check_bound` is a conservative count
of candidate checks, not an observed branch count. Streaming reports emitted
digits and peak logical workspace slots/integer bits; those bits are not a
Python heap-byte measurement. Reading metrics never constructs a macro or
verifies a certificate.

For A367620, `--no-value --info certificate` reports evidence availability
without checking the current forest. `runtime_verified` describes admission
already performed by that query; a metadata-only request reports false. Value
admission remains mandatory and separate until the boundary-quotient cutover
passes its proof and consumer gates.
Digit-stream admission runs at first consumption. Resetting the shared cache
during consumption invalidates that stream before its next digit is emitted.

The macrocell `cache_scope` distinguishes `source_cylinder` application reuse
from Mahler's `complete_associated_action` memo. The latter reuses exact
consumer coefficients after the receiving image is admitted; it is not an all-level
temporal constructor or a claim of skipped source discovery.
When an admitted Mahler source occurrence supplies both its arithmetic summary
and associated action, the scope is `source_occurrence_associated_action`.
Its reuse lane reports source-action lookups and hits separately from the outer
observer memo; observer hits never count as skipped child discovery.

## Removed architectural declarations

The detailed runtime fields `bounded_temporal_runtime_cutover_complete` and
`bounded_temporal_runtime_cutover_blocker` have been removed without aliases.
They were architectural/proof declarations, not measured execution. Consumers
should check exact output, admitted image ownership, demanded-consumer work,
resource accounting and forbidden reconstruction directly. Checked refinement
status belongs to the source-fingerprinted proof inventory and build evidence.
A missing refinement theorem does not retroactively make a successful runtime
comparison a construction failure.

Mahler's `source_action` and `outer_observer` lanes are both reported when
present. The first measures admitted complete source actions; the second
measures exact associated-action retrieval, with scope
`process_complete_associated_action`. Its counters use
`mahler_hashlife_action_*`, replacing the misleading
`mahler_hashlife_occurrence_*` prefix. The action key retains every exact
constructor input and law; source seed, lift and precision are checked at
receiving-image admission rather than duplicated in this pure-action key.
An action hit is not an occurrence application or skipped child discovery;
unmeasured application and parent-hit fields remain null. Their hits are not added.
No number of semantic interning hits or temporal depth is converted into
occurrence applications or estimated work saved.


Ordinary Antihydra digit/value requests of at least 1,024 returns consult the
same authenticated complete-source-action store as Mahler when shared caching
is enabled. Their counters use `antihydra_hashlife_source_action_*` and appear
in the Antihydra row's `source_action` lane, separate from its `occurrence` lane.
A parent hit skips cold arithmetic discovery; it does not mean a Mahler observer
was requested. No Mahler binding is published for digit-only requests. Small
and cache-bypassed digit requests leave this lane uninstrumented (`null`).

## Homogeneous growth and canonical gain reuse

Schema 8 separates Collatz canonical-gain lookup from occurrence application.
The macrocell row's `gain_local_hits` and `gain_process_hits` count retrievals of
`3^H`; they are never added to occurrence or semantic-action hits.
`gain_key_operand_bits`, `gain_construction_operand_bits`,
`gain_validation_operand_bits` and `gain_bypasses` retain their distinct costs.

`growth_readout` describes demanded exact homogeneous radix arithmetic:
work, operand bits, precision bits, refinements, exact rational cases, bounded
integer-ratio cases, identity shortcuts, memo hits,
continued-fraction requests and budget refusals. Missing instrumentation is null. These
are observation costs, not measurements of nonlinear source discovery or the
number of actual endpoint growth events. Metrics snapshots perform no readout.

Collatz's `collatz_physical_tape_width_compositions`,
`collatz_physical_tape_width_repeat_operations` and
`collatz_physical_tape_width_operand_bits` charge width-summary construction
alongside already admitted runs and cycles. Width displacements and extrema
are result metadata in the optional clock packet, not accumulated work
counters. An unavailable width summary does not imply a zero displacement.

The `affine_width` lane reports exact leading-bit interval decisions:
requests, operand-bit work, interval checks, precision refinements, full-precision
boundary decisions and failed work. These counters measure deciding a width
from an admitted nonnegative affine source view; they do not count source
discovery or emitted digits. A width decision refines an ambiguous interval
instead of rounding it. Uninstrumented fields remain null, and reading this
lane never evaluates an affine view.

`macrocells[].width_projection` counts source-qualified width-summary lookups,
local/process retrievals, misses and publications. These retrievals do not count
as applying an occurrence. Collatz endpoint cylinders may transport across high
fibers, but their exact width summaries require the same high fiber.

`construction.reverse_pair_steps` counts executed pair-grammar transitions;
`construction.reverse_pair_sections` counts their newly evaluated spatial
sections. They remain visible when the higher output evaluator is unused.
Zero higher-evaluator work alone does not establish powered cold construction.

`construction.reverse_successor_rows` and `reverse_successor_spatial_bits`
measure the transient successor-width producer separately from completed
pair-grammar construction. `reverse_successor_pair_symbols` and
`reverse_successor_event_symbols` charge its pair and carry-event operands.
`reverse_successor_bootstrap_rows` counts actual rows before the carry-history
cutover; the decimal event-memory horizon is 20, rather than an eight-step
powered startup certificate.
These are executed work, not accumulated growth or represented time. A cached
width projection avoids repeating this work, but does not provide a completed
output grammar or prove a sublinear cold constructor.

`construction.reverse_successor_transport_updates` counts coefficient updates in
the live-event polynomial reconstruction. Each update includes two products, an
addition and a modular reduction; schedule, binomial and modular-power work is
not included in this counter. A spatial-row count alone does not measure that
reconstruction. Like the other optional constructor fields, it remains null
when that owner has not run.

`macrocells[].joint_action` separately reports requested joint endpoint and
accumulator-action reuse. It reads the existing `*_hashlife_joint_*` counters;
retrieval, transported admission and consumed application remain distinct.
It never adds these hits to endpoint-only occurrence or semantic interning
hits. Uninstrumented fields remain null, and reporting performs no joint
construction or accumulator observation.

`macrocells[].mixed_action` reports complete guarded periodic actions separately
from dyadic joint-action reuse. `retrieved` means a process record was found;
`admitted` means its receiving source and requested extent passed validation;
`applied_hits` increments only after demanded consumers accept that action.
Each retrieved record is a bounded bucket of at most eight complete actions.
`inapplicable` and `rejected_fit` count rejected candidates, so they can exceed
the number of retrieved buckets. Admission and applied-hit counts are per
lookup. `publications` counts changed buckets that retain the new action;
duplicates and capacity-pruned candidates do not increment it. Larger admitted
actions are considered before smaller ones.
`root_tail_rejections` counts source-compatible candidates that leave more than
the root route's bounded remainder. That check precedes action restoration and
does not count as an admitted or applied hit. A low-bit index collision alone
cannot produce this refusal: the complete source cylinder must match.
Key, payload and validation operand-bit counts measure their respective work;
they do not estimate work saved. These fields are snapshot-only and remain
null when the owner was not instrumented.
