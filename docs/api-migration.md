# Public API migration

Keep using `from number_compiler import NumberCompiler`,
`CanonicalSequenceCompiler`, the family specification/compilation types,
`ReverseAddPoweredTerm` and `PoweredCollatzTerm`. Their high-level behavior and
return types are preserved. The console entry point remains
`number_compiler.api.cli:main`.

Old root modules such as `number_compiler.reverse_power`,
`number_compiler.semantic_structures` and `number_compiler.block_power` are removed.
There are no import redirection hooks or forwarding files. Low-level runtime,
proof and experiment exports are not part of the public API.

Internal callers import their implementation directly. For example, reverse terms
are implemented in `number_compiler.sequences.reverse_add.power`, semantic structures
in `number_compiler.hashlife.interfaces.semantic_structures`, and explicit proof
block operations in `devtools.proofs.block_power`. Developer packages are not shipped
in the production wheel.

The bounded Fermat/Mersenne carrier jump, symbolic proof power, and experimental
source-support language likewise live at
`devtools.proofs.oracles.special_binary_jump`,
`devtools.proofs.special_power_monoid`, and
`devtools.proofs.special_source_program`. They were never high-level sequence APIs;
production Fermat and Mersenne digits continue to use their sparse closed forms.

Canonical ownership and public exports are tested against the source and installed
package, replacing the former handwritten migration and export manifests.

## Metrics schema 8

Term/query APIs, CLI selectors, indices and budgets are unchanged. CLI
`--info metrics` now emits a compact `execution_metrics` object with
`schema_version: 8`. The detailed Python ledger report remains available to
probes; its `metrics_schema_version` is also 8.

- `action`, `application` and `projection` keep separate reuse populations.
  Action counts describe the current admitted action arena; they do not certify
  a saturated extensional macrocell or count its semantic equivalence classes.
- `construction` reports scheduler operations; finite source discovery is
  reported separately under `family_work`.
- `demand` and `stream` distinguish query counts, spatial visits and emitted
  symbols. A stream visit is not a temporal jump.
- `observations` exposes measured observer work; `resources` reports entries,
  nodes, peaks and accounting status.
- `null` means the exact counter is unavailable. Only an instrumented zero is
  emitted as `0`. Antihydra snapshot capture leaves `audit_complete=false`;
  unknown inventory comparisons remain `null`. No bootstrap bound or constructor success is inferred from
  missing counters, cache hits or a zero primitive count.

The detailed `power_metrics()` APIs retain the per-owner inventory and raw
work counters for audit tooling. Obsolete tile fields are not copied into
compact CLI output. Their removal from presentation does not close the
reverse/add constructor or Collatz cold-discovery obligations.

The schema-7 presentation assertions map to the same captured ledger's
`temporal_diagnostics` and `resources`; detailed inventory checks remain in
API tests. Positive temporal cutover assertions remain enabled and unchanged
apart from their schema version.

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
