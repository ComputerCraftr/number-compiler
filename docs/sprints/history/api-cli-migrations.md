# Historical API and CLI migrations

## Provenance

These migration notes retain the earlier removed-module and command-form decisions. The exact original migration day is not recorded here; the notes were separated from maintained references during the 0.60.0 documentation cleanup. They describe past changes, not current acceptance evidence. Current usage is documented in the [CLI reference](../../cli.md) and [metrics reference](../../metrics.md).

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
block operations in `devtools.verification.block_power`. Developer packages are not shipped
in the production wheel.

The bounded Fermat/Mersenne carrier jump, symbolic proof power, and experimental
source-support language likewise live at
`devtools.verification.oracles.special_binary_jump`,
`devtools.verification.special_power_monoid`, and
`devtools.verification.special_source_program`. They were never high-level sequence APIs;
production Fermat and Mersenne digits continue to use their sparse closed forms.

Canonical ownership and public exports are tested against the source and installed
package, replacing the former handwritten migration and export manifests.


## Family-first command migration

The CLI uses `number-compiler FAMILY --nth N`. The former `nth`, `observe`,
`classify`, `verify-nonhalting` and `families` commands are removed. Python API
entry points retain their existing behavior; Antihydra arithmetic is added to
`NumberCompiler.project_nth`.


## Metrics presentation migration

The detailed `power_metrics()` APIs retain the per-owner inventory and raw
work counters for audit tooling. Obsolete tile fields are not copied into
compact CLI output. Their removal from presentation does not close the
reverse/add constructor or Collatz cold-discovery obligations.

The schema-7 presentation assertions map to the same captured ledger's
`temporal_diagnostics` and `resources`; detailed inventory checks remain in
API tests. Positive temporal cutover assertions remain enabled and unchanged
apart from their schema version.
