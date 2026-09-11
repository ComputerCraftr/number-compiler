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
