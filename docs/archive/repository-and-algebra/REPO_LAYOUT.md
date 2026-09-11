# Repository concern layout

The package is moving behind seven concern namespaces while preserving the
existing `number_compiler` imports. `PACKAGE_CONCERNS.toml` records the modules
that already have one canonical owner and the migration groups that remain.
`PUBLIC_API_MANIFEST.json` freezes the top-level exports and console entry point
that the moves must preserve.

- `api` owns the public projection compiler, immutable sequence records and
  terms, and the CLI. Historical root module paths are cache-free aliases to
  these implementations.
- `core` owns scoped identity and representation contracts that have completed
  migration, the immutable canonical program-word rope, scoped monoid
  powering, and canonical finite semantic functions. Program-word global
  interners are weak and cannot retain words across index lifetimes.
- `runtime` owns field actions, finite interfaces, recursive field images,
  iterative execution, and the canonical factored semantic DAG compiler. The
  historical root `semantic_bits`, `semantic_structures`, state-codec,
  expression, publication, and primitive-macro module paths are cache-free
  aliases to these runtime implementations, so imports and monkeypatches retain
  one module identity.
- `families` owns the reverse/add and Collatz field-action integrations, plus
  the prime algorithms under `families/prime` and the Fermat/Mersenne
  algorithms under `families/special`. Historical `prime_*` and `special_*`
  root modules are forwarding-only compatibility facades. The family package
  initializers are intentionally import-free so low-level helpers do not
  create initialization cycles. The concern also owns the historical Collatz
  symbolic-action and spacetime compatibility implementations and their
  forcing morphism; their root modules are forwarding-only, and the powered
  public route does not import them.
- `resources` canonically owns the resource ledger, ledger-created stores,
  ownership inventory, semantic payload schemas, and representation audits.
  It also owns schema-six records, counter/inventory mappings, projection and
  behavior reporting, and the one ledger-snapshot collector. Payload-audit
  graph helpers are also kept here so the reporting module stays below the
  repository source-size ceiling. Their root modules are forwarding-only
  compatibility facades.
- `output` canonically owns digit normalization, endpoint lowering, the bounded
  scalar response register, capped exact microblocks, lazy radix projection,
  fused division actions, original-source radix views, and output quotients.
  The corresponding historical root modules are cache-free aliases.
- `proof` owns the exact slabs, whole-word certificates, proof machines, and
  differential helpers already moved there.

`legacy_root_migration_pending` remains true. Root diamond modules, other
family integrations, shared radix arithmetic/analysis, semantic payload audit
registries, and proof
compatibility owners have not all migrated. No completion claim is made for
those groups.

The old composed-block runtime and its partition, recursive-state, spacetime,
and statistics helpers now live under `proof` as one explicitly listed
compatibility group. Their historical root names are forwarding-only facades.
They remain live through `block_power` and direct compatibility imports, so the
implementation has not been deleted or relabeled as production field images.
Production generic admission recognizes an already constructed compatibility
value through a cacheless sealed marker and no longer imports that executor.
The retired reverse coordinate bridge that instantiated this runtime was
unreferenced and has been removed; reverse observations use the shared higher
field runtime.

Production code may use the shared runtime and generic finite-interface
compiler. It must not import `number_compiler.proof` or instantiate a retired
proof-only whole-word executor. Compatibility facades own no caches, ledgers,
or executors.

Exact digit geometry is restricted to immutable source construction, capped
microblocks, and explicit endpoint lowering. Future field images retain
canonical interface, output-morphism, geometry, and child IDs.
