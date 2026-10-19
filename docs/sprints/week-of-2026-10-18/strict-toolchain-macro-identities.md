# Strict toolchain and guarded macro identities

Period: 2026-10-18 through 2026-10-24 (Sunday–Saturday).

[Week index](README.md)

## Objective

Consolidate typed registry and guarded macro ownership, install the selected
current validation tools, and enforce strict whole-repository diagnostics without
weakening source, lifecycle, arithmetic, or performance assertions.

## Changes

The family registry now uses typed identifiers and lazy adapter contracts.
Observation packets and JSON boundaries have explicit types. Cross-module API
helpers have public names; superseded private re-exports and duplicate JSON
walkers were removed. Macro identity snapshots distinguish complete guarded
cycles, entry phases, paths, and finite bursts from display labels.

The Python development pins are declared in `pyproject.toml`; exact transitive
constraints identify CPython 3.14.8 on macOS arm64. Pyright is installed through a
private locked npm package. The quality runner checks dependency consistency and
runs serial batches of at most 25 authored files with a 2-GiB Node heap. Missing,
truncated, malformed, or incomplete diagnostic output fails the gate. Pylance is
strict with open-file background analysis; its editor results are separate.

The AST policy checks typed registry/macro boundaries and duplicate declarations.
The resource/scheduler migration replaces untyped task stacks with operation-specific
frames and separates causal state from spatial buffers. Review found and repaired
failed-insertion rollback, mutable operation tags, and missing buffer-growth
accounting. Audits still inspect actual retained payloads and backing-store identity.
Completed causal results validate their lease and authority without an unchecked
adapter cast. Helpers read the active run admission through a typed, read-only
interface; issuance and invalidation remain private to the engine. Cross-module
test helpers now have canonical public names.

The ownership audit now includes reverse/add, `2rev10`, Antihydra/Mahler and
Fermat/Mersenne. Reverse/add and `2rev10` source-bound trace builders are named
`border_occurrences`, rather than catalogues: they consume issued adjacent
children and share the existing guarded identity and exact-join contracts.
Redundant stored phase metadata was removed; Q19 ports and residue certificates
remain with their family issuers. Antihydra/Mahler supplied-action powers now
reuse the shared binary-composition owner, retaining their distinct spatial,
integer-cylinder and odd-return guards. Fermat and Mersenne clock identifiers own their arithmetic parameters and
serialized labels in typed declarations, replacing the separate display-label map.
Antihydra odd motifs now use a shared typed structural path identity, separate
from exact source and safety authority. Fermat/Mersenne joins consume the shared
clock/domain/seam contract and conditional radix-row composition; physical ticks
and trace-squaring steps remain distinct. Harmonic snapshots capture enum values
structurally, so mutation cannot hide behind the retained member object.

The temporal-bank audit extracted the common decimal five-band/F5 projection
into `arithmetic.fields.decimal_pair_partition`. Typed band identities replace
the reverse-local classifier, and reverse/add and `2rev10` frame builders share
the same projection. The generic compressed temporal-word concatenation owner
now lives in `arithmetic.automata.temporal_slp`; its reverse-local copy was deleted.
The seven-band successor partition and oriented family carry/borrow laws remain
separate. Band-only queries avoid allocating a complete projection record.

In Isabelle, the shared carry-domain owner now provides idempotence and decimal
threshold refinement to reverse consumers. The duplicate reverse proofs and
unreferenced Comma-local carry-power/reset chain were deleted. Carry orientation,
radix-specific emissions, and the distinct spatial/run Moore observations remain
with their semantic owners; local proof-fact names are not execution APIs. The duplicated first-reset scan
from reverse length and terminal output now has one owner in `Reverse_Residuals`;
terminal output projects its result while retaining the original theorem
statements and the independent query-count/palindrome arguments.

The ring consolidation removes the reverse-local channel tuple and repeated channel
projections. Typed family outputs extend the shared five-band partition; wire
names are emitted only at observation boundaries. The shared polynomial owner
now evaluates all four F5 modes in one Horner traversal, and finite ring period
search uses the existing linear word-period owner. 2rev10 width growth and skew
use `SkewMoment`; the mod-99 exponent proof consumes the shared weighted-exponent
composition theorem. Its source-specific growth schedule remains separately
admitted.

The Walsh audit found one remaining production butterfly in reverse/add. Its
signed convention is now derived from the common Boolean transform by
`W(1 - 2b) = 64 e0 - 2 W(b)`. Explicit low-64 masking preserves the old
observation boundary. The duplicate Walsh width and open-Moore state cap were
removed. Composable six-phase H5 actions, full Walsh64 transforms, physical
tripling clocks, Hensel precision, parity moments and norm-one trace clocks
remain distinct laws. Numerically equal caps for bits, nodes and physical ticks
are not treated as one resource limit. No production random-test generator was
found; seeded test distributions remain independent fixtures.

The port ownership audit found that `CrossFamilyPortAction` joined Collatz
border actions, not sequence families. Its owner is now
`collatz.source_closed_port_action.SourceClosedPortAction`, with callers
migrated and no alias. Schema-eight packet and metric spellings stay unchanged.
Generic diamond kernels and interfaces remain shared because reverse/add also
consumes them. The production HashLife tree and generic diamond test helpers
have no family imports. Collatz-only test setup is separated from those generic helpers;
the shared ordered-support layer owns joins, while family hooks own branch
interpretation and source admission.

Ring mutation review also found aliased enum snapshots, a stale positional
identity check and omitted center/mod-99/mod-198 retention. Value snapshots and
accounting now cover those fields. Public ring construction accepts authenticated
sources and demands, or two admitted adjacent children; it does not accept an
unchecked raw payload for publication. Source-owned frame windows validate once
at the batch boundary and retain child-issuance checks.

The audit did not justify interning Fermat/Mersenne issuer objects across
independent demands. Matrix/trace requests already share one query-context
construction, while adjacent matrix joins preserve exact issuer identity through
`rebase` and `then`. Fermat tripling clocks and Mersenne trace-squaring clocks
remain different laws. No global cache or alternative scheduler was introduced.

The audit interfaces now expose typed, read-only snapshots of retained stores and
source bindings. Developer statistics consume published metadata rather than
private execution fields. Forensic audits still validate the actual registered
backing store, malformed entries and nested issued authority on every requested
audit, including after disposal. Snapshot creation does not publish actions or
increment execution counters. Extracted contracts and audit helpers have one
canonical owner; callers import that owner directly.

The pending comma forest/fuel change is maintained as an authored, unapplied
[cutover patch](../../../devtools/cutovers/README.md). Its comparison tests retain
foreign, forged, stale and raced-lease checks. It does not register the candidate
artifact or replace the missing B1/B32/global kernel acceptance.

The typing tranche also repairs the runtime regressions exposed by migrated
audit interfaces. Reverse field and coordinate audits compare independently
computed actions with the actual canonical backing objects. Prime prefix
validation detects mutations in its admitted store. Causal queries authenticate
their issued action authority before selecting primitive or composite inputs;
replacing the record validator is rejected before invoking it. Ordinary Collatz
queries import lightweight physical-state helpers without loading proof engines.

Suite profiling removed repeated setup within individual inventory tests while
retaining fresh audits, mutation checks and independent output assertions.
Exhaustive research selections remain explicit validation work. The default
suite still includes production, source-authority and lifecycle regressions;
its watchdog and all positive F4/P0 assertions remain unchanged.

## Established results

The ownership migration preserves source authority and independent output checks.
Scoped typing, runtime, proof and packaging checks are recorded once below.
The [release gate table](../../release-status.md) owns the current cross-topic
release disposition; this topic does not duplicate that table.

## Rejected approaches

No diagnostics are suppressed, source roots excluded, or checks downgraded to
make the baseline green. Runtime handle authority is not replaced by annotations.
A generic constructor returning differently typed scheduler subclasses did not
provide sound static narrowing; operation-specific frames are replacing it.

Test-only historical dependency traversal helpers were removed. The current
source/ownership checker retains relative, absolute, alias and TYPE_CHECKING/else
coverage. The actual arithmetic and independent endpoint assertions remain.

The unused Antihydra `_runs`/`_run_steps` selector and its helper-only test were
removed after source-derived caller inspection. Production uses the punctured-step
selector; its independent output, source-authority and safety checks remain.

## Validation provenance

Development evidence at Git HEAD
`068827840bf80120b5bb6e8bd55cc202323466b8`, with pre-existing dirty work preserved.
Each receipt describes its tested working tree and selection, not acceptance of
this commit. Raw receipts remain in ignored `results/runs/` directories.

| Scope | Latest relevant receipt | Result and limits of claim |
| --- | --- | --- |
| Clean locked environment | `20261018T194706Z-8bc6691dce554af2826ce20f12337cb0` | Reproduced 16 locked packages; dependency consistency passed. |
| Whole-tree quality | `20261019T030413Z-04794486e19e486e9127bbfe33ad282a` | Strict mypy passed 2,317 sources; declared toolchain, dependency consistency, Ruff, formatting, source policy, documentation and proof inventory passed. The overall quality gate remains failed because Pyright is not clean. |
| Complete strict Pyright sweep | `20261019T030413Z-04794486e19e486e9127bbfe33ad282a` | 9,950 unique errors, down from the 14,946-error baseline. All 2,317 authored files covered in 93 serial batches of at most 25 files, with complete diagnostics and a 2-GiB Node heap cap. Largest sampled batch footprint: 598,091,208 bytes. |
| Causal authority and admission | `20261019T030355Z-29d5f582ef6b496d8cc1d14a807b1401` | 66 tests passed in 3.13 seconds, including changed-validator rejection, composite-sort enforcement, run invalidation and forged-token tests. |
| Shared carry and reverse refinement | `20261018T231229Z-6fe10baced854f8f91a914547826d9bb` | Three sessions rebuilt and passed; largest session took 278 seconds. |
| Decimal arithmetic extraction | `20261019T020716Z-3a94f3c875e94fdd9a04c83341e62b81` | Double_Reverse_Temporal_Refinement rebuilt in 90.4 seconds; unchanged shared dependency reused. No aggregate proof acceptance claimed. |
| Fresh wheel | `20261019T030413Z-04794486e19e486e9127bbfe33ad282a` | Fresh installed-wheel validation passed, including 40 family-first CLI cases, poisoned reconstruction checks and actual cross-seed and Mahler/Antihydra reuse. |
| Minimum Python wheel | `20261019T030923Z-d7c81b379bb745fb86446bd6810a9c1a` | The same wheel passed isolated Python 3.11.17 validation. |
| Complete default suite | `20261019T030950Z-e7be06380f2942d8bcb6e177bd614ca7` | 11,252 passed; one existing F4 concrete-resolution assertion failed. Pytest completed in 289.15 seconds, guarded wall time 291.70 seconds, peak footprint 850,379,928 bytes. No timeout or migration failure. |
| P0 release selection | `20261019T031450Z-dc7f1473375c49d3a5538a177de52d6f` | 61 passed, nine existing holds failed in 10.92 seconds: Antihydra source-7 non-halting, four candidate prime-bit decisions and their four CLI consumers. Reverse/add and Collatz passed. |
| Pending cutover quality | Comparison receipt `20261019T031650Z-1b0ecf53e363422b9adfe906e2d3f8cf`; baseline `20261019T031511Z-160d211458454520920f0374b2d639ca` | Ruff, formatting and strict mypy passed. Across 21 surviving affected Python files, the candidate has 113 Pyright diagnostics versus 128 on the baseline: zero added, 15 removed. Existing diagnostics remain failures. |
| Pending cutover behavior | Comparison receipt `20261019T031719Z-df1fcccafbce4aa095464aaf07e9e1fb` | 75 passed, including bounded-audit exhaustion tests; two positive public-global-authority assertions failed because the production release registry is empty. |
| Pending cutover source policy | Comparison receipt `20261019T031742Z-473dec6f82d54ec99bbb6686363e1249` | Whole-tree source policy passed, including line limits, recursion, duplicate bodies, ownership and validation entrypoints. |

The complete-suite timing record separates 13.74 seconds of collection, 7.41 of
setup, 259.04 of calls and 0.71 of teardown. Its slowest test took 3.75 seconds.
The 300-second suite and 60-second per-test limits were unchanged; cleanup was
confirmed and timing instrumentation completed normally.

Comparison checks used the candidate checkout's `src` before the editable main
installation. Synthetic admissions in mechanism tests do not establish kernel
acceptance. The two positive global-authority failures remain genuine gates;
the patch is unapplied and the live CLI retains forest admission. The developer
audit walker is bounded independently of the removed production fuel.

Earlier repaired import, fixture, typing and stale-wheel failures are superseded
by the corresponding checks above. Their raw diagnostics remain available;
repeating their old counts does not describe the remaining backlog.
Use the [central validation guide](../../development.md#reproducible-release-commands)
for current commands and limits.

## Remaining work

The under-10,000 Pyright tranche target is met. The strict gate still requires
eliminating the remaining diagnostics, and Pylance editor review remains open.
The complete default suite fits its deadline; its genuine F4 failure remains a
release hold. Unrelated mathematical and consumer obligations are tracked in the
[release gate table](../../release-status.md).

`2rev10` still lacks a term-owned published border-occurrence cursor for a
standalone `temporal.macro` request. Its exact typed occurrences are available
through explicit matrix traces. Advancing future children merely to manufacture
a macro summary would violate demand laziness; an always-unavailable registry
entry would not close that integration gap. Reverse/add's existing
`temporal.macro` remains its finite boundary-window certificate.
