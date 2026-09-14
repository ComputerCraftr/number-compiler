# Shared-action adversarial audit evidence

This is a read-only production/proof audit. No production or theory source was
changed. The audited authored-source fingerprint is
`95353e85f969895d8c6cc2bc9ab08c9dc7ac48d892bd323e8b798038853d1b24`, the same source
as the preceding frozen release validation. No new Isabelle build or full-unit
pass is claimed by this audit.

The consolidated findings and common proof dependency map are in
[the audit report](../../../docs/shared-action-adversarial-audit-2026-09-14.md).
Three independent read-only agents covered CLI slow paths, Isabelle objects,
and source/image/consumer invariants. The coordinator independently checked the
reported code paths and narrowed claims contradicted by the bounded controls.

`cli_trace.py` instruments actual `cli.main` calls, retaining original execution
and catching no internal refusal. It records common-core applications,
Antihydra arithmetic-owner count, validation calls, complete final counters,
exit codes and output packets. It is a call-count probe, not an installed-CLI
latency benchmark. The root coordinator ran it under 35 seconds / 1 GiB.

The final probe, `cli-trace-with-modular-controls.*`, completed in 2.221 seconds
with a sampled footprint of 41,075,144 bytes. Before/after source fingerprints
match. The initial `cli-trace.*` is retained; the second probe adds successful
modulus-three spacetime controls while retaining the default-budget refusals.

## CLI consumer connectivity

| Request | Common source-image core applications | Outcome |
|---|---:|---|
| prime nth 100, metrics | 1 prime application | Exact value 547 |
| 196 nth 4 | 0 | Term returned by existing executor |
| Collatz seed 27, nth 4 with clock | 0 | Existing physical consumer |
| Collatz seed 27, events 4 with modular | 0 | Existing event consumer |
| Fermat index 4, primality only | 0 | Exit 3, unresolved |
| Mersenne exponent 11, factor only | 0 | Existing conditional factor path |
| Antihydra clock/tape/Hasse controls | 0 | Existing physical/support consumers |
| Antihydra spacetime modulus 3, 64/128/256 returns | 1/2/4 | Shared-core bounded fragments |

Zero common-core applications do not mean zero computation. They identify the
remaining distinct execution owners. The probe does not assert these selected
calls exhaust every branch of a family.

## Antihydra validation amplification

Every request below has one arithmetic owner, no value rendering, and returns
success. The shared query owner does not eliminate repeated full validation.

| Information requested | Validation calls | Branch steps at n=64 | n=128 | n=256 |
|---|---:|---:|---:|---:|
| clock | 1 | 64 | 128 | 256 |
| clock twice | 1 | 64 | 128 | 256 |
| clock, tape | 6 | 384 | 768 | 1,536 |
| clock, tape, hasse | 15 | 960 | 1,920 | 3,840 |
| spacetime, modulus 3 | 3 | 192 | 384 | 768 |

`AntihydraArithmeticTerm._validate_result` reconstructs the canonical cylinder
for each retained segment, applies it again and checks the endpoint. Nested
`require_source` calls repeat that work. The source constructor's bounded
`admitted_arithmetic_cylinder` loops once per branch. Removing those checks
without replacement would regress existing mutation rejection; a repair must
preserve authenticated source/action authority, not cache a mutable “validated”
flag.

The successful spacetime controls visit exactly 64/128/256 leaf returns and
perform 7/14/28 chronological compositions respectively. The constructor is
still chunked into at most 64 returns; this is not arbitrary-size squaring.
With default modulus 257, the 128- and 256-return spacetime controls instead
refuse the unchanged work budget after 95 leaf returns. Those are recorded
refusals, not completed samples or zero-cost observations.

## Prime prefix-key and cache-eviction controls

`cache_trace.py` completed under its guard in 0.344 seconds, with matching
source fingerprints. These are instrumented counts, not timing comparisons.

| Actual prime CLI query, in order | Shared Φ reads | Prefix elements in read keys | Shared Φ writes | Prefix elements in write keys | Maximum key depth |
|---|---:|---:|---:|---:|---:|
| nth1000 after reset | 179 | 2,271 | 25 | 597 | 24 |
| nth1000 repeated | 28 | 668 | 1 | 23 | 24 |
| nth5000 extending that cache | 339 | 15,985 | 33 | 2,148 | 68 |
| nth5000 repeated | 40 | 2,624 | 0 | 0 | 68 |

All four queries return correct recorded values, 7,927 and 48,619. Each shared
access reconstructs its full prefix tuple in the current production owner;
local memo hits do not. This work is already charged. Immutable validation and
deep sizing occur before the process-cache lock, correcting an overly broad
initial agent claim about work under the lock.

A separate Antihydra capacity-64 engine control starts with one physical and
one arithmetic cylinder and inserts arithmetic residues 1–40 at width eight.
At residue 32, admission clears both memo tables: sizes `[1,32]` become `[0,1]`,
evicting 33 entries. Repeating the initial residue then performs eight arithmetic
and eight physical kernel branch steps. This demonstrates wholesale eviction
and rebuild at a supported small capacity; default-CLI saturation latency was
not measured in this audit.

## Owner-poison checks and rejected overclaims

`owner_poison.py` completed in 0.476 seconds. Its final evidence is
`owner-poison-constructor-controls.*`; the initial narrower check is retained.

| Poisoned method | CLI request | Result |
|---|---|---|
| Rich prime `PrimeSuccessorActionArena.__init__` | prime nth100 | Poison not invoked; value 547 |
| `HigherBimachineRuntime.point` | 196 nth4 | Poison not invoked; value 13,783 |
| `HigherBimachineRuntime.__init__` | 196 nth4 | Poison invoked; construction interrupted |
| `HigherBimachineRuntime.point` | 196 nth8, mirror only | Poison not invoked; mirror returned |

The mirror packet nevertheless records 88 higher action-continuation requests
and 290 higher concrete-operation evaluations. The verified dependency is on
higher construction/continuations. The proposed claim that every such CLI query
must invoke the `point` method was rejected by the audit.

The proof audit also preserves two scope corrections: the existing runtime
cylinder theory already imports and uses the common skew record, and the 196
publisher has a universal valid-list one-step theorem including growth. Neither
supplies temporal source-image construction. The M11 arbitrary-zero-key example
is not a counterexample to the intended terminal publisher or root-set
injectivity. No mathematical incompatibility of the parallel skew records was
demonstrated; their missing representation/refinement maps are the finding.

## Reproduction

From the repository root, run the probe with the development Python environment:

```bash
python results/current/shared-action-adversarial-audit-2026-09-14/cli_trace.py
python results/current/shared-action-adversarial-audit-2026-09-14/cache_trace.py
python results/current/shared-action-adversarial-audit-2026-09-14/owner_poison.py
```

The generated JSON/log files follow the repository's existing ignore policy.
The script and this report are reviewable sources. The prior growth manifest,
installed-wheel comparisons and P0 results remain in
[the frozen validation evidence](../skew-scheduler-unification-2026-09-13/README.md).
