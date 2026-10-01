# Linear bisimulation checkpoint release

Historical checkpoint: names and results below describe the recorded source.
For current runtime test owners and audit commands, see
[development guidance](../../development.md#reproducible-release-commands).

Status: **checkpoint implementation complete; higher-rung logarithmic HashLife closure remains open**.

This checkpoint removes the release-blocking sequential family/radix replay paths from the bounded production route without restoring exact future trees or provider-history carriers.

## Production execution

- Decimal reverse/add uses the SHA-verified minimized `T^2` bimachine (`757` LEFT + `179` RIGHT classes) as the verified bounded temporal rung. A generation-N query applies repeated `T^2` rungs, an optional one-step residual, and the terminal normalizer.
- Physical Collatz uses the SHA-verified minimized `C^4` bimachine (`50` LEFT + `90` RIGHT classes), followed by at most three primitive physical residual steps.
- The compiled `ActionProgramID` remains the semantic identity of the requested power. The checkpoint executor owns no second application-program DAG and no generation/event program list.
- The exact working word exists only as a transient list of <=64-bit microblocks under the fixed 256-byte aggregate transient cap. It is updated in place. Intermediate words are not retained.
- Only final observation blocks may enter the shared `MicroblockCache` (64 encoded bits/block, <=1024 entries, <=8 KiB payload/index).
- Wider/unadmitted sources fall back to the shared quotient diamond executor. There is no sequential-family fallback.

## Removed/rejected carriers

Production family routing does not instantiate `LazyReverseApplication` or `LazyCollatzApplication`. The recursive radix point/range replay backend is absent. The rejected provider-layer `_block_spacetime_runtime` experiment was removed from this checkpoint and the last validated generic fused runtime restored.

Reference/proof modules may still contain old algorithms for independent exact comparison. They are not selected by `_bounded_temporal_application` or the public powered family path.

## Frozen N=16..256 gate

Machine-rung applications are exactly:

| N | reverse/add 196 | Collatz 140137 |
|---:|---:|---:|
| 16 | 9 | 4 |
| 32 | 17 | 8 |
| 64 | 33 | 16 |
| 128 | 65 | 32 |
| 256 | 129 | 64 |

For every row: sequential-generation advances = 0, spatial occurrence-history bindings = 0, forbidden future payloads = 0, representation boundary complete = 1, and temporal cutover complete = 1.

Machine-readable evidence: `results/linear_bisimulation_checkpoint_v1.json`.

## What this checkpoint does not claim

The checkpoint restores a **linear temporal-machine floor**, not final logarithmic HashLife. Each low-power rung still scans the bounded working word, so total symbol visits are not claimed linear or logarithmic in N. The next phase is to construct higher powered family bisimulation machines via:

`compose powered machine -> refine by complete output + successor behavior -> publish canonical parent machine`.

The reverse initial partition should use the proven bounded mod-32/H=20 live-forcing interface plus complete two-sided output/growth/halo behavior. The Collatz initial partition should use the bounded 3-adic/frame observer plus affine/root-germ, valuation/cocycle, output and extent behavior. A higher rung is admitted only if minimization closes inside the fixed resource gate; otherwise execution remains on the largest lower verified rung. No provider-history or exact-tape fallback is permitted.

## Required validation

The dedicated `tests/test_linear_bisimulation_checkpoint.py` poisons the retired sequential family methods, checks exact T²/C⁴ rung counts, verifies the former seed-140137/step-11/radix-3 timeout path, checks capped transient storage, and verifies warm-point no-replay.

Final validation on this checkpoint tree: full pytest **2,862/2,862 passing** in 480.11 s; the focused checkpoint/representation/accounting batch is **275/275 passing** in 24.23 s; repository structural checks are **67/67 passing**. The former C4 fourth RIGHT16 35-second profile gate passes unchanged. Ruff and strict mypy were not installed and could not be fetched in this execution environment, so their earlier checkpoint passes are not relabeled as fresh final-tree runs.
