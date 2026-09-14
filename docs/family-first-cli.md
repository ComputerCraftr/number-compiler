# Family-first CLI

The CLI uses `number-compiler FAMILY --nth N`. The former `nth`, `observe`,
`classify`, `verify-nonhalting` and `families` commands are removed. Python API
entry points retain their existing behavior; Antihydra arithmetic is added to
`NumberCompiler.project_nth`.

```sh
number-compiler --list-families
number-compiler antihydra --help
number-compiler 196 --nth 8
number-compiler collatz --nth 64 --seed 27
number-compiler antihydra --nth 64 --info ledger --info clock
number-compiler fermat --nth 5 --info primality --info factor --format json
number-compiler mersenne --nth 131 --no-value --info primality
number-compiler collatz --events 20 --seed 27 --info hensel
number-compiler antihydra --verify-nonhalting certificate.json
```

## Indices and parameters

| Family | `--nth N` | Parameters |
|---|---|---|
| `196` | N reverse/add iterations; zero is 196 by default | optional `--seed`, `--base` |
| `reverse-add` | N reverse/add iterations; zero is the seed | required `--seed`, optional `--base` |
| `collatz` | N ordinary physical iterations; zero is the seed | required `--seed`, optional `--radix` |
| `antihydra` | N arithmetic iterations; zero is 8 | none |
| `prime` | zero-based prime position starting at `--start` | optional `--start` |
| `fermat` | Fermat index N, starting at zero | none |
| `mersenne` | exponent N, starting at one | none |

Collatz `--events E` selects accelerated odd events from an odd seed, requires
`--info`, and has no ordinary term value. It is exclusive with `--nth`.
Certificate verification is exclusive with term selectors and observation
options. Explicit options belonging to another family or observation are errors.

## Output and observations

The default stdout contains only the exact digits. `--output-base B` selects a
base from 2 through 36. `--format symbolic` requests the existing symbolic term
description. Requested information is a JSON dictionary on stderr. Repeated
`--info` names are deduplicated and evaluated once.

`--format json` writes one stdout object with `family`, `index`, `index_unit`,
`output_base`, `value` and `info`; no information is written to stderr. The value
is a digit string, or null for information-only requests. `--no-value` requires
information and skips term rendering. Metrics describe work performed in this
query. Metrics bypass digit rendering; family-specific construction may still
be required (prime rank/select computes its selected endpoint).

| Selector | Information names |
|---|---|
| Every term family | `metrics` |
| Reverse/add and 196 | `mirror` |
| Collatz `--nth` | `clock` |
| Collatz `--events` | `clock`, `modular`, `twisted`, `hasse`, `hensel`, `tropical`, `factor` |
| Fermat/Mersenne | `primality`, `factor`, `root` (requires `--defect`) |
| Antihydra | `ledger`, `clock`, `modular`, `tape`, `twisted`, `spacetime`, `hasse`, `hensel`, `mahler`, `tropical`, `factor` |

Family help lists the applicable projection parameters. Primality and factor
discovery run only when explicitly requested. UNKNOWN remains unresolved;
there is no classical primality fallback. A conditional factor result may say
`not_found`; this says nothing about primality. Printed witnesses retain their
checked integer target and discovery accounting.

Exit codes are 0 for successful requests, 2 for invalid input or budget refusal,
3 for requested information with UNKNOWN or unavailable status, and 1 for a
rejected non-halting certificate. Certificate acceptance requires an actual
checked certificate; a finite trace cannot supply it.

## Antihydra arithmetic and physical observations

The arithmetic endpoint is the total sequence
`a(0) = 8`, `a(n+1) = a(n) + floor(a(n)/2)`. Its ledger adds 2 on even values of
`a`, and subtracts 1 on odd values. Arithmetic continues if this ledger becomes
negative. `ledger` and `modular` use the arithmetic owner without a physical
clock roof. Labels distinguish odd centered states `D = a - 1` from odd values
of `a`.

Physical observations use guarded execution after the eleven-step blank-tape
startup. If a requested target crosses a discovered halt, they report an
unavailable result with the actual halt boundary. Continued arithmetic does
not authorize a continued tape or physical clock.

Value and information share a query owner. Bounded arithmetic blocks retain
their chronological branch words; demanded physical roofs reuse those words.
This removes repeated branch discovery for the roof, but source discovery and
roof arithmetic still cost work and are charged. Spacetime and other projection
refinement obligations remain separately tracked.

The compatibility `run()` and `CylinderEngine.execute()` Python entry points
also use this owner. Physical results carry a charged issuance record so a
changed cached endpoint cannot be accepted by an observer. This record validates
an output; it does not select successors. Shared payload auditing independently
checks its source trajectory. Retention metrics count nodes and bounded records;
operand-bit counters are separate and are not presented as allocated bytes.

## Budgets and proof scope

`--max-output-bits` controls value output. Antihydra uses `--max-steps` for its
iteration limit, `--max-state-bits` for arithmetic state size, and
`--max-observer-terms` for projection work. Other observation limits retain their
existing units: `--max-events`, `--max-digits`, `--max-candidate-bits` and
`--max-factor-products` where applicable. These are admission limits, not a
promise of inexpensive arbitrary-size jumps.

`Antihydra_Family_Iteration.thy` proves total arithmetic iteration, its generated
parity-word skew action, ledger/minimum-prefix agreement and guarded agreement
before first failure. Its scope does not include the full Python powered
constructor, all literal-TM projections, or a source-7 non-halting barrier.
Existing P0 mathematical and performance assertions remain release gates.

## Prime rank/select resource limits

Prime queries use the shared descriptor-only Legendre count DAG for factor-stage
construction and rank descent. One query retains intermediate count states across
all ranks. It discovers the needed consecutive prime prefix through the exact
square-root boundary, then selects by counts down to a singleton. It does not
construct parent wheel gaps or a candidate bitmap.

```sh
number-compiler prime --nth 1000 --info metrics
number-compiler prime --nth 0 --start 10000 --max-prime-states 131072 \
  --max-prime-work 1000000 --max-prime-stages 4096
```

These positive prime-only limits default to 131,072 completed DAG states,
1,000,000 charged work steps, and 4,096 factor stages (including seed 2).
Refusal returns exit code 2 without a fallback. Work counts DAG-frame visits, factor appends and rank/discovery admission steps,
including reused memo states. Cache hits count reuse that avoids scheduling or
evaluating a state, not every backing-map read. Operand-bit work sums accounted
operand widths; neither counter is a timing or bit-operation bound. `prime_retained_entries` reports the states
and factors retained at query completion before disposal; the memo and factors
are released when selection returns. `prime_peak_pending_frames` reports local
traversal storage. Historical `prime_block_compilations` now counts finite window
rank queries; `prime_max_block_length` retains its odd-window units. The Python
selector's `leaf_length` argument remains an initial-window hint (default now 8);
final descent is to one candidate. The initial size uses 4 times the requested
rank, with exact doubling when necessary; it assumes no prime-density bound.

This finite production bridge does not establish cheap unbounded prime-stage
discovery or the unresolved cross-family terminal and powered-construction proofs.
