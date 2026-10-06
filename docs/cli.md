# CLI reference

Use `number-compiler FAMILY --nth N` for exact terms and demand information with repeated `--info NAME` options. `number-compiler --list-families` lists supported families; `FAMILY --help` lists applicable selectors and budgets. The public Python entry points are exported from `number_compiler`; the console entry point is `number_compiler.api.cli:main`. See the [metrics reference](metrics.md) for schema 8 accounting.

```sh
number-compiler --list-families
number-compiler antihydra --help
number-compiler 196 --nth 8
number-compiler collatz --nth 64 --seed 27
number-compiler antihydra --nth 64 --info ledger --info clock
number-compiler fermat --nth 5 --info primality --info factor --format json
number-compiler mersenne --nth 131 --no-value --info primality
number-compiler collatz --events 20 --seed 27 --info hensel
number-compiler collatz --events 20 --seed 27 --info safety --format json
number-compiler antihydra --verify-nonhalting certificate.json
```

## Indices and parameters

`--nth-power10 K` selects the exact index `10^K` for an integer `K ≥ 0`.
`K=0` selects index 1. It is mutually exclusive with `--nth`, `--events` and
certificate verification. `--max-index-bits` defaults to 1,000,000 and bounds
both explicit and power-of-ten indices before construction; invalid inputs or
exhausted budgets exit 2. No expression or floating-point parser is involved.
These selectors retain each family's index unit and do not imply cheap
execution at that horizon.

```sh
number-compiler collatz --seed 27 --nth-power10 6
number-compiler a367620 --nth-power10 8 --info metrics --format json
number-compiler fermat --nth-power10 3 --no-value --info metrics --format json
```

Compact queries present the coordinate as
`{"index": {"encoding": "power10", "exponent": 6}}` in JSON and information
packets. Diagnostics keep the coordinate compact; symbolic output uses `10^K`.
Ordinary `--nth` presentation is unchanged. Execution still receives an exact
binary integer. For example, `--nth-power10 6 --max-index-bits 19` refuses
before sequence construction: one million requires 20 bits.


| Family | `--nth N` | Parameters |
|---|---|---|
| `196` | N reverse/add iterations; zero is 196 by default | optional `--seed`, `--base` |
| `reverse-add` | N reverse/add iterations; zero is the seed | required `--seed`, optional `--base` |
| `collatz` | N ordinary physical iterations; zero is the seed | required `--seed`, optional `--radix` |
| `antihydra` | N macro-return coordinates after startup; zero is 8 | none |
| `prime` | zero-based prime position starting at `--start` | optional `--start` |
| `fermat` | Fermat index N, starting at zero | none |
| `mersenne` | exponent N, starting at one | none |
| `a367620` | OEIS index N, starting at one; checked-prefix admission required | none |

Collatz `--events E` selects accelerated odd events from an odd seed, requires
`--info`, and has no ordinary term value. It is exclusive with both term selectors.
Explicit `--radix`, `--output-base`, and `--max-output-bits` are rejected for
this selector because they configure a term output. Event help lists its own
information choices; `metrics` currently applies to term queries only.
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

Every CLI information packet carries `family`, `kind` (the requested info name),
`index`, `index_unit`, and `status`. Family-specific values and completion counts
remain separate: physical iterations and accelerated odd events are different
units. Antihydra uses `macro_returns_after_startup`; Collatz terms use
`physical_iterations` and event queries use `accelerated_odd_events`.

Work-counter inventories are emitted only through `--info metrics`. Schema 8
execution metrics use a read-only scalar-ledger snapshot after all requested
work. Reporting never invokes semantic audits or inventory callbacks:
`audit_complete` is false and `accounting_mismatch` is null. The `reporting`
lane records counter extraction size separately from execution work; it does
not measure dataclass-to-dictionary conversion or JSON serialization. Explicit
Python audited metrics remain available.
Families without a live execution ledger report null execution metrics rather
than invented zero work.

The following capability table is generated from the CLI registry. `root` requires `--defect`; reverse/add and Collatz seed requirements are described above.

<!-- cli-capabilities:start -->
| Family | Index unit | Parameters | Term information | Event information |
| --- | --- | --- | --- | --- |
| `a367620` | `oeis_index` | — | `metrics`, `clock`, `tropical`, `certificate` | — |
| `reverse-add` | `iterations` | `--seed`, `--base` | `metrics`, `mirror` | — |
| `196` | `iterations` | `--seed`, `--base` | `metrics`, `mirror` | — |
| `collatz` | `physical_iterations` | `--seed`, `--radix` | `metrics`, `clock` | `clock`, `modular`, `twisted`, `hasse`, `hensel`, `tropical`, `factor`, `safety` |
| `prime` | `prime_index` | `--start` | `metrics` | — |
| `fermat` | `fermat_index` | — | `metrics`, `primality`, `factor`, `root` | — |
| `mersenne` | `mersenne_exponent` | — | `metrics`, `primality`, `factor`, `root` | — |
| `antihydra` | `macro_returns_after_startup` | — | `metrics`, `ledger`, `clock`, `modular`, `tape`, `twisted`, `spacetime`, `hasse`, `hensel`, `mahler`, `tropical`, `factor` | — |
<!-- cli-capabilities:end -->

Family help lists the applicable projection parameters. Primality and factor
discovery run only when explicitly requested. UNKNOWN remains unresolved;
there is no classical primality fallback. A conditional factor result may say
`not_found` for a decided composite; this says nothing about primality.
An undecided special-number factor query reports `unknown` and exits 3.
Printed witnesses retain their
checked integer target and discovery accounting.

Collatz `safety` asks whether any event in the admitted finite prefix fell
strictly below the starting seed. Its exact affine endpoint, Hensel cylinder
and normalized inverse-threshold envelope are included. Events stop at one,
as for the other event observations. A false result only describes this
prefix; it is not a claim about the infinite trajectory. Safety reuses event
discovery, but its demanded threshold construction still costs work.

Exit codes are 0 for successful requests, 2 for invalid input or budget refusal,
3 for requested information with UNKNOWN or unavailable status, and 1 for a
rejected non-halting certificate. Certificate acceptance requires an actual
checked certificate; a finite trace cannot supply it.

## Decimal reverse/add availability

Decimal reverse/add uses an authenticated decimal pair-output owner when the
same-carry clause does not apply. For example, `number-compiler 196 --nth 20`
emits `70446464506`. The old decimal 128-iteration cap is removed; requests still
obey their resource budgets. Length-only queries can retain a scalar successor
summary without constructing the output grammar. This remains a sequential cold
constructor, and its availability does not close the powered-construction or
performance gates. Nondecimal fallback limits are unchanged.

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

`--max-output-bits` controls value output and defaults to 1,000,000.
Antihydra's `--max-steps` and `--max-state-bits` default to 4,096;
`--max-observer-terms` defaults to 1,000,000 projection operations.
Applicable observation defaults remain 4,096 for `--max-events` and
`--max-digits`, 1,000,000 for `--max-candidate-bits`, and 4,096 for
`--max-factor-products`. Index admission has its separate `--max-index-bits`
limit described above. These are admission limits, not a
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

## A367620 prefix admission

`number-compiler a367620 --nth N` uses fixed source 20 and decimal comma-child
semantics. It rejects `--seed`, `--base`, `--radix`, `--start` and `--events`.
Construction budgets are `--max-comma-states` (131,072) and `--max-comma-work`
(1,000,000); stricter resource limits still apply.

The runtime-verified prefix covers indices **1 through 412987860**, including
the first certified fork choice. The last admitted value is `19999999999`.
Later indices return exit 3: JSON contains `value: null` and an
`unresolved_sequence_boundary` error; text reports the boundary on stderr.
The full Isabelle certificate-instance proof remains a release obligation.

```sh
number-compiler a367620 --nth 1
number-compiler a367620 --nth 20000 --info clock
number-compiler a367620 --nth 412987860 --info certificate --format json
number-compiler a367620 --nth 20000 --no-value --info certificate --info metrics --format json
```

The certificate packet distinguishes `runtime_verified` from
`isabelle_instance_checked`. Verification streams complete finite regions;
the published OEIS choice bits are not runtime branch oracles. `--info metrics`
alone never initiates certificate verification or arithmetic. Metrics remain
read-only schema 8.
Its shared `family_work` rows report `punctured_event_actions` (completed
source events) and `punctured_event_symbols` (transitions represented by those
events). They remain null when uninstrumented. These counters do not imply
source discovery was skipped or that anonymous harmonic fibers determine a
successor.
Its `comma` lane distinguishes published transitions from evaluated image work,
phase cycles, transfer constructions and phase-fold terms. Work budgets charge
ten conservative slots per transfer; operand widths include phase-fold bounds,
composition inputs and arbitrary-precision step counts. These are charged
work units, not measured CPU instructions or a bit-complexity theorem. Missing
counters are null. Exact width is null until a width demand has a certified result; it is
not replaced by a bit upper bound. See the [mathematics](research/comma.md).

Certificate work counts record parsing/checking, guarded-cycle checks and
bounded child classifications. One such classification tests all nine possible
leading digits; `certificate_candidate_digit_trials` reports these scalar
trials separately. The work cap is not a cap on individual candidate trials.
Verification markers use the existing bounded process cache, while bypassed
queries retain only their own ledger-owned admission marker. Repeated demands
still hash the immutable compressed certificate; those bytes are charged.

### Homogeneous growth projections

Collatz's requested `clock` value includes `homogeneous_growth`, with exact
`growths=H`, `halvings=D`, `radix=10` and
`homogeneous_radix_order=floor(H log10(3) - D log10(2))`.
Antihydra's requested `mahler` associated action uses the same fields with
`H=D=R`, derived from its admitted return extent. This is the homogeneous
multiplier's radix order, not the endpoint's digit width or a safety result;
source offsets, caps and existing clock meanings remain separate.
These projections use certified rational bounds, and a precision/work refusal
never returns an approximate result. Digit-only and metrics-only queries do
not request them. There is no growth-word selector.

The physical Collatz `clock` packet also includes `width_tape`. When the
admitted run or exact cycle already supplies its width walk, this reports
binary (`radix=2`) source/target widths and the relative displacement and
prefix extrema in `blank`. It is `null` when an applied macro has no retained
width-walk certificate. Reading it never starts another trajectory or tape
compiler. It is not a complete carry tape or a decimal-width projection.
