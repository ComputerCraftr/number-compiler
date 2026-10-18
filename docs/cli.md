# CLI reference

Use `number-compiler FAMILY --nth N` for exact terms and demand information with repeated `--info NAME` options. `number-compiler --list-families` lists supported families; `FAMILY --help` lists applicable selectors and budgets. The public Python entry points are exported from `number_compiler`; the console entry point is `number_compiler.api.cli:main`. See the [metrics reference](metrics.md) for schema 8 accounting.

```sh
number-compiler --list-families
number-compiler antihydra --help
number-compiler reverse-add --seed 196 --nth 8
number-compiler 2rev10 --seed 10 --nth 1
number-compiler collatz --nth 64 --seed 27
number-compiler antihydra --nth 64 --info safety.ledger --info temporal.clock
number-compiler fermat --nth 5 --info number-theory.primality --info number-theory.factor --format json
number-compiler mersenne --nth 131 --no-value --info number-theory.primality
number-compiler collatz --events 20 --seed 27 --info arithmetic.hensel
number-compiler collatz --events 20 --seed 27 --info safety.execution --format json
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


Reverse/add, double-reversal and Collatz count iterations from the supplied
source at index zero. Antihydra counts macro returns after startup, starting at 8.
Prime queries use zero-based positions at or above `--start`; Fermat uses its
zero-based sequence index, Mersenne uses a positive exponent, and A367620 uses
positive OEIS indices with checked-prefix admission. The generated capability
table below owns the supported source parameters and observations.

`2rev10` uses `U(n) = 2 * reverse10(n)`, including decimal normalization: `10 → 2`. Its decimal grammar is applied through the shared scheduler. Admitted four-phase boundary cylinders use temporal HashLife composition of the exact two-step cellular rule; other source regions retain charged exact transitions. `--max-steps` and `--max-state-bits` both default to 4096. It accepts `--info metrics`, `--info temporal.closed-form`, `--info spatial.stencil`, `--info temporal.bank`, `--info spatial.pair-bank` and `--info temporal.grammar`, output formats and output bases, but no input base, radix or event selector. The demanded closed-form packet reports source-bound carry and moment ports from the completed endpoint; `--temporal-closed-form-modulus M` projects them modulo a positive integer. Modular output does not authorize an approximate branch or phase decision. Metrics alone never constructs these ports. `--info spatial.stencil --spatial-stencil-position P` demands one LSD-indexed digit from an admitted temporal cylinder. `--info temporal.bank` reports the admitted border’s forced growth/carry word and separately labeled bounds for conditional observers. Both share bounded, charged entry discovery; neither renders the full endpoint. A source without a certified entry returns an unavailable observation (exit 3), rather than guessing a digit or treating a bound as exact. The `pair-bank` observation uses a final outer-to-inner pair coordinate. The `temporal-grammar` observation uses an entry-source coordinate and `--temporal-grammar-period` (1–8) to certify both finite causal halos before publishing a repeated motif. Their coordinate units are explicit in JSON. A `closed-form` request retains original-source fields and separately reports an admitted transient prefix and affine suffix; the suffix shift is endpoint-derived, not a new predictive source certificate.

`temporal.carry-safety` on `2rev10` reports the source-derived three-cell
carry constraints and conditional component bounds. It does not construct the
full border graph or authorize repeating an entire source from a compatible
border trace. The source width change includes trailing-zero contraction.
Summary and metrics requests do not demand this analysis.

For `2rev10`, `arithmetic.radix25-shift` projects the original decimal
source through its exact radix-2/5 shift and carry correction.
`temporal.radix-walsh` demands a source-certified finite temporal bank and its
64-lane Walsh/F5 projection. Use `--arithmetic-radix-places`,
`--temporal-walsh-start`, and the shared `--temporal-grammar-position` and
`--temporal-grammar-period` options. Conditional borrow-ingress responses are
not a global innovation tape. The ordinary value route does not demand these
spectral projections.

```sh
number-compiler 2rev10 --seed 196 --nth 0 --no-value --info arithmetic.radix25-shift --arithmetic-radix-places 8 --format json
```

Both decimal reversal families support `--info temporal.residue99` without
rendering an endpoint. Reverse/add predicts modulo 99; the certified 2rev10
width clock predicts modulo 99 and 198. These scalar projections do not select
future carry banks or authorize a full digit word.

`reverse-add --info temporal.seed-orbit` reads the completed scheduler endpoint
and its correlated center/carry ports for indices 2 through 4097. Width and
digit consumers share that occurrence; this observation does not replay the
trajectory. Its measured Q19 block count does not imply logarithmic temporal
construction. `2rev10 --info temporal.seed-morphism` publishes the exact source
entry and powered endpoint. Optional `--temporal-period-samples` requests a
bounded center-window scan, controlled by `--temporal-period-stride`,
`--temporal-period-depth` and `--temporal-period-max-lag`. The default sample
count is zero. Finite matching windows never certify an infinite period.

```sh
number-compiler reverse-add --seed 196 --nth 64 --no-value --info temporal.seed-orbit --format json
number-compiler 2rev10 --seed 196 --nth 128 --no-value --info temporal.seed-morphism --format json
```

`--info spatial.bank-morphism` emits a compressed output for an authenticated
protected source region. Use `--spatial-pair-bank-position`,
`--spatial-bank-morphism-count` and `--temporal-grammar-period`. For reverse/add,
the pair position is LSD-first; for 2rev10 it is the final outer-to-inner pair
position, including the accumulated border displacement. Unsupported source
halos refuse rather than inferring periodicity from a band mask. Reverse/add also
reports a bounded `inward_harmonic_bank`: five must/may masks for one
source-admitted successor. Unresolved reflected carries remain conditional;
this packet does not certify repeated future forcing.

For 2rev10, `spatial.bank-window` instead reads an exact finite window of at most
64 final pairs. It does not claim temporal pumping or build the full target.

```sh
number-compiler reverse-add --seed 196 --nth-power10 12 --no-value --info temporal.residue99 --format json
number-compiler 2rev10 --seed 196 --nth 64 --no-value --info spatial.bank-window --spatial-pair-bank-position 0 --spatial-bank-morphism-count 14 --format json
```

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
`--info` names are deduplicated and evaluated once. `--info temporal` is a
snapshot-only summary: it reports the requested clock and already-published
projection metadata, and lists supported temporal details without activating
them. Detailed packets use namespaced IDs such as `temporal.clock`,
`spatial.stencil`, and `arithmetic.hensel`.

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

The following capability table is generated from the CLI registry. `number-theory.root` requires `--defect`; reverse/add and Collatz seed requirements are described above.

`--info temporal.open-ring` demands a finite source-owned inward bank for
`reverse-add` or an open-inlet bank for `2rev10`. Use
`--spatial-pair-bank-position` and `--spatial-bank-morphism-count` to select
its pair window. For `2rev10`, `--temporal-open-ring-lookback` selects 1–32
certified two-step transitions (default 8). Packets explicitly distinguish
finite source admission from unbounded repetition; an unclosed inlet cannot
supply a future periodicity claim. Metrics and ordinary digit output do not
automatically demand this observation.

`--info temporal.matrix --temporal-matrix-steps N` requests a finite
source-guarded transfer beginning at the selected term. `N` counts physical
recurrence ticks, independently of the family's main query index unit. Pair
transfers use `--temporal-matrix-pair-depth`. Packets explicitly identify pair
coordinate order: reverse/add uses lower/LSD then upper/MSD; `2rev10` uses
upper/MSD then lower/LSD. Reverse/add admits depths 1–12; `2rev10` admits
1–16 and chooses bounded windows that fit its 18-pair causal halo. `2rev10`
requires an even horizon because one internal paired action spans two physical
ticks. Fermat carry transfers use `--temporal-matrix-digit-position`; their
horizon counts ordinary tripling ticks on the selected terminal source, not
successive Fermat indices. The Mahler center is selected from its source width. Coordinate kinds and admitted limits are declared by the family
registry; two equally sized matrices need not have the same state space.

The matrix is published directly under `info["temporal.matrix"]`, separately
from `temporal.macro` and `arithmetic.mahler`. Its finite source and conditional
relation are distinguished, and the packet itself conveys no execution or
infinite-repetition authority. Ordinary output, temporal summaries and metrics
never request these detailed matrix observations.

`fermat --info number-theory.primality --ordered-carry-windows` adds fixed,
ordered carry samples from the terminal physical-tripling source for Fermat
indices 0–16. It uses bounded radix residues and source periods, without
materializing the power of three or enumerating its period. This is an optional
arithmetic projection: it does not certify the full square-carry cochain or
change an unresolved primality result. Ordinary primality queries omit it.

`2rev10 --info temporal.birth-layers` follows the canonical moving boundary
through a finite source-issued suffix. `--spatial-bank-morphism-count` selects
1–16 retained pairs and `--temporal-open-ring-lookback` selects at most 160
F-steps for this demand. Reported return periods describe the conditional inlet
model; they do not extend the source certificate beyond its checked horizon.
The ordinary `temporal.open-ring` demand retains its 32-F-step limit.

<!-- cli-capabilities:start -->
| Family | Index unit | Parameters | Term information | Event information |
| --- | --- | --- | --- | --- |
| `reverse-add` | `iterations` | `--seed`, `--base` | `temporal`, `metrics`, `spatial.mirror`, `temporal.macro`, `temporal.matrix`, `temporal.residue99`, `temporal.open-ring`, `temporal.seed-orbit`, `temporal.stencil`, `spatial.bank-morphism` | — |
| `2rev10` | `iterations` | `--seed` | `temporal`, `metrics`, `temporal.matrix`, `temporal.closed-form`, `temporal.residue99`, `temporal.seed-morphism`, `temporal.carry-safety`, `spatial.stencil`, `temporal.bank`, `temporal.open-ring`, `temporal.birth-layers`, `spatial.pair-bank`, `spatial.bank-morphism`, `spatial.bank-window`, `temporal.grammar`, `temporal.radix-walsh`, `arithmetic.radix25-shift` | — |
| `collatz` | `physical_iterations` | `--seed`, `--radix` | `temporal`, `metrics`, `temporal.matrix`, `temporal.clock`, `temporal.accumulator`, `temporal.macro`, `temporal.innovation-borrow` | `temporal`, `temporal.clock`, `arithmetic.modular`, `arithmetic.twisted`, `arithmetic.hasse`, `arithmetic.hensel`, `arithmetic.tropical`, `arithmetic.factor`, `safety.execution` |
| `antihydra` | `macro_returns_after_startup` | — | `temporal`, `metrics`, `temporal.matrix`, `safety.ledger`, `temporal.clock`, `arithmetic.modular`, `spatial.tape`, `arithmetic.twisted`, `temporal.spacetime`, `arithmetic.hasse`, `arithmetic.hensel`, `arithmetic.mahler`, `arithmetic.tropical`, `arithmetic.factor` | — |
| `a367620` | `oeis_index` | — | `temporal`, `metrics`, `temporal.clock`, `arithmetic.tropical`, `safety.certificate` | — |
| `prime` | `prime_index` | `--start` | `metrics` | — |
| `fermat` | `fermat_index` | — | `temporal`, `metrics`, `temporal.matrix`, `number-theory.primality`, `number-theory.factor`, `number-theory.root` | — |
| `mersenne` | `mersenne_exponent` | — | `metrics`, `number-theory.primality`, `number-theory.factor`, `number-theory.root` | — |
<!-- cli-capabilities:end -->

Family help lists the applicable projection parameters. Primality and factor
discovery run only when explicitly requested. UNKNOWN remains unresolved;
there is no classical primality fallback. A conditional factor result may say
`not_found` for a decided composite; this says nothing about primality.
An undecided special-number factor query reports `unknown` and exits 3.
Printed witnesses retain their
checked integer target and discovery accounting.

Collatz `safety.execution` asks whether any event in the admitted finite prefix fell
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

Decimal reverse/add uses the scheduler's authenticated Q19 pair-output owner.
For example, `number-compiler reverse-add --seed 196 --nth 20` emits
`70446464506`. Length, point and streamed output share its completed occurrence;
length reads the admitted extent without rendering digits or replaying a
separate carry history. Metrics-only requests leave that construction lazy.

The scheduler applies bounded T2/T4 pair blocks and composes larger requests
from completed children. The old decimal 128-iteration cap is removed; resource
budgets still apply. This does not establish an unrestricted temporal quotient,
a subquadratic cold-construction bound or cross-request reverse cache savings.
Nondecimal fallback limits are unchanged. Guarded homogeneous/alternating
interior formulas alone do not authorize a whole-integer endpoint.

`--info temporal.matrix --temporal-matrix-kind innovation` reports endpoint-consistent innovation moments from
the completed decimal occurrence. With `--temporal-matrix-modulus M`, it folds the output
grammar modulo M without constructing the exact endpoint integer.
`--info temporal.stencil` explicitly requests the bounded five-band carry and
signed-borrow diagnostic, subject to `--max-digits` and `--max-output-bits`.
These observations do not authorize repeating a conditional source action.
Neither runs for an ordinary value or metrics-only request.

```sh
number-compiler reverse-add --seed 196 --nth 20 --no-value --info temporal.matrix --temporal-matrix-kind innovation --temporal-matrix-modulus 1009 --format json
```

## Antihydra arithmetic and physical observations

The arithmetic endpoint is the total sequence
`a(0) = 8`, `a(n+1) = a(n) + floor(a(n)/2)`. Its ledger adds 2 on even values of
`a`, and subtracts 1 on odd values. Arithmetic continues if this ledger becomes
negative. `safety.ledger` and `arithmetic.modular` use the arithmetic owner without a physical
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
Applicable observation defaults remain 4,096 for the event-selector
`--max-events`, the clock-specific `--temporal-clock-max-events` and
`--temporal-clock-max-digits`, and reverse/add's `--max-digits`; 1,000,000 for
`--max-candidate-bits`; and 4,096 for `--max-factor-products`. Index admission has its separate `--max-index-bits`
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
number-compiler a367620 --nth 20000 --info temporal.clock
number-compiler a367620 --nth 412987860 --info safety.certificate --format json
number-compiler a367620 --nth 20000 --no-value --info safety.certificate --info metrics --format json
```

The safety.certificate packet distinguishes `runtime_verified` from
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

Collatz's requested `temporal.clock` value includes `homogeneous_growth`, with exact
`growths=H`, `halvings=D`, `radix=10` and
`homogeneous_radix_order=floor(H log10(3) - D log10(2))`.
Antihydra's requested `arithmetic.mahler` associated action uses the same fields with
`H=D=R`, derived from its admitted return extent. This is the homogeneous
multiplier's radix order, not the endpoint's digit width or a safety result;
source offsets, caps and existing clock meanings remain separate.
These projections use certified rational bounds, and a precision/work refusal
never returns an approximate result. Digit-only and metrics-only queries do
not request them. There is no growth-word selector.

The physical Collatz `temporal.clock` packet also includes `width_tape`. When the
admitted run or exact cycle already supplies its width walk, this reports
binary (`radix=2`) source/target widths and the relative displacement and
prefix extrema in `blank`. It is `null` when an applied macro has no retained
width-walk certificate. Reading it never starts another trajectory or tape
compiler. It is not a complete carry tape or a decimal-width projection.


### Reverse boundary certificates

Decimal `reverse-add` accepts `--info temporal.macro`. With
`--no-value`, this requests only a source-bound boundary certificate: unanimous
width and edge digits across all admitted unknown-interior carry branches.
It never certifies the complete future integer. Window precision is tried at
2, 4 and 8 digits under bounded construction resources; an unsupported narrow
source or ambiguous continuation reports `unavailable` with exit 3.

Value output and `temporal.macro` may be requested together. Both use the same
admitted source workspace and carry-prefix summaries; the observer does not
decode the source or scan its interior again. Its future relation still retains
both possible unknown carries, so it does not authorize full-integer jumps.

```bash
number-compiler reverse-add --seed 10001 --nth 1 --no-value --info temporal.macro --format json
```

Nondecimal `--base` is rejected for this observer. A double-reverse operation
is available to the finite-window arithmetic tests; it is not registered as a
new public sequence family.


### Collatz accumulator action

`collatz --info temporal.accumulator --temporal-accumulator-modulus M` requests the residue of the original
source plus its completed **normalized** successors. An odd normalized step
includes its forced division; it consumes two physical ticks. An unmatched
final odd physical tick is reported by the pending phase and is not added as
a normalized successor. The selected `--nth` index remains physical time.
The modulus defaults to 257. This observer uses the same admitted root image
as a requested value and is not constructed for ordinary value/clock queries.

```bash
number-compiler collatz --seed 27 --nth 16 --no-value --info temporal.accumulator --temporal-accumulator-modulus 49 --format json
```

Joint affine coefficients are budgeted even when only a modular output is
requested. This does not promise cheap arbitrary-horizon accumulator queries
or use a bounded Moore observation class as an endpoint cache key.

### Collatz guarded innovation observations

`collatz --info temporal.macro` reports the first guarded boundary macro
actually executed by the source-image constructor. `--info temporal.innovation-borrow`
requests the signed normalized second-innovation tape for the requested prefix at an odd
modulus between 3 and 4096 (default 257). It also reports bounded radix-6 and
radix-10 position spectra when the admitted return supports them. These
spectra describe certified return sources, not a prediction of an unknown
parity itinerary. Both may accompany a value request.

```bash
number-compiler collatz --seed 2174 --nth 13 --no-value --info temporal.innovation-borrow --temporal-innovation-borrow-modulus 49 --format json
```

The tape is selected from the authenticated run grammar, including admitted
mixed-word repetitions and exact cycles. Its finite input-driven Moore machine
keeps both possible next parity inputs; the arithmetic producer supplies the
actual input. Signed, borrow-punctured and carry-punctured machines are separate
observation quotients. They do not establish an autonomous finite quotient of
all future Collatz branches. Physical ticks, completed normalized steps and a
pending odd half-step remain separate.
These information requests do not demand the whole chronological accumulator;
add `--info temporal.accumulator` when that output is needed. Ordinary value requests
do not construct the modular Moore observer.

Finite-horizon Moore IDs authorize reuse of the declared output word only at
that horizon. They do not identify endpoint or width actions. Guarded arithmetic
macros separately authenticate their source cylinder and physical duration.

The `6305R` packet distinguishes macro-wide `physical_ticks` and
`normalized_symbols` from `return_physical_ticks` and
`return_normalized_steps`. The latter arrays exclude entry and exit transfers:
a return with zero tail `j` consumes `j+4` physical ticks and `j+2` normalized
steps. Guarded `0563` and `26847` actions likewise include the final division
needed to complete their normalized boundary. Shorter requests retain their
exact physical endpoint instead of rounding up to a macro boundary.


## Typed Python queries

Use `NumberCompiler.project(query)` for lazy projection, `nth(query, max_bits=...)`
for bounded integer output, and `project_digit(query, coordinate)` for a single
radix digit. Coordinates follow the selected family's existing radix convention.
The exported frozen query records carry only execution parameters; event and
certificate-verification requests are separate variants. Optional observations
and compact-index presentation do not become mathematical query coordinates.

```python
from number_compiler import CollatzTermQuery, NumberCompiler

compiler = NumberCompiler()
query = CollatzTermQuery(8, seed=27, radix=2)
assert compiler.nth(query) == 71
assert compiler.project_digit(query, 0) == 1
```

The family registry supplies parser options, capability documentation and lazy
execution/observation adapters. Help does not import family engines. Query
constructors reject invalid external integers, including Booleans; cache admission
still checks source, generation, budget and consumer authority. JSON serialization
copies demanded packets, preserves null measurements and encodes oversized integers
exactly. Compact indices replace only explicitly declared index fields.
