# CLI reference

Use `number-compiler FAMILY --nth N` for exact terms and demand information with repeated `--info NAME` options. `number-compiler --list-families` lists supported families; `FAMILY --help` lists applicable selectors and budgets. The public Python entry points are exported from `number_compiler`; the console entry point is `number_compiler.api.cli:main`. See the [metrics reference](metrics.md) for schema 8 accounting.

```sh
number-compiler --list-families
number-compiler antihydra --help
number-compiler reverse-add --seed 196 --nth 8
number-compiler reverse-add --seed 89 --first-palindrome-within 24 --format json
number-compiler 2rev10 --seed 10 --nth 1
number-compiler 5rev10 --seed 196 --nth 2
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
`K=0` selects index 1. It is mutually exclusive with `--nth`, `--events`,
`--first-palindrome-within` and certificate verification. `--max-index-bits` defaults to 1,000,000 and bounds
both explicit and power-of-ten indices before construction; invalid inputs or
exhausted budgets exit 2. No expression or floating-point parser is involved.
These selectors retain each family's index unit and do not imply cheap
execution at that horizon.

```sh
number-compiler collatz --seed 27 --nth-power10 6
number-compiler a367620 --nth-power10 8 --info metrics --format json
number-compiler fermat --nth-power10 3 --no-value --info metrics --format json
```

For decimal `reverse-add` and `2rev10`, `--first-palindrome-within N` searches
physical generations 1 through N, inclusively. The seed is generation zero.
A successful value is the earliest generation, or `none` if the entire interval
has been excluded. JSON reports `first_generation` and `searched_through`
under `info["first-palindrome-within"]`. At horizon zero these are `null` and
`0`. Reverse/add can certify a bounded prefix of up to 4,096 physical steps per search.
An earlier hit answers a longer request. When a longer interval remains open,
JSON reports the last covered generation in the unresolved result. Double
reverse uses its source and step budgets. A budget refusal has a nonzero exit
status. Ordinary term and digit
requests incur no event search.

Compact queries present the coordinate as
`{"index": {"encoding": "power10", "exponent": 6}}` in JSON and information
packets. Diagnostics keep the coordinate compact; symbolic output uses `10^K`.
Ordinary `--nth` presentation is unchanged. Execution still receives an exact
binary integer. For example, `--nth-power10 6 --max-index-bits 19` refuses
before sequence construction: one million requires 20 bits.


Reverse/add, double-reversal, five-reversal and Collatz count iterations from the supplied
source at index zero. Antihydra counts macro returns after startup, starting at 8.
Prime queries use zero-based positions at or above `--start`; Fermat uses its
zero-based sequence index, Mersenne uses a positive exponent, and A367620 uses
positive OEIS indices with global-provider admission. The generated capability
table below owns the supported source parameters and observations.

`5rev10` uses `x(0) = seed` and `x(n+1) = 5 * reverse10(x(n))` for a nonnegative
seed. It preserves decimal normalization, for example `120 → 105`.
Exact bounded execution defaults to 4,096 physical steps and 4,096 state bits.
For wide sources and long bounded requests, the endpoint publisher can use
overlapping padded digit cones. Eligible spans of at least 1,024 steps on
uncapped ledgers can use a packed two-step action from the authenticated
receiving value. Each physical intermediate is checked against the state-bit
budget. The execution preserves zero trimming and both generation parities.
`arithmetic.modular` projects the all-source mod-45 clock without constructing
the full term; its modulus must divide 45. A finite source certificate does not
authorize repeating a border cycle beyond that certificate's horizon.

`5rev10 --info arithmetic.modular --arithmetic-modular-kind digit-field` reports the variable-width concatenation
of the blocks `decimal(5*d)` modulo \(9\cdot5^k\).
`--arithmetic-modular-places k` defaults to 2, which uses the universal
mod-225 action without constructing a physical term. Higher precision reads
a bounded physical suffix. `temporal.closed-form` reports the unnormalized
reflected H action at `--temporal-closed-form-places` decimal places.
`--temporal-closed-form-digits` separately requests exact normalized low digits
and their carry masks, subject to the source and moving-cut budgets.

```sh
number-compiler 5rev10 --seed 196 --nth-power10 60 --no-value --info arithmetic.modular --arithmetic-modular-kind digit-field --format json
number-compiler 5rev10 --seed 196 --nth 209 --no-value --info temporal.closed-form --temporal-closed-form-digits 4 --format json
```

The reversal families use `temporal.matrix` for demanded ordered outputs as
well as source transfer. `--temporal-matrix-kind digit-band` uses
`--temporal-matrix-band-width` in decimal digits (default 2).
The horizon `--temporal-matrix-steps` always counts physical ticks. `2rev10`
digit-band requests require multiples of four; reverse/add retains its
128-tick limit. Source certificates can impose tighter limits than the public
4,096-tick ceiling.
`temporal.matrix.trace` requests bounded chronological detail, at most 128
ticks. Ordered outputs use `--temporal-matrix-modulus` (default 1,000,000,007)
and optional `--temporal-matrix-coefficients=1,-2,3` for a degree-zero through
degree-eight covector. Coefficients are ordered by the power of the first
coordinate. Later chronological column actions multiply on the left. These
are finite mathematical observations, not selectable execution algorithms or
certificates of unrestricted future closure. Reverse/add's existing innovation
kind retains its own default modulus behavior. Bit-fibre `carry-continuant`
outputs are not advertised until their concrete source-period refinement is
accepted. A base-five port is not a bit-fibre certificate.

`2rev10` uses `U(n) = 2 * reverse10(n)`, including decimal normalization,
for example `10 → 2`. Its decimal grammar is applied through the shared
scheduler. Admitted four-phase boundary cylinders use temporal HashLife
composition of the exact two-step cellular rule. A bounded source probe can
select a padded cone for a long, wide request outside the cylinder. Short
requests keep their packed route. `--max-steps` and `--max-state-bits` both
default to 4,096. The family supports output formats, output bases, the bounded
`--first-palindrome-within` selector and the observations in its generated
capability table.

The demanded `temporal.closed-form` packet reports source-bound carry and moment
ports from the completed endpoint. `--temporal-closed-form-modulus M` projects
them modulo a positive integer without authorizing an approximate branch or
phase decision. The packet retains original-source fields and separately
reports an admitted transient prefix and affine suffix. Its suffix shift is
derived from the endpoint and supplies no new predictive source certificate.
Metrics alone never construct these ports.

`--info spatial.stencil --spatial-stencil-position P` demands one LSD-indexed
digit from an admitted temporal cylinder. `--info temporal.bank` reports the
admitted border’s forced growth/carry word and separately labeled bounds for
conditional observers. Both share bounded, charged entry discovery and avoid
rendering the full endpoint. A source without a certified entry returns an
unavailable observation with exit 3. `spatial.pair-bank` uses a final
outer-to-inner pair coordinate. `temporal.grammar` uses an entry-source
coordinate and `--temporal-grammar-period` (1–8) to certify both finite causal
halos before publishing a repeated motif. Their coordinate units are explicit
in JSON.

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

### Grouped result views

Use each view flag more than once to request several results under one
information category. Unsupported combinations fail at parsing. JSON puts
each selected view under `info[category]["views"][view]`, with its law, clock
unit, coordinate, authority scope, status, and value. Compatible views share
one source preparation. Each value retains its own precision and coverage.

<!-- cli-views:start -->
| Category | View flag | Views |
| --- | --- | --- |
| `arithmetic.modular` | `--arithmetic-modular-kind` | `residue` (reverse-add, 2rev10), `mixed-adic` (2rev10), `endpoint` (5rev10, collatz, antihydra), `digit-field` (5rev10) |
| `temporal.clock` | `--temporal-clock-detail` | `residue-period` (2rev10), `defect-samples` (2rev10) |
| `temporal.accumulator` | `--temporal-accumulator-kind` | `alternating` (reverse-add, 2rev10, collatz), `single` (collatz) |
| `temporal.closed-form` | `--temporal-closed-form-kind` | `source-action` (reverse-add, 2rev10), `endpoint` (2rev10, 5rev10) |
| `safety.ledger` | `--safety-ledger-detail` | `finite-guard` (antihydra), `finite-safety` (antihydra) |
| `temporal.macro` | `--temporal-macro-kind` | `executed` (collatz), `graph-action` (antihydra) |
<!-- cli-views:end -->

The family listing shows supported choices. Antihydra always reports the
arithmetic ledger when requested. Its optional finite guard reports the
weighted source action. For the authenticated source 7 the fractional
interval is certified empty from two steps onward. The ledger continues
to report the physical prefix and first failure independently.

Finite rational safety and closed graph actions share the exact fractional tail
at the selected centered endpoint. Their results count physical ticks. The
graph view covers the certified 60/40 row and its rotation, up to 2,048 copies.

```sh
number-compiler antihydra --nth 254 --no-value --format json \
  --info safety.ledger --safety-ledger-detail finite-safety --safety-horizon 4 \
  --info temporal.macro --temporal-macro-kind graph-action --temporal-macro-copies 2 \
  --fractional-tail 1/57
```

The continued-fraction band takes the starting power-of-five exponent, the
decimal cut, the digit width, and the row count. The cut advances one place per
row. The packet contains the exact MSD-first continuant for the ordered rows.
An information-only band request can run independently of the Antihydra term.

```sh
number-compiler antihydra --nth 0 --no-value --format json \
  --info arithmetic.continued-fraction --continued-fraction-band 1530,33,1,6
```

A finite continued-fraction cylinder uses `--safety-horizon` in physical
ticks, from 0 through 4,096. Its input concatenates the decimal digits of
`5^1, 5^2, ...` in most-significant-first order within each power and adds
one to each digit. The packet gives the shortest prefix that determines the
safe path, its ordered continuant, and exact rational bounds. Set
`--continued-fraction-max-coefficients` to bound the search. It accepts
1–100,000 and defaults to 20,000. An exhausted search reports `unknown`.
Use `--no-value` to request the independent cylinder without computing the
Antihydra term.

```sh
number-compiler antihydra --nth 0 --no-value --format json \
  --info arithmetic.continued-fraction --safety-horizon 96
```

Reverse/add and `2rev10` support `--info arithmetic.modular --arithmetic-modular-kind residue`
without rendering an endpoint. Reverse/add predicts modulo 99. The certified 2rev10
width clock predicts modulo 99 and 198. These scalar projections do not select
future carry banks or authorize a full digit word.

Reverse/add's `temporal.accumulator` with the `alternating` view reports both
accumulator residues with their physical phase. Innovation matrices requested
with `--temporal-matrix-modulus 99` use this same bounded-bootstrap, powered
projection without constructing a Q19 endpoint. This projection admits source
seeds of at most 4,096 decimal digits and charges its source scan and arithmetic
under the query ledger; the requested generation is powered logarithmically.
Other moduli retain their
existing source requirements. Collatz's `temporal.accumulator` with `--temporal-accumulator-kind alternating` reports
the exact added and subtracted physical-operation totals, including a pending
odd half-step, from the admitted joint action.

`reverse-add --info temporal.closed-form --temporal-closed-form-kind source-action` reads the completed scheduler endpoint
and its correlated center/carry ports for indices 2 through 4097. Width and
digit consumers share that occurrence; this observation does not replay the
trajectory. Its measured Q19 block count does not imply logarithmic temporal
construction. `2rev10 --info temporal.closed-form --temporal-closed-form-kind source-action` publishes the exact source
entry and powered endpoint. Optional `--temporal-period-samples` requests a
bounded center-window scan, controlled by `--temporal-period-stride`,
`--temporal-period-depth` and `--temporal-period-max-lag`. The default sample
count is zero. Finite matching windows never certify an infinite period.

`reverse-add --info temporal.mirrored-diagonal` requests a finite decimal
center-carry action with a 512-physical-tick horizon, subject to the request's
scratch budget; the default budget can refuse shorter intervals. Its `center11` packet includes
the two half-word residues and their accumulated difference, which differs from
the difference at just the final endpoint. The action retains exact source and
carry seams. This diagnostic evaluates the bounded seed trajectory, rather than
reusing a completed successor path. It supplies no autonomous future-port program; ordinary output,
metrics and temporal summaries do not construct this diagnostic.

For `2rev10`, `temporal.clock` with `--temporal-clock-detail defect-samples` requests finite carry-defect samples
from a shared causal halo. `--temporal-defect-digits` selects up to 96 low
decimal positions, with 8 used when omitted for this observation.
`--temporal-period-samples` selects at most 128 four-generation samples;
the defect observation uses 24 when no positive count is supplied.
Stride and maximum lag use the existing temporal-period options. Supplying
positive defect digits and samples with the `source-action` closed-form view requests
the same finite samples and checks their suffix against its exact endpoint.
Combined requests reuse that checked result. Candidate periods remain finite
observations, not authority to repeat a physical source action indefinitely.

For `2rev10`, `temporal.accumulator` reports the source-guarded Laurent
accumulator modulo 198 and its first decimal jet modulo 1980. A separate
`temporal.clock` request with `--temporal-clock-detail residue-period` reports
the exact mod-99 and mod-198 lassos. Both can consume the action issued for
`arithmetic.modular` at the same source and generation.

`2rev10 --info arithmetic.modular --arithmetic-modular-kind mixed-adic` admits a bounded source prefix into the
closed outer border and powers its phase, width parity and residue modulo 99.
It returns the exact residue modulo 1980, the four oriented digit fields and
a set of possible residues modulo 9900. The latter is an enclosure.
The mod-18/90 field returns after 72 and 576 ticks on that border. The
mixed state can have a different period. A source outside the admitted border
returns an unavailable observation.

```sh
number-compiler reverse-add --seed 196 --nth 64 --no-value --info temporal.closed-form --temporal-closed-form-kind source-action --format json
number-compiler 2rev10 --seed 196 --nth 128 --no-value --info temporal.closed-form --temporal-closed-form-kind source-action --format json
number-compiler 2rev10 --seed 196 --nth-power10 80 --no-value --info arithmetic.modular --arithmetic-modular-kind mixed-adic --format json
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
number-compiler reverse-add --seed 196 --nth-power10 12 --no-value --info arithmetic.modular --arithmetic-modular-kind residue --format json
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
1–16; powered endpoints use bounded point queries into its admitted causal halo. `2rev10`
requires an even horizon because one internal paired action spans two physical
ticks, with powered horizons through 4,096 ticks. Fermat carry transfers use `--temporal-matrix-digit-position`; their
horizon counts ordinary tripling ticks on the selected terminal source, not
successive Fermat indices. The Mahler center is selected from its source width. Coordinate kinds and admitted limits are declared by the family
registry; two equally sized matrices need not have the same state space.

The matrix is published directly under `info["temporal.matrix"]`, separately
from `temporal.macro` and `arithmetic.mahler`. Its finite source and conditional
relation are distinguished, and the packet itself conveys no execution or
infinite-repetition authority. Ordinary output, temporal summaries and metrics
never request these detailed matrix observations.

`--info temporal.matrix.trace` explicitly requests chronological detail under
its packet's `trace` field. A combined matrix and trace request shares one
source admission and observation. `2rev10` traces are bounded to 128 physical
ticks; Fermat and Mersenne traces to 64 steps. Trace demands do not select a
competing execution algorithm. Oversized traces are rejected before construction.

Mersenne source-transfer uses the norm-one matrix associated with the selected
Mersenne value, evaluated through bounded residues. Its horizon unit is
`trace-squaring-steps`, not recurrence ticks or successive Mersenne indices.
Neither this transfer nor Fermat's ordinary-tripling transfer supplies a
primality certificate. Both support bounded horizons through 4,096 steps.

For Fermat indices 0–8, `--temporal-matrix-kind negacyclic` projects the
selected source through up to 4,096 ordinary tripling ticks in the ring
modulo `2^W + 1`, where `W = 2^index`. The source fixes the width, so this
view takes no digit-position option and has no chronological trace.

```sh
number-compiler fermat --nth 2 --no-value --info temporal.matrix \
  --temporal-matrix-kind negacyclic --temporal-matrix-steps 3 --format json
```

The packet includes the canonical endpoint and the low 32 bits of the wrap
quotient calculated from the canonical tick-zero residue. It also includes
the initial signed inlet split. Raw carry from the unreduced integer is
reported as null, and the packet carries no primality authority.

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
| `reverse-add` | `iterations` | `--seed`, `--base` | `temporal`, `metrics`, `spatial.mirror`, `temporal.macro`, `temporal.matrix`, `arithmetic.modular`, `temporal.accumulator`, `temporal.mirrored-diagonal`, `temporal.open-ring`, `temporal.closed-form`, `temporal.stencil`, `spatial.bank-morphism`, `temporal.matrix.trace` | — |
| `2rev10` | `iterations` | `--seed` | `temporal`, `metrics`, `temporal.matrix`, `temporal.closed-form`, `arithmetic.modular`, `temporal.accumulator`, `temporal.clock`, `temporal.carry-safety`, `spatial.stencil`, `temporal.bank`, `temporal.open-ring`, `temporal.birth-layers`, `spatial.pair-bank`, `spatial.bank-morphism`, `spatial.bank-window`, `temporal.grammar`, `temporal.radix-walsh`, `arithmetic.radix25-shift`, `temporal.matrix.trace` | — |
| `5rev10` | `iterations` | `--seed` | `temporal`, `metrics`, `temporal.bank`, `arithmetic.modular`, `temporal.closed-form`, `temporal.matrix`, `temporal.matrix.trace` | — |
| `collatz` | `physical_iterations` | `--seed`, `--radix` | `temporal`, `metrics`, `temporal.matrix`, `temporal.clock`, `temporal.accumulator`, `temporal.diagonal-carry`, `temporal.carry-bellman`, `temporal.macro`, `temporal.innovation-borrow`, `temporal.matrix.trace` | `temporal`, `temporal.clock`, `arithmetic.modular`, `arithmetic.twisted`, `arithmetic.hasse`, `arithmetic.hensel`, `arithmetic.tropical`, `arithmetic.factor`, `safety.execution` |
| `antihydra` | `macro_returns_after_startup` | — | `temporal`, `metrics`, `temporal.matrix`, `safety.ledger`, `temporal.clock`, `arithmetic.modular`, `spatial.tape`, `arithmetic.twisted`, `temporal.spacetime`, `temporal.diagonal-carry`, `arithmetic.hasse`, `arithmetic.hensel`, `arithmetic.mahler`, `arithmetic.continued-fraction`, `temporal.macro`, `arithmetic.tropical`, `arithmetic.factor`, `temporal.matrix.trace` | — |
| `a367620` | `oeis_index` | — | `temporal`, `metrics`, `temporal.clock`, `arithmetic.tropical`, `safety.certificate` | — |
| `prime` | `prime_index` | `--start` | `metrics` | — |
| `fermat` | `fermat_index` | — | `temporal`, `metrics`, `temporal.matrix`, `number-theory.primality`, `number-theory.factor`, `number-theory.root`, `temporal.matrix.trace` | — |
| `mersenne` | `mersenne_exponent` | — | `temporal`, `metrics`, `temporal.matrix`, `number-theory.primality`, `number-theory.factor`, `number-theory.root`, `temporal.matrix.trace` | — |
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
the completed decimal occurrence. With `--temporal-matrix-modulus M`, it transports
endpoint residues through the issued carry-switch intervals without constructing
the exact endpoint integer or rescanning each successor's complete digit tape.
`--info temporal.stencil` explicitly requests the bounded five-band carry and
signed-borrow diagnostic, subject to `--max-digits` and `--max-output-bits`.
These observations do not authorize repeating a conditional source action.
Neither runs for an ordinary value or metrics-only request.

```sh
number-compiler reverse-add --seed 196 --nth 20 --no-value --info temporal.matrix --temporal-matrix-kind innovation --temporal-matrix-modulus 1009 --format json
```

## Collatz diagonal carry observations

`--info temporal.diagonal-carry` uses the query's already issued joint action.
It reports normalized and physical endpoints separately, including a pending
odd half-step. `--temporal-clock-max-digits` bounds its binary spatial field;
truncated fields are marked incomplete. The packet also reports the aggregate
two-ledger Laurent defect when it fits that bound. This aggregate is not a sum
of historical per-step carry polynomials. A moving-cut reflection is sparse,
including negative exponents, and never pads a word to the temporal index.

Ordinary values, metrics and temporal summaries do not construct these fields.
The finite source-window executor shares its admitted action with endpoint,
clock and demanded innovation consumers; it does not infer an unrestricted
future parity word or a periodic orbit.

```sh
number-compiler collatz --seed 27 --nth 64 --no-value --info temporal.diagonal-carry --temporal-clock-max-digits 256 --format json
```

`--info temporal.carry-bellman` finds the first positive offset at which the
homogeneous ×3, ×5 and ×15 carries on the centered source `x + 1` are
simultaneously even at all requested binary cuts.
`--temporal-bellman-cuts` accepts comma-separated cut positions.
`--temporal-bellman-horizon` counts normalized odd steps from the selected
endpoint. The source must force the entire odd interval from a completed
normalized step. The packet reports the corresponding physical horizon and
first physical offset, using two physical ticks per odd step.
The `corrected` field applies the moving correction `−2^t` to the ×3
lane and reports the first aligned event with the ×5 and ×15 lanes.
It also reports the low bits of the scaled physical numerator
`3^t (x + 1) − 2^t` at the requested horizon. Both event results share
the same source and cuts.

```sh
number-compiler collatz --seed 7 --nth 2 --no-value --info temporal.carry-bellman --temporal-bellman-cuts 2,3 --temporal-bellman-horizon 2 --format json
```

## Antihydra arithmetic and physical observations

The arithmetic endpoint is the total sequence
`a(0) = 8`, `a(n+1) = a(n) + floor(a(n)/2)`. Its ledger adds 2 on even values of
`a`, and subtracts 1 on odd values. Arithmetic continues if this ledger becomes
negative. `safety.ledger` and `arithmetic.modular` use the arithmetic owner without a physical
clock roof. Labels distinguish odd centered states `D = a - 1` from odd values
of `a`.

`--info temporal.diagonal-carry` projects the raw multiplication and corrected
physical carry fields from that same authenticated arithmetic endpoint.
`--spatial-width 0` requests every significant column; a positive width requests
a bounded prefix. `--max-observer-terms` and the query's resource budget apply
before field allocation. The packet carries eleven lanes in 32-bit column slots,
with explicit lane offsets and widths; large packed words use the common exact
hexadecimal integer encoding. It does not retain intermediate temporal rows.

The raw floor of `(3/2)^n * a(0)` differs from iterating the physical integer
floor. The returned correction keeps them distinct. This observation supplies
finite source-bound arithmetic, not an all-time safety or non-halting certificate.
Ordinary value, ledger and temporal-summary requests do not construct the field.

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

Prime queries discover a consecutive prime prefix through the exact square-root
boundary using the shared Legendre count DAG. Short relative queries with
`--start` at least 10,000 and `--nth` at most 128 can scan candidates in
the coprime residue classes modulo 210. Each scan batch uses the committed
factor prefix to test its candidates in increasing order. Other queries use rank
descent and retain intermediate count states across ranks.

```sh
number-compiler prime --nth 1000 --info metrics
number-compiler prime --nth 0 --start 10000 --max-prime-states 131072 \
  --max-prime-work 1000000 --max-prime-stages 4096
```

These positive prime-only limits default to 131,072 completed DAG states,
1,000,000 charged work steps, and 4,096 factor stages (including seed 2).
Refusal returns exit code 2 without a fallback. Work counts DAG-frame visits,
factor appends, rank and discovery admission, and wheel probes and trial divisions.
Cache hits count reuse that avoids scheduling or
evaluating a state, not every backing-map read. Operand-bit work sums accounted
operand widths; neither counter is a timing or bit-operation bound. `prime_retained_entries` reports the states
and factors retained at query completion before disposal; the memo and factors
are released when selection returns. `prime_peak_pending_frames` reports local
traversal storage. Historical `prime_block_compilations` now counts finite window
rank queries; `prime_max_block_length` retains its odd-window units. The Python
selector's `leaf_length` argument remains an initial-window hint (default 8).
Rank descent ends at one candidate. The initial size uses four times the requested
rank, with exact doubling when necessary. It assumes no prime-density bound.

This finite production bridge does not establish cheap unbounded prime-stage
discovery or the unresolved cross-family terminal and powered-construction proofs.

## A367620 global-provider admission

`number-compiler a367620 --nth N` uses fixed source 20 and decimal comma-child
semantics. It rejects `--seed`, `--base`, `--radix`, `--start` and `--events`.
Construction budgets are `--max-comma-states` (131,072) and `--max-comma-work`
(1,000,000); stricter resource limits still apply.

All value requests require a registered global release artifact. The finite
forest/prefix fallback has been removed. The required artifact and admission
are currently absent, so public value requests return exit 3 with `value: null`
and an `unresolved_sequence_boundary` error; text reports the boundary on stderr.
The following command forms remain valid, but do not yet have successful
production value admission. See the [release gate](release-status.md).

```sh
number-compiler a367620 --nth 1
number-compiler a367620 --nth 20000 --info temporal.clock
number-compiler a367620 --nth 412987860 --info safety.certificate --format json
number-compiler a367620 --nth 20000 --no-value --info safety.certificate --info metrics --format json
```

The safety.certificate packet distinguishes `runtime_verified` from
`isabelle_instance_checked`. Only an exact artifact registered against the
global kernel release contract can authorize values; metadata or a checksum
alone cannot. `--info metrics` alone never initiates certificate verification
or arithmetic. Metrics remain read-only schema 8.
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

Provider admission retains source, generation and ledger ownership checks.
Parsing, authority checks and source-selected execution remain budgeted.
Legacy certificate metric fields remain part of schema 8; their presence does
not mean the retired forest verifier ran.

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

Nondecimal `--base` is rejected for this observer. `2rev10` is also a public
sequence family. It currently has no `temporal.macro` registry entry because
the term does not publish a reusable occurrence cursor; deriving one by
advancing adjacent actions would make a summary demand perform future work.
Its typed border occurrences appear only in an explicit
`temporal.matrix.trace` request. The reverse/add `temporal.macro` observer
remains the separate finite boundary-window certificate described above.
Both trace families use shared typed border identities and exact-join
contracts, while their source issuers, guards, clocks and recurrence laws
remain family-owned. An observed finite return or burst does not certify that
it repeats after its authenticated source interval.


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
