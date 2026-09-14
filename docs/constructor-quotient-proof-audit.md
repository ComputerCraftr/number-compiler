# Constructor quotient proof audit — September 11

## Correction: a carry readout is not the clock-cylinder state

The previous audit tested an insufficient projection and used it to frame the
clock-cylinder proposal. That was the wrong proof target. The mathematical
fact about LT/EQ/GT alone did not refute the proposed source-sensitive cylinder.
The domain-only impossibility theorem has been removed from this development,
and its regression is replaced with a positive predicate-pullback check.

The intended ownership is:

| Layer | Owns |
| --- | --- |
| Reusable cylinder action | Publisher morphism and pullback of demanded consumers |
| Exact occurrence | Source payload on which pulled-back predicates are evaluated |
| Local interface | Evaluated carry, domain and output readouts |

Sources 2 and 8 can share one double action while answering its pulled-back
future threshold differently. Neither LT/EQ/GT nor a finite clock phase is the
complete source occurrence. The updated theorem target is
`eval_O(P*D) = D(P(O))`, with contravariant composition
`(P2 o P1)*D = P1*(P2*D)` and carry/domain derived afterward.

Passing local arithmetic theorems is not evidence that production implements
this full construction. The production 196/Collatz P0 gate remains open because
the required constructor integration and measured work bounds are missing,
not because the clock-cylinder proposal was disproved.

## Concrete proof additions

[Decimal_Publisher_Constructor.thy](../devtools/proofs/isabelle/temporal_clocks/Decimal_Publisher_Constructor.thy)
formalizes a local digit publisher with two explicit Boolean incoming carry
ports. Decimal residue normalization is idempotent and is consumed at the local
publisher seam; the output value and LT/EQ/GT domain agree with the exact
normalized digit sum. This normalizer is `x mod 10`, not a time-advancing
whole-occurrence endpoint map. The carry ports must already be admitted; this
local theorem does not discover a future whole-field carry grammar.
The local publisher is strictly noninjective across every Boolean port pair:
digit inputs `(0,3)` and `(1,2)` publish the same value and domain. This is a
local consumer alias, not an all-duration whole-field constructor.

The corrected theory additionally proves generic consumer evaluation under
pullback, contravariant composition, the integer affine threshold law
`(a,t) -> (a*M,t-a*b)`, and domain/carry readouts from pulled thresholds 9 and
10. The positive doubling theorem reduces the demanded threshold to 5.
These are exact laws for the specified functions. Generic function composition
does not itself provide a reduced decision-DAG constructor or bound its size;
the new proof is not presented as a certificate for those absent operations.

The same theory proves that commuting transports `2` and `y`, under the
explicit ring assumptions `2^5=0` and `y^5=0`, have 25 potentially live exponent
slots `(q,r)` with `q,r<5`. Transport composes by adding the two depths, and a
slot outside that rectangle is zero. This is a bound on transported
contributions in the selected primary module. It is neither a proof that every
exact output consumer factors through that module nor a cost bound for
constructing future births.

[Collatz_Cylinder_Constructor.thy](../devtools/proofs/isabelle/temporal_clocks/Collatz_Cylinder_Constructor.thy)
replaces the supplied valuation premise for its concrete reference constructor
with a source-derived split of `3*x+1`. It proves the normalized cylinder atom,
prefix composition `(beta1 + 2^K1*beta2, K1+K2)`, exact N-event endpoint identity,
and composition of physical-tick weights. The second prefix is evaluated at
clock `n+N`, not at the original clock. The physical embedding is restricted to
odd source inputs; the public runtime additionally requires positive seeds.
The theory also embeds the admitted production shortcut:
`C^(k+t)(2^k) = C^t(1)` and `C^3(1)=1`. This result requires no assumption
that arbitrary positive sources eventually reach that cycle.

The reference constructor deliberately exposes its work: one source split per
accelerated event. Thus it removes an itinerary from the theorem inputs without
pretending that discovering the itinerary became sublinear. It remains a
proof-side reference, not a new production jump implementation. The formal
counter counts recursive event calls; source-node visits, integer bit work and
the divisions inside each valuation computation are additional costs.

## Positive pullback regression and representation boundaries

**One shared cylinder action gives the correct two answers.** For the admitted
no-growth chamber, `P(s)=2s` pulls the future GT consumer back to
`[2s>=10]=[s>=5]`. Evaluating at 2 and 8 produces false and true, respectively.
The runtime regression compiles this pullback through the existing
`ReverseContextualResidualArena.pullback` owner, with occurrence evaluation
poisoned during compilation. Its canonical function ID equals the directly
compiled threshold-five predicate. Only afterward are the two occurrences
bound. This tests a real existing substitution primitive, not a domain-only
automaton or an arbitrary-duration publisher implementation.

**The previous endpoint quotient cannot directly serve as the new normalizer.** For the
reachable pair occurrence `(2,)`, successive endpoints are `(4,)`, `(8,)`,
`(16,)`. Taking `NF` itself to be one successor makes the proposed
`NF(T(NF(O))) = NF(T(O))` equation fail. The local digit normalizer above is a
valid seam normalizer; the proposed whole-state `NF_target` still needs its own
concrete definition and proof. The attachment distinguishes these objects;
this regression guards against conflating them during implementation.

**Clock action and source occurrence remain separate in Collatz too.**
At precision six, 16 accelerated events return the inverse-three clock to the
same phase. Seeds 1 and 129 both have low prefix 1, but the exact outcomes are:

| Seed | Accelerated events | Endpoint | Valuation sum | Physical ticks |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 16 | 1 | 32 | 48 |
| 129 | 16 | 175 | 25 | 41 |

The executable regression records these different occurrence outputs. The
formal theory uses a smaller two-event/three-bit example. These are not
counterexamples to the proposed valuation-cylinder tree or to temporal motion
on cylinder points. That source-sensitive tree retains information absent from
the finite phase readout; shared action identity does not mean equal output
for different occurrence bindings.

**The inverse-three valuation formula has a low-level exception.**
`v2(3^(2^p)-1)=p+2` requires `p>=1`; for `p=0`, `3-1=2` has valuation one. In
particular, the unqualified phase-death bound fails at precision two and level
zero. The existing runtime phase owner already treats the low precisions
separately. Radix-64 depths use precision at least six and avoid this exception.

## Remaining release obligations

| Required construction | What is still missing |
| --- | --- |
| 196 publisher substitution | An executable canonical morphism representation with an all-port future-consumer congruence that retains the necessary value predicates |
| 196 finite innovation absorption | Proof that every demanded exact consumer factors through the retained module, plus a bound on discovering source-dependent new births |
| Collatz residual grammar composition | Canonical source-cylinder intersection and tangent substitution that avoid constructing and scanning every intermediate occurrence |
| Physical-time Collatz query | Correct partial-block selection for a requested physical duration, since N accelerated events have source-dependent physical weight |
| First-use HashLife release gate | Bounds on newly constructed residual nodes, cold source-node visits and retained work across A1…A1024, with forbidden midpoint/ordinary-successor paths poisoned |

## Actual production wiring

The implementation audit confirms that the latest general clock-cylinder
constructor is absent from the production path. This is an integration finding,
not a theorem against the researched algebra.

| Path/owner | Implemented behavior | Gap relative to the proposed constructor |
| --- | --- | --- |
| [196 compilation](../src/number_compiler/sequences/reverse_add/compilation.py#L34), [power index](../src/number_compiler/sequences/reverse_add/power.py#L341) | Powers the base block effect and builds the generic HashLife index | Does not instantiate a powered threshold/publisher cylinder |
| [Collatz compilation](../src/number_compiler/sequences/collatz/compilation.py#L10) | Powers the physical binary transducer | Does not construct a valuation-cylinder occurrence tree |
| [Production causal completion](../src/number_compiler/hashlife/execution/tile_causal_entry.py#L89) | Handles composite primitive-adapter actions before the generic temporal fallback; point and width use the same causal engine | Exact prefixes and future boundary consumers still require causal construction; this is the current production optimization target |
| [Generic temporal fallback](../src/number_compiler/hashlife/execution/tile_temporal.py#L35) | Completes a midpoint and uses it as the next source | This helper is not reached for the supported composite production adapter once causal completion succeeds; replacing it alone would not fix the CLI |
| [Scheduler dispatch](../src/number_compiler/hashlife/execution/tile_scheduler.py#L601) | Tries cached/cycle/causal completion, then temporal or direct completion | No general cylinder-residual adapter dispatch before the causal path |
| [Reverse contextual pullback](../src/number_compiler/sequences/reverse_add/contextual_residual.py#L137) | Canonical finite-function substitution; exercised by the new positive test | Local primitive exists, but no arbitrary powered piecewise-affine publisher is installed |
| [Collatz initial root shift](../src/number_compiler/hashlife/execution/tile_collatz_root.py#L15), [cycle shortcut](../src/number_compiler/hashlife/execution/tile_collatz_cycle.py#L163) | Initial root-prefix and admitted power-of-two/cycle acceleration | These narrow paths do not construct arbitrary future valuation prefixes |
| [Hensel slab arena](../src/number_compiler/sequences/collatz/hensel_slabs.py#L77) | Research composition of supplied slab atoms | Not a scheduler adapter that derives a free multi-event predicate from the source |

For Collatz, the next owner must combine a free source-cylinder predicate,
phase-aware inverse-three translation, tangent, event/tick weights, structural
normalization, and binding to the endpoint occurrence. Existing components
already supply local root matching, inverse-three clocks, seven mismatch
skeletons, directional consumers, affine composition and formula prefix
selection. The missing owner combines those operations across powered blocks.

The exact valuation-code identity `V(U^N(x)) = drop_N(V(x))` is compatible with
this design. Defining the code by iterating U proves a shift law without
constructing that code efficiently. A source-derived cylinder constructor and
its weighted-select implementation remain separate obligations.

For an installed family residual, point dispatch belongs after complete
execution-key admission and before `causal_point`; width has the corresponding
hook before `causal_width_query`; explicit completion belongs before
`causal_complete`. A completed result must retain the exact request's source,
ports, wiring, boundaries and fusion contract, and publish through the existing
result arena. An action-only result cache would conflate occurrences.

Symbolic composition laws do not discharge the final row unless the constructor
and its cost model are included. A source-sensitive occurrence may retain all
necessary information while the residual grammar still grows linearly; the
proposals explicitly require measuring and excluding that outcome.

The corrected complexity target is source-sensitive: charge unique original
source-DAG nodes inspected, source summaries published, residual nodes created,
and target children published, together with tree-descent and arithmetic cost.
Do not demand `O(log N)` independent of arbitrary source size. Conversely, do
not rename each newly computed valuation event a "source node" and claim the
bound by definition. The source is the original input DAG. Construction from a
compact source must expose whether repeated temporal work remains; weighted
drop/select over a valuation tree prebuilt by N scalar successors does not
discharge that gate. Existing release assertions are not weakened by this
clarification.

No production algorithm changed in the proof correction below. The causal-frame and cache
measurements in the [preceding production audit](production-p0-followup.md)
therefore remain the current baseline; no improvement is attributed to adding
proof files.

## Executable regression scope

[Constructor obligation tests](../tests/validation/research/algebra/test_constructor_quotient_obligations.py)
check exact rational cylinder identities and shifted-prefix composition for
five positive seeds, three clock phases and multiple block splits. They also
check the positive decimal pullback, representation normalization and distinct
Collatz occurrence bindings. The
scalar helper is explicitly an ordinary-step oracle, not a claimed optimized
constructor. Generated build and test transcripts remain local under the
[artifact retention policy](../results/README.md).

## Prior verified checkpoint (before this correction)

The complete registered `Temporal_Clock_Jumps` session, including both new
constructor theories, passed Isabelle2025-2 with `quick_and_dirty=false`.
The new theories also inspect their exported theorem dependencies and reject
any oracle dependency. No `sorry` or additional axioms were introduced.

| Check | Result |
| --- | --- |
| Seven-theory Isabelle session | Passed; guarded wall time 9.85 s, sampled peak 435 MiB |
| Constructor regression tests | 19 passed |
| Existing temporal-clock executable gates | 9 passed |
| Repository policy and proof/production boundary | 43 passed |
| Final frozen-source rerun of the 28 arithmetic/proof tests | Passed in 0.55 s pytest time |
| New Python module | Strict mypy and Ruff passed |
| Whitespace and generated artifacts | `git diff --check` clean; no tracked test logs, XML or results JSON |

All guarded checks used the unchanged 35-second/1-GiB envelope. Isabelle used
the existing `number-compiler-ports-proof` runtime profile. Diagnostic console
runs located and removed recursive simplifier loops; they are not counted as
successful validations. No proof workers remain running.

Authored-source fingerprint after the final proof edits:
`2d89a304934220ba16fc7b9228879647cdd6f46624fbffa306c20f8502d94e33`.

This checkpoint certifies the stated arithmetic laws. It does not certify the
missing cold constructor or change the production growth/cache measurements.

## Verified proof correction checkpoint

The revised seven-theory Isabelle session passes with the domain-only theorem
deleted and the positive pullback laws in its place. Guarded wall time was
12.60 seconds with a sampled 421 MiB peak, within the unchanged 35-second/1-GiB
envelope. The exported theorem oracle-dependency check passes.

The corrected research tests, existing temporal-clock tests and contextual
residual tests pass **36/36** (1.48 seconds pytest time). Strict mypy and Ruff
pass for the changed Python module, and `git diff --check` is clean. The deleted
theorem and negative test identifiers have no remaining references in authored
code or documentation. Generated diagnostics remain outside Git.

Authored-source fingerprint:
`a57a503773a801b0174cd7bb43f66a9ce717c449f3f0cec681b4ba51703eece0`.

No production algorithm or release flag changed in this correction. The
remaining integration gap is the free cylinder/publisher constructor and its
scheduler dispatch, including correct occurrence binding, structural
normalization and source-sensitive work accounting. This report makes no new
runtime speedup or full-constructor proof claim.

## Constructor implementation follow-up

The [fresh cylinder-collapse audit](cylinder-collapse-audit.md) cross-checks
these proof boundaries and reproduces the bounded physical Collatz collapse
through T1024 alongside the seed-196 linear cold endpoint work. It separates
existing local pullback formulas from the remaining complete-constructor proof.

The [free-cylinder experiment](../devtools/experiments/collatz/free_cylinder_residual.py)
now constructs an accelerated Collatz residual without applying a concrete
midpoint. A primitive contains the exact valuation guards
`C(k+1, (2^k-1)/3 mod 2^(k+1))`. Composition pulls the second guard trie back
through each live first affine transport, intersects it with the admitted
source cylinder, and prunes impossible prefixes before visiting their children.
The traversal is iterative. Equal decision structures are interned; this is
not a claim of minimality over all equivalent affine representations.

The admitted finite source chart is explicit in the identity. Within
`0 < x < 2^b`, a nonempty guard `C(q,r)` with `q>b` reduces to `C(b,r)`.
This removes dead high guard precision. It is not an identity on unrestricted
2-adic inputs. Exact affine transports and physical tick weights remain in the
leaves. Lazy binding reads only requested original source bits.

For each row below, a fresh arena starts from precision `q=b+N+1` with `b=3`
and builds N events by squaring. Guard visits and terminal compositions are
cumulative construction work; decision nodes are reachable from the final root,
not all retained intermediate arenas. There is one primitive construction per
trial. N counts accelerated events, not physical Collatz ticks.
The primitive call itself enumerates `q-1` valuation guards; counting it as one
construction does not make that setup constant work as q increases with N.

| N | Endpoint branches | Reachable decision nodes | Guard visits | Terminal compositions |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 3 | 3 | 0 | 0 |
| 2 | 4 | 4 | 14 | 4 |
| 4 | 4 | 4 | 55 | 15 |
| 8 | 4 | 4 | 368 | 98 |
| 16 | 4 | 4 | 12,223 | 2,625 |

The rejected Cartesian implementation performed 3,209,140 pair checks at N=16
and retained 128 reachable decision nodes. Guard traversal and chart
normalization materially improve that bounded construction. These work units
differ, so their ratio is not a measured runtime speedup or a CLI cache-hit gain.
At N=32 the revised route still exceeds its four-million guard-visit limit
(approximately 28 seconds and 795 MB sampled). It constructs a wide intermediate
predicate before applying the final small source chart. Thus
`primitive_constructions=1` alone does not establish logarithmic cold work.

The next required operation is source-chart-aware composition that restricts
intermediate predicates before constructing them. The experiment also lacks
production resource reservations, a canonical tile publisher and physical-time
partial-block selection. It remains under `devtools`; installing it as an
unaccounted second backend would not close the release gate. Its exact-integer
`bind` helper is a differential validation seam, not production output.

For 196, the existing runtime already memoizes exact composite residual requests
under the full `CausalPrefix`. At N=32 it recorded 2,582 such requests, 544 hits
and 2,038 evaluations. The primitive carry quotient discharged 4,064 positions
through 127 transfers. Extending its nine-slot `ReverseBoundOutput` directly
to a composite consumer would omit the intermediate value publisher. The
missing canonical object is that lazy publisher under future consumer
substitution. Persisting exact prefix memos would require dependency leases
and would not itself construct this quotient. No unused Higher-runtime wrapper
was retained as a purported production integration.

### Production scalar-cache admission repair

Both families' direct point path now admits the live tile execution contract
before either the scalar-response cache or the microblock cache can answer.
Previously the outer cache authenticated its issued application and program
but could return a scalar after adapter wiring became invalid. The shared
`TileApplication.validate_execution` entry uses the existing execution-key
validator; it introduces no second result identity.

The regression covers cold, response-cache and microblock-cache requests for
both 196 and Collatz. Rejected wiring cannot credit a query or cache hit or
publish nodes, and restoring valid wiring leaves the existing cached answer
usable. Warm queries now pay live context admission; earlier zero-work warm
measurements must not be read as claiming that these validation visits vanish.
This is a production correctness repair, not a temporal construction speedup.

General 196/Collatz P0 remains open. No proof of logarithmic construction was
added, no release assertion was relaxed, and the bounded Collatz trial is not
reported as a refutation of the clock-cylinder proposal.

### Frozen follow-up validation

Authored-source fingerprint:
`28bb03bfbc4bf2c0bbbc4ddb82114831d6dd50e0a363cb36da71575383e2e0b0`.

The final selected run passes 52 tests in 2.18 seconds pytest time (2.76 seconds
guarded wall time, 84,066,856 bytes sampled peak). It includes all six scalar
admission regressions, the five free-cylinder tests, constructor obligations,
existing contextual residual tests and temporal-clock gates. The dyadic test
poisons both primitive reconstruction and exact midpoint application after A1.
All 1,214 files under `src`, `tests` and `devtools` pass strict mypy; Ruff passes
the changed Python files, and `git diff --check` is clean. The Isabelle theories
are unchanged from the verified proof correction checkpoint above.

An earlier broader invocation that also enabled existing N=64 growth validation
timed out at the unchanged 35-second guard after 13 progress marks; it has no
completed suite result. No test budget or selection marker was changed. A
separate `mypy .` attempt stops on existing duplicate `validation_driver` module
names under two historical `results/current` directories; the successful typed
source-root run must not be described as that whole-directory invocation.
Generated logs and guard JSON remain under `/tmp`, outside Git.

The separate repository-policy and proof/production-boundary gate passes all
43 tests in 30.30 seconds pytest time (30.87 seconds guarded wall time,
618,923,352 bytes sampled peak). No tracked test logs, XML or results JSON were
found. These checks establish the stated scope, not a full-suite release pass.

## Production integration attempt: consumer normalization and exact state types

The attempted reverse/add scheduler optimization reassociated a demanded
`(B ; (M ; L))` boundary as `((B ; M) ; L)` so the last primitive could consume
a carry interface without a materialized intermediate boundary output. The
live A4 request exposed a missing representation: the opposite boundary
argument for `B=A2` is itself a `CausalPrefix`. The proposed rotation tried to
insert that composite state into `CausalPrefix.producer_seed`, which is a
finite integer port. Accepting it would silently change the payload contract;
the candidate was removed. No finite-state or resource assertion was relaxed.

This is a failure of that implementation attempt, not a counterexample to the
clock-cylinder construction. The missing production object must explicitly
own the recursive publisher states, their exact source-view dependencies and
associative substitution. It must also show that evaluation avoids expanding
one primitive boundary summary per generation. The existing finite contextual
chain does not supply an arbitrary-duration publisher implementation.

The Collatz experiment now uses physical-step parity germs, rather than
confusing accelerated event count with the CLI duration. Its source-chart
builder derives the following range from actual branch images. A further
normalization defect was found and corrected: raw affine histories were being
retained even when a source guard forced a constant output. The earlier
31-branch five-bit result is **not** evidence of an injective endpoint quotient.
At 16 physical ticks, the independent exact oracle gives eight endpoints and
ten `(endpoint, event_weight)` outputs. The corrected consumer normalizer
agrees with those counts.

Singleton guards now consume their affine witness, and future composition
uses the resulting constant consumer directly. Equal sibling consumers merge;
endpoint identity stays separate from event-weight metadata. For the three-bit
control, three weighted consumers remain through 1,024 physical ticks, with no
live affine offset payload after tick 16. This bounded result does not establish
the work bound for arbitrary source diagrams or provide the missing production
tile publisher.

### Sparse physical images through 1,024 ticks

The following-chart builder now uses the deduplicated constant image whenever
the first half has only constant consumers. It memoizes the normalized finite
image and duration, builds the next half on that image, and substitutes its
weighted consumers back into the original guards. Mixed affine contexts retain
the symbolic cylinder route. The builder does not replace a sparse image with
every integer of the same width.

| Positive source chart | T16 endpoint / weighted IDs | T1024 endpoint / weighted IDs | Base future-endpoint consumptions by T1024 | Distinct sparse endpoint values / payload bits |
| --- | ---: | ---: | ---: | ---: |
| `0 < x < 2^3` | 3 / 3 | 3 / 3 | 27 | 9 / 33 |
| `0 < x < 2^5` | 8 / 10 | 3 / 7 | 471 | 96 / 865 |
| `0 < x < 2^8` | 84 / 98 | 3 / 20 | 3,928 | 190 / 1,613 |

The complete probe of these three charts through 1,024 ticks takes 0.575 seconds
with a 49.5 MB sampled peak. This replaces the failed five-bit/T128 broad-chart
attempt that reached the 1 GiB guard. On these bounded controls, base consumer
work stabilizes by T128 and the remaining root constants occupy at most three
bits each. The seven weighted five-bit classes preserve event counts even
though there are only three endpoint values.

`future_endpoint_consumptions` explicitly counts evaluation of the physical
parity germ at scalar future endpoints. Zero original-source bit probes is not
zero future-state work, and one primitive object is not one primitive
evaluation. The finite image maps retain exact endpoint integers in the research
arena. Thus this improvement is a bounded endpoint-grammar construction, not
the missing accounted recursive tile publisher or a source-DAG work theorem
for arbitrary input widths. It makes no claim about negative inputs or general
Collatz convergence.

No new production dispatch was retained from this integration attempt. The
earlier admitted cache and cycle changes remain in place. A preparatory pinning
refactor was also removed because the proposed constructor did not become a
production consumer; unrelated scheduler churn is not credited as integration.

Frozen authored-source fingerprint for this attempt:
`8530e637e2ca2e9deeef72644d918ab520134690622e290069056b414bc7782f`.
The final constructor, contextual, temporal-clock and admission selection passes
55 tests in 2.27 seconds; the independent repository-policy and proof-boundary
selection passes 43 tests in 28.85 seconds. Both use the unchanged
35-second/1-GiB guard. Strict mypy passes 1,214 files under `src`, `tests` and
`devtools`; changed-file Ruff and `git diff --check` pass. Isabelle sources are
unchanged from the previous verified session; no new constructor cost theorem
is claimed. Generated evidence remains in `/tmp`, with no tracked test logs,
XML or results JSON. This is not a full-suite or production P0 pass.

## Production root-cylinder dispatch

This later checkpoint retains a production change. `tile_clock_dispatch`
dispatches admitted clock completions after complete-key validation and the
existing result lookup. `TileScheduler.complete` and `TileApplication.interface`
use it for complete outputs; direct demanded point/width use it for the compact
cycle sector. No new cache owner or alternate identity is introduced. Repeated
complete requests reuse `CompletedResultArena`; a freshly constructed clock
result is not counted as a cache hit. Both root and cycle completions use a
shared bounded kernel helper that calls the existing iterative engines directly;
they no longer recursively re-enter `TileScheduler.complete`. A poison test
requires this for both clock sectors, beyond the static call-graph policy gate.

`tile_collatz_root_completion` admits exactly the existing first-root sector:
canonical homogeneous physical Collatz action, standard ports/wiring, no fused
or cropped boundary context, sufficient source padding, and
`3 <= ticks <= v2(3*x+1)+1`. The root valuation comes from the canonical source
DAG's root-matching summary. The complete-output construction is:

1. Execute the odd primitive on the source.
2. Shift its tile DAG right by `ticks-2`, preserving the fixed-width blank frame
   by sharing/concatenating canonical tile subtrees.
3. Execute the final even primitive to derive the exact outgoing interface,
   ports and boundary metadata; publish the result at the original action key
   with `physical_ticks=ticks` and `event_weight=1`.

Thus two primitive field evaluations replace temporal replay in this sector.
The shift does not decode a future integer or digit vector. Point and width
requests deliberately retain the existing lazy first-root coordinate pullback,
which is cheaper than constructing two full primitive fields for one demand.
The existing Isabelle `physical_collatz_removes_dyadic_prefix` and source-split
laws justify the intervening divisions; the new scheduler metadata and resource
contracts are covered by executable tests. No new Isabelle constructor-cost
certificate is claimed.

### Cold work and reuse

The same-process old/new probe disables only the new first-root completion for
the old measurement. Both paths use the same CLI term implementation, seed
`9557=(7*2^12-1)/3`, and full output demand. Times include cold term construction.

| Physical ticks | Old causal frames | New causal frames | Old seconds | New seconds | Old / new retained ledger nodes |
| --- | ---: | ---: | ---: | ---: | ---: |
| 4 | 3,037 | 0 | 0.3177 | 0.0909 | 267 / 248 |
| 8 | 6,025 | 0 | 0.5107 | 0.0903 | 273 / 249 |
| 13 | 9,620 | 0 | 0.7029 | 0.0740 | 279 / 238 |

For sources `(7*2^e-1)/3`, complete output at `e+1` ticks is exactly `7`:

| Source bits | Physical ticks | Skipped division ticks | Primitive field evaluations | Seconds | Retained ledger nodes |
| --- | ---: | ---: | ---: | ---: | ---: |
| 34 | 33 | 31 | 2 | 0.2380 | 247 |
| 130 | 129 | 127 | 2 | 0.0994 | 263 |
| 1,026 | 1,025 | 1,023 | 2 | 0.1867 | 290 |

Zero causal temporal frames does not mean zero spatial work. Source ingestion,
root summaries, two primitive spatial computations, shifting and publication
are still charged. Repeated full-output requests add zero causal frames. The
scheduler regression also requires a parent-result cache hit with no additional
root completion and balanced inventory.

General-input point-zero controls still show substantial cold work:

| Family / seed | Physical ticks | Causal frames | Seconds | Retained ledger nodes |
| --- | ---: | ---: | ---: | ---: |
| reverse/add 196 | 16 | 15,912 | 1.0894 | 11,022 |
| reverse/add 196 | 32 | 53,396 | 3.5700 | 26,595 |
| Collatz 27 | 16 | 5,588 | 0.4534 | 416 |
| Collatz 27 | 32 | 21,233 | 1.5123 | 669 |

Each repeated point request adds one response-cache hit and zero causal frames.
These are observations on this checkpoint, not a controlled comparison with
older historical fingerprints. These are individual timing samples, not a
statistical timing guarantee. The whole probe completed in 10.099 seconds at
a 56,312,264-byte sampled peak under the unchanged 35-second/1-GiB guard.

### Removed prototype and remaining constructor boundary

The recursive 196 state-ID prototype was tested rather than promoted on the
strength of its type shape. Its eager reassociation gives the wrong A4 output
(index 1: 10 instead of 11). The nested consumer is a function of the opposite
port, which is not available until the two directional computations meet.
The engine changes and unused prototype owner were deleted; the finite-port
and resource contracts were not weakened.

The required object is a lazy application of a parametric interface/output
morphism to an exact leased source occurrence. Both directional applications
must remain symbolic until paired emission, where consumer pullback substitutes
their port functions together. Existing primitive `ReverseBoundOutput` functions
handle the local case, but do not publish the general future value morphism.
This is an implementation failure of eager one-sided evaluation, not a
counterexample identifying the carry-domain label with the cylinder clock.

For general Collatz, the normalized admitted-image constructor still retains
research scalar endpoints or mixed affine coefficients. It has no production
owner providing accounted recursive target tiles, arbitrary-block substitution
and the corresponding cold-work bound. It is therefore not imported into the
CLI as a hidden future-integer evaluator. The source-root sector above is the
portion with a complete production publisher and explicit admission law.

The generic exact executor remains reachable for unsupported contexts. Deleting
it now would remove correct 196 and general Collatz output. Neither endpoint
congruence nor the bounded measurements establish arbitrary-input logarithmic
construction; the release status remains blocked on that integration and work
gate. No assertion about general positive or negative Collatz convergence is
used by the new dispatch.

### Validation scope

The initial dispatcher/root integration passed 129 ordinary selected tests in
10.68 seconds and 27 selected constructor research tests in 0.57 seconds.
After removing the bounded recursive scheduler calls, all 45 affected clock
dispatch, root-completion and cycle tests passed again in 6.05 seconds
(6.604 seconds guarded, 75,989,520-byte sampled peak). These include poisoned
temporal replay, forbidden scheduler re-entry, full metadata differential,
invalid-context admission and result-cache/inventory checks. The final static
repository selection passes 42 tests in 7.19 seconds; its separate production
oracle-import poison workload through reverse N=64 passed in 22.22 seconds.
No limits or assertions were weakened and deselected validation tests were run
explicitly rather than counted as passes.

The actual CLI invocation `number-compiler collatz --nth 13 --seed 9557` prints
`7`. Strict mypy passes all 1,219 files under `src`, `tests` and `devtools`.
Changed-file Ruff and `git diff --check` pass. Isabelle sources are unchanged
from the preceding verified session. Generated logs and guard reports remain
under `/tmp`; no tracked test logs, XML or results JSON were found.

Frozen authored-source fingerprint:
`7acfa6a625f3fa16296449ca23641d254e79bf41e0dbd247bbce5dc1a0123638`.
These checks cover the stated production sector and regressions; they do not
constitute a full-suite or general production P0 pass.
