# Production integration P0 — September 11

> Superseded classification policy, September 12: production recurrence runners
> and their CLI enabling flags have been removed. Commands using
> `--allow-classical-ceiling` or `--max-classical-squarings` below are historical
> and now rejected. See the [current recurrence-removal record](production-shadow-jet-release-blocker-2026-09-12.md)
> and [candidate recovery audit](candidate-shadow-recovery-audit-2026-09-12.md).
> The release remains blocked by the missing powered construction and proofs.

**Release remains blocked on 196 and Collatz.** Production CLI execution,
first-use HashLife construction, and removal of implicit recurrence work remain
their P0 requirements. Expensive Fermat/Mersenne prime-certificate extraction is
deferred to outputs that actually require certification. Passing local quotient
proofs or warm-cache checks does not clear the 196/Collatz gate. The latest
[focused implementation audit](production-p0-followup.md) records the changes
after this checkpoint and the exact proof assumptions still outstanding.

## Implemented production changes

The primitive behavior minimizer now captures each immutable emission and
occurrence row once and reuses its two directional views through refinement.
Only successor-class signatures change between rounds. A multi-round decimal
regression checks exact row-read accounting and the existing canonical
partitions/output tests still pass. This removes repeated local proof work on
the actual cold 196/Collatz paths, without changing semantic IDs.

The 196 threshold-summary traversal consumes its already-validated miss instead
of looking up the root again and reproving the same miss on each internal ready
frame. The public warm lookup and child publication checks remain authenticated.
The added counter is `reverse_threshold_summary_known_missing_probe_elisions`.
This changes work, not the completed-result key or carry semantics.

Physical Collatz now reads the low source bit for event weight only at the START
carry port. Every other admitted left port already proves the event is zero.
The five non-START states pass a source-read poison regression; START still reads
once and emits the correct event. Physical tick weight is preserved. The counter
is `collatz_physical_event_source_reads_elided`.

`NumberCompiler` now retains up to eight recent powered term owners, with LRU
replacement. Repeating an equivalent 196 request reuses the same ledger,
compiler, source geometry, scheduler and completed results. Collatz output radix
is a view on the same binary owner, so views share its existing radix projections.
Family, seed, generation and reverse/add base remain distinct. Eviction releases
only the API reference; a returned term remains valid. Counters are cumulative
per owner, and API cache statistics are reported separately by
`powered_cache_info()`. `clear_powered_cache()` releases API references and
`max_cached_terms=0` gives independent cold requests. This is a serial-use cache
with a term-count bound, not a total memory bound or a cross-process cache.

Fermat/Mersenne PASS certificates now consume `PureTwoPrimaryClockShape` and its
direct target-distance jump instead of allocating the complete image-rank,
depth-stratum and unary-transition tables. The full filtration derives from the
same shape owner when explicitly requested. The certificate shape retains a
fixed number of integers; this is not constant bit-space. In particular, the
existing Mersenne stable-image count still has O(p) bits. These are the existing
pulled certificate clocks, not a claim that the full-carrier Moore observer has
changed its class count.

## CLI and fallback policy

The CLI now connects the public theorem resolver through:

```sh
number-compiler fermat --nth 3 --no-value --info primality --format json
number-compiler mersenne --nth 13 --no-value --info primality --format json
```

The first command produces a proved prime result without recurrence. The second
reports `unknown` with exit 3 and zero classical squarings. Both prime and
composite decisions exit 0; invalid or over-budget inputs exit 2. Candidate size
is checked before theorem work using `--max-candidate-bits` (default 1,000,000).
F4 likewise stays unknown. The historical classical-ceiling option has been
removed; production does not enable Pépin or Lucas–Lehmer fallback. An unknown
result is never interpreted as composite.

The Python theorem/certificate APIs accept `allow_classical_ceiling=False` for
the same policy. Their default remains true for backward compatibility. Cache
identity distinguishes the policy when it can affect an unresolved answer and
removes it when terminal-certificate work is disabled. Previously established
exact source constraints can still answer without new recurrence work.

Ordinary `nth fermat` and `nth mersenne` continue using sparse candidate digits.
Those commands do not request primality and must not pay for a theorem clock.

## Remaining release gates

| Family | Production work now avoided | P0 still missing |
| --- | --- | --- |
| 196 | Redundant threshold-summary probes; rebuilt owners on repeated API requests | Construct future nonlinear forcing and canonical tiles with the required first-use work bound |
| Physical Collatz | Provably unnecessary source reads; rebuilt owners and radix views | Compose future forcing under physical-clock semantics with the required first-use work bound |
| Fermat | Full filtration allocation after PASS; implicit recurrence in default CLI classification | Deferred: terminal-depth admission for outputs requiring prime certificates |
| Mersenne | Full filtration allocation after PASS; implicit recurrence in default CLI classification | Deferred: local-capacity/terminal admission for outputs requiring prime certificates |

Sharing completed results across different powered terms needs a deliberately
shared authority and resource budget. Existing per-index radix owner names and
remainder cache keys assume one original source. This patch keeps those scopes
separate; it does not transplant scoped tile IDs or discard live boundary
operands to manufacture hits.

The release acceptance test must charge cold construction as well as warm
application, poison forbidden recurrence/materialization routes, preserve exact
outputs and physical ticks, and enforce the existing work/retention envelopes.
An O(log N) operator DAG or zero sequential-generation counter alone is
insufficient. F/M must establish clock admission from the candidate, not from a
pre-enumerated prime carrier or a supplied factorization.

## Evidence

The recorded September 11 run passed **368 tests**, all five `Temporal_Clock_Jumps`
theories, strict mypy over 1,208 source files, Ruff, and the repository policy
gates. This is a selected change-cone run, not a full-suite or runtime-release
certificate.

Cold primitive-proof observation checks fell from **65,320 to 21,840 for 196**
(66.6%) and **567 to 243 for Collatz** (57.1%). Successor checks and semantic
partitions are unchanged. These reductions are measured work counts, not claimed
wall-time speedups or a logarithmic execution theorem.

The point-query comparison uses the same positions and horizons as the prior
frozen probe:

| Family | N=8 completed results | N=16 | N=32 |
| --- | ---: | ---: | ---: |
| 196 | 143 | 597 | 2,305 |
| Physical Collatz | 111 | 248 | 1,024 |

Those retained populations are unchanged. At every measured horizon, repeating
the request through the same `NumberCompiler` gives one API-owner hit, one point
response hit, and zero additional measured scheduler work. Distinct future
generations still own distinct result caches.

Full CLI output uses a different endpoint-completion workload. All four outputs
below match the existing independent scalar oracles:

| Family | N | Completed results | Ledger nodes | Causal frames | Port-validation visits |
| --- | ---: | ---: | ---: | ---: | ---: |
| 196 | 32 | 218 | 27,226 | 54,083 | 185,645 |
| 196 | 64 | 414 | 71,999 | 185,699 | 739,649 |
| Physical Collatz | 32 | 99 | 302 | 30,254 | 43,849 |
| Physical Collatz | 64 | 113 | 312 | 66,080 | 89,564 |

The growth is still in causal request construction and boundary/port validation,
even where retained endpoint nodes stay small. For 196, directed-transfer
validation visits also rise from 70,749 to 334,930; boundary-cover frames rise
from 12,365 to 55,759. The relevant owners are
`tile_scheduler._validate_execution_key`, `CompletedResultArena` validation,
the causal task engine, and the boundary transfer/cover traversal. These checks
carry admission and ownership obligations; dropping boundary fields or bypassing
validation is not an established optimization.

The new threshold-probe and non-START source-read elisions are proved and
exercised by their dedicated interface tests, but their counters are **zero in
these point and full-CLI workloads**. They are not credited with the cold-path
improvement. The actual measured cold change here is primitive emission-proof
reuse. Plain N64 CLI output without metrics also takes about 14.5 s for 196 and
4.9 s for Collatz in these single guarded runs, so expensive JSON reporting is
not the explanation for the remaining cost.

The [retained run summary](../results/current/production-p0-2026-09-11/README.md)
and its reproduction drivers describe the validation and comparison workloads.
Generated manifests, measurements and transcripts were removed from Git during
artifact cleanup. Reproducing the run generates fresh local evidence; this
historical summary is not a current release certificate. The unchanged limits
are 35 seconds and 1 GiB per heavy command, executed serially. The recorded run
separates warm API reuse, full CLI output, exact oracle checks, and local proof
work. Its source fingerprint was
`afd0fb5d5c3b01ff0b66ce72187eacaed7d3e1efeb8f084752a6a89bcae4c8e0`.

The prior [endpoint-seam report](endpoint-seam-powering-audit.md) remains the
source of the bounded semantic closure results. This production patch does not
promote those results into an unproved first-use complexity certificate.

An adversarial audit also located the cross-owner certificate opportunity in
`DiamondKernelArena.intern`: the immutable primitive quotient could be reused
after complete effect/domain admission, but its current templates contain
arena-scoped program and transfer IDs. A separately bounded and metered value
certificate cache is required before sharing those results across new owners.
The `SHARED_GLOBAL` ledger label alone does not implement that ownership. No
unmetered module cache or scoped-handle sharing was added.
