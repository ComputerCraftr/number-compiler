# 196 and Collatz production follow-up — September 11

The subsequent [constructor proof audit](constructor-quotient-proof-audit.md)
records the proposed publisher/prefix repair and corrects an abstraction error
in the initial audit: carry/domain labels are derived readouts, not the full
clock-cylinder state. The positive pullback proof and actual scheduler wiring
audit replace the domain-only rejection as the relevant evidence.

The active P0 scope is 196 and physical Collatz CLI execution, cold tile
construction and HashLife reuse. Expensive Fermat/Mersenne prime-certificate
extraction is deferred to outputs requiring certification. Their existing exact
fallback and `unknown` behavior are unchanged.

**The general P0 gate remains open.** This pass removes measured redundant work
and adds an admitted Collatz jump sector. Three agents independently examined
family integration and the proof-to-scheduler boundary. The current Isabelle
results do not supply a general logarithmic first-use constructor.

## Implemented changes

The 196 left-port codec now derives activity from its existing carry bands. A
predicate pullback through a composed transfer uses band masks and at most two
carry representatives, replacing enumeration of all 43 decimal left states.
Both operations retain exactly the same predicate and successor semantics;
they add no cache or new state coordinate. Exhaustive tests cover radices 2–15
for activity, plus composed transfers and a singleton-predicate basis at radices
2, 3, 10 and 15. A poison regression rejects activity-state enumeration.

Completed-result lookup now performs arena-key validation once, followed by
adapter-context validation, before reading the memo. Direct completion,
temporal completion and demanded observations use that combined entry point.
Warm hits still validate action scope, ports, boundaries, wiring, output and
leases. Public application creation and held-root observations also check the
adapter context; a forged or revoked wiring cannot obtain a warm result. The context hook cannot bypass key admission, and a rejected context
cannot acquire a cached result or increment its hit counter. No validation
certificate cache or unchecked public lookup was introduced.

Collatz cycle completion now admits a source tile spelling `0^k 1 blank*` in
little-endian binary. A transient DAG summary recognizes the power of two;
repeated subtrees are summarized once. An odd source wider than one bit is
rejected before allocating that summary. After `k` physical divisions the value
is 1, so a requested duration `t >= k` is reduced to the known three-cycle with
`t-k` cycle ticks. The result keeps `t` physical ticks and exactly
`(t-k+2)//3` odd events. It executes at most three residual physical steps and
publishes through the existing result arena. Before entry, or outside the
admitted homogeneous initial-boundary contract, the existing executor remains
responsible. Summary visits and workspace peaks are reported explicitly.

Tests include every residual cycle phase, exact cycle entry, a request before
entry, rejection of a source with multiple one bits, and `2^1000` advanced by
`10^12+1000` physical steps. This is a sector-specific jump; seed 27 does not
satisfy this admission condition.

## Cycle admission is not a convergence assumption

The powered Collatz API currently admits positive integer seeds only:
`PoweredCollatzTerm` and `NumberCompiler.project_nth` enforce `seed >= 1`.
A separate admission audit confirmed rejection of 0, -1, -2, -5 and -17 by
both public constructors; the CLI rejected seed -1 with exit 2. Under the
signed physical map, for example,
`-1 -> -2 -> -1` is already a counterexample to a universal `4 -> 2 -> 1`
cycle claim. Supporting signed inputs would require separate signed arithmetic
and admission laws.

No theorem here says that every positive seed reaches the positive cycle. That
statement is the [Collatz conjecture](https://arxiv.org/abs/2111.02635). The new
shortcut proves entry only for its recognized power-of-two sector. General
P0 correctness requires a jump to equal the finite iterate `C^N(seed)` under
its admission conditions, with the claimed construction/work bound. It does
not require or permit assuming eventual convergence of arbitrary seeds.

## Cold CLI comparison

The baseline is Git commit `98938b9`, executed in an isolated worktree using the
same Python environment. Each command ran serially under the unchanged
35-second, 1-GiB process guard. JSON generation and resource audits are included
in elapsed times. Each row is a single run, so small timing differences should
not be interpreted as established speedups.

| Family / seed | N | Predicate-state observations before → after | Port-validation visits before → after | Elapsed seconds before → after |
| --- | ---: | ---: | ---: | ---: |
| 196 | 32 | 15,824 → 338 | 185,645 → 185,566 | 5.49 → 5.36 |
| 196 | 64 | 44,376 → 1,000 | 739,649 → 739,277 | 15.13 → 15.04 |
| Collatz / 27 | 32 | 0 → 0 | 43,849 → 43,818 | 2.80 → 2.93 |
| Collatz / 27 | 64 | 0 → 0 | 89,564 → 89,533 | 4.92 → 5.09 |

The 196 predicate observation reduction is 97.9% at N32 and 97.7% at N64.
General causal construction remains the dominant unresolved cost:

| Family / seed | N | Causal frames | Completed results | Ledger nodes |
| --- | ---: | ---: | ---: | ---: |
| 196 | 32 | 54,083 | 218 | 27,226 |
| 196 | 64 | 185,699 | 414 | 71,999 |
| Collatz / 27 | 32 | 30,254 | 99 | 302 |
| Collatz / 27 | 64 | 66,080 | 113 | 312 |

Those three counts are unchanged from the baseline. All four outputs agree
with the baseline and independent scalar recurrence checks. Resource accounting
is complete with zero mismatch. The Collatz odd-source admission check declines
three requests in each measured run and visits zero power-summary DAG nodes.
The specialized power-of-two result must not be credited as a seed-27 speedup.

The repeated-request probe still reports one API-owner hit and one point-response
hit at each of N8, N16 and N32 for both families, with zero additional measured
scheduler work. This confirms preserved warm reuse; it does not demonstrate
new reuse across different future generations. The full CLI timings provide
no established general speedup beyond the removed local proof work.

## Why the existing proofs do not close the remaining gate

The distinction is present in the theorem statements, not an Isabelle runtime
availability problem:

- [Decimal_Clock_Jumps.thy](../devtools/proofs/isabelle/temporal_clocks/Decimal_Clock_Jumps.thy)
  powers a **fixed admitted forcing action** and explicitly does not assert that
  reverse/add retains that forcing action at the next generation.
- [Collatz_Clock_Jumps.thy](../devtools/proofs/isabelle/temporal_clocks/Collatz_Clock_Jumps.thy)
  composes a **caller-supplied valuation itinerary**. Its valuation sum is an
  input; discovering future valuations and proving first-use cost are excluded.
- [Temporal_Clock_Jumps.thy](../devtools/proofs/isabelle/temporal_clocks/Temporal_Clock_Jumps.thy)
  proves future congruence and dyadic composition of exact endpoints, and
  explicitly says those equations count no arithmetic work. Constructing the
  first image is a separate evaluator obligation.

The production key still binds action, exact input tile, ports, wiring,
boundaries and output region. Removing a live context field without a proved
consumer equivalence would corrupt cache identity. The missing integration is
an admitted constructor for varying nonlinear forcing that composes future
clock/occurrence residuals without recurrence-equivalent midpoint work. Its
cold construction must satisfy the release work and retention bounds. Renaming
an exact endpoint as a clock ID would not meet that requirement.

## Remaining P0 obligations

| Family | Unresolved construction | Required release evidence |
| --- | --- | --- |
| 196 | Compose the changing carry/threshold forcing and growth contexts into canonical future consumer actions before replaying intermediate pair occurrences | Cold dyadic N16…N1024 construction within the work/retention envelopes, exact oracle outputs, and poison gates against whole-field and recurrence-equivalent fallback |
| Physical Collatz | Discover and compose the future valuation/carry residuals while preserving physical duration, rather than taking the branch itinerary as given | Exact physical `C^N` outputs across admitted seeds and boundaries, charged first-use construction within the envelopes, and sound future cache reuse |
| Shared scheduler | Prove which live input/boundary distinctions can disappear before interning future requests | Adversarial context separation, safe lease/eviction behavior, and measured cold reductions beyond the unchanged causal-frame populations |

The existing production probes explicitly keep
`spacetime_logarithmic_closure_proved=False` and
`spacetime_macrocell_absorption_installed=False` in
[reverse_temporal_power_probe.py](../devtools/benchmarks/reverse_temporal_power_probe.py)
and
[collatz_temporal_power_probe.py](../devtools/benchmarks/collatz_temporal_power_probe.py).
They were not weakened. Application creation still repeats a defensive context
check in its sealed constructor; held-root observations revalidate their live
contract. Even non-power-of-two inputs can require a full source-DAG admission
scan. A cold `2^1000 + 2^3` admission check correctly declined after 65 node
visits with 34 transient summary entries. These are remaining measured/audited
costs, not completed optimizations.

## Validation

The final source checkpoint passed **277 selected tests**: 233 focused
scheduler/family/API tests, the explicit N64 reverse public materialization
poison regression, and 43 repository/proof-boundary policy tests. Four heavier
validation cases were deselected by the ordinary focused invocation; the full
suite and runtime-release gate are not claimed green. Strict mypy passed all
1,210 source files, Ruff passed, and `git diff --check` was clean.

The installed Isabelle `Temporal_Clock_Jumps` session build succeeded with its
existing theories. No new theorem was introduced and no fixed-action or
caller-supplied-itinerary premise was removed. The validation and CLI/warm
measurements all used the same authored-source fingerprint:

`ad2c51d72ce3ef95d265c32daf2c83997d739ce64d09ceff063d64dedf0a9abc`.

## Reproduction and evidence retention

Use a clean baseline worktree and the current checkout, with each tree's `src`
on `PYTHONPATH`, to run the same commands:

```sh
python -m devtools.checks.process_guard \
  --output /tmp/fresh-cli.json --report /tmp/fresh-cli.guard.json -- \
  python -m number_compiler nth 196 64 --format json
```

For Collatz use `nth collatz 64 --seed 27 --format json`; repeat at N32. Choose
fresh output paths for every invocation. The existing
`devtools.benchmarks.production_p0_probe --mode repeat --family FAMILY` measures
same-owner warm reuse separately at N8/N16/N32. Generated JSON, test transcripts
and guard reports remain local under the [retention policy](../results/README.md).
