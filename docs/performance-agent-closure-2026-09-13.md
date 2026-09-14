# Performance implementation and adversarial audit — September 13

**Release remains blocked.** This execution implements bounded prime process
reuse, joint Collatz event/support publication, and bounded Antihydra projection
batching. It does not supply all of the requested family constructors. No failed
construction assertion is replaced by cache-hit success or an UNKNOWN result.
The fixed limits and baseline wheels are recorded in
[frozen acceptance](../results/current/performance-agent-closure-2026-09-13/frozen-acceptance.json).

## Implemented production paths

`NumberCompiler(shared_cache=True)` is backward compatible and enables prime
reuse by default. `shared_cache=False` bypasses that reuse;
`NumberCompiler.clear_shared_cache()` invalidates outstanding leases. CLI syntax,
indices and outputs are unchanged. Other families do not yet use this process
cache, and its presence does not close their construction obligations.

The process store owns immutable summaries under exact, issued source-qualified
leases. Aggregate limits are 131,072 retained records and 32 MiB, including lease
metadata; stricter request limits still apply. Eviction chooses the oldest
published unleased entries deterministically. Disabled-cache leases still undergo
authority checks. Reset, foreign/reconstructed leases, saturation, refusal and
cleanup have focused adversarial coverage. Retained nth endpoints and expanded
event histories are not cache payloads.

The prime CLI reaches `nth_prime_at_or_after` → `PrimePrefixRank` → the canonical
iterative `CoprimeRankDAG`. Reuse stores admitted consecutive prefixes and demanded
Phi roots, keyed by the entire factor prefix and query bound. Source discovery
publishes its admitted prefix rather than every interior count. Already-covered
warm requests do no repeated factor discovery; smaller queries admit only their
needed prefix. Shared factor retention is capped at 4,096 stages. Key construction,
admission, local allocations and shared retention/activity are reported separately.
Reduced budgets cannot be bypassed by a previously expensive cached horizon.
The issuer is private to the canonical producer: this is an in-process ownership
boundary, not a claim of protection from arbitrary trusted code modifying private
module state. No sieve bitmap, parent primorial gaps or primality oracle is used.

Collatz accelerated queries discover each admitted germ transition once and
jointly publish the event root and ordered physical support `O E^valuation`.
The event arena, transition cache and support arena allocate retained stores
through ledger factories. Source-bound snapshots reject substituted roots,
foreign children and changed target bindings before observation. Requested
accelerated observations share one query context. Ordinary nth values and their
physical clocks remain on the existing physical owner; the published support is not
yet the common consumer for every observer.

Antihydra spacetime observations batch identical translated section images modulo
the demanded coefficient ring. The key retains signed spatial/time phases and
typed event ports until prime evaluation. Batch storage and translation work are
charged and released. Guarded source traversal, overwrites and directional labels
retain their existing semantics. This reduces counted translation work in one
installed comparison, but
its median latency was 235.46 ms versus 224.25 ms for the previous wheel. It still
visits every retained macro return and earns no powered-performance closure.

## Independent review and remaining obligations

| Gate | Finding and missing evidence |
|---|---|
| Shared reuse | Independent audit accepts public lease authentication, full prime keys and charged key construction. Complete executable/cache refinement remains open. |
| Prime | Numerical Phi, memo-update, prefix restriction, rank/bisection and finite local Enter/Finish execution lemmas are checked. Full Python loop/shortcut/lease/budget/cleanup refinement and an unbounded stage-growth bound remain separate obligations. |
| 196 | Warm public-point reuse is authenticated. Cold N=64 still makes 2,745 continuation requests and 9,372 concrete operations. Both carry ports, active extent, growth seam and mirror orientation must close under subsequent image composition without reading the intermediate word. No such construction/bound was delivered. |
| Collatz | Event observers use the published event arena while ordinary physical execution has a separate owner. Ledger-backed `PhysicalSupport.specialize` still refuses without a charged workspace. Chronological event/support/source correspondence and common-consumer refinement remain open. |
| Antihydra | Batched images still perform N retained support visits. Source-generated composed images with overwrite/read semantics, guarded first-failure refinement and demanded-projection homomorphisms remain open. The source-7 non-halting certificate is a separate mathematical P0. |
| Fermat/Mersenne | The candidate-bound transverse descriptor has no compact unit/annihilator evaluator. The live terminal path remains UNKNOWN where no compatible residue is available. Existing product/gcd theorems assume the missing publisher; a tree over every progression leaf does not satisfy compact construction. |

The special-number audit found that the Fermat progression window for n≥4 is
`2^(2^(n-1)-n-2)-1`. Existing evaluation and sibling product updates still depend
on that window. No poly-compressed-input bound or source-derived replacement was
established. Proper factors are printed only from checked compatible residues;
classical primality fallbacks and supplied-factor shortcuts remain prohibited.

No counterexample to the full source-bound shadow-cylinder construction was
established. Failed carry-only or mirror-only projections do not refute it.
These missing objects remain required work, not assumed hypotheses that can be
hidden in a passing theorem.

## Validation

Final measurements and source fingerprints are recorded in the accompanying
[evidence directory](../results/current/performance-agent-closure-2026-09-13/).
Performance comparisons distinguish fresh installed processes, repeated requests
in one process, and cache bypass. The full existing growth manifest and explicit
P0 tests keep their original workloads, assertions and resource limits. A timeout,
missing row, incomplete refinement or unavailable constructor leaves its gate red.

Final frozen validation records **5,127 unit passes and four unchanged failures**
in 268.49 seconds; explicit P0 remains **15 failed / seven passed**. The full
105-trial growth manifest has **80 completed samples and 25 timeouts**, so its
status is RED and metric collection is incomplete. Paired prime latency gates
pass against both baselines. Authored-source typing, Ruff and policy pass; older
result-artifact whole-directory typing/Ruff failures remain separately recorded.
The temporal Isabelle build and its explicit parent-heap retry both time out at
35 seconds; prime, reverse/add, étale and Antihydra component builds pass. See the
[evidence index](../results/current/performance-agent-closure-2026-09-13/README.md)
for the source fingerprint, full logs, measurements and independent audit.
