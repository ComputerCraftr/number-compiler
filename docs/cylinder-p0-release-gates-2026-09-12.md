# P0 powered-cylinder release gates — 2026-09-12

Release is **blocked**. The user's accepted factor contract is conditional:
print a checked proper factor when one is available. Universal free factor
discovery is not the acceptance condition. A failed split must not be turned
into a primality decision. Work to search for another witness remains charged.

The following are P0 release obligations, not optional future improvements.
No historical P1/P2 heading in the earlier audit downgrades this release hold.

## Transverse-germ restoration — latest release target

The September 12 retest supplies the primality-sensitive object explicitly:
`Delta_N(z,t)=(z+t)^N-z^N-t^N`, with
`(k+1)c_(k+1)=-k*c_k (mod N)`. Its transverse nonunit support must remain
available in the common source-bound cylinder. The finite primary carry key
does not replace that support. The M11 zero-root key is no counterexample to
this germ or its proposed compact constructor.

Set `C=2^(n+2)` for Fermat `n>=2`, or `C=2p` for odd prime Mersenne exponent
`p`; `W=(isqrt(N)-1)//C`, and `H=product(1+C*m, m=1..W) mod N`.
The restored semantic criterion is **prime iff gcd(H,N)=1**. This has the
opposite gcd polarity from the auxiliary defect `E` whose all-pass packet is
`gcd(E,N)=N`; feeding `H` to that packet would be incorrect.

| P0 | Assigned owner and required evidence |
| --- | --- |
| Transverse semantic proof — CHECKED | `support_semantics_proof` and `remove_classical_production`: coefficient transport, closed family progression admission, exact indexed square-root product criterion, nonzero ring annihilator, and conditional proper-factor extraction all pass Isabelle. The empty product is 1. A whole-product gcd equal to N is not a printable proper factor. This is a semantic proof, not the compact evaluator or its runtime refinement. |
| Compact transverse construction | `remove_classical_production`: derive the same unit/annihilator information from the admitted common cylinder without scanning W coordinates, supplied factorization, or reference primality recurrences. Preserve ordered source binding and the transverse support across powered composition. |
| Runtime and CLI refinement | Production owner plus root: prove and test that the CLI reads this exact constructed support; primary carry, twisted lanes, jets, and annihilator are consumers of that owner. No default enumerative fallback. |
| Construction cost | Root plus production owner: record atom evaluations, multiplication work, retained state and cold construction cost. A W-leaf product tree uses W atoms and W-1 multiplications despite logarithmic depth; that is a semantic oracle, not release completion. |

Mandatory semantic controls are F4 CLEAR, F5 SPLIT(641), M11 SPLIT(23), and
M13 CLEAR; additionally M11 must recover `binom(2047,23) mod 2047=89` and
`23*89=2047`. Semantic controls and the unchanged compact-production gates are
separate: passing the former by enumerating the window does not pass the latter.
The existing research owner is
`devtools/experiments/power_numbers/special_transverse_jet.py`.

The factor-progression sub-obligation is now checked:
[`Special_Factor_Progressions.thy`](../devtools/proofs/isabelle/etale/Special_Factor_Progressions.thy)
derives both family progressions from prime-divisor assumptions, with no
supplied factorization and no theorem oracle dependencies. The full
Etale_Primary_Carry session passed under the unchanged 35s/4GiB guard.
The connected
[`Transverse_Frobenius_Holonomy.thy`](../devtools/proofs/isabelle/etale/Transverse_Frobenius_Holonomy.thy)
also checks exact slot/index-product equality and public Fermat/Mersenne
criteria `prime N iff gcd(indexed_H mod N,N)=1`, using only the stated family
admission assumptions. For nonunit H it proves that `a=N div gcd(N,H)` obeys
`0<a<N` and `H*a=0 mod N`, including the full-gcd case. The final combined
session passed in 21.41s with 479MB sampled peak and no oracle dependencies.
This closes the semantic proof, not compact evaluation or CLI refinement.

## Assigned implementation and review ownership

| Owner | Assigned blockers |
| --- | --- |
| `support_semantics_proof` | Fermat/Mersenne candidate binding, exact mod-16 recovery mathematics, separation and primality proofs; adversarial checks against proving only a supplied-root projection. |
| `remove_classical_production` | Fermat/Mersenne production recovery and CLI classification, proper-factor output, bounded certificate admission, and recurrence exclusion; independent 196 two-port constructor and runtime audit. |
| `bound_clock_proof` | Shared executor and Collatz source-admitted powered construction, genuine output publisher, ordered support preservation, runtime refinement and powered performance gates. |
| Root coordinator | Cross-owner integration, proof builds, installed-package checks, frozen-source release and retention evidence, and adversarial review of claimed completion. |

Assignment does not discharge a gate. Completion requires executable evidence
and a theorem about the same source-bound construction used by production.

**Production recurrence prohibition:** Pépin and Lucas–Lehmer are research
oracles only. They may not supply a production answer when shadow-cylinder
recovery is missing. The transverse unit/annihilator must be recovered from
the candidate's admitted powered shadow action and connected to the primality
bit by a refinement proof. The mod-16 jet is a projection of that same owner;
it is not a substitute for transverse support. A key computed from a supplied
root does not close this gate. Optional checked factor output is separate
from prime-bit recovery.

The executable gate
`tests/validation/proofs/test_shadow_jet_primality_release.py` requires default
candidate classification without recurrence, carrier enumeration or an extra
factor probe. It remains failing while recovery is unavailable; UNKNOWN unit
tests are failure-handling checks, not release acceptance.

The ordinary unit test
`tests/projection/test_idempotent_output.py::test_source_compiler_is_theorem_free_and_cheap_shapes_resolve_impossible_sheets_first`
also requires F4 `require_concrete=True` to return a resolved value. It still
fails at that assertion while the evaluator is absent. The assertion is
retained; accepting `GUARDED` there would conceal a coverage blocker.

Final runtime checkpoint: 126 focused regression tests, strict mypy on 1,263
files, and the rebuilt installed-wheel check pass. The final primality
selection still has nine failures (eight API/CLI assertions plus that ordinary
F4 unit assertion). The earlier full-unit run hit the unchanged 300-second
guard; subsequent selected repairs do not clear that full-suite gate. See the
[recorded evidence](../results/current/shadow-recovery-audit-2026-09-12/README.md).

The [support-owner repair](support-owner-repair-2026-09-12.md) preserves ordered
physical support in research consumer normalization. Its Isabelle support
semantics and component tests pass. It neither supplies the general production
constructor nor clears any of the four-family gates below.

| Gate | Missing integration and required evidence |
| --- | --- |
| Fermat/Mersenne terminal construction | Construct the transverse holonomy unit/annihilator information from the candidate and its admitted source clock. Prove equality with the specified progression product, without enumerating its entire window, and with the value consumed by the CLI. No factor-backed CRT enumeration may supply the input. |
| Fermat/Mersenne decision observation | Prove the transverse unit criterion for both admitted families and refine the compact evaluator to it. The existing Mersenne zero-section assumes a quadratic root and carry premises; it does not construct the transverse germ. Universal primary-key injectivity is not the current acceptance condition. |
| Collatz physical output morphism | Connect the admitted source-bound cylinder action to the production compiler of physical output and cocycle. `radix4_source_action` is a derived carry view. `CollatzPoweredLocalTransferAdapter` currently delegates complete output to a callback implemented only by synthetic tests; `PoweredCollatzTerm` uses the separate primitive tile path. The bound common action must evaluate the demanded output correctly; neither a carry collision nor a discarded call/counter increment establishes this integration. |
| Collatz powered observer construction | Derive the parity/valuation events and their skew, S-arithmetic, Hensel and tropical observations through the admitted source quotient, with successor and consumer agreement. `--kind physical-clock` now reads the actual bound tile interface's retained ordered physical support and derives its weights. Other `observe collatz` views still discover an accelerated prefix sequentially. The full executor-to-clock refinement and general powered observer construction remain open. Fast observation of a supplied repeated event word does not certify discovery cost. |
| 196 powered construction | Instantiate the source-dependent carry/mirror quotient in the production powered route. Prove the decimal scan, terminal carry, growth/no-growth seam, active width and demanded output refinement. The abstract symmetric pair-list invariant does not establish these facts for the runtime. |
| Consumer refinement | Match the actual signed coefficient-vector fold, clipping, reverse orientation and mirror stopping rule, and the actual Hensel/tropical predicates. Preserve source/action/lease authority and account for all memo storage. Scalar polynomial evaluation alone cannot establish equality of cylinder vectors. |
| CLI performance and retention | Pass the unchanged unit time gate and the applicable opt-in powered release gates on frozen source, including real source-morphism use and completed-result retention. Preserve measured work counters and resource audits; do not relabel finite evaluations as zero work. |

## Why the existing proofs do not close these gates

The 320-row audit enumerated roots `D(D+2)=0 mod N` using complete CRT factor
sheets and then performed one folded family square. It had no terminal clock
admission. Its injective keys on those sheets cannot prove a candidate-derived
terminal construction or its complexity.

Nor is that root variety automatically a successor invariant: on M11, root 621
maps under the trace-square to 803, and `803*(803+2) mod 2047 = 1610`. The actual
M11 Frobenius coefficients 391 and 1474 are not quadratic roots, although their
coefficient gcd can yield a valid proper factor. Existing Isabelle lemmas
explicitly distinguish those premises. A new bridge must use the correct
invariant; assuming every such coefficient is an étale root would be false.

The successor congruence and temporal doubling laws prove exact endpoint
composition. They do not prove that a compact collection of observer values is
closed under successors, that it can be constructed cheaply from the source,
or that the CLI consumes that collection instead of rebuilding an endpoint.

The proof target is the common source-bound shadow-cylinder morphism, including
its skew composition and S-arithmetic interpretation. Carry domains, primary
jets, mirror sheets, Hensel coordinates and tropical values are derived
observers, not substitute temporal states. Distinct source occurrences may
share an ActionID and still yield different outputs when bound. A collision in
one observer therefore cannot refute the production morphism. The attempted
carry-only and mirror-only counterexample development has been withdrawn from
the Isabelle session and tests; it addressed the wrong invariant.

Required evidence is exact consumer agreement after binding the powered action
to the admitted source, together with preservation under normalized composition.
A counterexample must violate that law for the actual action, source binding,
admission conditions and demanded consumer. It must not discard the common
owner and compare only two evaluated shadows. No counterexample to that full
construction has been established here.

Finite powered output is the release target here. All-future Collatz and 196
ray claims remain separate research conjectures; finite traces cannot be
promoted into proofs of those claims.

## Concrete production boundaries

- `sequences/collatz/block_power.py` → `HashLifeBlockIndex` →
  `runtime_router.build_certified_field_application` → `PrimitiveTileKernelAdapter`
  is the current physical CLI route.
- `sequences/collatz/local_transfer.py` and `powered_local_codec.py` own the
  separate local carry-action interface. The missing complete-output compiler
  must bridge these semantics; the current test callback supplies fake outputs.
- `sequences/reverse_add/power.py` now sends positive-generation mirror demands
  through `LazyProjection` to `hashlife/observation/tile_cylinder.py`. That
  consumer folds a completed target DAG with shared clipped subtree summaries.
  It still calls `TileApplication.complete()`; this is not the missing cheap
  cold powered constructor.
- `api/cylinder_observation.py` reports the actual demanded observations.
  Its supplied-root F/M command is explicitly distinct from terminal discovery.
- `devtools/proofs/isabelle/etale/` owns the carry, zero-section, skew, Hensel,
  tropical and mirror-consumer lemmas. `Reverse_Invariant.thy` and the proof-side
  reverse spacetime engine do not yet refine the production powered constructor.

## Latest adversarial disposition

The proposed query-scoped action-child cache was removed after review found
stale authority hits, an omitted workspace-peak component, and an unapproved
payload-audit role. No cache-validation shortcut was retained to improve timing.

The new 196 consumer uses two reusable charged workspace accounts, clears their
contents after each sheet including failures, rejects interior padding, and
performs zero scalar point queries. Each demanded sheet folds the DAG again;
sharing is within a sheet, not a claim that every leaf is read once across the
whole ladder. CLI JSON exposes its work counters and peak/retained node counts.

`Cylinder_Vector_Refinement.thy` now proves the actual coefficient-vector shift,
append, clipping and mirror identities, including terminal-vector zero iff the
list is a palindrome. `Etale_Primary_Carry` builds with all oracle checks enabled.
This closes the scalar-only algebra gap for that consumer. It does not prove
the Python arena implementation, its source-to-target construction, or a bound
on cold construction work.

The ordinary-unit and opt-in release gates remain unpassed. The final frozen
unit run reached the unchanged 300-second guard near 98%, with no captured
failure markers and an unchanged source fingerprint. Targeted tests
and local timing samples do not change this status. See the
[fix and validation record](cylinder-cli-release-fixes-2026-09-12.md).
