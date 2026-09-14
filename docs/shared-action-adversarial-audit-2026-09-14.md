# Adversarial audit of CLI execution and shared-action proofs

**Release remains blocked.** Three independent explorer agents audited CLI slow
paths, Isabelle proof objects, and source/image/consumer invariants. The
coordinator checked their findings against current code and ran bounded CLI
traces, cache controls and owner-poison tests. Production and theory source were
not changed. The source fingerprint remains
`95353e85f969895d8c6cc2bc9ab08c9dc7ac48d892bd323e8b798038853d1b24`.

The common algebra is useful and partly present. The missing connection is the
checked path from each admitted source through the executable image constructor
to every production consumer. Repeating associativity proofs does not supply
that path. Nor does a common skew formula imply that every family has the same
admission, boundaries, event clock or étale-root predicate.

## Ranked production findings

1. **P0: ordinary prime generation does not use the rich powered successor
   action.** The actual path is `PrimePrefixRank.count_prime_interval` →
   `PrimePartialSuccessorQuery` → `PrimePartialSuccessorAdapter`. Its
   [children are absent](../src/number_compiler/sequences/prime/partial_successor_image.py:209),
   and its [composition and relative transport reject requests](../src/number_compiler/sequences/prime/partial_successor_image.py:297).
   The separate `PrimeSuccessorImageAdapter` supports those operations, but is
   disconnected from this CLI path. Poisoning `PrimeSuccessorActionArena`'s
   constructor leaves `prime --nth 100` successful with value 547. Thus a passing
   “shared core invoked” test proves integration of a primitive filter, not
   production skew squaring. The repair must make the finite-interval/count
   action closed under the required composition and preserve rank/select
   descent; blindly constructing the full old period would violate acceptance.

2. **P1: prime shared-cache access rebuilds complete prefix keys.**
   [Every shared lookup/publication](../src/number_compiler/sequences/prime/coprime_rank.py:213)
   constructs `tuple(self._primes[:depth])`. Local memo hits bypass this path.
   The traversal is explicitly charged, but still costs O(depth), followed by
   immutable-key validation and tuple hashing. A repeated CLI nth1000 request
   visits 668 prefix elements across 28 shared reads and 23 more in one write;
   repeated nth5000 visits 2,624 across 40 reads. An authenticated, interned
   consecutive-prefix identity could avoid rebuilding the same word, but needs
   extension, reset, stale/foreign authority and byte-accounting proofs. A
   sampled hash or unverified supplied-prime tuple is not an equivalent key.

3. **P0 performance: Antihydra observers amplify full-source validation.**
   [`_validate_result`](../src/number_compiler/sequences/antihydra/runtime.py:312)
   reconstructs every retained canonical cylinder and reapplies it to the
   source. Nested `require_source` calls in the
   [physical owner](../src/number_compiler/sequences/antihydra/runtime.py:62),
   [CLI observer](../src/number_compiler/api/antihydra_observation.py:52) and support
   projections repeat this work. At 256 returns, clock alone validates 256
   branch steps; clock+tape validates 1,536; clock+tape+Hasse validates 3,840.
   All use one arithmetic owner and omit value rendering. Duplicate names are
   correctly deduplicated. The missing optimization is authenticated reuse
   within a stable query/image scope, preserving mutation rejection; deleting
   validation or caching a mutable “valid” flag would be unsound.

4. **P0: Antihydra shared-core execution is bounded and observer-specific.**
   Its [adapter declines transported reuse](../src/number_compiler/sequences/antihydra/projection_core.py:386),
   and final projection visits every leaf return. Successful modulus-three
   spacetime queries at 64/128/256 returns perform 1/2/4 core applications,
   7/14/28 compositions, and 64/128/256 leaf visits. Clock, tape and Hasse controls
   do not call the common core. The existing total-arithmetic and guarded-TM
   distinction must survive migration; first-failure minimality is not proved
   by agreeing with a stored failure-prefix field.

5. **P1: Antihydra memo admission discards both memo tables on saturation.**
   The [physical](../src/number_compiler/sequences/antihydra/runtime.py:540) and
   [arithmetic](../src/number_compiler/sequences/antihydra/runtime.py:585) entry
   points clear both tables when their reserve margin is crossed. A capacity-64
   engine control evicts all 33 entries at once, including an unrelated physical
   cylinder. Revisiting the original residue then rebuilds eight arithmetic and
   eight physical branch steps. This is a demonstrated component policy, not a
   measurement of saturation at the default CLI capacity. The two methods also
   duplicate the postorder constructor skeleton rather than using the common
   source-image worklist. Consolidation must preserve optional physical roofs.

6. **P0: 196 still needs a temporal image accepted by the next action.**
   [`_ensure_image`](../src/number_compiler/sequences/reverse_add/publisher_projection.py:319)
   constructs the higher semantic runtime. Poisoning that runtime's constructor
   breaks `196 --nth 4`. A mirror query at nth8 records 88 higher continuation
   requests and 290 higher concrete operation evaluations. However, poisoning
   its `point` method does not affect these two controls: the audit does not
   claim point replay is universal. The missing object remains a successor-
   usable image with both context ports, dynamic active extent, growth seam and
   mirror orientation. Context summaries accepting only original source cells
   do not implement temporal substitution of the first emitted image.

7. **P0: Collatz physical and accelerated consumers remain separate.**
   The [event publisher](../src/number_compiler/sequences/collatz/source_publisher.py:185)
   advances one event at a time, with `allow_power=False` on its transition
   cache. Ordinary nth/clock queries use the existing physical path. Neither
   selected CLI control enters the common image core. A shared source germ must
   admit physical cuts inside a halving suffix, initial even runs, and the total
   1–4–2 cycle while accelerated event queries terminate at one. Wrapping an
   already expanded event list would preserve this construction gap.

8. **P0: Fermat/Mersenne are missing a constructor, not merely a speedup.**
   The candidate's compact transverse pullback does not compute its unit or
   annihilator in the general case. The CLI's conditional factor path and
   unresolved primality results do not pass through a shared image. The missing
   chain is candidate → admitted terminal germ → compact transverse information
   → checked classification/factor consumer. A semantic progression product, a
   product tree over all leaves, or a fast UNKNOWN result does not discharge it.

The generic core does structurally feed the first admitted image to the second
child. Its [postorder implementation](../src/number_compiler/hashlife/execution/source_bound_images.py:582)
is useful existing work. Adapter semantics, source preservation, transported
ports, and minimal failure descent remain additional obligations. Images also
remain outside the common leased process cache.

## Isabelle ownership and missing derivations

| Proof object | What is established | Missing production refinement |
|---|---|---|
| `Skew_Cylinder_Observers.skew_transfer` | Generic triangular composition, observer homomorphisms, demand pullback | Actual admitted source/image handles, constructor and consumers |
| `Antihydra_Mahler_Skew.antihydra_skew` | Numerator composition plus width and ledger minimum-prefix laws | Checked projection to the generic skew record; production cylinder and guarded TM interpretation |
| `Collatz_Clock_Jumps` affine effects and `Collatz_Cylinder_Constructor.cylinder_prefix` | Supplied-word laws plus a separate source-derived scalar constructor | Representation maps, actual physical/event publisher worklist and partial cuts |
| `Prime_Wheel_Executor.phi_postorder_completes` | Existence of an exact Enter/Finish run with valid memo | Deterministic Python shortcuts, shared hits, prefix extension, exception cleanup, selection and budgets |
| `Prime_Wheel_Skew_Actions` | Φ/Ψ cardinalities, phase transport/closure, seven-deletion implication | Lazy action construction, authenticated prefix discovery and CLI rank/select descent |
| `Reverse_196_Publisher_Refinement.reverse_two_port_publisher_refines_step` | Whole-list valid-pair one-step refinement, including growth | Executable temporal image, all transported channels and continuation-free composition |
| `Physical_Collatz_Bound_Consumer.compiled_publisher_refines_physical_emit` | Finite local table/selected-port equality | Actual source-bound support and full CLI consumer |
| `Antihydra_Family_Iteration`, `Antihydra_Macro_Grammar` | Arithmetic iteration and conditional literal port-word replay | Source-generated macro word, reads/overwrites, startup-to-section invariant, powered image and first failure |
| `Primary_Carry_Jet`, étale and transverse bridge theories | Carry identities and conditional root/unit/factor criteria | Candidate-derived terminal defect, exact production jet equality and compact evaluator |

The duplicate skew records are not shown inconsistent: the Antihydra record's
three numerator fields follow the same triangular law, with additional ledger
geometry. The actionable duplication is proving parallel laws without a checked
representation map or shared ownership. Extracting the generic semiring action
from its current étale/number-theory import chain would allow other sessions to
instantiate it without inheriting unrelated primality machinery. This is a
proposed dependency change, not a completed refactor.

Existing reuse must also be preserved.
[`Runtime_Cylinder_Refinement`](../devtools/proofs/isabelle/etale/Runtime_Cylinder_Refinement.thy:77)
already uses the imported `clock_transfer` and proves event-tree/list and
tropical-support relationships. It should not be described as a duplicate
independent skew algebra. Likewise the 196 whole-list theorem goes beyond its
earlier n<3 prefix control; the remaining gap is temporal construction, not
absence of any growth theorem.

The [prime executor's scope statement](../devtools/proofs/isabelle/prime_wheel/Prime_Wheel_Executor.thy:141)
explicitly excludes deterministic simulation of production branches and budgets.
The [generic temporal quotient](../devtools/proofs/isabelle/temporal_clocks/Temporal_Clock_Jumps.thy:9)
assumes the commuting successor equation. These are sound scoped results; using
them as proof that production constructs an admitted cheap successor would
assume the missing step. Oracle-dependency checks establish proof hygiene, not
that the theorem describes the production object.

The M11 zero-key theorem is also narrowly scoped. It constructs an arbitrary
zero root and its one-square carry key for a composite modulus. Its
[explicit limitation](../devtools/proofs/isabelle/etale/Mersenne_Zero_Key_Counterexample.thy:113)
says it does not refute a candidate-derived terminal publisher. It also does
not refute injectivity on the admitted root set. This audit found no exact
counterexample to the intended complete source-bound terminal construction.

## Common derivation required for closure

For each family, let `S` be an admitted source, `A` an action and `I(S,A)` its
published image. The common theorem should establish, on admitted domains,

\[
\operatorname{decode}(I(S,A))=\llbracket A\rrbracket S,
\qquad
I(S,A;B)\simeq I(I(S,A),B_{I(S,A)}).
\]

Here `B` consumes the transported source context and boundary. The relation
`≃` must preserve every successor-relevant field; it is not equality of a small
jet, phase summary or tropical projection. The proof dependency order is:

1. One chronological action algebra, cylinder transport, cocycle/minimum-prefix
   products and coefficient-map laws, reused by explicit representation maps.
2. Family-specific source admission and semantic action laws: prime consecutive
   prefix and forbidden residues; 196 two ports/growth/mirror; Collatz physical
   and event cuts; Antihydra total arithmetic plus guarded TM; special-number
   terminal/étale conditions.
3. Refinement of the actual iterative constructor, including the second-half
   input, canonicalization, memo key, leases, exception cleanup and first-failure
   descent. A supplied word or existential evaluator run is insufficient.
4. Consumer theorems `project_d(I(S,A)) = observe_d(⟦A⟧S)` for value, clock,
   directional moments, frontier support, Hasse, cyclic/negacyclic lanes and
   Hensel precision. Tropical/Newton views follow exact coefficient cancellation;
   tropicalization is not an unrestricted additive homomorphism.
5. Actual CLI demand sharing and separate bounds for discovery, image
   construction, arithmetic, validation, observations, output and retention.
   Shared algebra alone establishes no complexity bound.

Étaleness is a family-specific admitted predicate, not a premise available for
every 196/Collatz/Antihydra state. Antihydra's all-time source-7 barrier and
universal Goldbach multiplicity remain separate mathematical obligations even
after this common derivation is completed.

## Evidence and disposition

The [reproducible probes and audit scope](../results/current/shared-action-adversarial-audit-2026-09-14/README.md)
record actual CLI paths, negative controls, cache behavior and source hashes.
All probes use the unchanged 35-second/1-GiB guard. They are bounded call-count
and dependency checks, not replacements for the prior installed-wheel latency,
growth, Isabelle or P0 validation. No passing release assertion was added and
no required assertion was weakened. Findings above remain open implementation
and proof obligations; the audit does not claim their repair.
