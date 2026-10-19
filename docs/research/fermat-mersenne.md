# Fermat and Mersenne square actions and terminal certificates

[Current release gates](../release-status.md) own validation status; this page
records mathematical scope and source connections.

Status: **shared square arithmetic and conditional terminal theorems are
checked; the candidate-derived compact terminal extractor remains missing**.

Fermat and Mersenne use the shared square tile with different rings and terminal
observers. Fermat is negacyclic and tests the `-1` terminal; Mersenne is cyclic,
uses the `x^2-2` trace recurrence, and tests zero. A sign quotient valid for the
Mersenne zero observer cannot be copied to Fermat's sign-sensitive observer.

## Reading guide

- **Definitions:** `F_n=2^(2^n)+1` and `M_p=2^p-1`. An admitted etale defect satisfies `D*(D+2)=0 mod N`; a supplied root is not a candidate-derived terminal certificate.
- **Checked theorem:** indexed transverse unit/annihilator criteria imply the corresponding terminal conclusions under their construction premises.
- **Implemented construction:** compact ordinary terms and checked conditional factor output are available independently of primality resolution.
- **Open obligation:** construct compact terminal evidence from the candidate and connect it to classification without enumerating progression leaves or replaying classical tests.

## Checked arithmetic

The maintained implementation contract is in
[arithmetic square tiles](../architecture/arithmetic-square-tiles.md).
[`Special_Factor_Progressions.thy`](../../proofs/isabelle/integration/etale/etale/Special_Factor_Progressions.thy)
proves the prime-factor progression restrictions for admitted Fermat and
Mersenne candidates. These restrict possible factors; they are not a primality
decision procedure.

[`Primary_Carry_Jet.thy`](../../proofs/isabelle/integration/etale/etale/Primary_Carry_Jet.thy)
proves mod-16 reduction, recovery/defect inverses, shift composition, and the
carry-normalization coefficient identity. A carry jet derived from a supplied
root does not construct that root from the candidate.

[`Transverse_Frobenius_Holonomy.thy`](../../proofs/isabelle/integration/etale/etale/Transverse_Frobenius_Holonomy.thy)
proves indexed transverse unit criteria and Fermat/Mersenne prime-bit theorems
under the stated family progression and product construction. It also proves a
nonunit slot can yield an annihilator or factor. The theorem does not compactly
compute the indexed product.

[`Special_Frobenius_Defect_Bridge.thy`](../../proofs/isabelle/integration/etale/etale/Special_Frobenius_Defect_Bridge.thy)
connects terminal defects and gcd criteria and proves that a proper terminal gcd
prints a factor. This is conditional on obtaining the terminal defect.

## Known invalid shortcuts

[`Runtime_Cylinder_Refinement.thy`](../../proofs/isabelle/integration/etale/etale/Runtime_Cylinder_Refinement.thy)
records three explicit boundaries: a zero root does not decide M11, the M11
Frobenius coordinates need not be roots, and nonzero F5 coefficients need not
split. The dedicated
[`Mersenne_Zero_Key_Counterexample.thy`](../../proofs/isabelle/integration/etale/etale/Mersenne_Zero_Key_Counterexample.thy)
shows the normalized zero key is not a universal prime/composite classifier.
These witnesses reject the named shortcut, not the indexed holonomy criterion.

Five-bit folded-square, radix-64 mirror, and deck measurements are bounded
research observations. Class counts or a supplied compatible residue do not
authorize the candidate's terminal bit.

## Production gate

Production needs a candidate-derived, source-clock-bound compact evaluator for
the transverse unit/annihilator information, a proof that it equals the indexed
criterion, and a construction/demand bound that does not enumerate the whole
progression window. When unavailable, primality remains `unknown`. A separately
checked proper divisor may prove composite, but failure to find one does not
prove prime. Classical modular Pépin and Lucas–Lehmer loops remain research
oracles rather than hidden fallbacks.

The reconstructive [integral witness reference](../../devtools/verification/fermat_integral_ideal_reference.py)
lives in development tooling. Its bounded binomial fold and signed carry
cochain are useful independent research checks, but are no longer a production
`FermatNumberSpec` method. The reference's 65,536-term budget admits F4's 32,769
coefficients and rejects F5 before constructing its source. It does not establish
a compact arbitrary-index constructor or close the production gate above.

The explicit [factor-search reference](../../devtools/verification/special_factor_reference.py)
also lives in development tooling. Its modular divisibility witnesses and finite
factor-slot searches are not production primality fallbacks. Bounded radix
observations remain available as explicitly demanded source information.

The NC12 source/fold audits distinguish a compressed source from a compressed
primality computation. A four-node ternary grammar for `3^(2^t)` still needs
`t` candidate-modulus action squares when its repeat is evaluated by generic
modular composition. That reference is not a production fallback. Likewise,
fixed low-radix ports at levels 15 and 75 can coincide while their remainders
modulo 65,537 are respectively -1 and 1. A local pivot, Walsh or radial observer
cannot supply the missing global signed-order character by itself.

`GuardedBinarySource` admits and copies a supplied binary SLP once. Guarded
uniform interval toggles update its Fermat fold with signed endpoint terms;
the fold and tripling observation use the shared iterative SLP traversal.
Neither the input grammar nor a caller-supplied pivot label certifies that the
word is `3^(2^t)`. The tripling residue is a separate observation, not an SLP
action with the original word's length.

`FermatNumberSpec.demand_dyadic_pivot_moore` exposes bounded fixed-offset
ports of the normalized unit `u_t=(3^(2^t)-1)/2^(t+2)`, for `t>=1`.
The exact recurrence `u_(t+1)=u_t+2^(t+1)*u_t^2` makes low fixed windows
stationary; large occurrence levels therefore do not require a level-sized
loop. Moving windows retain an explicit precision bound. Observer identities
include the selected offsets, and the external level remains occurrence data.
These ports do not replace the unresolved global source-to-fold producer.

The checked [binomial source theory](../../proofs/isabelle/integration/etale/etale/Fermat_Binomial_Negacyclic_Source.thy)
proves the finite negacyclic source identity. The [integral ideal bridge](../../proofs/isabelle/integration/etale/etale/Fermat_Integral_Ideal_Pepin_Bridge.thy)
proves signed-carry telescoping and the sufficient Pépin implication for Fermat
indices at least one. The final theorem assumes that the coefficient vector
equals that exact fold and satisfies the signed carry chain. A refinement of
the Python streamed coefficient recurrence and certificate encoding remains
separate; the theorem is not an unconditional production-checker refinement.

## Production and reproduction

- **Implemented owner:** [sequences/power_numbers/transverse_pullback.py](../../src/number_compiler/sequences/power_numbers/transverse_pullback.py).
- **Checked theorem:** the named Isabelle results above apply with their explicit premises; use the [proof index](../proofs.md) for source statements, sessions and oracle audits.
- **Finite experiment:** bounded test comparisons establish only the tested sources and horizons.
- **Construction-cost status:** The semantic progression criterion is conditional on terminal evidence. Compact candidate-derived extraction and its construction bound remain open.

Run the exact executable checks (including validation-marked assertions):

```console
.venv/bin/python -m devtools.checks.release --suite unit --select tests/validation/proofs/test_shadow_jet_primality_release.py
```
