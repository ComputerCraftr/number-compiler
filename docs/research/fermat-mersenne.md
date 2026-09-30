# Fermat and Mersenne square actions and terminal certificates

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
[`Special_Factor_Progressions.thy`](../../proofs/isabelle/etale/Special_Factor_Progressions.thy)
proves the prime-factor progression restrictions for admitted Fermat and
Mersenne candidates. These restrict possible factors; they are not a primality
decision procedure.

[`Primary_Carry_Jet.thy`](../../proofs/isabelle/etale/Primary_Carry_Jet.thy)
proves mod-16 reduction, recovery/defect inverses, shift composition, and the
carry-normalization coefficient identity. A carry jet derived from a supplied
root does not construct that root from the candidate.

[`Transverse_Frobenius_Holonomy.thy`](../../proofs/isabelle/etale/Transverse_Frobenius_Holonomy.thy)
proves indexed transverse unit criteria and Fermat/Mersenne prime-bit theorems
under the stated family progression and product construction. It also proves a
nonunit slot can yield an annihilator or factor. The theorem does not compactly
compute the indexed product.

[`Special_Frobenius_Defect_Bridge.thy`](../../proofs/isabelle/etale/Special_Frobenius_Defect_Bridge.thy)
connects terminal defects and gcd criteria and proves that a proper terminal gcd
prints a factor. This is conditional on obtaining the terminal defect.

## Known invalid shortcuts

[`Runtime_Cylinder_Refinement.thy`](../../proofs/isabelle/etale/Runtime_Cylinder_Refinement.thy)
records three explicit boundaries: a zero root does not decide M11, the M11
Frobenius coordinates need not be roots, and nonzero F5 coefficients need not
split. The dedicated
[`Mersenne_Zero_Key_Counterexample.thy`](../../proofs/isabelle/etale/Mersenne_Zero_Key_Counterexample.thy)
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
prove prime. Pépin and Lucas–Lehmer remain research oracles rather than hidden
fallbacks.

## Production and reproduction

- **Implemented owner:** [sequences/power_numbers/transverse_pullback.py](../../src/number_compiler/sequences/power_numbers/transverse_pullback.py).
- **Checked theorem:** the named Isabelle results above apply with their explicit premises; use the [proof index](../proofs.md) for source statements, sessions and oracle audits.
- **Finite experiment:** bounded test comparisons establish only the tested sources and horizons.
- **Construction-cost status:** The semantic progression criterion is conditional on terminal evidence. Compact candidate-derived extraction and its construction bound remain open.

Run the exact executable checks (including validation-marked assertions):

```console
python -m pytest -o addopts='' tests/validation/proofs/test_shadow_jet_primality_release.py
```
