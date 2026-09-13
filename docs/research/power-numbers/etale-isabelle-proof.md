# Étale carry-jet formalization

The Isabelle session `Etale_Primary_Carry` is in
[`devtools/proofs/isabelle/etale`](../../../devtools/proofs/isabelle/etale).
Its statements distinguish the exact one-step root-variety experiment from the
unconstructed terminal clock pullback. Each theory checks its exported theorems
for oracle dependencies, and the session disables `quick_and_dirty`.

The current release target is the transverse progression holonomy, not the
finite zero-section key. Its exact formula and remaining compact-evaluator
obligation are in the
[current ledger](../../cylinder-p0-release-gates-2026-09-12.md).
`Special_Factor_Progressions.thy` now checks the Fermat and Mersenne progression
admission theorems. `Transverse_Frobenius_Holonomy.thy` formalizes the binomial
transport and complete-window unit criterion. The root-variety material below
remains a separate, narrower result and must not substitute for that target.

The session inherits standard `HOL-Number_Theory`. After that standard session
is available, select the project session with
`isabelle build -j 1 -o threads=1 -d devtools/proofs/isabelle Etale_Primary_Carry`.
The release proof check retains its 35-second/4GiB process guard. Dependency
setup is recorded separately from that check.

## Exact experiment being formalized

For a fixed candidate `N=2^w-s`, take a canonical residue `D` satisfying
`D*(D+2)=0 mod N`. Choose `Dhat` from `D` and `-D mod N` by minimum canonical
binary Hamming weight, breaking ties by smaller integer. The key's deck bit is
`[Dhat != D]`. The exceptional Fermat residue `-1` has the signed word
`(-1,0,...)`; that output/input chart convention is distinct from the deck bit.

For the digit polynomial `d(z)` of `Dhat`, the coefficient word is exactly

```
Fermat:   A(z) = d(z)^2       mod (z^w+1)
Mersenne: A(z) = (d(z)^2 - 2) mod (z^w-1).
```

Normalize `a_i+c_i=r_i+2*c_(i+1)` with `c_w=s*c_0`, using the canonical output
representative. Put `Q(z)=sum c_(i+1)*z^i`. The key is
`(deck,c_0,Q(-1) mod16,Q'(-1) mod16)`; the outgoing seam is redundant once the
family is fixed.

The user clarified that all 320 input rows came from factor-backed enumeration
of CRT orientations on 45 complete sheets. Admission imposed the root equation,
with no temporal `L` restriction. Thus these are tests of the quadratic root
variety, not tests of a terminal Pépin/Lucas–Lehmer construction. Corpus counts
are supplied observations, not a machine-checked universal theorem.

## Mersenne zero-section argument

For odd width `w` and `N>3`, define the nonnegative folded-square value

```
S = sum_(i,j<w) d_i*d_j*2^((i+j) mod w).
```

The zero root has deck zero and cyclic seam `(-2) div N = -1`. Matching that
seam gives `(S-2) div N = -1`, so `S<=1`. If a bit `d_i` is one, its diagonal
summand implies `2^((2*i) mod w)<=1`; hence `w` divides `2*i`. Oddness of `w`
forces `i=0`. Thus the selected word represents at most one. When the deck is
zero it represents `D` itself, and the root equation excludes `D=1`, since
`N>3` cannot divide three. Therefore `D=0`.

This proves a Boolean zero-section separation result without needing the two
small jet coordinates. It does not prove injectivity between two nonzero roots.
The signed coefficients of the Fermat fold invalidate the nonnegativity step,
so this argument does not establish the Fermat zero-section.

## Other formal obligations

`Primary_Carry_Jet.thy` proves the carry normalization identity, the invertible
jet/normalization-defect conversion in `(Z/16)[y]/y^2`, and associativity of the
full endpoint-plus-jet action. These are algebraic correctness results, not a
proof that every production Python implementation refines Isabelle.

`Etale_Primality_Bridge.thy` proves:

- For `N>1`, primality is equivalent to every prime divisor having maximal
  stride `N-1 | q-1`.
- For `N=B^2+1`, `B>0`, primality is equivalent to `B | q-1` at every prime
  divisor `q`.
- For `N+1=2*C^2`, `C>1`, primality is equivalent to
  `2*C | q-1` or `2*C | q+1` at every prime divisor `q`.
- Every canonical root `D*(D+2)=0 mod N`, with `N>2` and `D` outside
  `{0,N-2}`, has a proper gcd with `N`. That gcd gives an exact nontrivial
  factorization and proves compositeness. The more general coefficient-gcd
  theorem applies whenever a proper gcd is supplied.

The production `factor_from_etale_root(N,D)` checks the canonical range and
root equation, then returns an available proper gcd. This is a direct consumer
of the root-factor theorem; it does not supply the root-construction premise.
`ArithmeticTile.step_with_primary_carry_jet()` exposes the exact experiment key
from the existing one-square field and retains the step's work counters.

The two smaller thresholds use the fact that a composite number has a prime
divisor at most its square root. The universal quantification over prime
factors is a theorem premise, not an implementation that secretly factors `N`.

## Earlier root-variety construction boundary

An extractor following this earlier root-variety route would need a terminal
defect and proofs that (1) it satisfies `D*(D+2)=0 mod N`, (2) its zero/support
section expresses the required all-local bit, and (3) the compact clock
pullback returns the exact carry key above with its claimed work bound. The
supplied experiment defines none of these constructions. Isabelle cannot infer
them from the finite orientation corpus. For example, `D=0` belongs to the
root variety even for the composite `M11=2047=23*89`. Identifying that root
alone cannot classify the candidate; the terminal/all-local relation is essential.

The Fermat zero-section and universal support separation remain open here.
Factor printing is conditional on obtaining a proper support/annihilator; no
unconditional factor recovery or cost-free construction is asserted. Existing
production `unknown` results and explicit classical fallback accounting remain
necessary at this boundary.

Build with:

```sh
/Applications/Isabelle2025-2.app/bin/isabelle build -j 1 \
  -o naproche_server=false -d devtools/proofs/isabelle Etale_Primary_Carry
```
