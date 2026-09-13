# Skew, S-arithmetic, Hensel, twisted and tropical cylinder observers

The September 12 follow-up adds exact observer APIs to existing production
modules. This is component integration: it does not establish that the physical
CLI powers the proposed common shadow-cylinder morphism. It does not add
observer tuples to `ActionID`.
The supplied notes propose a common geometric quotient; their empirical counts
and universal factor-separation hypotheses remain research statements.

## Successor closure and its scope

The [endpoint-seam theorem](endpoint-seam-powering-audit.md) proves successor
congruence for exact endpoints of a deterministic map. It explicitly does not
prove sublinear cold evaluation or a smaller sufficient feature key. This
integration keeps that distinction: it adds views of existing actions rather
than admitting a new temporal certificate from sampled jets or tropical data.

The action remains the owner. A Hensel cylinder, carry jet, tropical minimum,
negacyclic sheet or gcd is produced only when demanded. Reading these views does
not change the action's interning key or its node count. Known Collatz event
programs can contain repeated subactions; their observers use that sharing.
Discovery of the applicable future valuation program remains separate.

## Collatz's single matrix and its projections

[`CollatzClockObservers`](../src/number_compiler/sequences/collatz/clock_observers.py)
folds the existing `CollatzEventArena` DAG with the generic
[`SkewTransfer`](../src/number_compiler/arithmetic/fields/skew_transfer.py) law.
For chronological blocks A then B:

```
M = [ s^N  P ]       P_AB = s^N_B P_A + z^K_A P_B
    [  0  z^K ]      N_AB = N_A+N_B, K_AB = K_A+K_B.

P = sum_(j=0..N-1) s^(N-1-j) z^K_j,  K_0=0.
```

No expanded polynomial is retained. Modular evaluation and finite polynomial
quotients use the existing modular-power and `CyclotomicRing` owners. The query
visits each reachable uncached node once for the demanded specialization; queries report cumulative node,
composition and ring-power composition counters on the observer object.
Different queries currently perform separate folds. These counters measure
operations, not constant bit-cost arithmetic.

| Query | Exact observation |
| --- | --- |
| `modular` | Matrix specialization at s,z modulo the demanded integer |
| `hasse` | Coefficients of P(s,1+y) modulo y^degree: Hasse derivatives at z=1 |
| `polynomial` | Arbitrary supported quotient, including the primary jet at z=-1 |
| `twisted` | P modulo z^width-sign, sign either +1 or -1 |
| `hensel_pullback` | Exact preimage of a target dyadic cylinder, including integrality |
| `tropical` | Minimum alpha*(N-1-j)+beta*K_j over the positive polynomial support |
| `clock` | Physical ticks N+K and exact prime exponents of the slope |
| `factor_observation` | gcd(modulus,P(3,2)); a proper factor when that gcd is proper |

The tropical query uses the existing min-plus matrix implementation. It is a
support-function query, not a claim that the Newton hull determines coefficients,
future branches, cancellation or CRT support.

At s=3,z=2, the matrix relation is `3^N*x+P(3,2)=2^K*y`.
The real slope is `3^N/2^K`, its 2-adic norm is `2^K`, and its 3-adic norm is
`3^(-N)`: their product is exactly one. The implementation stores the exponents
and does not approximate logarithms or construct huge rational powers.

Hensel pullback evaluates the offset only modulo `2^(K+q)` for target precision
q. It reuses `HenselCylinder.pullback_modular`, now also the owner behind the
existing exact-coefficient pullback. It never lowers the complete affine offset.
The existing Hensel precision budget still applies. A universal target demands
integrality alone; an odd target adds a condition that must not be discarded
when using the action as an exact accelerated-event program.

Example:

```python
from number_compiler.sequences.collatz.power import CollatzEventArena
from number_compiler.sequences.collatz.clock_observers import CollatzClockObservers

arena = CollatzEventArena()
action = arena.power(arena.event(2), 10**100 + 17)
views = CollatzClockObservers(arena)
residue = views.modular(action, 257).offset
jet = views.hasse(action, degree=2, modulus=16)
```

This evaluates the supplied repeated event action. It does not assert that an
arbitrary Collatz seed follows that event program.

## Decimal skew already has one production owner

The decimal LT/EQ/GT plus mod-9 readout remains in
[`skew_residue_laws.py`](../src/number_compiler/arithmetic/formula/skew_residue_laws.py),
with the existing `Reverse_Mod9_Skew` Isabelle theory. Its 19 reachable pairs
encode the pair coefficients 0..18; they are not a nine-state temporal quotient.
The normalization consumer derives digits from the admitted carry domain,
residue and incoming carry. This integration preserves that owner and its
removed-state boundary rather than reintroducing those coordinates as keys.

## One signed-cylinder observer for 196, Fermat and Mersenne

[`TwistedCylinderProjection`](../src/number_compiler/arithmetic/polynomials/twisted_observer.py)
reuses the existing cyclic and negacyclic fold kernels. It accepts streamed
coefficients and retains only the demanded sheet. Arithmetic evaluation is
admitted only when `radix^width = sign mod modulus`. At a compatible modulus,
folding commutes with evaluation. Rejecting incompatible moduli prevents a
spatial polynomial quotient from silently changing arithmetic factor support.

`ArithmeticTile.step_with_twisted_projection()` consumes the same transient
square/trace-square field as the primary carry-jet query and returns the existing
step with its convolution counters. For the supplied étale root D:

- Fermat's field A represents D^2.
- Mersenne's field A represents D^2-2; query support with `constant=2` to observe
  the square rather than the trace-square offset.

Mixed-root controls recover 641 from F5 and 23 from M11 via these fields.
The test uses CRT to prepare its input root; production neither enumerates
factors nor claims to construct that root from the candidate. The earlier
[nontrivial-root factor theorem](research/power-numbers/etale-isabelle-proof.md)
remains the basis for guaranteed output once an appropriate root is supplied.

`ReverseAddPoweredTerm.mirror_obstruction()` evaluates the target mirror defect
on the ladder `z^d-1`, `z^d+1`, `z^(2d)+1`, ... . It returns the first nonzero
sheet. If a zero sheet's width reaches the target width, the polynomial itself
is zero and the current target is a palindrome. A zero smaller sheet is never
accepted as a zero-polynomial certificate. The method consumes the existing
target-output owner and does not reconstruct an integer or replay an independent
history.

For positive generations the current implementation completes the target DAG,
then folds shared clipped subtrees separately for each demanded sheet. It makes
zero scalar point queries; that does not make target construction free. The final
sheet may be as wide as the target. This optional certificate query is not installed over
the faster existing early mirrored-digit comparison. Neither query proves that
196 avoids palindromes for all future times. The [196 and Collatz ray record](cylinder-helix-rays.md)
retains the independently reproduced bounded experiment and helix optimization.

## Tropical divisor output and the meaning of free factors

The exact factor-free `TropicalDivisorState` has moved from the research module
to [`arithmetic/fields/tropical_divisor.py`](../src/number_compiler/arithmetic/fields/tropical_divisor.py).
Research imports this production owner. Factor-backed axes, slot searches and
source-work audits remain in research.

An observation is `d=gcd(N,a)`. Saturated multiplication is `gcd(N,d1*d2)`,
meet is gcd and join is lcm. No factorization is required for those operations.
`proper_factor` emits d precisely when `1<d<N`. This is downstream arithmetic
output, not a field added to a temporal action key.

Arithmetic addition is not tropical meet: modulo 15, both 1 and 4 have unit
support, but 1+4 exposes factor 5 whereas 1+1 does not. Saturation also loses
multiplicity overflow, so its multiplication cannot be inverted to delete
observations. The research negative controls are preserved.

“Free” means no additional temporal replay or factor enumeration after the
relevant observation is available. Observation evaluation, polynomial arithmetic,
gcd and output still cost work. A proper split is not guaranteed for arbitrary
Collatz or reverse/add observations. Successor closure alone does not prove the
Fermat/Mersenne nontrivial-section existence or terminal pullback obligations.

## Research provenance and unresolved geometric quotient

The supplied Collatz note reports 8,192 odd 14-bit sources and an eight-event
depth-word partition with 7,099 classes and 495 successor-conflicted classes.
Appending residues mod 3,9,27,81 reportedly gives respectively 7,759, 8,113,
8,187, 8,192 classes, with 255,65,5,0 conflicted classes. The last case has no
aliases. These supplied counts are not independently reproduced by this change.
They motivate derived observers rather than an expanding Cartesian key.

The proposed universal cylinder-germ groupoid, a minimal pullback-closed
observable algebra containing the terminal étale ideal, and separation of every
pair of CRT components are still theorem targets. In particular, arbitrary
linear determinants need not detect nonlinear Frobenius orientation. This
implementation does not identify its skew matrix with that unconstructed
universal nonlinear quotient.

A future promotion must demonstrate genuine aliases and successor/consumer
agreement on every admitted binding, while charging normalized-node growth and
poisoning exact midpoint construction. Passing those tests on a supplied
repeated event DAG does not prove them for arbitrary newly discovered rays.

See the [CLI fixes and current proof boundary](cylinder-cli-release-fixes-2026-09-12.md)
for demanded CLI commands, work budgets, shared observation caches and the later
vector/min-plus refinement theorems. Earlier validation below records the original
integration scope.

## Isabelle and validation

The `Etale_Primary_Carry` session now includes `Skew_Cylinder_Observers` and
`Twisted_Support_Observers`. They formalize matrix associativity, homomorphic
observer composition, the clock append/offset law, transport composition,
the S-arithmetic product formula, contravariant demand composition, compatible
twisted evaluation, invariance of affine modular demands under coefficient
reduction, exact saturated-gcd multiplication and current-target mirror
obstructions. Each exported theorem group rejects oracle dependencies.

Tests compare all Collatz projections with an independent explicit polynomial,
check Hensel preimages against exact transport, poison event execution and affine
lowering through A1..A1024 and a duration above 10^100, preserve node identity,
check arena ownership, verify compatible arithmetic evaluation, and exercise
actual Fermat/Mersenne and powered reverse/add consumers. This is formal algebra
plus differential Python validation, not extracted Python correctness.
