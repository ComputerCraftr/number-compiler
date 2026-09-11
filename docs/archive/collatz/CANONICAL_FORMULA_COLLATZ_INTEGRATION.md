# Canonical Formula / Collatz integration

This release keeps the early-canonical powered compiler as the only production codebase.
No parallel S/M/B state package is introduced.

## One semantic state

The only persistent exact semantic state remains:

```text
FormulaRoot(exact positional coefficient/digit bit planes)
```

The useful S/M/B representation is exposed only as `SMBFormulaView`:

- `S` is the existing pair `FormulaRoot`;
- `M` is a derived ternary threshold-domain FormulaRoot;
- `B` is the derived single carry-border FormulaRoot.

The view is cached by `(base, canonical_root_key(pair))`; it is compiler/view metadata, not
an alternative root type or jump input.

## Generic exact digit formulas

`digit_formula.py` compiles arbitrary finite radix digit transducers through an exact
transition-monoid prefix scan.  State labels are canonicalized by reachable BFS from the
start state before any monoid/cache key is created.  Equivalent machines with different
caller state labels therefore share one compiled monoid.

Implemented exact arithmetic generators:

- `x -> m*x+c` via an LSD-first finite carry monoid;
- exact `x/d` via an MSD-first finite remainder monoid.

`reverse_digits.py` constructs every output digit of any reverse-and-add orbit from the pair
FormulaRoot and its derived carry formula.  No seed-196 assumption is present.

## Collatz

Binary Collatz is synthesized from the generic arithmetic compiler:

- odd branch `3*n+1`: 3 carry states, transition monoid size 8;
- even branch `n/2`: 2 remainder states, transition monoid size 3.

Regression results:

- seed 27: 111 steps to 1, maximum 9232;
- seed 196: 26 steps to 1.

These are exact concrete-orbit results, not a proof of the Collatz conjecture.

## Canonical cache policy

Known semantic canonicalization happens before caches:

- Formula/view caches use `canonical_root_key()`;
- digit transducer caches use `canonical_transducer_key()`;
- T^2 residual states are quotient-before-determinize as in the early canonical release;
- once a `LazyBimachine` has a canonical output MTDD, `emit()` bypasses the raw
  `(left,symbol,right)` tuple cache completely;
- cascade `_Behavior.E()` likewise does not maintain a shadow output cache for canonical
  source machines.

The raw tuple caches remain only as a fallback for small uncanonicalized research/reference
machines.  They are not populated after canonical output installation.

## Native temporal formula elimination

The canonical pair algebra now has a root-free internal layer (`pair_algebra.py`) shared by
the ordinary successor wrapper and native temporal compilers.  The low-level carry and branch
functions consume and return only `Expr` planes; they never create a second semantic state
type.

`native_power.py` adds direct T^2 and T^4 formula constructors.  T^2 substitutes the first
pair coefficients into the second carry/reset predicates and final pair formula without ever
constructing an intermediate FormulaRoot.  T^4 expands four such equation layers directly and
is explicitly tested not to call T^2.  Exact digit and final set projectors are available for
T^2, including the fully substituted second reset sets.

The native formula DAGs are intentionally extensionally identical to sequential recurrence
DAGs after canonical hash-consing.  The research question is now isolated cleanly: lower these
fully substituted source predicates directly to residual machines and compare their state
counts against composed bimachine powers.

## Powered machinery retained

The merge does not delete or replace:

- exact bimachine/transducer construction;
- residual Myhill--Nerode quotienting;
- T^2 quotient-before-determinize powering;
- grouped T^4+ dependency cascade;
- SLP compressed projection;
- `BulkPower` and Lucas/Frobenius factors;
- release guard / full-J complexity gates.

The full exact `J_0/J_1 : FormulaRoot -> FormulaRoot` remains intentionally fail-closed.
The missing research result is still a polylogarithmic exact powered quotient for the
nonlinear threshold/carry forcing residual, not another state representation.
