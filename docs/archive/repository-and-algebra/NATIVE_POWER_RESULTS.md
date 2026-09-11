# Native temporal formula power results

The canonical tree now has a genuinely root-native two-step primitive.  It builds

```text
S -> L/R -> tau(S,L,R) -> K(tau) -> S^(2)(S,L,R,K)
```

inside one hash-consed formula construction.  `tau` is an internal tuple of `Expr` planes:
it is never a `FormulaRoot`, never registered with `BlockSummary`, never assigned first-step
value sets, and never passed through `successor()`.

## Exactness

- randomized arbitrary-radix cases: **400** exact T² comparisons, bases 2..17;
- repeated seed-196 run: **100 native T² applications = 200 ordinary steps**, exact final
  pair field, width 88;
- full pytest regression suite separately covers the substituted second reset sets, native exact
  two-step digit projector, final `X_v -> Z_w` set map, and direct native T⁴.

## Construction footprint on the seed-196 source pair `(7,18,7)`

| metric | native T² | `successor(successor(S))` reference |
|---|---:|---:|
| final reachable formula nodes | 66 | 66 |
| final formula depth | 24 | 24 |
| arena nodes added | 68 | 68 |
| metadata entries added | 1 | 3 |
| derived-cache entries | 0 | 2 |
| closed bits evaluated | 34 | 57 |

The final reachable DAG is deliberately the same canonical algebra: native T² changes the
**construction boundary**, not the extensional recurrence.  Its immediate win is that the
first successor is not a semantic/compiler state and its summary/carry cache identity never
exists.

## Native T⁴ formula experiment

Native T⁴ is also built directly from four carry/branch equation layers.  It does **not** call
`native_two_step()` and retains no S² intermediate root.  On the same seed-196 source:

| metric | native T⁴ | native `T²(T²(S))` reference |
|---|---:|---:|
| final reachable formula nodes | 128 | 128 |
| final formula depth | 47 | 47 |
| arena nodes added | 136 | 136 |
| metadata entries added | 1 | 2 |
| closed bits evaluated | 155 | 155 |

Again, the final canonical formula DAG is expected to match because both denote the same fully
substituted equations.  The distinction is that native T⁴ never assigns semantic identity to
the two-step midpoint.

## What this does *not* claim yet

The existing powered bimachine T² remains the older composed construction at
**688 left / 91 right states**.  This patch does not pretend
those numbers are native-T² state counts.  The next research step is to lower the fully
substituted native T² predicates directly into the canonical residual compiler so quotienting
happens while source predicates are constructed.  Only then is a native-machine state-count
comparison meaningful.  The direct native T⁴ formula now exists, so that lowering can compare
it against the existing composed `T² o T²` machine construction without conflating the two.
