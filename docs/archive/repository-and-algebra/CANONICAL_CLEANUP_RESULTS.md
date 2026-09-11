# Canonical powered-projection cleanup

This pass removes the non-canonical state and compiler paths that had crept back
into the powered interval release.

## Deleted semantic duplication

Production no longer contains or accepts:

- `ScaleState`;
- pre-resolved growth words / schedule grammars;
- interval maps specialized by an external scale prefix;
- persistent carry monoid, carry vector, border, marker, one-hot value-set, or CRT state;
- a separate scale backend in the binary index driver.

The only semantic state is:

```text
FormulaRoot(planes)
```

Width, parity and half-length are properties of the formula shape. Carry classes,
carry masks, borders and the terminal growth bit are derived from the exact pair
coefficient formula when needed.

## Canonical successor

`successor(arena, root, spec)` now:

1. derives the carry expression from `root`;
2. evaluates only its terminal bit to synthesize growth;
3. compiles exactly the one reachable branch;
4. returns the next `FormulaRoot`.

There is no target-width or growth argument.

## Performance regressions removed

The old lazy evaluator recursively recomputed closed subexpressions and cached
individual `(node, position)` tuples. This pass replaces it with:

- arena-wide structural carry-expression reuse;
- iterative closed-bit evaluation (no Python recursion-depth dependency);
- compact per-expression `known/value` bitmask caches rather than millions of
  tuple-key Python entries;
- one carry derivation per successor instead of deriving it separately for growth
  selection and branch compilation.

Representative current-container formula construction timings from seed 196:

```text
steps   seconds   width
  50     ~0.07      24
 100     ~0.30      47
 150     ~0.56      67
 200     ~0.99      88
 300     ~2.35     133
 500     ~6.97     216
```

Before the closed-expression cache fix, the same 100-step path was about 2.8 s,
and deeper runs eventually hit Python recursion limits.

## Universal projection enumerator removed

The previous experimental all-source projection constructed every hypothetical
growth history. That creates an artificial exponential decision tree and is not
the fixed-seed `0 -> n` projection. It has been removed from production and is
preserved only in the separate research archive.

## Remaining powered-jump problem

The cleanup does not claim a full compact `J_0/J_1`. It makes the contract
canonical:

```text
J_a(FormulaRoot_n) -> FormulaRoot_(2n+a)
```

Any future powered backend must derive its width/growth information from the
formula it produces. A scale oracle or precomputed schedule can no longer make a
non-canonical implementation appear complete.
