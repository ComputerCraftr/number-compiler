> **v0.53.8 note:** the historical fixed-height carry-slab backend described below has been removed. Current 196 spatial carry/digit projection uses the exact finite threshold-defect state and shared logarithmic prefix monoid in `reverse_domain.py` / `prefix_monoid.py`. Historical measurements are retained only as research evidence.

> **v0.10 update:** the exact carry/event theorem restores a fixed-height decimal H=20 binary carry slab; this file remains valid for the legacy exact T⁸+ executor, but that syntax tower is no longer the preferred nonlinear theorem coordinate. See `CARRY_EVENT_FORMULA_RESULTS.md`.

> **Historical v0.7 checkpoint.** v0.8 deletes the T^8+ provenance object; see `SHARED_DAG_POWER_RESULTS.md`.

# Lazy canonical continuation decisions — v0.7.0

## T⁴ is no longer provenance

The first higher-order continuation layer is now represented by `_PartitionBoundaryState`.
For `C = T² o T²`, a left continuation is a function from the 179 canonical T² right states to
T² left states, and a right continuation is a function from the 757 canonical T² left states to
T² right states.

Instead of storing a 179/757-entry tuple, the state stores the reduced exact partition

```text
output_state -> argument_bitset
```

with disjoint masks covering the complete proof domain.  Equal output masks are merged and the
normalized partition is hash-consed together with the canonical first-child anchor.

At decimal 196 / T^1024, the reached T⁴ states are:

| side | canonical states | complete argument domain | avg output regions | max output regions | flat vectors |
|---|---:|---:|---:|---:|---:|
| left | 43,765 | 179 | 9.176 | 14 | 0 |
| right | 5,886 | 757 | 23.359 | 48 | 0 |

The interner records **34,861** exact reuse hits during this
projection.  Those are whole-function identity hits over the complete finite T² domain, not
sample/cache collisions.

## Exact transition algebra

For one input symbol `a`, let `P_y` be the bitset on which the old continuation returns second
state `y`.  The new region is computed as

```text
preimage_a(P_y) & emit_selector(anchor, a, s)
```

and relabeled by `second.advance(y, s)`.  Regions with equal resulting state are unioned.  Python
big integers implement the finite set algebra directly, so work scales with the number of reduced
regions rather than one Python object per argument cell.

## Blank-tail cleanup

The previous composition metadata settled first-left, first-right, and second tails serially.
That is unnecessarily conservative because both first-child boundaries consume the same blank
stream.  v0.7 proves/uses

```text
ready_first = max(first_left_tail, first_right_tail)
out_left    = ready_first + second_left_tail
out_right   = ready_first + second_right_tail
```

which yields exact T^N tails `N/(N-1)` for decimal powers.  Direct 196 checks through T^1024 agree
with sequential reverse-add exactly.

## What remains sparse

T⁸ is now the first provenance layer.  On the same T^1024 projection:

| side | reached T⁸ sparse programs | demanded cells | avg args/program | max args/program |
|---|---:|---:|---:|---:|
| left | 28,892 | 29,428 | 1.019 | 18 |
| right | 27,623 | 29,396 | 1.064 | 419 |

This is why the next recursive decision representation cannot enumerate a universal T⁴ state
list first.  It must treat canonical T⁴ states themselves as a compressed decision domain.
