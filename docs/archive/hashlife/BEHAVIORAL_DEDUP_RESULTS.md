> **v0.53.8 note:** the historical fixed-height carry-slab backend described below has been removed. Current 196 spatial carry/digit projection uses the exact finite threshold-defect state and shared logarithmic prefix monoid in `reverse_domain.py` / `prefix_monoid.py`. Historical measurements are retained only as research evidence.

> **v0.10 update:** the exact carry/event theorem restores a fixed-height decimal H=20 binary carry slab; this file remains valid for the legacy exact T⁸+ executor, but that syntax tower is no longer the preferred nonlinear theorem coordinate. See `CARRY_EVENT_FORMULA_RESULTS.md`.

# Behavioral / state-index deduplication results — v0.9.0

## Removed duplicate state index

v0.8 already used one canonical `CanonicalWord` object per compressed program, but every
`ComposedBlockEffect` also retained its own `_sparse_roots` set.  On decimal 196 / `T^1024`
those layer-local sets contained **116,144 entries** for only **86,004 globally unique words**:
**30,140 duplicate root-index entries**.

v0.9 deletes `_sparse_roots` entirely.  `BlockContextBudget.program_word_roots` is the one
authoritative global registry.  Layer-local research profiles are derived from transition caches
and retain no second set of root ids.  The current global count is
**86,005**, including the single EMPTY identity word.

The demanded `(effect, side, word, argument) -> result` table is explicitly a memo cache and is
excluded from semantic identity (`compare=False` on the execution budget); it cannot become a
parallel state representation.

## Exact T^4 behavioral quotient

The in-progress output-pushed refinement was completed as a proof-only diagnostic.  For every
input symbol it compares the complete symbolic output residual, then merges a candidate pair only
when all exact one-symbol successors are the same canonical states.

At the 196 / `T^1024` reached T^4 universe it proves:

```text
left aliases proved          3
right aliases proved       189
left states after quotient  43,761
right states after quotient  5,697
proof time                    5.362 s
```

Only **192 / 49,650** reached T^4 partition states merge
(~0.387%).  Therefore T^4 dead-coordinate
identity is not the source of the near-quadratic high-power growth.  The proof pass is diagnostic
and intentionally not inserted into the hot projection path.

## Remaining semantic target

The remaining large family is T^8+ compressed program *actions*:

```text
T^8 left program roots   28,697
T^8 right program roots  27,620
all higher global roots  86,005
```

These are one canonical syntax carrier, not duplicated provenance state.  They are not yet a
proved minimal behavioral quotient.  Full `J_0/J_1` remains fail-closed until output pushing /
streaming-transducer residual minimization proves a bit-length-bounded action quotient.
