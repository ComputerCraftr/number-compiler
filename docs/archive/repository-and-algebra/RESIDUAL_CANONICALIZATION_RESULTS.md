> **v0.53.8 note:** the historical fixed-height carry-slab backend described below has been removed. Current 196 spatial carry/digit projection uses the exact finite threshold-defect state and shared logarithmic prefix monoid in `reverse_domain.py` / `prefix_monoid.py`. Historical measurements are retained only as research evidence.

> **v0.10 update:** the exact carry/event theorem restores a fixed-height decimal H=20 binary carry slab; this file remains valid for the legacy exact T⁸+ executor, but that syntax tower is no longer the preferred nonlinear theorem coordinate. See `CARRY_EVENT_FORMULA_RESULTS.md`.

# Residual canonicalization results — v0.9.0

The runtime distinguishes semantic identity from compressed syntax and memoization explicitly.

```text
T² decimal = minimized complete finite semantics (757 / 179)
T² other   = complete finite continuation-function image
T⁴ decimal = canonical reduced argument-bitset continuation function
T⁸+        = one global CanonicalWord RLE/SLP carrier + non-semantic demanded-cell cache
```

## T²

The deterministic decimal T² kernel is 757 / 179 states, 451,918 compressed bytes, SHA-256
`35276802973d716c642cb1e78dfa7ee395ba60798bc3014cfc57da10e1927e61`. Distinct derivations of
the same continuation are one state before higher composition.

## T⁴

`_PartitionBoundaryState` covers the complete T² argument domain with disjoint output bitsets and
hash-conses the normalized whole function. The additional output-pushed all-symbol behavioral
refinement is now complete as a diagnostic. At 196/T^1024 it proves 3 left + 189 right aliases,
leaving 43,761 / 5,697 states. Only 0.387% of the reached T⁴ states merge, so dead T⁴ coordinates
are not the high-power bottleneck.

## T⁸+

The former provenance object is absent. `CanonicalWord` is the only higher carrier, and v0.9 also
deletes the per-effect `_sparse_roots` shadow index. One global root registry replaces 116,144
v0.8 layer-local index entries with 86,005 current global roots including EMPTY. Exact demanded
semantic cells are cached but never used as state equality.

The remaining full-J blocker is whole-action behavioral quotienting of these compressed programs.
Partial demand equality is never promoted to whole-function equality.
