# Restored carry-event / length formulas — v0.10.0

The canonical tree again exposes the exact nonlinear forcing decomposition

```text
S_(t+1) = A_g S_t + E_t
A_0 = 2
A_1 = 1+z
```

without restoring any parallel semantic state. `X_v`, forward carry `C`, carry border,
and the signed event-value position sets are hash-consed derived `Expr`/position-set views of the FormulaRoot planes.

## Fixed temporal memory

For decimal, `w=bit_length(18)=5` and `H=4w=20`. The release verifies at
steps 20, 64, 128, 256, 512 and 1024 that the previous **20** event fields reconstruct
the exact endpoint pair, and that the previous 20 forward binary carry fields do the same.
No older pair state, separate reverse-carry state or separate growth stream is required.

Event widths are exact lengths: `len(E_t)=len(S_(t+1))`, so successive event-width
differences recover the later growth bits in the window.

## Carry-only event formula

No growth:

```text
E_i = C_i + C_(d-i-1) - b(C_(i+1)+C_(d-i))
```

Growth edges:

```text
E_0 = E_d = 1-b*C_1
```

Growth interior:

```text
E_i = C_i + C_(d-i) - b(C_(i+1)+C_(d-i+1))
```

The current source `(7,18,7)` event Formula IR uses **54** reachable
Boolean DAG nodes across all `X_v`, carry/border and event-value masks, and creates
**zero semantic FormulaRoots**.

## Architectural consequence

The remaining nonlinear target is no longer conceptually an unbounded temporal tower. It is

```text
20 binary carry position-set fields x growing spatial coordinate
```

The earlier T^8+ canonical-program machinery remains an exact execution path, but the research
quotient should now be formulated over this fixed-height carry slab. Full J remains fail-closed
until that spatial grammar has a proved compact behavioral closure.
