# v0.59.9 bounded causal spacetime results

The family-specific causal engines are now production application backends for the two release sequences rather than reference-only oracles.

## Reverse/add

For base 10 the exact temporal memory is the fixed H=20 carry window. Production bootstraps that window, maps it to `ReverseAddCarryCutState`, and discards older temporal history. Exact pair content remains arena-owned dyadic **spatial payload**.

At N=256 for seed 196:

```text
bounded temporal state classes       2
bounded temporal action classes      2
unquotiented recursive app nodes     0
raw temporal scalar/span fields      0 / 0
exact spatial forcing occurrences    236
symbolic spatial action nodes        10,567
primitive forcing evaluations        255
```

The temporal quotient is therefore closed. The remaining reverse/add release blocker is composition of the exact cut-to-cut spatial forcing action: the cold primitive forcing evaluation count is still approximately linear in N.

## Physical Collatz

Production uses the normalized Collatz forcing quotient: bounded residue/local phase plus symbolic event/affine transport. Fixed radix-4 frame depth is a cocycle/weight, not state identity, and exact normalized tail tiles are spatial payload.

At N=256 for seed 27:

```text
bounded temporal state classes       3
bounded temporal action classes      3
unquotiented recursive app nodes     0
raw temporal scalar/span fields      0 / 0
exact spatial forcing occurrences    41
symbolic spatial action nodes        122
primitive evaluations                42
residual physical steps              1
```

The representative seed 27 tail is sublinear/saturating, but this is not an arbitrary-source logarithmic proof.

## Correct interpretation

The old generic `_RecursiveResidualAction` and macrocell-cache measurements are retained only as historical evidence for the bugs that were removed. Production point queries for reverse/add and Collatz now require zero generic spacetime macro entries and zero generic recursive-value entries.
