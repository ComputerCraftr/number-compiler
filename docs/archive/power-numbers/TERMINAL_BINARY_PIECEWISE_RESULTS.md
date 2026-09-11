# Shared binary piecewise cleanup / theorem-closure audit

The Collatz and Frobenius section controllers now use the same domain-neutral
`BinaryPiecewiseHandler`.  The handler owns only the control lattice
`ZERO | ONE | SPLIT | UNKNOWN`; branch discovery and arithmetic remain domain
specific.

For Collatz, `ZERO/ONE` is derived from the current formula LSB.  For the local
Frobenius odometer, `ZERO` sections `k -> k/2` and `ONE` terminates the terminal
chunk.  The candidate-level Frobenius discriminator is deliberately still
`UNKNOWN`: no supplied stride bit, factor truth, or per-level replay is accepted.

| family | parameter | queried span | one-step status | method |
|---|---:|---:|---|---|
| fermat | 4 | 2 | UNKNOWN | candidate-derived-frobenius-root-action-unavailable |
| fermat | 5 | 9 | UNKNOWN | candidate-derived-frobenius-root-action-unavailable |
| mersenne | 11 | 2 | UNKNOWN | candidate-derived-frobenius-root-action-unavailable |
| mersenne | 13 | 3 | UNKNOWN | candidate-derived-frobenius-root-action-unavailable |

## Closure status

- shared binary control cleanup: **complete**;
- local Frobenius section transition: **complete**;
- candidate-derived root action: **not proved**;
- production oracle/replay fallback: **none**.

The remaining theorem is exactly

```text
unfactored sparse special candidate
    -> ZERO / ONE / natural SPLIT root action
    -> shared binary section morphism
```

A morphism that receives a supplied `k & 1`, factors the candidate, or computes
the root bit by replaying the Lucas/Pépin horizon is rejected.
