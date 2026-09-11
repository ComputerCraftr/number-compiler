# Reverse 196 canonical-tile complete-output profile

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../README.md).

Source fingerprint: `90326adda1b0373b`.

Scope: intermediate full completed-output construction for reverse/add 196. Each N row applies `BaseBlockEffect(10)^(N-1)` to `(7,18,7)`, then explicitly applies `DigitNormalizeBlockEffect(10)`; the terminal normalization is the first reverse-add step, so the scalar oracle advances 196 exactly N times. The source is padded to the least dyadic width covering `3+N`. This is not a fused demand-route measurement or evidence of logarithmic cold point execution.

The ordinary timings in `reverse196.json` include only the powered pair completion and explicit terminal completion. Caches start cold per row. Acceleration response caches are not involved.

A deterministic cProfile comparison at N=32 identified discarded channel rewrites as the dominant bounded cost:

| measure | before live-channel projection | after |
|---|---:|---:|
| profiler total | 40.535 s | 29.451 s |
| Python calls | 165,077,372 | 121,567,644 |
| child DAG substitutions | 8,820 | 2,835 |
| `_parent_components` cumulative | 34.330 s | 22.695 s |

Profiler times include substantial instrumentation overhead and must not be compared directly with ordinary wall times. The ordinary N=32 completion changed from approximately 11.01 s to 8.20 s on this run. The optimization preserves all thirteen published semantic channels while computing only the two midpoint transfers and seven child channels that survive the deterministic parent projection.
