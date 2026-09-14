# Prime-clock recursive wheel quotient results — v0.54.0

For old wheel modulus `M` and next prime `q`, deletion phase obeys `kappa_(i+1)=kappa_i-M^-1*g_i (mod q)`. The canonical morphism keeps only endpoint phase plus the exact deletion histogram modulo the uniform `Phi_q` direction; endpoint differences and half-gap radix coordinates generate the same action.

| M | add q | old gaps | new gaps | phase itinerary bits | circular bits | max deviation | endpoint-diff | half-gap | q-power uniform | extension exact |
|---:|---:|---:|---:|---:|---:|---:|---|---|---|---|
| 2 | 3 | 1 | 2 | 2 | 7 | 1 | True | True | True | True |
| 6 | 5 | 2 | 8 | 6 | 13 | 1 | True | True | True | True |
| 30 | 7 | 8 | 48 | 24 | 19 | 1 | True | True | True | True |
| 210 | 11 | 48 | 480 | 192 | 31 | 2 | True | True | True | True |
| 2,310 | 13 | 480 | 5,760 | 1,920 | 37 | 1 | True | True | True | True |
| 30,030 | 17 | 5,760 | 92,160 | 28,800 | 74 | 4 | True | True | True | True |

The historical phase quotient remains exact. v0.54.0 additionally closes the carrier-expansion part of recursive rank/select: `PrimeRecursiveWheelIndex` works directly from the wheel-prime descriptor, and `PrimeWheelExtensionIndex` provides a non-expanding compatibility view for a materialized parent wheel.

The remaining prime frontier is no longer "how do I rank/select without expanding the parent gap cycle?"; it is how to collapse the increasing number of exact factor/wheel stages needed by arbitrary-magnitude nth-prime selection. The Legendre recurrence is exact but is not advertised as polylogarithmic in wheel depth.

The [September 13 owner audit](../../prime-clock-owner-audit-2026-09-13.md)
reproduces the eleven-stage million-bound count, adds a gate poisoning all
parent-gap construction, and distinguishes the current query-local DAG from
the separate nth-prime CLI path. It also records exact scopes for state counts.
