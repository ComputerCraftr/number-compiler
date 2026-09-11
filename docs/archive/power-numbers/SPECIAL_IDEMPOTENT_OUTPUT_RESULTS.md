# Special idempotent output quotient — condensed summary

## Closed results

- Raw Fermat/Mersenne source digits are independent of the unresolved primality theorem.
- A single unresolved Boolean source class lifts exactly to `R[E]/(E^2-E)`, so every value is represented by rank-two state `A+B*E`.
- `QuadraticPower`, source-digit/cyclotomic multiplication, and output observers can operate on that rank-two state without guessing the source bit.
- Digit, canonical-length, and boundary-carry coordinates collapse to concrete values when both sheets agree.
- Separating coordinates remain exact guarded values and can be specialized later by a valid certificate/constraint.
- Output equivalence is only an initial partition; a powered machine must refine it to successor congruence.
- Nontrivial CRT idempotents are not interchangeable with Boolean `0/1` endpoints; endpoint-only collapse is guarded by adversarial tests.

## Remaining boundary

- The unfactored candidate still needs a valid terminal support/orientation source for genuinely theorem-sensitive outputs.
- A concrete value for a coordinate that truly separates the unresolved source classes is at least as informative as that source bit.
- Output-relative lazy constraints can reduce how often the theorem is needed, but cannot manufacture the theorem from raw digits of the same integer.

## Evidence

- Probe: `bench/special_idempotent_output_probe.py`.
- Metrics: `results/special_idempotent_output_metrics.json`.
