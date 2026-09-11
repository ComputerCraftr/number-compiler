# Baby/giant backward behavioral bend quotient — condensed summary

## Key findings

- The exact dyadic backward partition has a closed class formula: distance to the next bend capped at the observed horizon.
- Before saturation, the extensional class count is `min(h+1,q)`; the partition has a one-rule grammar even though the number of residual classes grows.
- Endpoint `hit/no-hit` is **not** a successor-closed powered state; exact closure can require `q` classes.
- Baby/giant phase itself is not the quotient; the hidden phases are effectively injective on the relevant control.
- One fixed-window BSGS evaluation can be reused: it returns `CLEAR` or a compact `BEND(first_slot,gcd)` packet and later observers do not rerun the window.
- v0.53.7 removes linear GCD descent after that evaluation: support-only queries stop at the root GCD and witness localization uses a balanced support tree.
- The one-shot injector is still square-root/sublinear scale, not polylogarithmic.

## Promotion status

- Closed: capped-distance formula, dyadic pullback law, one-rule split grammar, fixed-window packet reuse.
- Refuted: endpoint-only powered state and baby/giant phase as a compact behavioral quotient.
- Open: factor-free capped-distance injector and polylog unseen-window constructor.
- Production therefore keeps the lazy constraint + classical theorem ceiling.

## Evidence

- Probe: `bench/baby_giant_behavioral_bend_probe.py`.
- Metrics: `results/baby_giant_behavioral_bend_metrics.json`.
