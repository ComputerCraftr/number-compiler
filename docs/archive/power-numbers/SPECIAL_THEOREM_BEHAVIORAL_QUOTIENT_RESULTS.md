# Direct Pépin / Lucas–Lehmer behavioral quotient — condensed summary

## Key findings

- The hidden factor/bend coordinate can be bypassed semantically by observing the actual Pépin/LL target predicate directly.
- At one fixed decision horizon, the final-output quotient is genuinely only two classes: `T^h(x)=target` versus not.
- The hard operation is **injecting the seed into that two-class fiber**.
- On passing prime controls, the PASS fiber has `2^h` roots; an exact polynomial defect for that fiber needs degree at least `2^h`, giving multiplicative depth at least `h` in the generic polynomial circuit model.
- A reusable successor-closed all-horizons quotient has `h+1` prime-domain behavioral classes.
- The passing seed's target-observer sequence is a single impulse, giving Hankel rank `B-1` at the decision depth.
- `QuadraticPower(depth=h)` is a compact operator description, but specializing the full map still retains the classical nonlinear-depth chain.
- Existing two-primary filtration compresses some state but still has Theta(`B`) class growth and lacks a cheap deeper-character injector.

## Promotion decision

- No powered theorem shortcut is promoted.
- Production keeps the exact lazy-constraint + Pépin/Lucas--Lehmer ceiling.
- A future win must change the injector/arithmetic model, not merely rename factor, bend, Frobenius, character, or wreath state.

## Evidence

- Probe: `bench/special_theorem_behavioral_quotient_probe.py`.
- Metrics: `results/special_theorem_behavioral_quotient_metrics.json`.
