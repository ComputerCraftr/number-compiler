# v0.53.2 direct theorem behavioral quotient

Added `research/special_theorem_behavioral_quotient.py`, `tests/test_special_theorem_behavioral_quotient.py`, and `bench/special_theorem_behavioral_quotient_probe.py`.

The research separates two exact objects that earlier discussion conflated:

1. the fixed-horizon terminal fiber `[T^h(x)=target]`, which has only two classes but a prime-domain exact polynomial injector with `2^h` roots / degree and h multiplicative-depth lower bound;
2. the reusable next-h-output behavioral quotient, constructed by `P_(2h)=P_h ^ (T^h)^*P_h`, whose nonrecurrent-target grammar is capped first-future-hit distance and whose prime-domain extensional size is `h+1`.

The module also verifies the passing seed's exact `B-1` Hankel rank, the full-map degree obstruction, and the equivalence of the remaining source-depth frontier with the existing conditional two-primary filtration. No factor/bend/Frobenius-support coordinate is consumed.

All code remains under `research/`/`bench`/`tests`; production imports are unchanged.
