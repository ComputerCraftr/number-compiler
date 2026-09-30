import json
import random
from pathlib import Path

from devtools.paths import report_output
from devtools.verification.builders.bimachine_lazy_power import compose, lazy_from_eager
from devtools.verification.builders.bimachine_power import (
    DFA,
    Bimachine,
    build_step,
    decode,
    encode,
    ref,
)
from devtools.verification.random_inputs import random_half
from devtools.verification.builders.grouped_cascade_power import (
    build_left,
    build_right,
    metrics,
)
from devtools.verification.builders.minimize_bimachine import minimize_eager

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def main() -> None:
    B1 = minimize_eager(build_step(10))
    T2L = compose(lazy_from_eager(B1), lazy_from_eager(B1), verbose=False)
    out = {}
    for left_state in T2L.left.states:
        for a in T2L.alphabet:
            for r in T2L.right.states:
                z = T2L.emit(left_state, a, r)
                if z is not None:
                    out[(left_state, a, r)] = z
    assert isinstance(T2L.left, DFA) and isinstance(T2L.right, DFA)
    T2M = minimize_eager(Bimachine(T2L.base, T2L.alphabet, T2L.left, T2L.right, out))
    rng = random.Random(196)
    for _ in range(100):
        p = rng.randrange(2)
        h = random_half(rng, 4)
        pp, hh = p, tuple(h)
        for __ in range(2):
            pp, hh = ref(pp, hh, 10)
        assert decode(T2M.output(encode(p, h, 10)), 10) == (pp, hh)
    T2 = lazy_from_eager(T2M)
    _L4, LS4, _, capL, secL = build_left(T2, T2, cap=1000, time_cap=60)
    _R4, RS4, _, capR, secR = build_right(T2, T2, cap=1000, time_cap=60)
    data = {
        "T1_min": {"left": len(B1.left.states), "right": len(B1.right.states)},
        "T2_pre_min": {"left": len(T2L.left.states), "right": len(T2L.right.states)},
        "T2_min": {
            "left": len(T2M.left.states),
            "right": len(T2M.right.states),
            "defined_outputs": len(T2M.out),
        },
        "T4_first_1000": {
            "left": metrics(LS4),
            "right": metrics(RS4),
            "left_capped": capL,
            "right_capped": capR,
            "left_seconds": secL,
            "right_seconds": secR,
        },
    }
    (
        report_output(
            "devtools.verification.builders.minimized_cascade_probe",
            "minimized_cascade_metrics.json",
        )
    ).write_text(json.dumps(data, indent=2))
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
