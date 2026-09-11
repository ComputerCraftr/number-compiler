import random

from devtools.experiments.collatz.collatz_word_transducer import (
    apply_accelerated_reference,
    apply_transducer_value,
    collatz_accelerated_radix4_transducer,
    compose_subsequential,
    minimize_aligned_subsequential,
)


def test_radix4_accelerated_collatz_is_a_small_exact_subsequential_transducer() -> None:
    raw = collatz_accelerated_radix4_transducer()
    machine = minimize_aligned_subsequential(raw)
    assert len(raw.states) == 16
    assert len(machine.states) == 10
    assert machine.description_bits() == 317
    rng = random.Random(0xACCE1)
    for _ in range(2000):
        n = rng.randrange(1, 1 << 40) | 1
        assert apply_transducer_value(machine, n) == apply_accelerated_reference(n, 1)


def test_two_accelerated_steps_compose_exactly_but_state_growth_is_real() -> None:
    one = minimize_aligned_subsequential(collatz_accelerated_radix4_transducer())
    two_raw = compose_subsequential(one, one)
    two = minimize_aligned_subsequential(two_raw)
    assert len(two_raw.states) == 91
    assert len(two.states) == 70
    assert two.description_bits() == 3189
    for n in range(1, 4096, 2):
        assert apply_transducer_value(two, n) == apply_accelerated_reference(n, 2)
