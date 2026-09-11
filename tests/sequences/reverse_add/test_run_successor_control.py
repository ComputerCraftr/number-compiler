"""Small independent controls; exhaustive sweeps remain validation work."""

from itertools import product

import pytest

from devtools.proofs import ExactOracleAccessForbidden, exact_oracle
from devtools.proofs import reverse_run_successor as control
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.fields.radix import symbol_runs


def test_uniform_runs_do_not_call_expanded_oracle(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("expanded field or oracle consulted")

    monkeypatch.setattr(control, "pair_step", forbidden)
    monkeypatch.setattr(control, "symbol_runs", forbidden)
    monkeypatch.setattr(control, "reverse_pair_sums", forbidden)
    with exact_oracle():
        assert control.uniform_control(1)[-1] == ((7, 2),)
        for width in (4, 1_000_000, 10**100):
            assert control.uniform_control(width) == [
                ((2, width),),
                ((4, width),),
                ((8, width),),
                ((16, width),),
                ((7, 1), (14, width - 1), (7, 1)),
            ]


def test_carry_domains_and_growth_alignment_against_pair_oracle() -> None:
    with exact_oracle():
        # LT, EQ, GT and changes at both boundaries, including center runs.
        for left, middle in product(range(19), repeat=2):
            field = (left, left, middle, middle, left, left)
            expected, growth = pair_step(field, 10)
            assert control.run_successor(symbol_runs(field)) == (
                symbol_runs(expected),
                growth,
            )


@pytest.mark.parametrize("seed", [1, 1111, 196])
def test_one_hundred_successors(seed: int) -> None:
    with exact_oracle():
        assert control.compare_trajectory(seed)["exact_steps"] == 100


def test_reference_scope_and_invalid_runs() -> None:
    with pytest.raises(ExactOracleAccessForbidden):
        control.run_successor(((2, 1),))
    with exact_oracle():
        for source in (
            (),
            ((2, 0),),
            ((19, 1),),
            ((2, 1), (4, 1)),
            ((2, 1), (2, 1)),
            ((2, True),),
        ):
            with pytest.raises(ValueError):
                control.run_successor(source)
