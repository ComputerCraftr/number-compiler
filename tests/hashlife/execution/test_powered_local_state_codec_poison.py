"""Powered family observers bypass generic codecs and scalar runtimes."""

from collections.abc import Callable
from typing import Never

import pytest

from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


@pytest.mark.parametrize(
    ("term", "coordinate", "expected"),
    (
        (lambda: ReverseAddPoweredTerm(196, 16), 0, 8),
        (lambda: PoweredCollatzTerm(27, 16), 0, 1),
    ),
    ids=("reverse-add", "collatz"),
)
def test_certified_powered_observation_poison_generic_state_codec(
    monkeypatch: pytest.MonkeyPatch,
    term: Callable[[], ReverseAddPoweredTerm | PoweredCollatzTerm],
    coordinate: int,
    expected: int,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError(
            "certified field observation entered the generic state codec"
        )

    monkeypatch.setattr(
        "number_compiler.hashlife.interfaces.semantic_state_codec.StateCodecArena.compile",
        forbidden,
    )
    monkeypatch.setattr(
        "number_compiler.hashlife.execution.continuations.diamond_runtime.DiamondRuntime.execute",
        forbidden,
    )
    powered = term()
    assert powered.width() > 0
    assert powered.digit(coordinate) == expected
