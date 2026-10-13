"""P0: powered reverse/add digits must consume the temporal publisher.

Using TileScheduler is necessary but does not by itself establish this
cutover: its causal reconstruction path must also be absent. These assertions
remain red until production constructs the composed two-port output image.
"""

from typing import Never

import pytest

from number_compiler.api.cli import main
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.recursive_outputs import (
    RecursiveCoordinateMorphismArena,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError(
        "P0: powered reverse/add output still executes causal reconstruction "
        "or a higher temporal continuation"
    )


def _reference(seed: int, steps: int) -> str:
    """Independent bounded oracle, never supplied to the production request."""
    for _ in range(steps):
        seed += int(str(seed)[::-1])
    return str(seed)


@pytest.mark.parametrize(
    "seed,steps",
    [(196, steps) for steps in (2, 4, 8, 16, 20, 32, 64, 128, 256, 512, 1024)]
    + [(11, 4), (89, 8), (100, 16), (0, 4), (12003, 4)],
)
def test_cli_digits_use_composed_publisher_without_causal_reconstruction(
    seed: int,
    steps: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    expected = _reference(seed, steps)
    monkeypatch.setattr(CausalTileEngine, "_run", _forbidden)
    monkeypatch.setattr(HigherBimachineRuntime, "point", _forbidden)
    monkeypatch.setattr(RecursiveCoordinateMorphismArena, "temporal", _forbidden)

    status = main(["reverse-add", "--nth", str(steps), "--seed", str(seed)])

    captured = capsys.readouterr()
    assert status == 0
    assert captured.out == expected + "\n"
    assert captured.err == ""
