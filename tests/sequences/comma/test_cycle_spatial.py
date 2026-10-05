"""Independent partition and literal-transition checks for arithmetic Q19."""

from __future__ import annotations

from itertools import product

import pytest

from devtools.verification.comma_semantic_quotients import build_q19_production_ports
from number_compiler.sequences.comma.arithmetic import cycle_transfer
from number_compiler.sequences.comma.cycle_spatial import CycleSpatialState


def test_q19_formula_matches_independent_moore_partition() -> None:
    reference = build_q19_production_ports()
    direct = tuple(CycleSpatialState.from_port(*port) for port in reference.ports)
    assert len(set(direct)) == reference.classes == 19
    for i, j in product(range(90), repeat=2):
        assert (direct[i] == direct[j]) == (
            reference.class_ids[i] == reference.class_ids[j]
        )


@pytest.mark.parametrize("leading", range(1, 10))
@pytest.mark.parametrize("digit", range(10))
def test_q19_power_preserves_literal_port_observations(
    leading: int, digit: int
) -> None:
    state = CycleSpatialState.from_port(leading, digit)
    current = digit
    for steps in range(31):
        expected = CycleSpatialState.from_port(leading, current)
        assert state.advance(steps) == expected
        assert expected.observation == (
            (current - leading) % 10 == 0,
            cycle_transfer(leading, current).period,
        )
        current = (current - leading) % 10 or (-leading) % 10


def test_q19_does_not_call_graph_minimization(monkeypatch: pytest.MonkeyPatch) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("classification expanded a graph")

    monkeypatch.setattr(
        "devtools.verification.comma_semantic_quotients.minimize_finite_observer",
        forbidden,
    )
    steps = 10**1000
    for f, d in product(range(1, 10), range(10)):
        state = CycleSpatialState.from_port(f, d)
        assert state.advance(steps).advance(17) == state.advance(steps + 17)
        assert state.advance(0) is state


def test_q19_equality_does_not_authorize_another_occurrence_weight() -> None:
    assert CycleSpatialState.from_port(1, 0) == CycleSpatialState.from_port(3, 0)
    assert cycle_transfer(1, 0).displacement != cycle_transfer(3, 0).displacement


@pytest.mark.parametrize(
    ("period", "phase"),
    ((True, 0), (3, 0), (10, None), (5, -1), (2, 2), (10, False)),
)
def test_q19_rejects_forged_states(period: int, phase: int | None) -> None:
    with pytest.raises(ValueError, match="Q19"):
        CycleSpatialState(period, phase)


@pytest.mark.parametrize("steps", (-1, True))
def test_q19_rejects_invalid_duration(steps: int) -> None:
    with pytest.raises(ValueError, match="duration"):
        CycleSpatialState.from_port(1, 0).advance(steps)


@pytest.mark.parametrize(("f", "d"), ((0, 0), (10, 0), (True, 0), (1, False)))
def test_q19_uses_shared_source_validation(f: int, d: int) -> None:
    with pytest.raises(ValueError, match="invalid comma port"):
        CycleSpatialState.from_port(f, d)
