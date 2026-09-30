"""Proof output dependencies use an iterative stack, including nested powers."""

from collections.abc import Callable

import pytest

from devtools.verification.builders.bimachine_lazy_power import (
    EmissionRequest,
    EmissionSteps,
    LazyBimachine,
    compose,
    lazy_from_eager,
)
from devtools.verification.builders.bimachine_power import DFA, build_step, encode


def _forward(previous: LazyBimachine) -> Callable[[int, int, int], EmissionSteps]:
    def steps(left: int, symbol: int, right: int) -> EmissionSteps:
        output = yield EmissionRequest(previous, left, symbol, right)
        return output

    return steps


def test_deep_proof_dependencies_never_reenter_emit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    scan = DFA((0,), 0, {(0, 0): 0}, (0,), {0: 0})
    machine = LazyBimachine(2, (0,), scan, scan, lambda _l, a, _r: (a,), {})
    for _ in range(2000):
        machine = LazyBimachine(2, (0,), scan, scan, _forward(machine), {})
    original = LazyBimachine.emit
    active = False

    def guarded(
        self: LazyBimachine, left: int, symbol: int, right: int
    ) -> tuple[int, ...] | None:
        nonlocal active
        assert not active, "proof output replay recursively reentered emit"
        active = True
        try:
            return original(self, left, symbol, right)
        finally:
            active = False

    monkeypatch.setattr(LazyBimachine, "emit", guarded)
    assert machine.emit(0, 0, 0) == (0,)
    assert machine.emit(0, 0, 0) == (0,)


def test_composed_proof_emission_matches_independent_primitive_outputs() -> None:
    primitive = build_step(3)
    lazy = lazy_from_eager(primitive)
    squared = compose(lazy, lazy, verbose=False)
    for parity in (0, 1):
        for half in ((1,), (2,), (1, 0), (2, 3), (4, 2, 1)):
            word = encode(parity, half, 3)
            assert squared.output(word) == primitive.output(primitive.output(word))


def test_cyclic_proof_dependency_fails_explicitly() -> None:
    scan = DFA((0,), 0, {(0, 0): 0}, (0,), {0: 0})
    machine = LazyBimachine(2, (0,), scan, scan, lambda _l, a, _r: (a,), {})
    machine.resolver = _forward(machine)
    with pytest.raises(ValueError, match="cyclic"):
        machine.emit(0, 0, 0)
