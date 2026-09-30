"""Independent trajectory checks of the restricted pump's analytic exit."""

from __future__ import annotations

from tests.support.reference_arithmetic import reverse_add_digit_step
import pytest

from devtools.experiments.reverse_add.chamber_exit import analyze_chamber_exit
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts


def _digits(seed: int, base: int) -> tuple[int, ...]:
    result = []
    while True:
        seed, digit = divmod(seed, base)
        result.append(digit)
        if not seed:
            return tuple(result)


@pytest.mark.parametrize("base", [2, 3, 10, 16])
def test_analytic_exit_is_first_literal_carry_change(base: int) -> None:
    for seed in range(512):
        digits = _digits(seed, base)
        source = ExactSource(digits, base)
        ledger = ResourceLedger()
        report = analyze_chamber_exit(source, ledger)
        _, original = reverse_add_digit_step(digits, base)
        assert ledger.entries == ledger.nodes == 0
        if report.initial_growth:
            assert original[-1] == 1
            assert report.safe_applications == 0
            continue
        if report.safe_applications is None:
            # With fixed width, a positive integer cannot double forever.
            assert seed == 0
            continue
        endpoint = digits
        for _ in range(report.safe_applications):
            endpoint, carries = reverse_add_digit_step(endpoint, base)
            assert carries == original
            assert len(endpoint) == len(digits)
        _, changed = reverse_add_digit_step(endpoint, base)
        assert changed != original
        witness = report.exit
        assert witness is not None
        pair = endpoint[witness.position] + endpoint[-1 - witness.position]
        assert pair == witness.value
        assert not witness.lower <= pair <= witness.upper


@pytest.mark.parametrize("seed,safe,position,value", [(1, 3, 0, 16), (196, 1, 0, 15)])
def test_exact_source_reachable_exit(
    seed: int, safe: int, position: int, value: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    def forbidden(*args: object, **kwargs: object) -> object:
        pytest.fail("exit discovery must not construct a future coefficient layer")

    monkeypatch.setattr(SourceCarryPorts, "second_pair", forbidden)
    monkeypatch.setattr(SourceCarryPorts, "second_carry", forbidden)
    ledger = ResourceLedger()
    report = analyze_chamber_exit(ExactSource(_digits(seed, 10), 10), ledger)
    assert report.safe_applications == safe
    assert report.exit is not None
    assert (report.exit.position, report.exit.value) == (position, value)
    assert ledger.counters["reverse_pump_exit_source_coordinates"] == report.width
