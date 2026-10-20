"""Independent bounded references for the source-bound no-growth branch."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_chamber import (
    SameCarryChamberRejected,
    iter_same_carry_digits,
)
from number_compiler.sequences.reverse_add.source_images import (
    ReverseSourceImageWorkspace,
)
from tests.support.reference_arithmetic import (
    radix_digits_lsd,
)
from tests.support.reference_arithmetic import (
    reverse_add_digit_step as _step,
)


@pytest.mark.parametrize("base", [2, 3, 10, 16])
@pytest.mark.parametrize("steps", [3, 4, 6])
@pytest.mark.parametrize(
    "exhaustive", [False, pytest.param(True, marks=pytest.mark.validation)]
)
def test_chamber_acceptance_matches_independent_full_trajectories(
    base: int, steps: int, exhaustive: bool
) -> None:
    seeds = (
        range(256)
        if exhaustive
        else (0, 1, base - 1, base, base + 1, base**2 - 1, 196, 255)
    )
    outcomes: set[bool] = set()
    for seed in seeds:
        digits = radix_digits_lsd(seed, base)
        endpoint = digits
        initial = _step(digits, base)[1]
        admitted = initial[-1] == 0
        for _ in range(steps):
            endpoint, carries = _step(endpoint, base)
            admitted &= carries == initial and len(endpoint) == len(digits)
        outcomes.add(bool(admitted))
        ledger = ResourceLedger()
        output = iter_same_carry_digits(ExactSource(digits, base), steps, ledger)
        if admitted:
            assert tuple(output) == endpoint, (base, seed, steps)
        else:
            with pytest.raises(SameCarryChamberRejected):
                next(output)
            assert ledger.counters["reverse_source_chamber_rejections"] == 1
    assert outcomes == {False, True}


@pytest.mark.parametrize("width", [16, 32, 64, 128, 256, 512, 1024])
def test_complete_stream_has_linear_source_reads(width: int) -> None:
    source = ExactSource((1,) * width, 10)
    ledger = ResourceLedger()
    assert tuple(iter_same_carry_digits(source, 3, ledger)) == (8,) * width
    assert ledger.counters["reverse_source_pullback_pair_reads"] <= 10 * width
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize(
    "seed,expected", [(13783, 94039), (18211171, 60744805), (111589511, 454050344)]
)
def test_196_orbit_no_growth_pairs_preserve_generic_two_step_path(
    seed: int, expected: int
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2)
    assert tuple(workspace.iter_digits()) == radix_digits_lsd(expected, 10)
    assert workspace.ledger.counters.get("source_image_primitive_applications", 0) == 0
    workspace.dispose()


def test_q19_stream_does_not_repeat_point_prefixes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts

    source = ExactSource((1,) * 257, 10)
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), int("1" * 257), 3)
    assert workspace.width() == len(source.digits)
    # Scalar width does not admit digit ports; the first point demand does.
    assert workspace.digit(0) == 8

    def forbidden(*_args: object) -> int:
        raise AssertionError("stream repeated point-prefix demand")

    monkeypatch.setattr(SourceCarryPorts, "_first_prefix", forbidden)
    assert tuple(workspace.iter_digits()) == (8,) * 257
    counters = workspace.ledger.counters
    assert counters["recursive_output_stream_node_visits"] < 12 * 257
    assert counters["recursive_output_stream_emitted_digits"] == 257
    workspace.dispose()
