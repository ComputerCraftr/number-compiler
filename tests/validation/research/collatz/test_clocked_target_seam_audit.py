from __future__ import annotations

from typing import cast

import pytest

from devtools.verification.collatz_clocked_target_seam_probe import build_report
from devtools.verification.endpoint_seam_audit import BoundedEndpointPowerArena
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz


def _step(value: int) -> int:
    return accelerated_odd_collatz(value).target


@pytest.mark.validation
@pytest.mark.parametrize(
    "bits,expected",
    [
        (14, (6_144, 4_992, 3_588, 2_251, 1_095)),
        (16, (24_576, 19_968, 14_352, 9_029, 4_474)),
    ],
)
def test_clocked_exact_endpoint_frontier_counts(
    bits: int, expected: tuple[int, ...]
) -> None:
    report = build_report(bits=bits)
    rows = cast(list[dict[str, int]], report["rows"])
    assert tuple(row["endpoint_classes"] for row in rows) == expected
    assert rows[0]["aliases"] == ((1 << (bits - 1)) - expected[0])
    assert all(row["primitive_successors"] > 0 for row in rows)
    assert report["first_use_sublinear_certified"] is False
    assert report["clock_kind"] == "exact accelerated event tick"
    assert report["clock_is_physical_tick"] is False


@pytest.mark.validation
def test_warm_dyadic_endpoint_query_needs_no_primitive_replay() -> None:
    arena = BoundedEndpointPowerArena(_step)
    expected = arena.power(27, 4)
    primitive = arena.primitive_successors

    def forbidden(_value: int) -> int:
        raise AssertionError("warm exact endpoint query replayed a primitive")

    arena.step = forbidden
    assert arena.power(27, 4) == expected
    assert arena.primitive_successors == primitive
