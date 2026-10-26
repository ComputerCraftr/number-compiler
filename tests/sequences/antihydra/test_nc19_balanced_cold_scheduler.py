"""The cold exact-source producer reuses the shared balanced carry worklist."""

from __future__ import annotations

import pytest


def _literal(centered_source: int, ticks: int) -> tuple[int, int, int]:
    value = centered_source
    delta = minimum = 0
    for _ in range(ticks):
        parity = value & 1
        delta += 3 * parity - 1
        minimum = min(minimum, delta)
        value = (3 * value + parity) // 2
    return value, delta, minimum


@pytest.mark.parametrize("ticks", (65, 128, 256, 1024, 2048, 3072))
def test_main_root_nth_uses_certified_route_without_generic_tree(
    ticks: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.sequences.antihydra.arithmetic_images import (
        AntihydraArithmeticImageWorkspace,
    )
    from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("cold root action opened a generic source constructor")

    monkeypatch.setattr(AntihydraArithmeticImageWorkspace, "_run_candidate", forbidden)
    monkeypatch.setattr(
        AntihydraArithmeticImageWorkspace, "complete_composite_candidate", forbidden
    )

    term = AntihydraArithmeticTerm(ticks, shared_cache=False)
    result = term.result()
    result.require_source()
    endpoint, balance, minimum = _literal(7, ticks)
    assert (result.h - 1, result.balance, result.minimum) == (
        endpoint,
        balance,
        minimum,
    )
    counters = term.ledger.counters
    assert (
        counters.get("antihydra_arithmetic_balanced_effect_requests", 0) > 0
        or counters.get("antihydra_arithmetic_temporal_odd_macro_repetitions", 0) > 0
    )
    assert counters.get("antihydra_arithmetic_composite_cutover_chunks", 0) == 0
    assert counters.get("antihydra_arithmetic_temporal_balanced_routes", 0) == 0
