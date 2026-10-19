"""Actual term and clock consumers share the dyadic source-image construction."""

from __future__ import annotations

import pytest

from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.physical_images import (
    CollatzPhysicalImageWorkspace,
)


@pytest.mark.parametrize("steps", (0, 1, 2, 63, 64, 65, 130, 257, 1024))
def test_digits_and_clock_reuse_one_admitted_collatz_image(
    steps: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("Collatz consumer entered the causal executor")

    monkeypatch.setattr(CausalTileEngine, "__init__", forbidden)
    value, odd = 27, 0
    for _ in range(steps):
        odd += value & 1
        value = 3 * value + 1 if value & 1 else value // 2
    term = PoweredCollatzTerm(27, steps)
    assert term.materialize(max_bits=10000) == value
    before = dict(term.resource_ledger.counters)
    clock = term.s_arithmetic_clock()
    assert (clock.events, clock.divisions) == (odd, steps - odd)
    for key, count in before.items():
        if key.startswith("source_image_") or key.endswith("branch_steps"):
            assert term.resource_ledger.counters[key] == count
    for radix in (2, 3, 10, 16):
        remainder, index = value, 0
        while remainder:
            remainder, expected = divmod(remainder, radix)
            assert term.radix_digit(radix, index) == expected
            index += 1


def test_antihydra_and_collatz_share_the_implementation_not_just_a_formula() -> None:
    for method in (
        "apply_primitive",
        "first_child_source",
        "second_child_source",
        "compose_chronological",
        "first_failure_index",
        "saturated_summary",
    ):
        assert getattr(AntihydraArithmeticImageWorkspace, method) is getattr(
            DyadicReturnImageWorkspace, method
        )
        assert getattr(CollatzPhysicalImageWorkspace, method) is getattr(
            DyadicReturnImageWorkspace, method
        )
    term = AntihydraArithmeticTerm(130)
    result = term.result()
    workspace = term.arithmetic_workspace
    assert type(workspace) is AntihydraArithmeticImageWorkspace
    assert workspace.summary().delta == result.balance
    assert workspace.endpoint() == result.h
    transfer = workspace.summary().transfer
    assert transfer.upper == 3**130
    assert transfer.lower == 2**130


@pytest.mark.parametrize("family", ("collatz", "antihydra"))
def test_aggregate_projection_is_history_free_and_revalidates_its_image(
    family: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger = ResourceLedger()
    workspace = (
        CollatzPhysicalImageWorkspace(ledger, 27, 130)
        if family == "collatz"
        else AntihydraArithmeticImageWorkspace(ledger, 130)
    )
    image = workspace.summary()

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("aggregate projection rediscovered chronological support")

    monkeypatch.setattr(workspace, "branch_segments", forbidden)
    monkeypatch.setattr(workspace, "leaf_summaries", forbidden)
    projected = workspace.saturated_summary()
    assert not hasattr(projected, "support")
    assert projected.transfer is image.transfer
    assert (
        projected.width,
        projected.delta,
        projected.minimum,
        projected.odd_steps,
    ) == (image.width, image.delta, image.minimum, image.odd_steps)
    before = ledger.entries
    assert workspace.saturated_summary() == projected
    assert ledger.entries == before
    odd = image.odd_steps
    try:
        object.__setattr__(image, "odd_steps", odd + 1)
        with pytest.raises(ValueError):
            workspace.saturated_summary()
    finally:
        object.__setattr__(image, "odd_steps", odd)
