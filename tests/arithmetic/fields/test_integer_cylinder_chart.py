"""Joint-adic chart arithmetic, distinct from source-branch admission."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.arithmetic.fields.skew_transfer import (
    SkewTransfer,
    integer_dyadic_fiber_action,
)
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.hashlife.execution.dyadic_return_records import DyadicReturnLaw
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
)
from number_compiler.sequences.collatz.physical_images import COLLATZ_PHYSICAL_LAW


@pytest.mark.parametrize("law", (COLLATZ_PHYSICAL_LAW, ANTIHYDRA_ARITHMETIC_LAW))
@pytest.mark.parametrize("width", (0, 1, 4, 6, 8, 16))
def test_production_endpoint_uses_source_bound_fiber_chart(
    law: DyadicReturnLaw, width: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    # No exact-state cycle shortcut: every high fiber must share this branch.
    law = replace(law, cycle=None)
    for residue in (0, min(7, (1 << width) - 1)):
        source = residue + (17 << width)
        expected = source
        for _ in range(width):
            bit = expected % 2
            expected = (law.gains[bit] * expected + law.offsets[bit]) // 2
        workspace = DyadicReturnImageWorkspace(ResourceLedger(), source, width, law)
        try:
            chart = integer_dyadic_fiber_action(
                workspace.summary().transfer, residue, width
            )
            assert chart.addend + chart.multiplier * 17 == expected

            # This consumer doesn't reconstruct the full input or read history.
            def forbidden(*args: object) -> int:
                raise AssertionError("endpoint reconstructed input or history")

            monkeypatch.setattr(workspace, "_source_value", forbidden)
            monkeypatch.setattr(workspace, "branch_segments", forbidden)
            assert workspace.endpoint() == expected
            assert (
                workspace.ledger.counters[
                    workspace.counter_prefix + "_fiber_endpoint_demands"
                ]
                == 1
            )
            if law.gains == (3, 3):
                assert chart.multiplier == 3**width
                # Vanishing is modulo a demanded 3-adic precision, not over Z.
                assert (chart.multiplier * 17) % (3**width) == 0
        finally:
            workspace.dispose()


def test_accelerated_six_event_chart_retains_variable_source_precision() -> None:
    # Independent bounded oracle: E is not six for six accelerated odd events.
    for source in (1, 3, 27, 931386509544713451):
        value, offset, divisions = source, 0, 0
        for _ in range(6):
            numerator = 3 * value + 1
            exponent = (numerator & -numerator).bit_length() - 1
            offset = 3 * offset + (1 << divisions)
            divisions += exponent
            value = numerator >> exponent
        bits = divisions + 1
        residue = source % (1 << bits)
        chart = integer_dyadic_fiber_action(
            SkewTransfer(729, offset, 1 << divisions), residue, bits
        )
        assert chart.multiplier == 1458
        assert chart.addend % 2 == 1
        assert chart.addend + chart.multiplier * (source >> bits) == value
        assert ((chart.addend - 1) // 2) % 3 in (0, 2)
        if source == 1:
            assert divisions == 12
            assert chart.addend == 1


@pytest.mark.parametrize(
    "transfer,origin,precision",
    (
        (SkewTransfer(3, 0, 2), 1, 1),  # Nonintegral origin.
        (SkewTransfer(3, 0, 4), 0, 1),  # Nonintegral stride.
        (SkewTransfer(3, 0, 3), 0, 1),
        (SkewTransfer(3, 0, 0), 0, 1),
        (SkewTransfer(3, 0, 2), 2, 1),
        (SkewTransfer(3, 0, 2), 0, -1),
    ),
)
def test_rechart_rejects_invalid_cylinder_arithmetic(
    transfer: SkewTransfer[int], origin: int, precision: int
) -> None:
    with pytest.raises(ValueError):
        integer_dyadic_fiber_action(transfer, origin, precision)


def test_rechart_is_not_source_admission_and_cannot_replace_a_published_skew() -> None:
    # The supplied patch accepts this false six-event Collatz occurrence.
    # Its arithmetic is consistent, but it is not evidence about Collatz.
    chart = integer_dyadic_fiber_action(SkewTransfer(729, 45927, 64), 1, 7)
    assert chart.addend == 729
    workspace = DyadicReturnImageWorkspace(ResourceLedger(), 1, 6, COLLATZ_PHYSICAL_LAW)
    try:
        transfer = workspace.summary().transfer
        old = transfer.offset
        object.__setattr__(transfer, "offset", 729)
        with pytest.raises(ValueError, match="publication was altered"):
            workspace.endpoint()
        object.__setattr__(transfer, "offset", old)
        assert workspace.endpoint() == 1
    finally:
        workspace.dispose()


def test_singleton_cycle_rechart_does_not_allocate_the_source_stride() -> None:
    assert integer_dyadic_fiber_action(SkewTransfer(0, 1, 1), 1, 10**20).addend == 1
