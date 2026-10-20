"""The centered-zero Antihydra source is an exact fixed-point run."""

from number_compiler.hashlife.execution.dyadic_return_actions import append_source
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnSourceRecord,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageDemand,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
    AntihydraArithmeticImageWorkspace,
)
from tests.support.source_image_assertions import dyadic_image_summary


def test_centered_zero_fixed_point_preserves_literal_bits_and_prefix_safety() -> None:
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, 1, shared_cache=False)
    try:
        assert workspace.law is ANTIHYDRA_ARITHMETIC_LAW
        for width in (1, 4, 16, 32, 64):
            source = append_source(
                workspace,
                DyadicReturnSourceRecord(1, width, 0, None, None, None, 0, True),
            )
            action = workspace.action_for_extent(width)
            image = workspace.scheduler.source_image_demanded(
                workspace,
                source,
                action,
                SourceImageDemand("physical-summary"),
            )
            view = workspace.scheduler.source_image_core().view(image)
            summary = dyadic_image_summary(workspace, view)

            h = 1
            balance = 0
            minimum = 0
            bits: list[int] = []
            for _ in range(width):
                bit = h % 2
                bits.append(bit)
                balance += 2 - 3 * bit
                minimum = min(minimum, balance)
                h += h // 2

            endpoint, remainder = divmod(
                summary.transfer.upper + summary.transfer.offset,
                summary.transfer.lower,
            )
            assert not remainder
            assert h == endpoint == 1
            assert bits == [1] * width
            assert (summary.delta, summary.minimum, summary.odd_steps) == (
                balance,
                minimum,
                width,
            )
            assert (balance, minimum) == (-width, -width)
    finally:
        workspace.dispose()
