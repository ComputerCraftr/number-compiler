"""Exact finite digit-band windows from authenticated 2rev10 images."""

from __future__ import annotations

from collections.abc import Generator
from contextlib import AbstractContextManager

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.ordered_output import (
    OrderedBandOutput,
    OrderedSourceCoverage,
)
from number_compiler.arithmetic.fields.ordered_band import (
    OrderedDigitBandFrame,
    ordered_digit_band_frame,
    ordered_digit_band_output,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.double_reverse.source_adapter import (
    DoubleReverseAction,
    DoubleReverseSource,
    DoubleReverseSourceAdapter,
)


def source_issued_ordered_digit_band(
    source_index: int,
    max_steps: int,
    steps: int,
    width: int,
    modulus: int,
    scheduler: TileScheduler,
    adapter: DoubleReverseSourceAdapter,
    source: DoubleReverseSource,
    arena: LedgerSLPArena,
    ledger: ResourceLedger,
    scratch_owner: int,
    *,
    coefficients: tuple[int, ...] | None = None,
    trace: bool = False,
) -> OrderedBandOutput:
    """Return exact bands for every scheduler-issued physical source tick."""

    steps = require_integer(steps, "physical matrix ticks", 1, 4096)
    if source_index + steps > max_steps:
        raise BlockContextBudgetExceeded(
            "ordered digit band exceeds the remaining source step budget"
        )

    def reserve(entries: int, nodes: int) -> AbstractContextManager[object]:
        return ledger.reservation(scratch_owner, entries=entries, nodes=nodes)

    def frames() -> Generator[OrderedDigitBandFrame, None, None]:
        for offset in range(steps):
            action = DoubleReverseAction(source_index + offset)
            image = scheduler.source_image(adapter, source, action)
            view = scheduler.source_image_core().view(image)
            payload = adapter.view_payload(view)
            if (
                payload.source is not source
                or payload.action != action
                or view.binding.source is not source
                or view.binding.action != action
            ):
                raise ValueError("ordered band image has a foreign source action")
            root = payload.root
            source_width = arena.nodes[root].length

            def digit_from_least_significant(
                position: int, bound_root: int = root, bound_width: int = source_width
            ) -> int:
                return symbol_at(arena, bound_root, bound_width - position - 1)

            yield ordered_digit_band_frame(
                offset, source_width, width, digit_from_least_significant
            )

    return ordered_digit_band_output(
        source_index,
        steps,
        width,
        modulus,
        frames,
        reserve,
        source_coverage=OrderedSourceCoverage.SCHEDULER_WINDOW,
        coefficients=coefficients,
        trace=trace,
    )
