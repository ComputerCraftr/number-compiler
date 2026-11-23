"""Exact finite digit-band windows from the authenticated Q19 path."""

from __future__ import annotations

from collections.abc import Callable, Generator
from contextlib import contextmanager
from typing import TYPE_CHECKING

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
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.ledger_records import ResourceScope

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
    )
    from number_compiler.sequences.reverse_add.source_workspace import (
        ReverseSourceImageWorkspace,
    )


def source_issued_ordered_digit_band(
    source_index: int,
    base: int,
    steps: int,
    width: int,
    modulus: int,
    ledger: ResourceLedger,
    workspace_factory: Callable[[], ReverseSourceImageWorkspace],
    *,
    coefficients: tuple[int, ...] | None = None,
    trace: bool = False,
) -> OrderedBandOutput:
    """Fold exact adjacent issued Q19 ports; no repeated-word authority."""

    source_index = require_integer(source_index, "reverse/add generation", 0)
    base = require_integer(base, "reverse/add radix", 2)
    steps = require_integer(steps, "physical matrix ticks", 1, 128)
    if source_index == 0:
        raise ValueError(
            "ordered reverse/add bands require a completed positive-generation "
            "Q19 endpoint"
        )
    if base != 10:
        raise ValueError("ordered reverse/add bands require decimal source digits")

    owner = ledger.register(
        f"reverse-ordered-band-work-{ledger.owner_count}",
        "temporary_work",
        scope=ResourceScope.INDEX_OWNED,
    )

    @contextmanager
    def reserve(entries: int, nodes: int) -> Generator[None, None, None]:
        with ledger.reservation(owner, entries=entries, nodes=nodes):
            yield

    def frames() -> Generator[OrderedDigitBandFrame, None, None]:
        workspace = workspace_factory()
        q19_owner, current, _reused, _applications = (
            workspace.completed_q19_occurrence()
        )
        q19_owner.validate_issued_occurrence(current)
        if current.temporal_steps != source_index:
            raise ValueError("Q19 endpoint does not match term generation")

        for offset in range(steps):
            source_width = current.output_width

            def digit_from_least_significant(
                position: int, occurrence: ReversePairOutputOccurrence = current
            ) -> int:
                return q19_owner.digit(occurrence, position)

            yield ordered_digit_band_frame(
                offset, source_width, width, digit_from_least_significant
            )
            if offset + 1 < steps:
                current = q19_owner.apply_pair_step(current)
                q19_owner.validate_issued_occurrence(current)
                if current.temporal_steps != source_index + offset + 1:
                    raise ValueError("Q19 child does not follow the source seam")

    try:
        return ordered_digit_band_output(
            source_index,
            steps,
            width,
            modulus,
            frames,
            reserve,
            source_coverage=OrderedSourceCoverage.Q19_CHILD_PATH,
            coefficients=coefficients,
            trace=trace,
        )
    finally:
        ledger.mark_disposed(owner)
