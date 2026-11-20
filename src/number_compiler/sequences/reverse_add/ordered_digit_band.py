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
    ordered_digit_band_output,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.ledger_records import ResourceScope

if TYPE_CHECKING:
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
            lower_digits = tuple(
                q19_owner.digit(current, position) if position < source_width else 0
                for position in range(width - 1, -1, -1)
            )
            upper_digits = tuple(
                q19_owner.digit(current, source_width - position - 1)
                if position < source_width
                else 0
                for position in range(width)
            )
            yield OrderedDigitBandFrame(
                tick_offset=offset,
                lower_digits=lower_digits,
                upper_digits=upper_digits,
                lower_source_letters=min(width, source_width),
                upper_source_letters=min(width, source_width),
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
