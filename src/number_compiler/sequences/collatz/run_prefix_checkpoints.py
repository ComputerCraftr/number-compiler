"""Publish root dyadic checkpoints from already admitted Collatz blocks."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.parity import normalized_collatz
from number_compiler.sequences.collatz.source_cylinder_cache import (
    CollatzDyadicMacros,
)
from number_compiler.sequences.collatz.tape_width import (
    CollatzWidthSpineAccumulator,
)
from number_compiler.sequences.collatz.temporal_dyadic import D8CylinderFrame

_MIN_CHECKPOINT_WIDTH = 8


def temporal_run_share_width(seed: int, physical_ticks: int) -> int:
    """Choose the first power-of-two run checkpoint for this source horizon."""
    bounded_extent = min(max(8, seed.bit_length()), max(8, physical_ticks // 2))
    return 1 << (bounded_extent.bit_length() - 1)


def observe_temporal_run_prefix(
    macros: CollatzDyadicMacros | None,
    width_spine: CollatzWidthSpineAccumulator,
    *,
    previous_source: int,
    previous_width: int,
    previous_ones: int,
    current: int,
    normalized: int,
    one_symbols: int,
    anchor: int,
    share_width: int,
) -> None:
    """Publish one already-consumed run prefix at its exact query boundary."""
    if macros is None or not previous_width < normalized <= share_width:
        return
    macros.observe(
        previous_source,
        normalized - previous_width,
        one_symbols - previous_ones,
        current,
        anchor=anchor,
        tape_width_summary=width_spine.segment_summary(
            previous_source.bit_length(),
            current.bit_length(),
            normalized - previous_width,
            one_symbols - previous_ones,
        ),
    )
    width_spine.reset_segment()


def _crosses_root_checkpoint(start: int, width: int, maximum: int) -> bool:
    """Check whether a block crosses a retained root width without stepping it."""
    if any(type(value) is not int for value in (start, width, maximum)):
        raise TypeError("Collatz checkpoint extents require exact integers")
    if start < 0 or width < 0 or maximum < 0:
        raise ValueError("Collatz checkpoint extents must be nonnegative")
    if width == 0 or start >= maximum:
        return False
    checkpoint = 1 << max(3, start.bit_length())
    return checkpoint <= start + width and checkpoint <= maximum


def _checkpoint_widths(start: int, width: int, maximum: int) -> tuple[int, ...]:
    """Return global power-of-two boundaries crossed by one admitted block."""
    if width == 0 or start >= maximum:
        return ()
    stop = start + width
    checkpoint = 1 << max(3, start.bit_length())
    crossed: list[int] = []
    while checkpoint <= stop and checkpoint <= maximum:
        crossed.append(checkpoint)
        checkpoint *= 2
    return tuple(crossed)


def _publish_checkpoints(
    macros: CollatzDyadicMacros,
    scratch: RunArithmeticWorkspace,
    *,
    anchor: int,
    source: int,
    normalized_offset: int,
    odd_offset: int,
    block_width: int,
    prefix: Callable[[int], tuple[int, int, int, int]],
) -> int:
    if (
        type(macros) is not CollatzDyadicMacros
        or type(scratch) is not RunArithmeticWorkspace
    ):
        raise TypeError("Collatz checkpoints require their cache and scratch owners")
    if not scratch.active:
        raise RuntimeError("Collatz checkpoint arithmetic needs active scratch")
    if any(
        type(value) is not int
        for value in (anchor, source, normalized_offset, odd_offset, block_width)
    ):
        raise TypeError("Collatz checkpoint coordinates require exact integers")
    if (
        anchor <= 0
        or source <= 0
        or normalized_offset < 0
        or not 0 <= odd_offset <= normalized_offset
        or block_width <= 0
    ):
        raise ValueError("Collatz checkpoint coordinates are outside their domain")

    ledger: ResourceLedger = macros.ledger
    published = 0
    for checkpoint in _checkpoint_widths(
        normalized_offset, block_width, anchor.bit_length()
    ):
        prefix_width = checkpoint - normalized_offset
        try:
            scratch.require_bits(
                16 * (anchor.bit_length() + source.bit_length() + prefix_width + 32)
            )
            endpoint, prefix_ones, primitive_steps, action_bits = prefix(prefix_width)
            if any(
                type(value) is not int
                for value in (endpoint, prefix_ones, primitive_steps, action_bits)
            ):
                raise TypeError("Collatz checkpoint prefix returned a non-integer")
            if primitive_steps:
                ledger.bump(
                    _collatz_keys.COLLATZ_TEMPORAL_ROOT_CHECKPOINT_D8_STEPS,
                    primitive_steps,
                )
            ledger.bump(_collatz_keys.COLLATZ_TEMPORAL_ROOT_CHECKPOINT_CANDIDATES)
            ledger.bump(
                _collatz_keys.COLLATZ_TEMPORAL_ROOT_CHECKPOINT_OPERAND_BITS,
                anchor.bit_length()
                + source.bit_length()
                + endpoint.bit_length()
                + checkpoint.bit_length(),
            )
            ledger.bump(
                _collatz_keys.COLLATZ_TEMPORAL_ROOT_CHECKPOINT_ACTION_OPERAND_BITS,
                action_bits,
            )
            if not 0 <= prefix_ones <= prefix_width:
                raise AssertionError("Collatz root checkpoint odd count is invalid")
            if endpoint <= 2:
                return published
            if macros.remember(
                anchor,
                checkpoint,
                odd_offset + prefix_ones,
                endpoint,
            ):
                published += 1
                ledger.bump(_collatz_keys.COLLATZ_TEMPORAL_ROOT_CHECKPOINT_PUBLICATIONS)
        except BlockContextBudgetExceeded:
            ledger.bump(_collatz_keys.COLLATZ_TEMPORAL_ROOT_CHECKPOINT_BUDGET_BYPASSES)
            break
    return published


def _publish_run_root_checkpoints(
    macros: CollatzDyadicMacros,
    scratch: RunArithmeticWorkspace,
    *,
    anchor: int,
    source: int,
    normalized_offset: int,
    odd_offset: int,
    run_length: int,
    odd_run: bool,
) -> int:
    """Publish crossed root prefixes by the exact zero/one-run affine action."""
    if type(odd_run) is not bool:
        raise TypeError("Collatz run kind must be Boolean")

    def prefix(width: int) -> tuple[int, int, int, int]:
        action = (
            DyadicTerminalFieldAction.one_run(width)
            if odd_run
            else DyadicTerminalFieldAction.zero_run(width)
        )
        endpoint = action.endpoint(source)
        action_bits = sum(
            value.bit_length()
            for value in (
                action.gain,
                action.offset,
                action.sum_gain,
                action.sum_offset,
                action.previous_gain,
                action.previous_offset,
            )
        )
        return endpoint, width if odd_run else 0, 0, action_bits

    return _publish_checkpoints(
        macros,
        scratch,
        anchor=anchor,
        source=source,
        normalized_offset=normalized_offset,
        odd_offset=odd_offset,
        block_width=run_length,
        prefix=prefix,
    )


def _publish_d8_root_checkpoints(
    macros: CollatzDyadicMacros,
    scratch: RunArithmeticWorkspace,
    *,
    anchor: int,
    source: int,
    normalized_offset: int,
    odd_offset: int,
    endpoint: int,
    odd_symbols: int,
) -> int:
    """Publish a crossed root prefix from one D8 block with at most seven steps."""
    if type(endpoint) is not int or type(odd_symbols) is not int:
        raise TypeError("D8 checkpoint result requires exact integers")
    if not 0 <= odd_symbols <= 8:
        raise ValueError("D8 checkpoint odd count is invalid")

    def prefix(width: int) -> tuple[int, int, int, int]:
        if width == 8:
            return endpoint, odd_symbols, 0, 0
        value = source
        ones = 0
        operand_bits = 0
        for _ in range(width):
            before = value
            ones += value & 1
            value = normalized_collatz(value)
            operand_bits += before.bit_length() + value.bit_length()
        return value, ones, width, operand_bits

    return _publish_checkpoints(
        macros,
        scratch,
        anchor=anchor,
        source=source,
        normalized_offset=normalized_offset,
        odd_offset=odd_offset,
        block_width=8,
        prefix=prefix,
    )


def _publish_d8_frame_root_checkpoints(
    macros: CollatzDyadicMacros,
    scratch: RunArithmeticWorkspace,
    *,
    anchor: int,
    source_frame: D8CylinderFrame,
    normalized_offset: int,
    odd_offset: int,
    endpoint_frame: D8CylinderFrame,
    odd_symbols: int,
    ledger: ResourceLedger,
) -> None:
    """Publish a crossed D8 root point, charging its two required lifts."""
    source = source_frame.materialize()
    endpoint = endpoint_frame.materialize()
    ledger.bump(
        _collatz_keys.COLLATZ_TEMPORAL_ROOT_CHECKPOINT_FRAME_MATERIALIZATIONS, 2
    )
    ledger.bump(
        _collatz_keys.COLLATZ_TEMPORAL_ROOT_CHECKPOINT_FRAME_OPERAND_BITS,
        source.bit_length() + endpoint.bit_length(),
    )
    _publish_d8_root_checkpoints(
        macros,
        scratch,
        anchor=anchor,
        source=source,
        normalized_offset=normalized_offset,
        odd_offset=odd_offset,
        endpoint=endpoint,
        odd_symbols=odd_symbols,
    )
