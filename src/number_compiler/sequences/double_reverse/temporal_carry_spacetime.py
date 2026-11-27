"""Finite exact temporal squaring for the normalized 2rev10 carry stencil.

The helper computes a finite causal cone for ``T²``. Perfect binary tiles are
interned by their exact digit children inside one invocation, so distinct SLP
grammars for the same bounded source window share semantic tiles. Temporary
tile references are not retained across calls. This is a finite successor
constructor, not an all-depth period certificate.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, Protocol, cast

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.automata.temporal_cone import (
    CarrySpacetimePower,
    TemporalSquarePublicationFailed,
    TemporalSquareScratchCapacityRefused,
    TemporalSquareScratchReservation,
    TemporalSquareStats,
)
from number_compiler.resources.metric_keys import double_reverse as double_reverse_keys
from number_compiler.resources.owned_memo import LedgerReservation

from .stencil_moore import f_port_cell
from .temporal_packed_diagonal import (
    PACKED_DIAGONAL_MIN_STEPS,
    publish_packed_diagonal,
    record_square_work,
)

if TYPE_CHECKING:
    from .source_adapter import DoubleReverseSourceAdapter


_MAX_CELLS = 4096
_MAX_T2_STEPS = 1024
_MAX_LARGE_PACKED_T2_STEPS = 16384
_SHORT_RING_MIN_STEPS: int | None = None


def _try_short_ring_cone(
    arena: LedgerSLPArena,
    root: int,
    steps: int,
    scratch: TemporalSquareScratchReservation,
    on_source_task: Callable[[bool], None] | None,
    account_semantic_metrics: bool,
) -> tuple[int, TemporalSquareStats] | None:
    """Use a complete repeated one/two-digit halo for a centered F action."""
    node = arena.nodes[root]
    if (
        _SHORT_RING_MIN_STEPS is None
        or steps < _SHORT_RING_MIN_STEPS
        or node.kind != "REPEAT"
        or arena.ledger.max_nodes is not None
        or arena.ledger.max_cache_entries is not None
    ):
        return None
    width = arena.nodes[node.child].length
    if width not in (1, 2) or not scratch.try_acquire(32, 32):
        return None
    checkpoint = len(arena.nodes)
    try:
        from number_compiler.arithmetic.carry.decimal_ring_action import (
            centered_short_ring,
        )

        motif = tuple(symbol_at(arena, node.child, index) for index in range(width))
        target = centered_short_ring(motif, 2, steps)
        phase = steps % width
        target = target[phase:] + target[:phase]
        if on_source_task is not None:
            for _ in range(width):
                on_source_task(True)
        scratch.use_exact_growth()
        result = arena.repeat(arena.word(target), 2 * steps // width)
        if arena.nodes[result].length != 2 * steps:
            raise AssertionError("short-ring cone changed the output width")
        stats = TemporalSquareStats(0, 0, 0, width, 0)
        if account_semantic_metrics:
            record_square_work(arena, stats)
            arena.ledger.bump(double_reverse_keys.DOUBLE_REVERSE_F_MODULAR_RING_POWERS)
        return result, stats
    except BaseException as error:
        if len(arena.nodes) > checkpoint:
            try:
                arena.rollback_unpublished_suffix(checkpoint)
            except BaseException as cleanup_error:
                raise error from cleanup_error
        raise
    finally:
        scratch.release(32, 32)


def temporal_square_cone(
    arena: LedgerSLPArena,
    root: int,
    steps: int,
    *,
    scratch_owner: int,
    max_cells: int = _MAX_CELLS,
    on_source_task: Callable[[bool], None] | None = None,
    on_cone_visit: Callable[[bool], None] | None = None,
    on_tile_pair: Callable[[], None] | None = None,
    account_semantic_metrics: bool = False,
) -> tuple[int, TemporalSquareStats]:
    """Compute an exact ``T²`` cone from one complete ``4*steps`` causal halo."""
    if type(arena) is not LedgerSLPArena:
        raise TypeError("temporal square requires its exact ledgered SLP arena")
    if type(steps) is not int or steps < 1 or steps & (steps - 1):
        raise ValueError("temporal square requires a positive dyadic horizon")
    if steps > _MAX_T2_STEPS:
        raise ValueError("temporal square horizon exceeds the admitted bound")
    if type(max_cells) is not int or max_cells < 4 or max_cells > _MAX_CELLS:
        raise ValueError("temporal square cell bound is invalid")
    if type(scratch_owner) is not int or scratch_owner < 0:
        raise ValueError("temporal square scratch owner is invalid")
    if type(account_semantic_metrics) is not bool:
        raise TypeError("semantic metrics selector must be Boolean")
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("temporal square source root is invalid")
    arena.empty()
    source_width = arena.nodes[root].length
    if source_width != 4 * steps or source_width > max_cells:
        raise ValueError("temporal square source is not its complete admitted halo")

    if _SHORT_RING_MIN_STEPS is not None:
        checkpoint = len(arena.nodes)
        short_ring: tuple[int, TemporalSquareStats] | None = None
        try:
            with TemporalSquareScratchReservation(
                LedgerReservation(arena.ledger, scratch_owner)
            ) as scratch:
                short_ring = _try_short_ring_cone(
                    arena,
                    root,
                    steps,
                    scratch,
                    on_source_task,
                    account_semantic_metrics,
                )
        except BaseException as error:
            if short_ring is not None and len(arena.nodes) > checkpoint:
                try:
                    arena.rollback_unpublished_suffix(checkpoint)
                except BaseException as cleanup_error:
                    raise error from cleanup_error
            raise
        if short_ring is not None:
            return short_ring

    reservation = LedgerReservation(arena.ledger, scratch_owner)
    with TemporalSquareScratchReservation(reservation) as scratch:
        packed_attempt: TemporalSquareStats | None = None
        if steps >= PACKED_DIAGONAL_MIN_STEPS:
            stats = TemporalSquareStats(0, 0, 0, 0, 0)
            publication_checkpoint = len(arena.nodes)
            published_root: int | None = None
            try:
                packed_result = publish_packed_diagonal(
                    arena,
                    root,
                    steps,
                    scratch,
                    on_source_task,
                    stats,
                )
                published_root = packed_result[0]
                return packed_result
            except TemporalSquareScratchCapacityRefused:
                if len(arena.nodes) != publication_checkpoint:
                    raise AssertionError(
                        "packed scratch refusal occurred after output publication"
                    ) from None
                # Release packed scratch before using the exact semantic path.
                scratch.release_unused_capacity()
                packed_attempt = stats
            finally:
                if account_semantic_metrics and packed_attempt is None:
                    # Packed work counts source visits and row transforms.
                    try:
                        record_square_work(arena, stats)
                    except BaseException as record_error:
                        if (
                            published_root is not None
                            and len(arena.nodes) > publication_checkpoint
                        ):
                            try:
                                arena.rollback_unpublished_suffix(
                                    publication_checkpoint
                                )
                            except BaseException as cleanup_error:
                                raise cleanup_error from record_error
                        raise
        try:
            power = CarrySpacetimePower(
                scratch, on_cone_visit, on_tile_pair, four_cell_action=f_port_cell
            )
        except BaseException:
            if account_semantic_metrics and packed_attempt is not None:
                record_square_work(arena, packed_attempt)
            raise
        publication_checkpoint = len(arena.nodes)
        published_semantic_root: int | None = None
        try:
            source = power.compile_slp(
                arena,
                root,
                max_cells,
                on_source_task,
            )
            scratch.release_unused_capacity()
            center = power.middle(source)
            scratch.use_exact_growth()
            publication_checkpoint = len(arena.nodes)
            result = power.publish(arena, center)
            if arena.nodes[result].length != source_width // 2:
                try:
                    arena.rollback_unpublished_suffix(publication_checkpoint)
                except BaseException as cleanup_error:
                    raise AssertionError(
                        "temporal cone output width changed and rollback failed"
                    ) from cleanup_error
                raise AssertionError("temporal cone output has the wrong width")
            published_semantic_root = result
            stats = power.stats
            if packed_attempt is not None:
                stats.source_traversal_tasks += packed_attempt.source_traversal_tasks
                stats.packed_row_evaluations += packed_attempt.packed_row_evaluations
                stats.packed_row_operand_bits += packed_attempt.packed_row_operand_bits
                stats.packed_output_digit_visits += (
                    packed_attempt.packed_output_digit_visits
                )
            return result, stats
        finally:
            try:
                if account_semantic_metrics:
                    # Record partial/completed work before dropping the graph.
                    try:
                        record_square_work(
                            arena, power.stats, packed_attempt, include_semantic=True
                        )
                    except BaseException as record_error:
                        if (
                            published_semantic_root is not None
                            and len(arena.nodes) > publication_checkpoint
                        ):
                            try:
                                arena.rollback_unpublished_suffix(
                                    publication_checkpoint
                                )
                            except BaseException as cleanup_error:
                                raise cleanup_error from record_error
                            published_semantic_root = None
                        raise
            finally:
                try:
                    # Tracebacks retain frames, so clear the DAG on failures.
                    power.release_temporary_storage()
                except BaseException as cleanup_error:
                    if (
                        published_semantic_root is not None
                        and len(arena.nodes) > publication_checkpoint
                    ):
                        try:
                            arena.rollback_unpublished_suffix(publication_checkpoint)
                        except BaseException as rollback_error:
                            raise rollback_error from cleanup_error
                    raise


def try_source_bound_square_cone(
    arena: LedgerSLPArena,
    root: int,
    steps: int,
    scratch_owner: int,
) -> int | None:
    """Publish one exact cone; ``None`` declines before packed output publication."""
    if type(steps) is not int or steps < 1 or steps & (steps - 1):
        raise ValueError("source-bound cone requires a positive dyadic horizon")
    if steps > _MAX_T2_STEPS:
        if steps > _MAX_LARGE_PACKED_T2_STEPS:
            return None
        if type(arena) is not LedgerSLPArena:
            raise TypeError("source-bound cone requires its ledgered SLP arena")
        arena.empty()
        if type(root) is not int or not 0 <= root < len(arena.nodes):
            raise ValueError("source-bound cone root is invalid")
        if arena.nodes[root].length != 4 * steps:
            raise ValueError("source-bound cone needs its complete causal halo")
        if type(scratch_owner) is not int or scratch_owner < 0:
            raise ValueError("source-bound cone scratch owner is invalid")
        checkpoint = len(arena.nodes)
        stats = TemporalSquareStats(0, 0, 0, 0, 0)
        published: int | None = None
        work_recorded = False
        try:
            with TemporalSquareScratchReservation(
                LedgerReservation(arena.ledger, scratch_owner)
            ) as scratch:
                short_ring = _try_short_ring_cone(
                    arena, root, steps, scratch, None, True
                )
                if short_ring is not None:
                    published = short_ring[0]
                    work_recorded = True
                else:
                    try:
                        published, _ = publish_packed_diagonal(
                            arena,
                            root,
                            steps,
                            scratch,
                            None,
                            stats,
                        )
                    except TemporalSquareScratchCapacityRefused:
                        if len(arena.nodes) != checkpoint:
                            raise AssertionError(
                                "packed scratch refusal occurred after publication"
                            ) from None
                        work_recorded = True
                        record_square_work(arena, stats)
                        return None
                    work_recorded = True
                    record_square_work(arena, stats)
        except BaseException as error:
            if not work_recorded:
                try:
                    record_square_work(arena, stats)
                except BaseException as record_error:
                    raise error from record_error
            if published is not None and len(arena.nodes) > checkpoint:
                try:
                    arena.rollback_unpublished_suffix(checkpoint)
                except BaseException as cleanup_error:
                    raise error from cleanup_error
            raise
        return published

    publication_checkpoint = len(arena.nodes)

    try:
        result, _statistics = temporal_square_cone(
            arena,
            root,
            steps,
            scratch_owner=scratch_owner,
            max_cells=_MAX_CELLS,
            account_semantic_metrics=True,
        )
    except TemporalSquareScratchCapacityRefused:
        if len(arena.nodes) != publication_checkpoint:
            raise AssertionError(
                "scratch refusal occurred after temporal cone publication"
            ) from None
        return None

    return result


__all__ = [
    "TemporalSquarePublicationFailed",
    "TemporalSquareScratchCapacityRefused",
    "temporal_square_cone",
    "try_source_bound_square_cone",
    "try_native_reflected_endpoint",
]


class _ReflectedMultiply(Protocol):
    def multiply(self, source: str, ticks: int) -> str: ...


def try_native_reflected_endpoint(
    arena: LedgerSLPArena, root: int, steps: int, phase: int, scratch_owner: int
) -> int | None:
    """Optionally publish one bounded, source-checked C0 reflected endpoint."""
    import os

    if os.environ.get("NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY") != "1":
        return None
    return _native_reflected_endpoint(arena, root, steps, phase, scratch_owner)


def _reflected_kernel() -> _ReflectedMultiply | None:
    from importlib import import_module

    try:
        return cast(
            _ReflectedMultiply,
            import_module("number_compiler.kernels._reflected_multiply"),
        )
    except ModuleNotFoundError as error:
        if error.name != "number_compiler.kernels._reflected_multiply":
            raise
        return None


def try_native_source_suffix(
    adapter: DoubleReverseSourceAdapter, ticks: int
) -> int | None:
    """Bind one native endpoint to the authenticated C0 suffix of the initial source."""
    import os

    from .temporal_hashlife_types import UncertifiedPointedStencilError

    if os.environ.get("NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY", "1") != "1":
        return None
    ledger = adapter.ledger
    if ledger.max_nodes is not None or ledger.max_cache_entries is not None:
        return None
    native = _reflected_kernel()
    if native is None:
        return None
    try:
        entry = adapter.certified_prefix_entry(
            ticks, max_prefix=16, require_even_remainder=True
        )
    except UncertifiedPointedStencilError:
        return None
    engine = adapter.temporal_hashlife
    phase = entry.certified_phase
    if phase is None or engine.validate_source_prefix(entry) is not entry:
        raise ValueError("native reflected suffix requires its issued border")
    root = engine.root_of(entry.target)
    remaining = ticks - entry.physical_steps
    if remaining <= 0 or remaining % 2:
        raise ValueError("issued reflected suffix has the wrong physical clock")
    return _native_reflected_endpoint(
        adapter.arena,
        root,
        remaining // 2,
        phase,
        adapter.scratch_owner,
        native,
        suffix_width_admitted=lambda width: (
            adapter.width_bits(width) <= adapter.max_state_bits
        ),
    )


def _native_reflected_endpoint(
    arena: LedgerSLPArena,
    root: int,
    steps: int,
    phase: int,
    scratch_owner: int,
    native: _ReflectedMultiply | None = None,
    *,
    suffix_width_admitted: Callable[[int], bool] | None = None,
) -> int | None:
    from contextlib import ExitStack, closing

    from number_compiler.arithmetic.automata.slp_walks import iter_symbols
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    from .temporal_hashlife_borders import edge_phase, growth_ports

    ticks = 2 * steps
    width = arena.nodes[root].length
    if not 128 <= ticks <= 8192 or not 4 <= width <= 32 * ticks:
        return None
    ledger = arena.ledger
    if ledger.max_nodes is not None or ledger.max_cache_entries is not None:
        return None
    if native is None:
        native = _reflected_kernel()
        if native is None:
            return None
    slots = 128 * 1000 + 256 * (width + ticks + 256)
    if slots > 64 * 1024 * 1024:
        return None
    left, right = growth_ports(phase, steps)
    final_width = width + left + right
    if suffix_width_admitted is not None and not suffix_width_admitted(final_width):
        return None
    checkpoint = len(arena.nodes)
    try:
        with ExitStack() as stack:
            try:
                stack.enter_context(
                    ledger.reservation(scratch_owner, nodes=slots, entries=slots)
                )
            except BlockContextBudgetExceeded:
                return None
            with closing(
                iter_symbols(arena, root, ledger=ledger, owner=scratch_owner)
            ) as source:
                digits = bytes(source)
            if len(digits) != width or any(digit > 9 for digit in digits):
                raise ValueError("native reflected source width or digit mismatch")
            if edge_phase((digits[0], digits[1]), (digits[-2], digits[-1])) != phase:
                raise ValueError("native reflected source has another issued phase")
            word = bytes(digit + 48 for digit in digits).decode("ascii")
            result = native.multiply(word, ticks)
            if (
                type(result) is not str
                or not result.isascii()
                or not result.isdecimal()
                or len(result) != final_width
                or edge_phase(divmod(int(result[:2]), 10), divmod(int(result[-2:]), 10))
                != (phase + 2 * steps) % 4
            ):
                raise ValueError("native reflected endpoint changed its issued borders")
            target = arena.word(tuple(ord(char) - 48 for char in result))
            if suffix_width_admitted is not None:
                ledger.bump(
                    double_reverse_keys.DOUBLE_REVERSE_NATIVE_SUFFIX_TICKS, ticks
                )
                ledger.bump(
                    double_reverse_keys.DOUBLE_REVERSE_REPRESENTED_GROWTH_CELLS,
                    left + right,
                )
            return target
    except BaseException:
        arena.rollback_unpublished_suffix(checkpoint)
        raise
