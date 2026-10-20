"""Finite source-scoped border and pair transfer from a 2rev10 endpoint."""

from __future__ import annotations

from contextlib import ExitStack
from itertools import pairwise
from typing import cast

from number_compiler.arithmetic.automata.slp_walks import iter_symbols, symbol_at
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)
from number_compiler.resources.output_stream_metrics import closing_output_stream
from number_compiler.sequences.double_reverse.source_bound_bank import PointedBankSource
from number_compiler.sequences.double_reverse.temporal_certified_halo import (
    SourceConditionedDepthWindowUnavailable,
)
from number_compiler.sequences.double_reverse.temporal_depth_transfer_matrix import (
    ALL_PAIRS,
    BooleanPairMatrix,
    SourceConditionedDepthWindow,
    pair_index,
    source_conditioned_depth_window,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import growth_ports
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    DoubleReversePortAction,
    DoubleReverseSourcePrefix,
    UncertifiedPointedStencilError,
)

from .power import DoubleReverseTerm

MAX_PHYSICAL_STEPS = 128
MAX_POWERED_PHYSICAL_STEPS = 4096
MAX_PAIR_DEPTH = 16
MAX_F_STEPS_PER_WINDOW = 4
PAIR_COORDINATE_ORDER = ("upper_msd_inward", "lower_lsd_inward")


def _unavailable(reason: str, *, steps: int, pair_depth: int) -> dict[str, object]:
    return {
        "status": "unavailable",
        "reason": reason,
        "physical_ticks": steps,
        "pair_depth": pair_depth,
        "physical_repeat_certified": False,
        "future_repetition_claimed": False,
    }


def _root_pair(term: DoubleReverseTerm, root: int, pair_depth: int) -> tuple[int, int]:
    width = term.source_arena.nodes[root].length
    if width <= 2 * pair_depth:
        raise UncertifiedPointedStencilError(
            "source endpoint is too narrow for the requested pair depth"
        )
    return (
        symbol_at(term.source_arena, root, pair_depth),
        symbol_at(term.source_arena, root, width - 1 - pair_depth),
    )


def same_word(term: DoubleReverseTerm, left: int, right: int) -> bool:
    """Compare complete bounded SLP words without requiring canonical roots.

    The physical source adapter and the powered temporal owner can factor the
    same exact word through different CONCAT/REPEAT nodes. Root handles are
    therefore not a semantic equality test. Width is admitted by the term's
    state-bit budget. Each root is streamed once; the compared digits and
    visited grammar nodes use the existing state-comparison counters, and
    retained traversal tasks are charged to the term's scratch owner.
    """
    if left == right:
        return True
    left_width = term.source_arena.nodes[left].length
    if left_width != term.source_arena.nodes[right].length:
        return False

    def record_visit(is_node: bool) -> None:
        if is_node:
            term.resource_ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_STATE_COMPARISON_NODE_VISITS
            )

    def reserve_task() -> None:
        term.resource_ledger.reserve(term.scratch_owner, entries=1, nodes=1)

    def release_tasks(count: int) -> None:
        term.resource_ledger.release(term.scratch_owner, entries=count, nodes=count)

    with ExitStack() as streams:
        left_symbols = streams.enter_context(
            closing_output_stream(
                iter_symbols(
                    term.source_arena,
                    left,
                    on_task=record_visit,
                    reserve_task=reserve_task,
                    release_tasks=release_tasks,
                    check_open=term.check_open,
                )
            )
        )
        right_symbols = streams.enter_context(
            closing_output_stream(
                iter_symbols(
                    term.source_arena,
                    right,
                    on_task=record_visit,
                    reserve_task=reserve_task,
                    release_tasks=release_tasks,
                    check_open=term.check_open,
                )
            )
        )
        for left_symbol, right_symbol in zip(left_symbols, right_symbols, strict=True):
            term.resource_ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_STATE_COMPARISON_DIGITS
            )
            if left_symbol != right_symbol:
                return False
    return True


def chronological_source_transfer_packet(
    term: DoubleReverseTerm,
    *,
    steps: int,
    pair_depth: int,
    include_trace: bool,
) -> dict[str, object]:
    """Join a bounded forward interval to exact endpoint children.

    ``steps`` counts physical generations from ``term.generation``. The
    current depth owner exposes exact T-squared children, so only even spans
    are admitted. Every depth matrix is checked against the source root pair
    and typed border path before composition.
    """
    if type(term) is not DoubleReverseTerm:
        raise TypeError("2rev10 source transfer requires DoubleReverseTerm")
    if type(steps) is not int or not 2 <= steps <= MAX_PHYSICAL_STEPS or steps % 2:
        raise ValueError(f"physical ticks must be even and in 2..{MAX_PHYSICAL_STEPS}")
    if type(pair_depth) is not int or not 1 <= pair_depth <= MAX_PAIR_DEPTH:
        raise ValueError(f"pair depth must be in 1..{MAX_PAIR_DEPTH}")
    term.check_open()
    if term.generation + steps > term.max_steps:
        return _unavailable(
            "requested future interval exceeds the term's physical-step budget",
            steps=steps,
            pair_depth=pair_depth,
        )
    if term.generation < 2:
        return _unavailable(
            "a certified pointed endpoint requires at least two completed ticks",
            steps=steps,
            pair_depth=pair_depth,
        )

    try:
        entry, prepared = term.prepare_bank_source(
            max_prefix=min(32, term.generation - 2)
        )
        if (
            type(entry) is not DoubleReverseSourcePrefix
            or type(prepared) is not PointedBankSource
        ):
            raise TypeError("term returned an invalid pointed source cursor")
        prepared.validate(require_issued_cursor=True)
        endpoint_root = term.endpoint_root()
        engine = prepared.engine
        endpoint_action = engine.advance_action(
            prepared.root, prepared.f_steps, prepared.phase
        )
        engine.validate_action(endpoint_action)
        action_root = engine.root_of(endpoint_action.target)
        if (
            not same_word(term, action_root, endpoint_root)
            or prepared.physical_prefix + 2 * prepared.f_steps != term.generation
            or prepared.width_out != term.source_arena.nodes[endpoint_root].length
        ):
            raise ValueError("prepared source cursor does not equal the term endpoint")
        # Continue from the authenticated action root. The independently
        # materialized endpoint root may have a distinct SLP factorization;
        # exact word equality above is the bridge, while this action retains
        # the original prefix issuer's lineage.
        endpoint_phase = engine.certify(endpoint_root)
        if (
            endpoint_phase is None
            or endpoint_action.phase_out != endpoint_phase
            or engine.certify(action_root) != endpoint_phase
        ):
            raise ValueError(
                "prepared endpoint phase differs from its owner-issued action"
            )
        _root_pair(term, endpoint_root, pair_depth)
        lineage = (
            endpoint_action
            if prepared.lineage_action is None
            else prepared.lineage_action.then(endpoint_action)
        )
        engine.validate_action(lineage)
        future_f_steps = steps // 2
        left_births, right_births = growth_ports(endpoint_phase, future_f_steps)
        future = PointedBankSource(
            prepared.arena,
            engine,
            prepared.ledger,
            prepared.scratch_owner,
            term.generation,
            action_root,
            endpoint_phase,
            future_f_steps,
            prepared.arena.nodes[action_root].length + left_births + right_births,
            prepared.max_steps,
            prepared.max_state_bits,
            prepared.width_bits,
            entry,
            lineage,
        )
        future.validate(require_issued_cursor=True)
    except UncertifiedPointedStencilError as exc:
        return _unavailable(str(exc), steps=steps, pair_depth=pair_depth)
    except BlockContextBudgetExceeded as exc:
        return _unavailable(str(exc), steps=steps, pair_depth=pair_depth)

    roots = [action_root]
    actions: list[DoubleReversePortAction] = []
    current_root = action_root
    current_phase = endpoint_phase
    try:
        for _ in range(future_f_steps):
            action = engine.advance_action(current_root, 1, current_phase)
            engine.validate_action(action)
            if action.steps != 1 or action.phase_in != current_phase:
                raise ValueError("Hashlife returned a non-adjacent owner action")
            current_root = engine.root_of(action.target)
            current_phase = action.phase_out
            actions.append(action)
            roots.append(current_root)
        root_path = tuple(roots)
        action_path = tuple(actions)
        from .border_occurrences import (
            DoubleReverseBorderTrace,
            trace_double_reverse_border_occurrences,
        )

        border_occurrences = trace_double_reverse_border_occurrences(
            future,
            root_path,
            action_path,
            pair_depth=pair_depth,
        )
        if type(border_occurrences) is not DoubleReverseBorderTrace:
            raise TypeError("2rev10 trace owner returned an invalid border trace")
    except UncertifiedPointedStencilError as exc:
        return _unavailable(str(exc), steps=steps, pair_depth=pair_depth)
    except BlockContextBudgetExceeded as exc:
        return _unavailable(str(exc), steps=steps, pair_depth=pair_depth)

    try:
        actual_pairs = tuple(_root_pair(term, root, pair_depth) for root in root_path)
    except UncertifiedPointedStencilError as exc:
        return _unavailable(str(exc), steps=steps, pair_depth=pair_depth)
    # A depth window is intentionally bounded to four F steps. Split longer
    # admitted horizons into contiguous windows from this same prepared
    # source, then join their full relations in chronological order. Each
    # seam is checked against the already completed exact child path before
    # it can participate in matrix composition.
    window_f_step_limit = min(MAX_F_STEPS_PER_WINDOW, 17 - pair_depth)
    depth_windows: list[SourceConditionedDepthWindow] = []
    joined_depth_action = BooleanPairMatrix.identity()
    try:
        for start_f_step in range(0, future_f_steps, window_f_step_limit):
            window_f_steps = min(window_f_step_limit, future_f_steps - start_f_step)
            depth_window = source_conditioned_depth_window(
                future,
                outer_pairs=pair_depth,
                start_f_steps=start_f_step,
                f_steps=window_f_steps,
            )
            if type(depth_window) is not SourceConditionedDepthWindow:
                raise TypeError(
                    "source-conditioned owner returned an invalid depth window"
                )
            depth_window.validate_source_authority()
            end_f_step = start_f_step + window_f_steps
            if (
                depth_window.source_root != action_root
                or depth_window.start_generation != term.generation + 2 * start_f_step
                or depth_window.end_generation != term.generation + 2 * end_f_step
                or depth_window.transfer.pointed_trace
                != actual_pairs[start_f_step : end_f_step + 1]
                or depth_window.initial_pair != actual_pairs[start_f_step]
            ):
                raise ValueError(
                    "finite depth relation does not match its exact completed child path"
                )
            if depth_windows and (
                depth_windows[-1].end_generation != depth_window.start_generation
                or depth_windows[-1].transfer.pointed_trace[-1]
                != depth_window.transfer.pointed_trace[0]
            ):
                raise ValueError("source-conditioned depth windows have a broken seam")
            depth_windows.append(depth_window)
            joined_depth_action = joined_depth_action.then(depth_window.transfer.action)
    except (
        SourceConditionedDepthWindowUnavailable,
        UncertifiedPointedStencilError,
        BlockContextBudgetExceeded,
    ) as exc:
        return _unavailable(str(exc), steps=steps, pair_depth=pair_depth)
    if (
        not depth_windows
        or depth_windows[0].start_generation != term.generation
        or depth_windows[-1].end_generation != term.generation + steps
        or joined_depth_action.endpoints(actual_pairs[0]) != (actual_pairs[-1],)
    ):
        raise ValueError(
            "chronological depth-window join differs from its exact endpoint path"
        )

    source_action = BooleanPairMatrix.identity()
    source_matrices: list[BooleanPairMatrix] = []

    for ordinal, (source_root, target_root) in enumerate(pairwise(root_path)):
        phase = border_occurrences.phases[ordinal]
        if (
            phase.phase.source.root != source_root
            or phase.phase.target.root != target_root
            or phase.phase.source.owner is not engine
            or phase.phase.target.owner is not engine
            or phase.phase.source.physical_tick != term.generation + 2 * ordinal
            or phase.phase.target.physical_tick != term.generation + 2 * (ordinal + 1)
        ):
            raise ValueError(
                "typed border cursor does not name the exact completed child"
            )

        source_pair, target_pair = actual_pairs[ordinal : ordinal + 2]
        source_index = pair_index(source_pair)
        target_index = pair_index(target_pair)
        rows = [0] * len(ALL_PAIRS)
        rows[source_index] = 1 << target_index
        guarded = BooleanPairMatrix(tuple(rows))
        if include_trace:
            source_matrices.append(guarded)
        source_action = source_action.then(guarded)

    if source_action.endpoints(actual_pairs[0]) != (actual_pairs[-1],):
        raise AssertionError("source-scoped matrix lost its exact completed child path")

    summary = _chronological_summary(
        family="2rev10",
        source_generation=term.generation,
        steps=steps,
        pair_depth=pair_depth,
        source_root=action_root,
        target_root=root_path[-1],
        source_pair=actual_pairs[0],
        target_pair=actual_pairs[-1],
        matrix_semantics="source_scoped_exact_pair_path",
    )
    if not include_trace:
        return summary

    border_phases = tuple(
        {
            "phase": item.phase.phase,
            "physical_interval": (
                item.phase.source.physical_tick,
                item.phase.target.physical_tick,
            ),
            "identity": item.phase.identity.packet(),
            "source_root_local_diagnostic": item.phase.source.root,
            "target_root_local_diagnostic": item.phase.target.root,
            "source_border": item.phase.source_state,
            "target_border": item.phase.target_state,
            "fourth_digit_carries": item.fourth_digit_carries,
            "growth": item.growth,
            "mod99": (
                item.residue_action.source_mod99,
                item.residue_action.target_mod99,
            ),
            "mod198": (
                item.residue_action.source_mod198,
                item.residue_action.target_mod198,
            ),
        }
        for item in border_occurrences.phases
    )
    return {
        **summary,
        "status": "available",
        "source_pair_path": actual_pairs,
        "transition_rows": source_action.rows,
        "phase_matrices": tuple(matrix.rows for matrix in source_matrices),
        "border_phases": border_phases,
        "four_tick_observed_words": tuple(
            {
                "identity": macro.identity.packet(),
                "physical_interval": (
                    term.generation + 2 * macro.start_phase,
                    term.generation + 2 * macro.end_phase,
                ),
                "width_interval": (macro.width_in, macro.width_out),
                "mod99": (macro.mod99_in, macro.mod99_out),
                "mod198": (macro.mod198_in, macro.mod198_out),
                "physical_repeat_certified": False,
            }
            for macro in border_occurrences.four_tick_occurrences
        ),
        "depth_windows": tuple(
            {
                "physical_interval": (
                    window.start_generation,
                    window.end_generation,
                ),
                "source_root_local_diagnostic": root_path[window.start_f_steps],
                "target_root_local_diagnostic": root_path[
                    window.start_f_steps + window.f_steps
                ],
                "source_pair_path": window.transfer.pointed_trace,
                "causal_halo_pairs": window.source_halo.pairs,
                "transition_rows": window.transfer.action.rows,
            }
            for window in depth_windows
        ),
        "depth_window_joined_transition_rows": joined_depth_action.rows,
        "source_horizon_physical_ticks": steps,
        "physical_repeat_certified": False,
        "future_repetition_claimed": False,
    }


def _chronological_summary(
    *,
    family: str,
    source_generation: int,
    steps: int,
    pair_depth: int,
    source_root: int,
    target_root: int,
    source_pair: tuple[int, int],
    target_pair: tuple[int, int],
    matrix_semantics: str,
) -> dict[str, object]:
    """Build the non-trace packet shared by exact-path consumers."""
    return {
        "status": "available",
        "family": family,
        "source_generation": source_generation,
        "physical_interval": (source_generation, source_generation + steps),
        "physical_ticks": steps,
        "pair_depth": pair_depth,
        "pair_coordinate_order": PAIR_COORDINATE_ORDER,
        "source_root_local_diagnostic": source_root,
        "target_root_local_diagnostic": target_root,
        "source_pair": source_pair,
        "pointed_target_pair": target_pair,
        "matrix_semantics": matrix_semantics,
        "source_pair_path_guarded": True,
        "source_guard_applied_before_matrix_composition": True,
        "exact_completed_children_joined": True,
        "physical_repeat_certified": False,
        "future_repetition_claimed": False,
        "execution_authority": False,
    }


def _chronological_packet_summary(packet: dict[str, object]) -> dict[str, object]:
    """Project an explicitly requested full chronological packet to its summary."""
    source_path = cast(tuple[tuple[int, int], ...], packet["source_pair_path"])
    return _chronological_summary(
        family=cast(str, packet["family"]),
        source_generation=cast(int, packet["source_generation"]),
        steps=cast(int, packet["physical_ticks"]),
        pair_depth=cast(int, packet["pair_depth"]),
        source_root=cast(int, packet["source_root_local_diagnostic"]),
        target_root=cast(int, packet["target_root_local_diagnostic"]),
        source_pair=source_path[0],
        target_pair=source_path[-1],
        matrix_semantics=cast(str, packet["matrix_semantics"]),
    )


def _with_trace(
    summary: dict[str, object], details: dict[str, object]
) -> dict[str, object]:
    """Nest chronological detail under one declared trace field."""
    trace_keys = {
        "source_pair_path",
        "transition_rows",
        "phase_matrices",
        "matrix_semantics",
        "exact_completed_children_joined",
        "source_guard_applied_before_matrix_composition",
        "border_phases",
        "four_tick_observed_words",
        "depth_windows",
        "depth_window_joined_transition_rows",
        "source_horizon_physical_ticks",
    }
    trace = {key: value for key, value in details.items() if key in trace_keys}
    return {**summary, "trace": trace}


def source_transfer_packet(
    term: DoubleReverseTerm,
    *,
    steps: int,
    pair_depth: int,
    trace: bool = False,
) -> dict[str, object]:
    """Return the powered endpoint projection or an explicit bounded trace.

    On an admitted closed border, the default powers the nine-state border
    relation and residue clock, then reads the exact requested pair through
    source-rooted cones. If that projection is unavailable, a bounded exact
    chronological path remains the fallback. ``trace=True`` asks for that
    chronological detail explicitly and is capped at 128 physical ticks.
    """
    if type(trace) is not bool:
        raise TypeError("trace demand must be Boolean")
    if type(steps) is not int or steps < 2 or steps % 2:
        raise ValueError("physical matrix ticks must be a positive even number")
    if type(pair_depth) is not int or not 1 <= pair_depth <= MAX_PAIR_DEPTH:
        raise ValueError(f"pair depth must be in 1..{MAX_PAIR_DEPTH}")
    if trace:
        if steps > MAX_PHYSICAL_STEPS:
            raise ValueError(
                f"chronological trace is limited to {MAX_PHYSICAL_STEPS} physical ticks"
            )
        packet = chronological_source_transfer_packet(
            term, steps=steps, pair_depth=pair_depth, include_trace=True
        )
        if packet.get("status") != "available":
            return packet
        return _with_trace(_chronological_packet_summary(packet), packet)

    if steps > MAX_POWERED_PHYSICAL_STEPS:
        raise ValueError(
            f"powered matrix ticks are limited to {MAX_POWERED_PHYSICAL_STEPS}"
        )
    from .temporal_predictive_border import predictive_source_transfer

    powered = predictive_source_transfer(term, steps=steps, pair_depth=pair_depth)
    if powered.get("status") == "available":
        return powered
    if steps <= MAX_PHYSICAL_STEPS:
        # Preserve the prior exact source path when the powered cylinder does
        # not apply, while making its extra work visible in the packet.
        fallback = chronological_source_transfer_packet(
            term, steps=steps, pair_depth=pair_depth, include_trace=False
        )
        if fallback.get("status") == "available":
            return {
                **fallback,
                "construction": "bounded_exact_source_fallback",
                "powered_projection_unavailable": powered.get("reason"),
            }
    return powered


__all__ = [
    "MAX_F_STEPS_PER_WINDOW",
    "MAX_PAIR_DEPTH",
    "MAX_PHYSICAL_STEPS",
    "MAX_POWERED_PHYSICAL_STEPS",
    "PAIR_COORDINATE_ORDER",
    "source_transfer_packet",
]
