"""Finite source-scoped border and pair transfer from a 2rev10 endpoint."""

from __future__ import annotations

from contextlib import ExitStack
from itertools import pairwise

from number_compiler.arithmetic.automata.slp_walks import iter_symbols, symbol_at
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.interfaces.border_macros import BorderMacroIdentity
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


def _identity_packet(identity: BorderMacroIdentity) -> dict[str, object]:
    if type(identity) is not BorderMacroIdentity:
        raise TypeError("source transfer metadata requires a typed border identity")
    return {
        "family": identity.family.value,
        "kind": identity.kind.value,
        "signature": identity.signature,
    }


def _root_pair(term: DoubleReverseTerm, root: int, pair_depth: int) -> tuple[int, int]:
    width = term._arena.nodes[root].length
    if width <= 2 * pair_depth:
        raise UncertifiedPointedStencilError(
            "source endpoint is too narrow for the requested pair depth"
        )
    return (
        symbol_at(term._arena, root, pair_depth),
        symbol_at(term._arena, root, width - 1 - pair_depth),
    )


def _same_word(term: DoubleReverseTerm, left: int, right: int) -> bool:
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
    left_width = term._arena.nodes[left].length
    if left_width != term._arena.nodes[right].length:
        return False

    def record_visit(is_node: bool) -> None:
        if is_node:
            term._ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_STATE_COMPARISON_NODE_VISITS
            )

    def reserve_task() -> None:
        term._ledger.reserve(term._scratch_owner, entries=1, nodes=1)

    def release_tasks(count: int) -> None:
        term._ledger.release(term._scratch_owner, entries=count, nodes=count)

    with ExitStack() as streams:
        left_symbols = streams.enter_context(
            closing_output_stream(
                iter_symbols(
                    term._arena,
                    left,
                    on_task=record_visit,
                    reserve_task=reserve_task,
                    release_tasks=release_tasks,
                    check_open=term._check_open,
                )
            )
        )
        right_symbols = streams.enter_context(
            closing_output_stream(
                iter_symbols(
                    term._arena,
                    right,
                    on_task=record_visit,
                    reserve_task=reserve_task,
                    release_tasks=release_tasks,
                    check_open=term._check_open,
                )
            )
        )
        for left_symbol, right_symbol in zip(left_symbols, right_symbols, strict=True):
            term._ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_STATE_COMPARISON_DIGITS
            )
            if left_symbol != right_symbol:
                return False
    return True


def source_transfer_packet(
    term: DoubleReverseTerm, *, steps: int, pair_depth: int
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
    term._check_open()
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
        entry, prepared = term._prepare_bank_source(
            max_prefix=min(32, term.generation - 2)
        )
        if (
            type(entry) is not DoubleReverseSourcePrefix
            or type(prepared) is not PointedBankSource
        ):
            raise TypeError("term returned an invalid pointed source cursor")
        prepared.validate(require_issued_cursor=True)
        endpoint_root = term._root()
        engine = prepared.engine
        endpoint_action = engine.advance_action(
            prepared.root, prepared.f_steps, prepared.phase
        )
        engine.validate_action(endpoint_action)
        action_root = engine.root_of(endpoint_action.target)
        if (
            not _same_word(term, action_root, endpoint_root)
            or prepared.physical_prefix + 2 * prepared.f_steps != term.generation
            or prepared.width_out != term._arena.nodes[endpoint_root].length
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
        from .border_macro_catalogue import (
            SourceBorderMacroCatalogue,
            source_border_macro_catalogue,
        )

        catalogue = source_border_macro_catalogue(
            future,
            root_path,
            action_path,
            pair_depth=pair_depth,
        )
        if type(catalogue) is not SourceBorderMacroCatalogue:
            raise TypeError("source border owner returned an invalid catalogue")
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
        phase = catalogue.phases[ordinal]
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
        source_matrices.append(guarded)
        source_action = source_action.then(guarded)

    if source_action.endpoints(actual_pairs[0]) != (actual_pairs[-1],):
        raise AssertionError("source-scoped matrix lost its exact completed child path")

    border_phases = tuple(
        {
            "phase": item.phase.phase,
            "physical_interval": (
                item.phase.source.physical_tick,
                item.phase.target.physical_tick,
            ),
            "identity": _identity_packet(item.phase.identity),
            "source_root": item.phase.source.root,
            "target_root": item.phase.target.root,
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
        for item in catalogue.phases
    )
    return {
        "status": "available",
        "family": "2rev10",
        "source_generation": term.generation,
        "physical_interval": (term.generation, term.generation + steps),
        "physical_ticks": steps,
        "pair_depth": pair_depth,
        "pair_coordinate_order": PAIR_COORDINATE_ORDER,
        "source_root": action_root,
        "target_root": root_path[-1],
        "exact_completed_children_joined": True,
        "source_guard_applied_before_matrix_composition": True,
        "matrix_semantics": "source_scoped_exact_pair_path",
        "source_pair_path": actual_pairs,
        "transition_rows": source_action.rows,
        "phase_matrices": tuple(matrix.rows for matrix in source_matrices),
        "border_phases": border_phases,
        "four_tick_observed_words": tuple(
            {
                "identity": _identity_packet(macro.identity),
                "physical_interval": (
                    term.generation + 2 * macro.start_phase,
                    term.generation + 2 * macro.end_phase,
                ),
                "width_interval": (macro.width_in, macro.width_out),
                "mod99": (macro.mod99_in, macro.mod99_out),
                "mod198": (macro.mod198_in, macro.mod198_out),
                "physical_repeat_certified": False,
            }
            for macro in catalogue.four_tick_macros
        ),
        "depth_windows": tuple(
            {
                "physical_interval": (
                    window.start_generation,
                    window.end_generation,
                ),
                "source_root": root_path[window.start_f_steps],
                "target_root": root_path[window.start_f_steps + window.f_steps],
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


__all__ = [
    "MAX_F_STEPS_PER_WINDOW",
    "MAX_PAIR_DEPTH",
    "MAX_PHYSICAL_STEPS",
    "PAIR_COORDINATE_ORDER",
    "source_transfer_packet",
]
