"""Powered 2rev10 border relation with exact source-rooted endpoint cones.

The nine-state relation retains every possible inward carry. Its powered
image is therefore a border envelope, while the requested source's endpoint
digits are read from exact pointed cones rooted at the authenticated source.
Neither result establishes a repeating physical trajectory.
"""

from __future__ import annotations

from functools import lru_cache

from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.boolean_transfer import (
    BooleanMatrix,
    BooleanStateSpace,
)
from number_compiler.sequences.double_reverse.boundary_cycles import (
    Edge,
    boundary_steps,
    is_edge_tuple,
)
from number_compiler.sequences.double_reverse.temporal_border_bank import EDGE_STATES
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    edge_phase,
    growth_ports,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    UncertifiedPointedStencilError,
)
from number_compiler.sequences.double_reverse.temporal_residue_quotient import (
    certified_residue_action,
    decimal_residues_from_slp,
)

_EDGE_INDEX = {edge: index for index, edge in enumerate(EDGE_STATES)}
_EDGE_STATE_SPACE = BooleanStateSpace("double_reverse.carry-closed-border", EDGE_STATES)


@lru_cache(maxsize=1)
def _one_step() -> BooleanMatrix[Edge]:
    rows: list[int] = []
    for edge in EDGE_STATES:
        relation = boundary_steps(edge)
        if relation.shrinking_frontier:
            raise AssertionError("closed 2rev10 border reached a shrink frontier")
        targets = 0
        for step in relation.steps:
            if step.target not in _EDGE_INDEX:
                raise AssertionError("closed 2rev10 border left its state space")
            targets |= 1 << _EDGE_INDEX[step.target]
        rows.append(targets)
    return BooleanMatrix(_EDGE_STATE_SPACE, tuple(rows))


def powered_border_relation(physical_ticks: int) -> tuple[int, ...]:
    """Return the nine-state relation power in O(log physical_ticks) joins."""
    if type(physical_ticks) is not int or not 0 <= physical_ticks <= 4096:
        raise ValueError("border relation is bounded to 0..4096 physical ticks")
    return _one_step().power(physical_ticks).rows


def _validate_edge(edge: object) -> Edge:
    if not is_edge_tuple(edge) or edge not in _EDGE_INDEX:
        raise ValueError("source border is outside the exact carry-closed cylinder")
    return edge


def reachable_edges(edge: Edge, physical_ticks: int) -> tuple[Edge, ...]:
    """Return all border states admitted by the finite powered relation."""
    edge = _validate_edge(edge)
    if type(physical_ticks) is not int or not 0 <= physical_ticks <= 4096:
        raise ValueError("border reachability is bounded to 0..4096 ticks")
    mask = powered_border_relation(physical_ticks)[_EDGE_INDEX[edge]]
    return tuple(
        state for index, state in enumerate(EDGE_STATES) if mask & (1 << index)
    )


def _forced_outer_pair_word(
    edge: Edge, physical_ticks: int
) -> tuple[tuple[int, int], ...]:
    """Accumulate only the short forced-prefix relation, without global memoization."""
    result: list[tuple[int, int]] = []
    relation = BooleanMatrix[Edge].identity(_EDGE_STATE_SPACE)
    one_step = _one_step()
    source = 1 << _EDGE_INDEX[edge]
    for tick in range(physical_ticks + 1):
        mask = relation.image(source)
        pairs = {
            (state[0], state[-1])
            for index, state in enumerate(EDGE_STATES)
            if mask & (1 << index)
        }
        if len(pairs) != 1:
            raise AssertionError("outer pair is not forced by the closed border")
        result.append(next(iter(pairs)))
        if tick < physical_ticks:
            relation = relation.then(one_step)
    return tuple(result)


def forced_outer_pair_word(
    edge: Edge, physical_ticks: int
) -> tuple[tuple[int, int], ...]:
    """Check outer-pair consensus through at most 32 physical transitions."""
    if type(physical_ticks) is not int or not 0 <= physical_ticks <= 32:
        raise ValueError("invalid bounded border word request")
    return _forced_outer_pair_word(_validate_edge(edge), physical_ticks)


def predictive_source_transfer(
    term: object, *, steps: int, pair_depth: int
) -> dict[str, object]:
    """Join certified border clocks before reading an exact packed endpoint."""
    from number_compiler.resources.metric_keys import double_reverse as keys

    from .power import DoubleReverseTerm
    from .temporal_packed_ring import RingWindowRequest, pointed_ring_windows

    if type(term) is not DoubleReverseTerm:
        raise TypeError("2rev10 source transfer needs its exact term owner")
    if type(steps) is not int or steps < 2 or steps > 4096 or steps % 2:
        raise ValueError("powered matrix ticks must be even in 2..4096")
    if type(pair_depth) is not int or not 1 <= pair_depth <= 16:
        raise ValueError("powered matrix pair depth must be 1..16")
    term.check_open()
    origin = term.generation
    common: dict[str, object] = {
        "family": "2rev10",
        "source_generation": origin,
        "physical_interval": (origin, origin + steps),
        "physical_ticks": steps,
        "pair_depth": pair_depth,
        "pair_coordinate_order": ("upper_msd_inward", "lower_lsd_inward"),
        "physical_repeat_certified": False,
        "future_repetition_claimed": False,
    }

    def unavailable(reason: str) -> dict[str, object]:
        return {**common, "status": "unavailable", "reason": reason}

    if origin + steps > term.max_steps:
        return unavailable("future endpoint exceeds the term step budget")
    try:
        root = term.endpoint_root()
        arena = term.source_arena
        engine = term.temporal_engine
        phase = engine.certify(root)
        if phase is None:
            return unavailable("source has no authenticated carry-closed border")

        source_width = arena.nodes[root].length
        left_births, right_births = growth_ports(phase, steps // 2)
        target_width = source_width + left_births + right_births
        window_size = max(pair_depth + 1, 2)
        if (
            source_width <= 2 * pair_depth
            or target_width <= 2 * pair_depth
            or window_size > 18
        ):
            return unavailable("source or endpoint is too narrow for this pair depth")

        source_left = tuple(
            symbol_at(arena, root, index) for index in range(window_size)
        )
        source_right = tuple(
            symbol_at(arena, root, source_width - window_size + index)
            for index in range(window_size)
        )
        source_edge: Edge = (
            source_left[0],
            source_left[1],
            source_right[-2],
            source_right[-1],
        )
        if source_edge not in _EDGE_INDEX:
            return unavailable("source root is outside the closed nine-state border")
        source_upper = (source_edge[0], source_edge[1])
        source_lower = (source_edge[2], source_edge[3])
        if edge_phase(source_upper, source_lower) != phase:
            raise ArithmeticError("certified source phase disagrees with its border")

        possible_edges = reachable_edges(source_edge, steps)
        source_mod99, source_mod198 = decimal_residues_from_slp(
            arena,
            root,
            ledger=term.resource_ledger,
            scratch_owner=term.scratch_owner,
        )
        clock = certified_residue_action(
            phase=phase,
            width=source_width,
            duration=steps,
            source_mod99=source_mod99,
            source_mod198=source_mod198,
        )
        if clock.width_out != target_width:
            raise ArithmeticError("powered width clock disagrees with border births")
        if steps % 4 == 0 and (
            clock.multiplier_mod99 != pow(61, steps // 4, 99)
            or clock.multiplier_mod198 != pow(160, steps // 4, 198)
        ):
            raise ArithmeticError("four-step residue action disagrees with its clock")

        # The powered border envelope is an overapproximation. Singleton
        # exterior projections are already exact and must be consumed before
        # any interior output cone is constructed.
        leading_domains = {state[:2] for state in possible_edges}
        trailing_domains = {state[-2:] for state in possible_edges}
        forced_left = (
            next(iter(leading_domains))
            if window_size == 2 and len(leading_domains) == 1
            else None
        )
        forced_right = (
            next(iter(trailing_domains))
            if window_size == 2 and len(trailing_domains) == 1
            else None
        )
        requests: list[RingWindowRequest] = []
        labels: list[str] = []
        if forced_left is None:
            requests.append(RingWindowRequest(0, window_size, (pair_depth,)))
            labels.append("left")
        if forced_right is None:
            requests.append(
                RingWindowRequest(
                    target_width - window_size,
                    window_size,
                    (window_size - 1 - pair_depth,),
                )
            )
            labels.append("right")

        before = term.metrics()
        projection_modes: list[str] = []
        affine_summaries: list[dict[str, object]] = []
        projected: dict[str, tuple[int, ...]] = {}
        for label, forced in (("left", forced_left), ("right", forced_right)):
            if forced is not None:
                projected[label] = forced
                term.resource_ledger.bump(
                    keys.DOUBLE_REVERSE_POINTED_RING_FORCED_PORTS, len(forced)
                )
                projection_modes.append("registered_macro_forced_" + label)

        if requests:
            try:
                windows = pointed_ring_windows(
                    engine, root, steps // 2, phase, tuple(requests)
                )
                for label, window in zip(labels, windows, strict=True):
                    projected[label] = window.digits
                    projection_modes.append("packed_digit_affine_carry_ring")
                    for action in window.actions:
                        affine = action.action
                        four_phase_offset = None
                        if affine.physical_ticks % 4 == 0:
                            c0, c1, c2, c3 = affine.phase_counts
                            four_phase_offset = (3 * c0 + 4 * c1 + 2 * c2 + c3) % 5
                        affine_summaries.append(
                            {
                                "initial_digit": action.initial_digit,
                                "result_digit": action.result_digit,
                                "initial_residue": action.initial_digit % 5,
                                "result_residue": action.result_digit % 5,
                                "multiplier_mod5": affine.multiplier,
                                "offset_mod5": affine.offset,
                                "action_relative_carry_phase_counts": affine.phase_counts,
                                "carry_phase_origin": "action_relative_physical_tick_zero",
                                "four_phase_weighted_offset_mod5": four_phase_offset,
                                "physical_ticks": affine.physical_ticks,
                                "affine_verified": True,
                                "full_digit_verified": True,
                                "future_driver_period_certified": False,
                            }
                        )
            except BlockContextBudgetExceeded:
                term.resource_ledger.bump(
                    keys.DOUBLE_REVERSE_POINTED_RING_BUDGET_FALLBACKS
                )
                for label, request in zip(labels, requests, strict=True):
                    projected[label] = engine.pointed_window(
                        root,
                        steps // 2,
                        phase,
                        request.start,
                        request.count,
                    )
                    projection_modes.append("guarded_hashlife_budget_fallback")

        target_left = projected["left"]
        target_right = projected["right"]
        target_edge: Edge = (
            target_left[0],
            target_left[1],
            target_right[-2],
            target_right[-1],
        )
        if target_edge not in possible_edges:
            raise ArithmeticError(
                "exact projected endpoint violates the guarded border"
            )

        initial_pair = (source_left[pair_depth], source_right[-1 - pair_depth])
        target_pair = (target_left[pair_depth], target_right[-1 - pair_depth])
        possible_pairs = {
            (state[pair_depth], state[-1 - pair_depth]) for state in possible_edges
        }
        if window_size == 2 and target_pair not in possible_pairs:
            raise ArithmeticError("exact endpoint violates the projected pair domain")
        outer_word = forced_outer_pair_word(source_edge, 4)
        if (target_edge[0], target_edge[-1]) != outer_word[steps % 4]:
            raise ArithmeticError(
                "pointed endpoint violates the forced outer pair word"
            )

        scalar_order = next(
            order
            for order in range(1, 31)
            if pow(61, order, 99) * clock.source_mod99 % 99 == clock.source_mod99
        )
        after = term.metrics()
        actual_work = {
            "new_hashlife_cones": after.get(keys.DOUBLE_REVERSE_HASHLIFE_CONES, 0)
            - before.get(keys.DOUBLE_REVERSE_HASHLIFE_CONES, 0),
            "hashlife_cone_hits": after.get(keys.DOUBLE_REVERSE_HASHLIFE_CONE_HITS, 0)
            - before.get(keys.DOUBLE_REVERSE_HASHLIFE_CONE_HITS, 0),
            "ring_window_attempts": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_WINDOW_ATTEMPTS, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_WINDOW_ATTEMPTS, 0),
            "ring_windows": after.get(keys.DOUBLE_REVERSE_POINTED_RING_WINDOWS, 0)
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_WINDOWS, 0),
            "ring_source_cells": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_SOURCE_CELLS, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_SOURCE_CELLS, 0),
            "ring_operand_bits": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_OPERAND_BITS, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_OPERAND_BITS, 0),
            "ring_stencil_cells": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_STENCIL_CELLS, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_STENCIL_CELLS, 0),
            "ring_packed_steps": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_PACKED_STEPS, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_PACKED_STEPS, 0),
            "forced_ports": after.get(keys.DOUBLE_REVERSE_POINTED_RING_FORCED_PORTS, 0)
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_FORCED_PORTS, 0),
            "affine_digits_verified": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_DIGITS, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_DIGITS, 0),
            "affine_carry_ports_read": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_PORTS, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_PORTS, 0),
            "affine_logical_carry_ports": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_LOGICAL_PORTS, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_LOGICAL_PORTS, 0),
            "periodic_guard_attempts": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_ATTEMPTS, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_ATTEMPTS, 0),
            "periodic_guard_hits": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_HITS, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_HITS, 0),
            "periodic_guard_states": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_GUARD_STATES, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_GUARD_STATES, 0),
            "periodic_source_probes": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_SOURCE_PROBES, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_SOURCE_PROBES, 0),
            "periodic_source_node_visits": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_SOURCE_NODE_VISITS, 0
            )
            - before.get(
                keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_SOURCE_NODE_VISITS, 0
            ),
            "periodic_motif_steps": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_MOTIF_STEPS, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_MOTIF_STEPS, 0),
            "periodic_motif_cell_evaluations": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_MOTIF_CELL_EVALUATIONS, 0
            )
            - before.get(
                keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_MOTIF_CELL_EVALUATIONS, 0
            ),
            "failed_packed_work": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_FAILED_WORK, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_FAILED_WORK, 0),
            "packed_budget_fallbacks": after.get(
                keys.DOUBLE_REVERSE_POINTED_RING_BUDGET_FALLBACKS, 0
            )
            - before.get(keys.DOUBLE_REVERSE_POINTED_RING_BUDGET_FALLBACKS, 0),
        }
        return {
            **common,
            "status": "available",
            "construction": "powered_border_and_clock_with_packed_source_endpoint",
            "source_root_local_diagnostic": root,
            "source_width": source_width,
            "target_width": target_width,
            "source_border": source_edge,
            "possible_target_borders": possible_edges,
            "pointed_target_border": target_edge,
            "source_pair": initial_pair,
            "pointed_target_pair": target_pair,
            "source_mod99": clock.source_mod99,
            "target_mod99": clock.target_mod99,
            "source_mod198": clock.source_mod198,
            "target_mod198": clock.target_mod198,
            "residue_multiplier_mod99": clock.multiplier_mod99,
            "residue_multiplier_mod198": clock.multiplier_mod198,
            "exact_width_growth": clock.growth,
            "outer_pair_word": outer_word,
            "outer_pair_period": 4,
            "source_residue_stabilizer_order": scalar_order,
            "outer_pair_and_mod99_return_scope": 4 * scalar_order,
            "border_relation_semantics": "all_carry_histories_overapproximation",
            "matrix_semantics": "powered_border_relation_plus_exact_pointed_projection",
            "border_relation_rows": powered_border_relation(steps),
            "inner_pair_matrix_computed": False,
            "source_pair_endpoint_verified": True,
            "chronological_source_replay_used": False,
            "chronological_future_roots_constructed": False,
            "exact_completed_children_joined": False,
            "inner_pair_period_certified": False,
            "execution_authority": False,
            "projection_engine": "guarded_macro_first_packed_digit_affine_carry_ring",
            "target_border_verified_by_pointed_cone": target_edge,
            "target_border_verified_by_exact_ring_projection": target_edge,
            "source_port_puncture": {
                "leading_two_admissible": tuple(sorted(leading_domains)),
                "trailing_two_admissible": tuple(sorted(trailing_domains)),
                "next_pair_admissible_if_outer_two": tuple(sorted(possible_pairs))
                if window_size == 2
                else None,
                "projection_kernels": tuple(projection_modes),
                "source_certified_digit_affine_actions": tuple(affine_summaries),
                "ring_stencil_cells_are_logical_not_python_steps": True,
                "future_inlet_program_autonomous": False,
            },
            "actual_projection_work": actual_work,
            "scope": "source-bound endpoint projection; no infinite inlet or inner-return claim",
        }
    except (UncertifiedPointedStencilError, BlockContextBudgetExceeded) as exc:
        return unavailable(str(exc))


__all__ = [
    "forced_outer_pair_word",
    "powered_border_relation",
    "predictive_source_transfer",
    "reachable_edges",
]
