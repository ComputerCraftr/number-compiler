"""Finite source-scoped border and pair transfer from a reverse/add endpoint."""

from __future__ import annotations

from itertools import pairwise

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.reverse_add.boundary_window_store import (
    WindowRelationBudgetExceeded,
)
from number_compiler.sequences.reverse_add.q19_border_control import (
    BoundaryControlNotAuthorized,
    CertifiedBorderGrowth,
)
from number_compiler.sequences.reverse_add.q19_occurrence import (
    ReversePairOutputOccurrence,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.q19_source_authority import digits_at
from number_compiler.sequences.reverse_add.temporal_carry_phase import (
    CertifiedCarryWord,
)
from number_compiler.sequences.reverse_add.temporal_depth_transfer_matrix import (
    PAIR_COORDINATE_ORDER,
    BooleanPairMatrix,
    ConditionalQ19DepthWindow,
)
from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
    ReverseAddTemporalRingBank,
    ReverseTemporalRingRefused,
)

from .power import ReverseAddPoweredTerm
from .source_images import ReverseSourceImageWorkspace

MAX_PHYSICAL_STEPS = 128
MAX_PAIR_DEPTH = 12
MAX_RELATION_CELLS = 16_384


class SourcePairDepthUnavailable(ValueError):
    """The exact endpoint is too narrow to carry the requested pair index."""


def _source_pair(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
    pair_depth: int,
) -> tuple[int, int]:
    if (
        type(owner) is not ReversePairQ19OutputOwner
        or type(occurrence) is not ReversePairOutputOccurrence
    ):
        raise TypeError("source pair requires an owner-issued Q19 occurrence")
    width = occurrence.output_width
    if width < 2 * pair_depth + 1:
        raise SourcePairDepthUnavailable(
            "source endpoint is too narrow for the requested pair depth"
        )
    left, right = digits_at(owner, occurrence, (pair_depth, width - 1 - pair_depth))
    return left, right


def _unavailable(reason: str, *, steps: int, pair_depth: int) -> dict[str, object]:
    return {
        "status": "unavailable",
        "reason": reason,
        "physical_ticks": steps,
        "pair_depth": pair_depth,
        "physical_repeat_certified": False,
        "future_repetition_claimed": False,
    }


def source_transfer_packet(
    term: ReverseAddPoweredTerm,
    *,
    steps: int,
    pair_depth: int,
    trace: bool = False,
) -> dict[str, object]:
    """Return a finite source-guarded Q19 relation from the completed endpoint.

    The default packet is built from the issued border and carry tapes before
    asking the Q19 owner for future roots. ``trace=True`` additionally builds
    the bounded exact child path and verifies that it lies in that relation.
    Neither result grants authority to repeat the physical source.
    """
    if type(term) is not ReverseAddPoweredTerm:
        raise TypeError("reverse/add source transfer requires ReverseAddPoweredTerm")
    term.validate_source_binding()
    if term.base != 10:
        raise ValueError("reverse/add term source/action binding changed")
    if type(steps) is not int or not 1 <= steps <= MAX_PHYSICAL_STEPS:
        raise ValueError(f"physical steps must be in 1..{MAX_PHYSICAL_STEPS}")
    if type(pair_depth) is not int or not 1 <= pair_depth <= MAX_PAIR_DEPTH:
        raise ValueError(f"pair depth must be in 1..{MAX_PAIR_DEPTH}")
    if type(trace) is not bool:
        raise TypeError("trace demand must be Boolean")

    from .temporal_depth_transfer_matrix import (
        conditional_depth_window,
        pair_index,
    )

    if term.generation < 1:
        return _unavailable(
            "a positive completed decimal endpoint is required",
            steps=steps,
            pair_depth=pair_depth,
        )
    workspace = term.source_workspace()
    if (
        type(workspace) is not ReverseSourceImageWorkspace
        or workspace.ledger is not term.resource_ledger
    ):
        raise TypeError("reverse/add term returned a foreign source workspace")
    owner, endpoint, _reused, _applications = workspace.completed_q19_occurrence()
    if (
        type(owner) is not ReversePairQ19OutputOwner
        or type(endpoint) is not ReversePairOutputOccurrence
    ):
        raise TypeError("completed endpoint is not an owner-issued Q19 occurrence")
    owner.validate_issued_occurrence(endpoint)
    if endpoint.temporal_steps != term.generation:
        raise ValueError("completed endpoint does not match the term generation")
    try:
        source_pair = _source_pair(owner, endpoint, pair_depth)
    except SourcePairDepthUnavailable as exc:
        return _unavailable(str(exc), steps=steps, pair_depth=pair_depth)

    try:
        # Certify the whole requested border interval first. This may inspect
        # the source's bounded carry language, but it does not publish Q19
        # child roots and therefore rejects unsupported horizons cheaply.
        certificate = owner.certify_border_growth(
            endpoint,
            steps=steps + 1,
            window_digits=pair_depth,
            max_states=8192,
        )
        if type(certificate) is not CertifiedBorderGrowth:
            raise TypeError("Q19 border owner returned an invalid certificate type")
        future_growth = certificate.growth_word[1:]
        if certificate.source is not endpoint or len(future_growth) != steps:
            raise ValueError("border certificate does not cover the requested interval")
        bank = certificate.temporal_ring_bank(
            start=1,
            duration=steps,
            positions=(pair_depth,),
            max_cells=MAX_RELATION_CELLS,
        )
        if type(bank) is not ReverseAddTemporalRingBank:
            raise TypeError("Q19 owner returned an invalid temporal ring bank")
        carry_word = bank.conditional_carry_word(border_digits=pair_depth)
        if type(carry_word) is not CertifiedCarryWord:
            raise TypeError("temporal ring returned an invalid carry word")
        projected = conditional_depth_window(
            carry_word,
            position=pair_depth,
            start_tick=0,
            steps=steps,
        )
        if type(projected) is not ConditionalQ19DepthWindow:
            raise TypeError("Q19 depth projection returned an invalid record")
        projected.validate()
    except (
        BoundaryControlNotAuthorized,
        BlockContextBudgetExceeded,
        ReverseTemporalRingRefused,
        WindowRelationBudgetExceeded,
    ) as exc:
        return _unavailable(
            f"source border transfer unavailable: {exc}",
            steps=steps,
            pair_depth=pair_depth,
        )

    if (
        type(projected.phase_matrices) is not tuple
        or len(projected.phase_matrices) != steps
    ):
        raise ValueError("projected Q19 relation does not span the source interval")
    if any(
        type(matrix) is not BooleanPairMatrix for matrix in projected.phase_matrices
    ):
        raise TypeError("projected Q19 phase is not an owned Boolean pair matrix")

    possible_endpoints = projected.action.endpoints(source_pair)
    summary: dict[str, object] = {
        "status": "available",
        "family": "reverse-add",
        "source_generation": endpoint.temporal_steps,
        "physical_interval": (endpoint.temporal_steps, endpoint.temporal_steps + steps),
        "target_generation": endpoint.temporal_steps + steps,
        "physical_ticks": steps,
        "pair_depth": pair_depth,
        "pair_coordinate_order": PAIR_COORDINATE_ORDER,
        "source_root_local_diagnostic": endpoint.root,
        "source_pair": source_pair,
        "source_width": endpoint.output_width,
        "target_width": certificate.final_width,
        "source_width_growth": future_growth,
        "conditional_endpoint_pairs": possible_endpoints,
        "transition_rows": projected.action.rows,
        "affine_transition_rows": projected.affine_action.rows,
        "matrix_semantics": "projected_source_word_overapproximation",
        "source_root_assignment_joined": False,
        "source_pair_path_guarded": False,
        "exact_completed_children_joined": False,
        "future_q19_roots_constructed": False,
        "source_guard_applied_before_matrix_composition": True,
        "physical_repeat_certified": False,
        "future_repetition_claimed": False,
        "execution_authority": False,
        "canonical_one_digit_candidate_count": 96,
    }
    if not trace:
        return summary

    # Materialize and verify exact children only for an explicitly demanded
    # chronological trace. The projected products above are reused; exact
    # children are checked for membership in each phase relation without a
    # second matrix multiplication pass.
    children = [endpoint]
    current = endpoint
    exact_phase_matrices: list[BooleanPairMatrix] = []
    exact_action = BooleanPairMatrix.identity()
    try:
        for _ in range(steps):
            current = owner.apply_pair_step(current)
            owner.validate_issued_occurrence(current)
            children.append(current)
        actual_pairs = tuple(
            _source_pair(owner, child, pair_depth) for child in children
        )
        if (
            tuple(
                target.output_width - source.output_width
                for source, target in pairwise(children)
            )
            != future_growth
        ):
            raise ValueError("certified growth differs from exact completed children")

        from .border_occurrences import (
            ReverseAddBorderPhaseOccurrence,
            ReverseAddBorderTrace,
            trace_reverse_add_border_occurrences,
        )

        border_occurrences = trace_reverse_add_border_occurrences(
            certificate,
            tuple(children),
            pair_depth=pair_depth,
        )
        if type(border_occurrences) is not ReverseAddBorderTrace:
            raise TypeError("reverse/add trace owner returned an invalid border trace")
        if any(phase is None for phase in border_occurrences.window_phases):
            return _unavailable(
                "the exact endpoint has no admitted border phase at this pair depth",
                steps=steps,
                pair_depth=pair_depth,
            )

        phase_packets: list[dict[str, object]] = []
        for tick, (source, target) in enumerate(pairwise(children)):
            border_phase = border_occurrences.window_phases[tick]
            if type(border_phase) is not ReverseAddBorderPhaseOccurrence:
                raise ValueError("source border phase is unavailable at this depth")
            if (
                border_phase.phase.source.root != source.root
                or border_phase.phase.target.root != target.root
                or border_phase.phase.source.owner is not owner
                or border_phase.phase.target.owner is not owner
            ):
                raise ValueError("typed border cursor does not name the exact child")
            source_index = pair_index(actual_pairs[tick])
            target_index = pair_index(actual_pairs[tick + 1])
            if not (
                projected.phase_matrices[tick].rows[source_index] & (1 << target_index)
            ):
                raise ValueError("exact Q19 child edge is absent from its relation")
            rows = [0] * len(projected.phase_matrices[tick].rows)
            rows[source_index] = 1 << target_index
            exact_phase = BooleanPairMatrix(tuple(rows))
            exact_phase_matrices.append(exact_phase)
            exact_action = exact_action.then(exact_phase)
            phase_packets.append(
                {
                    "phase": border_phase.phase.phase,
                    "phase_index": border_phase.tick,
                    "physical_interval": (
                        source.temporal_steps,
                        target.temporal_steps,
                    ),
                    "identity": border_phase.phase.identity.packet(),
                    "source_root_local_diagnostic": source.root,
                    "target_root_local_diagnostic": target.root,
                    "source_state": border_phase.phase.source_state,
                    "target_state": border_phase.phase.target_state,
                    "width": border_phase.width,
                    "growth": border_phase.port.growth,
                    "low_carry": border_phase.port.low_carry,
                    "middle_maps": tuple(
                        fn.value for fn in border_phase.port.admitted_middle
                    ),
                    "mod99": (border_phase.residue99, border_phase.target99),
                    "mod198": (border_phase.residue198, border_phase.target198),
                }
            )
        if exact_action.endpoints(actual_pairs[0]) != (actual_pairs[-1],):
            raise AssertionError("source-guarded Q19 trace lost its exact endpoint")
    except (
        BoundaryControlNotAuthorized,
        BlockContextBudgetExceeded,
        ReverseTemporalRingRefused,
        WindowRelationBudgetExceeded,
    ) as exc:
        return _unavailable(
            f"source trace unavailable: {exc}",
            steps=steps,
            pair_depth=pair_depth,
        )

    return {
        **summary,
        "trace": {
            "source_pair_path": actual_pairs,
            "target_pair": actual_pairs[-1],
            "target_root_local_diagnostic": current.root,
            "transition_rows": exact_action.rows,
            "exact_completed_children_joined": True,
            "source_pair_path_guarded": True,
            "source_guard_applied_before_matrix_composition": True,
            "matrix_semantics": "source_scoped_exact_pair_path",
            "phase_matrices": tuple(matrix.rows for matrix in exact_phase_matrices),
            "border_phases": tuple(phase_packets),
            "observed_returns": tuple(
                {
                    "identity": macro.identity.packet(),
                    "entry_phase": macro.entry_phase,
                    "phase_interval": (macro.start, macro.end),
                    "physical_interval": (
                        endpoint.temporal_steps + macro.start,
                        endpoint.temporal_steps + macro.end,
                    ),
                    "physical_ticks": macro.phases,
                    "width_interval": (macro.width_start, macro.width_end),
                    "mod99": (macro.mod99_start, macro.mod99_end),
                    "mod198": (macro.mod198_start, macro.mod198_end),
                    "clock_return": macro.clocks_return,
                    "physical_repeat_certified": False,
                }
                for macro in border_occurrences.window_macros
            ),
            "observed_episodes": tuple(
                {
                    "identity": episode.identity.packet(),
                    "kind": episode.kind.value,
                    "phase_interval": (episode.start, episode.end),
                    "physical_interval": (
                        endpoint.temporal_steps + episode.start,
                        endpoint.temporal_steps + episode.end,
                    ),
                    "repeat_units": episode.repeat_units,
                    "growth_word": episode.growth_word,
                    "low_carry_word": episode.low_carry_word,
                    "middle_maps": episode.middle_maps,
                    "mod99": (episode.mod99_start, episode.mod99_end),
                    "mod198": (episode.mod198_start, episode.mod198_end),
                    "clock_return": episode.clocks_return,
                    "physical_repeat_certified": False,
                }
                for episode in border_occurrences.window_episodes
            ),
        },
    }


__all__ = [
    "MAX_PAIR_DEPTH",
    "MAX_PHYSICAL_STEPS",
    "PAIR_COORDINATE_ORDER",
    "source_transfer_packet",
]
