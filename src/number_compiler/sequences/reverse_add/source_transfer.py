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
from number_compiler.sequences.reverse_add.temporal_carry_phase import (
    CertifiedCarryWord,
)
from number_compiler.sequences.reverse_add.temporal_depth_transfer_matrix import (
    PAIR_COORDINATE_ORDER,
    BooleanPairMatrix,
    ConditionalQ19DepthWindow,
    Q19AffinePairMatrix,
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


def _identity_packet(identity: object) -> dict[str, object]:
    from number_compiler.hashlife.interfaces.border_macros import BorderMacroIdentity

    if type(identity) is not BorderMacroIdentity:
        raise TypeError("source transfer metadata requires a typed border identity")
    return {
        "family": identity.family.value,
        "kind": identity.kind.value,
        "signature": identity.signature,
    }


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
    owner.validate_issued_occurrence(occurrence)
    width = occurrence.output_width
    if width < 2 * pair_depth + 1:
        raise SourcePairDepthUnavailable(
            "source endpoint is too narrow for the requested pair depth"
        )
    return (
        owner.digit(occurrence, pair_depth),
        owner.digit(occurrence, width - 1 - pair_depth),
    )


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
    term: ReverseAddPoweredTerm, *, steps: int, pair_depth: int
) -> dict[str, object]:
    """Compose exact future children beginning at ``term``'s completed endpoint.

    Border/cyclotomic phase checks are joined to each exact owner child before
    pair-matrix rows are composed. The resulting relation is scoped to the
    observed pair path and grants no permission to reuse its input word.
    """
    if type(term) is not ReverseAddPoweredTerm:
        raise TypeError("reverse/add source transfer requires ReverseAddPoweredTerm")
    if (term.seed, term.generation, term.base) != term._binding or term.base != 10:
        raise ValueError("reverse/add term source/action binding changed")
    if type(steps) is not int or not 1 <= steps <= MAX_PHYSICAL_STEPS:
        raise ValueError(f"physical steps must be in 1..{MAX_PHYSICAL_STEPS}")
    if type(pair_depth) is not int or not 1 <= pair_depth <= MAX_PAIR_DEPTH:
        raise ValueError(f"pair depth must be in 1..{MAX_PAIR_DEPTH}")

    from .border_macro_catalogue import source_border_macro_catalogue
    from .temporal_depth_transfer_matrix import (
        ALL_PAIRS,
        conditional_depth_window,
        pair_index,
    )

    if term.generation < 1:
        return _unavailable(
            "a positive completed decimal endpoint is required",
            steps=steps,
            pair_depth=pair_depth,
        )
    workspace = term._source_workspace()
    if (
        type(workspace) is not ReverseSourceImageWorkspace
        or workspace.ledger is not term._ledger
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
        _source_pair(owner, endpoint, pair_depth)
    except SourcePairDepthUnavailable as exc:
        return _unavailable(str(exc), steps=steps, pair_depth=pair_depth)

    children = [endpoint]
    current = endpoint
    try:
        for _ in range(steps):
            current = owner.apply_pair_step(current)
            owner.validate_issued_occurrence(current)
            children.append(current)
        actual_pairs = tuple(
            _source_pair(owner, child, pair_depth) for child in children
        )
        certificate = owner.certify_border_growth(
            endpoint,
            # The Q19 certificate starts with the already-completed emission
            # from the source pair width. The requested source interval starts
            # at that emitted endpoint, so retain one leading certificate edge.
            steps=steps + 1,
            window_digits=pair_depth,
            max_states=8192,
        )
        if type(certificate) is not CertifiedBorderGrowth:
            raise TypeError("Q19 border owner returned an invalid certificate type")
        future_growth = certificate.growth_word[1:]
        if certificate.source is not endpoint or len(future_growth) != steps:
            raise ValueError(
                "border certificate does not cover the requested endpoint interval"
            )
        if (
            tuple(
                target.output_width - source.output_width
                for source, target in pairwise(children)
            )
            != future_growth
        ):
            raise ValueError(
                "certified growth differs from the exact completed children"
            )
        catalogue = source_border_macro_catalogue(
            certificate,
            tuple(children),
            pair_depth=pair_depth,
        )
        from .border_macro_catalogue import (
            ClockedBorderPhase,
            SourceBorderMacroCatalogue,
        )

        if type(catalogue) is not SourceBorderMacroCatalogue:
            raise TypeError("source border catalogue returned an invalid record")
        if any(phase is None for phase in catalogue.window_phases):
            return _unavailable(
                "the exact endpoint has no admitted border phase at this pair depth",
                steps=steps,
                pair_depth=pair_depth,
            )
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
            source_pair_path=actual_pairs,
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

    # Bind every phase to the actual ordered pair at the same source and
    # completed child. Only after these source-root and clock guards pass do
    # we compose the restricted matrices.
    guarded_matrices: list[BooleanPairMatrix] = []
    affine_action = Q19AffinePairMatrix.identity()
    action = BooleanPairMatrix.identity()
    if (
        type(projected.phase_matrices) is not tuple
        or len(projected.phase_matrices) != steps
    ):
        raise ValueError("projected Q19 matrix does not span the exact source interval")
    for tick, (source, target) in enumerate(pairwise(children)):
        border_phase = catalogue.window_phases[tick]
        if type(border_phase) is not ClockedBorderPhase:
            raise ValueError("source border phase is unavailable at this depth")
        if (
            border_phase.phase.source.root != source.root
            or border_phase.phase.target.root != target.root
            or border_phase.phase.source.owner is not owner
            or border_phase.phase.target.owner is not owner
        ):
            raise ValueError(
                "typed border cursor does not name the exact completed child"
            )
        source_state = actual_pairs[tick]
        target_state = actual_pairs[tick + 1]
        source_index = pair_index(source_state)
        target_index = pair_index(target_state)
        projected_phase = projected.phase_matrices[tick]
        if type(projected_phase) is not BooleanPairMatrix:
            raise TypeError("projected Q19 phase is not an owned Boolean pair matrix")
        expected_rows = tuple(
            (1 << target_index) if index == source_index else 0
            for index in range(len(ALL_PAIRS))
        )
        if projected_phase.rows != expected_rows:
            raise ValueError("source edge was not guarded before matrix composition")
        guarded_matrices.append(projected_phase)
        action = action.then(projected_phase)
        affine_action = affine_action.then(
            Q19AffinePairMatrix.from_boolean(projected_phase)
        )

    if action.endpoints(actual_pairs[0]) != (actual_pairs[-1],):
        raise AssertionError(
            "source-scoped matrix composition lost its exact child path"
        )
    if affine_action.boolean != action:
        raise AssertionError("affine and Boolean source-scoped actions disagree")

    phase_packets = tuple(
        {
            "phase": phase.phase.phase,
            "phase_index": phase.tick,
            "physical_tick": endpoint.temporal_steps + phase.tick,
            "physical_interval": (
                endpoint.temporal_steps + phase.tick,
                endpoint.temporal_steps + phase.tick + 1,
            ),
            "identity": _identity_packet(phase.phase.identity),
            "source_root": phase.phase.source.root,
            "target_root": phase.phase.target.root,
            "source_state": phase.phase.source_state,
            "target_state": phase.phase.target_state,
            "width": phase.width,
            "growth": phase.port.growth,
            "low_carry": phase.port.low_carry,
            "middle_maps": tuple(fn.value for fn in phase.port.admitted_middle),
            "mod99": (phase.residue99, phase.target99),
            "mod198": (phase.residue198, phase.target198),
        }
        for phase in catalogue.window_phases
        if phase is not None
    )
    return {
        "status": "available",
        "family": "reverse-add",
        "source_generation": endpoint.temporal_steps,
        "physical_interval": (endpoint.temporal_steps, current.temporal_steps),
        "physical_ticks": steps,
        "pair_depth": pair_depth,
        "pair_coordinate_order": PAIR_COORDINATE_ORDER,
        "source_root": endpoint.root,
        "target_root": current.root,
        "exact_completed_children_joined": True,
        "source_guard_applied_before_matrix_composition": True,
        "matrix_semantics": "source_scoped_exact_pair_path",
        "source_pair_path": actual_pairs,
        "transition_rows": action.rows,
        "affine_transition_rows": affine_action.rows,
        "phase_matrices": tuple(matrix.rows for matrix in guarded_matrices),
        "border_phases": phase_packets,
        "observed_returns": tuple(
            {
                "identity": _identity_packet(macro.identity),
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
            for macro in catalogue.window_macros
        ),
        "observed_episodes": tuple(
            {
                "identity": _identity_packet(episode.identity),
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
            for episode in catalogue.window_episodes
        ),
        "canonical_one_digit_candidate_count": 96,
        "physical_repeat_certified": False,
        "future_repetition_claimed": False,
    }


__all__ = [
    "MAX_PAIR_DEPTH",
    "MAX_PHYSICAL_STEPS",
    "PAIR_COORDINATE_ORDER",
    "source_transfer_packet",
]
