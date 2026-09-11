from pathlib import Path

import pytest

from number_compiler.arithmetic.fields.dyadic_tile import source_span, split, uniform


def test_uniform_dyadic_tiles_share_children_without_run_length_identity() -> None:
    blank = 19
    a = uniform(blank, 10)
    b = uniform(blank, 11)
    assert b.left is a and b.right is a
    assert a.width == 1024
    assert b.width == 2048
    # Width is implied by the level; there is no run-length payload.
    assert not hasattr(a, "run_length")


def test_source_blank_exterior_is_logarithmic_aligned_forest() -> None:
    span = source_span((7, 18, 7), blank=19, logical_length=1_000_003)
    assert span.length == 1_000_003
    assert len(span.chunks) <= 2 * span.length.bit_length() + 3
    for chunk in span.chunks:
        assert chunk.start % chunk.tile.width == 0


def test_dyadic_split_preserves_absolute_alignment_and_exact_lengths() -> None:
    span = source_span((7, 18, 7), blank=19, logical_length=259)
    left, rest = split(span, 86)
    middle, right = split(rest, 87)
    assert (left.length, middle.length, right.length) == (86, 1, 172)
    assert left.end == middle.start and middle.end == right.start
    for part in (left, middle, right):
        assert sum(chunk.tile.width for chunk in part.chunks) == part.length
        assert all(chunk.start % chunk.tile.width == 0 for chunk in part.chunks)


def test_hashlife_production_source_has_no_rle_or_generation_padding_carrier() -> None:
    import number_compiler.hashlife.observation.hashlife_projection as hashlife
    import number_compiler.sequences.reverse_add.power as reverse_power

    hash_text = Path(hashlife.__file__).read_text()
    power_text = Path(reverse_power.__file__).read_text()
    # The historical compatibility executor owns no word-shaped temporal
    # carrier. Production family projection does not import this proof module.
    assert "def _partition3" not in hash_text
    assert "def _leaf_partition3" not in hash_text
    assert "def output_word" not in hash_text
    assert "def point(" not in hash_text
    assert "program_pop_last" not in hash_text
    from devtools import proofs

    package = Path(proofs.__file__).parent
    runtime_text = (package / "block_runtime.py").read_text()
    spacetime_text = (package / "block_spacetime_runtime.py").read_text()
    production_text = runtime_text + spacetime_text
    assert "from .program_word" not in production_text
    assert "CanonicalWord" not in production_text
    assert "def _eval_residual" not in production_text
    assert "def _output_word" not in production_text
    assert "def _output_tile_macro" not in spacetime_text
    assert "from .program_word" not in spacetime_text
    assert "padding = generation" not in power_text
    assert "logical_length=self.maximum_width" in power_text


def test_certified_reverse_uses_tile_hashlife_and_reports_concrete_work() -> None:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    term = ReverseAddPoweredTerm(196, 64)
    term.digit(0)
    point = term._point_index().metrics()
    behavior = term.behavior_metrics()
    assert point.bounded_application_enabled == 1
    assert behavior.temporal_quotient_family == "reverse-add-tile-hashlife"
    assert (
        behavior.temporal_quotient_state_class_bound == point.local_interface_nodes > 0
    )
    assert behavior.temporal_quotient_action_class_bound == point.field_action_nodes
    assert behavior.bounded_temporal_runtime_cutover_complete == 1
    assert behavior.bounded_temporal_runtime_cutover_blocker == ""
    assert behavior.representation_boundary_complete == 1
    assert behavior.unquotiented_recursive_application_description_nodes == 0
    assert point.application_program_nodes == 0
    assert point.field_action_nodes > 0
    assert point.temporal_parent_requests == (
        point.temporal_parent_early_hits + point.temporal_parent_compositions
    )
    assert point.reverse_t2_proof_left_state_classes == 757
    assert point.reverse_t2_proof_right_state_classes == 179
    assert (
        point.bounded_application_temporal_state_classes
        == point.local_interface_nodes
        > 0
    )
    assert point.bounded_application_temporal_action_classes == point.field_action_nodes
    assert point.whole_word_sweeps == point.whole_word_symbol_visits == 0
    assert point.proof_machine_applications == 0
    assert point.higher_concrete_operation_evaluations == 0
    assert point.tile_scheduler_leaf_function_applications > 0
    assert (
        point.bounded_application_nonlinear_branch_evaluations
        == point.primitive_transition_evaluations
        > 0
    )
    assert point.bounded_application_exact_endpoint_entries == 0
    assert point.exact_endpoint_nodes == 0
    assert point.forbidden_future_payloads == 0
    assert point.resource_audit_complete == 1


def test_finite_tile_actions_are_exact_for_every_t2_boundary_state_on_small_tiles() -> (
    None
):
    from number_compiler.arithmetic.contracts.block_effect import BoundarySide
    from number_compiler.arithmetic.contracts.block_kernel import _load_base10_t2_kernel
    from number_compiler.arithmetic.fields.dyadic_tile import join, leaf
    from devtools.proofs.finite_tile_action import (
        FiniteTileActionArena,
    )

    effect = _load_base10_t2_kernel()
    tile = join(join(leaf(7), leaf(18)), join(leaf(12), leaf(7)))
    arena = FiniteTileActionArena(effect)
    for side, count in (
        (BoundarySide.LEFT, effect.left_count),
        (BoundarySide.RIGHT, effect.right_count),
    ):
        for incoming in range(count):
            direct = incoming
            values: tuple[int, ...] = (7, 18, 12, 7)
            if side is BoundarySide.RIGHT:
                values = tuple(reversed(values))
            for symbol in values:
                direct = effect.advance(side, direct, symbol)
            assert arena.apply(side, tile, incoming) == direct


@pytest.mark.validation
def test_reverse_hashlife_semantic_action_interning_merges_distinct_tiles() -> None:
    """Run the N=128 public application before auditing semantic tile reuse."""
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    term = ReverseAddPoweredTerm(196, 128)
    term.digit(term.maximum_width // 3)
    metrics = term.metrics()
    # Cold canonical tiles may evaluate unresolved primitive leaves. That work
    # is reported separately from forbidden generation/continuation replay.
    assert metrics.hashlife_temporal_leaf_applications == (
        metrics.tile_scheduler_leaf_function_applications
    )
    assert metrics.hashlife_temporal_leaf_applications > 0
    assert metrics.higher_concrete_operation_evaluations == 0
    assert metrics.sequential_generation_advances == 0
    assert metrics.completed_result_entries > 0
    assert metrics.hashlife_direct_powered_point_queries == 1
    assert (
        metrics.hashlife_boundary_cache_entries <= 4 * term.maximum_width.bit_length()
    )
    assert metrics.hashlife_section_cache_entries == 0
    assert metrics.hashlife_leaf_cache_entries == 0
    assert metrics.spacetime_carry_direction == "lsd-to-msd"


def test_shared_reverse_add_carry_symmetry_is_exact_and_mirror_canonical() -> None:
    from number_compiler.arithmetic.automata.symmetry_powering import (
        ActionTransform,
        OrientedFiniteActionArena,
    )
    from number_compiler.arithmetic.carry.carry_symmetry import (
        reverse_add_carry_kernel,
        reverse_add_carry_word_action,
    )

    kernel = reverse_add_carry_kernel(10)
    kernel.verify_conjugacy()
    arena = OrientedFiniteActionArena(kernel)
    word = (2, 9, 15, 9, 18, 4)
    a = reverse_add_carry_word_action(word, base=10, arena=arena)
    b = reverse_add_carry_word_action(tuple(reversed(word)), base=10, arena=arena)
    complemented = tuple(18 - x for x in word)
    c = reverse_add_carry_word_action(complemented, base=10, arena=arena)
    assert a.action_id == b.action_id == c.action_id
    assert a.action_id == b.action_id
    assert (a.transform ^ c.transform) & ActionTransform.CONJUGATE
    for incoming in (0, 1):
        direct = incoming
        for symbol in word:
            direct = kernel.transition(direct, symbol)
        assert arena.apply(a.ref, incoming) == direct
