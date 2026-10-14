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
    from devtools import verification

    package = Path(verification.__file__).parent
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


@pytest.mark.validation
def test_reverse_q19_completed_occurrence_reuses_public_projection() -> None:
    """The punctured producer publishes an exact output reused by demand."""
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
    from tests.support.reverse_cutover import assert_q19_output_authority

    term = ReverseAddPoweredTerm(196, 128)
    position = term.maximum_width // 3
    expected = term.digit(position)
    workspace, occurrence = assert_q19_output_authority(term)
    assert occurrence.temporal_steps == 128
    exact_width = term.width()
    assert occurrence.output_width == exact_width

    counters = term._ledger.counters
    t2 = counters.get("reverse_q19_punctured_t2_applications", 0)
    t4 = counters.get("reverse_q19_punctured_t4_applications", 0)
    assert 2 * t2 + 4 * t4 > 0
    assert counters.get("reverse_q19_punctured_emitted_grammar_nodes", 0) > 0

    projection_hits = counters.get("source_image_projection_hits", 0)
    assert term.digit(position) == expected
    assert counters.get("source_image_projection_hits", 0) == projection_hits + 1

    metrics = term.metrics()
    assert metrics.higher_concrete_operation_evaluations == 0
    assert metrics.sequential_generation_advances == 0
    q19_owner = workspace.adapter._q19_owner
    assert q19_owner is not None
    q19_owner.validate(occurrence)
    issued = q19_owner.ledger.inventory_owner(q19_owner._issued.owner)
    grammar = q19_owner.ledger.inventory_owner(q19_owner.arena.owners[0])
    assert q19_owner._issued[(occurrence.root, occurrence.temporal_steps)] is occurrence
    assert issued.entries > 0
    assert grammar.entries == len(q19_owner.arena.nodes)
    assert grammar.nodes == len(q19_owner.arena.nodes)
    assert (
        q19_owner._summaries[occurrence.root].symbols
        == (occurrence.pair_width + 1) // 2
    )
    assert (
        metrics.hashlife_boundary_cache_entries <= 4 * term.maximum_width.bit_length()
    )
    assert metrics.hashlife_section_cache_entries == 0
    assert metrics.hashlife_leaf_cache_entries == 0
    assert metrics.spacetime_carry_direction == "lsd-to-msd"
    assert workspace is term._workspace


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
