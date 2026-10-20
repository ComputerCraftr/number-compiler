from __future__ import annotations

import random
from itertools import product

import pytest

from devtools.verification.block_power import (
    apply_block_power,
    compose_block_effects,
    power_block_effect,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudget,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
)
from tests.support.reference_arithmetic import symmetric_word
from tests.support.reverse_pair_oracle import reference_successor

__all__ = ("symmetric_word",)


_UNIT_BLOCK_POWER_CASES = (
    (2, 0),
    (2, 1),
    (2, 8),
    (3, 2),
    (3, 8),
    (10, 0),
    (10, 4),
    (10, 8),
    (12, 1),
    (12, 8),
)
_FULL_BLOCK_POWER_CASES = tuple(product(range(2, 13), range(9)))
_BLOCK_POWER_CASES = tuple(
    pytest.param(base, exponent, False) for base, exponent in _UNIT_BLOCK_POWER_CASES
) + tuple(
    pytest.param(base, exponent, True, marks=pytest.mark.validation)
    for base, exponent in _FULL_BLOCK_POWER_CASES
)


@pytest.mark.parametrize("base,exponent,full_case", _BLOCK_POWER_CASES)
def test_block_power_exact_multibase_without_intermediate_generations(
    base: int, exponent: int, full_case: bool
) -> None:
    rng = random.Random(0xB10C196 + base * 9 + exponent)
    power = power_block_effect(base=base, exponent=exponent)
    source_samples = 8 if full_case else 2
    for _ in range(source_samples):
        source = symmetric_word(rng, base, rng.randint(1, 10))
        expected: tuple[int, ...] = source
        for _step in range(exponent):
            expected = reference_successor(expected, base)
        application = apply_block_power(power, source)
        assert application.values == expected
        assert application.intermediate_pair_words == 0
        assert application.elementary_generations == 0


def test_block_power_operator_syntax_is_logarithmic_for_huge_exponent() -> None:
    exponent = 10**18
    power = power_block_effect(base=10, exponent=exponent)
    bits = exponent.bit_length()
    assert power.exponent == exponent
    assert power.compose_operations <= 2 * bits
    assert power.operator_nodes <= 2 * bits
    assert power.syntax_depth <= bits + 1
    # Construction does not discover seed-specific contexts because no source
    # has been applied yet.  Only the two initial residuals per composition node
    # are retained by the generic semantic operator.
    assert power.budget.created_nodes <= 4 * power.compose_operations


def test_block_power_application_separates_compact_operator_from_projection_work() -> (
    None
):
    source = (7, 18, 7)
    exponent = 32
    power = power_block_effect(base=10, exponent=exponent)
    application = apply_block_power(power, source)
    expected: tuple[int, ...] = source
    for _ in range(exponent):
        expected = reference_successor(expected, 10)
    assert application.values == expected
    assert application.represented_positions == len(source) + exponent
    assert power.operator_nodes < application.represented_positions


def test_t2_residual_identity_is_exact_function_not_history() -> None:
    # The generic constructor itself is extensional: different derivations of
    # the same continuation function return one object identity.
    base = BaseBlockEffect(10)
    effect = compose_block_effects(base, base, budget=BlockContextBudget())
    start = effect.initial(BoundarySide.LEFT)
    direct = effect.advance(BoundarySide.LEFT, start, 10)
    via_neutral_prefix = effect.advance(
        BoundarySide.LEFT,
        effect.advance(BoundarySide.LEFT, start, 0),
        10,
    )
    assert direct is via_neutral_prefix
    stats = effect.runtime_stats()
    assert stats["functional_residual_intern_hits"] >= 1
    assert stats["canonical_function_left_states"] >= 1
    assert stats["canonical_function_right_states"] >= 1
    assert stats["provenance_path_left_states"] == 0
    assert stats["provenance_path_right_states"] == 0


def test_projection_memos_do_not_drop_exact_reusable_entries() -> None:
    source = (7, 18, 7)
    power = power_block_effect(base=10, exponent=64, max_cache_entries=1_000_000)
    application = apply_block_power(power, source)
    stats = application.runtime_stats
    assert stats["residual_cache_dropped_entries"] == 0
    assert stats["output_cache_slots"] == stats["output_cache_occupied"]
    assert stats["retained_cache_entries"] > 0
    assert stats["canonical_program_word_roots"] == 0
    assert stats["canonical_spacetime_boundary_roots"] == 0
    assert stats["canonical_recursive_left_states"] > 0
    assert stats["recursive_action_left_nodes"] > 0
    assert stats["sparse_carrier_layers_left"] == 0
    assert stats["sparse_carrier_layers_right"] == 0
    assert stats["spacetime_tile_output_entries"] > 0
    assert stats["provenance_path_left_states"] == 0
    assert stats["provenance_path_right_states"] == 0
    assert stats["positional_context_vectors"] == 0


def test_composed_runtime_stats_contain_no_retired_finite_kernel() -> None:
    power = power_block_effect(base=10, exponent=1024)
    assert power.root is not None
    stats = power.root.runtime_stats()
    assert stats["finite_kernel_left_states"] == 0
    assert stats["finite_kernel_right_states"] == 0
    assert stats["finite_kernel_storage_bytes"] == 0


def test_t4_uses_canonical_partition_decision_state_not_history() -> None:
    effect = power_block_effect(base=10, exponent=4).root
    assert effect is not None

    # These are distinct input histories but the exact T^4 left continuation
    # functions are equal over the complete primitive-composition domain.
    start_left = effect.initial(BoundarySide.LEFT)
    a = effect.advance(
        BoundarySide.LEFT,
        effect.advance(BoundarySide.LEFT, start_left, 19),
        0,
    )
    b = effect.advance(
        BoundarySide.LEFT,
        effect.advance(BoundarySide.LEFT, start_left, 19),
        1,
    )
    assert a is b

    # Same check on the opposite side. Equality is partition/MTDD identity,
    # not a cache hit on one sampled argument.
    start_right = effect.initial(BoundarySide.RIGHT)
    c = effect.advance(
        BoundarySide.RIGHT,
        effect.advance(BoundarySide.RIGHT, start_right, 0),
        0,
    )
    d = effect.advance(
        BoundarySide.RIGHT,
        effect.advance(BoundarySide.RIGHT, start_right, 1),
        0,
    )
    assert c is d

    stats = effect.runtime_stats()
    assert stats["canonical_partition_left_states"] > 0
    assert stats["canonical_partition_right_states"] > 0
    assert stats["partition_residual_intern_hits"] >= 2
    assert stats["provenance_path_left_states"] == 0
    assert stats["provenance_path_right_states"] == 0


def test_blank_tail_power_theorem_is_linear_not_serially_overcounted() -> None:
    # A T^N padded operator can activate at most N growth blanks.  The left
    # boundary settles after N blanks and the right after N-1: first-child left
    # and right settling happens in parallel before the second child tail.
    for exponent in (2, 4, 8, 16, 32, 64, 128, 256, 512, 1024):
        effect = power_block_effect(base=10, exponent=exponent).root
        assert effect is not None
        assert effect.blank_left_tail == exponent
        assert effect.blank_right_tail == exponent - 1


def test_parallel_blank_tail_theorem_preserves_long_power_semantics() -> None:
    source = (7, 18, 7)
    expected: tuple[int, ...] = source
    for _ in range(256):
        expected = reference_successor(expected, 10)
    power = power_block_effect(
        base=10, exponent=256, max_context_nodes=2_000_000, max_cache_entries=2_000_000
    )
    got = apply_block_power(power, source)
    assert got.values == expected
    assert power.root is not None
    assert power.root.blank_left_tail == 256
    assert power.root.blank_right_tail == 255


def test_higher_spacetime_macrocells_use_recursive_actions_not_boundary_roots() -> None:
    from devtools.verification.block_composed import ComposedBlockEffect

    # T16 includes T4, T8 and their recursive parents. Larger endpoints add
    # compatibility-lowering work without exercising another storage invariant.
    power = power_block_effect(base=10, exponent=16)
    application = apply_block_power(power, (7, 18, 7))
    stats = application.runtime_stats
    assert stats["canonical_program_word_roots"] == 0
    assert not hasattr(power.budget, "program_word_roots")
    assert stats["canonical_spacetime_boundary_roots"] == 0
    assert not hasattr(power.budget, "spacetime_boundary_roots")
    assert stats["canonical_recursive_left_states"] > 0
    assert stats["recursive_action_left_nodes"] > 0
    assert stats["spacetime_boundary_advance_cache_entries"] == 0
    assert stats["spacetime_boundary_output_cache_entries"] == 0
    assert stats["spacetime_sparse_transition_cache_entries"] == 0
    assert stats["spacetime_tile_output_entries"] > 0
    assert stats.get("proof_machine_applications", 0) == 0
    assert stats.get("whole_word_sweeps", 0) == 0
    # The frozen proof operator remains metadata only. Compatibility lowering
    # publishes its recursive parent/output records in the per-application
    # field runtime rather than repopulating the proof execution caches.
    assert power.root is not None
    proof_stats = power.root.runtime_stats()
    assert proof_stats["spacetime_tile_output_entries"] == 0
    assert proof_stats["spacetime_macro_cache_entries"] == 0

    # No temporal layer is allowed to retain another set of the same macrocell ids.
    stack = [power.root]
    seen: set[object] = set()
    while stack:
        node = stack.pop()
        node_id = getattr(node, "node_id", id(node))
        if node_id in seen:
            continue
        seen.add(node_id)
        if isinstance(node, ComposedBlockEffect):
            assert not hasattr(node, "_sparse_roots")
            stack.extend((node.first, node.second))


def test_partition_ids_are_final_before_recursive_parent_use() -> None:
    from pathlib import Path

    import devtools.verification.block_partition as partition_mod
    from devtools.verification.block_composed import ComposedBlockEffect
    from tests.support.diamond_halos import suffix_parity

    # A finite child explicitly admits the partition carrier. Reverse T4 now
    # uses recursive actions and does not populate this compatibility carrier.
    kernel = suffix_parity()
    budget = BlockContextBudget(1_000_000, 1_000_000)
    partition = compose_block_effects(kernel, kernel, budget=budget)
    assert isinstance(partition, ComposedBlockEffect)
    parent = compose_block_effects(partition, partition, budget=budget)

    def warm_parent() -> tuple[object, ...]:
        final_states: list[object] = []
        for side in (BoundarySide.LEFT, BoundarySide.RIGHT):
            state = parent.initial(side)
            for symbol in (0, 1, 2, 3):
                state = parent.advance(side, state, symbol)
            final_states.append(state)
        return tuple(final_states)

    expected = warm_parent()
    stats = partition.runtime_stats()
    assert stats["behavioral_partition_left_aliases"] == 0
    assert stats["behavioral_partition_right_aliases"] == 0
    assert stats["behavioral_partition_left_refinement_runs"] == 0
    assert stats["behavioral_partition_right_refinement_runs"] == 0
    assert not hasattr(partition, "refine_partition_behavioral_aliases")

    # A recursive parent retains its child's partition objects. Their IDs must
    # remain final so a warm parent cannot retain stale child identities.
    states = partition.partition_identity_snapshot()
    before = {state.object_id: state.node_id for state in states}
    assert states
    assert all(state.canonical for state in states)

    assert warm_parent() == expected
    after = partition.partition_identity_snapshot()
    assert all(state.canonical for state in after)
    assert {state.object_id: state.node_id for state in after} == before

    source = Path(partition_mod.__file__).read_text()
    assert "canonical_representative" not in source
    assert "refine_partition_behavioral_aliases" not in source


def test_program_word_transient_cache_clear_preserves_live_canonical_identity() -> None:
    from number_compiler.arithmetic.automata.program_word import (
        clear_transient_program_word_caches,
        concat,
        run,
    )

    left = run(3, 7)
    right = run(5, 11)
    word = concat(left, right)
    clear_transient_program_word_caches()
    again = concat(left, right)
    assert again is word


def test_program_word_global_interners_do_not_retain_unreferenced_words() -> None:
    import gc
    from weakref import ref

    from number_compiler.arithmetic.automata.program_word import concat, run

    left = run(10_000_019, 7)
    right = run(10_000_079, 11)
    word = concat(left, right)
    references = (ref(left), ref(right), ref(word))
    del left, right, word
    gc.collect()
    assert all(reference() is None for reference in references)
