from __future__ import annotations

import random
from typing import Never

import pytest

from number_compiler.arithmetic.automata.guard import (
    JumpAudit,
    JumpGuardViolation,
    powered_jump_scope,
)
from number_compiler.arithmetic.automata.slp import BimachineSLPProjector, SLPArena
from number_compiler.arithmetic.automata.transducer import (
    build_pair_step_bimachine,
    decode_pair_half,
    encode_pair_half,
)
from number_compiler.arithmetic.fields.tropical import TropicalMatrix, normalize_vector
from number_compiler.arithmetic.functions.decision import MultiTerminalDecisionArena
from number_compiler.arithmetic.functions.residual import minimize_bimachine
from number_compiler.hashlife.actions.power import compose_bimachines
from number_compiler.hashlife.execution.cascade_power import (
    build_left_context,
    build_right_context,
    compose_bimachines_cascade,
)


def ref_step(
    parity: int, half: tuple[int, ...], base: int = 10
) -> tuple[int, tuple[int, ...]]:
    # Use the exact one-step bimachine on a literal word as an independent codec-level reference.
    b = build_pair_step_bimachine(base)
    return decode_pair_half(b.output(encode_pair_half(parity, half, base)), base)


def test_slp_projection_matches_exact_bimachine_without_input_expansion() -> None:
    b = minimize_bimachine(build_pair_step_bimachine(10), cache_outputs=False).machine
    rng = random.Random(196)
    for _ in range(80):
        parity = rng.randrange(2)
        half = tuple(rng.randrange(19) for __ in range(rng.randrange(1, 8)))
        a = SLPArena()
        root = a.word(encode_pair_half(parity, half, 10))
        projector = BimachineSLPProjector(b, a)
        out = projector.apply(root)
        assert a.materialize(out) == b.output(encode_pair_half(parity, half, 10))


def test_repeat_projection_uses_powered_block_actions() -> None:
    b = minimize_bimachine(build_pair_step_bimachine(10), cache_outputs=False).machine
    a = SLPArena()
    # This is not necessarily a valid pair-half word; test DFA action powering on
    # a repeated internal value block inside a valid envelope.
    body = a.repeat(a.terminal(9), 64)
    root = a.concat_many((a.terminal(19), body, a.terminal(21)))
    p = BimachineSLPProjector(b, a)
    out = p.apply(root)
    literal = (19,) + (9,) * 64 + (21,)
    assert a.materialize(out) == b.output(literal)
    assert a.metrics(root).reachable_nodes <= 6


def test_slp_materialization_is_forbidden_in_powered_jump() -> None:
    a = SLPArena()
    q = a.word((1, 2, 3))
    audit = JumpAudit()
    with pytest.raises(JumpGuardViolation):
        with powered_jump_scope(audit):
            a.materialize(q)
    assert audit.forbidden_attempts["slp_materialize"] == 1


def test_tropical_projective_normalization_and_power() -> None:
    assert normalize_vector((7, 9, None, 12)) == (0, 2, None, 5)
    m = TropicalMatrix(((0, 3), (None, 0)))
    assert m.power(5).rows == ((0, 3), (None, 0))
    assert m.upper_triangular_signature() == ((0, 3), (None, 0))


def test_multiterminal_decision_cofactors_are_exact_and_shared() -> None:
    arena = MultiTerminalDecisionArena((4, 3, 5), order=(0, 1, 2))

    def f(x: tuple[int, ...]) -> tuple[int, ...] | None:
        left_index, a, r = x
        return (a,) if (left_index & 1) == (r & 1) else None

    root = arena.build(f)
    for left_index in range(4):
        for a in range(3):
            for r in range(5):
                assert arena.evaluate(root, (left_index, a, r)) == f((left_index, a, r))
    # l=0 and l=2 have exactly the same residual function of (a,r).
    assert arena.cofactor(root, {0: 0}) == arena.cofactor(root, {0: 2})
    assert arena.cofactor(root, {0: 1}) == arena.cofactor(root, {0: 3})
    assert arena.metrics().internal_nodes < 4 * 3 * 5


def test_grouped_cascade_composition_matches_exact_t2_without_flat_tuple_universe() -> (
    None
):
    b = minimize_bimachine(build_pair_step_bimachine(10), cache_outputs=False).machine
    c = compose_bimachines_cascade(
        b, b, state_cap=5000, time_cap=20, cache_outputs=False
    )
    assert c.complete and c.machine is not None
    # The research cascade still exposes the 690/91 raw determinized contexts.
    # Production composition now quotients primitive semantic witnesses *before*
    # determinization and therefore lands directly on the exact 688/91 quotient.
    canonical = compose_bimachines(
        b, b, state_cap=10000, time_cap=20, cache_outputs=False
    )
    assert (len(c.left.states), len(c.right.states)) == (690, 91)
    assert (
        len(canonical.machine.left.states),
        len(canonical.machine.right.states),
    ) == (688, 91)
    rng = random.Random(0x196)
    for _ in range(60):
        parity = rng.randrange(2)
        half = tuple(rng.randrange(19) for __ in range(rng.randrange(1, 7)))
        word = encode_pair_half(parity, half, 10)
        assert c.machine.output(word) == canonical.machine.output(word)
    assert c.left.metrics().represented_tuples > c.left.metrics().dependency_groups
    assert c.right.metrics().represented_tuples > c.right.metrics().dependency_groups


def test_quotient_first_t2_has_zero_late_state_merges_and_no_cartesian_output_scan() -> (
    None
):
    b = minimize_bimachine(build_pair_step_bimachine(10), cache_outputs=False).machine
    comp = compose_bimachines(b, b, state_cap=10000, time_cap=20, cache_outputs=False)
    cm = comp.metrics
    assert (cm.left_nfa_states, cm.primitive_left_classes, cm.left_dfa_states) == (
        2609,
        1857,
        688,
    )
    assert (cm.right_nfa_states, cm.primitive_right_classes, cm.right_dfa_states) == (
        378,
        150,
        91,
    )
    assert cm.primitive_refinement_rounds >= 1
    # 688*22*91 = 1,377,376 possible output contexts.  The canonical relation is
    # generated from only boundary-compatible primitive witnesses and then merged
    # into a few thousand Cartesian regions before the MTDD exists.
    possible = (
        len(comp.machine.left.states)
        * len(comp.machine.alphabet)
        * len(comp.machine.right.states)
    )
    assert cm.primitive_output_probes < possible // 10
    assert cm.semantic_generator_boxes < possible // 20
    assert cm.semantic_regions < 5000
    assert cm.semantic_decision_nodes < 500
    # Canonical output MTDD is authoritative; there is no per-context late cache.
    assert comp.machine.has_canonical_output
    assert comp.machine.cached_outputs == 0
    q = minimize_bimachine(comp.machine, cache_outputs=False)
    assert (q.metrics.left_before, q.metrics.left_after) == (688, 688)
    assert (q.metrics.right_before, q.metrics.right_after) == (91, 91)
    assert q.metrics.canonical_generator_boxes == cm.semantic_generator_boxes
    assert q.metrics.canonical_regions == cm.semantic_regions


def test_cascade_power_cap_is_not_usable_as_complete_operator() -> None:
    b1 = minimize_bimachine(build_pair_step_bimachine(10), cache_outputs=False).machine
    b2 = minimize_bimachine(
        compose_bimachines(b1, b1, state_cap=10000, time_cap=20).machine,
        cache_outputs=False,
    ).machine
    left = build_left_context(b2, b2, state_cap=25, time_cap=5)
    right = build_right_context(b2, b2, state_cap=25, time_cap=5)
    assert not left.complete
    assert not right.complete


def test_semantic_residual_minimizer_has_no_cartesian_grid_regression() -> None:
    import number_compiler.arithmetic.functions.residual as residual

    assert not hasattr(residual, "CompactOutputGrid")
    b = build_pair_step_bimachine(10)
    q = minimize_bimachine(b, cache_outputs=False)
    m = q.metrics
    assert (len(q.machine.left.states), len(q.machine.right.states)) == (50, 6)
    assert m.exact_output_probes == len(b.left.states) * len(b.alphabet) * len(
        b.right.states
    )
    assert m.decision_nodes > 0
    assert m.decision_nodes < m.exact_output_probes
    assert m.decision_groups < m.exact_output_probes


def test_quotient_first_composition_is_exhaustive_on_small_bases() -> None:
    from itertools import product

    for base in (2, 3, 4):
        step = minimize_bimachine(
            build_pair_step_bimachine(base), cache_outputs=False
        ).machine
        square = compose_bimachines(
            step, step, state_cap=10000, time_cap=20, cache_outputs=False
        ).machine
        values = range(2 * base - 1)
        for parity in (0, 1):
            for width in (1, 2):
                for half in product(values, repeat=width):
                    word = encode_pair_half(parity, half, base)
                    try:
                        once = step.output(word)
                        expected = step.output(once)
                    except ValueError:
                        continue
                    assert square.output(word) == expected


def test_power_table_t4_forbids_raw_primitive_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.actions.power as power

    b = minimize_bimachine(build_pair_step_bimachine(10), cache_outputs=False).machine
    table = power.ResidualPowerTable(b, state_cap=10000, time_cap=20)
    table.ensure(1)  # T^2 may use the exact quotient-first primitive compiler.
    table.state_cap = 25
    table.time_cap = 5

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("raw primitive composer used beyond T^2")

    monkeypatch.setattr(power, "compose_bimachines", forbidden)
    with pytest.raises(
        power.PowerConstructionLimit, match="canonical dependency cascade"
    ):
        table.ensure(2)


def test_canonical_output_boxes_reconstruct_exact_t2_relation() -> None:
    b = minimize_bimachine(build_pair_step_bimachine(10), cache_outputs=False).machine
    t2 = compose_bimachines(
        b, b, state_cap=10000, time_cap=20, cache_outputs=False
    ).machine
    rel = t2.canonical_output
    assert rel is not None
    boxes_by_symbol = {a: tuple(rel.iter_boxes(symbol=a)) for a in t2.alphabet}
    # Box regions are exact and disjoint: every sampled context has exactly one
    # matching output label, with no tuple-output cache involved.
    rng = random.Random(0xC196)
    for _ in range(500):
        left_index = rng.choice(t2.left.states)
        a = rng.choice(t2.alphabet)
        r = rng.choice(t2.right.states)
        hits = []
        for word, (lm, am, rm) in boxes_by_symbol[a]:
            if ((lm >> left_index) & 1) and ((rm >> r) & 1):
                hits.append(word)
        expected = t2.emit(left_index, a, r)
        if expected is None:
            assert hits == []
        else:
            assert hits == [expected]
    assert t2.cached_outputs == 0
