from __future__ import annotations

import pytest

from devtools.verification import comma_borrow_vieta_audit as audit
from devtools.verification.comma_semantic_quotients import CommaFutureGraph
from number_compiler.sequences.comma import occurrence as occurrence_module
from number_compiler.sequences.comma.boundary_chart import PERIOD
from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    construct_macro,
)
from number_compiler.sequences.comma.carry_generator import (
    BitsCharge,
    BoundC1Return,
    C1Phase,
    WorkCharge,
    source_bound_return,
)
from number_compiler.sequences.comma.occurrence import OccurrencePrefixReturn


def test_macro_cycle_fragments_use_the_shared_powered_c1_return(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state = BoundaryState("N", 2, 10)
    macro = construct_macro(state, grouped_near=True)
    assert any(fragment.period for fragment in macro.sector_fragments)
    calls: list[tuple[int, int]] = []
    shared_source_bound_return = source_bound_return

    def tracked_return(
        source_value: int,
        start: C1Phase,
        steps: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> BoundC1Return:
        calls.append((start.sector, steps))
        return shared_source_bound_return(
            source_value,
            start,
            steps,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )

    monkeypatch.setattr(occurrence_module, "source_bound_return", tracked_return)
    result = audit.macro_c1_return_constructive(macro, 10)
    assert calls
    assert any(steps > 1 for _, steps in calls)
    assert 0 <= result.terminal_low_suffix < 100
    assert result.c1_count >= 0


def test_child_returns_use_actual_transported_exponent() -> None:
    parent = BoundaryState("N", 5, 921)
    parent_macro = construct_macro(parent, grouped_near=True)
    assert parent_macro.exponent_delta == 8
    assert parent_macro.ordered_children == (
        BoundaryState("N", 6, 5),
        BoundaryState("Z", 6, 5),
    )
    actual_exponent = audit.canonical_exponent(parent.exponent_residue)
    actual_exponent += parent_macro.exponent_delta
    assert actual_exponent == 929

    states = tuple(
        BoundaryState(kind, a, residue)
        for kind in ("N", "Z")
        for a in range(2, 10)
        for residue in range(PERIOD)
    )
    parent_id = audit._state_id(parent)
    macro_slots = [parent_macro] * len(states)
    cache: dict[tuple[int, int], OccurrencePrefixReturn] = {}
    canonical: list[OccurrencePrefixReturn] = []
    for child in parent_macro.ordered_children:
        child_id = audit._state_id(child)
        child_macro = construct_macro(child, grouped_near=True)
        macro_slots[child_id] = child_macro
        canonical_exponent = audit.canonical_exponent(child.exponent_residue)
        canonical_return = audit.macro_c1_return_constructive(
            child_macro, canonical_exponent
        )
        cache[(child_id, canonical_exponent)] = canonical_return
        canonical.append(canonical_return)

    actual = audit._macro_child_returns(
        parent_id,
        audit.canonical_exponent(parent.exponent_residue),
        states,
        tuple(macro_slots),
        cache,
    )
    assert all(result is not None for result in actual)
    actual_returns = tuple(result for result in actual if result is not None)

    assert tuple(result.c1_count for result in canonical) == (4_000, 93_999)
    assert tuple(result.c1_count for result in actual_returns) == (
        4_000 * 10**PERIOD,
        94_000 * 10**PERIOD - 1,
    )
    assert actual_returns[0] is not canonical[0]
    assert actual_returns[1] is not canonical[1]
    assert tuple(result.source.exponent for result in actual_returns) == (929, 929)
    assert tuple(result.width_delta for result in actual_returns) == tuple(
        macro_slots[audit._state_id(child)].exponent_delta
        for child in parent_macro.ordered_children
    )
    assert (audit._state_id(parent_macro.ordered_children[0]), actual_exponent) in cache
    assert (audit._state_id(parent_macro.ordered_children[1]), actual_exponent) in cache
    actual_zeta = actual_returns[1].c1_count - actual_returns[0].c1_count + 1
    canonical_zeta = canonical[1].c1_count - canonical[0].c1_count + 1
    assert canonical_zeta == 90_000
    assert actual_zeta == canonical_zeta * 10**PERIOD


def test_fragment_accumulation_can_run_without_endpoint_evaluation() -> None:
    state = BoundaryState("N", 2, 10)
    macro = construct_macro(state, grouped_near=True)

    class PoisonEndpoint:
        def evaluate_at_scale(self, _scale: int) -> int:
            pytest.fail("fragment producer read the completed macro endpoint")

    object.__setattr__(macro, "endpoint", PoisonEndpoint())
    result = audit.macro_c1_return_constructive(macro, 10, check_endpoint=False)
    assert 0 <= result.terminal_low_suffix < 100
    assert result.c1_count >= 0


def test_greatest_live_pruning_uses_reverse_edges_and_preserves_cycles() -> None:
    states = tuple(BoundaryState("N", 2, residue) for residue in range(8))
    graph = CommaFutureGraph(
        states,
        (
            (1, None),
            (2, None),
            (1, None),
            (0, None),
            (5, None),
            (None, None),
            (5, None),
            (7, None),
        ),
        (0,) * len(states),
    )

    assert audit.greatest_live_fixed_point(graph) == frozenset((0, 1, 2, 3, 7))


def test_pointed_only_payload_does_not_construct_c1_returns(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    states = tuple(BoundaryState("N", 2, residue) for residue in range(4))
    graph = CommaFutureGraph(
        states,
        ((1, None), (None, 0), (3, None), (None, None)),
        (462, 462, 0, 0),
    )

    def forbidden(*_args: object, **_kwargs: object) -> OccurrencePrefixReturn:
        pytest.fail("pointed-only path constructed carry returns")

    monkeypatch.setattr(audit, "macro_c1_return_constructive", forbidden)
    payload = audit._pointed_only_payload(graph)
    assert payload["rank_labelled"] is False
    assert payload["endpoint_derived_counts"] is False
    scope = payload["scope"]
    assert isinstance(scope, dict)
    assert scope["macro_c1_runtime_used"] is False
    assert payload["endpoint_role"] == "not evaluated in pointed-only mode"
