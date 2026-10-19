from __future__ import annotations

import base64
from collections.abc import Callable
from types import MappingProxyType
from typing import cast

import pytest

from number_compiler.sequences.comma import future_authority, future_provider
from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    boundary_source_index,
    construct_macro,
)
from number_compiler.sequences.comma.future_authority import (
    FINITE_TEST_FIXTURE_CLAIMS,
    FINITE_TEST_FIXTURE_CONTRACT_ID,
    FINITE_TEST_FIXTURE_SCOPE,
    FINITE_TEST_FIXTURE_SESSION_ID,
    FINITE_TEST_FIXTURE_THEOREM_ID,
    SOURCE20_FIRST_FORK_CHILDREN,
    SOURCE20_FIRST_FORK_INDEX,
    SOURCE20_FIRST_FORK_VALUE,
    SOURCE20_SELECTED_CHILD_INDEX,
)
from number_compiler.sequences.comma.occurrence import (
    BoundaryOccurrence,
    OccurrencePrefixReturn,
)
from number_compiler.sequences.comma.semantic_branch import (
    SemanticMacroChild,
    bind_source20_first_child_entry,
    select_global_semantic_macro_child,
    select_semantic_macro_child,
)
from number_compiler.sequences.comma.weighted_return import WeightedBoundaryAction


def _work_log() -> Callable[[int], None]:
    def charge(amount: int) -> None:
        if type(amount) is not int or amount <= 0:
            raise ValueError("test charger received an invalid amount")

    return charge


def _candidate_for_prefix(
    prefix: OccurrencePrefixReturn,
    *,
    selected_slot: int,
    reverse_child_classes: bool = False,
) -> dict[str, object]:
    children = prefix.ordered_children()
    assert len(children) == 2
    n_class, z_class = (1, 0)
    child_classes = (n_class, z_class)
    if reverse_child_classes:
        child_classes = (child_classes[1], child_classes[0])

    source_classes = bytearray(future_provider.SOURCE_COUNT)
    source_classes[boundary_source_index(prefix.source.state)] = 2
    source_classes[boundary_source_index(children[0].state)] = n_class
    source_classes[boundary_source_index(children[1].state)] = z_class
    finite_slot = 1 - selected_slot
    class_ranks: list[int | None] = [None, None, None]
    class_ranks[child_classes[finite_slot]] = 0
    return {
        "format": future_provider.FUTURE_CANDIDATE_FORMAT,
        "authority": future_provider.FUTURE_CANDIDATE_AUTHORITY,
        "state_universe": future_provider.FUTURE_SOURCE_UNIVERSE,
        "class_of_state_varint_base64": base64.b64encode(source_classes).decode(
            "ascii"
        ),
        "controls": [
            ["landmine", None],
            ["landmine", None],
            ["fork", prefix.template.destination_a],
        ],
        "ordered_children": [[None, None], [None, None], list(child_classes)],
        "class_rank_candidate": class_ranks,
    }


def _admitted_provider(
    monkeypatch: pytest.MonkeyPatch,
    record: dict[str, object],
    charge_work: Callable[[int], None],
) -> future_provider.SemanticFutureProvider:
    parsed = future_provider.parse_future_candidate(record, charge_work=charge_work)
    admission = future_authority.KernelInstanceAdmission(
        artifact_sha256=parsed.artifact_sha256,
        instance_id=FINITE_TEST_FIXTURE_SESSION_ID,
        theorem_id=FINITE_TEST_FIXTURE_THEOREM_ID,
        contract_id=FINITE_TEST_FIXTURE_CONTRACT_ID,
        claims=FINITE_TEST_FIXTURE_CLAIMS,
        scope=FINITE_TEST_FIXTURE_SCOPE,
    )
    monkeypatch.setattr(
        future_provider,
        "_ADMITTED_KERNEL_INSTANCES",
        MappingProxyType({parsed.artifact_sha256: admission}),
    )
    return future_provider.SemanticFutureProvider.from_record(
        record, charge_work=charge_work
    )


def _source_prefix() -> tuple[BoundaryOccurrence, OccurrencePrefixReturn]:
    source = BoundaryOccurrence(BoundaryState("N", 9, 5), 5)
    prefix = OccurrencePrefixReturn(
        source,
        construct_macro(source.state, grouped_near=True),
    )
    assert prefix.outcome == "fork"
    return source, prefix


def _literal_children(prefix: OccurrencePrefixReturn) -> tuple[int, int]:
    values = tuple(child.value() for child in prefix.ordered_children())
    assert len(values) == 2
    return values[0], values[1]


def test_production_branch_rejects_fixture_before_observation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source, prefix = _source_prefix()
    provider = _admitted_provider(
        monkeypatch, _candidate_for_prefix(prefix, selected_slot=0), _work_log()
    )

    def forbid_observation(*_args: object, **_kwargs: object) -> None:
        pytest.fail("fixture admission triggered production occurrence observation")

    monkeypatch.setattr(
        OccurrencePrefixReturn, "ordered_literal_children", forbid_observation
    )
    with pytest.raises(PermissionError, match="global release authority"):
        select_global_semantic_macro_child(
            source,
            prefix,
            fork_value=0,
            ordered_literal_children=(0, 0),
            provider=provider,
            charge_work=forbid_observation,
        )


def test_source20_entry_requires_exact_order_and_global_authority(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _source, prefix = _source_prefix()
    record = _candidate_for_prefix(prefix, selected_slot=0)
    provider = _admitted_provider(monkeypatch, record, _work_log())
    assert provider.runtime_admitted
    assert not provider.global_release_admitted

    with pytest.raises(ValueError, match="global first-child theorem"):
        bind_source20_first_child_entry(
            parent_index=SOURCE20_FIRST_FORK_INDEX,
            parent_value=SOURCE20_FIRST_FORK_VALUE,
            child_index=SOURCE20_SELECTED_CHILD_INDEX,
            provider=provider,
            charge_work=_work_log(),
            ordered_children=(
                SOURCE20_FIRST_FORK_CHILDREN[1],
                SOURCE20_FIRST_FORK_CHILDREN[0],
            ),
        )
    with pytest.raises(PermissionError, match="global release authority"):
        bind_source20_first_child_entry(
            parent_index=SOURCE20_FIRST_FORK_INDEX,
            parent_value=SOURCE20_FIRST_FORK_VALUE,
            child_index=SOURCE20_SELECTED_CHILD_INDEX,
            provider=provider,
            charge_work=_work_log(),
            ordered_children=SOURCE20_FIRST_FORK_CHILDREN,
        )

    with pytest.raises(PermissionError, match="global release authority"):
        bind_source20_first_child_entry(
            parent_index=SOURCE20_FIRST_FORK_INDEX,
            parent_value=SOURCE20_FIRST_FORK_VALUE,
            ordered_children=SOURCE20_FIRST_FORK_CHILDREN,
            child_index=SOURCE20_SELECTED_CHILD_INDEX,
            provider=provider,
            charge_work=_work_log(),
        )


def _selected_child_for_mutation(
    monkeypatch: pytest.MonkeyPatch,
) -> SemanticMacroChild:
    source, prefix = _source_prefix()
    charge_work = _work_log()
    provider = _admitted_provider(
        monkeypatch,
        _candidate_for_prefix(prefix, selected_slot=1),
        charge_work,
    )
    return select_semantic_macro_child(
        source,
        prefix,
        fork_value=prefix.terminal_value,
        ordered_literal_children=_literal_children(prefix),
        provider=provider,
        charge_work=charge_work,
    )


def test_semantic_branch_binds_ordered_literal_choice_and_weighted_event(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source, prefix = _source_prefix()
    charge_work = _work_log()
    record = _candidate_for_prefix(prefix, selected_slot=1)
    provider = _admitted_provider(monkeypatch, record, charge_work)
    literal_children = _literal_children(prefix)
    expected_action = WeightedBoundaryAction.from_selected_fork(
        prefix.template,
        prefix.template.ordered_children[1],
    )
    calls: list[int] = []
    original_value = BoundaryOccurrence.value

    def count_value(
        occurrence: BoundaryOccurrence,
        *,
        charge_work: Callable[[int], None] | None = None,
        charge_bits: Callable[[int], None] | None = None,
    ) -> int:
        calls.append(1)
        return original_value(
            occurrence,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )

    def reject_legacy_child_view(*_args: object, **_kwargs: object) -> None:
        pytest.fail("adapter must use the validated ordered literal-child view")

    monkeypatch.setattr(BoundaryOccurrence, "value", count_value)
    monkeypatch.setattr(
        OccurrencePrefixReturn,
        "ordered_children",
        reject_legacy_child_view,
    )

    selected = select_semantic_macro_child(
        source,
        prefix,
        fork_value=prefix.terminal_value,
        ordered_literal_children=literal_children,
        provider=provider,
        charge_work=charge_work,
    )

    assert selected.selection.selected_slot == 1
    assert selected.literal_value == literal_children[1]
    assert selected.occurrence.target.state == prefix.template.ordered_children[1]
    assert selected.occurrence.target.exponent == source.exponent + prefix.width_delta
    assert selected.fork_event_offset == prefix.transition_count
    assert selected.total_transition_count == prefix.transition_count + 1
    assert selected.weighted_action == expected_action
    assert selected.weighted_action.exponent_delta == prefix.width_delta
    assert len(calls) == 2


def test_semantic_branch_rejects_wrong_fork_value_children_and_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source, prefix = _source_prefix()
    charge_work = _work_log()
    provider = _admitted_provider(
        monkeypatch,
        _candidate_for_prefix(prefix, selected_slot=1),
        charge_work,
    )
    children = _literal_children(prefix)

    with pytest.raises(ValueError, match="terminal differs"):
        select_semantic_macro_child(
            source,
            prefix,
            fork_value=prefix.terminal_value + 1,
            ordered_literal_children=children,
            provider=provider,
            charge_work=charge_work,
        )
    with pytest.raises(ValueError, match="differ from the exact boundary children"):
        select_semantic_macro_child(
            source,
            prefix,
            fork_value=prefix.terminal_value,
            ordered_literal_children=(children[1], children[0]),
            provider=provider,
            charge_work=charge_work,
        )
    with pytest.raises(ValueError, match="bound to another source occurrence"):
        select_semantic_macro_child(
            BoundaryOccurrence(BoundaryState("N", 8, 5), 5),
            prefix,
            fork_value=prefix.terminal_value,
            ordered_literal_children=children,
            provider=provider,
            charge_work=charge_work,
        )


def test_semantic_branch_charges_large_caller_integers_before_comparison(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source, prefix = _source_prefix()
    charge_work = _work_log()
    provider = _admitted_provider(
        monkeypatch,
        _candidate_for_prefix(prefix, selected_slot=1),
        charge_work,
    )
    children = _literal_children(prefix)
    large_value = -(1 << 4096)
    bit_charges: list[int] = []

    def charge_bits(amount: int) -> None:
        bit_charges.append(amount)

    with pytest.raises(ValueError, match="terminal differs"):
        select_semantic_macro_child(
            source,
            prefix,
            fork_value=large_value,
            ordered_literal_children=children,
            provider=provider,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
    assert bit_charges[0] >= large_value.bit_length()

    bit_charges.clear()
    with pytest.raises(ValueError, match="differ from the exact boundary children"):
        select_semantic_macro_child(
            source,
            prefix,
            fork_value=prefix.terminal_value,
            ordered_literal_children=(large_value, children[1]),
            provider=provider,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
    assert bit_charges[-1] >= large_value.bit_length()


def test_semantic_branch_rejects_provider_child_class_slot_mismatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source, prefix = _source_prefix()
    charge_work = _work_log()
    provider = _admitted_provider(
        monkeypatch,
        _candidate_for_prefix(
            prefix,
            selected_slot=1,
            reverse_child_classes=True,
        ),
        charge_work,
    )
    children = _literal_children(prefix)

    with pytest.raises(ValueError, match="child slots differ"):
        select_semantic_macro_child(
            source,
            prefix,
            fork_value=prefix.terminal_value,
            ordered_literal_children=children,
            provider=provider,
            charge_work=charge_work,
        )


def test_comma_term_rejects_child_cid_mismatch_before_boundary_return(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.comma.image_adapter import CommaOccurrenceID
    from number_compiler.sequences.comma.power import CommaTerm

    source, prefix = _source_prefix()
    charge_work = _work_log()
    provider = _admitted_provider(
        monkeypatch,
        _candidate_for_prefix(
            prefix,
            selected_slot=1,
            reverse_child_classes=True,
        ),
        charge_work,
    )
    with CommaTerm(1) as term:
        template = term.arena._boundary_template(source.state)
        prefix_steps = template.weight.evaluate(
            source.exponent,
            charge_bits=term.arena.charge_bits,
        )
        term.index = term._current_index + prefix_steps + 1
        term._boundary_occurrence = source
        term._boundary_occurrence_owner = cast(CommaOccurrenceID, term._source)
        monkeypatch.setattr(term, "_require_global_future_provider", lambda: provider)

        def reject_boundary_publication(*_args: object, **_kwargs: object) -> None:
            pytest.fail("mismatched child CIDs reached the boundary-return publisher")

        monkeypatch.setattr(
            term.arena, "_global_boundary_return", reject_boundary_publication
        )
        with pytest.raises(ValueError, match="child slots differ"):
            term._resolve()


def test_semantic_branch_rejects_total_fake_selection_sentinel(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source, prefix = _source_prefix()
    charge_work = _work_log()
    provider = _admitted_provider(
        monkeypatch,
        _candidate_for_prefix(prefix, selected_slot=1),
        charge_work,
    )

    def return_none(
        _self: future_provider.SemanticFutureProvider,
        _source_state: BoundaryState,
        *,
        charge_work: Callable[[int], None],
    ) -> None:
        del charge_work

    monkeypatch.setattr(
        future_provider.SemanticFutureProvider,
        "select_unique_unranked_child",
        return_none,
    )
    with pytest.raises(TypeError, match="malformed child selection"):
        select_semantic_macro_child(
            source,
            prefix,
            fork_value=prefix.terminal_value,
            ordered_literal_children=_literal_children(prefix),
            provider=provider,
            charge_work=charge_work,
        )


def test_semantic_branch_rejects_boolean_alias_from_source_lookup(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source, prefix = _source_prefix()
    charge_work = _work_log()
    provider = _admitted_provider(
        monkeypatch,
        _candidate_for_prefix(prefix, selected_slot=1),
        charge_work,
    )
    selection = provider.select_unique_unranked_child(
        source.state,
        charge_work=charge_work,
    )
    # Construct a valid-looking selection with the wrong integral source CID.
    # The forged bool result below aliases it under Python equality.
    object.__setattr__(selection, "source_class", 1)
    actual_source_class = future_provider.SemanticFutureProvider.source_class

    def bool_alias_for_source(
        self: future_provider.SemanticFutureProvider,
        state: BoundaryState,
        *,
        charge_work: Callable[[int], None],
    ) -> int:
        if state == source.state:
            charge_work(1)
            return True
        return actual_source_class(self, state, charge_work=charge_work)

    def return_forged_selection(
        _self: future_provider.SemanticFutureProvider,
        _state: BoundaryState,
        *,
        charge_work: Callable[[int], None],
    ) -> future_provider.UnrankedChildSelection:
        charge_work(1)
        return selection

    monkeypatch.setattr(
        future_provider.SemanticFutureProvider,
        "source_class",
        bool_alias_for_source,
    )
    monkeypatch.setattr(
        future_provider.SemanticFutureProvider,
        "select_unique_unranked_child",
        return_forged_selection,
    )
    with pytest.raises(ValueError, match="malformed source CID"):
        select_semantic_macro_child(
            source,
            prefix,
            fork_value=prefix.terminal_value,
            ordered_literal_children=_literal_children(prefix),
            provider=provider,
            charge_work=charge_work,
        )


def test_semantic_branch_rejects_mutated_source_kind_alias(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source, prefix = _source_prefix()
    charge_work = _work_log()
    provider = _admitted_provider(
        monkeypatch,
        _candidate_for_prefix(prefix, selected_slot=1),
        charge_work,
    )
    selection = provider.select_unique_unranked_child(
        source.state,
        charge_work=charge_work,
    )

    class NKindAlias:
        def __eq__(self, other: object) -> bool:
            return other == "N"

    forged_source = BoundaryState("N", 9, 5)
    object.__setattr__(forged_source, "kind", NKindAlias())
    object.__setattr__(selection, "source", forged_source)

    def return_forged_selection(
        _self: future_provider.SemanticFutureProvider,
        _state: BoundaryState,
        *,
        charge_work: Callable[[int], None],
    ) -> future_provider.UnrankedChildSelection:
        charge_work(1)
        return selection

    monkeypatch.setattr(
        future_provider.SemanticFutureProvider,
        "select_unique_unranked_child",
        return_forged_selection,
    )
    with pytest.raises(ValueError, match="malformed comma boundary source state"):
        select_semantic_macro_child(
            source,
            prefix,
            fork_value=prefix.terminal_value,
            ordered_literal_children=_literal_children(prefix),
            provider=provider,
            charge_work=charge_work,
        )


def test_semantic_macro_child_detects_selection_handle_mutation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    selected = _selected_child_for_mutation(monkeypatch)
    object.__setattr__(selected.selection, "selected_slot", 0)
    with pytest.raises(ValueError, match="FutureCID snapshot changed"):
        _ = selected.target


@pytest.mark.parametrize(
    "payload_field",
    ("literal_value", "numerator_scale", "numerator_offset", "denominator"),
)
def test_semantic_macro_child_detects_numeric_payload_mutation(
    monkeypatch: pytest.MonkeyPatch,
    payload_field: str,
) -> None:
    selected = _selected_child_for_mutation(monkeypatch)

    if payload_field == "literal_value":
        object.__setattr__(selected, payload_field, selected.literal_value + 1)
    else:
        weight = selected.weighted_action.weight
        object.__setattr__(weight, payload_field, getattr(weight, payload_field) + 1)

    with pytest.raises(ValueError, match="numeric payload snapshot changed"):
        _ = selected.target


@pytest.mark.parametrize("endpoint", ("start", "end"))
def test_semantic_macro_child_rejects_equality_alias_in_action_binding(
    monkeypatch: pytest.MonkeyPatch,
    endpoint: str,
) -> None:
    class EqualityTrap:
        calls = 0

        def __eq__(self, _other: object) -> bool:
            self.calls += 1
            raise AssertionError("untrusted boundary equality was evaluated")

    selected = _selected_child_for_mutation(monkeypatch)
    exact_state = (
        selected.source.state if endpoint == "start" else selected.target.state
    )
    forged_state = BoundaryState(
        exact_state.kind,
        exact_state.a,
        exact_state.exponent_residue,
    )
    alias = EqualityTrap()
    object.__setattr__(forged_state, "kind", alias)
    object.__setattr__(selected.weighted_action, endpoint, forged_state)

    with pytest.raises(ValueError, match="noncanonical scalar fields"):
        _ = selected.target
    assert alias.calls == 0


def test_semantic_branch_requires_registered_provider_admission() -> None:
    source, prefix = _source_prefix()
    with pytest.raises(PermissionError, match="no kernel-admitted"):
        future_provider.SemanticFutureProvider.from_record(
            _candidate_for_prefix(prefix, selected_slot=1),
            charge_work=_work_log(),
        )
    assert source == prefix.source
