"""Independent bounded references for the comma source cylinder."""

from __future__ import annotations

from typing import cast

import pytest

from number_compiler.arithmetic.fields.consumer_pullback import PrefixSafety
from number_compiler.hashlife.execution.source_bound_images import SourceImageDemand
from number_compiler.sequences.comma import certificates
from number_compiler.sequences.comma.arithmetic import (
    comma_children,
    cycle_transfer,
    decimal_sector,
    safe_complete_cycles,
)
from number_compiler.sequences.comma.power import (
    FIRST_FORK_INDEX,
    FIRST_FORK_VALUE,
    CommaImagePayload,
    CommaOccurrenceID,
    CommaSource,
    CommaTerm,
    UnresolvedCommaBranch,
)


def _literal_children(value: int) -> tuple[int, ...]:
    digit = int(str(value)[-1])
    out: list[int] = []
    for candidate_digit in range(1, 10):
        child = value + 10 * digit + candidate_digit
        if int(str(child)[0]) == candidate_digit:
            out.append(child)
    return tuple(out)


def _literal_term(index: int) -> int:
    value = 20
    for _ in range(index - 1):
        children = _literal_children(value)
        assert len(children) == 1
        value = children[0]
    return value


@pytest.mark.parametrize("index", (1, 2, 3, 4, 19, 200, 201, 1000, 20000))
def test_powered_endpoint_matches_independent_literal_prefix(index: int) -> None:
    term = CommaTerm(index)
    if index <= 1000:
        assert term.materialize() == _literal_term(index)
    else:
        # The public 20,000-row OEIS b-file ends with this value. The runtime
        # obtains it through source-bound cycles rather than a table lookup.
        assert term.materialize() == 1_039_404
    assert term.ledger.counters.get("comma_represented_transitions", 0) == index - 1


@pytest.mark.parametrize("leading", range(1, 10))
@pytest.mark.parametrize("digit", range(10))
def test_phase_cycle_is_a_guarded_exact_composition(leading: int, digit: int) -> None:
    source = leading * 100_000 + 100 + digit
    transfer = cycle_transfer(leading, digit)
    safety = PrefixSafety(-transfer.displacement, -transfer.maximum_guard)
    assert safety.repeat(3) == PrefixSafety(
        -3 * transfer.displacement,
        -transfer.maximum_guard - 2 * transfer.displacement,
    )
    assert safe_complete_cycles(source, transfer, 3 * transfer.period) >= 3
    sector = decimal_sector(source)
    assert safety.first_failing_copy(sector.boundary - 1 - source, 3) is None
    value = source
    for _ in range(3 * transfer.period):
        children = _literal_children(value)
        assert len(children) == 1
        value = children[0]
    assert value == source + 3 * transfer.displacement
    assert decimal_sector(value).leading == leading
    assert comma_children(source) == _literal_children(source)


def test_mixed_chronological_actions_keep_executable_children() -> None:
    term = CommaTerm(201)
    source = CommaSource(20)
    steps = term.arena.compose(term.arena.step(2), term.arena.step(4))
    assert term.arena.node(steps).before is not None
    image = term.scheduler.source_image(term.adapter, source, steps)
    assert (
        term.scheduler.source_projection(
            term.adapter, image, SourceImageDemand("value")
        ).value
        == 46
    )

    term.materialize()
    entered = term._source
    cycle = term.arena.one_cycle(1, 7)
    cycle_then_step = term.arena.compose(cycle, term.arena.step(1))
    after = term.scheduler.source_image(term.adapter, entered, cycle_then_step)
    assert (
        term.scheduler.source_projection(
            term.adapter, after, SourceImageDemand("value")
        ).value
        == 10_588
    )
    step_then_cycle = term.arena.compose(term.arena.step(1), term.arena.one_cycle(1, 8))
    after = term.scheduler.source_image(term.adapter, entered, step_then_cycle)
    assert (
        term.scheduler.source_projection(
            term.adapter, after, SourceImageDemand("value")
        ).value
        == 10_588
    )


def test_first_fork_is_not_silently_selected() -> None:
    assert FIRST_FORK_INDEX == 412_987_859
    assert CommaTerm(FIRST_FORK_INDEX).materialize() == FIRST_FORK_VALUE
    with pytest.raises(UnresolvedCommaBranch):
        CommaTerm(FIRST_FORK_INDEX + 1).materialize()
    assert comma_children(FIRST_FORK_VALUE) == (
        19_999_999_999,
        20_000_000_000,
    )


def test_fork_requires_source_bound_certificate_at_discovery_and_admission(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[dict[str, object]] = []

    def checked_choice(**binding: object) -> int:
        calls.append(binding)
        assert binding["source_index"] == FIRST_FORK_INDEX
        assert binding["source_value"] == FIRST_FORK_VALUE
        assert binding["children"] == (19_999_999_999, 20_000_000_000)
        assert binding["certificate_version"] == "test-checked-fork-v1"
        return 19_999_999_999

    monkeypatch.setattr(
        certificates, "require_selected_child", checked_choice, raising=False
    )
    term = CommaTerm(
        FIRST_FORK_INDEX + 1,
        certificate_version="test-checked-fork-v1",
        shared_cache=False,
    )
    assert term.materialize() == 19_999_999_999
    assert len(calls) == 2
    assert calls[0]["ledger"] is term.ledger
    assert calls[0]["memo"] is term.certificate_memo
    assert calls[1]["memo"] is term.certificate_memo
    assert calls[1]["max_work"] == term.max_work
    assert all(call["shared_cache"] is False for call in calls)

    source = CommaTerm(FIRST_FORK_INDEX, certificate_version="test-checked-fork-v1")
    source.materialize()
    with pytest.raises(ValueError, match="selected another child"):
        source.scheduler.source_image(
            source.adapter, source._source, source.arena.step(2)
        )


def test_comma_shared_cache_selection_must_be_boolean() -> None:
    with pytest.raises(ValueError, match="shared-cache selection"):
        CommaTerm(1, shared_cache=cast(bool, 1))


def test_equal_phase_does_not_authorize_a_cycle_across_the_fork() -> None:
    term = CommaTerm(FIRST_FORK_INDEX)
    term.materialize()
    action = term.arena.one_cycle(1, 8)
    with pytest.raises(ValueError, match="unadmitted seam"):
        term.scheduler.source_image(term.adapter, term._source, action)


def test_partial_term_index_inside_phase_cycle_is_exact() -> None:
    assert CommaTerm(201).materialize() == 10_057
    assert CommaTerm(204).materialize() == 10_300
    assert CommaTerm(205).materialize() == 10_301
    whole = CommaTerm(211)
    assert whole.materialize() == 10_517
    assert whole.ledger.counters.get("comma_phase_cycles", 0) >= 1


def test_binary_cycle_parenthesizations_share_an_exact_action() -> None:
    term = CommaTerm(201)
    term.materialize()
    one = term.arena.one_cycle(1, 7)
    left = term.arena.compose(term.arena.compose(one, one), one)
    right = term.arena.compose(one, term.arena.compose(one, one))
    assert left == right
    image = term.scheduler.source_image(term.adapter, term._source, left)
    assert (
        term.scheduler.source_projection(
            term.adapter, image, SourceImageDemand("value")
        ).value
        == 10_057 + 3 * 460
    )


def test_refused_work_keeps_last_admitted_source() -> None:
    term = CommaTerm(1_000, max_work=100)
    with pytest.raises(ValueError, match="--max-comma-work"):
        term.materialize()
    if term._occurrences:
        assert isinstance(term._source, CommaOccurrenceID)
        assert term._source.local_id == len(term._occurrences) - 1
    assert term._current_index > 1
    assert (
        term._current_index - 1 == term.ledger.counters["comma_represented_transitions"]
    )
    term.max_work = term.arena.max_work = 100_000
    assert term.materialize() == _literal_term(1_000)
    assert term.ledger.counters["comma_represented_transitions"] == 999


def test_foreign_or_altered_occurrence_cannot_become_a_provider() -> None:
    first = CommaTerm(100)
    second = CommaTerm(101)
    first.materialize()
    second.materialize()
    with pytest.raises(ValueError):
        second.adapter.validate_source(first._source)
    assert isinstance(second._source, CommaOccurrenceID)
    second._occurrences[second._source.local_id] = first._occurrences[-1]
    with pytest.raises(ValueError, match="publication was altered"):
        second.adapter.validate_source(second._source)


def test_forged_numerical_types_do_not_authenticate() -> None:
    term = CommaTerm(2)
    with pytest.raises(ValueError, match="authenticated root"):
        term.adapter.validate_source(CommaSource(cast(int, 20.0)))
    with pytest.raises(ValueError, match="endpoint coordinates"):
        term.adapter.validate_payload(CommaImagePayload(cast(int, 20.0), 1))
    with pytest.raises(ValueError, match="endpoint coordinates"):
        term.adapter.validate_payload(CommaImagePayload(20, cast(int, 1.0)))
    with pytest.raises(ValueError, match="endpoint coordinates"):
        term.adapter.validate_payload(CommaImagePayload(cast(int, True), 1))


def test_certificate_binding_prevents_cross_version_image_reuse() -> None:
    first = CommaTerm(201, certificate_version="checked-prefix-alpha")
    second = CommaTerm(201, certificate_version="checked-prefix-beta")
    assert first.materialize() == second.materialize()
    with pytest.raises(ValueError, match="authenticated root"):
        second.adapter.validate_source(
            CommaSource(20, certificate_version="checked-prefix-alpha")
        )
    with pytest.raises(ValueError, match="endpoint coordinates"):
        second.adapter.validate_payload(
            CommaImagePayload(10_057, 201, "checked-prefix-alpha")
        )
    with pytest.raises(ValueError):
        second.adapter.validate_action(first.arena.identity)


def test_explicit_zero_resource_limit_is_never_ignored() -> None:
    with pytest.raises(ValueError, match="--max-comma-states"):
        CommaTerm(2, max_states=0)
    with pytest.raises(ValueError, match="--max-comma-work"):
        CommaTerm(2, max_work=0)
    with pytest.raises(ValueError, match="context node budget"):
        CommaTerm(2, max_context_nodes=0)
    with pytest.raises(ValueError, match="cache entry budget"):
        CommaTerm(2, max_cache_entries=0)


def test_certificate_and_arithmetic_share_one_work_budget() -> None:
    term = CommaTerm(2, max_work=2)
    term.ledger.bump("comma_certificate_work")
    with pytest.raises(ValueError, match="max-comma-work"):
        term.materialize()
    assert term.ledger.counters["comma_work"] == 1
    assert term.ledger.counters["comma_budget_refusals"] > 0


def test_discovery_phase_transfer_is_charged_before_evaluation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.comma import action_arena

    term = CommaTerm(2, max_work=2)

    def forbidden(*_args: object) -> None:
        pytest.fail("phase transfer evaluated after its budget admission failed")

    monkeypatch.setattr(action_arena, "cycle_transfer", forbidden)
    with pytest.raises(ValueError, match="max-comma-work"):
        term.materialize()
    assert term.ledger.counters.get("comma_transfer_constructions", 0) == 0


def test_phase_transfer_work_includes_discovery_and_validation() -> None:
    term = CommaTerm(4)
    assert term.materialize() == 107
    assert term.ledger.counters["comma_transfer_constructions"] >= 3
    assert term.ledger.counters["comma_cycle_rule_evaluations"] >= 3
    assert term.ledger.counters["comma_transfer_phase_terms"] == 0


def test_certificate_budget_refusal_is_not_a_failed_certificate() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from number_compiler.resources.temporal_diagnostics import (
        collect_temporal_diagnostics_snapshot,
    )
    from number_compiler.sequences.comma.certificates import require_certified_index

    term = CommaTerm(1, max_work=1)
    with pytest.raises(BlockContextBudgetExceeded, match="certificate work budget"):
        require_certified_index(1, term.ledger, term.max_work)
    report = collect_temporal_diagnostics_snapshot(term.ledger)
    assert report.comma.certificate_budget_refusals == 1
    assert report.comma.budget_refusals == 1
    assert "comma_certificate_failed_work" not in term.ledger.counters
