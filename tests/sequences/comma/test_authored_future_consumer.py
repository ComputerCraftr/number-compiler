"""Consumer regressions over the authored FutureCID tables.

These tests deliberately install synthetic test admission for the exact
authored table bytes. That exercises the Python consumer boundary only; it is
not kernel evidence and must never be used to register a production artifact.
"""

from __future__ import annotations

import json
from collections.abc import Callable, Mapping
from dataclasses import replace
from importlib.resources.abc import Traversable
from importlib.util import find_spec
from pathlib import Path
from types import ModuleType
from typing import Never, Protocol, cast

import pytest

from number_compiler.api.cli import main
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageCandidate,
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.comma import future_provider
from number_compiler.sequences.comma import power as comma_power
from number_compiler.sequences.comma.action_arena import (
    CommaActionID,
    CommaActionRecord,
)
from number_compiler.sequences.comma.arithmetic import comma_children, decimal_sector
from number_compiler.sequences.comma.boundary_quotient import (
    PERIOD,
    BoundaryState,
    MacroTemplate,
    construct_macro,
)
from number_compiler.sequences.comma.boundary_receipt import (
    BoundaryPrefixCursor,
    BoundarySelectionReceiptID,
    CommaImagePayload,
)
from number_compiler.sequences.comma.carry_generator import BitsCharge, WorkCharge
from number_compiler.sequences.comma.future_authority import (
    SOURCE20_FIRST_FORK_INDEX,
    SOURCE20_FIRST_FORK_VALUE,
    SOURCE20_SELECTED_CHILD_INDEX,
)
from number_compiler.sequences.comma.occurrence import (
    BoundaryOccurrence,
    OccurrencePrefixReturn,
    OrderedMacroChildren,
)
from number_compiler.sequences.comma.semantic_branch import (
    FutureProvider,
    SemanticMacroChild,
    select_global_semantic_macro_child,
)
from tests.support.comma_future_provider_fixture import (
    authored_candidate_record,
    canonical_bytes,
    install_test_only_global_registry,
)
from tests.support.comma_source_image_payload import source_image_payload


class _CommaApply(Protocol):
    def __call__(
        self,
        node: CommaActionRecord,
        source: SourceImageView,
        *,
        boundary_template: MacroTemplate | None = None,
    ) -> SourceImageCandidate: ...


def _no_work(_amount: int) -> None:
    return None


def _record_provider_loads(monkeypatch: pytest.MonkeyPatch) -> list[Path]:
    loaded: list[Path] = []
    load_file = future_provider.SemanticFutureProviderStore.load_file

    def record_load(
        store: future_provider.SemanticFutureProviderStore,
        path: Path,
        *,
        charge_work: Callable[[int], None],
    ) -> future_provider.SemanticFutureProviderLease:
        loaded.append(Path(path))
        return load_file(store, path, charge_work=charge_work)

    monkeypatch.setattr(
        future_provider.SemanticFutureProviderStore,
        "load_file",
        record_load,
    )
    return loaded


def _provider(
    record: Mapping[str, object], request: pytest.FixtureRequest
) -> future_provider.SemanticFutureProviderLease:
    store = future_provider.SemanticFutureProviderStore(ResourceLedger())
    request.addfinalizer(store.close)
    return store.load_record(record, charge_work=_no_work)


def _next_boundary_child(
    source: BoundaryOccurrence,
    provider: FutureProvider,
) -> SemanticMacroChild:
    prefix = OccurrencePrefixReturn(source, construct_macro(source.state))
    assert prefix.outcome == "fork"
    ordered = prefix.ordered_literal_children()
    _boundary_children, literals = ordered.validated_parts()
    assert len(literals) == 2
    return select_global_semantic_macro_child(
        source,
        prefix,
        fork_value=prefix.terminal_value,
        ordered_literal_children=(literals[0], literals[1]),
        provider=provider,
        charge_work=_no_work,
    )


def _literal_window(value: int, steps: int) -> tuple[int, ...]:
    """Return a bounded literal prefix without replaying the powered macro."""
    current = value
    result = [current]
    for _ in range(steps):
        children = comma_children(current)
        assert len(children) == 1, "macro prefix crossed a fork before its endpoint"
        current = children[0]
        result.append(current)
    return tuple(result)


def _source20_first_child() -> BoundaryOccurrence:
    return BoundaryOccurrence(BoundaryState("N", 2, 10), 10)


def test_authored_provider_selects_two_later_forks_and_transports_exponents(
    monkeypatch: pytest.MonkeyPatch,
    request: pytest.FixtureRequest,
) -> None:
    record = authored_candidate_record()
    install_test_only_global_registry(monkeypatch, record)
    provider = _provider(record, request)
    source = _source20_first_child()
    visited: list[BoundaryOccurrence] = []
    expected_sources = (
        BoundaryOccurrence(BoundaryState("N", 2, 10), 10),
        BoundaryOccurrence(BoundaryState("N", 7, 12), 12),
    )
    expected_windows = (
        (
            19_999_999_999,
            20_000_000_091,
            20_000_000_103,
            20_000_000_135,
            20_000_000_187,
            20_000_000_259,
            20_000_000_351,
            20_000_000_363,
            20_000_000_395,
        ),
        (
            6_999_999_999_999,
            7_000_000_000_096,
            7_000_000_000_163,
            7_000_000_000_200,
            7_000_000_000_207,
            7_000_000_000_284,
            7_000_000_000_331,
            7_000_000_000_348,
            7_000_000_000_435,
        ),
    )
    expected_terminals = (6_999_999_999_963, 19_999_999_999_918)
    expected_terminal_children = (
        (6_999_999_999_999, 7_000_000_000_000),
        (19_999_999_999_999, 20_000_000_000_000),
    )

    expected_slots = (0, 1)
    expected_selected_literals = (6_999_999_999_999, 20_000_000_000_000)

    for (
        expected_source,
        expected_window,
        expected_terminal,
        expected_children,
        expected_slot,
        expected_literal,
    ) in zip(
        expected_sources,
        expected_windows,
        expected_terminals,
        expected_terminal_children,
        expected_slots,
        expected_selected_literals,
        strict=True,
    ):
        assert source == expected_source
        prefix = OccurrencePrefixReturn(source, construct_macro(source.state))
        assert prefix.outcome == "fork"
        assert _literal_window(source.value(), 8) == expected_window
        assert prefix.terminal_value == expected_terminal
        assert comma_children(prefix.terminal_value) == expected_children

        selected = _next_boundary_child(source, provider)
        slot = selected.selection.selected_slot
        assert slot == expected_slot
        assert expected_children[expected_slot] == expected_literal
        assert selected.literal_value == expected_literal
        assert selected.total_transition_count == prefix.transition_count + 1
        assert selected.weighted_action.weight.evaluate(source.exponent) == (
            selected.total_transition_count
        )
        assert selected.target.exponent == source.exponent + prefix.width_delta
        assert selected.target.value() == expected_children[slot]
        assert selected.occurrence.kind == ("N" if slot == 0 else "Z")
        visited.append(source)
        source = selected.target

    assert tuple(visited) == expected_sources

    translated_from = next(
        (
            occurrence
            for occurrence in visited
            if construct_macro(occurrence.state).weight.numerator_scale != 0
        ),
        None,
    )
    assert translated_from is not None, "selected path has no exponent-sensitive return"
    translated = BoundaryOccurrence(
        translated_from.state,
        translated_from.exponent + PERIOD,
    )
    original_selection = provider.select_unique_unranked_child(
        translated_from.state, charge_work=_no_work
    )
    shifted_selection = provider.select_unique_unranked_child(
        translated.state, charge_work=_no_work
    )
    assert original_selection.source_class == shifted_selection.source_class
    assert (
        original_selection.ordered_child_classes
        == shifted_selection.ordered_child_classes
    )
    assert original_selection.selected_slot == shifted_selection.selected_slot

    original_result = _next_boundary_child(translated_from, provider)
    shifted_result = _next_boundary_child(translated, provider)
    assert original_result.literal_value != shifted_result.literal_value
    assert original_result.target.state == shifted_result.target.state
    assert shifted_result.target.exponent == (original_result.target.exponent + PERIOD)
    assert (
        original_result.total_transition_count != shifted_result.total_transition_count
    )


def test_authenticated_global_return_crosses_the_selected_fork(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    request: pytest.FixtureRequest,
) -> None:
    record = authored_candidate_record()
    install_test_only_global_registry(monkeypatch, record)
    provider = _provider(record, request)
    selected = _next_boundary_child(_source20_first_child(), provider)
    target_index = SOURCE20_SELECTED_CHILD_INDEX + selected.total_transition_count

    artifact_directory = tmp_path / "kernels"
    artifact_directory.mkdir()
    artifact = artifact_directory / future_provider.FUTURE_PROVIDER_ASSET
    artifact.write_bytes(canonical_bytes(record))

    with comma_power.CommaTerm(target_index) as term:
        stage_provider = cast(
            Callable[[Path], None],
            object.__getattribute__(term, "_stage_global_future_provider_artifact"),
        )
        stage_provider(artifact)
        term.require_certified_public_prefix()

        assert term.materialize() == selected.target.value()
        assert object.__getattribute__(term, "_boundary_occurrence") == selected.target
        assert len(term.audit_snapshot().boundary_receipts) == 1
        assert term.ledger.counters["comma_global_branch_action_applications"] == 2
        receipt_count = len(term.audit_snapshot().boundary_receipts)
        assert term.materialize() == selected.target.value()
        assert term.ledger.counters["comma_global_branch_action_applications"] == 2
        assert len(term.audit_snapshot().boundary_receipts) == receipt_count


@pytest.mark.validation
def test_authored_candidate_drives_public_cli_after_the_source20_edge(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    request: pytest.FixtureRequest,
) -> None:
    record = authored_candidate_record()
    digest = install_test_only_global_registry(monkeypatch, record)
    parsed = future_provider.parse_future_candidate(record, charge_work=_no_work)
    assert parsed.artifact_sha256 == digest
    provider = _provider(record, request)
    first_selected = _next_boundary_child(_source20_first_child(), provider)
    second_selected = _next_boundary_child(first_selected.target, provider)
    target_index = (
        SOURCE20_SELECTED_CHILD_INDEX
        + first_selected.total_transition_count
        + second_selected.total_transition_count
    )
    assert first_selected.selection.selected_slot == 0
    assert first_selected.literal_value == 6_999_999_999_999
    assert second_selected.selection.selected_slot == 1
    assert second_selected.literal_value == 20_000_000_000_000
    expected = 20_000_000_000_000

    artifact_directory = tmp_path / "kernels"
    artifact_directory.mkdir()
    artifact = artifact_directory / future_provider.FUTURE_PROVIDER_ASSET
    artifact.write_bytes(canonical_bytes(record))

    def local_package_files(_package: str | ModuleType) -> Traversable:
        return tmp_path

    monkeypatch.setattr(comma_power, "files", local_package_files)

    staged_artifacts = _record_provider_loads(monkeypatch)

    selected_sources: list[BoundaryState] = []
    select = future_provider.SemanticFutureProvider.select_unique_unranked_child

    def record_selection(
        self: future_provider.SemanticFutureProvider,
        state: BoundaryState,
        *,
        charge_work: Callable[[int], None],
    ) -> future_provider.UnrankedChildSelection:
        selected_sources.append(state)
        return select(self, state, charge_work=charge_work)

    monkeypatch.setattr(
        future_provider.SemanticFutureProvider,
        "select_unique_unranked_child",
        record_selection,
    )

    ordered_sources: list[BoundaryState] = []
    ordered_children = OccurrencePrefixReturn.ordered_literal_children

    def record_ordered_children(
        self: OccurrencePrefixReturn,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> OrderedMacroChildren:
        ordered_sources.append(self.source.state)
        return ordered_children(
            self,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )

    monkeypatch.setattr(
        OccurrencePrefixReturn,
        "ordered_literal_children",
        record_ordered_children,
    )

    assert find_spec("number_compiler.sequences.comma.forest_verifier") is None
    assert main(["a367620", "--nth", str(target_index), "--format", "json"]) == 0
    packet = json.loads(capsys.readouterr().out)
    assert packet["index"] == target_index
    assert packet["value"] == str(expected)
    expected_sources = [BoundaryState("N", 2, 10), BoundaryState("N", 7, 12)]
    assert selected_sources == expected_sources
    assert ordered_sources == expected_sources
    assert staged_artifacts == [artifact]


def test_future_publication_poison_and_stale_provider_fail_before_term_commit(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = authored_candidate_record()
    digest = install_test_only_global_registry(monkeypatch, record)
    artifact_directory = tmp_path / "kernels"
    artifact_directory.mkdir()
    artifact = artifact_directory / future_provider.FUTURE_PROVIDER_ASSET
    artifact.write_bytes(canonical_bytes(record))

    with comma_power.CommaTerm(1) as term:
        stage_provider = cast(
            Callable[[Path], None],
            object.__getattribute__(term, "_stage_global_future_provider_artifact"),
        )
        stage_provider(artifact)
        term.index = SOURCE20_FIRST_FORK_INDEX
        assert term.materialize() == SOURCE20_FIRST_FORK_VALUE
        publish = cast(
            Callable[[CommaActionID], int],
            object.__getattribute__(term, "_publish"),
        )

        def term_state() -> tuple[object, ...]:
            core = term.scheduler.source_image_core()
            cache_snapshot = core.audit_snapshot()
            return (
                object.__getattribute__(term, "_source"),
                object.__getattribute__(term, "_current_index"),
                object.__getattribute__(term, "_current_value"),
                object.__getattribute__(term, "_boundary_occurrence"),
                object.__getattribute__(term, "_boundary_occurrence_owner"),
                len(term.audit_snapshot().occurrences),
                len(term.audit_snapshot().boundary_receipts),
                len(cache_snapshot.nodes),
                len(cache_snapshot.applications),
                len(cache_snapshot.relative),
            )

        original_apply = cast(
            _CommaApply, object.__getattribute__(term.adapter, "_apply")
        )

        def reject_before_commit(
            action: CommaActionID,
            expected_kind: str,
            poison: str,
            source_state: BoundaryState | None = None,
        ) -> None:
            core = term.scheduler.source_image_core()
            core.origin(
                term.adapter,
                object.__getattribute__(term, "_source"),
            )
            before = term_state()

            def poisoned_apply(
                node: CommaActionRecord,
                image_source: SourceImageView,
                *,
                boundary_template: MacroTemplate | None = None,
            ) -> SourceImageCandidate:
                candidate = original_apply(
                    node,
                    image_source,
                    boundary_template=boundary_template,
                )
                if node.kind != expected_kind:
                    return candidate
                payload = candidate.payload
                assert type(payload) is CommaImagePayload
                cursor = payload.boundary_cursor
                assert type(cursor) is BoundaryPrefixCursor
                if poison == "missing-cursor":
                    return replace(
                        candidate,
                        payload=replace(payload, boundary_cursor=None),
                    )
                if poison == "wrong-state":
                    return replace(
                        candidate,
                        payload=replace(
                            payload,
                            boundary_cursor=replace(
                                cursor,
                                state=BoundaryState("Z", 2, 10),
                            ),
                        ),
                    )
                if poison == "partial-cursor":
                    return replace(
                        candidate,
                        payload=replace(
                            payload,
                            boundary_cursor=replace(cursor, transitions=1),
                        ),
                    )
                if poison == "wrong-target":
                    assert source_state is not None
                    template = term.arena.boundary_template(source_state)
                    other_target = next(
                        child
                        for child in template.ordered_children
                        if child != cursor.state
                    )
                    return replace(
                        candidate,
                        payload=replace(
                            payload,
                            boundary_cursor=replace(cursor, state=other_target),
                        ),
                    )
                if poison == "alternate-valid-target":
                    assert source_state is not None
                    template = term.arena.boundary_template(source_state)
                    receipt_id = cursor.selection_receipt
                    assert receipt_id is not None
                    receipt = term.resolve_boundary_selection_receipt(receipt_id)
                    other_target = template.ordered_children[
                        1 - receipt.selection.selected_slot
                    ]
                    other_value = other_target.value(cursor.exponent)
                    sector = decimal_sector(other_value)
                    return replace(
                        candidate,
                        payload=replace(
                            payload,
                            value=other_value,
                            boundary_cursor=replace(cursor, state=other_target),
                        ),
                        boundary_ports=(
                            sector.leading,
                            sector.digit,
                            sector.headroom,
                        ),
                    )
                if poison == "mutated-receipt-slot":
                    receipt_id = cursor.selection_receipt
                    assert receipt_id is not None
                    receipt = term.resolve_boundary_selection_receipt(receipt_id)
                    object.__setattr__(
                        receipt.selection,
                        "selected_slot",
                        1 - receipt.selection.selected_slot,
                    )
                    return candidate
                return replace(candidate, extent=candidate.extent + 1)

            with monkeypatch.context() as patcher:
                patcher.setattr(term.adapter, "_apply", poisoned_apply)
                with pytest.raises(ValueError):
                    publish(action)
            assert term_state() == before

        source20_action = term.arena.source20_first_child(digest)
        for poison in (
            "missing-cursor",
            "wrong-state",
            "partial-cursor",
            "wrong-extent",
        ):
            reject_before_commit(
                source20_action,
                "source20-first-child",
                poison,
            )

        publish(source20_action)
        source_occurrence = object.__getattribute__(term, "_boundary_occurrence")
        assert type(source_occurrence) is BoundaryOccurrence
        global_action = term.arena.global_boundary_return(
            source_occurrence.state,
            digest,
        )
        for poison in (
            "missing-cursor",
            "wrong-target",
            "alternate-valid-target",
            "mutated-receipt-slot",
            "wrong-extent",
        ):
            reject_before_commit(
                global_action,
                "global-boundary-return",
                poison,
                source_occurrence.state,
            )

        # Admit a good image into the scheduler cache, then stale the provider
        # lease without clearing the term's source occurrence. The publication
        # boundary must reject authority before consulting this warm entry.
        source = object.__getattribute__(term, "_source")
        cached_payload = source_image_payload(term, source, global_action)
        assert type(cached_payload.boundary_cursor) is BoundaryPrefixCursor
        receipt_id = cached_payload.boundary_cursor.selection_receipt
        assert type(receipt_id) is BoundarySelectionReceiptID
        before = term_state()

        def reject_cache_entry(*_args: object, **_kwargs: object) -> None:
            pytest.fail("stale provider reached the warm source-image cache")

        provider_store = object.__getattribute__(term, "_future_provider_store")
        assert type(provider_store) is future_provider.SemanticFutureProviderStore
        provider_store.close()
        with monkeypatch.context() as cache_patch:
            cache_patch.setattr(
                type(term.scheduler), "source_image", reject_cache_entry
            )
            with pytest.raises(RuntimeError, match="stale"):
                publish(global_action)
            assert term_state() == before
        object.__setattr__(term, "_future_provider_store", None)

        # A failed close keeps the completed receipt in its owner for retry;
        # once close completes, it clears the cache and invalidates the handle.
        receipt_count = len(term.audit_snapshot().boundary_receipts)

        def fail_close_once(_scheduler: object) -> None:
            raise RuntimeError("injected image disposal failure")

        with monkeypatch.context() as close_patch:
            close_patch.setattr(
                type(term.scheduler), "dispose_source_images", fail_close_once
            )
            with pytest.raises(RuntimeError, match="injected image disposal failure"):
                term.close()
            assert len(term.audit_snapshot().boundary_receipts) == receipt_count
            with pytest.raises(ValueError, match="closing or closed"):
                term.resolve_boundary_selection_receipt(receipt_id)

        term.close()
        closed_snapshot = term.audit_snapshot()
        assert closed_snapshot.stores_owned
        assert not closed_snapshot.occurrences
        assert not closed_snapshot.occurrence_seals
        assert not closed_snapshot.boundary_receipts
        assert not closed_snapshot.boundary_receipt_seals
        with pytest.raises(ValueError, match="closing or closed|foreign or stale"):
            term.resolve_boundary_selection_receipt(receipt_id)
        from number_compiler.resources.payload_audit import audit_registered_payloads
        from number_compiler.sequences.comma.payload_audit import audit_comma_term

        owner_names = {entry.owner: entry.name for entry in term.ledger.inventory()}
        comma_contribution = audit_comma_term(term.ledger, term)
        comma_rejections = tuple(
            (
                owner_names.get(entry.owner, f"owner-{entry.owner}"),
                type(entry.value).__qualname__,
                id(entry.value),
            )
            for entry in comma_contribution.invalid
        )
        assert not comma_contribution.invalid, comma_rejections

        contract_audit = term.ledger.collect_payload_contract_audit()
        _, comma_contract_invalid = contract_audit.family("comma", ledger=term.ledger)

        def named_contract_entries(
            entries: frozenset[tuple[int, int]],
        ) -> tuple[tuple[str, int], ...]:
            return tuple(
                sorted(
                    (
                        owner_names.get(owner, f"owner-{owner}"),
                        identity,
                    )
                    for owner, identity in entries
                )
            )

        assert not comma_contract_invalid, named_contract_entries(
            comma_contract_invalid
        )
        assert audit_registered_payloads(term.ledger).forbidden_future_payloads == 0
        term.close()


def test_global_provider_warm_reuse_is_term_owned(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = authored_candidate_record()
    digest = install_test_only_global_registry(monkeypatch, record)
    artifact_directory = tmp_path / "kernels"
    artifact_directory.mkdir()
    artifact = artifact_directory / future_provider.FUTURE_PROVIDER_ASSET
    artifact.write_bytes(canonical_bytes(record))

    def local_package_files(_package: str | ModuleType) -> Traversable:
        return tmp_path

    monkeypatch.setattr(comma_power, "files", local_package_files)
    loaded = _record_provider_loads(monkeypatch)
    with comma_power.CommaTerm(1) as term:
        first = term.global_future_provider_for_prefix_admission()
        assert first is not None and first.artifact_sha256 == digest

        def reject_warm_package_read(_package: str | ModuleType) -> Never:
            raise AssertionError("warm provider reopened package resources")

        monkeypatch.setattr(comma_power, "files", reject_warm_package_read)
        second = term.global_future_provider_for_prefix_admission()
        assert second is first
        term.require_certified_public_prefix()
        assert term.materialize() == 20
    assert loaded == [artifact]
