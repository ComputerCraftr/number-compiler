"""Consumer regressions over the authored FutureCID tables.

These tests deliberately install synthetic test admission for the exact
authored table bytes. That exercises the Python consumer boundary only; it is
not kernel evidence and must never be used to register a production artifact.
"""

from __future__ import annotations

import json
from collections.abc import Callable, Mapping
from pathlib import Path
from types import MappingProxyType, ModuleType

import pytest

from devtools.paths import isabelle_root
from devtools.verification.comma_semantic_future_artifact import (
    runtime_candidate_record_from_isabelle_data,
)
from number_compiler.api.cli import main
from number_compiler.sequences.comma import (
    certificates,
    future_authority,
    future_provider,
)
from number_compiler.sequences.comma import power as comma_power
from number_compiler.sequences.comma.arithmetic import comma_children
from number_compiler.sequences.comma.boundary_quotient import (
    PERIOD,
    BoundaryState,
    construct_macro,
)
from number_compiler.sequences.comma.future_authority import (
    SOURCE20_SELECTED_CHILD_INDEX,
)
from number_compiler.sequences.comma.occurrence import (
    BoundaryOccurrence,
    OccurrencePrefixReturn,
)
from number_compiler.sequences.comma.semantic_branch import (
    SemanticMacroChild,
    select_global_semantic_macro_child,
)
from tests.support.comma_future_provider_fixture import canonical_bytes


def _no_work(_amount: int) -> None:
    return None


def _authored_candidate() -> dict[str, object]:
    source = (
        isabelle_root()
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Candidate_Data.thy"
    )
    return runtime_candidate_record_from_isabelle_data(
        source.read_text(encoding="utf-8"), source
    )


def _install_test_only_global_registry(
    monkeypatch: pytest.MonkeyPatch,
    record: Mapping[str, object],
) -> str:
    """Exercise the global consumer with explicitly synthetic admission."""
    parsed = future_provider.parse_future_candidate(record, charge_work=_no_work)
    admission = future_authority.KernelInstanceAdmission(
        artifact_sha256=parsed.artifact_sha256,
        instance_id=future_authority.GLOBAL_RELEASE_SESSION_ID,
        theorem_id=future_authority.GLOBAL_RELEASE_THEOREM_ID,
        contract_id=future_authority.GLOBAL_RELEASE_CONTRACT_ID,
        claims=future_authority.GLOBAL_RELEASE_CLAIMS,
        scope=future_authority.KERNEL_RELEASE_SCOPE,
    )
    monkeypatch.setattr(
        future_provider,
        "_ADMITTED_KERNEL_INSTANCES",
        MappingProxyType({parsed.artifact_sha256: admission}),
    )
    # The production callable is a partial bound to the immutable empty
    # release registry at import time. Rebind only this test process to the
    # synthetic fixture registry; production authority remains unchanged.
    monkeypatch.setattr(
        future_provider,
        "registered_global_release_artifact_sha256",
        lambda: parsed.artifact_sha256,
    )
    return parsed.artifact_sha256


def _provider(record: Mapping[str, object]) -> future_provider.SemanticFutureProvider:
    return future_provider.SemanticFutureProvider.from_record(
        record, charge_work=_no_work
    )


def _next_boundary_child(
    source: BoundaryOccurrence,
    provider: future_provider.SemanticFutureProvider,
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
) -> None:
    record = _authored_candidate()
    _install_test_only_global_registry(monkeypatch, record)
    provider = _provider(record)
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

    for expected_source, expected_window, expected_terminal, expected_children in zip(
        expected_sources,
        expected_windows,
        expected_terminals,
        expected_terminal_children,
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
        assert selected.literal_value == expected_children[slot]
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


@pytest.mark.validation
def test_authored_candidate_drives_public_cli_after_the_source20_edge(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    record = _authored_candidate()
    digest = _install_test_only_global_registry(monkeypatch, record)
    parsed = future_provider.parse_future_candidate(record, charge_work=_no_work)
    assert parsed.artifact_sha256 == digest
    provider = _provider(record)
    first_selected = _next_boundary_child(_source20_first_child(), provider)
    second_selected = _next_boundary_child(first_selected.target, provider)
    target_index = (
        SOURCE20_SELECTED_CHILD_INDEX
        + first_selected.total_transition_count
        + second_selected.total_transition_count
    )
    expected = second_selected.literal_value

    artifact_directory = tmp_path / "kernels"
    artifact_directory.mkdir()
    artifact = artifact_directory / future_provider.FUTURE_PROVIDER_ASSET
    artifact.write_bytes(canonical_bytes(record))

    def local_package_files(_package: str | ModuleType) -> Path:
        return tmp_path

    monkeypatch.setattr(comma_power, "files", local_package_files)

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

    def forbid_finite_admission(*_args: object, **_kwargs: object) -> None:
        pytest.fail("global future CLI route fell back to finite forest admission")

    monkeypatch.setattr(certificates, "_verify", forbid_finite_admission)
    assert main(["a367620", "--nth", str(target_index), "--format", "json"]) == 0
    packet = json.loads(capsys.readouterr().out)
    assert packet["index"] == target_index
    assert packet["value"] == str(expected)
    assert BoundaryState("N", 2, 10) in selected_sources
    assert BoundaryState("N", 7, 12) in selected_sources
