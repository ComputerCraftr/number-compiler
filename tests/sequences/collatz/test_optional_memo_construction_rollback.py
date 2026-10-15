"""Failure-injection checks for lazily published Collatz query memos."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Sized

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.sequences.collatz.border_identity import ENTRY_421
from number_compiler.sequences.collatz.border_return_grammar import BorderReturnMacro
from number_compiler.sequences.collatz.boundary_macros import (
    BoundaryActionTemplateMemo,
    CollatzBoundaryMacro,
)
from number_compiler.sequences.collatz.innovation_port_moore import (
    InnovationTapeObservation,
)
from number_compiler.sequences.collatz.physical_images import (
    CollatzPhysicalImageWorkspace,
)
from tests.support.ledger_failures import assert_constructor_rollback


@pytest.mark.parametrize(
    ("owner_prefix", "modulus"),
    (
        ("collatz-boundary-macro-occurrences-", None),
        ("collatz-innovation-observations-", 49),
    ),
)
def test_failed_optional_memo_registration_retires_partial_owner(
    owner_prefix: str,
    modulus: int | None,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    initial_inventory = len(ledger.inventory())
    original = ledger.register_container
    registrations: dict[int, int] = {}

    def fail_after_store_creation(
        owner: int,
        container: Sized,
        *,
        node_count: Callable[[], int] | None = None,
        payloads: Callable[[], Iterable[object]] | None = None,
        roots: Callable[[], Iterable[ArenaHandle]] | None = None,
        evict: Callable[[], None] | None = None,
        composition_count: Callable[[], int] | None = None,
    ) -> None:
        name = ledger.inventory_owner(owner).name
        if name.startswith(owner_prefix):
            registrations[owner] = registrations.get(owner, 0) + 1
            if registrations[owner] == 2:
                raise RuntimeError("injected optional memo publication failure")
        original(
            owner,
            container,
            node_count=node_count,
            payloads=payloads,
            roots=roots,
            evict=evict,
            composition_count=composition_count,
        )

    monkeypatch.setattr(ledger, "register_container", fail_after_store_creation)
    with pytest.raises(RuntimeError, match="injected optional memo"):
        CollatzPhysicalImageWorkspace(
            ledger,
            2174,
            13,
            retain_chronology=False,
            include_innovation_tape=True,
            innovation_modulus=modulus,
        )

    assert len(registrations) == 1
    assert tuple(registrations.values()) == (2,)
    assert_constructor_rollback(ledger, initial_inventory)


def test_failed_boundary_template_memo_construction_can_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    initial_inventory = len(ledger.inventory())
    original = ledger.register_container
    registrations: dict[int, int] = {}

    def fail_after_store_creation(
        owner: int,
        container: Sized,
        *,
        node_count: Callable[[], int] | None = None,
        payloads: Callable[[], Iterable[object]] | None = None,
        roots: Callable[[], Iterable[ArenaHandle]] | None = None,
        evict: Callable[[], None] | None = None,
        composition_count: Callable[[], int] | None = None,
    ) -> None:
        if ledger.inventory_owner(owner).name.startswith(
            "collatz-boundary-action-templates-"
        ):
            registrations[owner] = registrations.get(owner, 0) + 1
            if registrations[owner] == 2:
                raise RuntimeError("injected template memo publication failure")
        original(
            owner,
            container,
            node_count=node_count,
            payloads=payloads,
            roots=roots,
            evict=evict,
            composition_count=composition_count,
        )

    memo = BoundaryActionTemplateMemo(ledger)
    monkeypatch.setattr(ledger, "register_container", fail_after_store_creation)
    with pytest.raises(RuntimeError, match="injected template memo"):
        memo.get(ENTRY_421, 2)

    assert len(registrations) == 1
    assert tuple(registrations.values()) == (2,)
    assert_constructor_rollback(ledger, initial_inventory)
    assert memo._templates is None

    monkeypatch.setattr(ledger, "register_container", original)
    try:
        action = memo.get(ENTRY_421, 2)
        assert action[0].steps > 0
    finally:
        memo.dispose()
    assert ledger.entries == ledger.nodes == 0


def _workspace_with_optional_memos() -> tuple[
    ResourceLedger,
    CollatzPhysicalImageWorkspace,
    OwnedMemo[str, CollatzBoundaryMacro | BorderReturnMacro],
    OwnedMemo[str, InnovationTapeObservation],
]:
    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(
        ledger,
        2174,
        13,
        retain_chronology=False,
        include_innovation_tape=True,
        innovation_modulus=49,
    )
    boundary = workspace._boundary_macro_memo
    innovation = workspace._innovation_observation_memo
    assert boundary is not None and innovation is not None
    return ledger, workspace, boundary, innovation


def test_workspace_cleanup_retains_failed_owner_for_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, workspace, boundary, innovation = _workspace_with_optional_memos()
    original = OwnedMemo.dispose
    failed = False

    def fail_boundary_once(memo: OwnedMemo[object, object]) -> None:
        nonlocal failed
        if memo is boundary and not failed:
            failed = True
            raise RuntimeError("injected boundary cleanup failure")
        original(memo)

    monkeypatch.setattr(OwnedMemo, "dispose", fail_boundary_once)
    with pytest.raises(RuntimeError, match="injected boundary cleanup"):
        workspace.dispose()

    assert failed
    assert workspace._closed
    assert workspace._boundary_macro_memo is boundary
    assert workspace._innovation_observation_memo is None
    assert ledger.inventory_owner(boundary.owner).entries > 0
    assert ledger.inventory_owner(innovation.owner).disposed

    monkeypatch.setattr(OwnedMemo, "dispose", original)
    workspace.dispose()
    assert workspace._boundary_macro_memo is None
    assert ledger.inventory_owner(boundary.owner).disposed
    assert ledger.entries == ledger.nodes == 0


def test_construction_rollback_attempts_all_cleanup_and_preserves_cause(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, workspace, boundary, innovation = _workspace_with_optional_memos()
    original = OwnedMemo.dispose
    events: list[str] = []

    def fail_both_memos(memo: OwnedMemo[object, object]) -> None:
        if memo is boundary:
            events.append("boundary")
            raise RuntimeError("boundary cleanup failed")
        if memo is innovation:
            events.append("innovation")
            raise ValueError("innovation cleanup failed")
        original(memo)

    monkeypatch.setattr(OwnedMemo, "dispose", fail_both_memos)
    construction_error = LookupError("original construction failure")
    try:
        try:
            raise construction_error
        except LookupError as active:
            with pytest.raises(
                ValueError, match="innovation cleanup failed"
            ) as failure:
                workspace._rollback_construction()
            assert failure.value.__cause__ is active

        assert events == ["boundary", "innovation"]
        boundary_failure = failure.value.__context__
        assert isinstance(boundary_failure, RuntimeError)
        assert str(boundary_failure) == "boundary cleanup failed"
        assert failure.value.__cause__ is construction_error
        assert workspace._closed
        assert workspace._boundary_macro_memo is boundary
        assert workspace._innovation_observation_memo is innovation
    finally:
        monkeypatch.setattr(OwnedMemo, "dispose", original)
        workspace.dispose()

    assert ledger.entries == ledger.nodes == 0
