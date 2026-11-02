"""Collatz root morphology consumes the scheduler's existing run quotient."""

from collections.abc import Callable
from copy import copy
from typing import cast

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.temporal_source_morphism import (
    CollatzRootFiber,
    PointedCollatzSource,
)


def test_detailed_scheduler_publishes_carrier_without_recompiling(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = PoweredCollatzTerm(27, 16, shared_cache=False)
    term.prepare_joint_cocycle()
    observation = term.accumulator(97)

    def fail_if_recompiled(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("root morphism recompiled the temporal quotient")

    monkeypatch.setattr(
        "number_compiler.sequences.collatz.temporal_run_quotient.compile_collatz_temporal_run_quotient",
        fail_if_recompiled,
    )
    try:
        root = term.true_root_morphism()
        assert observation.physical_ticks == root.ticks == 16
        assert root.first.value == term.seed
        assert root.last.value == term.materialize(max_bits=1024)
        assert root.odd_ticks + root.division_ticks == root.ticks
        assert root.physical_f5.apply(root.first.value) == root.last.value % 5
        repeated = term.true_root_morphism()
        assert repeated == root and repeated is not root
        root.validate()
        audit = audit_registered_payloads(term.resource_ledger)
        assert audit.forbidden_future_payloads == 0
        assert audit.unbounded_future_integers == 0
        assert audit.unknown_payloads == 0
    finally:
        workspace = term.audit_snapshot().workspace
        if workspace is not None:
            workspace.dispose()
    # The root record owns exact scalar/action authority; it does not retain a
    # lookup into the disposed image workspace.
    root.validate()
    repeated.validate()


def test_root_issuance_rejects_shallow_copies() -> None:
    owner = PointedCollatzSource.issue(27, 16, ledger=ResourceLedger())
    term = PoweredCollatzTerm(27, 16, shared_cache=False)
    term.prepare_joint_cocycle()
    term.accumulator(97)
    try:
        root = term.true_root_morphism()
        with pytest.raises(ValueError, match="unchanged factory result"):
            copy(owner).verify_issued()
        with pytest.raises(ValueError, match="lost issued authority"):
            copy(root).validate()
    finally:
        workspace = term.audit_snapshot().workspace
        if workspace is not None:
            workspace.dispose()


def test_tampered_scheduler_root_port_is_rejected() -> None:
    term = PoweredCollatzTerm(27, 16, shared_cache=False)
    term.prepare_joint_cocycle()
    term.accumulator(97)
    workspace = term.audit_snapshot().workspace
    assert workspace is not None
    try:
        core = workspace.scheduler.source_image_core()
        binding = core.view(workspace.root_image).binding
        object.__setattr__(binding, "boundary_ports", ())
        with pytest.raises(ValueError, match="publication record was altered"):
            term.true_root_morphism()
    finally:
        workspace.dispose()


def test_morphism_from_another_scheduler_owner_is_not_a_valid_midpoint() -> None:
    first = PoweredCollatzTerm(27, 16, shared_cache=False)
    foreign = PoweredCollatzTerm(27, 16, shared_cache=False)
    first.prepare_joint_cocycle()
    foreign.prepare_joint_cocycle()
    first.accumulator(97)
    foreign.accumulator(97)
    first_workspace = first.audit_snapshot().workspace
    foreign_workspace = foreign.audit_snapshot().workspace
    assert first_workspace is not None and foreign_workspace is not None
    try:
        first_root = first.true_root_morphism()
        foreign_root = foreign.true_root_morphism()
        with pytest.raises(ValueError, match="true-root adjacency"):
            first_root.then(foreign_root)
    finally:
        first_workspace.dispose()
        foreign_workspace.dispose()


def test_root_morphism_is_unavailable_without_detailed_demand() -> None:
    term = PoweredCollatzTerm(27, 16, shared_cache=False)

    with pytest.raises(ValueError, match="prepare the joint-cocycle detail"):
        term.true_root_morphism()


def test_root_fiber_large_radix_position_returns_zero_before_powering() -> None:
    fiber = CollatzRootFiber.of(123)
    assert fiber.digit_at(10, 10**100) == 0


@pytest.mark.parametrize("cleanup", ("_rollback_construction", "dispose"))
def test_joint_snapshot_is_released_with_workspace(cleanup: str) -> None:
    term = PoweredCollatzTerm(27, 16, shared_cache=False)
    term.prepare_joint_cocycle()
    term.accumulator(97)
    workspace = term.audit_snapshot().workspace
    assert workspace is not None
    assert not workspace.closed
    if cleanup == "_rollback_construction":
        rollback = cast(
            Callable[[], None],
            object.__getattribute__(workspace, "_rollback_construction"),
        )
        rollback()
    else:
        workspace.dispose()
    assert workspace.closed
