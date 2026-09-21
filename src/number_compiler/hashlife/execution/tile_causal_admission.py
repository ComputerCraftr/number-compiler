"""Run-scoped deep admission of a causal temporal-action DAG."""

from __future__ import annotations

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.resources.causal_workspace import CausalTaskWorkspace
from number_compiler.resources.ledger import ResourceLedger


def admit_run_actions(
    adapter: PrimitiveTileKernelAdapter,
    tasks: CausalTaskWorkspace,
    ledger: ResourceLedger,
    action: FieldCellActionID,
) -> object:
    """Deeply validate every reachable action under one workspace lease."""
    if type(adapter._next_action) is not int or adapter._next_action < 1:
        raise ValueError("causal action authority has no admitted actions")
    token = tasks.begin_action_admission(action)
    visits = 0
    try:
        while tasks.action_pending:
            current = tasks.pop_action(token)
            if type(current) is not FieldCellActionID:
                raise TypeError("causal execution requires a field action ID")
            current.validate(
                adapter.owner, "field-cell-action", size=adapter._next_action
            )
            if tasks.action_is_admitted(token, current):
                continue
            visits += 1
            ledger.bump("tile_causal_action_admission_visits")
            adapter.validate_action(current)
            record = adapter._action_record(current)
            tasks.admit_action(token, current, record)
            if record.children is not None:
                tasks.push_action(token, record.children[0])
                tasks.push_action(token, record.children[1])
    except BaseException:
        tasks.clear_action_admission(token)
        raise
    return token


def admitted_wiring(
    adapter: PrimitiveTileKernelAdapter,
    tasks: CausalTaskWorkspace,
    token: object | None,
    action: FieldCellActionID,
) -> ResultWiring:
    """Obtain wiring through the live admission or the deep public boundary."""
    if token is None:
        return adapter.wiring(action)
    signature, _kernel, _record = tasks.admitted_action_metadata(token, adapter, action)
    return ResultWiring(signature)


def admitted_children(
    adapter: PrimitiveTileKernelAdapter,
    tasks: CausalTaskWorkspace,
    token: object | None,
    action: FieldCellActionID,
) -> tuple[FieldCellActionID, FieldCellActionID] | None:
    if token is None:
        return adapter.action_children(action)
    _signature, _kernel, record = tasks.admitted_action_metadata(token, adapter, action)
    return record.children


def admitted_kernel(
    adapter: PrimitiveTileKernelAdapter,
    tasks: CausalTaskWorkspace,
    token: object | None,
    action: FieldCellActionID,
) -> PrimitiveKernel:
    if token is None:
        return adapter.primitive_law(action)
    _signature, kernel, _record = tasks.admitted_action_metadata(token, adapter, action)
    return adapter.kernels.kernel(kernel)


def admitted_cocycle(
    adapter: PrimitiveTileKernelAdapter,
    tasks: CausalTaskWorkspace,
    token: object | None,
    action: FieldCellActionID,
) -> TemporalCocycle:
    if token is None:
        return adapter.action_cocycle(action)
    _signature, _kernel, record = tasks.admitted_action_metadata(token, adapter, action)
    return record.cocycle


__all__ = [
    "admit_run_actions",
    "admitted_children",
    "admitted_cocycle",
    "admitted_kernel",
    "admitted_wiring",
]
