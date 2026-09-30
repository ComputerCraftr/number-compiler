"""Parent-first concrete directed transfers over canonical primitive tiles."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.hashlife.tiles.tile_directed_transfer_memo import (
    DirectedTransferRequest,
    _DirectedTransferAdmission,
    _prepare_admission,
    _prepare_canonical_admission,
    _prepare_directed_transfer_with_admission,
    lookup_prepared_directed_transfer,
    publish_prepared_directed_transfer,
)
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tile_result_records import (
    DirectedTransferKey,
    PoweredInterfaceKey,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileArena, TileID
from number_compiler.resources.causal_workspace import (
    CausalFrameStack,
    CausalValueStack,
)
from number_compiler.resources.ledger import ResourceLedger


class _Host(Protocol):
    tiles: TileArena
    ledger: ResourceLedger

    def _require_results(self) -> CompletedResultArena: ...

    def _observe(
        self, interface: LocalInterfaceID, channel: str, ports: tuple[int, ...]
    ) -> int: ...


@dataclass(slots=True)
class _Frame:
    tile: TileID
    incoming: int
    stage: int = 0
    midpoint: int = 0
    request: DirectedTransferRequest | None = None

    @property
    def args(self) -> tuple[object, ...]:
        return (self.tile, self.incoming)

    @property
    def saved(self) -> tuple[object, ...]:
        return () if self.request is None else (self.midpoint, self.request)


def directed_transfer(
    host: _Host,
    action: FieldCellActionID,
    tile: TileID,
    side: int,
    incoming: int,
    wiring: ResultWiring,
) -> int:
    """Apply one primitive transfer, caching concrete canonical parents first."""
    results = host._require_results()
    frames, values = _directed_workspace(results)
    admission = _prepare_admission(results, action, wiring, side)
    try:
        return _run_directed(
            host,
            results,
            frames,
            values,
            tile,
            incoming,
            admission,
        )
    finally:
        frames.clear()
        values.clear()


def canonical_directed_transfer(
    host: _Host,
    action: FieldCellActionID,
    tile: TileID,
    side: int,
    incoming: int,
    *,
    _action_admission: object | None = None,
) -> int:
    """Apply canonical primitive wiring after one action validation."""
    results = host._require_results()
    frames, values = _directed_workspace(results)
    admission = _prepare_canonical_admission(
        results,
        action,
        side,
        action_admission=_action_admission,
    )
    ports = list(admission.initial_ports)
    ports[side] = incoming
    results._validate_ports(admission.wiring.signature, (ports[0], ports[1]))
    try:
        return _run_directed(
            host,
            results,
            frames,
            values,
            tile,
            incoming,
            admission,
        )
    finally:
        frames.clear()
        values.clear()


def _run_directed(
    host: _Host,
    results: CompletedResultArena,
    frames: CausalFrameStack,
    values: CausalValueStack,
    tile: TileID,
    incoming: int,
    admission: _DirectedTransferAdmission,
) -> int:
    action, side, wiring = admission.action, admission.side, admission.wiring
    law = admission.kernel
    frames.append(_Frame(tile, incoming))
    while frames:
        old_peak = host.ledger.counters.get("tile_directed_transfer_workspace_peak", 0)
        if len(frames) + len(values) > old_peak:
            host.ledger.bump(
                "tile_directed_transfer_workspace_peak",
                len(frames) + len(values) - old_peak,
            )
        frame = frames.pop()
        key = DirectedTransferKey(
            action,
            frame.tile,
            side,
            frame.incoming,
            wiring,
        )
        if frame.stage == 0:
            frame.request = _prepare_directed_transfer_with_admission(
                results,
                key,
                admission,
            )
            found = lookup_prepared_directed_transfer(results, frame.request)
            if found is not None:
                values.append(found)
                continue
            interface_key = PoweredInterfaceKey(action, frame.tile, wiring)
            # An existing parametric interface already covers every incoming
            # state. Probe it before specializing this request through children.
            # The membership probe avoids repeating full interface admission on
            # misses; hits still use the validating public lookup.
            if interface_key in results._memo:
                interface = results.lookup_interface(interface_key)
                if interface is None:
                    raise AssertionError("directed interface disappeared during lookup")
                ports = list(admission.initial_ports)
                ports[side] = frame.incoming
                outgoing = host._observe(
                    interface,
                    "boundary_right" if side else "boundary_left",
                    (ports[0], ports[1]),
                )
                values.append(
                    publish_prepared_directed_transfer(results, frame.request, outgoing)
                )
                host.ledger.bump("tile_directed_transfer_interface_hits")
                continue
            node = host.tiles.resolve(frame.tile)
            if not node.level:
                if node.symbol is None:
                    raise ValueError("directed transfer reached a malformed leaf")
                outgoing = law.advance(
                    BoundarySide(side),
                    frame.incoming,
                    node.symbol,
                )
                values.append(
                    publish_prepared_directed_transfer(
                        results,
                        frame.request,
                        outgoing,
                    )
                )
                host.ledger.bump("tile_directed_transfer_leaf_evaluations")
                continue
            if node.left is None or node.right is None:
                raise ValueError("directed transfer reached a malformed parent")
            first = node.left if side == 0 else node.right
            frame.stage = 1
            frames.extend((frame, _Frame(first, frame.incoming)))
            continue
        node = host.tiles.resolve(frame.tile)
        if node.left is None or node.right is None:
            raise ValueError("directed transfer parent lost its children")
        if frame.stage == 1:
            frame.midpoint = values.pop()
            frame.stage = 2
            second = node.right if side == 0 else node.left
            frames.extend((frame, _Frame(second, frame.midpoint)))
            continue
        outgoing = values.pop()
        if frame.request is None:
            raise AssertionError("directed transfer parent lost its request")
        values.append(
            publish_prepared_directed_transfer(results, frame.request, outgoing)
        )
        host.ledger.bump("tile_directed_transfer_parent_evaluations")
    if len(values) != 1:
        raise AssertionError("directed transfer scheduler returned another shape")
    return values.pop()


__all__ = ["canonical_directed_transfer", "directed_transfer"]


def _directed_workspace(
    results: CompletedResultArena,
) -> tuple[CausalFrameStack, CausalValueStack]:
    tasks = results._causal_tasks
    if tasks is None:
        raise ValueError("directed transfer requires its scheduler task workspace")
    frames, values = tasks.directed_frames, tasks.directed_values
    if len(frames) or len(values):
        raise ValueError("directed transfer auxiliary workspace is already active")
    return frames, values
