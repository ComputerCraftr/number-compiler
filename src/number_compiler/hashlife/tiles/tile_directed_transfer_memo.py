"""Atomic primitive directed-transfer bindings in the shared result memo."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, cast

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.finite_function_types import SemanticNode
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tile_result_records import DirectedTransferKey
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileAlphabet, TileID
from number_compiler.resources.result_cache_kinds import (
    record_unattributed_post_eviction_miss,
)

_REQUEST_SEAL = object()
_ADMISSION_SEAL = object()
_ACTION_VALIDATED_SEAL = object()

_KeySnapshot = tuple[
    int,
    int,
    str,
    int,
    int,
    str,
    int,
    int,
    int,
    int,
    str,
    int,
    int,
    int,
]


def _snapshot_key(key: DirectedTransferKey) -> _KeySnapshot:
    """Copy every security-relevant key scalar without retaining its handles."""
    if type(key) is not DirectedTransferKey:
        raise TypeError("directed transfer has another key sort")
    action = key.action
    tile = key.input
    wiring = key.wiring
    if type(action) is not FieldCellActionID:
        raise TypeError("directed transfer requires a scoped primitive action")
    if type(tile) is not TileID:
        raise TypeError("directed transfer requires a scoped input tile")
    if type(wiring) is not ResultWiring:
        raise TypeError("directed transfer requires normalized wiring")
    signature = wiring.signature
    if type(signature) is not PortSignatureID:
        raise TypeError("directed transfer requires a scoped port signature")
    handles = (action, tile, signature)
    if any(
        type(handle.owner) is not ArenaToken
        or type(handle.kind) is not str
        or not handle.kind
        or type(handle.local_id) is not int
        or handle.local_id < 0
        for handle in handles
    ):
        raise ValueError("directed transfer contains a malformed scoped handle")
    if type(key.side) is not int or type(key.incoming_state) is not int:
        raise TypeError("directed transfer direction and state require exact integers")
    if type(wiring.orientation) is not int or type(wiring.phase) is not int:
        raise TypeError("directed transfer wiring requires exact integers")
    return (
        id(key),
        id(action.owner),
        action.kind,
        action.local_id,
        id(tile.owner),
        tile.kind,
        tile.local_id,
        key.side,
        key.incoming_state,
        id(signature.owner),
        signature.kind,
        signature.local_id,
        wiring.orientation,
        wiring.phase,
    )


@dataclass(frozen=True, slots=True)
class DirectedTransferRequest:
    """A transient, once-validated primitive transfer descriptor."""

    key: DirectedTransferKey
    exit_cardinality: int
    _arena: CompletedResultArena
    _key_snapshot: _KeySnapshot
    _validated_exit_cardinality: int
    _seal: object

    def __post_init__(self) -> None:
        if self._seal is not _REQUEST_SEAL:
            raise TypeError("directed transfer requests require their validator")
        if id(self.key) != self._key_snapshot[0]:
            raise ValueError("directed transfer request key changed after validation")
        if _snapshot_key(self.key) != self._key_snapshot:
            raise ValueError("directed transfer request key metadata changed")
        if (
            type(self.exit_cardinality) is not int
            or self.exit_cardinality != self._validated_exit_cardinality
        ):
            raise ValueError(
                "directed transfer request cardinality changed after validation",
            )


@dataclass(frozen=True, slots=True)
class _DirectedTransferAdmission:
    """Transient primitive metadata validated once for one directed scan."""

    action: FieldCellActionID
    wiring: ResultWiring
    side: int
    cardinality: int
    own: PortVariable
    admissible: SemanticNode
    expected_alphabet: TileAlphabet
    kernel: PrimitiveKernel
    initial_ports: tuple[int, int]
    arena: CompletedResultArena
    snapshot: tuple[object, ...]
    seal: object

    def __post_init__(self) -> None:
        if self.seal is not _ADMISSION_SEAL:
            raise TypeError("directed transfer admission requires its validator")
        if type(self.kernel) is not PrimitiveKernel:
            raise TypeError("directed transfer admission has another kernel sort")
        if (
            type(self.initial_ports) is not tuple
            or len(self.initial_ports) != 2
            or any(type(value) is not int for value in self.initial_ports)
        ):
            raise TypeError("directed transfer admission has invalid initial ports")
        if self.snapshot != _admission_snapshot(self.action, self.wiring, self.side):
            raise ValueError("directed transfer admission metadata changed")


def _authority(results: CompletedResultArena) -> Any:
    if type(results) is not CompletedResultArena:
        raise TypeError("directed transfers require the shared result arena")
    return cast(Any, results.action_authority)


def _admission_snapshot(
    action: FieldCellActionID,
    wiring: ResultWiring,
    side: int,
) -> tuple[object, ...]:
    if type(action) is not FieldCellActionID:
        raise TypeError("directed transfer requires a scoped primitive action")
    if type(wiring) is not ResultWiring:
        raise TypeError("directed transfer requires normalized wiring")
    signature = wiring.signature
    if type(signature) is not PortSignatureID:
        raise TypeError("directed transfer requires a scoped port signature")
    for handle in (action, signature):
        if (
            type(handle.owner) is not ArenaToken
            or type(handle.kind) is not str
            or not handle.kind
            or type(handle.local_id) is not int
            or handle.local_id < 0
        ):
            raise ValueError("directed transfer admission contains a malformed handle")
    if (
        type(wiring.orientation) is not int
        or type(wiring.phase) is not int
        or type(side) is not int
    ):
        raise TypeError("directed transfer admission requires exact integers")
    return (
        id(action),
        id(action.owner),
        action.kind,
        action.local_id,
        id(wiring),
        id(wiring.signature.owner),
        wiring.signature.kind,
        wiring.signature.local_id,
        wiring.orientation,
        wiring.phase,
        side,
    )


def _prepare_admission(
    results: CompletedResultArena,
    action: FieldCellActionID,
    wiring: ResultWiring,
    side: int,
    *,
    action_validation: object | None = None,
) -> _DirectedTransferAdmission:
    """Audit immutable action metadata once for one non-reentrant scan."""
    if type(side) is not int:
        raise TypeError("directed transfer side requires an exact integer")
    if side not in (0, 1):
        raise ValueError("directed transfer side lies outside its two directions")
    authority = _authority(results)
    if action_validation is not _ACTION_VALIDATED_SEAL:
        results._validate_action(action)
    record = authority._actions[action.local_id]
    if record.children is not None:
        raise ValueError("directed transfer binding requires a primitive action")
    if type(wiring) is not ResultWiring:
        raise TypeError("directed transfer requires normalized wiring")
    wiring.__post_init__()
    if wiring.signature != record.signature:
        raise ValueError("directed transfer signature differs from its action")
    declaration = results.interfaces.interface(record.signature)
    if (
        wiring.orientation not in declaration.orientations
        or wiring.phase >= declaration.phase_count
    ):
        raise ValueError("directed transfer wiring lies outside its signature")
    if len(declaration.inputs) != 2:
        raise ValueError("directed transfer signature requires two finite ports")
    kernel = authority.kernels.kernel(record.kernel)
    expected = TileAlphabet(
        kernel.blank + 1,
        kernel.blank,
        kernel.base,
        max(1, kernel.blank.bit_length()),
        "unsigned-radix-cell-with-explicit-blank",
        "canonical-tile-alphabet-v1",
    )
    domain = declaration.inputs[side]
    return _DirectedTransferAdmission(
        action,
        wiring,
        side,
        domain.cardinality,
        domain.variable,
        results.interfaces.functions.resolve(declaration.admissible),
        expected,
        kernel,
        (
            kernel.initial(BoundarySide.LEFT),
            kernel.initial(BoundarySide.RIGHT),
        ),
        results,
        _admission_snapshot(action, wiring, side),
        _ADMISSION_SEAL,
    )


def _prepare_canonical_admission(
    results: CompletedResultArena,
    action: FieldCellActionID,
    side: int,
) -> _DirectedTransferAdmission:
    """Validate an action once and derive its canonical primitive wiring."""
    authority = _authority(results)
    results._validate_action(action)
    record = authority._actions[action.local_id]
    return _prepare_admission(
        results,
        action,
        ResultWiring(record.signature),
        side,
        action_validation=_ACTION_VALIDATED_SEAL,
    )


def _validate_admission(
    results: CompletedResultArena,
    admission: _DirectedTransferAdmission,
) -> None:
    if type(admission) is not _DirectedTransferAdmission:
        raise TypeError("directed transfer has another admission sort")
    admission.__post_init__()
    if admission.arena is not results:
        raise ValueError("directed transfer admission belongs to another result arena")


def _validate_key(
    results: CompletedResultArena,
    key: DirectedTransferKey,
    admission: _DirectedTransferAdmission | None = None,
) -> int:
    if type(key) is not DirectedTransferKey:
        raise TypeError("directed transfer has another key sort")
    if type(key.side) is not int:
        raise TypeError("directed transfer side requires an exact integer")
    if key.side not in (0, 1):
        raise ValueError("directed transfer side lies outside its two directions")
    if type(key.incoming_state) is not int:
        raise TypeError("directed transfer state requires an exact integer")
    checked = (
        _prepare_admission(results, key.action, key.wiring, key.side)
        if admission is None
        else admission
    )
    _validate_admission(results, checked)
    if (
        key.action != checked.action
        or key.wiring != checked.wiring
        or key.side != checked.side
    ):
        raise ValueError("directed transfer key differs from its validated admission")
    cardinality = checked.cardinality
    if not 0 <= key.incoming_state < cardinality:
        raise ValueError("directed transfer state lies outside its finite state sort")
    if type(key.input) is not TileID:
        raise TypeError("directed transfer requires a scoped input tile")
    node = results.tiles.resolve(key.input)
    if results.tiles.alphabet(node.alphabet) != checked.expected_alphabet:
        raise ValueError("directed transfer tile has another alphabet interpretation")
    # Existentially quantify the opposite port over the reduced admissibility
    # DAG.  Enumerating that numeric domain is unnecessary and is impossible
    # for symbolic 64-bit remainder ports.  The incoming side stays fixed;
    # decision branches owned by any other port remain free.
    pending = [checked.admissible]
    visited: set[int] = set()
    admitted = False
    while pending:
        cursor = pending.pop()
        identity = id(cursor)
        if identity in visited:
            continue
        visited.add(identity)
        results.ledger.bump("tile_directed_transfer_validation_visits")
        terminal = cursor.terminal
        if terminal is not None:
            if terminal.kind == "atom" and terminal.value == 1:
                admitted = True
                break
            continue
        variable = cursor.variable
        if variable is None:
            raise AssertionError("admissibility node omitted its decision")
        base = PortVariable(variable.time, variable.side, variable.role, 0)
        if base == checked.own:
            child = (
                cursor.high if (key.incoming_state >> variable.bit) & 1 else cursor.low
            )
            pending.append(results.interfaces.functions.nodes[child])
        else:
            pending.extend(
                (
                    results.interfaces.functions.nodes[cursor.low],
                    results.interfaces.functions.nodes[cursor.high],
                )
            )
    if not admitted:
        raise ValueError("directed transfer state has no admissible opposite port")
    results.ledger.bump("tile_directed_transfer_validation_requests")
    return cardinality


def prepare_directed_transfer(
    results: CompletedResultArena,
    key: DirectedTransferKey,
) -> DirectedTransferRequest:
    """Validate one request once for a lookup followed by optional publication."""
    cardinality = _validate_key(results, key)
    return DirectedTransferRequest(
        key,
        cardinality,
        results,
        _snapshot_key(key),
        cardinality,
        _REQUEST_SEAL,
    )


def _prepare_directed_transfer_with_admission(
    results: CompletedResultArena,
    key: DirectedTransferKey,
    admission: _DirectedTransferAdmission,
) -> DirectedTransferRequest:
    cardinality = _validate_key(results, key, admission)
    return DirectedTransferRequest(
        key,
        cardinality,
        results,
        _snapshot_key(key),
        cardinality,
        _REQUEST_SEAL,
    )


def _validate_request(
    results: CompletedResultArena,
    request: DirectedTransferRequest,
) -> None:
    if type(results) is not CompletedResultArena:
        raise TypeError("directed transfers require the shared result arena")
    if type(request) is not DirectedTransferRequest:
        raise TypeError("directed transfer has another request sort")
    request.__post_init__()
    if request._arena is not results:
        raise ValueError("directed transfer request belongs to another result arena")
    # Prepared requests are transient validation capabilities.  Tile identities
    # can retire while a caller holds one, so liveness remains a use-time check.
    results.tiles.resolve(request.key.input)


def _validate_exit(
    request: DirectedTransferRequest,
    outgoing: int,
) -> None:
    if type(outgoing) is not int:
        raise TypeError("directed transfer exit requires an exact integer")
    if not 0 <= outgoing < request.exit_cardinality:
        raise ValueError("directed transfer exit lies outside its finite state sort")


def lookup_prepared_directed_transfer(
    results: CompletedResultArena,
    request: DirectedTransferRequest,
) -> int | None:
    """Probe a validated request without repeating primitive admission."""
    _validate_request(results, request)
    found = results._memo.get(request.key)
    results.ledger.bump("tile_directed_transfer_requests")
    if found is None:
        record_unattributed_post_eviction_miss(results.ledger, "interface")
        return None
    if type(found) is not int:
        raise TypeError("directed transfer memo contains another value sort")
    _validate_exit(request, found)
    results.ledger.bump("tile_directed_transfer_early_hits")
    return found


def lookup_directed_transfer(
    results: CompletedResultArena,
    key: DirectedTransferKey,
) -> int | None:
    """Probe one canonical primitive transfer before descending spatially."""
    return lookup_prepared_directed_transfer(
        results,
        prepare_directed_transfer(results, key),
    )


def publish_prepared_directed_transfer(
    results: CompletedResultArena,
    request: DirectedTransferRequest,
    outgoing: int,
) -> int:
    """Publish a validated request without repeating primitive admission."""
    _validate_request(results, request)
    _validate_exit(request, outgoing)
    key = request.key
    results.ledger.bump("tile_directed_transfer_publication_requests")
    found = results._memo.get(key)
    if found is not None:
        if type(found) is not int:
            raise TypeError("directed transfer memo contains another value sort")
        _validate_exit(request, found)
        if found != outgoing:
            raise ValueError("directed transfer already has another exact exit")
        results.ledger.bump("tile_directed_transfer_late_duplicates")
        return found
    referenced = results._tiles_for(key, outgoing)
    reverse_entries = results._index_entries(referenced)
    reservations = (
        (results._memo_owner, 1, 0),
        (results._reverse_owner, reverse_entries, 0),
    )
    results.ledger.reserve_many(reservations)
    reverse_snapshot = results._reverse_snapshot(referenced, key)
    try:
        results._memo[key] = outgoing
        for tile in referenced:
            results._add_membership(tile, key)
    except BaseException:
        results._memo.pop(key, None)
        results._restore_reverse(reverse_snapshot)
        for owner, entries, nodes in reservations:
            results.ledger.release(owner, entries, nodes)
        raise
    results.ledger.bump("tile_directed_transfer_publications")
    return outgoing


def publish_directed_transfer(
    results: CompletedResultArena,
    key: DirectedTransferKey,
    outgoing: int,
) -> int:
    """Publish an exact finite exit with atomic memo/reverse-index accounting."""
    return publish_prepared_directed_transfer(
        results,
        prepare_directed_transfer(results, key),
        outgoing,
    )


__all__ = [
    "lookup_directed_transfer",
    "publish_directed_transfer",
]
