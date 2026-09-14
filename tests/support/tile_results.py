"""Tile results with one canonical implementation owner."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    DiamondQuotientArena,
    MacroComponents,
    MacroInterface,
)
from number_compiler.hashlife.tiles.tile_ports import (
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    CompletedResult,
    PoweredResultKey,
)
from number_compiler.hashlife.tiles.tile_results import (
    CompletedResultArena,
)
from number_compiler.hashlife.tiles.tiles import (
    TileAlphabet,
    TileAlphabetID,
    TileArena,
    TileID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerList

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tiles import TileLease


class _ActionAuthority:
    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        self.owner = ArenaToken("test-tile-result-actions")
        store_owner = ledger.register(
            f"test-tile-result-actions-{len(ledger.inventory())}",
            "test_semantic_authority",
        )
        self._actions: LedgerList[None] = ledger.make_list(store_owner)
        ledger.reserve(store_owner, entries=1, nodes=1)
        self._actions.append(None)
        ledger.register_execution_root(self)
        self.signature_id: PortSignatureID | None = None
        self.fused_enabled = True
        self.heterogeneous_fused_wiring = False

    @property
    def action(self) -> FieldCellActionID:
        return FieldCellActionID(self.owner, "field-cell-action", 0)

    def validate_action(self, action: FieldCellActionID) -> None:
        action.validate(self.owner, "field-cell-action", size=len(self._actions))

    def signature(self, action: FieldCellActionID) -> PortSignatureID:
        self.validate_action(action)
        if self.signature_id is None:
            raise RuntimeError("test action signature was not installed")
        return self.signature_id

    def validate_fused_action(self, action: FieldCellActionID) -> None:
        self.validate_action(action)
        if not self.fused_enabled:
            raise ValueError("test action is not an admitted fused pair")

    def validate_fused_wiring(
        self,
        action: FieldCellActionID,
        producer: ResultWiring,
        result: ResultWiring,
    ) -> None:
        self.validate_fused_action(action)
        if producer != result and not self.heterogeneous_fused_wiring:
            raise ValueError("test action does not admit this fused wiring")


def _setup(
    max_entries: int | None = None,
    *,
    authority_type: type[_ActionAuthority] = _ActionAuthority,
) -> tuple[
    ResourceLedger,
    _ActionAuthority,
    TileArena,
    CompletedResultArena,
    TileLease,
    TileLease,
    PoweredResultKey,
    CompletedResult,
]:
    ledger = ResourceLedger(max_cache_entries=max_entries)
    functions = SemanticFunctionArena(ledger)
    interfaces = DiamondQuotientArena(functions)
    port = FinitePort(PortVariable(0, 0, "carry", 0), 3)
    signature = FunctionSignature((port,), BOOL)
    zero = functions.atom(signature, 0)
    one = functions.atom(signature, 1)
    declared = interfaces.intern_interface(
        MacroInterface(
            SemanticIdentity("tile-results-test-v1", ("finite",)),
            (port,),
            (BOOL,) * len(COMPONENT_ROLES),
            one,
            phase_count=2,
        )
    )
    outgoing = interfaces.intern(
        declared,
        MacroComponents(*(zero for _ in COMPONENT_ROLES)),
    )
    actions = authority_type(ledger)
    actions.signature_id = declared
    tiles = TileArena(ledger)
    alphabet = tiles.intern_alphabet(TileAlphabet(3, 2, 2, 2, "binary", "v1"))
    results = CompletedResultArena(
        tiles,
        interfaces,
        action_authority=actions,
        validate_action=actions.validate_action,
        signature_for=actions.signature,
    )
    input_lease = tiles.leaf(alphabet, 1)
    output_lease = tiles.leaf(alphabet, 0)
    key = PoweredResultKey(
        actions.action,
        input_lease.tile,
        (1,),
        ResultWiring(declared, 0, 1),
    )
    result = CompletedResult(
        output_lease.tile,
        outgoing,
        (2,),
        7,
        3,
        -2,
        -1,
        1,
    )
    return ledger, actions, tiles, results, input_lease, output_lease, key, result


class _ChangingAlphabetAuthority(_ActionAuthority):
    """A -> B -> C admission; the result store must not collapse these domains."""

    def __init__(self, ledger: ResourceLedger) -> None:
        super().__init__(ledger)
        ledger.reserve(self._actions.owner, entries=2, nodes=2)
        self._actions.extend((None, None))
        self.tiles: TileArena | None = None
        self.domains: tuple[TileAlphabetID, ...] = ()

    def action_children(
        self, action: FieldCellActionID
    ) -> None | tuple[FieldCellActionID, ...]:
        self.validate_action(action)
        if action.local_id == 0:
            return tuple(FieldCellActionID(self.owner, action.kind, n) for n in (1, 2))
        return None

    def validate_input(self, action: FieldCellActionID, tile: TileID) -> None:
        self.validate_action(action)
        expected = self.domains[int(action.local_id == 2)]
        assert self.tiles is not None
        if self.tiles.resolve(tile).alphabet != expected:
            raise ValueError("wrong child input domain")

    def validate_output(self, action: FieldCellActionID, tile: TileID) -> None:
        self.validate_action(action)
        expected = self.domains[1 if action.local_id == 1 else 2]
        assert self.tiles is not None
        if self.tiles.resolve(tile).alphabet != expected:
            raise ValueError("wrong child output domain")
