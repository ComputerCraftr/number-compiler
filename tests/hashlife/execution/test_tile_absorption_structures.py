"""Structured boundary composition used by arbitrary-depth tile absorption."""

from dataclasses import dataclass
from itertools import product
from typing import Literal

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_macro_composer import (
    HigherSpatialMacroComposer,
    SourceBoundHigherMacro,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpressionID,
)
from number_compiler.hashlife.execution.recursive_outputs import (
    RecursiveCoordinateMorphismArena,
)
from number_compiler.hashlife.execution.tile_absorption import (
    HigherBoundaryTransfer,
    HigherSpatialWiring,
    StructuredBoundaryTransfer,
    apply_endomorphism,
    boundary_endomorphism,
    boundary_transfer,
    compose_higher_spatial_transfers,
    compose_spatial_transfers,
    higher_boundary_transfer,
)
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    DiamondQuotientArena,
    MacroComponents,
    MacroInterface,
)
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructureID,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.support.reverse_higher_runtime import _fixture


@dataclass
class _HigherSchema:
    ledger: ResourceLedger

    def __post_init__(self) -> None:
        self.owner = ArenaToken("tile-absorption-actions")
        self.primitive = self._handle(0)
        self.p2 = self._handle(1)
        self.p4 = self._handle(2)

    def _handle(self, local_id: int) -> FieldCellActionID:
        return FieldCellActionID(self.owner, "field-cell-action", local_id)

    def validate_action(self, action: FieldCellActionID) -> None:
        action.validate(self.owner, "field-cell-action", size=3)

    def children(
        self,
        action: FieldCellActionID,
    ) -> None | tuple[FieldCellActionID, FieldCellActionID]:
        self.validate_action(action)
        if action == self.p2:
            return self.primitive, self.primitive
        if action == self.p4:
            return self.p2, self.p2
        return None

    def kind(
        self,
        action: FieldCellActionID,
    ) -> Literal["identity", "primitive", "compose"]:
        self.validate_action(action)
        return "primitive" if action == self.primitive else "compose"

    def alphabet(self, action: FieldCellActionID) -> tuple[int, int]:
        self.validate_action(action)
        return 2, 2

    def state_count(self, action: FieldCellActionID, side: int) -> int:
        self.validate_action(action)
        return 2

    def initial(self, action: FieldCellActionID, side: int) -> int:
        self.validate_action(action)
        return 0

    def step(
        self,
        action: FieldCellActionID,
        side: int,
        state: int,
        symbol: int,
    ) -> int:
        self.validate_action(action)
        return state ^ symbol ^ side

    def emit(
        self,
        action: FieldCellActionID,
        left: int,
        symbol: int,
        right: int,
    ) -> int:
        self.validate_action(action)
        return left ^ symbol ^ right


def _setup() -> tuple[StructureArena, FinitePort, FinitePort]:
    structures = StructureArena(BitFunctionArena(ResourceLedger()))
    left = FinitePort(PortVariable(0, 0, "left-state", 0), 2)
    right = FinitePort(PortVariable(0, 1, "right-state", 0), 2)
    return structures, left, right


def _transition(
    structures: StructureArena,
    port: FinitePort,
    *,
    flip: bool,
) -> StructureID:
    state = AtomSort(port.variable.role, port.cardinality)
    value = structures.bits.variable((port,), port, state)
    if flip:
        zero = structures.bits.constant(FunctionSignature((port,), state), 0)
        one = structures.bits.constant(FunctionSignature((port,), state), 1)
        value = structures.bits.select(value, zero, one)
    return boundary_endomorphism(structures, port, value)


def _cell(
    structures: StructureArena,
    left: FinitePort,
    right: FinitePort,
    left_flip: bool,
    right_flip: bool,
) -> StructuredBoundaryTransfer:
    return boundary_transfer(
        structures,
        _transition(structures, left, flip=left_flip),
        _transition(structures, right, flip=right_flip),
        left,
        right,
    )


def test_four_cell_spatial_transfer_matches_direct_two_sided_scan() -> None:
    structures, left, right = _setup()
    cells = (
        _cell(structures, left, right, False, True),
        _cell(structures, left, right, True, True),
        _cell(structures, left, right, False, False),
        _cell(structures, left, right, True, False),
    )
    two_left = compose_spatial_transfers(structures, cells[0], cells[1], left, right)
    two_right = compose_spatial_transfers(structures, cells[2], cells[3], left, right)
    four_cells = compose_spatial_transfers(
        structures,
        two_left,
        two_right,
        left,
        right,
    )

    for left_state, right_state in product(range(2), repeat=2):
        expected_left = left_state
        for flip in (False, True, False, True):
            expected_left ^= int(flip)
        expected_right = right_state
        for flip in reversed((True, True, False, False)):
            expected_right ^= int(flip)
        assert (
            apply_endomorphism(
                structures,
                four_cells.left,
                left,
                left_state,
            )
            == expected_left
        )
        assert (
            apply_endomorphism(
                structures,
                four_cells.right,
                right,
                right_state,
            )
            == expected_right
        )


def test_equivalent_spatial_derivations_share_structured_ids() -> None:
    structures, left, right = _setup()
    a = _cell(structures, left, right, False, True)
    b = _cell(structures, left, right, True, False)
    c = _cell(structures, left, right, True, True)
    left_grouped = compose_spatial_transfers(
        structures,
        compose_spatial_transfers(structures, a, b, left, right),
        c,
        left,
        right,
    )
    right_grouped = compose_spatial_transfers(
        structures,
        a,
        compose_spatial_transfers(structures, b, c, left, right),
        left,
        right,
    )
    assert left_grouped == right_grouped


def test_function_valued_boundary_pair_publishes_as_one_complete_quotient() -> None:
    structures, left, right = _setup()
    a = _cell(structures, left, right, False, True)
    b = _cell(structures, left, right, True, False)
    two_cells = compose_spatial_transfers(structures, a, b, left, right)
    four_cells = compose_spatial_transfers(
        structures,
        two_cells,
        two_cells,
        left,
        right,
    )
    functions = structures.functions
    quotients = DiamondQuotientArena(functions, structures=structures)
    boolean = structures.atom(structures.bits.constant(FunctionSignature((), BOOL), 0))
    admitted = functions.atom(FunctionSignature((), BOOL), 1)
    outputs = (
        structures.resolve(four_cells.left).signature.output,
        structures.resolve(four_cells.right).signature.output,
        *((BOOL,) * (len(COMPONENT_ROLES) - 2)),
    )
    signature = quotients.intern_interface(
        MacroInterface(
            SemanticIdentity("tile-absorption-boundary-v1", ("two-sided",)),
            (),
            outputs,
            admitted,
        )
    )
    components = MacroComponents(
        four_cells.left,
        four_cells.right,
        *(boolean for _ in range(len(COMPONENT_ROLES) - 2)),
    )
    first = quotients.intern(signature, components)
    second = quotients.intern(signature, components)
    assert first == second
    record = quotients.resolve(first)
    assert record.components.boundary_left == four_cells.left
    assert record.components.boundary_right == four_cells.right


def test_boundary_composition_rejects_foreign_handles_before_mutation() -> None:
    structures, left, right = _setup()
    local = _cell(structures, left, right, False, False)
    foreign, foreign_left, foreign_right = _setup()
    other = _cell(foreign, foreign_left, foreign_right, False, False)
    before = structures.ledger.snapshot()
    with pytest.raises(ValueError):
        compose_spatial_transfers(structures, local, other, left, right)
    assert structures.ledger.snapshot() == before


def test_p4_function_valued_boundaries_compose_without_runtime_evaluation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    schema = _HigherSchema(ResourceLedger())
    semantics = HigherSemanticArena(schema)
    left = semantics.variable(semantics.state_sort(schema.p4, 0), "left-boundary")
    right = semantics.variable(semantics.state_sort(schema.p4, 1), "right-boundary")
    zero = semantics.symbol(schema.p4, 0)
    one = semantics.symbol(schema.p4, 1)

    def cell(symbol: HigherExpressionID) -> HigherBoundaryTransfer:
        return higher_boundary_transfer(
            semantics,
            schema.p4,
            left,
            right,
            semantics.action_step(schema.p4, 0, left, symbol),
            semantics.action_step(schema.p4, 1, right, symbol),
        )

    symbols = (zero, one, zero, zero)
    cells = tuple(cell(symbol) for symbol in symbols)
    with monkeypatch.context() as guard:
        guard.setattr(
            semantics.runtime_values,
            "action_function",
            lambda *args, **kwargs: (_ for _ in ()).throw(
                AssertionError("higher runtime continuation was evaluated")
            ),
        )
        two_left = compose_higher_spatial_transfers(semantics, cells[0], cells[1])
        two_right = compose_higher_spatial_transfers(semantics, cells[2], cells[3])
        four = compose_higher_spatial_transfers(semantics, two_left, two_right)

    direct_left = left
    for symbol in symbols:
        direct_left = semantics.action_step(schema.p4, 0, direct_left, symbol)
    direct_right = right
    for symbol in reversed(symbols):
        direct_right = semantics.action_step(schema.p4, 1, direct_right, symbol)
    initial_left = semantics.evaluate(semantics.initial(schema.p4, 0))
    initial_right = semantics.evaluate(semantics.initial(schema.p4, 1))
    environment = {left: initial_left, right: initial_right}
    assert semantics.evaluate(four.left, environment) == semantics.evaluate(
        direct_left,
        environment,
    )
    assert semantics.evaluate(four.right, environment) == semantics.evaluate(
        direct_right,
        environment,
    )


def test_live_higher_macro_composer_uses_shared_absorption_wiring(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        _actions,
        primitive,
        semantics,
        _runtime,
        interfaces,
        compiler,
        sources,
        binding,
    ) = _fixture((7, 18, 7, 19))
    compiled = compiler.compile(primitive)
    outputs = RecursiveCoordinateMorphismArena(
        interfaces,
        evaluate=semantics.evaluate,
    )
    composer = HigherSpatialMacroComposer(
        semantics,
        interfaces,
        outputs,
        sources,
        primitive,
        compiled.interface,
        compiled.left,
        compiled.symbol,
        compiled.right,
    )
    original = HigherSpatialMacroComposer._spatial_wiring
    calls = 0

    def observed(
        instance: HigherSpatialMacroComposer,
        left_macro: SourceBoundHigherMacro,
        right_macro: SourceBoundHigherMacro,
    ) -> HigherSpatialWiring:
        nonlocal calls
        calls += 1
        return original(instance, left_macro, right_macro)

    monkeypatch.setattr(HigherSpatialMacroComposer, "_spatial_wiring", observed)
    macro = composer.compile(binding)
    assert macro.width == 4
    assert calls == 3
