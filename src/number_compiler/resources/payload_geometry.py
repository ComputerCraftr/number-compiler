"""Geometry-only scalar fields admitted by the independent retained-payload audit."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.block_kernel import (
    _BaseLeftState,
    _BaseRightState,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
    FrameTransform,
    LoweringCapability,
    TransferSummaryID,
)
from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.arithmetic.fields.consumer_pullback import (
    AssociatedActionID,
    AssociatedActionRecord,
    ExactRational,
    SaturatingAffineAction,
    ThresholdDemand,
)
from number_compiler.arithmetic.functions.finite_port_action import (
    ChoiceKey,
    DecisionKey,
    FoldedPortCut,
    PortComponent,
    PortCompositionKey,
    PortVariable,
    _ChoiceIndexKey,
    _Decision,
    _DecisionIndexKey,
)
from number_compiler.arithmetic.functions.finite_port_substitution import (
    SubstitutionKey,
    _PortIndexComponent,
    _SubstitutionIndexKey,
)
from number_compiler.hashlife.actions.lazy_compiler import CompilerCompositionKey
from number_compiler.hashlife.execution.associated_action_images import (
    AssociatedScalarPayload,
    AssociatedScalarSource,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    BehaviorBindingKey,
    CompletedBehaviorClassification,
)
from number_compiler.projection.digit_terminal import _DigitLeftState
from number_compiler.projection.microblock_cache import MicroblockKey
from number_compiler.projection.point_response import PointResponse


def geometry_field_policy() -> dict[type[object], frozenset[str]]:
    return {
        ArenaHandle: frozenset(("local_id",)),
        ActionProgramID: frozenset(("local_id",)),
        TransferSummaryID: frozenset(("local_id",)),
        ArenaToken: frozenset(),
        FrameTransform: frozenset(("shift",)),
        LoweringCapability: frozenset(),
        _BaseLeftState: frozenset(),
        _BaseRightState: frozenset(),
        _DigitLeftState: frozenset(),
        PortVariable: frozenset(("time", "side", "bit")),
        _Decision: frozenset(("low", "high")),
        _DecisionIndexKey: frozenset(("low", "high")),
        _ChoiceIndexKey: frozenset(("condition", "yes", "no")),
        PortComponent: frozenset(),
        FoldedPortCut: frozenset(),
        DecisionKey: frozenset(),
        ChoiceKey: frozenset(),
        PortCompositionKey: frozenset(),
        SubstitutionKey: frozenset(),
        _PortIndexComponent: frozenset(("function",)),
        _SubstitutionIndexKey: frozenset(("function",)),
        CompilerCompositionKey: frozenset(),
        PointResponse: frozenset(("position",)),
        MicroblockKey: frozenset(("radix", "stage", "block")),
        BehaviorBindingKey: frozenset(),
        CompletedBehaviorClassification: frozenset(),
        ExactRational: frozenset(("numerator", "denominator")),
        ThresholdDemand: frozenset(),
        SaturatingAffineAction: frozenset(),
        BlankLedger: frozenset(("delta", "minimum", "maximum")),
        AssociatedActionID: frozenset(("local_id",)),
        AssociatedActionRecord: frozenset(("semantic_id", "logical_extent")),
        AssociatedScalarSource: frozenset(),
        AssociatedScalarPayload: frozenset(),
    }
