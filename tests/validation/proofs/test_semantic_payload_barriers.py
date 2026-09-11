"""Known record names never authorize numeric limbs in semantic fields."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import fields
from typing import TYPE_CHECKING, cast, get_type_hints

import pytest

import devtools.proofs.lazy_collatz as collatz
import devtools.proofs.lazy_collatz_range as collatz_range
import devtools.proofs.lazy_reverse as reverse
import number_compiler.arithmetic.contracts.block_kernel as base
import number_compiler.arithmetic.functions.finite_port_action as finite
import number_compiler.projection.digit_terminal as digit
from devtools.proofs.carry_interval_effects import (
    CarryIntervalCompositionKey,
    CarryIntervalEffect,
)
from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
    FrameTransform,
    LoweringCapability,
    TransferSummaryID,
    WordLimb,
)
from number_compiler.arithmetic.functions.finite_port_substitution import (
    SubstitutionKey,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
    FieldGeometryID,
)
from number_compiler.hashlife.actions.lazy_compiler import CompilerCompositionKey
from number_compiler.hashlife.execution.field_images import (
    SourceBindingID,
    SourceCellID,
)
from number_compiler.hashlife.execution.field_transfers import (
    FieldTransferRecord,
    FieldTransferRequestKey,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.projection.microblock_cache import ExactMicroblock, MicroblockKey
from number_compiler.projection.point_response import PointResponse
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerList
from tests.support.dataclass_records import replace_record

if TYPE_CHECKING:
    from devtools.proofs.carry_interval_effects import (
        CarryIntervalCompositionKey,
        CarryIntervalEffect,
    )
    from devtools.proofs.lazy_collatz import (
        CarryRangeSummary,
        CarryRangeTransfer,
        CollatzLazyView,
        LazyCollatzResult,
        _Mul3Port,
        _Program,
        _ResultKey,
        _ShiftPort,
        _SourceRangeKey,
        _SummaryKey,
    )
    from devtools.proofs.lazy_collatz_range import (
        CollatzRangeEffect,
        _CompositionKey,
        _RangeKey,
        _Request,
        _SourceTileKey,
    )
    from devtools.proofs.lazy_reverse import (
        OffsetProgram,
        ReverseProgram,
        ReverseRangeKey,
    )
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
    from number_compiler.arithmetic.functions.finite_port_action import (
        ChoiceKey,
        DecisionKey,
        FoldedPortCut,
        PortComponent,
        PortCompositionKey,
        PortVariable,
        _Decision,
    )
    from number_compiler.arithmetic.functions.finite_port_substitution import (
        SubstitutionKey,
    )
    from number_compiler.hashlife.actions.lazy_compiler import CompilerCompositionKey
    from number_compiler.hashlife.execution.field_transfers import (
        FieldTransferRecord,
        FieldTransferRequestKey,
    )
    from number_compiler.projection.digit_terminal import _DigitLeftState
    from number_compiler.projection.microblock_cache import (
        ExactMicroblock,
        MicroblockKey,
    )
    from number_compiler.projection.point_response import PointResponse


def templates() -> tuple[
    ArenaToken,
    ArenaHandle,
    ActionProgramID,
    TransferSummaryID,
    FrameTransform,
    LoweringCapability,
    OffsetProgram,
    ReverseProgram,
    ReverseRangeKey,
    reverse.CarryRangeSummary,
    CarryIntervalEffect,
    TransferSummaryID,
    CarryIntervalCompositionKey,
    CompilerCompositionKey,
    PointResponse,
    _Program,
    _ResultKey,
    _SummaryKey,
    _SourceRangeKey,
    _Mul3Port,
    _ShiftPort,
    CollatzLazyView,
    LazyCollatzResult,
    CarryRangeSummary,
    CarryRangeTransfer,
    CollatzRangeEffect,
    _RangeKey,
    _CompositionKey,
    _Request,
    TransferSummaryID,
    _SourceTileKey,
    FieldTransferRequestKey,
    FieldTransferRecord,
    _BaseLeftState,
    _BaseRightState,
    _DigitLeftState,
    PortVariable,
    _Decision,
    PortComponent,
    FoldedPortCut,
    DecisionKey,
    ChoiceKey,
    PortCompositionKey,
    SubstitutionKey,
    MicroblockKey,
    ExactMicroblock,
]:
    token = ArenaToken("test")
    source, program = (
        ArenaHandle(token, "source", 0),
        ActionProgramID(token, "program", 0),
    )
    function = TransferSummaryID(token, "finite-port-function", 0)
    interval = TransferSummaryID(token, "carry-interval-effect", 0)
    range_action = TransferSummaryID(token, "collatz-range-effect", 0)
    field_action = FieldCellActionID(token, "field-cell-action", 0)
    source_binding = SourceCellID(token, "source-cell", 0)
    geometry = FieldGeometryID(token, "field-geometry", 0)
    signature = PortSignatureID(token, "port-signature", 0)
    interface = LocalInterfaceID(token, "diamond-quotient", 0)
    output = CoordinateOutputMorphismID(token, "coordinate-output-morphism", 0)
    port = finite.PortVariable(0, 0, "carry", 0)
    component = finite.PortComponent(port, function)
    view = collatz.CollatzLazyView(source, program, 1)
    return (
        token,
        source,
        program,
        function,
        FrameTransform(),
        LoweringCapability(token),
        reverse.OffsetProgram("zero"),
        reverse.ReverseProgram(0, 0, 0, 0, 1, 0),
        reverse.ReverseRangeKey(0, 8),
        reverse.CarryRangeSummary(0, 8, interval),
        CarryIntervalEffect(function, function, 1),
        interval,
        CarryIntervalCompositionKey(interval, interval, port),
        CompilerCompositionKey(
            ActionProgramID(token, "action-program", 0),
            ActionProgramID(token, "action-program", 0),
        ),
        PointResponse(ActionProgramID(token, "action-program", 0), 0, 0),
        collatz._Program("mul3"),
        collatz._ResultKey("events", 1),
        collatz._SummaryKey(program, 1),
        collatz._SourceRangeKey(1),
        collatz._Mul3Port(program),
        collatz._ShiftPort(program, 1),
        view,
        collatz.LazyCollatzResult(view, (1,)),
        collatz.CarryRangeSummary(1, 0, 0, 0),
        collatz.CarryRangeTransfer.bit(0),
        collatz_range.CollatzRangeEffect(collatz.CarryRangeTransfer.bit(0), None, None),
        collatz_range._RangeKey(program, 0, 8),
        collatz_range._CompositionKey(range_action, range_action),
        collatz_range._Request("range", program, 0, 8),
        range_action,
        collatz_range._SourceTileKey(ArenaHandle(token, "source-tile", 0), 8),
        FieldTransferRequestKey(field_action, source_binding, geometry, signature),
        FieldTransferRecord(0, interface, output, geometry, 1),
        base._BaseLeftState(0, 0, False),
        base._BaseRightState(CarryFn.ID, CarryFn.ID),
        digit._DigitLeftState(0, False),
        port,
        finite._Decision(None),
        component,
        finite.FoldedPortCut((component,)),
        finite.DecisionKey(port, function, function),
        finite.ChoiceKey(function, function, function),
        finite.PortCompositionKey(function, function, port),
        SubstitutionKey(function, (component,)),
        MicroblockKey(ActionProgramID(token, "action-program", 0), 3, 0, 0, "binary"),
        ExactMicroblock(1, 1),
    )


CASES = tuple(
    (record, field.name) for record in templates() for field in fields(record)
)


@pytest.mark.parametrize(
    "record,field_name",
    CASES,
    ids=lambda value: type(value).__name__ if not isinstance(value, str) else value,
)
def test_every_semantic_field_rejects_a_numeric_four_limb_substitution(
    record: object, field_name: str
) -> None:
    forged = []
    for index in range(4):
        try:
            forged.append(
                replace_record(record, {field_name: WordLimb((1 << 62) + index)})
            )
        except (TypeError, ValueError, AttributeError):
            return  # The constructor enforces the stronger boundary already.
    ledger = ResourceLedger()
    owner = ledger.register("semantic-records", "transfer_summary")
    storage: LedgerList[object]
    storage = ledger.make_list(owner)
    ledger.reserve(owner, entries=4, nodes=4)
    storage.extend(forged)
    report = collect_ledger_metrics(ledger)
    assert report.forbidden_future_payloads > 0, (type(record).__name__, field_name)


@pytest.mark.parametrize(
    "make",
    (
        lambda value: FieldTransferRequestKey(
            FieldCellActionID(ArenaToken("test"), "field-cell-action", 0),
            cast("SourceBindingID", value),
            FieldGeometryID(ArenaToken("test"), "field-geometry", 0),
            PortSignatureID(ArenaToken("test"), "port-signature", 0),
        ),
        lambda value: base._BaseLeftState(0, value, False),
        lambda value: finite._Decision(None, value, 0),
    ),
)
def test_raw_numeric_words_cannot_pose_as_finite_states_or_local_ids(
    make: Callable[[int], object],
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("states", "transfer_summary")
    storage: LedgerList[object]
    storage = ledger.make_list(owner)
    ledger.reserve(owner, entries=4, nodes=4)
    storage.extend(make((1 << 62) + i) for i in range(4))
    assert collect_ledger_metrics(ledger).forbidden_future_payloads > 0


@pytest.mark.parametrize(
    "record", (reverse.OffsetProgram("zero"), collatz._ResultKey("events", 1))
)
def test_unknown_operation_strings_are_not_semantic_programs(record: object) -> None:
    forged = replace_record(
        record, {"kind": "a future numeric word encoded as an opcode"}
    )
    ledger = ResourceLedger()
    owner = ledger.register("programs", "action_program")
    storage: LedgerList[object]
    storage = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    storage.append(forged)
    assert collect_ledger_metrics(ledger).forbidden_future_payloads > 0


def test_metric_snapshot_resolves_each_record_type_annotation_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.resources.payload_schema as payload_schema
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        SpatialSummary,
    )
    from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
    from tests.support.diamond_runtime import build

    runtime, action = build(CollatzPhysicalBlockEffect(), (1, 1, 0, 1), 4, 1)
    runtime.execute(SpatialSummary(action, runtime.cells.source(0, 2), 0))
    calls: list[type[object]] = []
    original = get_type_hints

    def measured(record_type: type[object]) -> dict[str, object]:
        calls.append(record_type)
        return original(record_type)

    monkeypatch.setattr(payload_schema, "get_type_hints", measured)
    assert collect_ledger_metrics(runtime.ledger).resource_audit_complete == 1
    assert len(calls) == len(set(calls))
