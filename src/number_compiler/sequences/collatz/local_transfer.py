"""Local transfer with one canonical implementation owner."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.contracts.input_validation import is_runtime_instance
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.field_images import (
    SourceBindingID,
    SourceCellID,
    SourceForestID,
)
from number_compiler.hashlife.execution.field_transfer import FieldTransferCandidate
from number_compiler.hashlife.execution.field_transfers import FieldTransferID
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.sequences.collatz.field_action import (
    CollatzCocyclePrograms,
    CollatzFieldActionArena,
    CollatzFieldActionID,
)
from number_compiler.sequences.collatz.powered_local_codec import (
    CollatzLocalActionID,
    CollatzPoweredLocalCodec,
)


class CollatzPoweredLocalTransferAdapter:
    """Publish Collatz source transfers from bounded local and symbolic actions.

    The local codec contributes only its canonical three-carry word action.
    The complete compiler receives the already canonical symbolic output and
    cocycle program handles; it cannot obtain an exact tail or future span
    through this interface.
    """

    output_complete_observation = True
    bounded_interface_successor_closed = False

    def __init__(
        self,
        actions: CollatzFieldActionArena,
        powered_local: CollatzPoweredLocalCodec,
        interfaces: DiamondQuotientArena,
        *,
        compile_complete: Callable[
            [
                CollatzFieldActionID,
                CollatzLocalActionID,
                ActionProgramID,
                CollatzCocyclePrograms,
                FieldGeometryID,
                PortSignatureID,
            ],
            FieldTransferCandidate,
        ],
        validate_port: Callable[[ArenaHandle], None],
        point: Callable[[FieldTransferID, SourceBindingID, ArenaHandle, int], int],
        width: Callable[[FieldTransferID, SourceBindingID, ArenaHandle], int],
        validate_output: Callable[[CoordinateOutputMorphismID], None] | None = None,
        expected_output: CoordinateOutputMorphismID | None = None,
        source_action: Callable[[SourceCellID | SourceForestID], CollatzLocalActionID]
        | None = None,
    ) -> None:
        if (
            actions.ledger is not powered_local.ledger
            or actions.ledger is not interfaces.ledger
        ):
            raise ValueError("Collatz field transfer requires one index ledger")
        if not all(
            callable(value)
            for value in (
                compile_complete,
                validate_port,
                point,
                width,
            )
        ):
            raise TypeError("Collatz field transfer requires executable bounded laws")
        self.actions = actions
        self.powered_local = powered_local
        self.interfaces = interfaces
        self.ledger = actions.ledger
        self._compile_complete = compile_complete
        self._validate_port = validate_port
        self._point = point
        self._width = width
        self.output_validator = validate_output
        self._expected_output = expected_output
        self._source_action = (
            powered_local.source_action if source_action is None else source_action
        )
        if not callable(self._source_action):
            raise TypeError("Collatz transfer requires an executable source morphism")

    def _action(self, action: FieldCellActionID) -> CollatzFieldActionID:
        if type(action) is not CollatzFieldActionID:
            raise TypeError("Collatz transfers require a Collatz field action")
        self.actions.validate_action(action)
        return action

    def validate_action(self, action: FieldCellActionID) -> None:
        self._action(action)

    def validate_port(self, incoming: ArenaHandle) -> None:
        if not is_runtime_instance(incoming, ArenaHandle):
            raise TypeError("Collatz transfer requires a scoped boundary port")
        ArenaHandle.__post_init__(incoming)
        self._validate_port(incoming)

    def _validate_source(self, source: SourceBindingID) -> None:
        if type(source) is SourceCellID:
            self.powered_local.sources.resolve(source)
        elif type(source) is SourceForestID:
            self.powered_local.sources.resolve_forest(source)
        else:
            raise TypeError("Collatz transfer requires a scoped source binding")

    def compile_transfer(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> FieldTransferCandidate:
        collatz_action = self._action(action)
        self._validate_source(source)
        if (
            type(geometry) is not FieldGeometryID
            or type(signature) is not PortSignatureID
        ):
            raise TypeError(
                "Collatz transfer requires scoped geometry and signature IDs"
            )
        self.interfaces.interface(signature)
        record = self.actions.resolve(collatz_action)
        local_action = self._source_action(source)
        result = self._compile_complete(
            collatz_action,
            local_action,
            record.output_morphism,
            record.cocycles,
            geometry,
            signature,
        )
        if type(result) is not FieldTransferCandidate:
            raise TypeError("Collatz transfer compiler returned an incomplete result")
        quotient = self.interfaces.resolve(result.interface)
        if quotient.signature != signature:
            raise ValueError(
                "Collatz transfer compiler returned another port signature"
            )
        if self.output_validator is None:
            if result.output != self.actions.coordinate_output(collatz_action):
                raise ValueError(
                    "Collatz transfer compiler returned another output morphism"
                )
        else:
            self.output_validator(result.output)
            if (
                self._expected_output is not None
                and result.output != self._expected_output
            ):
                raise ValueError(
                    "Collatz transfer compiler returned another output morphism"
                )
        result.__post_init__()
        return result

    def point_transfer(
        self,
        transfer: FieldTransferID,
        source: SourceBindingID,
        incoming: ArenaHandle,
        coordinate: int,
    ) -> int:
        self.validate_port(incoming)
        self._validate_source(source)
        if type(transfer) is not FieldTransferID or type(coordinate) is not int:
            raise TypeError("Collatz point transfer requires scoped exact inputs")
        result = self._point(transfer, source, incoming, coordinate)
        # The internal coordinate morphism is output-complete over the padded
        # source cover.  Its blank symbol is needed so the public term can turn
        # an observation at or beyond the exact extent into ``IndexError``.
        if type(result) is not int or result not in (0, 1, 2):
            raise ValueError("Collatz point transfer returned another alphabet")
        return result

    def width_transfer(
        self,
        transfer: FieldTransferID,
        source: SourceBindingID,
        incoming: ArenaHandle,
    ) -> int:
        self.validate_port(incoming)
        self._validate_source(source)
        if type(transfer) is not FieldTransferID:
            raise TypeError("Collatz width transfer requires a scoped transfer ID")
        result = self._width(transfer, source, incoming)
        if type(result) is not int or result < 0:
            raise ValueError("Collatz width transfer returned an invalid extent")
        return result
