"""Field transfer with one canonical implementation owner."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Never, Protocol

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
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
from number_compiler.hashlife.execution.field_transfers import (
    FieldTransferArena,
    FieldTransferID,
    FieldTransferRecord,
    FieldTransferRequestKey,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)


def _invalid_source_binding() -> Never:
    raise TypeError("field transfer requires a scoped source binding")


@dataclass(frozen=True, slots=True)
class FieldTransferCandidate:
    interface: LocalInterfaceID
    output: CoordinateOutputMorphismID
    extent_bound: int

    def __post_init__(self) -> None:
        if type(self.extent_bound) is not int or self.extent_bound < 0:
            raise ValueError("field transfer requires a nonnegative exact extent bound")


class FieldTransferAdapter(Protocol):
    """Compile and observe complete parent transfers without exact images."""

    def validate_action(self, action: FieldCellActionID) -> None: ...

    def validate_port(self, incoming: ArenaHandle) -> None: ...

    def compile_transfer(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> FieldTransferCandidate:
        """Return a complete parametric parent action without child images."""
        ...

    def point_transfer(
        self,
        transfer: FieldTransferID,
        source: SourceBindingID,
        incoming: ArenaHandle,
        coordinate: int,
    ) -> int: ...

    def width_transfer(
        self,
        transfer: FieldTransferID,
        source: SourceBindingID,
        incoming: ArenaHandle,
    ) -> int: ...


class FieldTransferExecutor:
    """Parent-first point/width executor over bounded parametric transfers."""

    is_algebraic_field_action_executor = True

    def __init__(
        self,
        transfers: FieldTransferArena,
        adapter: FieldTransferAdapter,
    ) -> None:
        self.transfers = transfers
        self.sources = transfers.sources
        self.adapter = adapter
        self.ledger = transfers.ledger
        self.ledger.register_execution_root(self)

    def transfer(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> FieldTransferID:
        key = FieldTransferRequestKey(action, source, geometry, signature)
        found = self.transfers.probe(key)
        self.ledger.bump(_execution_keys.FIELD_TRANSFER_PARENT_REQUESTS)
        if found is not None:
            self.ledger.bump(_execution_keys.FIELD_TRANSFER_PARENT_EARLY_HITS)
            return found
        source_level = (
            self.sources.resolve(source).level
            if type(source) is SourceCellID
            else (self.sources.resolve_forest(source).extent - 1).bit_length()
            if type(source) is SourceForestID
            else _invalid_source_binding()
        )
        candidate = self.adapter.compile_transfer(action, source, geometry, signature)
        if type(candidate) is not FieldTransferCandidate:
            raise TypeError("field-transfer compiler returned an incomplete parent")
        record = FieldTransferRecord(
            source_level,
            candidate.interface,
            candidate.output,
            geometry,
            candidate.extent_bound,
        )
        result = self.transfers.publish(key, record)
        self.ledger.bump(_execution_keys.FIELD_TRANSFER_PARENT_EVALUATIONS)
        return result

    def point(
        self,
        transfer: FieldTransferID,
        source: SourceBindingID,
        incoming: ArenaHandle,
        coordinate: int,
    ) -> int:
        if type(coordinate) is not int:
            raise TypeError("field-transfer coordinate must be an exact integer")
        self.adapter.validate_port(incoming)
        record = self.transfers.resolve(transfer)
        self.transfers.validate_observation_source(transfer, source)
        if not 0 <= coordinate < record.extent_bound:
            raise IndexError(coordinate)
        self.ledger.bump(_execution_keys.POINT_OBSERVATIONS)
        return self.adapter.point_transfer(transfer, source, incoming, coordinate)

    def width(
        self,
        transfer: FieldTransferID,
        source: SourceBindingID,
        incoming: ArenaHandle,
    ) -> int:
        self.adapter.validate_port(incoming)
        record = self.transfers.resolve(transfer)
        self.transfers.validate_observation_source(transfer, source)
        result = self.adapter.width_transfer(transfer, source, incoming)
        if type(result) is not int or not 0 <= result <= record.extent_bound:
            raise ValueError("field-transfer width lies outside its extent")
        self.ledger.bump(_execution_keys.WIDTH_OBSERVATIONS)
        return result

    def application(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
        incoming: ArenaHandle,
    ) -> FieldTransferApplication:
        from number_compiler.hashlife.execution.field_executor import (
            _TRANSFER_APPLICATION_SEAL,
        )

        self.transfers.validate_request(
            FieldTransferRequestKey(action, source, geometry, signature)
        )
        self.adapter.validate_port(incoming)
        return FieldTransferApplication(
            self,
            action,
            source,
            geometry,
            signature,
            incoming,
            _TRANSFER_APPLICATION_SEAL,
        )


class FieldTransferApplication:
    """Public point/width view that never constructs an exact future image."""

    __slots__ = (
        "__weakref__",
        "_seal",
        "action",
        "executor",
        "geometry",
        "incoming",
        "ledger",
        "signature",
        "source",
    )

    is_algebraic_field_action_executor = True

    def __init__(
        self,
        executor: FieldTransferExecutor,
        action: FieldCellActionID,
        source: SourceBindingID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
        incoming: ArenaHandle,
        seal: object,
    ) -> None:
        from number_compiler.hashlife.execution.field_executor import (
            _TRANSFER_APPLICATION_SEAL,
        )

        if seal is not _TRANSFER_APPLICATION_SEAL:
            raise TypeError("field-transfer applications are issued by their executor")
        self.executor = executor
        self.action = action
        self.source = source
        self.geometry = geometry
        self.signature = signature
        self.incoming = incoming
        self.ledger = executor.ledger
        self._seal = seal
        from number_compiler.hashlife.execution.field_capabilities import (
            register_field_application,
        )

        register_field_application(self.ledger, self)

    def _transfer(self) -> FieldTransferID:
        return self.executor.transfer(
            self.action,
            self.source,
            self.geometry,
            self.signature,
        )

    def point(self, position: int) -> int:
        if type(position) is not int:
            raise TypeError("field-transfer coordinate must be an exact integer")
        return self.executor.point(
            self._transfer(),
            self.source,
            self.incoming,
            position,
        )

    def active_width(self) -> int:
        return self.executor.width(
            self._transfer(),
            self.source,
            self.incoming,
        )

    def retained_entries(self) -> int:
        return self.executor.transfers.retained_bindings
