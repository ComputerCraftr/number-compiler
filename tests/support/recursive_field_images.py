"""Recursive field images with one canonical implementation owner."""

from __future__ import annotations

from collections.abc import Callable, MutableSequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, Never, overload

from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaHandle,
    ArenaToken,
    ExactSource,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
    FieldGeometry,
    FieldGeometryArena,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.continuations.provider_absorption import (
    ProviderAbsorptionArena,
    ProviderAction,
)
from number_compiler.hashlife.execution.continuations.provider_image_input import (
    ProviderImageInputArena,
)
from number_compiler.hashlife.execution.field_executor import (
    FieldImageAdapter,
    FieldImageCandidate,
    ParentObservation,
    RecursiveFieldImageExecutor,
)
from number_compiler.hashlife.execution.field_images import (
    FieldImageID,
    FieldImageSummary,
    RecursiveFieldImageArena,
    SourceBindingID,
    SourceCellArena,
    SourceCellID,
    SourceForestID,
)
from number_compiler.hashlife.execution.field_transfer import (
    FieldTransferCandidate,
    FieldTransferExecutor,
)
from number_compiler.hashlife.execution.field_transfers import (
    FieldTransferArena,
    FieldTransferID,
)
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    DiamondQuotientArena,
    LocalInterfaceID,
    MacroComponents,
    MacroInterface,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.support.finite_functions import carry_atoms

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
    from number_compiler.hashlife.actions.field_actions import (
        FieldGeometryID,
    )
    from number_compiler.hashlife.execution.continuations.provider_absorption import (
        ProviderActionID,
        ProviderBindingKey,
    )
    from number_compiler.hashlife.execution.continuations.provider_image_input import (
        ProviderImageInputID,
    )
    from number_compiler.hashlife.execution.field_executor import FieldImageApplication
    from number_compiler.hashlife.execution.field_images import (
        SourceForestID,
    )


class _Adapter:
    signature_id: PortSignatureID
    observe_parent_point: Callable[
        [
            FieldCellActionID,
            SourceBindingID,
            FieldGeometryID,
            PortSignatureID,
            ArenaHandle,
            int,
        ],
        ParentObservation | None,
    ]
    observe_parent_width: Callable[
        [
            FieldCellActionID,
            SourceBindingID,
            FieldGeometryID,
            PortSignatureID,
            ArenaHandle,
        ],
        ParentObservation | None,
    ]

    def __init__(
        self,
        action: FieldCellActionID,
        interface: LocalInterfaceID,
        output: CoordinateOutputMorphismID,
        sources: SourceCellArena | None = None,
    ) -> None:
        self.action = action
        self.interface = interface
        self.output = output
        self.sources = sources
        self.leaf_calls = 0
        self.join_calls = 0
        self.forest_calls = 0
        self.port_owner = ArenaToken("test-image-port")

    def validate_action(self, action: FieldCellActionID) -> None:
        if type(action) is not FieldCellActionID or action != self.action:
            raise ValueError("foreign field action")

    def validate_output(self, output: CoordinateOutputMorphismID) -> None:
        output.validate(self.output.owner, self.output.kind, size=1)

    def signature(
        self, action: FieldCellActionID, geometry: FieldGeometryID
    ) -> PortSignatureID:
        self.validate_action(action)
        return self.signature_id

    def validate_port(self, incoming: ArenaHandle) -> None:
        incoming.validate(self.port_owner, "test-image-port", size=1)

    def action_children(
        self, action: FieldCellActionID
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        self.validate_action(action)
        return None

    def leaf(
        self, action: FieldCellActionID, source: SourceCellID, geometry: FieldGeometryID
    ) -> FieldImageCandidate:
        self.validate_action(action)
        self.leaf_calls += 1

        return FieldImageCandidate(
            self.interface,
            self.output,
            FieldImageSummary(True, 0, 0, 1),
        )

    def join(
        self,
        action: FieldCellActionID,
        source: SourceCellID,
        left: FieldImageID,
        right: FieldImageID,
        geometry: FieldGeometryID,
    ) -> FieldImageCandidate:
        self.validate_action(action)
        assert type(left) is FieldImageID and type(right) is FieldImageID
        self.join_calls += 1

        return FieldImageCandidate(
            self.interface,
            self.output,
            FieldImageSummary(True, 0, 1, 2),
        )

    def forest(
        self,
        action: FieldCellActionID,
        source: SourceForestID,
        geometry: FieldGeometryID,
    ) -> FieldImageCandidate:
        self.validate_action(action)
        self.forest_calls += 1
        assert self.sources is not None
        extent = self.sources.resolve_forest(source).extent

        return FieldImageCandidate(
            self.interface,
            self.output,
            FieldImageSummary(True, 0, extent - 1, extent),
        )

    def temporal(self, *_args: object, **_kwargs: object) -> Never:
        raise AssertionError("the primitive test action has no temporal children")

    def point(self, image: FieldImageID, coordinate: int) -> int:
        assert type(image) is FieldImageID
        return 0

    def point_bound(
        self,
        image: FieldImageID,
        source: SourceBindingID,
        incoming: ArenaHandle,
        coordinate: int,
    ) -> int:
        self.validate_port(incoming)
        return self.point(image, coordinate)

    def width_bound(
        self, image: FieldImageID, source: SourceBindingID, incoming: ArenaHandle
    ) -> int:
        self.validate_port(incoming)
        return 2


class _SecondDomainArena:
    def __init__(
        self,
        ledger: ResourceLedger,
        action_owner: ArenaToken,
        output_owner: ArenaToken,
        signature: PortSignatureID,
        action_kind: str = "second-field-action",
        output_kind: str = "second-output",
        action_size: int = 1,
        output_size: int = 1,
    ) -> None:
        self.ledger = ledger
        self.action_owner = action_owner
        self.output_owner = output_owner
        self.action_kind = action_kind
        self.output_kind = output_kind
        self.signature_id = signature
        self.action_size = action_size
        self.output_size = output_size
        owner = ledger.register(
            f"test-second-domain-{len(ledger.inventory())}",
            "test_semantic_authority",
        )
        self._nodes: MutableSequence[tuple[ArenaToken, ArenaToken]] = ledger.make_list(
            owner
        )
        ledger.register_container(owner, self._nodes, payloads=lambda: self._nodes)
        ledger.reserve(owner, entries=1, nodes=1)
        self._nodes.append((action_owner, output_owner))
        ledger.register_execution_root(self)

    def validate_action(self, value: FieldCellActionID) -> None:
        value.validate(self.action_owner, self.action_kind, size=self.action_size)

    def validate_output(self, value: CoordinateOutputMorphismID) -> None:
        value.validate(self.output_owner, self.output_kind, size=self.output_size)

    def signature(
        self, value: FieldCellActionID, _geometry: FieldGeometryID
    ) -> PortSignatureID:
        self.validate_action(value)
        return self.signature_id


@overload
def _setup() -> tuple[
    ResourceLedger,
    SourceCellID,
    PortSignatureID,
    FieldGeometryID,
    FieldCellActionID,
    RecursiveFieldImageArena,
    _Adapter,
    RecursiveFieldImageExecutor[FieldImageAdapter],
]: ...


@overload
def _setup(
    digits: tuple[int, ...],
) -> tuple[
    ResourceLedger,
    SourceCellID | SourceForestID,
    PortSignatureID,
    FieldGeometryID,
    FieldCellActionID,
    RecursiveFieldImageArena,
    _Adapter,
    RecursiveFieldImageExecutor[FieldImageAdapter],
]: ...


def _setup(
    digits: tuple[int, ...] = (0, 0),
) -> tuple[
    ResourceLedger,
    SourceCellID | SourceForestID,
    PortSignatureID,
    FieldGeometryID,
    FieldCellActionID,
    RecursiveFieldImageArena,
    _Adapter,
    RecursiveFieldImageExecutor[FieldImageAdapter],
]:
    ledger = ResourceLedger()
    geometry = SourceGeometry(
        ledger, ExactSource(digits, 2, blank=2, extent=len(digits))
    )
    geometry.span(digits, 2, len(digits))
    sources = SourceCellArena(geometry)
    level = (len(digits) - 1).bit_length()
    root = (
        sources.intern(0, level)
        if len(digits) == 1 << level
        else sources.forest(0, len(digits))
    )
    functions = SemanticFunctionArena(ledger)
    quotients = DiamondQuotientArena(functions)
    port, _unused_signature_binding, zero, one = carry_atoms(functions)
    declared = quotients.intern_interface(
        MacroInterface(
            SemanticIdentity("recursive-image-test-v1", ("kernel",)),
            (port,),
            (BOOL,) * len(COMPONENT_ROLES),
            one,
        )
    )
    interface = quotients.intern(
        declared, MacroComponents(*(zero for _ in COMPONENT_ROLES))
    )
    geometries = FieldGeometryArena(ledger)
    field_geometry = geometries.intern(FieldGeometry(level))
    action_owner = ArenaToken("test-field-actions")
    output_owner = ArenaToken("test-field-outputs")
    action = FieldCellActionID(action_owner, "field-cell-action", 0)
    output = CoordinateOutputMorphismID(output_owner, "coordinate-output-morphism", 0)
    adapter = _Adapter(action, interface, output, sources)
    adapter.signature_id = declared
    authority = _SecondDomainArena(
        ledger,
        action_owner,
        output_owner,
        declared,
        action_kind="field-cell-action",
        output_kind="coordinate-output-morphism",
    )
    images = RecursiveFieldImageArena(
        ledger,
        sources,
        geometries,
        quotients,
        action_owner=action_owner,
        output_owner=output_owner,
        signature_owner=quotients.owner,
        action_validate=authority.validate_action,
        output_validate=authority.validate_output,
        signature_for=authority.signature,
        action_authority=authority,
        output_authority=authority,
        signature_authority=authority,
        signature_kind="diamond-semantic-signature",
    )
    executor = RecursiveFieldImageExecutor(sources, images, adapter)
    return ledger, root, declared, field_geometry, action, images, adapter, executor


def _provider_setup() -> tuple[
    ResourceLedger, ProviderAbsorptionArena, ProviderActionID, ProviderBindingKey
]:
    ledger, source, _signature, _, action, images, adapter, _ = _setup((0, 1))

    def validate_boundary(value: object) -> None:
        if type(value) is not int or value not in (0, 1):
            raise ValueError("invalid boundary")

    def validate_output(value: CoordinateOutputMorphismID) -> None:
        value.validate(images.output_owner, images.output_kind, size=2)

    def observe(
        _output: CoordinateOutputMorphismID,
        coordinate: int,
        left: object,
        right: object,
    ) -> int:
        assert isinstance(left, int) and isinstance(right, int)
        return (coordinate + left + right) & 1

    providers = ProviderAbsorptionArena(
        ledger,
        images.sources,
        validate_output=validate_output,
        validate_bound_output=validate_output,
        validate_interface=images.interfaces.resolve,
        validate_bound_interface=images.interfaces.resolve,
        validate_action=images._action_validate,
        validate_boundary=validate_boundary,
        observe=observe,
    )
    provider = providers.intern(
        ProviderAction(adapter.output, adapter.interface, action, 0, 0, 1)
    )
    bound_output = CoordinateOutputMorphismID(
        images.output_owner,
        images.output_kind,
        1,
    )
    binding = providers.bind(provider, source, bound_output, adapter.interface)
    return ledger, providers, provider, binding


def _completed_provider_input_setup(
    digits: tuple[int, int] = (0, 1),
) -> tuple[
    ResourceLedger,
    RecursiveFieldImageArena,
    ProviderAbsorptionArena,
    ProviderImageInputArena,
    ProviderImageInputID,
]:
    (
        ledger,
        source,
        _signature,
        _geometry,
        _action,
        images,
        _adapter,
        _executor,
        _image,
        providers,
        _provider,
        binding,
    ) = _completed_provider_setup(digits)
    inputs = ProviderImageInputArena(providers, images)
    assert isinstance(source, SourceCellID)
    root = inputs.bind(binding, source, 2)
    return ledger, images, providers, inputs, root


@dataclass(frozen=True, slots=True)
class _PortID(ArenaHandle):
    pass


class _TransferAdapter:
    def __init__(
        self,
        action: FieldCellActionID,
        interface: LocalInterfaceID,
        output: CoordinateOutputMorphismID,
    ) -> None:
        self.action = action
        self.interface = interface
        self.output = output
        self.port_owner = ArenaToken("test-boundary-values")
        self.compile_calls = 0

    def validate_action(self, action: FieldCellActionID) -> None:
        if type(action) is not FieldCellActionID or action != self.action:
            raise ValueError("foreign field action")

    def validate_port(self, incoming: ArenaHandle) -> None:
        if type(incoming) is not _PortID:
            raise TypeError("expected a typed test boundary")
        incoming.validate(self.port_owner, "test-boundary", size=2)

    def compile_transfer(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> FieldTransferCandidate:
        self.validate_action(action)
        assert type(source) is SourceCellID
        self.compile_calls += 1
        return FieldTransferCandidate(
            self.interface,
            self.output,
            2,
        )

    def point_transfer(
        self,
        transfer: FieldTransferID,
        source: SourceBindingID,
        incoming: ArenaHandle,
        coordinate: int,
    ) -> int:
        self.validate_port(incoming)
        return incoming.local_id

    def width_transfer(
        self, transfer: FieldTransferID, source: SourceBindingID, incoming: ArenaHandle
    ) -> int:
        self.validate_port(incoming)
        return incoming.local_id + 1


def _transfer_setup() -> tuple[
    ResourceLedger,
    SourceCellID | SourceForestID,
    PortSignatureID,
    FieldGeometryID,
    FieldCellActionID,
    RecursiveFieldImageArena,
    _TransferAdapter,
    FieldTransferArena,
    FieldTransferExecutor,
]:
    ledger, source, signature, geometry, action, images, adapter, _ = _setup()
    transfer_adapter = _TransferAdapter(action, adapter.interface, adapter.output)
    transfers = FieldTransferArena(
        ledger,
        images.sources,
        images.geometries,
        images.interfaces,
        action_owner=action.owner,
        output_owner=adapter.output.owner,
        action_validate=adapter.validate_action,
        output_validate=adapter.validate_output,
    )
    executor = FieldTransferExecutor(transfers, transfer_adapter)
    return (
        ledger,
        source,
        signature,
        geometry,
        action,
        images,
        transfer_adapter,
        transfers,
        executor,
    )


def _application_setup() -> tuple[
    ResourceLedger,
    SourceCellID,
    PortSignatureID,
    FieldGeometryID,
    FieldCellActionID,
    RecursiveFieldImageArena,
    _Adapter,
    RecursiveFieldImageExecutor[FieldImageAdapter],
    ArenaHandle,
    FieldImageApplication,
]:
    fixture = _setup()
    (
        _unused_ledger_binding,
        source,
        signature,
        geometry,
        action,
        _unused_images_binding,
        adapter,
        executor,
    ) = fixture
    incoming = ArenaHandle(adapter.port_owner, "test-image-port", 0)
    return (
        *fixture,
        incoming,
        executor.application(action, source, geometry, signature, incoming),
    )


def _completed_provider_setup(
    digits: tuple[int, int] = (0, 1),
) -> tuple[
    ResourceLedger,
    SourceCellID | SourceForestID,
    PortSignatureID,
    FieldGeometryID,
    FieldCellActionID,
    RecursiveFieldImageArena,
    _Adapter,
    RecursiveFieldImageExecutor[FieldImageAdapter],
    FieldImageID,
    ProviderAbsorptionArena,
    ProviderActionID,
    ProviderBindingKey,
]:
    fixture = _setup(digits)
    ledger, source, signature, geometry, action, images, adapter, executor = fixture
    image = executor.image(action, source, geometry, signature)
    providers = ProviderAbsorptionArena(
        ledger,
        images.sources,
        validate_output=images._output_validate,
        validate_bound_output=images._output_validate,
        validate_interface=images.interfaces.resolve,
        validate_bound_interface=images.interfaces.resolve,
        validate_action=images._action_validate,
        validate_boundary=lambda _value: None,
        observe=lambda *_args: 0,
        validate_image=images.resolve,
        validate_image_occurrence=images.validate_occurrence,
        validate_image_context_occurrence=images.validate_occurrence,
    )
    provider = providers.intern(
        ProviderAction(adapter.output, adapter.interface, action, 0, 0, 1)
    )
    binding = providers.bind(provider, source, adapter.output, adapter.interface, image)
    return (*fixture, image, providers, provider, binding)
