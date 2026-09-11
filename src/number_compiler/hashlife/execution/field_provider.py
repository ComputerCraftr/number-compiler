"""Sealed powered-provider views over canonical recursive field images."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.field_images import (
    FieldImageID,
    FieldImageRecord,
    ImageRequestKey,
    ParametricFieldImageSummary,
    SourceBindingID,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.field_executor import FieldImageApplication


_PROVIDER_VIEW_SEAL = object()


@dataclass(frozen=True, slots=True)
class PoweredFieldProviderView:
    """Constant-size capability for one complete powered field provider."""

    image: FieldImageID
    action: FieldCellActionID
    source: SourceBindingID
    geometry: FieldGeometryID
    signature: PortSignatureID
    incoming: ArenaHandle
    interface: LocalInterfaceID
    output: CoordinateOutputMorphismID
    extent_bound: int
    _application: FieldImageApplication
    _seal: object

    def __post_init__(self) -> None:
        if self._seal is not _PROVIDER_VIEW_SEAL:
            raise TypeError("powered provider views are issued by an application")
        if type(self.extent_bound) is not int or self.extent_bound < 0:
            raise ValueError("powered provider extent must be nonnegative")


def issue_powered_provider_view(
    application: FieldImageApplication,
) -> PoweredFieldProviderView:
    from number_compiler.hashlife.execution.field_executor import FieldImageApplication

    if type(application) is not FieldImageApplication:
        raise TypeError("provider view requires an issued field-image application")
    request = ImageRequestKey(
        application.action,
        application.source,
        application.geometry,
        application.signature,
    )
    application.executor.images.validate_request(request)
    application.executor.adapter.validate_port(application.incoming)
    image = application.executor.image(
        application.action,
        application.source,
        application.geometry,
        application.signature,
    )
    record = application.executor.images.resolve(image)
    application.executor.images.interfaces.resolve(record.interface)
    application.executor.images.validate_output(record.output)
    extent = (
        record.summary.extent_bound
        if isinstance(record.summary, ParametricFieldImageSummary)
        else record.summary.extent
    )
    return PoweredFieldProviderView(
        image,
        application.action,
        application.source,
        application.geometry,
        application.signature,
        application.incoming,
        record.interface,
        record.output,
        extent,
        application,
        _PROVIDER_VIEW_SEAL,
    )


def _validate_for_application(
    application: FieldImageApplication,
    view: PoweredFieldProviderView,
) -> FieldImageRecord:
    from number_compiler.hashlife.execution.field_executor import FieldImageApplication

    if type(application) is not FieldImageApplication:
        raise TypeError("provider observation requires a field-image application")
    if type(view) is not PoweredFieldProviderView:
        raise TypeError("expected a powered field provider view")
    if view._seal is not _PROVIDER_VIEW_SEAL or view._application is not application:
        raise ValueError("powered provider view belongs to another application")
    record = application.executor.images.resolve(view.image)
    extent = (
        record.summary.extent_bound
        if isinstance(record.summary, ParametricFieldImageSummary)
        else record.summary.extent
    )
    if type(view.extent_bound) is not int or view.extent_bound != extent:
        raise ValueError("powered provider extent disagrees with its image summary")
    if (
        view.action != application.action
        or view.source != application.source
        or view.geometry != application.geometry
        or view.signature != application.signature
        or view.incoming != application.incoming
        or view.interface != record.interface
        or view.output != record.output
    ):
        raise ValueError("powered provider view has inconsistent identities")
    application.executor.images.validate_request(
        ImageRequestKey(
            view.action,
            view.source,
            view.geometry,
            view.signature,
        )
    )
    application.executor.adapter.validate_port(view.incoming)
    application.executor.images.interfaces.resolve(view.interface)
    application.executor.images.validate_output(view.output)
    return record


def observe_provider_point(
    application: FieldImageApplication,
    view: PoweredFieldProviderView,
    position: int,
) -> int:
    if type(position) is not int:
        raise TypeError("field-image coordinate must be an exact integer")
    _validate_for_application(application, view)
    if not 0 <= position < view.extent_bound:
        raise IndexError(position)
    return application.executor.adapter.point_bound(
        view.image,
        view.source,
        view.incoming,
        position,
    )


def observe_provider_width(
    application: FieldImageApplication,
    view: PoweredFieldProviderView,
) -> int:
    _validate_for_application(application, view)
    result = application.executor.adapter.width_bound(
        view.image,
        view.source,
        view.incoming,
    )
    if type(result) is not int or not 0 <= result <= view.extent_bound:
        raise ValueError("powered provider width lies outside its extent")
    return result


def validate_powered_provider_view(view: object, ledger: object) -> bool:
    from number_compiler.hashlife.execution.field_capabilities import (
        validate_field_image_application,
    )

    if type(view) is not PoweredFieldProviderView:
        return False
    application = view._application
    if view._seal is not _PROVIDER_VIEW_SEAL or not validate_field_image_application(
        application, ledger
    ):
        return False
    try:
        _validate_for_application(application, view)
    except (TypeError, ValueError, IndexError):
        return False
    return True


__all__ = [
    "PoweredFieldProviderView",
    "issue_powered_provider_view",
    "observe_provider_point",
    "observe_provider_width",
    "validate_powered_provider_view",
]
