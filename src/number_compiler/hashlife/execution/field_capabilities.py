"""Read-only validation of issued field applications and their interface wiring."""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.field_executor import FieldImageApplication
    from number_compiler.hashlife.execution.field_transfer import (
        FieldTransferApplication,
    )

from number_compiler.hashlife.execution.field_images import ImageRequestKey
from number_compiler.hashlife.execution.field_transfers import FieldTransferRequestKey
from number_compiler.resources.ledger import ResourceLedger


def validate_field_image_application(
    application: object,
    ledger: object,
) -> bool:
    """Verify the runtime-issued capability and every owning arena identity."""
    from number_compiler.hashlife.execution.field_executor import (
        _APPLICATION_SEAL,
        FieldImageApplication,
    )

    if type(application) is not FieldImageApplication:
        return False
    if not _application_owner_matches(application, ledger, _APPLICATION_SEAL):
        return False
    executor = application.executor
    if executor.images.sources is not executor.sources:
        return False
    try:
        executor.images.validate_request(
            ImageRequestKey(
                application.action,
                application.source,
                application.geometry,
                application.signature,
            )
        )
        executor.adapter.validate_port(application.incoming)
        if (
            executor.adapter.signature(application.action, application.geometry)
            != application.signature
        ):
            return False
    except (TypeError, ValueError, IndexError):
        return False
    return True


def validate_field_transfer_application(
    application: object,
    ledger: object,
) -> bool:
    """Verify a runtime-issued transfer capability and all scoped bindings."""
    from number_compiler.hashlife.execution.field_executor import (
        _TRANSFER_APPLICATION_SEAL,
    )
    from number_compiler.hashlife.execution.field_transfer import (
        FieldTransferApplication,
    )

    if type(application) is not FieldTransferApplication:
        return False
    if not _application_owner_matches(application, ledger, _TRANSFER_APPLICATION_SEAL):
        return False
    executor = application.executor
    try:
        executor.transfers.validate_request(
            FieldTransferRequestKey(
                application.action,
                application.source,
                application.geometry,
                application.signature,
            )
        )
        executor.adapter.validate_port(application.incoming)
    except (TypeError, ValueError, IndexError):
        return False
    return True


__all__ = ["validate_field_image_application", "validate_field_transfer_application"]


def register_field_application(ledger: ResourceLedger, application: object) -> None:
    """Register an issued application and initialize its common work columns."""
    from number_compiler.resources.metric_registry import ALGEBRAIC_FIELD_WORK_COUNTERS

    ledger.register_execution_root(application)
    for name in (
        *ALGEBRAIC_FIELD_WORK_COUNTERS,
        "diamond_temporal_composition_requests",
        "diamond_temporal_composition_hits",
        "diamond_temporal_composition_evaluations",
    ):
        ledger.bump(name, 0)
    ledger.bump("algebraic_executor_capability_validated")


def _application_owner_matches(
    application: FieldImageApplication | FieldTransferApplication,
    ledger: object,
    seal: object,
) -> bool:
    return (
        application._seal is seal
        and application.ledger is ledger
        and application.executor.ledger is ledger
    )
