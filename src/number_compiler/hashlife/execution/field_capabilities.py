"""Read-only validation of issued field applications and their interface wiring."""

from __future__ import annotations

from number_compiler.hashlife.execution.field_images import ImageRequestKey
from number_compiler.hashlife.execution.field_transfers import FieldTransferRequestKey


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
    if application._seal is not _APPLICATION_SEAL or application.ledger is not ledger:
        return False
    executor = application.executor
    if executor.ledger is not ledger or executor.images.sources is not executor.sources:
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
    if (
        application._seal is not _TRANSFER_APPLICATION_SEAL
        or application.ledger is not ledger
    ):
        return False
    executor = application.executor
    if executor.ledger is not ledger:
        return False
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
