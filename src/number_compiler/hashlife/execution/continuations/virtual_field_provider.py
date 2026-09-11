"""Sealed executable providers for temporal-over-spatial composition.

The capability exposes the already verified concrete-port scheduler without
placing that executor, a boundary occurrence, or a source identity in a
semantic image record.  Consumers such as radix division can therefore absorb
the powered field one dyadic cell at a time instead of replaying scalar point
queries or materializing a midpoint word.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    PortAtom,
)
from number_compiler.hashlife.execution.continuations.concrete_port_scheduler import (
    ConcretePortScheduler,
)
from number_compiler.hashlife.execution.field_capabilities import (
    validate_field_image_application,
)
from number_compiler.hashlife.execution.field_executor import FieldImageApplication
from number_compiler.hashlife.execution.field_images import (
    SourceBindingID,
    SourceCellID,
)

_SEAL = object()


@dataclass(frozen=True, slots=True)
class VirtualFieldProvider:
    """Constant-size, occurrence-bound executable field provider."""

    action: FieldCellActionID
    source: SourceBindingID
    scheduler: ConcretePortScheduler
    application: FieldImageApplication
    _seal: object

    def __post_init__(self) -> None:
        if self._seal is not _SEAL:
            raise TypeError("virtual field providers are issued by the runtime")

    def _validate(self) -> None:
        if type(self.scheduler) is not ConcretePortScheduler or not (
            validate_virtual_field_provider(self, self.scheduler.ledger)
        ):
            raise ValueError("virtual field provider capability was altered")

    @source_reads_only
    def initial(self, side: int) -> PortAtom:
        self._validate()
        return self.scheduler.initial(self.action, side)

    @source_reads_only
    def advance(
        self,
        side: int,
        state: PortAtom,
        cell: SourceCellID,
        *,
        reverse: bool = False,
    ) -> PortAtom:
        self._validate()
        return self.scheduler.advance(
            self.action,
            side,
            state,
            cell,
            reverse=reverse,
        )

    @source_reads_only
    def emit(self, left: PortAtom, cell: SourceCellID, right: PortAtom) -> int:
        self._validate()
        return self.scheduler.emit(self.action, left, cell, right)

    @source_reads_only
    def point(self, coordinate: int) -> int:
        self._validate()
        return self.scheduler.point(self.action, self.source, coordinate)

    @source_reads_only
    def width(self) -> int:
        self._validate()
        return self.scheduler.width(self.action, self.source)


def issue_virtual_field_provider(
    application: FieldImageApplication,
) -> VirtualFieldProvider:
    """Issue a provider only for an adapter with the shared concrete scheduler."""
    if type(application) is not FieldImageApplication:
        raise TypeError("virtual provider requires a field-image application")
    if not validate_field_image_application(application, application.ledger):
        raise ValueError("field-image application failed scoped validation")
    scheduler = getattr(application.executor.adapter, "concrete_scheduler", None)
    if type(scheduler) is not ConcretePortScheduler:
        raise TypeError("field family has no executable virtual-provider scheduler")
    if scheduler.ledger is not application.ledger:
        raise ValueError("virtual-provider scheduler belongs to another index")
    if scheduler.sources is not application.executor.sources:
        raise ValueError("virtual-provider scheduler belongs to another source arena")
    scheduler.adapter.validate_action(application.action)
    scheduler.sources.binding_extent(application.source)
    application.ledger.bump("virtual_field_provider_capabilities")
    return VirtualFieldProvider(
        application.action,
        application.source,
        scheduler,
        application,
        _SEAL,
    )


def validate_virtual_field_provider(provider: object, ledger: object) -> bool:
    """Validate the sealed capability without trusting an adapter flag."""
    if type(provider) is not VirtualFieldProvider or provider._seal is not _SEAL:
        return False
    if type(provider.scheduler) is not ConcretePortScheduler:
        return False
    if provider.scheduler.ledger is not ledger:
        return False
    if not validate_field_image_application(provider.application, ledger):
        return False
    if (
        provider.action != provider.application.action
        or provider.source != provider.application.source
        or provider.scheduler.sources is not provider.application.executor.sources
        or provider.scheduler
        is not getattr(
            provider.application.executor.adapter,
            "concrete_scheduler",
            None,
        )
    ):
        return False
    try:
        provider.scheduler.adapter.validate_action(provider.action)
        provider.scheduler.sources.binding_extent(provider.source)
    except (TypeError, ValueError, IndexError):
        return False
    return True


__all__ = [
    "VirtualFieldProvider",
    "issue_virtual_field_provider",
    "validate_virtual_field_provider",
]
