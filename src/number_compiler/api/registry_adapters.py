"""Resolve typed registry adapters only for the demanded family operation."""

from __future__ import annotations

from dataclasses import dataclass
from importlib import import_module
from inspect import signature

from number_compiler.api import family_registry
from number_compiler.api.family_types import (
    AdmitObserver,
    ObserveObserver,
    PrepareObserver,
    ProjectionAdapter,
    VerificationAdapter,
)
from number_compiler.api.observation_types import ObservationId
from number_compiler.api.query_types import ExecutionQuery, TermQuery
from number_compiler.arithmetic.contracts.family_identity import FamilyId


def _accepts_positional_arguments(value: object, count: int) -> bool:
    """Reject stale registry bindings before exposing them to execution code."""
    if not callable(value):
        return False
    try:
        signature(value).bind(*(object() for _ in range(count)))
    except (TypeError, ValueError):
        return False
    return True


def resolve_projection_adapter(query: TermQuery) -> ProjectionAdapter:
    """Load only the projection code for the already-selected family query."""
    family = getattr(query, "family", None)
    spec = (
        family_registry.CAPABILITIES.get(family) if type(family) is FamilyId else None
    )
    if spec is None or type(query) is not spec.query_type:
        raise TypeError("unsupported family query type")
    binding = spec.projection
    adapter: object = getattr(import_module(binding.module), binding.attribute)
    if not isinstance(adapter, ProjectionAdapter) or not _accepts_positional_arguments(
        adapter, 2
    ):
        raise TypeError("registered projection adapter has an incompatible interface")
    return adapter


@dataclass(frozen=True, slots=True)
class ResolvedObservationAdapter:
    prepare: PrepareObserver
    admit: AdmitObserver
    observe: ObserveObserver


def resolve_observation_adapter(
    family: FamilyId,
    identifier: ObservationId | None = None,
) -> ResolvedObservationAdapter:
    if type(family) is not FamilyId:
        raise TypeError("observation lookup requires an admitted FamilyId")
    if identifier is not None and type(identifier) is not ObservationId:
        raise TypeError("observation lookup requires an admitted ObservationId")
    specification = family_registry.family_spec(family)
    if identifier is None:
        binding = specification.observation
    else:
        selected = next(
            (
                item
                for item in specification.observation_specs
                if item.identifier is identifier
            ),
            None,
        )
        if selected is None or selected.adapter is None:
            raise ValueError(
                f"observation is not registered for {family}: {identifier}"
            )
        binding = selected.adapter
    module = import_module(binding.module)
    prepare: object = getattr(module, binding.prepare)
    admit: object = getattr(module, binding.admit)
    observe: object = getattr(module, binding.observe)
    if not isinstance(prepare, PrepareObserver) or not _accepts_positional_arguments(
        prepare, 2
    ):
        raise TypeError("registered prepare adapter has an incompatible interface")
    if not isinstance(admit, AdmitObserver) or not _accepts_positional_arguments(
        admit, 1
    ):
        raise TypeError("registered admission adapter has an incompatible interface")
    if not isinstance(observe, ObserveObserver) or not _accepts_positional_arguments(
        observe, 2
    ):
        raise TypeError("registered observation adapter has an incompatible interface")
    return ResolvedObservationAdapter(
        prepare,
        admit,
        observe,
    )


def resolve_verification_adapter(query: ExecutionQuery) -> VerificationAdapter:
    """Load the selected family's verifier for its exact typed query."""
    spec = family_registry.family_spec(query.family)
    if spec.verify_query_type is None or type(query) is not spec.verify_query_type:
        raise TypeError("unsupported certificate verification query type")
    binding = spec.verification
    if binding is None:
        raise ValueError("family has no certificate verifier")
    verifier: object = getattr(import_module(binding.module), binding.attribute)
    if not isinstance(
        verifier, VerificationAdapter
    ) or not _accepts_positional_arguments(verifier, 1):
        raise TypeError("registered verifier has an incompatible interface")
    return verifier
