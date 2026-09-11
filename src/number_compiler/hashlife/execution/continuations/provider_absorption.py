"""Scoped provider actions and source-bound observation memos.

The semantic provider key contains only the canonical coordinate morphism,
complete local interface, temporal action, and bounded geometry. Exact source
occurrences and concrete boundary values are confined to evictable bindings
and observations. This is the publication boundary used by the iterative
spacetime absorber; it is deliberately not another field-image arena.
"""

from __future__ import annotations

from collections.abc import Callable, MutableMapping
from dataclasses import dataclass
from typing import TypeAlias

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeValueID,
)
from number_compiler.hashlife.execution.field_images import (
    FieldImageID,
    FieldImageRecord,
    SourceBindingID,
    SourceCellArena,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.resources.ledger import ResourceLedger

ProviderBoundary: TypeAlias = int | ArenaHandle


@dataclass(frozen=True, slots=True)
class ProviderActionID(ArenaHandle):
    """Scoped identity of one unbound canonical provider action."""


@dataclass(frozen=True, slots=True)
class ProviderAction:
    output: CoordinateOutputMorphismID
    interface: LocalInterfaceID
    action: FieldCellActionID
    orientation: int
    phase: int
    phase_count: int = 1

    def __post_init__(self) -> None:
        if type(self.orientation) is not int or self.orientation not in (0, 1):
            raise ValueError("provider orientation must be bounded")
        if type(self.phase) is not int or type(self.phase_count) is not int:
            raise TypeError("provider phase requires exact bounded integers")
        if not 1 <= self.phase_count <= 64:
            raise ValueError("provider phase domain exceeds its bounded interface")
        if not 0 <= self.phase < self.phase_count:
            raise ValueError("provider phase is outside its normalized domain")


@dataclass(frozen=True, slots=True)
class ProviderBindingKey:
    provider: ProviderActionID
    source: SourceBindingID
    output: CoordinateOutputMorphismID
    interface: LocalInterfaceID
    image: FieldImageID | None = None


@dataclass(frozen=True, slots=True)
class _PointKey:
    binding: ProviderBindingKey
    left: ProviderBoundary
    right: ProviderBoundary
    coordinate: int


class ProviderAbsorptionArena:
    """Canonical providers with evictable, boundary-bound observations."""

    _KIND = "provider-action"

    def __init__(
        self,
        ledger: ResourceLedger,
        sources: SourceCellArena,
        *,
        validate_output: Callable[[CoordinateOutputMorphismID], object],
        validate_bound_output: Callable[[CoordinateOutputMorphismID], object],
        validate_interface: Callable[[LocalInterfaceID], object],
        validate_bound_interface: Callable[[LocalInterfaceID], object],
        validate_action: Callable[[FieldCellActionID], object],
        validate_boundary: Callable[[ProviderBoundary], object],
        observe: Callable[[CoordinateOutputMorphismID, int, object, object], int],
        validate_image: Callable[[FieldImageID], FieldImageRecord] | None = None,
        validate_image_occurrence: Callable[
            [FieldImageID, SourceBindingID, FieldCellActionID], None
        ]
        | None = None,
    ) -> None:
        if sources.ledger is not ledger:
            raise ValueError("provider absorption requires one index ledger")
        if not all(
            callable(item)
            for item in (
                validate_output,
                validate_bound_output,
                validate_interface,
                validate_bound_interface,
                validate_action,
                validate_boundary,
                observe,
            )
        ):
            raise TypeError("provider absorption requires executable validators")
        self.ledger, self.sources = ledger, sources
        self._validate_output = validate_output
        self._validate_bound_output = validate_bound_output
        self._validate_interface = validate_interface
        self._validate_bound_interface = validate_bound_interface
        self._validate_action = validate_action
        self._validate_boundary = validate_boundary
        self._observe = observe
        if validate_image is not None and not callable(validate_image):
            raise TypeError("provider image validation must be executable")
        if validate_image_occurrence is not None and not callable(
            validate_image_occurrence,
        ):
            raise TypeError("provider image occurrence validation must be executable")
        self._validate_image = validate_image
        if (validate_image is None) != (validate_image_occurrence is None):
            raise ValueError(
                "provider image record and occurrence validation require one another"
            )
        self._validate_image_occurrence = validate_image_occurrence
        self.owner = ArenaToken("provider-actions")
        ledger.register_execution_root(self)
        prefix = f"provider-actions-{len(ledger.inventory())}"
        self._node_owner = ledger.register(prefix + "-nodes", "provider_action")
        self._key_owner = ledger.register(prefix + "-keys", "provider_action_interner")
        self._binding_owner = ledger.register(prefix + "-bindings", "spatial_binding")
        self._point_owner = ledger.register(prefix + "-points", "observation_memo")
        self._nodes: MutableMapping[int, ProviderAction] = ledger.make_dict(
            self._node_owner,
            nodes_per_entry=1,
        )
        self._keys: MutableMapping[ProviderAction, int] = ledger.make_dict(
            self._key_owner
        )
        self._bindings: MutableMapping[ProviderBindingKey, None] = ledger.make_dict(
            self._binding_owner,
        )
        self._points: MutableMapping[_PointKey, int] = ledger.make_dict(
            self._point_owner
        )
        for owner, container, nodes, evict in (
            (self._node_owner, self._nodes, True, None),
            (self._key_owner, self._keys, False, None),
            (self._binding_owner, self._bindings, False, self.clear_observations),
            (self._point_owner, self._points, False, self.clear_observations),
        ):
            ledger.register_container(
                owner,
                container,
                node_count=(lambda: len(self._nodes)) if nodes else None,
                payloads=container.items,
                evict=evict,
            )
        self._next_id = 0

    def _validate_image_binding(
        self,
        image: FieldImageID,
        source: SourceBindingID,
        action: FieldCellActionID,
        output: CoordinateOutputMorphismID,
        interface: LocalInterfaceID,
    ) -> FieldImageRecord:
        """Prove that an occurrence names the supplied completed behavior."""
        if type(image) is not FieldImageID or self._validate_image is None:
            raise TypeError("provider image binding requires an issued image validator")
        record = self._validate_image(image)
        if type(record) is not FieldImageRecord:
            raise TypeError("provider image validator returned another record sort")
        if record.output != output or record.interface != interface:
            raise ValueError("provider occurrence differs from its completed image")
        occurrence = self._validate_image_occurrence
        if occurrence is None:
            raise TypeError("provider image occurrence validation is not configured")
        occurrence(image, source, action)
        return record

    def clear_observations(self) -> None:
        # Provider-image occurrences depend on these bindings.  Invalidate
        # them first so a warm child ID can never outlive its authority.
        from number_compiler.hashlife.execution.continuations.provider_image_input import (
            ProviderImageInputArena,
        )

        for root in tuple(self.ledger.iter_execution_roots()):
            if type(root) is ProviderImageInputArena and root.providers is self:
                root.clear()
        bindings, points = len(self._bindings), len(self._points)
        self._bindings.clear()
        self._points.clear()
        self.ledger.release(self._binding_owner, entries=bindings)
        self.ledger.release(self._point_owner, entries=points)

    def _clear_points(self) -> None:
        count = len(self._points)
        self._points.clear()
        self.ledger.release(self._point_owner, entries=count)

    def _handle(self, local_id: int) -> ProviderActionID:
        return ProviderActionID(self.owner, self._KIND, local_id)

    def resolve(self, provider: ProviderActionID) -> ProviderAction:
        if type(provider) is not ProviderActionID:
            raise TypeError("expected a scoped provider action ID")
        provider.validate(self.owner, self._KIND, size=self._next_id)
        try:
            return self._nodes[provider.local_id]
        except KeyError as exc:
            raise ValueError("stale provider action ID") from exc

    def intern(self, record: ProviderAction) -> ProviderActionID:
        if type(record) is not ProviderAction:
            raise TypeError("provider publication requires canonical metadata")
        record.__post_init__()
        if type(record.output) is not CoordinateOutputMorphismID:
            raise TypeError("provider action requires a coordinate output program")
        if type(record.interface) is not LocalInterfaceID:
            raise TypeError("provider action requires a bounded local interface")
        if type(record.action) is not FieldCellActionID:
            raise TypeError("provider action requires a scoped temporal action")
        self._validate_output(record.output)
        self._validate_interface(record.interface)
        self._validate_action(record.action)
        found = self._keys.get(record)
        if found is not None:
            self.ledger.bump("provider_action_alias_hits")
            return self._handle(found)
        self.ledger.reserve_many(
            ((self._node_owner, 1, 1), (self._key_owner, 1, 0)),
        )
        local_id = self._next_id
        self._next_id += 1
        self._nodes[local_id] = record
        self._keys[record] = local_id
        self.ledger.bump("provider_action_publications")
        return self._handle(local_id)

    def bind(
        self,
        provider: ProviderActionID,
        source: SourceBindingID,
        output: CoordinateOutputMorphismID,
        interface: LocalInterfaceID,
        image: FieldImageID | None = None,
    ) -> ProviderBindingKey:
        return self.bind_many(((provider, source, output, interface, image),))[0]

    def bind_many(
        self,
        requests: tuple[
            tuple[
                ProviderActionID,
                SourceBindingID,
                CoordinateOutputMorphismID,
                LocalInterfaceID,
                FieldImageID | None,
            ],
            ...,
        ],
    ) -> tuple[ProviderBindingKey, ...]:
        """Validate and atomically publish several occurrence bindings."""
        keys = self._prepare_bindings(requests)
        missing = tuple(dict.fromkeys(key for key in keys if key not in self._bindings))
        self.ledger.reserve(self._binding_owner, entries=len(missing))
        self._publish_prepared_bindings(missing)
        return keys

    def _prepare_bindings(
        self,
        requests: tuple[
            tuple[
                ProviderActionID,
                SourceBindingID,
                CoordinateOutputMorphismID,
                LocalInterfaceID,
                FieldImageID | None,
            ],
            ...,
        ],
    ) -> tuple[ProviderBindingKey, ...]:
        """Purely validate a batch before a caller reserves associated stores."""
        if type(requests) is not tuple:
            raise TypeError("provider binding batch must be canonical")
        keys: list[ProviderBindingKey] = []
        for provider, source, output, interface, image in requests:
            self.resolve(provider)
            self.sources.binding_extent(source)
            if type(output) is not CoordinateOutputMorphismID:
                raise TypeError(
                    "provider binding requires a coordinate output morphism"
                )
            if type(interface) is not LocalInterfaceID:
                raise TypeError("provider binding requires a bounded local interface")
            self._validate_bound_output(output)
            self._validate_bound_interface(interface)
            if image is not None:
                action = self.resolve(provider).action
                self._validate_image_binding(image, source, action, output, interface)
            keys.append(ProviderBindingKey(provider, source, output, interface, image))
        return tuple(keys)

    def _publish_prepared_bindings(
        self,
        missing: tuple[ProviderBindingKey, ...],
    ) -> None:
        """Publish a prevalidated, already-reserved occurrence batch."""
        for key in missing:
            self._bindings[key] = None

    def point(
        self,
        binding: ProviderBindingKey,
        left: ProviderBoundary,
        right: ProviderBoundary,
        coordinate: int,
    ) -> int:
        if type(binding) is not ProviderBindingKey or type(coordinate) is not int:
            raise TypeError("provider observation requires scoped exact inputs")
        if coordinate < 0:
            raise IndexError(coordinate)
        self.validate_binding(binding, left, right)
        key = _PointKey(binding, left, right, coordinate)
        found = self._points.get(key)
        if found is not None:
            self.ledger.bump("provider_observation_hits")
            return found
        result = self._observe(binding.output, coordinate, left, right)
        if type(result) is not int:
            raise ValueError("provider observation returned a structured value")
        self._clear_points()
        if type(left) is RuntimeValueID or type(right) is RuntimeValueID:
            self.ledger.bump("provider_observation_uncacheable_boundaries")
            self.ledger.bump("provider_observation_evaluations")
            return result
        # Higher observations may evict their transient RuntimeValueIDs while
        # producing the scalar. Never retain a response key whose boundary
        # handles became stale during evaluation: it cannot be a valid warm
        # hit and would keep historical query identity in the object graph.
        try:
            self._validate_boundary(left)
            self._validate_boundary(right)
        except (TypeError, ValueError, IndexError):
            self.ledger.bump("provider_observation_uncacheable_boundaries")
            self.ledger.bump("provider_observation_evaluations")
            return result
        self.ledger.reserve(self._point_owner, entries=1)
        self._points[key] = result
        self.ledger.bump("provider_observation_evaluations")
        return result

    def validate_binding(
        self,
        binding: ProviderBindingKey,
        left: ProviderBoundary,
        right: ProviderBoundary,
    ) -> ProviderAction:
        """Validate occurrence and concrete ports before any memo probe."""
        if type(binding) is not ProviderBindingKey:
            raise TypeError("provider observation requires a scoped binding")
        record = self.resolve(binding.provider)
        self.sources.binding_extent(binding.source)
        if type(binding.output) is not CoordinateOutputMorphismID:
            raise TypeError("provider binding requires a coordinate output morphism")
        if type(binding.interface) is not LocalInterfaceID:
            raise TypeError("provider binding requires a bounded local interface")
        self._validate_bound_output(binding.output)
        self._validate_bound_interface(binding.interface)
        if binding.image is not None:
            self._validate_image_binding(
                binding.image,
                binding.source,
                record.action,
                binding.output,
                binding.interface,
            )
        self._validate_boundary(left)
        self._validate_boundary(right)
        if binding not in self._bindings:
            raise ValueError("provider source binding was not published")
        return record

    def validate_occurrence(self, binding: ProviderBindingKey) -> ProviderAction:
        """Validate a completed provider occurrence without binding its ports."""
        if type(binding) is not ProviderBindingKey:
            raise TypeError("expected a scoped provider occurrence")
        record = self.resolve(binding.provider)
        self.sources.binding_extent(binding.source)
        if type(binding.output) is not CoordinateOutputMorphismID:
            raise TypeError("provider binding requires a coordinate output morphism")
        if type(binding.interface) is not LocalInterfaceID:
            raise TypeError("provider binding requires a bounded local interface")
        self._validate_bound_output(binding.output)
        self._validate_bound_interface(binding.interface)
        if binding.image is None:
            raise TypeError("completed provider occurrence requires a field image")
        self._validate_image_binding(
            binding.image,
            binding.source,
            record.action,
            binding.output,
            binding.interface,
        )
        if binding not in self._bindings:
            raise ValueError("provider occurrence was not published")
        return record


__all__ = [
    "ProviderAbsorptionArena",
    "ProviderAction",
    "ProviderActionID",
    "ProviderBindingKey",
    "ProviderBoundary",
]
