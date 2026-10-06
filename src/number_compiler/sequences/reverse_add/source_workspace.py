"""Demand lifecycle for scheduler-owned reverse/add source images."""

from __future__ import annotations

from collections.abc import Iterator
from contextlib import ExitStack
from typing import cast

from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageDemand,
    SourceImageID,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_actions import (
    ReverseActionArena,
)
from number_compiler.sequences.reverse_add.successor_width import (
    ReverseSuccessorWidthSummary,
)


class ReverseSourceImageWorkspace:
    """Demanded reverse/add image bound to one original source and one action."""

    def __init__(
        self,
        ledger: ResourceLedger,
        seed: int,
        steps: int,
        *,
        base: int = 10,
        source_construction: OriginalSourceConstruction | None = None,
    ) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("reverse source workspace requires a resource ledger")
        seed = require_integer(seed, "seed", 0)
        steps = require_integer(steps, "reverse/add steps", 0)
        base = require_integer(base, "base", 2)
        if base == 10 and source_construction is not None:
            raise ValueError(
                "decimal source images do not consume recursive source authority"
            )
        self.ledger = ledger
        ledger.bump("temporal_point_requests", 0)
        ledger.bump("temporal_length_requests", 0)
        with ExitStack() as rollback:
            from number_compiler.sequences.reverse_add.source_images import (
                MAX_COMPLETED_CHILD_FALLBACK_STEPS,
                _ReverseSourceImageAdapter,
            )

            actions = ReverseActionArena(ledger)
            rollback.callback(actions.dispose)
            source = actions.admit_source(seed, base)
            root_action = actions.action(steps)
            scheduler = TileScheduler.source_only(ledger)
            rollback.callback(scheduler.dispose_source_images)
            adapter = _ReverseSourceImageAdapter(
                actions, successor_width_root=root_action
            )
            rollback.callback(adapter.dispose)
            if base != 10 and 3 <= steps <= MAX_COMPLETED_CHILD_FALLBACK_STEPS:
                adapter.prepare_recursive_authority(
                    actions.source(source), steps, source_construction
                )
            scheduler.register_source_image_adapter(adapter)
            rollback.pop_all()
        self.actions = actions
        self.source = source
        self.root_action = root_action
        self.scheduler = scheduler
        self.adapter = adapter
        self.steps = steps
        self.base = base
        self._image: SourceImageID | None = None
        self._width_image: SourceImageID | None = None
        self._image_cache_epoch = ledger.counters.get("source_image_cache_clears", 0)
        self._disposed = False
        self._authority = (
            ledger,
            actions,
            source,
            root_action,
            scheduler,
            adapter,
            steps,
            base,
            source_construction,
        )
        ledger.register_execution_root(self)
        self._audit_action_nodes = actions._nodes._data
        self._audit_action_normal = actions._normal._data
        self._audit_sources = actions._sources._data
        self._audit_action_workspace = actions._workspace
        self._audit_recursive_occurrences = adapter._recursive_occurrences._data
        self._audit_source_contract_key: (
            tuple[tuple[tuple[int, str, str], ...], tuple[int, ...]] | None
        ) = None
        self._register_source_payload_audit_contract()

    def _register_source_payload_audit_contract(self) -> None:
        from number_compiler.resources.payload_contracts import (
            PayloadAuditStoreBinding,
        )
        from number_compiler.sequences.reverse_add.source_audit_bindings import (
            bind_nested_source_stores,
        )
        from number_compiler.sequences.reverse_add.source_payload_audit import (
            audit_reverse_source_owner,
        )

        bindings = (
            PayloadAuditStoreBinding(
                self.actions._nodes.owner,
                "_audit_action_nodes",
                "reverse_source_action",
            ),
            PayloadAuditStoreBinding(
                self.actions._normal.owner,
                "_audit_action_normal",
                "reverse_source_action_normal_form",
            ),
            PayloadAuditStoreBinding(
                self.actions._sources.owner,
                "_audit_sources",
                "reverse_original_source",
            ),
            PayloadAuditStoreBinding(
                self.actions._workspace_owner,
                "_audit_action_workspace",
                "reverse_source_action_workspace",
            ),
            PayloadAuditStoreBinding(
                self.adapter._recursive_occurrences.owner,
                "_audit_recursive_occurrences",
                "reverse_recursive_occurrence_binding",
            ),
            *bind_nested_source_stores(self),
        )
        binding_key = tuple(
            (binding.owner, binding.attribute, binding.role) for binding in bindings
        )
        q19_owner = self.adapter._q19_owner
        dependencies = () if q19_owner is None else (q19_owner,)
        dependency_key = tuple(id(dependency) for dependency in dependencies)
        contract_key = (binding_key, dependency_key)
        if contract_key == self._audit_source_contract_key:
            return
        if self._audit_source_contract_key is not None:
            self.ledger.remove_payload_audit_contract(self, "reverse_add")
        self.ledger.register_payload_audit_contract(
            self,
            "reverse_add",
            bindings,
            audit_reverse_source_owner,
            dependencies=dependencies,
        )
        self._audit_source_contract_key = contract_key

    def _check_open(self, *, check_image: bool = True) -> None:
        if self._disposed:
            raise ValueError("disposed reverse source workspace")
        (
            ledger,
            actions,
            source,
            root_action,
            scheduler,
            adapter,
            steps,
            base,
            source_construction,
        ) = self._authority
        if (
            self.ledger is not ledger
            or self.actions is not actions
            or self.source != source
            or self.root_action != root_action
            or self.scheduler is not scheduler
            or self.adapter is not adapter
            or self.steps != steps
            or self.base != base
            or (
                source_construction is not None
                and adapter._recursive_construction is not source_construction
            )
            or adapter.actions is not actions
            or adapter.ledger is not ledger
            or scheduler.ledger is not ledger
        ):
            raise ValueError("reverse source workspace binding was altered")
        actions.source(source)
        actions.node(root_action)
        if actions.node(root_action).steps != steps:
            raise ValueError("reverse source workspace action was altered")
        cache_epoch = self.ledger.counters.get("source_image_cache_clears", 0)
        if cache_epoch != self._image_cache_epoch:
            self._image = None
            self._width_image = None
            self._image_cache_epoch = cache_epoch
        image = self._image
        if image is not None and check_image:
            view = scheduler._source_image_core().view(image)
            if view.binding.source != source or view.binding.action != root_action:
                raise ValueError("reverse source workspace image binding was altered")
        width_image = self._width_image
        if width_image is not None and check_image:
            view = scheduler._source_image_core().view(width_image)
            if view.binding.source != source or view.binding.action != actions.identity:
                raise ValueError("reverse source width image binding was altered")

    def completed_width_if_cached(self) -> int | None:
        """Return only a still-owned width projection; never demand one here."""
        self._check_open()
        image = self._image
        if image is not None:
            retained = self.scheduler.cached_source_projection(
                self.adapter, image, SourceImageDemand("width")
            )
            if retained is not None:
                if type(retained.value) is not int:
                    raise TypeError(
                        "reverse source width projection must be an integer"
                    )
                self._check_width_against_successor(retained.value)
                return retained.value
        successor = self._cached_successor_width_summary()
        return None if successor is None else successor.target_width

    def _cached_successor_width_summary(self) -> ReverseSuccessorWidthSummary | None:
        """Read a published scalar projection without creating an image or miss."""
        image = self._width_image
        if image is None:
            return None
        demand = SourceImageDemand("successor-width", (self.root_action, self.steps))
        retained = self.scheduler.cached_source_projection(self.adapter, image, demand)
        if retained is None:
            return None
        width_summary = retained.value
        if type(width_summary) is not ReverseSuccessorWidthSummary:
            raise TypeError("successor width projection lost its typed summary")
        if width_summary.steps != self.steps or width_summary.source_width != len(
            self.actions.source(self.source).digits
        ):
            raise ValueError("successor width projection belongs to another action")
        return width_summary

    def _check_width_against_successor(self, output_width: int) -> None:
        successor = self._cached_successor_width_summary()
        if successor is not None and output_width != successor.target_width:
            raise AssertionError(
                "completed output width disagrees with its cached successor projection"
            )

    def _demanded_image(self, demand: SourceImageDemand) -> SourceImageID:
        self._check_open()
        found = self._image
        if found is None:
            found = self.scheduler.source_image_demanded(
                self.adapter, self.source, self.root_action, demand
            )
            self._image = found
        self._register_source_payload_audit_contract()
        if self.base == 10 and self.steps >= 3:
            from number_compiler.sequences.reverse_add.source_images import (
                ReverseImagePayload,
            )

            view = self.scheduler._source_image_core().view(found)
            payload = cast(ReverseImagePayload, view.payload)
            pair_output = payload.pair_output
            if pair_output is not None:
                self._check_width_against_successor(pair_output.output_width)
            elif payload.occurrence is None and view.binding.precision is not None:
                self._check_width_against_successor(view.binding.precision)
        return found

    def _source_origin_image(self) -> SourceImageID:
        """Return the source image used by scheduler-owned scalar projections."""
        self._check_open()
        found = self._width_image
        if found is None:
            found = self.scheduler.source_origin_image(self.adapter, self.source)
            self._width_image = found
        return found

    @property
    def operator_nodes(self) -> int:
        return self.actions.operator_nodes

    @property
    def compose_operations(self) -> int:
        return self.actions.compose_operations

    @property
    def syntax_depth_bound(self) -> int:
        return self.actions.node(self.root_action).depth

    def digit(self, position: int) -> int:
        position = require_integer(position, "digit coordinate")
        self._check_open()
        self.ledger.bump("temporal_point_requests")
        if (
            self.base == 10
            and self.steps >= 3
            and self.actions.source(self.source).digits == (0,)
        ):
            if position != 0:
                raise IndexError(position)
            return 0
        demand = SourceImageDemand("digit", (position,))
        image = self._demanded_image(demand)
        return cast(
            int, self.scheduler.source_projection(self.adapter, image, demand).value
        )

    def width(self) -> int:
        self.ledger.bump("temporal_length_requests")
        if self.base == 10 and self.steps >= 3:
            self._check_open()
            if self._image is not None:
                demand = SourceImageDemand("width")
                projection = self.scheduler.source_projection(
                    self.adapter, self._image, demand
                )
                if type(projection.value) is not int:
                    raise TypeError(
                        "reverse source width projection must be an integer"
                    )
                self._check_width_against_successor(projection.value)
                return projection.value
            demand = SourceImageDemand(
                "successor-width", (self.root_action, self.steps)
            )
            image = self._source_origin_image()
            projection = self.scheduler.source_projection(self.adapter, image, demand)
            width_summary = projection.value
            if type(width_summary) is not ReverseSuccessorWidthSummary:
                raise TypeError("successor width projection lost its typed summary")
            if width_summary is not self._cached_successor_width_summary():
                raise ValueError("successor width projection publication changed")
            return width_summary.target_width
        demand = SourceImageDemand("width")
        image = self._demanded_image(demand)
        projection = self.scheduler.source_projection(self.adapter, image, demand)
        if type(projection.value) is not int:
            raise TypeError("reverse source width projection must be an integer")
        return projection.value

    def iter_digits(self) -> Iterator[int]:
        from number_compiler.sequences.reverse_add.source_images import (
            ReverseImagePayload,
        )

        self._check_open()
        if (
            self.base == 10
            and self.steps >= 3
            and self.actions.source(self.source).digits == (0,)
        ):
            yield 0
            return
        image = self._demanded_image(SourceImageDemand("width"))
        view = self.scheduler._source_image_core().view(image)
        payload = cast(ReverseImagePayload, view.payload)
        if payload.pair_output is not None:
            owner = self.adapter._q19_owner
            if owner is None:
                raise ValueError("decimal pair output owner was disposed")
            yield from owner.iter_digits(payload.pair_output)
            return
        if self.steps == 0:
            yield from self.actions.source(self.source).digits
            return
        if self.steps == 2:
            yield from self.adapter.iter_second_digits(self.actions.source(self.source))
            return
        if self.steps >= 3:
            recursive = self.adapter._recursive_for_steps(self.steps)
            if recursive is not None:
                cutover, occurrence = recursive
                yield from cutover.iter_digits(occurrence)
                return
            yield from self.adapter.iter_same_carry_digits(
                self.actions.source(self.source), self.steps
            )
            return
        yield from self.adapter.iter_primitive_digits(self.actions.source(self.source))

    def dispose(self) -> None:
        if self._disposed:
            return
        scheduler = self._authority[4]
        actions = self._authority[1]
        try:
            try:
                scheduler.dispose_source_images()
            finally:
                try:
                    self._authority[5].dispose()
                finally:
                    actions.dispose()
        finally:
            self._image = None
            self._width_image = None
            self._disposed = True


__all__ = ["ReverseSourceImageWorkspace"]
