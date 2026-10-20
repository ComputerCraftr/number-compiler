"""Shared source-image adapter for one bounded Antihydra section cylinder."""

from __future__ import annotations

from collections.abc import Hashable, MutableSequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, Final, cast

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
    SourceBoundSchedulerCore,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageBinding,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import ResourceInventory, ResourceLedger
from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
from number_compiler.sequences.antihydra.blocks import ArithmeticCylinder
from number_compiler.sequences.antihydra.projection_audit_state import (
    ProjectionAdapterAuditState,
    ProjectionStoreState,
)
from number_compiler.sequences.antihydra.projection_fragments import (
    ProjectionFragment,
    ProjectionFragmentCache,
    ProjectionFragmentKey,
    projection_key_snapshot,
)
from number_compiler.sequences.antihydra.projection_occurrences import (
    ProjectionBlockImage,
    ProjectionOccurrence,
    ProjectionOccurrenceCursor,
    ProjectionOccurrenceID,
)

ANTIHYDRA_SECTION_FRAGMENT_VERSION: Final[str] = "section-fragment-v2"

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.observers import SpaceTimeProjection


@dataclass(frozen=True, slots=True)
class AntihydraFragmentID(ArenaHandle):
    """Scoped payload handle for a composed demanded fragment."""


@dataclass(frozen=True, slots=True)
class AntihydraFragmentSourceID(ArenaHandle):
    """Scoped authority for one independently sealed projection source."""


@dataclass(frozen=True, slots=True)
class AntihydraFragmentAction:
    offset: int
    width: int


@dataclass(frozen=True, slots=True)
class _FragmentRecord:
    consumed: int
    image: ProjectionBlockImage | None


class AntihydraFragmentAdapter(SourceBoundImageAdapter):
    family = "antihydra"
    semantic_version = ANTIHYDRA_SECTION_FRAGMENT_VERSION

    def __init__(
        self,
        ledger: ResourceLedger,
    ) -> None:
        self.ledger = ledger
        self.projection: SpaceTimeProjection | None = None
        self.key: ProjectionFragmentKey | None = None
        self.block: ArithmeticCylinder | None = None
        self._cursor: ProjectionOccurrenceCursor | None = None
        self._occurrence: ProjectionOccurrenceID | None = None
        self._section_capacity = 0
        self._source_h = self._source_balance = 0
        self._source_token: ArenaToken | None = None
        self._source_kind = "antihydra-projection-source"
        self._token = ArenaToken("antihydra-projection-fragments")
        self._kind = "antihydra-projection-fragment"
        self._owner = self.ledger.register(
            f"antihydra.spacetime.core-fragments.{len(self.ledger.inventory())}",
            "demanded_projection",
        )
        self._records: MutableSequence[_FragmentRecord] = self.ledger.make_list(
            self._owner, append_only=False
        )
        self._seal_owner = self.ledger.register(
            f"antihydra.spacetime.core-fragment-seals.{len(self.ledger.inventory())}",
            "projection_binding",
        )
        self._seals: MutableSequence[tuple[object, ...]] = self.ledger.make_list(
            self._seal_owner, append_only=False
        )
        self._source_seal_owner = self.ledger.register(
            f"antihydra.spacetime.core-source-seals.{len(self.ledger.inventory())}",
            "projection_binding",
        )
        self._source_seals: MutableSequence[tuple[object, ...]] = self.ledger.make_list(
            self._source_seal_owner, append_only=False
        )
        self.ledger.register_container(
            self._owner,
            self._records,
            node_count=lambda: sum(
                self._record_nodes(record) for record in self._records
            ),
            payloads=self._records.__iter__,
        )
        self.ledger.register_container(
            self._seal_owner,
            self._seals,
            node_count=lambda: sum(self._seal_nodes(seal) for seal in self._seals),
            payloads=self._seals.__iter__,
        )
        self.ledger.register_container(
            self._source_seal_owner,
            self._source_seals,
            node_count=lambda: 20 * len(self._source_seals),
            payloads=self._source_seals.__iter__,
        )
        self.ledger.register_execution_root(self)
        from number_compiler.sequences.antihydra.payload_audit import (
            register_antihydra_payload_contract,
        )

        register_antihydra_payload_contract(self)

    def audit_snapshot(self) -> ProjectionAdapterAuditState:
        return ProjectionAdapterAuditState(
            (
                ProjectionStoreState(
                    self._owner, "_records", "demanded_projection", self._records
                ),
                ProjectionStoreState(
                    self._seal_owner, "_seals", "projection_binding", self._seals
                ),
                ProjectionStoreState(
                    self._source_seal_owner,
                    "_source_seals",
                    "projection_binding",
                    self._source_seals,
                ),
            ),
            self.projection is None
            and self.key is None
            and self.block is None
            and self._cursor is None
            and self._occurrence is None
            and self._source_h == self._source_balance == 0
            and self._section_capacity == 0
            and self._source_token is None
            and not self._records
            and not self._seals
            and not self._source_seals,
            type(self._token) is ArenaToken,
        )

    def configure(
        self,
        cursor: ProjectionOccurrenceCursor,
        occurrence: ProjectionOccurrenceID,
        section_capacity: int,
    ) -> None:
        if self.projection is not None or self._records:
            raise RuntimeError("Antihydra fragment driver is already in use")
        if type(cursor) is not ProjectionOccurrenceCursor:
            raise TypeError("Antihydra fragment requires its source occurrence cursor")
        record = cursor.materialize_image(occurrence)
        projection = cursor.projection
        if projection is None:
            raise ValueError("Antihydra fragment requires an active source occurrence")
        if projection.result.ledger is not self.ledger:
            raise ValueError("Antihydra fragment driver belongs to another ledger")
        key, block, h, balance = record.key, record.block, record.h, record.balance
        self.ledger.reserve(self._source_seal_owner, entries=1, nodes=20)
        try:
            self._source_seals.append((*projection_key_snapshot(key), h, balance))
        except BaseException:
            self.ledger.release(self._source_seal_owner, entries=1, nodes=20)
            raise
        self.projection, self.key, self.block = projection, key, block
        self._cursor, self._occurrence = cursor, occurrence
        self._source_h, self._source_balance = h, balance
        self._section_capacity = section_capacity
        self._source_token = ArenaToken("antihydra-projection-source")

    def source(self) -> AntihydraFragmentSourceID:
        self._context()
        if self._source_token is None:
            raise RuntimeError("Antihydra fragment source authority is inactive")
        return AntihydraFragmentSourceID(self._source_token, self._source_kind, 0)

    def _active_occurrence(self) -> ProjectionOccurrence:
        if self._cursor is None or self._occurrence is None:
            raise ValueError("Antihydra fragment lost its source occurrence")
        return self._cursor.resolve(self._occurrence)

    def _context(
        self,
    ) -> tuple[SpaceTimeProjection, ProjectionFragmentKey, ArithmeticCylinder]:
        if self.projection is None or self.key is None or self.block is None:
            raise RuntimeError("Antihydra fragment driver has no active source")
        if self._cursor is None or self._occurrence is None:
            raise ValueError("Antihydra fragment lost its source occurrence")
        record = self._cursor.resolve(self._occurrence)
        if (
            type(self._source_h) is not int
            or type(self._source_balance) is not int
            or self._cursor.projection is not self.projection
            or record.key is not self.key
            or record.block is not self.block
            or (self._source_h, self._source_balance) != (record.h, record.balance)
        ):
            raise ValueError("Antihydra fragment source occurrence was changed")
        return self.projection, self.key, self.block

    @staticmethod
    def _record_seal(record: _FragmentRecord) -> tuple[object, ...]:
        return (
            record.consumed,
            None
            if record.image is None
            else (
                record.image.source_h,
                record.image.source_balance,
                record.image.output_h,
                record.image.output_balance,
                record.image.head_delta,
                record.image.time_delta,
                record.image.classes,
            ),
        )

    @staticmethod
    def _image_nodes(image: ProjectionBlockImage | None) -> int:
        # ProjectionOccurrence owns the immutable image and its class tuple.
        # Fragment records retain only the image reference.
        return 0 if image is None else 1

    @classmethod
    def _record_nodes(cls, record: _FragmentRecord) -> int:
        return 1 + cls._image_nodes(record.image)

    @classmethod
    def _seal_nodes(cls, seal: tuple[object, ...]) -> int:
        if not is_exact_object_tuple(seal):
            return 1
        image = seal[-1]
        image_nodes = 0
        if (
            is_exact_object_tuple(image)
            and len(image) == 7
            and is_exact_object_tuple(image[-1])
        ):
            # The seal copies the seven-field wrapper and refers to the class
            # tuple already charged by the occurrence owner.
            image_nodes = 8
        return 1 + image_nodes

    def scoped_handle(self, record: _FragmentRecord) -> AntihydraFragmentID:
        _projection, _key, _block = self._context()
        seal = self._record_seal(record)
        nodes = self._record_nodes(record)
        seal_nodes = self._seal_nodes(seal)
        local_id = len(self._records)
        self.ledger.reserve_many(
            ((self._owner, 1, nodes), (self._seal_owner, 1, seal_nodes))
        )
        try:
            self._records.append(record)
            self._seals.append(seal)
        except BaseException:
            if len(self._records) > local_id:
                self._records.pop()
            if len(self._seals) > local_id:
                self._seals.pop()
            self.ledger.release(self._owner, entries=1, nodes=nodes)
            self.ledger.release(self._seal_owner, entries=1, nodes=seal_nodes)
            raise
        return AntihydraFragmentID(self._token, self._kind, local_id)

    def resolve(self, reference: AntihydraFragmentID) -> _FragmentRecord:
        if type(reference) is not AntihydraFragmentID:
            raise TypeError("expected an Antihydra fragment handle")
        reference.validate(self._token, self._kind, size=len(self._records))
        record = self._records[reference.local_id]
        if type(record) is not _FragmentRecord:
            raise ValueError("Antihydra fragment payload was changed")
        if record.image is not None:
            if (
                type(record.image) is not ProjectionBlockImage
                or type(self.key) is not ProjectionFragmentKey
                or type(self.block) is not ArithmeticCylinder
            ):
                raise ValueError("Antihydra fragment payload was changed")
            record.image.validate(self.key, self.block.width)
        if self._seals[reference.local_id] != self._record_seal(record):
            raise ValueError("Antihydra fragment payload was changed")
        return record

    def validate_source(self, source: Hashable) -> None:
        _projection, key, _block = self._context()
        if type(source) is not AntihydraFragmentSourceID or self._source_token is None:
            raise ValueError("Antihydra fragment has another source authority")
        source.validate(self._source_token, self._source_kind, size=1)
        if len(self._source_seals) != 1 or self._source_seals[0] != (
            *projection_key_snapshot(key),
            self._source_h,
            self._source_balance,
        ):
            raise ValueError("Antihydra fragment source binding was changed")

    def validate_action(self, action: Hashable) -> None:
        _projection, _key, block = self._context()
        if type(action) is not AntihydraFragmentAction:
            raise TypeError("Antihydra fragment requires its interval action")
        if (
            action.offset < 0
            or action.width < 0
            or action.offset + action.width > block.width
        ):
            raise ValueError("Antihydra fragment action leaves its source cylinder")

    def validate_payload(self, payload: Hashable) -> None:
        self.resolve(cast(AntihydraFragmentID, payload))

    def audit_image_binding(
        self,
        binding: SourceImageBinding,
        payload: Hashable,
        failure_prefix: Hashable | None,
    ) -> None:
        """Check the fragment's source/action extent without rebuilding it."""
        if type(binding) is not SourceImageBinding:
            raise TypeError("Antihydra image audit requires its exact binding")
        self.validate_source(binding.source)
        self.validate_action(binding.action)
        self.validate_payload(payload)
        _projection, key, _block = self._context()
        action = cast(AntihydraFragmentAction, binding.action)
        record = self.resolve(cast(AntihydraFragmentID, payload))
        if (
            binding.family != self.family
            or binding.semantic_version != self.semantic_version
            or binding.extent != record.consumed
            or binding.boundary_ports != (key.source_owner, key.start)
            or binding.orientation != 1
            or binding.radix != 2
            or binding.precision is not None
            or action.offset != 0
            or action.width != record.consumed
            or failure_prefix is not None
        ):
            raise ValueError("Antihydra image binding metadata is inconsistent")

    def identity_action(self, source: Hashable) -> AntihydraFragmentAction:
        self.validate_source(source)
        return AntihydraFragmentAction(0, 0)

    def action_children(self, action: Hashable) -> tuple[Hashable, Hashable] | None:
        self.validate_action(action)
        # The occurrence cursor already admitted the complete bounded block
        # image. Splitting it would rebuild a second roof chronology.
        return None

    def compose_actions(
        self, before: Hashable, after: Hashable
    ) -> AntihydraFragmentAction:
        self.validate_action(before)
        self.validate_action(after)
        left, right = (
            cast(AntihydraFragmentAction, before),
            cast(AntihydraFragmentAction, after),
        )
        if left.width == 0:
            return right
        if right.width == 0:
            return left
        if left.offset + left.width != right.offset:
            raise ValueError("Antihydra fragment actions are not chronological")
        return AntihydraFragmentAction(left.offset, left.width + right.width)

    def admit_source(self, source: Hashable) -> SourceImageCandidate:
        self.validate_source(source)
        _projection, key, _block = self._context()
        payload = self.scoped_handle(_FragmentRecord(0, None))
        return SourceImageCandidate(payload, 0, (key.source_owner, key.start))

    def apply_primitive(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_action(action)
        exact = cast(AntihydraFragmentAction, action)
        prior = self.resolve(cast(AntihydraFragmentID, source.payload))
        if exact.width == 0:
            return SourceImageCandidate(
                source.payload, prior.consumed, source.binding.boundary_ports
            )
        if prior.consumed != 0 or prior.image is not None:
            raise ValueError("Antihydra primitive requires its admitted source")
        _projection, _key, block = self._context()
        occurrence = self._active_occurrence()
        if exact.offset != 0 or exact.width != block.width or occurrence.image is None:
            raise ValueError("Antihydra primitive requires the admitted block image")
        payload = self.scoped_handle(_FragmentRecord(block.width, occurrence.image))
        self.ledger.bump(_antihydra_keys.SPACETIME_PROJECTION_CORE_PRIMITIVE_FRAGMENTS)
        return SourceImageCandidate(
            payload,
            block.width,
            source.binding.boundary_ports,
        )

    def compose_chronological(
        self,
        action: Hashable,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        raise ValueError("Antihydra block image has no fragment composition")

    def admitted_input_key(self, action: Hashable, source: SourceImageView) -> None:
        return None

    def transport_reuse(
        self,
        action: Hashable,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        raise ValueError("Antihydra fragment transport is not proved")

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        if demand != SourceImageDemand("typed-fragment"):
            raise ValueError("unsupported Antihydra fragment demand")
        self.validate_payload(image.payload)
        return SourceImageProjection(image.payload)

    def first_failure(self, image: SourceImageView) -> None:
        return None

    def finish(self, payload: AntihydraFragmentID) -> ProjectionFragment:
        record = self.resolve(payload)
        projection, key, block = self._context()
        occurrence = self._active_occurrence()
        image = record.image
        if (
            record.consumed != block.width
            or image is None
            or image is not occurrence.image
        ):
            raise ArithmeticError("shared Antihydra image disagrees with its roof")
        image.validate(key, block.width)
        if (image.source_h, image.source_balance) != (
            self._source_h,
            self._source_balance,
        ) or (image.output_h, image.output_balance) != block.advance(
            self._source_h, self._source_balance
        ):
            raise ArithmeticError("shared Antihydra image disagrees with its roof")
        ports = [[0] * key.area for _ in range(12)]
        samples = 0
        workspace = projection.result.source_term.engine.projection_workspace
        if workspace is None:
            raise RuntimeError("Antihydra section workspace was not started")
        classes: dict[tuple[tuple[int, int], int, int], int] = {}
        for section, head, time, copies in image.classes:
            classes[(section, head, time)] = copies
            self.ledger.bump(_antihydra_keys.SPACETIME_PROJECTION_COMPOSED_CLASS_READS)
            if len(classes) == 32:
                samples += projection.flush_section_classes(
                    ports, classes, workspace, self._section_capacity
                )
        if classes:
            samples += projection.flush_section_classes(
                ports, classes, workspace, self._section_capacity
            )
        return ProjectionFragment(key, tuple(tuple(row) for row in ports), samples)

    def clear_context(self) -> None:
        count = len(self._records)
        nodes = sum(self._record_nodes(record) for record in self._records)
        seal_nodes = sum(self._seal_nodes(seal) for seal in self._seals)
        self._records.clear()
        self._seals.clear()
        source_count = len(self._source_seals)
        self._source_seals.clear()
        self.ledger.release(self._owner, entries=count, nodes=nodes)
        self.ledger.release(self._seal_owner, entries=count, nodes=seal_nodes)
        self.ledger.release(
            self._source_seal_owner,
            entries=source_count,
            nodes=20 * source_count,
        )
        self.projection = None
        self.key = None
        self.block = None
        self._cursor = None
        self._occurrence = None
        self._source_h = self._source_balance = 0
        self._section_capacity = 0
        self._source_token = None
        self._token = ArenaToken("antihydra-projection-fragments-cleared")

    def transient_inventory(self) -> tuple[ResourceInventory, ...]:
        """Snapshot this adapter's fragment payload and source-seal stores."""
        return tuple(
            self.ledger.inventory_owner(owner)
            for owner in (self._owner, self._seal_owner, self._source_seal_owner)
        )


class AntihydraProjectionDriver:
    """One reusable common scheduler authority owned by a cylinder engine."""

    def __init__(self, ledger: ResourceLedger) -> None:
        self.adapter = AntihydraFragmentAdapter(ledger)
        self.cursor = ProjectionOccurrenceCursor(ledger)
        self.scheduler = TileScheduler.source_only(ledger)
        self.scheduler.register_source_image_adapter(self.adapter)

    @property
    def core(self) -> SourceBoundSchedulerCore:
        """Read-only access to the core owned by the canonical scheduler."""
        core = self.scheduler.published_source_image_core
        if core is None:
            raise RuntimeError("Antihydra projection scheduler has been disposed")
        return core

    def project_fragment(
        self, cache: ProjectionFragmentCache, image: SourceImageID
    ) -> ProjectionFragment:
        """Recover the exact projection through its admitted image and support."""
        projection = self.adapter.projection
        if (
            projection is None
            or cache.ledger is not self.core.ledger
            or projection.result.source_term.engine.projection_fragments is not cache
            or projection.result.source_term.engine.projection_fragment_driver
            is not self
        ):
            raise ValueError(
                "Antihydra fragment requires an active source-image publication"
            )
        payload = self.scheduler.source_projection(
            self.adapter, image, SourceImageDemand("typed-fragment")
        ).value
        if type(payload) is not AntihydraFragmentID:
            raise TypeError("shared Antihydra projection returned another payload")
        self.core.ledger.bump(
            _antihydra_keys.SPACETIME_PROJECTION_FRAGMENT_ISSUANCE_WORK
        )
        return self.adapter.finish(payload)

    def build(
        self,
        occurrence: ProjectionOccurrenceID,
        fragment_capacity: int,
        section_capacity: int,
    ) -> ProjectionFragment:
        record = self.cursor.resolve(occurrence)
        projection = self.cursor.projection
        if (
            projection is None
            or projection.result.source_term.engine.projection_fragment_driver
            is not self
        ):
            raise ValueError("Antihydra fragment requires its active source driver")
        self.adapter.configure(self.cursor, occurrence, section_capacity)
        try:
            image = self.scheduler.source_image(
                self.adapter,
                self.adapter.source(),
                AntihydraFragmentAction(0, record.block.width),
            )
            cache = projection.result.source_term.engine.projection_fragments
            return cache.put(image, fragment_capacity, issuer=self)
        finally:
            try:
                self.scheduler.clear_source_images()
            finally:
                self.adapter.clear_context()


def build_projection_fragment(
    projection: SpaceTimeProjection,
    occurrence: ProjectionOccurrenceID,
    fragment_capacity: int,
    section_capacity: int | None = None,
) -> ProjectionFragment:
    """Run the common chronological driver and return one detached root image."""
    engine = projection.result.source_term.engine
    driver = engine.projection_fragment_driver
    if type(driver) is not AntihydraProjectionDriver:
        raise ValueError("Antihydra projection driver owner was changed")
    if driver.cursor.projection is not projection:
        raise ValueError("Antihydra fragment has another projection occurrence")
    return driver.build(
        occurrence,
        fragment_capacity,
        fragment_capacity if section_capacity is None else section_capacity,
    )


__all__ = ["AntihydraProjectionDriver", "build_projection_fragment"]
