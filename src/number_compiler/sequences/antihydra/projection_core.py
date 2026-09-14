"""Shared source-image adapter for one bounded Antihydra section cylinder."""

from __future__ import annotations

from collections.abc import Hashable, MutableSequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
    SourceBoundSchedulerCore,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.blocks import (
    ArithmeticCylinder,
    arithmetic_from_word,
    physical_roof,
)
from number_compiler.sequences.antihydra.projection_fragments import (
    ProjectionFragment,
    ProjectionFragmentCache,
    ProjectionFragmentKey,
)

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
    leaf: ArithmeticCylinder | None
    parent: AntihydraFragmentID | None
    consumed: int
    head_delta: int
    time_delta: int
    leaf_head: int
    leaf_time: int
    prefix: ArithmeticCylinder | None


class _AntihydraFragmentAdapter(SourceBoundImageAdapter):
    family = "antihydra"
    semantic_version = "section-fragment-v1"

    def __init__(
        self,
        ledger: ResourceLedger,
    ) -> None:
        self.ledger = ledger
        self.projection: SpaceTimeProjection | None = None
        self.key: ProjectionFragmentKey | None = None
        self.block: ArithmeticCylinder | None = None
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
        self._source_seals: MutableSequence[tuple[object, ...]] = (
            self.ledger.make_list(self._source_seal_owner, append_only=False)
        )
        self.ledger.register_container(
            self._owner,
            self._records,
            node_count=lambda: sum(
                1
                + (record.leaf is not None)
                + (record.prefix is not None)
                for record in self._records
            ),
            payloads=self._records.__iter__,
        )
        self.ledger.register_container(
            self._seal_owner,
            self._seals,
            node_count=lambda: sum(
                1 + (seal[0] is not None) + (seal[-1] is not None)
                for seal in self._seals
            ),
            payloads=self._seals.__iter__,
        )
        self.ledger.register_container(
            self._source_seal_owner,
            self._source_seals,
            node_count=lambda: 18 * len(self._source_seals),
            payloads=self._source_seals.__iter__,
        )

    @staticmethod
    def _key_seal(key: ProjectionFragmentKey) -> tuple[object, ...]:
        return (
            key.source_owner,
            key.requested,
            key.start,
            key.cylinder,
            key.spatial_width,
            key.temporal_width,
            key.spatial_sign,
            key.temporal_sign,
            key.modulus,
            key.head_phase,
            key.time_phase,
        )

    def configure(
        self,
        projection: SpaceTimeProjection,
        key: ProjectionFragmentKey,
        block: ArithmeticCylinder,
        h: int,
        balance: int,
        section_capacity: int,
    ) -> None:
        if self.projection is not None or self._records:
            raise RuntimeError("Antihydra fragment driver is already in use")
        if projection.result.ledger is not self.ledger:
            raise ValueError("Antihydra fragment driver belongs to another ledger")
        if key.cylinder != (
            block.width,
            block.residue,
            block.output,
            block.delta,
            block.minimum,
            block.parity_word,
        ):
            raise ValueError("Antihydra fragment key has another cylinder")
        self.ledger.reserve(self._source_seal_owner, entries=1, nodes=18)
        try:
            self._source_seals.append(self._key_seal(key))
        except BaseException:
            self.ledger.release(self._source_seal_owner, entries=1, nodes=18)
            raise
        self.projection, self.key, self.block = projection, key, block
        self._source_h, self._source_balance = h, balance
        self._section_capacity = section_capacity
        self._source_token = ArenaToken("antihydra-projection-source")

    def source(self) -> AntihydraFragmentSourceID:
        self._context()
        if self._source_token is None:
            raise RuntimeError("Antihydra fragment source authority is inactive")
        return AntihydraFragmentSourceID(
            self._source_token, self._source_kind, 0
        )

    def _context(
        self,
    ) -> tuple[SpaceTimeProjection, ProjectionFragmentKey, ArithmeticCylinder]:
        if self.projection is None or self.key is None or self.block is None:
            raise RuntimeError("Antihydra fragment driver has no active source")
        return self.projection, self.key, self.block

    @staticmethod
    def _prefix_seal(
        prefix: ArithmeticCylinder | None,
    ) -> tuple[int, int, int, int, int, int] | None:
        if prefix is None:
            return None
        return (
            prefix.width,
            prefix.residue,
            prefix.output,
            prefix.delta,
            prefix.minimum,
            prefix.parity_word,
        )

    @staticmethod
    def _record_seal(record: _FragmentRecord) -> tuple[object, ...]:
        return (
            _AntihydraFragmentAdapter._prefix_seal(record.leaf),
            None
            if record.parent is None
            else (
                record.parent.owner,
                record.parent.kind,
                record.parent.local_id,
            ),
            record.consumed,
            record.head_delta,
            record.time_delta,
            record.leaf_head,
            record.leaf_time,
            _AntihydraFragmentAdapter._prefix_seal(record.prefix),
        )

    def _handle(self, record: _FragmentRecord) -> AntihydraFragmentID:
        _projection, _key, _block = self._context()
        nodes = (
            1
            + (record.leaf is not None)
            + (record.prefix is not None)
        )
        seal_nodes = 1 + (record.leaf is not None) + (record.prefix is not None)
        self.ledger.reserve_many(
            ((self._owner, 1, nodes), (self._seal_owner, 1, seal_nodes))
        )
        try:
            local_id = len(self._records)
            self._records.append(record)
            self._seals.append(self._record_seal(record))
        except BaseException:
            if len(self._records) > local_id:
                self._records.pop()
            if len(self._seals) > local_id:
                self._seals.pop()
            self.ledger.release(self._owner, entries=1, nodes=nodes)
            self.ledger.release(
                self._seal_owner, entries=1, nodes=seal_nodes
            )
            raise
        return AntihydraFragmentID(self._token, self._kind, local_id)

    def resolve(self, reference: AntihydraFragmentID) -> _FragmentRecord:
        if type(reference) is not AntihydraFragmentID:
            raise TypeError("expected an Antihydra fragment handle")
        reference.validate(self._token, self._kind, size=len(self._records))
        record = self._records[reference.local_id]
        if self._seals[reference.local_id] != self._record_seal(record):
            raise ValueError("Antihydra fragment payload was changed")
        return record

    def _input_after(self, prior: _FragmentRecord) -> tuple[int, int]:
        """Derive the next input by applying the admitted prefix transfer."""
        if prior.prefix is None:
            if prior.consumed != 0:
                raise ValueError("Antihydra fragment lost its prefix transfer")
            return self._source_h, self._source_balance
        if prior.prefix.width != prior.consumed:
            raise ValueError("Antihydra fragment prefix has another extent")
        return prior.prefix.advance(self._source_h, self._source_balance)

    def validate_source(self, source: Hashable) -> None:
        _projection, key, _block = self._context()
        if (
            type(source) is not AntihydraFragmentSourceID
            or self._source_token is None
        ):
            raise ValueError("Antihydra fragment has another source authority")
        source.validate(self._source_token, self._source_kind, size=1)
        if len(self._source_seals) != 1 or self._source_seals[0] != self._key_seal(key):
            raise ValueError("Antihydra fragment source binding was changed")

    def validate_action(self, action: Hashable) -> None:
        _projection, _key, block = self._context()
        if type(action) is not AntihydraFragmentAction:
            raise TypeError("Antihydra fragment requires its interval action")
        if action.offset < 0 or action.width < 0 or action.offset + action.width > block.width:
            raise ValueError("Antihydra fragment action leaves its source cylinder")

    def validate_payload(self, payload: Hashable) -> None:
        self.resolve(cast(AntihydraFragmentID, payload))

    def identity_action(self, source: Hashable) -> AntihydraFragmentAction:
        self.validate_source(source)
        return AntihydraFragmentAction(0, 0)

    def action_children(self, action: Hashable) -> tuple[Hashable, Hashable] | None:
        self.validate_action(action)
        exact = cast(AntihydraFragmentAction, action)
        if exact.width <= 8:
            return None
        first = 1 << ((exact.width - 1).bit_length() - 1)
        return (
            AntihydraFragmentAction(exact.offset, first),
            AntihydraFragmentAction(exact.offset + first, exact.width - first),
        )

    def compose_actions(self, before: Hashable, after: Hashable) -> AntihydraFragmentAction:
        self.validate_action(before)
        self.validate_action(after)
        left, right = cast(AntihydraFragmentAction, before), cast(AntihydraFragmentAction, after)
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
        payload = self._handle(_FragmentRecord(None, None, 0, 0, 0, 0, 0, None))
        return SourceImageCandidate(payload, 0, (key.source_owner, key.start))

    def apply_primitive(self, action: Hashable, source: SourceImageView) -> SourceImageCandidate:
        self.validate_action(action)
        exact = cast(AntihydraFragmentAction, action)
        prior = self.resolve(cast(AntihydraFragmentID, source.payload))
        if exact.width == 0:
            return SourceImageCandidate(source.payload, prior.consumed, source.binding.boundary_ports)
        if prior.consumed != exact.offset or exact.width > 8:
            raise ValueError("Antihydra primitive does not consume the next support interval")
        _projection, _key, block = self._context()
        word = (block.parity_word >> exact.offset) & ((1 << exact.width) - 1)
        input_h, input_balance = self._input_after(prior)
        leaf_block = arithmetic_from_word(
            input_h % (1 << exact.width), exact.width, word
        )
        prefix = leaf_block if prior.prefix is None else prior.prefix.then(leaf_block)
        roof = physical_roof(leaf_block)
        output_h, output_balance, left, right = roof.apply(
            input_h, input_balance
        )
        if (output_h, output_balance) != leaf_block.advance(
            input_h, input_balance
        ):
            raise ArithmeticError("Antihydra leaf roof lost its arithmetic action")
        payload = self._handle(
            _FragmentRecord(
                leaf_block,
                cast(AntihydraFragmentID, source.payload),
                prior.consumed + exact.width,
                prior.head_delta + right - left,
                prior.time_delta + right + left,
                prior.head_delta,
                prior.time_delta,
                prefix,
            )
        )
        self.ledger.bump("spacetime_projection_core_primitive_fragments")
        return SourceImageCandidate(
            payload,
            prior.consumed + exact.width,
            source.binding.boundary_ports,
        )

    def compose_chronological(
        self,
        action: Hashable,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        before_record = self.resolve(cast(AntihydraFragmentID, before.payload))
        after_record = self.resolve(cast(AntihydraFragmentID, after.payload))
        exact = cast(AntihydraFragmentAction, action)
        if before_record.consumed > after_record.consumed or after_record.consumed != exact.offset + exact.width:
            raise ValueError("Antihydra fragment composition lost chronology")
        return SourceImageCandidate(
            after.payload, after_record.consumed, source.binding.boundary_ports
        )

    def admitted_input_key(self, action: Hashable, source: SourceImageView) -> None:
        return None

    def transport_reuse(self, action: Hashable, cached_source: SourceImageView, cached_result: SourceImageView, source: SourceImageView) -> SourceImageCandidate:
        raise ValueError("Antihydra fragment transport is not proved")

    def project(self, image: SourceImageView, demand: SourceImageDemand) -> SourceImageProjection:
        if demand != SourceImageDemand("typed-fragment"):
            raise ValueError("unsupported Antihydra fragment demand")
        self.validate_payload(image.payload)
        return SourceImageProjection(image.payload)

    def first_failure(self, image: SourceImageView) -> None:
        return None

    def finish(self, payload: AntihydraFragmentID) -> ProjectionFragment:
        record = self.resolve(payload)
        projection, key, block = self._context()
        roof = physical_roof(block)
        _h, _balance, left, right = roof.apply(
            self._source_h, self._source_balance
        )
        if (
            record.consumed,
            record.head_delta,
            record.time_delta,
            record.prefix,
        ) != (block.width, right - left, right + left, block):
            raise ArithmeticError("shared Antihydra image disagrees with its roof")
        ports = [[0] * key.area for _ in range(12)]
        samples = 0
        current = payload
        seen = 0
        classes: dict[tuple[tuple[int, int], int, int], int] = {}
        spatial_phase = key.spatial_width * (
            2 if key.spatial_sign == -1 else 1
        )
        temporal_phase = key.temporal_width * (
            2 if key.temporal_sign == -1 else 1
        )
        workspace = projection.result._engine.projection_workspace
        if workspace is None:
            raise RuntimeError("Antihydra section workspace was not started")
        one_steps = (
            arithmetic_from_word(0, 1, 0),
            arithmetic_from_word(1, 1, 1),
        )
        one_roofs = tuple(physical_roof(step) for step in one_steps)
        while True:
            part = self.resolve(current)
            if part.parent is None:
                if part.consumed != 0 or part.leaf is not None:
                    raise ValueError("Antihydra fragment chain has another origin")
                break
            if part.leaf is None:
                raise ValueError("Antihydra fragment chain lost its leaf support")
            parent = self.resolve(part.parent)
            h, balance = self._input_after(parent)
            source_h, source_balance = h, balance
            head = time = 0
            for offset in range(part.leaf.width):
                odd = (part.leaf.parity_word >> offset) & 1
                if odd != h & 1:
                    raise ValueError(
                        "projection fragment differs from cylinder support"
                    )
                translated = (
                    projection._section_key(balance, h - 4),
                    (part.leaf_head + head) % spatial_phase,
                    (part.leaf_time + time) % temporal_phase,
                )
                classes[translated] = (
                    classes.get(translated, 0) + 1
                ) % key.modulus
                if len(classes) == 32:
                    samples += projection._flush_section_classes(
                        ports, classes, workspace, self._section_capacity
                    )
                h, balance, left, right = one_roofs[odd].apply(h, balance)
                head += right - left
                time += right + left
                self.ledger.bump(
                    "spacetime_projection_fragment_leaf_returns"
                )
            if (h, balance) != part.leaf.advance(
                source_h, source_balance
            ):
                raise ArithmeticError(
                    "projection leaf disagrees with arithmetic cylinder"
                )
            current = part.parent
            seen += 1
            if seen > 8:
                raise ValueError("Antihydra fragment chain exceeds its bounded grammar")
        if classes:
            samples += projection._flush_section_classes(
                ports, classes, workspace, self._section_capacity
            )
        return ProjectionFragment(
            key, tuple(tuple(row) for row in ports), samples
        )

    def clear_context(self) -> None:
        count = len(self._records)
        nodes = sum(
            1
            + (record.leaf is not None)
            + (record.prefix is not None)
            for record in self._records
        )
        seal_nodes = sum(
            1 + (seal[0] is not None) + (seal[-1] is not None)
            for seal in self._seals
        )
        self._records.clear()
        self._seals.clear()
        source_count = len(self._source_seals)
        self._source_seals.clear()
        self.ledger.release(self._owner, entries=count, nodes=nodes)
        self.ledger.release(
            self._seal_owner, entries=count, nodes=seal_nodes
        )
        self.ledger.release(
            self._source_seal_owner,
            entries=source_count,
            nodes=18 * source_count,
        )
        self.projection = None
        self.key = None
        self.block = None
        self._source_h = self._source_balance = 0
        self._section_capacity = 0
        self._source_token = None
        self._token = ArenaToken("antihydra-projection-fragments-cleared")


class AntihydraProjectionDriver:
    """One reusable common scheduler authority owned by a cylinder engine."""

    def __init__(self, ledger: ResourceLedger) -> None:
        self.adapter = _AntihydraFragmentAdapter(ledger)
        self.core = SourceBoundSchedulerCore(ledger)

    def project_fragment(
        self, cache: ProjectionFragmentCache, image: SourceImageID
    ) -> ProjectionFragment:
        """Recover the exact projection through its admitted image and support."""
        projection = self.adapter.projection
        if (
            projection is None
            or cache.ledger is not self.core.ledger
            or projection.result._engine.projection_fragments is not cache
            or projection.result._engine.projection_fragment_driver is not self
        ):
            raise ValueError("Antihydra fragment requires an active source-image publication")
        payload = self.core.projection(
            self.adapter, image, SourceImageDemand("typed-fragment")
        ).value
        if type(payload) is not AntihydraFragmentID:
            raise TypeError("shared Antihydra projection returned another payload")
        self.core.ledger.bump("spacetime_projection_fragment_issuance_work")
        return self.adapter.finish(payload)

    def build(
        self,
        projection: SpaceTimeProjection,
        key: ProjectionFragmentKey,
        block: ArithmeticCylinder,
        h: int,
        balance: int,
        section_capacity: int,
    ) -> ProjectionFragment:
        self.adapter.configure(
            projection, key, block, h, balance, section_capacity
        )
        try:
            self.core.register(self.adapter)
            image = self.core.apply(
                self.adapter,
                self.adapter.source(),
                AntihydraFragmentAction(0, block.width),
            )
            cache = projection.result._engine.projection_fragments
            return cache.put(image, section_capacity, issuer=self)
        finally:
            try:
                self.core.clear()
            finally:
                self.adapter.clear_context()


def build_projection_fragment(
    projection: SpaceTimeProjection,
    key: ProjectionFragmentKey,
    block: ArithmeticCylinder,
    h: int,
    balance: int,
    section_capacity: int,
) -> ProjectionFragment:
    """Run the common chronological driver and return one detached root image."""
    engine = projection.result._engine
    driver = engine.projection_fragment_driver
    if driver is None:
        driver = AntihydraProjectionDriver(projection.result.ledger)
        engine.projection_fragment_driver = driver
    if type(driver) is not AntihydraProjectionDriver:
        raise ValueError("Antihydra projection driver owner was changed")
    return driver.build(
        projection, key, block, h, balance, section_capacity
    )


__all__ = ["AntihydraProjectionDriver", "build_projection_fragment"]
