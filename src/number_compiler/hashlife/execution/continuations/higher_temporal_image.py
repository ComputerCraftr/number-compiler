"""Source-bound temporal substitution for recursive higher images.

This constructor consumes an already published recursive output image.  It
threads that image's exact bound exterior states to each leaf, substitutes the
leaf output into one primitive consumer, and publishes another ordinary
recursive leaf/branch image.  It never publishes ``RecursiveOutputTemporal``
and never asks a temporal evaluator for a coordinate.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.hashlife.execution.continuations.higher_macro_composer import (
    HigherMacroDeclaration,
    HigherSpatialMacroComposer,
    SourceBoundHigherMacro,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpressionID,
)
from number_compiler.hashlife.execution.field_images import (
    SourceBindingID,
    SourceCellID,
    SourceForestID,
)
from number_compiler.hashlife.execution.recursive_outputs import (
    RecursiveOutputBranch,
    RecursiveOutputLeaf,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList


@dataclass(frozen=True, slots=True)
class HigherTemporalImageID(ArenaHandle):
    """Scoped identity of one exact source-bound temporal image occurrence."""


@dataclass(frozen=True, slots=True)
class HigherTemporalImage:
    source: SourceBindingID
    chronology: FieldCellActionID
    boundary_action: FieldCellActionID
    macro: SourceBoundHigherMacro
    left: HigherExpressionID
    right: HigherExpressionID
    active_extent: int
    padded_extent: int
    admitted_extent_bound: int
    predecessor: HigherTemporalImageID | None = None


@dataclass(frozen=True, slots=True)
class _NodeKey:
    consumer: HigherMacroDeclaration
    output: CoordinateOutputMorphismID
    interface: LocalInterfaceID
    left: HigherExpressionID
    right: HigherExpressionID
    width: int
    source_extent: int


@dataclass(frozen=True, slots=True)
class _BlankKey:
    consumer: HigherMacroDeclaration
    width: int


@dataclass(frozen=True, slots=True)
class _Frame:
    output: CoordinateOutputMorphismID
    interface: LocalInterfaceID
    left: HigherExpressionID
    right: HigherExpressionID
    origin: int
    width: int
    ready: bool


class HigherTemporalImageArena:
    """Construct primitive successor images over a fixed padded spatial DAG.

    Composite consumers are deliberately rejected.  Repeated primitive calls
    are successor closed because every result is an ordinary recursive image
    and is retained with its exact source, chronology and exterior states.
    Workspace memos are request-local and consumer-bound, including blank
    summaries. Changing the spatial composer's declaration invalidates this
    arena; it does not authorize reusing earlier images under another action.
    """

    _KIND = "higher-temporal-image"

    def __init__(
        self,
        spatial: HigherSpatialMacroComposer,
        *,
        compose_actions: Callable[
            [FieldCellActionID, FieldCellActionID], FieldCellActionID
        ],
    ) -> None:
        if type(spatial) is not HigherSpatialMacroComposer or not callable(
            compose_actions
        ):
            raise TypeError("higher temporal images require canonical constructors")
        self.spatial = spatial
        self.semantics = spatial.semantics
        self.interfaces = spatial.interfaces
        self.outputs = spatial.outputs
        self.sources = spatial.sources
        self.ledger: ResourceLedger = spatial.ledger
        self._compose_actions = compose_actions
        self._consumer = self._consumer_key()
        self._consumer_seal = self._consumer.seal()
        self.owner = ArenaToken("higher-temporal-images")
        prefix = f"higher-temporal-images-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(prefix + "-nodes", "field_image")
        self._key_owner = self.ledger.register(prefix + "-keys", "field_image_interner")
        self._seal_owner = self.ledger.register(
            prefix + "-seals", "field_image_publication_seal"
        )
        self._frame_owner = self.ledger.register(prefix + "-frames", "query_workspace")
        self._built_owner = self.ledger.register(prefix + "-built", "query_workspace")
        self._source_frame_owner = self.ledger.register(
            prefix + "-source-frames", "query_workspace"
        )
        self._source_summary_owner = self.ledger.register(
            prefix + "-source-summaries", "query_workspace"
        )
        self._nodes: LedgerList[HigherTemporalImage] = self.ledger.make_list(
            self._node_owner
        )
        self._keys: LedgerDict[HigherTemporalImage, int] = self.ledger.make_dict(
            self._key_owner
        )
        self._seals: LedgerList[tuple[object, ...]] = self.ledger.make_list(
            self._seal_owner, nodes_per_entry=0
        )
        self._frames: LedgerList[_Frame] = self.ledger.make_list(
            self._frame_owner, append_only=False
        )
        self._built: LedgerDict[_NodeKey | _BlankKey, SourceBoundHigherMacro] = (
            self.ledger.make_dict(self._built_owner)
        )
        self._source_frames: LedgerList[tuple[SourceCellID, bool]] = (
            self.ledger.make_list(self._source_frame_owner, append_only=False)
        )
        self._source_summaries: LedgerDict[SourceCellID, tuple[int, bool]] = (
            self.ledger.make_dict(self._source_summary_owner)
        )
        self._running = False
        self._arena_authority = (
            self.owner,
            self.ledger,
            self.spatial,
            self.semantics,
            self.interfaces,
            self.outputs,
            self.sources,
            self.sources.owner,
            self._nodes,
            self._keys,
            self._seals,
            self._frames,
            self._built,
            self._source_frames,
            self._source_summaries,
            self._consumer,
            self._consumer_seal,
            self._compose_actions,
        )
        self.ledger.register_execution_root(self)

    def _check_authority(self) -> None:
        expected = self._arena_authority
        actual = (
            self.owner,
            self.ledger,
            self.spatial,
            self.semantics,
            self.interfaces,
            self.outputs,
            self.sources,
            self.sources.owner,
            self._nodes,
            self._keys,
            self._seals,
            self._frames,
            self._built,
            self._source_frames,
            self._source_summaries,
            self._consumer,
            self._consumer_seal,
            self._compose_actions,
        )
        if (
            type(expected) is not tuple
            or len(expected) != len(actual)
            or any(
                supplied is not issued
                for supplied, issued in zip(actual, expected, strict=True)
            )
        ):
            raise ValueError("higher temporal image arena lost its issued authority")
        if (
            self._consumer_key().seal() != self._consumer_seal
            or self._consumer.seal() != self._consumer_seal
            or self.spatial.semantics is not self.semantics
            or self.spatial.interfaces is not self.interfaces
            or self.spatial.outputs is not self.outputs
            or self.spatial.sources is not self.sources
            or self.spatial.ledger is not self.ledger
        ):
            raise ValueError("higher temporal image consumer binding was changed")

    def _consumer_key(self) -> HigherMacroDeclaration:
        try:
            return self.spatial.declaration()
        except ValueError as error:
            raise ValueError(
                "higher temporal image consumer binding was changed"
            ) from error

    def _handle(self, local_id: int) -> HigherTemporalImageID:
        return HigherTemporalImageID(self.owner, self._KIND, local_id)

    def resolve(self, image: HigherTemporalImageID) -> HigherTemporalImage:
        self._check_authority()
        if type(image) is not HigherTemporalImageID:
            raise TypeError("expected a higher temporal image ID")
        image.validate(self.owner, self._KIND, size=len(self._nodes))
        record = self._nodes[image.local_id]
        self._validate_record(record)
        if self._seal(record) != self._seals[image.local_id]:
            raise ValueError("higher temporal image publication seal is invalid")
        return record

    @staticmethod
    def _seal(record: HigherTemporalImage) -> tuple[object, ...]:
        macro = record.macro
        return (
            record.source,
            record.chronology,
            record.boundary_action,
            macro.interface,
            macro.output,
            macro.width,
            macro.source_extent,
            macro.activity,
            macro.first_active,
            macro.last_active,
            macro.extent,
            macro.growth,
            record.left,
            record.right,
            record.active_extent,
            record.padded_extent,
            record.admitted_extent_bound,
            record.predecessor,
        )

    def _validate_record(self, record: HigherTemporalImage) -> None:
        if type(record) is not HigherTemporalImage:
            raise TypeError("temporal image arena contains another record sort")
        self.sources.binding_extent(record.source)
        self.semantics.schema.validate_action(record.chronology)
        self.semantics.schema.validate_action(record.boundary_action)
        macro = record.macro
        if type(macro) is not SourceBoundHigherMacro:
            raise TypeError("temporal image requires a canonical higher macro")
        self.interfaces.resolve(macro.interface)
        self.outputs.resolve(macro.output)
        if (
            type(macro.width) is not int
            or type(macro.source_extent) is not int
            or type(macro.activity) is not HigherExpressionID
            or type(macro.first_active) is not HigherExpressionID
            or type(macro.last_active) is not HigherExpressionID
            or type(macro.extent) is not HigherExpressionID
            or type(macro.growth) is not HigherExpressionID
            or type(record.active_extent) is not int
            or type(record.padded_extent) is not int
            or type(record.admitted_extent_bound) is not int
            or not 0 <= record.active_extent <= record.admitted_extent_bound
            or record.admitted_extent_bound > record.padded_extent
            or macro.width != record.padded_extent
        ):
            raise ValueError("temporal image has invalid padded extent authority")
        self._boundary_sort(record.boundary_action, 0, record.left)
        self._boundary_sort(record.boundary_action, 1, record.right)
        if record.predecessor is not None:
            if type(record.predecessor) is not HigherTemporalImageID:
                raise TypeError("temporal predecessor has another handle sort")
            record.predecessor.validate(self.owner, self._KIND, size=len(self._nodes))

    def _intern(self, record: HigherTemporalImage) -> HigherTemporalImageID:
        self._check_authority()
        found = self._keys.get(record)
        if found is not None:
            result = self._handle(found)
            self.resolve(result)
            return result
        self._validate_record(record)
        self.ledger.reserve_many(
            (
                (self._node_owner, 1, 1),
                (self._key_owner, 1, 0),
                (self._seal_owner, 1, 0),
            )
        )
        local_id = len(self._nodes)
        try:
            self._nodes.append(record)
            self._seals.append(self._seal(record))
            self._keys[record] = local_id
        except BaseException:
            self._keys.pop(record, None)
            self._nodes._rollback_unpublished(local_id)
            self._seals._rollback_unpublished(local_id)
            self.ledger.release(self._node_owner, entries=1, nodes=1)
            self.ledger.release(self._key_owner, entries=1)
            self.ledger.release(self._seal_owner, entries=1)
            raise
        self.ledger.bump("higher_temporal_image_publications")
        return self._handle(local_id)

    def _ports(
        self, interface: LocalInterfaceID
    ) -> tuple[HigherExpressionID, HigherExpressionID]:
        signature = self.interfaces.interface(
            self.interfaces.resolve(interface).signature
        )
        ports = {port.role: port.variable for port in signature.inputs}
        if set(ports) != {"left-boundary", "right-boundary"}:
            raise ValueError("temporal image requires an exact two-port interface")
        return ports["left-boundary"], ports["right-boundary"]

    def _bound(
        self,
        interface: LocalInterfaceID,
        role: str,
        left: HigherExpressionID,
        right: HigherExpressionID,
    ) -> HigherExpressionID:
        record = self.interfaces.resolve(interface)
        value = getattr(record.components, role)
        if type(value) is not HigherExpressionID:
            raise TypeError(f"temporal image {role} is not a scalar expression")
        left_port, right_port = self._ports(interface)
        return self.semantics.bind_free_many(
            value, ((left_port, left), (right_port, right))
        )

    def _boundary_sort(
        self, action: FieldCellActionID, side: int, value: HigherExpressionID
    ) -> None:
        if type(value) is not HigherExpressionID:
            raise TypeError("temporal image exterior requires a scoped expression")
        if self.semantics.expression(value).sort != self.semantics.state_sort(
            action, side
        ):
            raise ValueError("temporal image exterior has another action state sort")

    def _closed_boundary(
        self, action: FieldCellActionID, side: int, value: HigherExpressionID
    ) -> object:
        self._boundary_sort(action, side, value)
        return self.semantics.evaluate(value)

    def bind_initial(
        self,
        producer: HigherSpatialMacroComposer,
        source: SourceBindingID,
        macro: SourceBoundHigherMacro,
        left: HigherExpressionID,
        right: HigherExpressionID,
    ) -> HigherTemporalImageID:
        """Bind the first published image to its exact live source occurrence."""
        self._check_authority()
        if producer.ledger is not self.ledger or producer.outputs is not self.outputs:
            raise ValueError("initial temporal image belongs to another runtime")
        producer.validate_binding(source, macro)
        if self.sources.binding_extent(source) != macro.width:
            raise ValueError("initial image width differs from its source binding")
        if self._source_prefix_extent(source) != macro.source_extent:
            raise ValueError("initial macro changes its authenticated source extent")
        left_value = self._closed_boundary(producer.action, 0, left)
        right_value = self._closed_boundary(producer.action, 1, right)
        left_port, right_port = self._ports(macro.interface)
        extent_value = self.semantics.evaluate(
            macro.extent,
            {left_port: left_value, right_port: right_value},
        )
        if type(extent_value) is not int or not 0 <= extent_value <= macro.width:
            raise ValueError("initial temporal image has invalid active extent")
        record = HigherTemporalImage(
            source,
            producer.action,
            producer.action,
            macro,
            left,
            right,
            extent_value,
            macro.width,
            extent_value,
        )
        return self._intern(record)

    def _source_push(self, source: SourceCellID, ready: bool) -> None:
        self.ledger.reserve(self._source_frame_owner, entries=1, nodes=1)
        try:
            self._source_frames.append((source, ready))
        except BaseException:
            self.ledger.release(self._source_frame_owner, entries=1, nodes=1)
            raise

    def _source_prefix_extent(self, source: SourceBindingID) -> int:
        """Derive one active-prefix extent from the immutable source DAG."""
        blank = self.sources.alphabet()[1]
        roots = (
            (source,)
            if type(source) is SourceCellID
            else self.sources.resolve_forest(source).cells
            if type(source) is SourceForestID
            else ()
        )
        if not roots:
            raise TypeError("temporal source prefix requires a scoped source binding")
        try:
            for root in reversed(roots):
                self._source_push(root, False)
            while self._source_frames:
                current, ready = self._source_frames.pop()
                self.ledger.release(self._source_frame_owner, entries=1, nodes=1)
                if current in self._source_summaries:
                    continue
                node = self.sources.resolve(current)
                self.ledger.bump("higher_temporal_source_prefix_node_visits")
                if not node.level:
                    prefix = int(self.sources.symbol(current) != blank)
                    summary = prefix, False
                elif not ready:
                    left, right = self.sources.children(current)
                    self._source_push(current, True)
                    if right not in self._source_summaries:
                        self._source_push(right, False)
                    if left not in self._source_summaries:
                        self._source_push(left, False)
                    continue
                else:
                    left, right = self.sources.children(current)
                    left_prefix, left_bad = self._source_summaries[left]
                    right_prefix, right_bad = self._source_summaries[right]
                    left_width = self.sources.resolve(left).width
                    bad = (
                        left_bad
                        or right_bad
                        or (left_prefix < left_width and right_prefix > 0)
                    )
                    prefix = (
                        left_prefix
                        if left_prefix < left_width
                        else left_width + right_prefix
                    )
                    summary = prefix, bad
                self.ledger.reserve(self._source_summary_owner, entries=1)
                try:
                    self._source_summaries[current] = summary
                except BaseException:
                    self.ledger.release(self._source_summary_owner, entries=1)
                    raise
            prefix = 0
            blank_seen = False
            for root in roots:
                root_prefix, bad = self._source_summaries[root]
                width = self.sources.resolve(root).width
                if bad or (blank_seen and root_prefix):
                    raise ValueError("temporal source is not one active prefix")
                if not blank_seen:
                    prefix += root_prefix
                    blank_seen = root_prefix < width
            return prefix
        finally:
            frames, summaries = len(self._source_frames), len(self._source_summaries)
            self._source_frames.clear()
            self._source_summaries.clear()
            self.ledger.release(self._source_frame_owner, entries=frames, nodes=frames)
            self.ledger.release(self._source_summary_owner, entries=summaries)

    def _push(self, frame: _Frame) -> None:
        self.ledger.reserve(self._frame_owner, entries=1, nodes=1)
        try:
            self._frames.append(frame)
        except BaseException:
            self.ledger.release(self._frame_owner, entries=1, nodes=1)
            raise

    def _node_key(self, frame: _Frame, active_extent: int) -> _NodeKey:
        return _NodeKey(
            self._consumer,
            frame.output,
            frame.interface,
            frame.left,
            frame.right,
            frame.width,
            min(frame.width, max(0, active_extent - frame.origin)),
        )

    def _clear_workspace(self) -> None:
        frames, built = len(self._frames), len(self._built)
        self._frames.clear()
        self._built.clear()
        self.ledger.release(self._frame_owner, entries=frames, nodes=frames)
        self.ledger.release(self._built_owner, entries=built)

    def _remember_built(
        self,
        key: _NodeKey | _BlankKey,
        result: SourceBoundHigherMacro,
    ) -> SourceBoundHigherMacro:
        if key.consumer != self._consumer:
            raise ValueError("temporal memo has another consumer binding")
        found = self._built.get(key)
        if found is not None:
            return found
        self.ledger.reserve(self._built_owner, entries=1)
        try:
            self._built[key] = result
        except BaseException:
            self.ledger.release(self._built_owner, entries=1)
            raise
        return result

    def _blank_macro(self, width: int) -> SourceBoundHigherMacro:
        """Build one parametric blank macro per spatial width.

        A blank macro still carries the consumer's exact two-port transfer, so
        it remains valid at every occurrence of an empty provider subtree.  It
        is constructed from logarithmically many distinct symbolic nodes and
        never expands or observes the provider word.
        """
        self._check_authority()
        if type(width) is not int or width < 1:
            raise ValueError("temporal blank macro requires a positive width")
        self.ledger.reserve(self._frame_owner, entries=1, nodes=1)
        pending = [width]
        try:
            while pending:
                current = pending[-1]
                key = _BlankKey(self._consumer, current)
                self.ledger.bump("higher_temporal_image_workspace_probes")
                if key in self._built:
                    self.ledger.bump("higher_temporal_image_blank_macro_cache_hits")
                    pending.pop()
                    self.ledger.release(self._frame_owner, entries=1, nodes=1)
                    continue
                if current == 1:
                    result = self.spatial.bind_symbol_expression(
                        self.semantics.symbol(self.spatial.action, self.spatial.blank),
                        source_extent=0,
                    )
                else:
                    left_width = 1 << ((current - 1).bit_length() - 1)
                    right_width = current - left_width
                    left = self._built.get(_BlankKey(self._consumer, left_width))
                    right = self._built.get(_BlankKey(self._consumer, right_width))
                    if left is None or right is None:
                        self.ledger.reserve(self._frame_owner, entries=1, nodes=1)
                        pending.append(left_width if left is None else right_width)
                        continue
                    result = self.spatial.combine(left, right)
                self._remember_built(key, result)
                self.ledger.bump("higher_temporal_image_blank_macro_nodes")
                pending.pop()
                self.ledger.release(self._frame_owner, entries=1, nodes=1)
            return self._built[_BlankKey(self._consumer, width)]
        finally:
            self.ledger.release(
                self._frame_owner, entries=len(pending), nodes=len(pending)
            )

    def _provider_subtree_is_blank(self, frame: _Frame) -> bool:
        """Prove that this exact bound provider subtree emits only blanks."""
        activity = self._bound(
            frame.interface,
            "activity",
            frame.left,
            frame.right,
        )
        value = self.semantics.evaluate(activity)
        self.ledger.bump("higher_temporal_image_blank_summary_checks")
        if type(value) is not int or value not in (0, 1):
            raise ValueError("temporal provider has invalid activity summary")
        return value == 0

    def step(
        self,
        provider: HigherTemporalImageID,
        left: HigherExpressionID,
        right: HigherExpressionID,
    ) -> HigherTemporalImageID:
        """Apply this arena's primitive action to one completed provider image."""
        self._check_authority()
        if self._running:
            raise RuntimeError("higher temporal image construction is not reentrant")
        prior = self.resolve(provider)
        consumer = self.spatial.action
        self.semantics.schema.validate_action(consumer)
        if self.semantics.schema.children(consumer) is not None:
            raise ValueError(
                "temporal image construction requires a primitive consumer"
            )
        next_extent_bound = prior.admitted_extent_bound + 1
        if next_extent_bound > prior.padded_extent:
            raise ValueError("temporal image has insufficient admitted blank padding")
        left_value = self._closed_boundary(consumer, 0, left)
        right_value = self._closed_boundary(consumer, 1, right)
        root = _Frame(
            prior.macro.output,
            prior.macro.interface,
            prior.left,
            prior.right,
            0,
            prior.padded_extent,
            False,
        )
        self._running = True
        try:
            self._push(root)
            while self._frames:
                frame = self._frames.pop()
                self.ledger.release(self._frame_owner, entries=1, nodes=1)
                key = self._node_key(frame, prior.active_extent)
                self.ledger.bump("higher_temporal_image_workspace_probes")
                if key in self._built:
                    self.ledger.bump("higher_temporal_image_memo_hits")
                    continue
                if key.source_extent == 0 and self._provider_subtree_is_blank(frame):
                    self.ledger.bump("higher_temporal_image_blank_subtree_hits")
                    self._remember_built(key, self._blank_macro(frame.width))
                    continue
                node = self.outputs.resolve(frame.output)
                self.interfaces.resolve(frame.interface)
                self.ledger.bump("higher_temporal_image_node_visits")
                if type(node) is RecursiveOutputLeaf:
                    if (
                        frame.ready
                        or frame.width != 1
                        or node.scalar_interface != frame.interface
                    ):
                        raise ValueError(
                            "temporal leaf disagrees with its image interface"
                        )
                    symbol = self._bound(
                        frame.interface, "output", frame.left, frame.right
                    )
                    result = self.spatial.bind_symbol_expression(
                        symbol,
                        source_extent=int(frame.origin < prior.active_extent),
                    )
                elif type(node) is RecursiveOutputBranch:
                    if (
                        node.left_width < 1
                        or node.left_width >= frame.width
                        or self.outputs.resolve(node.left) is None
                        or self.outputs.resolve(node.right) is None
                    ):
                        raise ValueError(
                            "temporal branch has invalid recursive geometry"
                        )
                    left_frame = _Frame(
                        node.left,
                        node.left_interface,
                        frame.left,
                        self._bound(
                            node.right_interface,
                            "boundary_right",
                            frame.left,
                            frame.right,
                        ),
                        frame.origin,
                        node.left_width,
                        False,
                    )
                    right_frame = _Frame(
                        node.right,
                        node.right_interface,
                        self._bound(
                            node.left_interface,
                            "boundary_left",
                            frame.left,
                            frame.right,
                        ),
                        frame.right,
                        frame.origin + node.left_width,
                        frame.width - node.left_width,
                        False,
                    )
                    left_key = self._node_key(left_frame, prior.active_extent)
                    right_key = self._node_key(right_frame, prior.active_extent)
                    self.ledger.bump("higher_temporal_image_boundary_substitutions", 2)
                    if not frame.ready:
                        self._push(
                            _Frame(
                                frame.output,
                                frame.interface,
                                frame.left,
                                frame.right,
                                frame.origin,
                                frame.width,
                                True,
                            )
                        )
                        for child in (right_key, left_key):
                            if child not in self._built:
                                self._push(
                                    right_frame if child == right_key else left_frame
                                )
                        continue
                    try:
                        result = self.spatial.combine(
                            self._built[left_key], self._built[right_key]
                        )
                    except KeyError as exc:
                        raise AssertionError(
                            "temporal image child was not constructed"
                        ) from exc
                else:
                    raise ValueError(
                        "temporal image input is not a completed leaf/branch image"
                    )
                self._remember_built(key, result)
            root_key = self._node_key(root, prior.active_extent)
            result = self._built[root_key]
            result_left, result_right = self._ports(result.interface)
            active_extent = self.semantics.evaluate(
                result.extent,
                {result_left: left_value, result_right: right_value},
            )
            if (
                type(active_extent) is not int
                or not 0 <= active_extent <= prior.padded_extent
                or active_extent > next_extent_bound
            ):
                raise ValueError("temporal image violated its admitted growth bound")
            chronology = self._compose_actions(prior.chronology, consumer)
            self.semantics.schema.validate_action(chronology)
            return self._intern(
                HigherTemporalImage(
                    prior.source,
                    chronology,
                    consumer,
                    result,
                    left,
                    right,
                    active_extent,
                    prior.padded_extent,
                    next_extent_bound,
                    provider,
                )
            )
        finally:
            self._clear_workspace()
            self._running = False


__all__ = ["HigherTemporalImage", "HigherTemporalImageArena", "HigherTemporalImageID"]
