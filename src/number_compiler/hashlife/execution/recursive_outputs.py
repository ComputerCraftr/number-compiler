"""Canonical recursive coordinate morphisms for source-bound field images.

The output of a spatial parent is a branch over two already canonical child
morphisms.  It is deliberately not represented by a finite coordinate table.
Observation follows one child and asks the sibling only for the directional
boundary transfer needed at the midpoint.
"""

from __future__ import annotations

from collections.abc import Callable, Generator, MutableMapping
from dataclasses import dataclass
from typing import TypeAlias

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.hashlife.execution.continuations.higher_interfaces import (
    HigherLocalInterfaceArena,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpressionID,
)
from number_compiler.hashlife.execution.field_images import (
    SourceBindingID,
    SourceCellID,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.stores import record_indexed_node, reserve_indexed_id


@dataclass(frozen=True, slots=True)
class RecursiveOutputLeaf:
    """One source-symbol-partially-applied local output interface."""

    scalar_interface: LocalInterfaceID


@dataclass(frozen=True, slots=True)
class RecursiveOutputSource:
    """One immutable original-source coordinate.

    This is the only exact digit-bearing provider admitted by the recursive
    morphism arena.  It references a scoped source cell rather than copying
    its symbol, so a temporal image can be canonicalized before any incoming
    boundary is bound.
    """

    source: SourceCellID


@dataclass(frozen=True, slots=True)
class RecursiveOutputBindingSource:
    """One immutable original source cell or dyadic forest binding."""

    source: SourceBindingID


@dataclass(frozen=True, slots=True)
class RecursiveOutputBranch:
    """One spatial branch; completion is derived from both children at issue."""

    left: CoordinateOutputMorphismID
    right: CoordinateOutputMorphismID
    left_interface: LocalInterfaceID
    right_interface: LocalInterfaceID
    left_width: int
    spatial_complete: bool = True

    def __post_init__(self) -> None:
        if type(self.left_width) is not int or self.left_width < 1:
            raise ValueError("recursive output branch needs a positive left width")
        if type(self.spatial_complete) is not bool:
            raise TypeError("recursive output completion must be Boolean")


@dataclass(frozen=True, slots=True)
class RecursiveOutputTemporal:
    """One normalized temporal image of an original recursive provider.

    ``provider`` is never another temporal node after publication.  ``action``
    therefore denotes the complete chronological action from the immutable
    source associated with that provider to this output.  This record is a
    normalized construction reference: observation still calls the registered
    temporal evaluator.  It is not evidence of a completed tile-output
    absorption quotient, even when the referenced boundary functions are exact.
    """

    provider: CoordinateOutputMorphismID
    action: FieldCellActionID
    interface: LocalInterfaceID


RecursiveOutputRecord: TypeAlias = (
    RecursiveOutputSource
    | RecursiveOutputBindingSource
    | RecursiveOutputLeaf
    | RecursiveOutputBranch
    | RecursiveOutputTemporal
)
BoundaryValue: TypeAlias = object
_StreamFrame: TypeAlias = tuple[
    CoordinateOutputMorphismID,
    int,
    int,
    BoundaryValue,
    BoundaryValue,
    int | None,
    LocalInterfaceID | None,
]
_STREAM_FRAME_NODES = 7
TemporalOutputEvaluator: TypeAlias = Callable[
    [
        CoordinateOutputMorphismID,
        FieldCellActionID,
        LocalInterfaceID,
        int,
        BoundaryValue,
        BoundaryValue,
    ],
    int,
]
TemporalActionCompleter: TypeAlias = Callable[
    [CoordinateOutputMorphismID, FieldCellActionID], FieldCellActionID
]


class RecursiveCoordinateMorphismArena:
    """Index-owned recursive outputs with scoped, non-recycled identities."""

    _KIND = "recursive-coordinate-output-morphism"

    def __init__(
        self,
        interfaces: HigherLocalInterfaceArena,
        *,
        evaluate: Callable[
            [HigherExpressionID, dict[HigherExpressionID, object]], object
        ],
        validate_action: Callable[[FieldCellActionID], object] | None = None,
        compose_actions: Callable[
            [FieldCellActionID, FieldCellActionID], FieldCellActionID
        ]
        | None = None,
        validate_temporal_interface: Callable[[LocalInterfaceID], object] | None = None,
        evaluate_temporal: TemporalOutputEvaluator | None = None,
        complete_temporal_action: TemporalActionCompleter | None = None,
        validate_source: Callable[[SourceCellID], object] | None = None,
        read_source: Callable[[SourceCellID], int] | None = None,
        validate_source_binding: Callable[[SourceBindingID], object] | None = None,
        read_source_binding: Callable[[SourceBindingID, int], int] | None = None,
    ) -> None:
        if type(interfaces) is not HigherLocalInterfaceArena or not callable(evaluate):
            raise TypeError(
                "recursive outputs require higher interfaces and evaluation"
            )
        self.interfaces = interfaces
        self.ledger: ResourceLedger = interfaces.ledger
        self._evaluate = evaluate
        self._validate_action = validate_action
        self._compose_actions = compose_actions
        self._validate_temporal_interface = (
            interfaces.resolve
            if validate_temporal_interface is None
            else validate_temporal_interface
        )
        self._evaluate_temporal = evaluate_temporal
        self._complete_temporal_action = complete_temporal_action
        if (validate_source is None) != (read_source is None):
            raise ValueError(
                "source validation and reading must be configured together"
            )
        self._validate_source = validate_source
        self._read_source = read_source
        if (validate_source_binding is None) != (read_source_binding is None):
            raise ValueError(
                "source-binding validation and reading require one another"
            )
        self._validate_source_binding = validate_source_binding
        self._read_source_binding = read_source_binding
        self.owner = ArenaToken("recursive-coordinate-outputs")
        self.ledger.register_execution_root(self)
        prefix = f"recursive-coordinate-outputs-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(prefix + "-nodes", "output_morphism")
        self._key_owner = self.ledger.register(
            prefix + "-keys", "output_morphism_interner"
        )
        self._nodes: MutableMapping[int, RecursiveOutputRecord] = self.ledger.make_dict(
            self._node_owner,
            nodes_per_entry=1,
        )
        self._keys: MutableMapping[RecursiveOutputRecord, int] = self.ledger.make_dict(
            self._key_owner,
        )
        self.ledger.register_container(
            self._node_owner,
            self._nodes,
            node_count=lambda: len(self._nodes),
            payloads=self._nodes.items,
        )
        self.ledger.register_container(
            self._key_owner,
            self._keys,
            payloads=self._keys.items,
        )
        self._next_id = 0
        self._stream_owner = self.ledger.register(
            prefix + "-stream-frames", "output_stream_workspace"
        )
        self._stream_frames: MutableMapping[int, _StreamFrame] = self.ledger.make_dict(
            self._stream_owner, nodes_per_entry=_STREAM_FRAME_NODES
        )
        self._stream_next_id = 0
        for name in (
            "requests",
            "node_visits",
            "boundary_evaluations",
            "emitted_digits",
            "frame_peak",
        ):
            self.ledger.bump("recursive_output_stream_" + name, 0)

    def set_temporal_evaluator(
        self,
        evaluator: TemporalOutputEvaluator,
        *,
        complete_action: TemporalActionCompleter | None = None,
    ) -> None:
        """Complete cyclic runtime wiring once, before temporal observation."""
        if not callable(evaluator):
            raise TypeError("temporal output evaluator must be callable")
        if self._evaluate_temporal is not None:
            raise RuntimeError("temporal output evaluator is already configured")
        self._evaluate_temporal = evaluator
        if complete_action is not None:
            if self._complete_temporal_action is not None:
                raise RuntimeError("temporal action completer is already configured")
            self._complete_temporal_action = complete_action

    @property
    def kind(self) -> str:
        return self._KIND

    def _handle(self, local_id: int) -> CoordinateOutputMorphismID:
        return CoordinateOutputMorphismID(self.owner, self._KIND, local_id)

    def resolve(
        self,
        reference: CoordinateOutputMorphismID,
    ) -> RecursiveOutputRecord:
        if type(reference) is not CoordinateOutputMorphismID:
            raise TypeError("expected a recursive coordinate-morphism ID")
        reference.validate(self.owner, self._KIND, size=self._next_id)
        try:
            return self._nodes[reference.local_id]
        except KeyError as exc:
            raise ValueError("stale recursive coordinate-morphism ID") from exc

    @staticmethod
    def _spatially_complete(record: RecursiveOutputRecord) -> bool:
        if isinstance(record, RecursiveOutputTemporal):
            return False
        if isinstance(record, RecursiveOutputBranch):
            return record.spatial_complete
        return True

    def _intern(self, record: RecursiveOutputRecord) -> CoordinateOutputMorphismID:
        if type(record) not in (
            RecursiveOutputSource,
            RecursiveOutputBindingSource,
            RecursiveOutputLeaf,
            RecursiveOutputBranch,
            RecursiveOutputTemporal,
        ):
            raise TypeError("recursive output publication requires a canonical record")
        if isinstance(record, RecursiveOutputSource):
            if self._validate_source is None:
                raise RuntimeError("source-backed output support was not configured")
            self._validate_source(record.source)
        elif isinstance(record, RecursiveOutputBindingSource):
            if self._validate_source_binding is None:
                raise RuntimeError("source-binding output support was not configured")
            self._validate_source_binding(record.source)
        elif isinstance(record, RecursiveOutputLeaf):
            self.interfaces.resolve(record.scalar_interface)
        elif isinstance(record, RecursiveOutputBranch):
            record.__post_init__()
            left = self.resolve(record.left)
            right = self.resolve(record.right)
            if record.spatial_complete != (
                self._spatially_complete(left) and self._spatially_complete(right)
            ):
                raise ValueError("recursive output completion disagrees with children")
            self.interfaces.resolve(record.left_interface)
            self.interfaces.resolve(record.right_interface)
        else:
            self.resolve(record.provider)
            self._validate_temporal_interface(record.interface)
            if self._validate_action is None:
                raise RuntimeError("temporal output support was not configured")
            self._validate_action(record.action)
        found = self._keys.get(record)
        if found is not None:
            self.ledger.bump(_execution_keys.RECURSIVE_OUTPUT_ALIAS_HITS)
            return self._handle(found)
        local_id, self._next_id = reserve_indexed_id(
            self.ledger, self._node_owner, self._key_owner, self._next_id
        )
        record_indexed_node(self._nodes, self._keys, local_id, record)
        self.ledger.bump(_execution_keys.OUTPUT_MORPHISM_PUBLICATIONS)
        return self._handle(local_id)

    def leaf(self, interface: LocalInterfaceID) -> CoordinateOutputMorphismID:
        return self._intern(RecursiveOutputLeaf(interface))

    def source(self, source: SourceCellID) -> CoordinateOutputMorphismID:
        """Intern one original-source leaf without copying its exact symbol."""
        if type(source) is not SourceCellID:
            raise TypeError("source output requires a scoped source-cell ID")
        return self._intern(RecursiveOutputSource(source))

    def source_binding(
        self,
        source: SourceBindingID,
    ) -> CoordinateOutputMorphismID:
        """Intern a complete immutable original-source forest by scoped ID."""
        return self._intern(RecursiveOutputBindingSource(source))

    def source_image(
        self,
        source: SourceCellID,
        action: FieldCellActionID,
        interface: LocalInterfaceID,
    ) -> CoordinateOutputMorphismID:
        """Apply one canonical temporal action to an original source leaf.

        The provider identity is published before boundary observation.  The
        resulting temporal record owns no concrete incoming state and nested
        temporal images are normalized by :meth:`temporal`.
        """
        return self.temporal(self.source(source), action, interface)

    def branch(
        self,
        left: CoordinateOutputMorphismID,
        right: CoordinateOutputMorphismID,
        left_interface: LocalInterfaceID,
        right_interface: LocalInterfaceID,
        left_width: int,
    ) -> CoordinateOutputMorphismID:
        spatial_complete = self._spatially_complete(
            self.resolve(left)
        ) and self._spatially_complete(self.resolve(right))
        return self._intern(
            RecursiveOutputBranch(
                left,
                right,
                left_interface,
                right_interface,
                left_width,
                spatial_complete,
            )
        )

    def temporal(
        self,
        provider: CoordinateOutputMorphismID,
        action: FieldCellActionID,
        interface: LocalInterfaceID,
    ) -> CoordinateOutputMorphismID:
        """Publish an output-complete temporal provider without a midpoint.

        Nested temporal images are combined before the interner is probed.  In
        particular, this prevents persistent ``Image(B, Image(A, X))`` chains:
        the published node is ``Image(compose(A, B), X)``.
        """
        if self._validate_action is None or self._compose_actions is None:
            raise RuntimeError("temporal output support was not configured")
        self._validate_action(action)
        self._validate_temporal_interface(interface)
        original = self.resolve(provider)
        if isinstance(original, RecursiveOutputTemporal):
            action = self._compose_actions(original.action, action)
            self._validate_action(action)
            provider = original.provider
            self.ledger.bump(_execution_keys.RECURSIVE_OUTPUT_TEMPORAL_NORMALIZATIONS)
        else:
            if self._complete_temporal_action is None:
                raise RuntimeError("temporal action completion was not configured")
            action = self._complete_temporal_action(provider, action)
            self._validate_action(action)
        return self._intern(RecursiveOutputTemporal(provider, action, interface))

    def _component(
        self,
        interface: LocalInterfaceID,
        role: str,
    ) -> HigherExpressionID:
        record = self.interfaces.resolve(interface)
        component = getattr(record.components, role)
        if type(component) is not HigherExpressionID:
            raise TypeError(f"recursive output {role} must be an expression")
        return component

    def _inputs(
        self,
        interface: LocalInterfaceID,
        left: BoundaryValue,
        right: BoundaryValue,
    ) -> dict[HigherExpressionID, object]:
        signature = self.interfaces.interface(
            self.interfaces.resolve(interface).signature
        )
        ports = {port.role: port.variable for port in signature.inputs}
        if set(ports) != {"left-boundary", "right-boundary"}:
            raise ValueError("source-bound recursive output has another port interface")
        return {ports["left-boundary"]: left, ports["right-boundary"]: right}

    def observe(
        self,
        output: CoordinateOutputMorphismID,
        coordinate: int,
        left: BoundaryValue,
        right: BoundaryValue,
    ) -> int:
        """Evaluate one coordinate by an iterative one-branch descent."""
        return self._observe(
            output, coordinate, left, right, _shared_keys.OUTPUT_MORPHISM_VISITS
        )

    def observe_extent(
        self,
        output: CoordinateOutputMorphismID,
        coordinate: int,
        left: BoundaryValue,
        right: BoundaryValue,
    ) -> int:
        """Probe the rightmost-active selector without publishing a digit."""
        return self._observe(output, coordinate, left, right, "extent_selector_visits")

    def _push_stream(self, frame: _StreamFrame) -> int:
        self.ledger.reserve(self._stream_owner, entries=1, nodes=_STREAM_FRAME_NODES)
        key = self._stream_next_id
        self._stream_next_id += 1
        try:
            self._stream_frames[key] = frame
        except BaseException:
            self._stream_frames.pop(key, None)
            self.ledger.release(
                self._stream_owner, entries=1, nodes=_STREAM_FRAME_NODES
            )
            raise
        peak = self.ledger.counters.get(
            _execution_keys.RECURSIVE_OUTPUT_STREAM_FRAME_PEAK, 0
        )
        if len(self._stream_frames) > peak:
            self.ledger.bump(
                _execution_keys.RECURSIVE_OUTPUT_STREAM_FRAME_PEAK,
                len(self._stream_frames) - peak,
            )
        return key

    def _pop_stream(self, key: int) -> int | None:
        frame = self._stream_frames.pop(key)
        self.ledger.release(self._stream_owner, entries=1, nodes=_STREAM_FRAME_NODES)
        return frame[5]

    def iter_observe_range(
        self,
        output: CoordinateOutputMorphismID,
        start: int,
        stop: int,
        left: BoundaryValue,
        right: BoundaryValue,
    ) -> Generator[int, None, None]:
        """Stream a completed spatial image without restarting at its root.

        Bounds are in the image's input coordinate chart, with ``stop`` exclusive.
        Each intersected branch transports each demanded boundary once. Frames
        remain charged across yields; closing a partial iterator releases only
        its linked stack, so interleaved streams cannot dispose one another.

        Temporal construction references are deliberately rejected. This method
        cannot turn a deferred temporal point evaluator into a completed image.
        Source-binding reads retain their own separately charged reader cost.
        """
        if type(start) is not int or type(stop) is not int or not 0 <= start <= stop:
            raise ValueError("output range requires 0 <= start <= stop")
        root = self.resolve(output)
        if not self._spatially_complete(root):
            raise TypeError("streaming requires a completed spatial image")
        self.ledger.bump(_execution_keys.RECURSIVE_OUTPUT_STREAM_REQUESTS)
        top: int | None = None
        try:
            if start < stop:
                top = self._push_stream((output, start, stop, left, right, None, None))
            while top is not None:
                (
                    current,
                    lo,
                    hi,
                    incoming_left,
                    incoming_right,
                    previous,
                    pending_left,
                ) = self._stream_frames[top]
                if lo == hi:
                    top = self._pop_stream(top)
                    continue
                if pending_left is not None:
                    incoming_left = self._evaluate(
                        self._component(pending_left, "boundary_left"),
                        self._inputs(pending_left, incoming_left, incoming_right),
                    )
                    self.ledger.bump(
                        _execution_keys.RECURSIVE_OUTPUT_STREAM_BOUNDARY_EVALUATIONS
                    )
                    self._stream_frames[top] = (
                        current,
                        lo,
                        hi,
                        incoming_left,
                        incoming_right,
                        previous,
                        None,
                    )
                node = self.resolve(current)
                self.ledger.bump(_shared_keys.RECURSIVE_OUTPUT_STREAM_NODE_VISITS)
                if isinstance(node, RecursiveOutputTemporal):
                    raise TypeError("streaming requires a completed spatial image")
                if isinstance(node, RecursiveOutputBranch):
                    # Keep the parent charged until both child frames finish.
                    # It also makes allocation failure cleanup transactional.
                    self._stream_frames[top] = (
                        current,
                        lo,
                        lo,
                        incoming_left,
                        incoming_right,
                        previous,
                        None,
                    )
                    if hi > node.left_width:
                        # A pending right branch may never be demanded. Keep
                        # its transfer in the charged frame until it is visited.
                        top = self._push_stream(
                            (
                                node.right,
                                max(0, lo - node.left_width),
                                hi - node.left_width,
                                incoming_left,
                                incoming_right,
                                top,
                                node.left_interface,
                            )
                        )
                    if lo < node.left_width:
                        transported_right = self._evaluate(
                            self._component(node.right_interface, "boundary_right"),
                            self._inputs(
                                node.right_interface, incoming_left, incoming_right
                            ),
                        )
                        self.ledger.bump(
                            _execution_keys.RECURSIVE_OUTPUT_STREAM_BOUNDARY_EVALUATIONS
                        )
                        top = self._push_stream(
                            (
                                node.left,
                                lo,
                                min(hi, node.left_width),
                                incoming_left,
                                transported_right,
                                top,
                                None,
                            )
                        )
                    continue
                # No temporal node can reach the point observer. A binding source
                # can cover multiple original-source coordinates; a leaf cannot.
                for coordinate in range(lo, hi):
                    value = self._observe(
                        current,
                        coordinate,
                        incoming_left,
                        incoming_right,
                        _shared_keys.OUTPUT_MORPHISM_VISITS,
                    )
                    self.ledger.bump(
                        _shared_keys.RECURSIVE_OUTPUT_STREAM_EMITTED_DIGITS
                    )
                    yield value
                top = self._pop_stream(top)
        finally:
            while top is not None:
                top = self._pop_stream(top)

    def _observe(
        self,
        output: CoordinateOutputMorphismID,
        coordinate: int,
        left: BoundaryValue,
        right: BoundaryValue,
        metric: str,
    ) -> int:
        if type(coordinate) is not int or coordinate < 0:
            raise IndexError(coordinate)
        current, offset = output, coordinate
        incoming_left, incoming_right = left, right
        while True:
            node = self.resolve(current)
            if isinstance(node, RecursiveOutputSource):
                if offset:
                    raise IndexError(coordinate)
                if self._read_source is None:
                    raise RuntimeError(
                        "source-backed output support was not configured"
                    )
                result = self._read_source(node.source)
                if type(result) is not int:
                    raise ValueError("source-backed output returned another alphabet")
                self.ledger.bump(_execution_keys.SOURCE_LEAF_VISITS)
                return result
            if isinstance(node, RecursiveOutputBindingSource):
                if self._read_source_binding is None:
                    raise RuntimeError(
                        "source-binding output support was not configured"
                    )
                result = self._read_source_binding(node.source, offset)
                if type(result) is not int:
                    raise ValueError("source-binding output returned another alphabet")
                self.ledger.bump(_execution_keys.SOURCE_LEAF_VISITS)
                return result
            if isinstance(node, RecursiveOutputTemporal):
                if self._evaluate_temporal is None:
                    raise RuntimeError("temporal output evaluation was not configured")
                temporal_result = self._evaluate_temporal(
                    node.provider,
                    node.action,
                    node.interface,
                    offset,
                    incoming_left,
                    incoming_right,
                )
                if type(temporal_result) is not int:
                    raise ValueError("temporal output returned a structured value")
                self.ledger.bump(metric)
                return temporal_result
            if isinstance(node, RecursiveOutputLeaf):
                if offset:
                    raise IndexError(coordinate)
                expression = self._component(node.scalar_interface, "output")
                evaluated = self._evaluate(
                    expression,
                    self._inputs(
                        node.scalar_interface,
                        incoming_left,
                        incoming_right,
                    ),
                )
                if type(evaluated) is not int:
                    raise ValueError(
                        "recursive output leaf returned a structured value"
                    )
                self.ledger.bump(metric)
                return evaluated
            if offset < node.left_width:
                boundary = self._component(node.right_interface, "boundary_right")
                incoming_right = self._evaluate(
                    boundary,
                    self._inputs(node.right_interface, incoming_left, incoming_right),
                )
                current = node.left
            else:
                boundary = self._component(node.left_interface, "boundary_left")
                incoming_left = self._evaluate(
                    boundary,
                    self._inputs(node.left_interface, incoming_left, incoming_right),
                )
                current = node.right
                offset -= node.left_width
            self.ledger.bump(
                _execution_keys.SPATIAL_OBSERVATION_DESCENTS
                if metric == _shared_keys.OUTPUT_MORPHISM_VISITS
                else "extent_selector_spatial_descents"
            )


__all__ = [
    "RecursiveCoordinateMorphismArena",
    "RecursiveOutputBindingSource",
    "RecursiveOutputBranch",
    "RecursiveOutputLeaf",
    "RecursiveOutputRecord",
    "RecursiveOutputSource",
    "RecursiveOutputTemporal",
    "TemporalActionCompleter",
    "TemporalOutputEvaluator",
]
