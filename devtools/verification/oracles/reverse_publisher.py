"""Compatibility harness for source-bound higher reverse/add observations.

This harness shares the production action/interface algebra and is not an
independent arithmetic oracle. Tests use separate literal arithmetic for truth.

The pending object authenticates one immutable source, the certificate's
reverse/add primitive power, and both exterior carry ports before observation.
Its first output-dependent demand currently constructs a recursive provider
through the higher continuation evaluator.  Consequently this module does not
claim that the missing powered reachable-image cutover has been completed.
No completed output tile or endpoint word is retained.  This adapter makes no
generic claim for actions outside that certificate language.
"""

from __future__ import annotations

from collections.abc import Iterator, MutableMapping, MutableSequence, Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.block_effect import BlockEffect, BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.arithmetic.contracts.temporal_family import (
    TemporalFamilyCertificate,
)
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.arithmetic.polynomials.twisted_observer import (
    TwistedCylinderProjection,
)
from number_compiler.hashlife.actions.field_actions import CoordinateOutputMorphismID
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.continuations.higher_interfaces import (
    HigherLocalInterfaceArena,
)
from number_compiler.hashlife.execution.continuations.higher_macro_composer import (
    HigherSpatialMacroComposer,
    SourceBoundHigherMacro,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
    SourceForestID,
)
from number_compiler.hashlife.execution.recursive_outputs import (
    RecursiveCoordinateMorphismArena,
    RecursiveOutputBranch,
    RecursiveOutputLeaf,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.coordinate_program import (
    ReverseCoordinateProgramArena,
)
from number_compiler.sequences.reverse_add.field_action import (
    ReverseActionAutomorphisms,
    ReverseFieldActionArena,
)
from number_compiler.sequences.reverse_add.higher_interface import (
    ReverseHigherInterfaceCompiler,
)
from number_compiler.sequences.reverse_add.higher_schema import (
    ReverseHigherActionSchema,
)
from number_compiler.sequences.reverse_add.powered_local_codec import (
    ReverseLocalActionID,
    ReversePoweredLocalCodec,
)


def _same_semantics(_before: object, _after: object) -> str:
    """The executable coordinate program owns temporal output semantics."""
    return "reverse-runtime"


@dataclass(frozen=True, slots=True)
class _FoldedWord:
    span: int
    forward: TwistedCylinderProjection
    reverse: TwistedCylinderProjection


@dataclass(frozen=True, slots=True)
class _FoldFrame:
    output: CoordinateOutputMorphismID
    span: int
    take: int
    left: object
    right: object
    ready: bool


class ReversePublisherProjection:
    """Sealed lazy request for one authenticated source-bound image.

    ``_macro`` is a demand-constructed recursive provider.  It must not be
    treated as evidence of the stronger source-image composition law while its
    construction or observation records higher continuation work.
    """

    __slots__ = (
        "__weakref__",
        "_binding",
        "_closed",
        "_coordinate_programs",
        "_fold_frame_owner",
        "_fold_frames",
        "_fold_owner",
        "_fold_values",
        "_image_binding",
        "_image_building",
        "_image_failure",
        "_issued_action",
        "_issued_action_identity",
        "_issued_certificate",
        "_issued_primitive",
        "_issued_primitive_initials",
        "_issued_schema",
        "_issued_terminal",
        "_left",
        "_macro",
        "_primitive",
        "_primitive_initials",
        "_right",
        "_schema",
        "_source_ports",
        "_terminal",
        "action",
        "actions",
        "base",
        "certificate",
        "compiler",
        "effect",
        "interfaces",
        "ledger",
        "local_codec",
        "logical_extent",
        "output_encoding",
        "outputs",
        "program",
        "runtime",
        "semantics",
        "source",
        "source_local_action",
        "sources",
    )

    is_source_bound_publisher = True

    def __init__(
        self,
        source_values: Sequence[int],
        *,
        logical_extent: int,
        source_geometry: object,
        ledger: ResourceLedger,
        effect: BlockEffect,
        compiler: LazyCompiler,
        certificate: TemporalFamilyCertificate,
    ) -> None:
        from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry

        if type(certificate) is not TemporalFamilyCertificate:
            raise TypeError("reverse publisher requires an exact family certificate")
        certificate.validate(effect)
        if certificate.family != "reverse-add":
            raise ValueError("reverse publisher requires a reverse-add certificate")
        if certificate.output_encoding not in ("digits", "pair"):
            raise ValueError(
                "reverse publisher certificate has another output encoding"
            )
        base = certificate.base
        pair_steps = certificate.steps
        output_encoding = certificate.output_encoding
        if type(source_geometry) is not SourceGeometry:
            raise TypeError("reverse publisher requires exact source geometry")
        if source_geometry.ledger is not ledger:
            raise ValueError("reverse publisher source belongs to another ledger")
        if type(compiler) is not LazyCompiler or compiler.ledger is not ledger:
            raise ValueError("reverse publisher compiler belongs to another ledger")
        values = tuple(source_values)
        if type(base) is not int or base < 2:
            raise ValueError("reverse publisher requires an exact radix")
        if type(pair_steps) is not int or pair_steps < 0:
            raise ValueError("reverse publisher requires nonnegative pair steps")
        if type(logical_extent) is not int or logical_extent < len(values):
            raise ValueError("reverse publisher requires its complete source extent")
        source_geometry.require_source(values, 2 * base - 1)
        self.ledger, self.base = ledger, base
        self.effect, self.compiler = effect, compiler
        self.certificate = self._issued_certificate = certificate
        self.program: ActionProgramID = compiler.reference(effect)
        self.output_encoding = output_encoding
        self.logical_extent = logical_extent
        self.sources = SourceCellArena(source_geometry)
        self.source: SourceForestID = self.sources.forest(0, logical_extent)

        programs = self._coordinate_programs = ReverseCoordinateProgramArena(
            base, ledger
        )
        self.actions = ReverseFieldActionArena(
            base=base,
            order=8,
            residual_identity="reverse-runtime",
            output_identity="reverse-runtime",
            residual_compose=_same_semantics,
            output_compose=_same_semantics,
            automorphisms=ReverseActionAutomorphisms.trivial(),
            ledger=ledger,
            coordinate_programs=programs,
        )
        residual = self.actions.intern_residual("reverse-runtime")
        geometry = self.actions.resolve(self.actions.identity).geometry
        primitive = self.actions.intern(
            base=base,
            innovation=ReverseAddCyclotomicInnovationBlock.atom(
                (1,), 0, order=8, bits=5
            ),
            carry_forward=CarryFn.ID,
            carry_backward=CarryFn.ID,
            residual=residual,
            output=programs.primitive,
            geometry=geometry,
        )
        terminal = self.actions.intern(
            base=base,
            innovation=ReverseAddCyclotomicInnovationBlock.identity(order=8, bits=5),
            carry_forward=CarryFn.ID,
            carry_backward=CarryFn.ID,
            residual=residual,
            output=programs.terminal,
            geometry=geometry,
        )
        powered = self.actions.power(primitive, pair_steps)
        self.action = (
            self.actions.compose(powered, terminal)
            if output_encoding == "digits"
            else powered
        )
        self._issued_action = self.action
        self._issued_action_identity = self.actions.semantic_identity(self.action)
        self._primitive, self._terminal = primitive, terminal
        self._issued_primitive, self._issued_terminal = primitive, terminal
        self._macro: SourceBoundHigherMacro | None = None
        self._image_binding: tuple[object, ...] | None = None
        self._image_building = False
        self._image_failure = False

        # This is the independent finite two-port source action.  Retaining its
        # scoped ID binds the published image to the exact source forest rather
        # than merely to a tuple of observed digits.
        self.local_codec = ReversePoweredLocalCodec(base, self.sources, ledger=ledger)
        self.source_local_action: ReverseLocalActionID = self.local_codec.source_action(
            self.source
        )
        primitive_schema = self._schema = ReverseHigherActionSchema(
            self.actions, primitive, terminal
        )
        self._issued_schema = primitive_schema
        self._primitive_initials = (
            primitive_schema.initial(primitive, 0),
            primitive_schema.initial(primitive, 1),
        )
        self._issued_primitive_initials = self._primitive_initials
        self._source_ports = tuple(
            self.local_codec.apply_index(
                self.source_local_action,
                BoundarySide(side),
                self._primitive_initials[side],
                reverse=bool(side),
            )
            for side in (0, 1)
        )
        # These source-owned primitive ports seal the pending descriptor before
        # the output-dependent higher image is constructed.
        self._binding = (
            self.source,
            self.action,
            self.source_local_action,
            self._source_ports,
            self.program,
            self.output_encoding,
        )
        self._closed = False
        suffix = len(ledger.inventory())
        self._fold_owner = ledger.register(
            f"reverse-publisher-cylinder-values-{suffix}", "explicit_lowering"
        )
        self._fold_frame_owner = ledger.register(
            f"reverse-publisher-cylinder-frames-{suffix}", "explicit_lowering"
        )
        self._fold_values: MutableMapping[tuple[object, ...], _FoldedWord] = (
            ledger.make_dict(self._fold_owner)
        )
        self._fold_frames: MutableSequence[_FoldFrame] = ledger.make_list(
            self._fold_frame_owner, append_only=False
        )
        ledger.register_container(
            self._fold_owner,
            self._fold_values,
            payloads=self._fold_values.items,
            node_count=lambda: sum(
                2 * word.forward.width + 3 for word in self._fold_values.values()
            ),
        )
        ledger.register_container(
            self._fold_frame_owner,
            self._fold_frames,
            payloads=lambda: self._fold_frames,
            node_count=lambda: len(self._fold_frames),
        )
        ledger.register_execution_root(self)
        ledger.bump("reverse_source_bound_publisher_publications")

    @property
    def macro(self) -> SourceBoundHigherMacro:
        """Construct the reachable image at its first output-dependent demand."""
        self._open()
        return self._ensure_image()

    def _ensure_image(self) -> SourceBoundHigherMacro:
        """Build the current recursive provider without hiding cutover work.

        The production P0 requires a future constructor that composes the
        source-restricted image itself.  Until that constructor exists, the
        higher evaluator below remains deliberately visible to resource and
        release accounting.
        """
        found = self._macro
        if found is not None:
            return found
        if self._image_failure:
            raise RuntimeError(
                "reverse source-bound image construction previously failed"
            )
        if self._image_building:
            raise RuntimeError("recursive reverse image construction")
        self._image_building = True
        try:
            semantics = HigherSemanticArena(self._schema)
            runtime = HigherBimachineRuntime(semantics, self.sources)
            interfaces = HigherLocalInterfaceArena(semantics)
            higher_compiler = ReverseHigherInterfaceCompiler(
                self.actions,
                self._schema,
                semantics,
                runtime,
                interfaces,
            )
            compiled = higher_compiler.compile(self.action)
            outputs = RecursiveCoordinateMorphismArena(
                interfaces,
                evaluate=semantics.evaluate,
            )
            publisher = HigherSpatialMacroComposer(
                semantics,
                interfaces,
                outputs,
                self.sources,
                self.action,
                compiled.interface,
                compiled.left,
                compiled.symbol,
                compiled.right,
            )
            macro = publisher.compile(self.source)
            publisher.clear()
            higher_ports = tuple(
                semantics.evaluate(
                    runtime.boundary(
                        self._primitive,
                        self.source,
                        side,
                        0,
                        self.logical_extent,
                    )
                )
                for side in (0, 1)
            )
            if higher_ports != self._source_ports:
                raise AssertionError(
                    "reverse local codec disagrees with higher source ports"
                )
            left = semantics.evaluate(runtime.initial(self.action, 0))
            right = semantics.evaluate(runtime.initial(self.action, 1))
            # Publish the coupled runtime only after every constituent was built.
            self.semantics, self.runtime, self.interfaces = (
                semantics,
                runtime,
                interfaces,
            )
            self.outputs, self._left, self._right = outputs, left, right
            self._image_binding = (macro.interface, macro.output)
            self._macro = macro
            self.ledger.bump("reverse_source_bound_image_first_demands")
            return macro
        except Exception:
            # Every arena allocated above is independently registered and
            # charged on the shared ledger.  Make the failed demand terminal so
            # a retry cannot accumulate another abandoned arena family.
            self._image_failure = True
            self.ledger.bump("reverse_source_bound_image_failed_demands")
            raise
        finally:
            self._image_building = False

    def _validate_action_binding(self) -> None:
        """Read-only action authority shared by execution and reporting."""
        if self.certificate is not self._issued_certificate:
            raise ValueError("reverse publisher certificate binding was changed")
        self.certificate.validate(self.effect)
        self.actions.validate_action(self.action)
        if self.action != self._issued_action:
            raise ValueError(
                "reverse publisher binding was changed: canonical action was changed"
            )
        if (
            self._primitive != self._issued_primitive
            or self._terminal != self._issued_terminal
        ):
            raise ValueError("reverse publisher primitive actions were changed")
        if (
            self._schema is not self._issued_schema
            or self._schema.actions is not self.actions
            or self._schema.primitive != self._primitive
            or self._schema.terminal != self._terminal
        ):
            raise ValueError("reverse publisher action schema was changed")
        action_record = self.actions.resolve(self.action)
        if self.actions.semantic_identity(self.action) != self._issued_action_identity:
            raise ValueError("reverse publisher canonical action semantics changed")
        self.actions.validate_action(self._primitive)
        self.actions.validate_action(self._terminal)
        if (
            self.actions.resolve(self._primitive).output
            != self._coordinate_programs.primitive
            or self.actions.resolve(self._terminal).output
            != self._coordinate_programs.terminal
        ):
            raise ValueError("reverse publisher primitive program binding changed")
        coordinate_program = self._coordinate_programs.resolve(action_record.output)
        if (
            coordinate_program.base != self.base
            or coordinate_program.pair_steps != self.certificate.steps
            or coordinate_program.normalized != (self.output_encoding == "digits")
            or not coordinate_program.executable
        ):
            raise ValueError(
                "reverse publisher action differs from certificate program"
            )
        if (
            tuple(self._schema.initial(self._primitive, side) for side in (0, 1))
            != self._issued_primitive_initials
            or self._primitive_initials != self._issued_primitive_initials
        ):
            raise ValueError("reverse publisher primitive initial states changed")

    def _open(self) -> ReversePublisherProjection:
        issued = self.ledger._execution_roots.get(id(self))
        if issued is None or issued() is not self:
            raise ValueError("reverse publisher was not issued by its ledger")
        if type(self._closed) is not bool or self._closed:
            raise ValueError("closed reverse publisher")
        if self.compiler.reference(self.effect) != self.program:
            raise ValueError("reverse publisher operator binding was changed")
        if self.compiler.resolve(self.program) is not self.effect:
            raise ValueError("reverse publisher operator is no longer canonical")
        self._validate_action_binding()
        self.sources.resolve_forest(self.source)
        self.local_codec.resolve(self.source_local_action)
        if self._binding != (
            self.source,
            self.action,
            self.source_local_action,
            self._source_ports,
            self.program,
            self.output_encoding,
        ):
            raise ValueError("reverse publisher source/action binding was changed")
        if self.local_codec.source_action(self.source) != self.source_local_action:
            raise ValueError("reverse publisher two-port source action was changed")
        observed_ports = tuple(
            self.local_codec.apply_index(
                self.source_local_action,
                BoundarySide(side),
                self._primitive_initials[side],
                reverse=bool(side),
            )
            for side in (0, 1)
        )
        if observed_ports != self._source_ports:
            raise ValueError("reverse publisher two-port source semantics were changed")
        macro = self._macro
        if macro is not None:
            self.interfaces.resolve(macro.interface)
            self.outputs.resolve(macro.output)
            if self._image_binding != (macro.interface, macro.output):
                raise ValueError("reverse publisher image binding was changed")
        return self

    def validate_execution(self) -> None:
        self._open()

    def point(self, position: int) -> int:
        self._open()
        if type(position) is not int:
            raise TypeError("reverse publisher coordinate must be an exact integer")
        if not 0 <= position < self.logical_extent:
            raise IndexError(position)
        macro = self._ensure_image()
        value = self.outputs.observe(
            macro.output,
            position,
            self._left,
            self._right,
        )
        if type(value) is not int or not 0 <= value <= 2 * self.base - 1:
            raise ValueError("reverse publisher emitted another alphabet")
        self.ledger.bump("reverse_source_bound_publisher_point_observations")
        return value

    def active_width(self) -> int:
        self._open()
        macro = self._ensure_image()
        record = self.interfaces.resolve(macro.interface)
        signature = self.interfaces.interface(record.signature)
        ports = {port.role: port.variable for port in signature.inputs}
        if set(ports) != {"left-boundary", "right-boundary"}:
            raise ValueError("reverse reachable image lost its two exterior ports")
        width = self.semantics.evaluate(
            macro.extent,
            {
                ports["left-boundary"]: self._left,
                ports["right-boundary"]: self._right,
            },
        )
        if type(width) is not int or not 0 <= width <= self.logical_extent:
            raise ValueError("reverse reachable image returned an invalid extent")
        self.ledger.bump("reverse_source_bound_publisher_width_observations")
        return width

    def iter_active(self) -> Iterator[int]:
        width = self.active_width()
        blank = 2 * self.base - 1
        for position in range(width):
            value = self.point(position)
            if value == blank:
                raise AssertionError("blank inside reverse reachable image")
            yield value

    def _bound_component(
        self,
        interface: LocalInterfaceID,
        role: str,
        left: object,
        right: object,
    ) -> object:
        record, ports = self.interfaces.bound_interface(
            interface, error="recursive publisher child lost its exterior ports"
        )
        return self.semantics.evaluate(
            getattr(record.components, role),
            {
                ports["left-boundary"]: left,
                ports["right-boundary"]: right,
            },
        )

    def _fold_sheet(
        self, extent: int, width: int, sign: int
    ) -> TwistedCylinderProjection:
        """Fold one clipped recursive output without scalar point callbacks."""
        values, frames = self._fold_values, self._fold_frames
        if values or frames:
            raise ValueError("reverse cylinder workspace is already in use")

        def push(frame: _FoldFrame) -> None:
            self.ledger.reserve(self._fold_frame_owner, entries=1, nodes=1)
            frames.append(frame)

        def pop() -> _FoldFrame:
            frame = frames.pop()
            self.ledger.release(self._fold_frame_owner, entries=1, nodes=1)
            return frame

        def put(key: tuple[object, ...], word: _FoldedWord) -> None:
            nodes = 2 * word.forward.width + 3
            self.ledger.reserve(self._fold_owner, entries=1, nodes=nodes)
            values[key] = word

        try:
            push(
                _FoldFrame(
                    self.macro.output,
                    self.macro.width,
                    extent,
                    self._left,
                    self._right,
                    False,
                )
            )
            root_key: tuple[object, ...] | None = None
            while frames:
                frame = pop()
                key = (
                    frame.output,
                    frame.span,
                    frame.take,
                    frame.left,
                    frame.right,
                )
                if root_key is None:
                    root_key = key
                if key in values:
                    self.ledger.bump("reverse_publisher_cylinder_cache_hits")
                    continue
                node = self.outputs.resolve(frame.output)
                if type(node) is RecursiveOutputLeaf:
                    if frame.span != 1 or frame.take != 1:
                        raise ValueError("reverse publisher leaf has another span")
                    digit = self.outputs.observe(
                        frame.output, 0, frame.left, frame.right
                    )
                    if not 0 <= digit < self.base:
                        raise ValueError("cylinder requires normalized reverse digits")
                    projection = TwistedCylinderProjection.observe(
                        (digit,), width=width, sign=sign
                    )
                    put(key, _FoldedWord(1, projection, projection))
                elif type(node) is RecursiveOutputBranch:
                    left_span = node.left_width
                    right_span = frame.span - left_span
                    left_take = min(frame.take, left_span)
                    right_take = max(0, frame.take - left_span)
                    left_right = self._bound_component(
                        node.right_interface,
                        "boundary_right",
                        frame.left,
                        frame.right,
                    )
                    right_left = self._bound_component(
                        node.left_interface,
                        "boundary_left",
                        frame.left,
                        frame.right,
                    )
                    left_key = (
                        node.left,
                        left_span,
                        left_take,
                        frame.left,
                        left_right,
                    )
                    right_key = (
                        node.right,
                        right_span,
                        right_take,
                        right_left,
                        frame.right,
                    )
                    if not frame.ready:
                        push(
                            _FoldFrame(
                                frame.output,
                                frame.span,
                                frame.take,
                                frame.left,
                                frame.right,
                                True,
                            )
                        )
                        if right_take:
                            push(
                                _FoldFrame(
                                    node.right,
                                    right_span,
                                    right_take,
                                    right_left,
                                    frame.right,
                                    False,
                                )
                            )
                        push(
                            _FoldFrame(
                                node.left,
                                left_span,
                                left_take,
                                frame.left,
                                left_right,
                                False,
                            )
                        )
                        continue
                    first = values[left_key]
                    if not right_take:
                        put(key, first)
                    else:
                        after = values[right_key]
                        put(
                            key,
                            _FoldedWord(
                                first.span + after.span,
                                first.forward.append(after.forward, span=first.span),
                                after.reverse.append(first.reverse, span=after.span),
                            ),
                        )
                        self.ledger.bump(
                            "reverse_publisher_cylinder_coefficient_additions",
                            2 * width,
                        )
                else:
                    raise ValueError(
                        "reverse reachable image contains an unbound output node"
                    )
                self.ledger.bump("reverse_publisher_cylinder_node_evaluations")
            if root_key is None:
                raise AssertionError("reverse cylinder did not visit its root")
            word = values[root_key]
            return TwistedCylinderProjection(
                width,
                sign,
                tuple(
                    a - b
                    for a, b in zip(
                        word.forward.coefficients,
                        word.reverse.coefficients,
                        strict=True,
                    )
                ),
            )
        finally:
            frame_count = len(frames)
            if frame_count:
                frames.clear()
                self.ledger.release(
                    self._fold_frame_owner,
                    entries=frame_count,
                    nodes=frame_count,
                )
            value_count = len(values)
            value_nodes = sum(2 * word.forward.width + 3 for word in values.values())
            values.clear()
            self.ledger.release(
                self._fold_owner, entries=value_count, nodes=value_nodes
            )

    def mirror_obstruction(
        self, *, first_width: int = 1
    ) -> TwistedCylinderProjection | None:
        self._open()
        if type(first_width) is not int or first_width < 1:
            raise ValueError("positive first sheet width required")
        extent = self.active_width()
        width, sign = first_width, 1
        while True:
            projection = self._fold_sheet(extent, width, sign)
            if projection.nonzero:
                return projection
            if width >= extent:
                return None
            if sign == 1:
                sign = -1
            else:
                width *= 2

    def retained_entries(self) -> int:
        self._open()
        return self.ledger.entries

    def close(self) -> None:
        self._closed = True


def build_reverse_publisher_projection(
    source: Sequence[int],
    *,
    logical_extent: int,
    source_geometry: object,
    ledger: ResourceLedger,
    effect: BlockEffect,
    compiler: LazyCompiler,
    certificate: TemporalFamilyCertificate,
) -> ReversePublisherProjection:
    """Construct the sole production reverse/add reachable-image publisher."""
    return ReversePublisherProjection(
        source,
        logical_extent=logical_extent,
        source_geometry=source_geometry,
        ledger=ledger,
        effect=effect,
        compiler=compiler,
        certificate=certificate,
    )


__all__ = ["ReversePublisherProjection", "build_reverse_publisher_projection"]
