"""Point and active-extent observations over an executable temporal diamond."""

from __future__ import annotations

from collections.abc import MutableSequence
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.actions.diamond_actions import CellID
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Initial,
    Result,
    Transfer,
)
from number_compiler.hashlife.execution.diamond_certificate import (
    DiamondCompositionCertificate,
    certify,
)
from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryStateID,
    ImageBinding,
)
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.resources.metric_keys import (
    hashlife_observation as _observation_keys,
)


def _boundary(result: Result) -> BoundaryStateID:
    if type(result) is not BoundaryStateID:
        raise AssertionError("a boundary observation produced a scalar")
    return result


@dataclass(frozen=True, slots=True)
class _ChunkContext:
    start: int
    cell: CellID
    left: BoundaryStateID


class DiamondApplication:
    """A compiled action plus its source; queries retain no scalar results."""

    def __init__(
        self,
        runtime: DiamondRuntime,
        root: ActionProgramID,
        *,
        program: ActionProgramID | None = None,
    ) -> None:
        node = runtime.actions.resolve(root)
        source = runtime.cells.source_geometry._construction.source
        if node.kind != "identity" and (node.base, node.blank) != (
            source.base,
            source.blank,
        ):
            raise ValueError("action and source alphabets disagree")
        compiler_program = (
            runtime.actions.compiler.reference(
                runtime.actions.compiler.resolve(program)
            )
            if program is not None
            else None
        )
        self.runtime, self.root = runtime, root
        self.program = compiler_program
        self.compiler, self.ledger = runtime.actions.compiler, runtime.ledger
        self.ledger.register_execution_root(self)
        observer = runtime.actions.compiler.atom(
            NonblankBlockEffect(source.base, source.blank)
        )
        self.observer = runtime.actions.intern(observer)
        certificate = certify(runtime, root)
        owner = self.ledger.register(
            f"diamond-certificate-{len(self.ledger.inventory())}",
            "composition_certificate",
        )
        self._certificates: MutableSequence[DiamondCompositionCertificate] = (
            self.ledger.make_list(owner)
        )
        self.ledger.reserve(owner, entries=1, nodes=1)
        self._certificates.append(certificate)
        self.composition_certificate = certificate
        hooks = runtime.family_hooks
        cycle = hooks.make_cycle(runtime, root) if hooks is not None else None
        self._issued_cycle = cycle
        cycle_owner = self.ledger.register(
            f"diamond-cycle-{len(self.ledger.inventory())}", "finite_cycle_certificate"
        )
        self._cycles: MutableSequence[object] = self.ledger.make_list(cycle_owner)
        if cycle is not None:
            self.ledger.reserve(cycle_owner, entries=1, nodes=1)
            self._cycles.append(cycle)

    def _cycle(self) -> object | None:
        if not self._cycles:
            return None
        projection = self._cycles[0]
        hooks = self.runtime.family_hooks
        geometry = self.runtime.cells.source_geometry
        source = geometry._read_root
        if (
            hooks is None
            or projection is not self._issued_cycle
            or not hooks.is_cycle_projection(projection)
            or not hooks.validate_cycle(self.runtime, self.root, projection)
            or source is None
        ):
            raise ValueError("cycle projection belongs to another source or action")
        return projection

    def _finite_cell_observation(self, channel: str, coordinate: int) -> int | None:
        """Execute the declared fixed-cell contract for a finite primitive.

        A single full dyadic source has precisely this contract's boundary
        conditions. Other operators and truncated spans need their separate
        composition/normalization interfaces; this does not certify those.
        """
        runtime = self.runtime
        node = runtime.actions.resolve(self.root)
        source = runtime.cells.source_geometry._read_root
        if (
            node.kind != "atom"
            or source is None
            or source.length <= 0
            or source.length & (source.length - 1)
            or source.length.bit_length() > 63
        ):
            return None
        definition = runtime.actions.primitive(self.root)
        if type(definition) is not FiniteBlockEffect:
            return None
        primitive = runtime.kernel(self.root)
        kernel = runtime.primitive_ids[self.root]
        cell = runtime.cells.source(0, source.length.bit_length() - 1)
        quotient = runtime.compile_primitive_macro(kernel, cell)
        from number_compiler.arithmetic.contracts.block_effect import BoundarySide

        return runtime.observe_primitive_macro(
            quotient,
            channel,
            left=primitive.initial(BoundarySide.LEFT),
            right=primitive.initial(BoundarySide.RIGHT),
            coordinate=coordinate,
        )

    @source_reads_only
    def point(self, position: int) -> int:
        self.runtime.actions.resolve(self.root)
        source = self.runtime.cells.source_geometry._read_root
        if type(position) is not int or position < 0:
            raise ValueError("point coordinate must be nonnegative")
        if source is None or position >= source.length:
            raise IndexError(position)
        cycle = self._cycle()
        self.ledger.bump(_observation_keys.DIAMOND_POINT_QUERIES)
        if cycle is not None:
            self.ledger.bump(_observation_keys.PHYSICAL_CYCLE_POINT_QUERIES)
            hooks = self.runtime.family_hooks
            if hooks is None:
                raise AssertionError("cycle projection lost its family owner")
            return hooks.cycle_point(cycle, position)
        finite = self._finite_cell_observation("output", position)
        if finite is not None:
            return finite
        return self.runtime.point(self.root, position)

    def _original(
        self, cell: CellID, left: BoundaryStateID, right: BoundaryStateID
    ) -> ImageBinding:
        return ImageBinding(self.runtime.actions.identity, cell, left, right)

    def _active(self, provider: ImageBinding, initial: BoundaryStateID) -> bool:
        self.ledger.bump(_observation_keys.WIDTH_OBSERVER_REQUESTS)
        result = _boundary(
            self.runtime.execute(Transfer(provider, self.observer, initial, 1))
        )
        value = self.runtime.boundaries.state(result)
        if value.literal not in (0, 1):
            raise AssertionError("activity observer did not return its finite state")
        return value.literal == 1

    @source_reads_only
    def active_width(self, maxwidth: int | None = None) -> int:
        """Find the last nonblank leaf by parent observations, never point scans.

        A truncated query still uses the original field's suffix interfaces;
        truncating the query does not replace that suffix with blank input.
        """
        runtime = self.runtime
        runtime.actions.resolve(self.root)
        runtime.actions.resolve(self.observer)
        source = runtime.cells.source_geometry._read_root
        if source is not None and maxwidth is None:
            maxwidth = source.length
        if (
            source is None
            or type(maxwidth) is not int
            or not 0 <= maxwidth <= source.length
        ):
            raise ValueError("width bound must fit the retained original source extent")
        cycle = self._cycle()
        self.ledger.bump(_observation_keys.WIDTH_QUERIES)
        if cycle is not None:
            self.ledger.bump(_observation_keys.PHYSICAL_CYCLE_WIDTH_QUERIES)
            hooks = self.runtime.family_hooks
            if hooks is None:
                raise AssertionError("cycle projection lost its family owner")
            return hooks.cycle_width(cycle, maxwidth)
        if not maxwidth:
            return 0
        if maxwidth == source.length:
            finite = self._finite_cell_observation("extent", 0)
            if finite is not None:
                return finite
        left = _boundary(runtime.execute(Initial(self.root, 0)))
        right = _boundary(runtime.execute(Initial(self.root, 1)))
        unit_left = _boundary(runtime.execute(Initial(runtime.actions.identity, 0)))
        unit_right = _boundary(runtime.execute(Initial(runtime.actions.identity, 1)))
        activity = _boundary(runtime.execute(Initial(self.observer, 1)))
        forest = runtime.cells.source_span(0, maxwidth)
        contexts: list[_ChunkContext] = []
        for index, (start, cell) in enumerate(forest):
            contexts.append(_ChunkContext(start, cell, left))
            self.ledger.bump(_observation_keys.WIDTH_FOREST_CONTEXT_VISITS)
            if index + 1 < len(forest):
                left = _boundary(
                    runtime.execute(
                        Transfer(
                            self._original(cell, unit_left, unit_right),
                            self.root,
                            left,
                            0,
                        )
                    )
                )
        peak = self.ledger.counters.get(_observation_keys.WIDTH_CONTEXT_PEAK_RECORDS, 0)
        self.ledger.bump(
            _observation_keys.WIDTH_CONTEXT_PEAK_RECORDS,
            max(0, len(contexts) - peak),
        )
        for _, cell in reversed(
            runtime.cells.source_span(maxwidth, source.length - maxwidth)
        ):
            right = _boundary(
                runtime.execute(
                    Transfer(
                        self._original(cell, unit_left, unit_right), self.root, right, 1
                    )
                )
            )
        for context in reversed(contexts):
            start, cell, left = context.start, context.cell, context.left
            self.ledger.bump(_observation_keys.WIDTH_PARENT_VISITS)
            if not self._active(ImageBinding(self.root, cell, left, right), activity):
                right = _boundary(
                    runtime.execute(
                        Transfer(
                            self._original(cell, unit_left, unit_right),
                            self.root,
                            right,
                            1,
                        )
                    )
                )
                continue
            while runtime.cells.node(cell).level:
                self.ledger.bump(_observation_keys.WIDTH_DESCENT_STEPS)
                low, high = runtime.cells.split(cell)
                middle = start + runtime.cells.node(low).width
                middle_left = _boundary(
                    runtime.execute(
                        Transfer(
                            self._original(low, unit_left, unit_right),
                            self.root,
                            left,
                            0,
                        )
                    )
                )
                if self._active(
                    ImageBinding(self.root, high, middle_left, right), activity
                ):
                    start, cell, left = middle, high, middle_left
                else:
                    right = _boundary(
                        runtime.execute(
                            Transfer(
                                self._original(high, unit_left, unit_right),
                                self.root,
                                right,
                                1,
                            )
                        )
                    )
                    cell = low
            return start + 1
        return 0

    def retained_entries(self) -> int:
        return self.ledger.entries
