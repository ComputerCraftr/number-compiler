"""Source-bound reverse/add images with fused and guarded affine pullbacks."""

from __future__ import annotations

from collections.abc import Hashable, Iterator
from dataclasses import dataclass
from typing import cast

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaHandle,
    ArenaToken,
    ExactSource,
)
from number_compiler.arithmetic.formula.skew_residue_laws import (
    skew_normalized_digit,
)
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.reverse_add.source_chamber import (
    SameCarryChamberRejected,
    same_carry_digit,
    validate_same_carry_chamber,
)
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts


class ReverseCylinderConstructionUnavailable(ValueError):
    """The requested temporal image needs the unbuilt successor cylinder."""


@dataclass(frozen=True, slots=True)
class ReverseSource(ArenaHandle):
    """Authenticated handle for the original input digits."""


@dataclass(frozen=True, slots=True)
class _ReverseSourceRecord:
    exact: ExactSource


@dataclass(frozen=True, slots=True)
class ReverseActionID(ArenaHandle):
    """Ledger-owned identity of one canonical reverse/add temporal action."""


@dataclass(frozen=True, slots=True)
class ReverseActionNode:
    steps: int
    before: ReverseActionID | None
    after: ReverseActionID | None
    depth: int


@dataclass(frozen=True, slots=True)
class ReverseImagePayload:
    """Image metadata only; endpoint digits are always reconstructed on demand."""

    action: ReverseActionID


class ReverseActionArena:
    """Canonical, authenticated binary descriptors for powers of one step."""

    _KIND = "reverse-source-action"
    _SOURCE_KIND = "reverse-source"

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("reverse action arena requires a resource ledger")
        self.ledger = ledger
        self.owner = ArenaToken("reverse-source-actions")
        prefix = f"reverse-source-actions-{ledger.owner_count}"
        self._nodes = OwnedMemo[int, ReverseActionNode](
            ledger,
            ledger.register(prefix + "-nodes", "reverse_source_action"),
            nodes_per_entry=1,
        )
        self._normal = OwnedMemo[int, ReverseActionID](
            ledger,
            ledger.register(prefix + "-normal", "reverse_source_action_normal_form"),
            composition_entries=True,
        )
        self._sources = OwnedMemo[int, _ReverseSourceRecord](
            ledger,
            ledger.register(prefix + "-sources", "reverse_original_source"),
            nodes_per_entry=1,
        )
        self._workspace_owner = ledger.register(
            prefix + "-workspace", "reverse_source_action_workspace"
        )
        self._workspace: LedgerList[tuple[int, bool]] = ledger.make_list(
            self._workspace_owner, append_only=False
        )
        ledger.register_container(
            self._workspace_owner,
            self._workspace,
            node_count=lambda: len(self._workspace),
            payloads=lambda: self._workspace,
        )
        self._source_authority: (
            tuple[_ReverseSourceRecord, ExactSource, tuple[int, ...], int] | None
        ) = None
        self._closed = False
        try:
            identity = self._append(ReverseActionNode(0, None, None, 0))
            primitive = self._append(ReverseActionNode(1, None, None, 1))
        except BaseException:
            self._normal.dispose()
            self._nodes.dispose()
            self._sources.dispose()
            self.ledger.mark_disposed(self._workspace_owner)
            self.owner = ArenaToken("failed-reverse-source-actions")
            self._closed = True
            raise
        self.identity, self.primitive = identity, primitive

    def _check_open(self) -> None:
        if self._closed:
            raise ValueError("disposed reverse action arena")

    def _append(self, node: ReverseActionNode) -> ReverseActionID:
        local_id = len(self._nodes)
        handle = ReverseActionID(self.owner, self._KIND, local_id)
        self._nodes[local_id] = node
        try:
            self._normal[node.steps] = handle
        except BaseException:
            del self._nodes[local_id]
            raise
        return handle

    def node(self, action: ReverseActionID) -> ReverseActionNode:
        self._check_open()
        if type(action) is not ReverseActionID:
            raise TypeError("reverse/add image requires a scoped action ID")
        action.validate(self.owner, self._KIND, size=len(self._nodes))
        node = self._nodes[action.local_id]
        if self._normal.get(node.steps) != action:
            raise ValueError("reverse action normal form was altered")
        if action.local_id == 0:
            if node != ReverseActionNode(0, None, None, 0):
                raise ValueError("reverse identity action was altered")
        elif action.local_id == 1:
            if node != ReverseActionNode(1, None, None, 1):
                raise ValueError("reverse primitive action was altered")
        else:
            if (
                type(node.steps) is not int
                or node.steps < 2
                or type(node.before) is not ReverseActionID
                or type(node.after) is not ReverseActionID
                or node.before.local_id >= action.local_id
                or node.after.local_id >= action.local_id
            ):
                raise ValueError("reverse composite action was altered")
            node.before.validate(self.owner, self._KIND, size=action.local_id)
            node.after.validate(self.owner, self._KIND, size=action.local_id)
            before = self._nodes[node.before.local_id]
            after = self._nodes[node.after.local_id]
            if (
                self._normal.get(before.steps) != node.before
                or self._normal.get(after.steps) != node.after
                or before.steps + after.steps != node.steps
                or node.depth != 1 + max(before.depth, after.depth)
            ):
                raise ValueError("reverse composite action geometry was altered")
        return node

    def admit_source(self, seed: int, base: int) -> ReverseSource:
        self._check_open()
        if self._source_authority is not None:
            raise ValueError("reverse action arena already owns an original source")
        digits: list[int] = []
        value = seed
        while True:
            digits.append(value % base)
            value //= base
            if not value:
                break
        exact = ExactSource(tuple(digits), base, orbit="reverse-add")
        record = _ReverseSourceRecord(exact)
        handle = ReverseSource(self.owner, self._SOURCE_KIND, 0)
        self._sources[0] = record
        self._source_authority = record, exact, exact.digits, exact.base
        return handle

    def source(self, source: ReverseSource) -> ExactSource:
        self._check_open()
        if type(source) is not ReverseSource:
            raise TypeError("reverse/add image requires a scoped source ID")
        source.validate(self.owner, self._SOURCE_KIND, size=len(self._sources))
        record = self._sources[source.local_id]
        authority = self._source_authority
        if (
            authority is None
            or record is not authority[0]
            or record.exact is not authority[1]
            or record.exact.digits is not authority[2]
            or record.exact.base != authority[3]
            or record.exact.orbit != "reverse-add"
            or record.exact.blank != 0
            or record.exact.extent is not None
            or record.exact.alphabet_size is not None
        ):
            raise ValueError("reverse original source authority was altered")
        return record.exact

    def action(self, steps: int) -> ReverseActionID:
        self._check_open()
        steps = require_integer(steps, "reverse/add steps", 0)
        found = self._normal.get(steps)
        if found is not None:
            self.node(found)
            return found
        if self._workspace:
            raise RuntimeError("reverse action construction workspace is active")
        credit = 0
        starting_nodes = len(self._nodes)

        def push(item: tuple[int, bool]) -> None:
            nonlocal credit
            self.ledger.reserve(self._workspace_owner, entries=1, nodes=1)
            credit += 1
            self._workspace.append(item)

        try:
            push((steps, False))
            while self._workspace:
                current, expanded = self._workspace.pop()
                self.ledger.release(self._workspace_owner, entries=1, nodes=1)
                credit -= 1
                if self._normal.get(current) is not None:
                    continue
                left_steps = current // 2
                right_steps = current - left_steps
                if not expanded:
                    push((current, True))
                    if self._normal.get(right_steps) is None:
                        push((right_steps, False))
                    if self._normal.get(left_steps) is None:
                        push((left_steps, False))
                    continue
                before = self._normal[left_steps]
                after = self._normal[right_steps]
                depth = 1 + max(self.node(before).depth, self.node(after).depth)
                self._append(ReverseActionNode(current, before, after, depth))
            return self._normal[steps]
        except BaseException:
            while self._workspace:
                self._workspace.pop()
            if credit:
                self.ledger.release(self._workspace_owner, entries=credit, nodes=credit)
            while len(self._nodes) > starting_nodes:
                local_id = len(self._nodes) - 1
                node = self._nodes[local_id]
                del self._normal[node.steps]
                del self._nodes[local_id]
            raise

    def compose(
        self, before: ReverseActionID, after: ReverseActionID
    ) -> ReverseActionID:
        return self.action(self.node(before).steps + self.node(after).steps)

    @property
    def operator_nodes(self) -> int:
        return max(0, len(self._nodes) - 1)

    @property
    def compose_operations(self) -> int:
        return sum(node.steps >= 2 for node in self._nodes.values())

    def dispose(self) -> None:
        if self._closed:
            return
        self._normal.dispose()
        self._nodes.dispose()
        self._sources.dispose()
        self.ledger.mark_disposed(self._workspace_owner)
        self._source_authority = None
        self.owner = ArenaToken("disposed-reverse-source-actions")
        self._closed = True


def _source_digit(source: ExactSource, position: int) -> int:
    return source.digits[position]


class _ReverseSourceImageAdapter(SourceBoundImageAdapter):
    family = "reverse-add"
    semantic_version = "source-cylinder-v5-composed-carry-ports"

    def __init__(self, actions: ReverseActionArena) -> None:
        self.actions = actions
        self.ledger = actions.ledger
        self._ports: SourceCarryPorts | None = None

    def ports(self, source: ExactSource) -> SourceCarryPorts:
        """One source-bound spatial projection shared by every consumer."""
        ports = self._ports
        if ports is None:
            ports = SourceCarryPorts(source, self.ledger)
            self._ports = ports
        ports.check_source(source)
        return ports

    def dispose(self) -> None:
        if self._ports is not None:
            self._ports.dispose()
            self._ports = None

    def validate_source(self, source: Hashable) -> None:
        if type(source) is not ReverseSource:
            raise TypeError("reverse/add image requires its exact original source")
        self.actions.source(source)

    def validate_action(self, action: Hashable) -> None:
        if type(action) is not ReverseActionID:
            raise TypeError("reverse/add image requires a scoped action ID")
        self.actions.node(action)

    def validate_payload(self, payload: Hashable) -> None:
        if type(payload) is not ReverseImagePayload:
            raise TypeError("reverse/add image has another payload sort")
        self.actions.node(payload.action)

    def identity_action(self, source: Hashable) -> ReverseActionID:
        self.validate_source(source)
        return self.actions.identity

    def action_children(
        self, action: Hashable
    ) -> tuple[ReverseActionID, ReverseActionID] | None:
        self.validate_action(action)
        node = self.actions.node(cast(ReverseActionID, action))
        if node.before is None or node.after is None:
            return None
        return node.before, node.after

    def compose_actions(self, before: Hashable, after: Hashable) -> ReverseActionID:
        self.validate_action(before)
        self.validate_action(after)
        return self.actions.compose(
            cast(ReverseActionID, before), cast(ReverseActionID, after)
        )

    def admit_source(self, source: Hashable) -> SourceImageCandidate:
        self.validate_source(source)
        exact = self.actions.source(cast(ReverseSource, source))
        return SourceImageCandidate(
            ReverseImagePayload(self.actions.identity),
            0,
            boundary_ports=(0,),
            radix=exact.base,
            precision=len(exact.digits),
        )

    def apply_primitive(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_action(action)
        self.validate_payload(source.payload)
        exact = cast(ReverseActionID, action)
        node = self.actions.node(exact)
        prior_steps = self.actions.node(
            cast(ReverseImagePayload, source.payload).action
        ).steps
        if node.steps not in (0, 1) or prior_steps + node.steps > 1:
            raise ReverseCylinderConstructionUnavailable(
                "reverse/add primitive application cannot extend an image "
                f"from {prior_steps} to {prior_steps + node.steps} temporal steps"
            )
        cumulative = self.actions.compose(
            cast(ReverseImagePayload, source.payload).action, exact
        )
        origin = self.actions.source(cast(ReverseSource, source.binding.source))
        width = len(origin.digits) + int(node.steps == 1)
        return SourceImageCandidate(
            ReverseImagePayload(cumulative),
            source.binding.extent + node.steps,
            boundary_ports=(0, 1),
            radix=origin.base,
            precision=width,
        )

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        self.validate_action(action)
        self.validate_payload(source.payload)
        if demand is not None:
            demand.__post_init__()
        steps = self.actions.node(cast(ReverseActionID, action)).steps
        source_steps = self.actions.node(
            cast(ReverseImagePayload, source.payload).action
        ).steps
        if steps < 2:
            raise ValueError(
                "reverse composite application requires at least two steps"
            )
        if source_steps == 0 and steps == 2:
            origin = self.actions.source(cast(ReverseSource, source.binding.source))
            cumulative = self.actions.compose(
                cast(ReverseImagePayload, source.payload).action,
                cast(ReverseActionID, action),
            )
            self.ledger.bump("reverse_source_two_step_pullback_publications")
            return SourceImageCandidate(
                ReverseImagePayload(cumulative),
                source.binding.extent + 2,
                boundary_ports=(0, 1),
                radix=origin.base,
                precision=len(origin.digits) + 2,
            )
        if source_steps == 0 and steps >= 3:
            origin = self.actions.source(cast(ReverseSource, source.binding.source))
            try:
                validate_same_carry_chamber(
                    origin, steps, self.ledger, ports=self.ports(origin)
                )
            except SameCarryChamberRejected as error:
                self.ledger.bump("reverse_cylinder_construction_failures")
                raise ReverseCylinderConstructionUnavailable(
                    f"reverse/add powered action for {steps} temporal steps left "
                    "the bounded same-carry no-growth cylinder"
                ) from error
            cumulative = self.actions.compose(
                cast(ReverseImagePayload, source.payload).action,
                cast(ReverseActionID, action),
            )
            self.ledger.bump("reverse_source_same_carry_publications")
            return SourceImageCandidate(
                ReverseImagePayload(cumulative),
                source.binding.extent + steps,
                boundary_ports=(0, 0),
                radix=origin.base,
                precision=len(origin.digits),
            )
        self.ledger.bump("reverse_cylinder_construction_failures")
        raise ReverseCylinderConstructionUnavailable(
            "reverse/add cannot answer this demand: the successor-closed "
            f"source cylinder for {source_steps + steps} temporal steps "
            "has not been constructed"
        )

    def compose_chronological(
        self,
        action: Hashable,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        del source, before, after
        steps = self.actions.node(cast(ReverseActionID, action)).steps
        raise ReverseCylinderConstructionUnavailable(
            "reverse/add composite chronology is unavailable; "
            f"cannot construct {steps} temporal steps"
        )

    def admitted_input_key(
        self, action: Hashable, source: SourceImageView
    ) -> Hashable | None:
        self.validate_action(action)
        self.validate_payload(source.payload)
        action_steps = self.actions.node(cast(ReverseActionID, action)).steps
        source_steps = self.actions.node(
            cast(ReverseImagePayload, source.payload).action
        ).steps
        total = source_steps + action_steps
        if total >= 2 and source_steps != 0:
            self.ledger.bump("reverse_cylinder_construction_failures")
            raise ReverseCylinderConstructionUnavailable(
                "reverse/add source cylinder construction is unavailable for "
                f"{total} temporal steps"
            )
        return None

    def transport_reuse(
        self,
        action: Hashable,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        del action, cached_source, cached_result, source
        raise ValueError("reverse/add images do not admit relative transport")

    def _width(self, source: ExactSource) -> int:
        ports = self.ports(source)
        return ports.width + ports.terminal

    def _normalized(self, pair: int, incoming: int, base: int) -> tuple[int, int]:
        outgoing = int(pair + incoming >= base)
        if base == 10:
            domain = int(pair >= 9) + int(pair > 9)
            digit = skew_normalized_digit(domain, pair % 9, incoming)
            self.ledger.bump("reverse_source_mod9_digit_reconstructions")
        else:
            digit = (pair + incoming) % base
            self.ledger.bump("reverse_source_radix_digit_reconstructions")
        return outgoing, digit

    def iter_second_digits(self, source: ExactSource) -> Iterator[int]:
        """Emit final digits; no prefix or prior output is replayed per point."""
        ports = self.ports(source)
        for position in range(ports.second_width()):
            yield self.second_digit(source, position)

    def second_digit(self, source: ExactSource, position: int) -> int:
        ports = self.ports(source)
        width = ports.width + ports.terminal
        if position == width:
            carry = ports.second_carry(width)
            if not carry:
                raise IndexError(position)
            return carry
        if not 0 <= position < width:
            raise IndexError(position)
        _, digit = self._normalized(
            ports.second_pair(position), ports.second_carry(position), source.base
        )
        self.ledger.bump("reverse_source_second_step_coordinates")
        return digit

    def iter_same_carry_digits(self, source: ExactSource, steps: int) -> Iterator[int]:
        """Consume the chamber already checked by image admission."""
        ports = self.ports(source)
        for position in range(ports.width):
            yield same_carry_digit(ports, steps, position)

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        self.validate_payload(image.payload)
        payload = cast(ReverseImagePayload, image.payload)
        source = self.actions.source(cast(ReverseSource, image.binding.source))
        source_width = len(source.digits)
        steps = self.actions.node(payload.action).steps
        if (
            payload.action != image.binding.action
            or image.binding.extent != steps
            or image.binding.family != self.family
            or image.binding.semantic_version != self.semantic_version
            or image.binding.radix != source.base
            or image.binding.orientation != 1
        ):
            raise ValueError("reverse image action and source binding disagree")
        if demand == SourceImageDemand("width"):
            if steps == 0:
                return SourceImageProjection(source_width)
            if steps == 2:
                self.ledger.bump("reverse_source_two_step_width_demands")
                return SourceImageProjection(self.ports(source).second_width())
            if steps >= 3:
                self.ledger.bump("reverse_source_same_carry_width_demands")
                return SourceImageProjection(source_width)
            return SourceImageProjection(self._width(source))
        if demand.name != "digit" or len(demand.parameters) != 1:
            raise ValueError("unsupported reverse/add source image demand")
        position = demand.parameters[0]
        if type(position) is not int:
            raise TypeError("reverse/add digit coordinate must be an integer")
        if position < 0:
            raise IndexError(position)
        if steps >= 3:
            if position >= source_width:
                raise IndexError(position)
            self.ledger.bump("reverse_source_same_carry_digit_demands")
            return SourceImageProjection(
                same_carry_digit(self.ports(source), steps, position)
            )
        if steps == 2:
            self.ledger.bump("reverse_source_two_step_digit_demands")
            return SourceImageProjection(self.second_digit(source, position))
        if steps == 0:
            if position >= source_width:
                raise IndexError(position)
            self.ledger.bump("reverse_source_digit_reads")
            return SourceImageProjection(_source_digit(source, position))
        if position > source_width:
            raise IndexError(position)
        ports = self.ports(source)
        if position == source_width:
            if not ports.terminal:
                raise IndexError(position)
            digit = 1
        else:
            _, digit = self._normalized(
                ports.pair(position), ports.carry(position), source.base
            )
            self.ledger.bump("reverse_source_carry_coordinates")
        return SourceImageProjection(digit)

    def iter_primitive_digits(self, source: ExactSource) -> Iterator[int]:
        """Demand output coordinates from the shared boundary action projection."""
        ports = self.ports(source)
        for position in range(ports.width):
            _, digit = self._normalized(
                ports.pair(position), ports.carry(position), source.base
            )
            self.ledger.bump("reverse_source_carry_coordinates")
            yield digit
        if ports.terminal:
            yield 1

    def first_failure(self, image: SourceImageView) -> None:
        self.validate_payload(image.payload)


class ReverseSourceImageWorkspace:
    """Demanded reverse/add image bound to one original source and one action."""

    def __init__(
        self, ledger: ResourceLedger, seed: int, steps: int, *, base: int = 10
    ) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("reverse source workspace requires a resource ledger")
        seed = require_integer(seed, "seed", 0)
        steps = require_integer(steps, "reverse/add steps", 0)
        base = require_integer(base, "base", 2)
        self.ledger = ledger
        actions = ReverseActionArena(ledger)
        scheduler: TileScheduler | None = None
        try:
            source = actions.admit_source(seed, base)
            root_action = actions.action(steps)
            scheduler = TileScheduler.source_only(ledger)
            adapter = _ReverseSourceImageAdapter(actions)
            scheduler.register_source_image_adapter(adapter)
        except BaseException:
            if scheduler is not None:
                scheduler.dispose_source_images()
            actions.dispose()
            raise
        self.actions = actions
        self.source = source
        self.root_action = root_action
        self.scheduler = scheduler
        self.adapter = adapter
        self.steps = steps
        self.base = base
        self._image: SourceImageID | None = None
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
        )
        ledger.register_execution_root(self)

    def _check_open(self) -> None:
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
            or adapter.actions is not actions
            or adapter.ledger is not ledger
            or scheduler.ledger is not ledger
        ):
            raise ValueError("reverse source workspace binding was altered")
        actions.source(source)
        actions.node(root_action)
        if actions.node(root_action).steps != steps:
            raise ValueError("reverse source workspace action was altered")
        image = self._image
        if image is not None:
            view = scheduler._source_image_core().view(image)
            if view.binding.source != source or view.binding.action != root_action:
                raise ValueError("reverse source workspace image binding was altered")

    def _demanded_image(self, demand: SourceImageDemand) -> SourceImageID:
        self._check_open()
        found = self._image
        if found is None:
            found = self.scheduler.source_image_demanded(
                self.adapter, self.source, self.root_action, demand
            )
            self._image = found
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
        demand = SourceImageDemand("digit", (position,))
        image = self._demanded_image(demand)
        return cast(
            int, self.scheduler.source_projection(self.adapter, image, demand).value
        )

    def width(self) -> int:
        demand = SourceImageDemand("width")
        image = self._demanded_image(demand)
        return cast(
            int, self.scheduler.source_projection(self.adapter, image, demand).value
        )

    def iter_digits(self) -> Iterator[int]:
        self._check_open()
        self._demanded_image(SourceImageDemand("width"))
        if self.steps == 0:
            yield from self.actions.source(self.source).digits
            return
        if self.steps == 2:
            yield from self.adapter.iter_second_digits(self.actions.source(self.source))
            return
        if self.steps >= 3:
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
            self._disposed = True


__all__ = [
    "ReverseActionArena",
    "ReverseActionID",
    "ReverseCylinderConstructionUnavailable",
    "ReverseSource",
    "ReverseSourceImageWorkspace",
]
