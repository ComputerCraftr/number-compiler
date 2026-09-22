"""Law-parameterized bounded source images for dyadic return systems.

The branch word of ``n`` dyadic returns is determined by the low ``n`` source bits.  This module keeps that fact local to the source-bound scheduler:
bounded leaves compose memoized residue macros, while images retain an exact
affine skew transfer and chronological support. Equal admitted source cylinders
share complete effects under transported occurrence bindings. Unmatched source
discovery still costs linear work in the requested physical extent.
"""

from __future__ import annotations

from collections.abc import Hashable, Iterator
from operator import add, mul

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicCycleSummary,
    DyadicImageSummary,
    DyadicReturnActionID,
    DyadicReturnCycle,
    DyadicReturnImageID,
    DyadicReturnLaw,
    DyadicReturnSourceID,
    DyadicReturnSupportID,
    _ActionNode,
    _ImageNode,
    _SourceNode,
    _SupportNode,
)
from number_compiler.hashlife.execution.dyadic_return_transport import _low_bits
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.hashlife.execution.source_image_application import (
    SourceBoundSplitContextAdapter,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList


def _identity_transfer() -> SkewTransfer[int]:
    return SkewTransfer(1, 0, 1)


class DyadicReturnImageWorkspace(
    SourceBoundImageAdapter, SourceBoundSplitContextAdapter
):
    """One pinned dyadic return image owned by ``TileScheduler``."""

    family = "dyadic-return-source-image"
    semantic_version = "dyadic-return-source-image-v1"
    _ACTION_KIND = "dyadic-return-action"
    _SOURCE_KIND = "dyadic-return-source"
    _SUPPORT_KIND = "dyadic-return-support"
    _IMAGE_KIND = "dyadic-return-image"
    MAX_LEAF_STEPS = 64

    def __init__(
        self, ledger: ResourceLedger, seed: int, steps: int, law: DyadicReturnLaw
    ) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("dyadic return images require a resource ledger")
        if type(seed) is not int or seed < 0:
            raise ValueError("dyadic return source must be nonnegative")
        if type(steps) is not int or steps < 0:
            raise ValueError("dyadic return extent must be nonnegative")
        if type(law) is not DyadicReturnLaw:
            raise TypeError("dyadic return workspace requires a pinned law")
        self.ledger = ledger
        self.seed = seed
        self.steps = steps
        self.law = law
        self._law_snapshot = law.descriptor
        self.family = law.family
        self.semantic_version = law.semantic_version
        if law.family.startswith("antihydra"):
            self.counter_prefix = "antihydra_arithmetic"
        elif law.family.startswith("collatz"):
            self.counter_prefix = "collatz_physical"
        else:
            self.counter_prefix = "dyadic_return"
        self.owner = ArenaToken("dyadic-return-images")
        self._closed = False
        prefix = f"dyadic-return-images-{len(ledger.inventory())}"
        action_role = (
            "arithmetic_action"
            if law.family.startswith("antihydra")
            else "dyadic_return_action"
        )
        source_role = (
            "arithmetic_source"
            if law.family.startswith("antihydra")
            else "dyadic_return_source"
        )
        support_role = (
            "arithmetic_cylinder_support"
            if law.family.startswith("antihydra")
            else "dyadic_return_support"
        )
        image_role = (
            "arithmetic_image"
            if law.family.startswith("antihydra")
            else "dyadic_return_image"
        )
        self.action_owner = ledger.register(prefix + "-actions", action_role)
        self.source_owner = ledger.register(prefix + "-sources", source_role)
        self.support_owner = ledger.register(prefix + "-support", support_role)
        self.image_owner = ledger.register(prefix + "-images", image_role)
        self.width_owner = ledger.register(
            prefix + "-widths", "dyadic_return_action_index"
        )
        self.construction_owner = ledger.register(prefix + "-construction", "workspace")
        self.action_snapshot_owner = ledger.register(
            prefix + "-action-snapshots", "workspace"
        )
        self.source_snapshot_owner = ledger.register(
            prefix + "-source-snapshots", "workspace"
        )
        self.support_snapshot_owner = ledger.register(
            prefix + "-support-snapshots", "workspace"
        )
        self.image_snapshot_owner = ledger.register(
            prefix + "-image-snapshots", "workspace"
        )
        self.macro_owner = ledger.register(
            prefix + "-macros", "dyadic_return_macro_index"
        )
        self.macro_stack_owner = ledger.register(prefix + "-macro-stack", "workspace")
        self.macros: LedgerDict[tuple[int, int], _SupportNode] = ledger.make_dict(
            self.macro_owner, nodes_per_entry=1
        )
        self.macro_stack: LedgerList[tuple[int, int, _SupportNode | None]] = (
            ledger.make_list(
                self.macro_stack_owner, nodes_per_entry=1, append_only=False
            )
        )
        self.actions: LedgerList[_ActionNode] = ledger.make_list(
            self.action_owner, nodes_per_entry=1, append_only=False
        )
        self.sources: LedgerList[_SourceNode] = ledger.make_list(
            self.source_owner, nodes_per_entry=1, append_only=False
        )
        self.support: LedgerList[_SupportNode] = ledger.make_list(
            self.support_owner, nodes_per_entry=1, append_only=False
        )
        self.images: LedgerList[_ImageNode] = ledger.make_list(
            self.image_owner, nodes_per_entry=1, append_only=False
        )
        self.by_width: LedgerDict[int, DyadicReturnActionID] = ledger.make_dict(
            self.width_owner, nodes_per_entry=0
        )
        self.construction_stack: LedgerList[int] = ledger.make_list(
            self.construction_owner, nodes_per_entry=1, append_only=False
        )
        self.action_snapshots: LedgerDict[int, object] = ledger.make_dict(
            self.action_snapshot_owner, nodes_per_entry=1
        )
        self.source_snapshots: LedgerDict[int, object] = ledger.make_dict(
            self.source_snapshot_owner, nodes_per_entry=1
        )
        self.support_snapshots: LedgerDict[int, object] = ledger.make_dict(
            self.support_snapshot_owner, nodes_per_entry=1
        )
        self.image_snapshots: LedgerDict[int, object] = ledger.make_dict(
            self.image_snapshot_owner, nodes_per_entry=1
        )
        # ``LedgerDict`` registers each scalar snapshot store with its own
        # owner.  The snapshots make later object.__setattr__ tampering
        # observable without replaying a composed image.
        self.scheduler = TileScheduler.source_only(ledger)
        try:
            self.scheduler.register_source_image_adapter(self)
            self.identity = self._append_action(_ActionNode(0, None))
            self.root_action = self._action(steps)
            if steps:
                residue = _low_bits(seed, steps)
                lift = 0 if seed.bit_length() <= steps else seed >> steps
            else:
                residue, lift = 0, seed
            self.root_source = self._append_source(
                _SourceNode(residue, steps, lift, None, None, None, 0, True)
            )
            self.root_image = self.scheduler.source_image_demanded(
                self,
                self.root_source,
                self.root_action,
                SourceImageDemand("physical-summary"),
            )
            projected = self.scheduler.source_projection(
                self, self.root_image, SourceImageDemand("physical-summary")
            ).value
            if type(projected) is not DyadicReturnImageID:
                raise TypeError("dyadic return projection changed its payload sort")
            self.root_payload = projected
        except BaseException:
            self._rollback_construction()
            self._bump("image_rollbacks")
            raise
        ledger.register_execution_root(self)

    def _rollback_construction(self) -> None:
        from number_compiler.hashlife.execution.dyadic_return_actions import (
            rollback_construction,
        )

        rollback_construction(self)

    def dispose(self) -> None:
        from number_compiler.hashlife.execution.dyadic_return_actions import dispose

        dispose(self)

    def _append_action(self, node: _ActionNode) -> DyadicReturnActionID:
        from number_compiler.hashlife.execution.dyadic_return_actions import (
            append_action,
        )

        return append_action(self, node)

    def _action(self, width: int) -> DyadicReturnActionID:
        from number_compiler.hashlife.execution.dyadic_return_actions import (
            build_action,
        )

        return build_action(self, width)

    def _append_source(self, node: _SourceNode) -> DyadicReturnSourceID:
        self.ledger.reserve_many(
            ((self.source_owner, 1, 1), (self.source_snapshot_owner, 1, 1))
        )
        identity = DyadicReturnSourceID(
            self.owner, self._SOURCE_KIND, len(self.sources)
        )
        try:
            self.sources.append(node)
            self.source_snapshots[identity.local_id] = (
                node.residue,
                node.precision,
                node.lift,
                node.parent,
                node.parent_action,
                node.before_image,
                node.side,
                node.exact,
            )
        except BaseException:
            self.ledger.release(self.source_owner, entries=1, nodes=1)
            self.ledger.release(self.source_snapshot_owner, entries=1, nodes=1)
            raise
        return identity

    def _append_support(self, node: _SupportNode) -> DyadicReturnSupportID:
        self.ledger.reserve_many(
            ((self.support_owner, 1, 1), (self.support_snapshot_owner, 1, 1))
        )
        identity = DyadicReturnSupportID(
            self.owner, self._SUPPORT_KIND, len(self.support)
        )
        try:
            self.support.append(node)
            self.support_snapshots[identity.local_id] = (
                node.width,
                node.residue,
                node.transfer.upper,
                node.transfer.offset,
                node.transfer.lower,
                node.odd_steps,
                node.delta,
                node.minimum,
                node.branch_word,
                node.children,
                node.cycle,
            )
        except BaseException:
            self.ledger.release(self.support_owner, entries=1, nodes=1)
            self.ledger.release(self.support_snapshot_owner, entries=1, nodes=1)
            raise
        return identity

    def _append_image(self, node: _ImageNode) -> DyadicReturnImageID:
        self.ledger.reserve_many(
            ((self.image_owner, 1, 1), (self.image_snapshot_owner, 1, 1))
        )
        identity = DyadicReturnImageID(self.owner, self._IMAGE_KIND, len(self.images))
        try:
            self.images.append(node)
            summary = node.summary
            self.image_snapshots[identity.local_id] = (
                node.source,
                node.action,
                summary.width,
                summary.residue,
                summary.transfer.upper,
                summary.transfer.offset,
                summary.transfer.lower,
                summary.delta,
                summary.minimum,
                summary.odd_steps,
                summary.support,
                summary.cycle,
            )
        except BaseException:
            self.ledger.release(self.image_owner, entries=1, nodes=1)
            self.ledger.release(self.image_snapshot_owner, entries=1, nodes=1)
            raise
        return identity

    def action_node(self, action: DyadicReturnActionID) -> _ActionNode:
        from number_compiler.hashlife.execution.dyadic_return_validation import (
            action_node,
        )

        return action_node(self, action)

    def source_node(self, source: DyadicReturnSourceID) -> _SourceNode:
        from number_compiler.hashlife.execution.dyadic_return_validation import (
            source_node,
        )

        return source_node(self, source)

    def support_node(self, support: DyadicReturnSupportID) -> _SupportNode:
        from number_compiler.hashlife.execution.dyadic_return_validation import (
            support_node,
        )

        return support_node(self, support)

    def image_node(self, image: DyadicReturnImageID) -> _ImageNode:
        from number_compiler.hashlife.execution.dyadic_return_validation import (
            image_node,
        )

        return image_node(self, image)

    def validate_source(self, source: Hashable) -> None:
        from number_compiler.hashlife.execution.dyadic_return_validation import (
            validate_source,
        )

        validate_source(self, source)

    def validate_action(self, action: Hashable) -> None:
        from number_compiler.hashlife.execution.dyadic_return_validation import (
            validate_action,
        )

        validate_action(self, action)

    def validate_payload(self, payload: Hashable) -> None:
        from number_compiler.hashlife.execution.dyadic_return_validation import (
            validate_payload,
        )

        validate_payload(self, payload)

    def _validate_law(self) -> None:
        from number_compiler.hashlife.execution.dyadic_return_validation import (
            validate_law,
        )

        validate_law(self)

    def _bump(self, suffix: str, amount: int = 1) -> None:
        self.ledger.bump(f"{self.counter_prefix}_{suffix}", amount)

    def identity_action(self, source: Hashable) -> DyadicReturnActionID:
        self.validate_source(source)
        return self.identity

    def action_children(
        self, action: Hashable
    ) -> tuple[DyadicReturnActionID, DyadicReturnActionID] | None:
        self.validate_action(action)
        assert type(action) is DyadicReturnActionID
        return self.action_node(action).children

    def compose_actions(
        self, before: Hashable, after: Hashable
    ) -> DyadicReturnActionID:
        self.validate_action(before)
        self.validate_action(after)
        assert type(before) is DyadicReturnActionID
        assert type(after) is DyadicReturnActionID
        return self._action(
            self.action_node(before).width + self.action_node(after).width
        )

    def _source_value(self, source: _SourceNode) -> int:
        from number_compiler.hashlife.execution.dyadic_return_transport import (
            source_value,
        )

        return source_value(self, source)

    def _transport_low(
        self, transfer: SkewTransfer[int], source_residue: int, after_width: int
    ) -> int:
        from number_compiler.hashlife.execution.dyadic_return_transport import (
            transport_low,
        )

        return transport_low(self, transfer, source_residue, after_width)

    def admit_source(self, source: Hashable) -> SourceImageCandidate:
        self.validate_source(source)
        assert type(source) is DyadicReturnSourceID
        node = self.source_node(source)
        summary = DyadicImageSummary(
            0, node.residue, _identity_transfer(), 0, 0, 0, None
        )
        payload = self._append_image(_ImageNode(source, self.identity, summary))
        return SourceImageCandidate(
            payload,
            0,
            (
                self.law.descriptor,
                summary.transfer.upper,
                summary.transfer.offset,
                summary.transfer.lower,
                0,
            ),
            precision=node.precision,
        )

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        """Offer a family-certified compressed image for one demand."""
        self.validate_action(action)
        self.validate_payload(source.payload)
        if demand is None or demand.name != "physical-summary" or demand.parameters:
            return None
        return self._compressed_cycle_candidate(action, source)

    def _compressed_cycle_candidate(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate | None:
        """Compress a directly admitted exact singleton cycle.

        This hook deliberately accepts only an exact source already equal to a
        pinned cycle state. Prefix discovery belongs to the normal scheduler
        leaves; this hook never re-enters the scheduler or infers a cycle from
        a residue class.
        """
        cycle = self.law.cycle
        if cycle is None or type(action) is not DyadicReturnActionID:
            return None
        if source.binding.action != self.identity:
            return None
        source_id = source.binding.source
        if type(source_id) is not DyadicReturnSourceID:
            return None
        source_node = self.source_node(source_id)
        if not source_node.exact:
            return None
        source_value = self._source_value(source_node)
        if source_value not in cycle.states:
            return None
        action_node = self.action_node(action)
        if action_node.width == 0:
            return None
        entry_phase = cycle.states.index(source_value)
        cycle_length = len(cycle.states)
        cycles, remainder = divmod(action_node.width, cycle_length)
        terminal_phase = (entry_phase + remainder) % cycle_length
        rotated_states = tuple(
            cycle.states[(entry_phase + offset) % cycle_length]
            for offset in range(cycle_length)
        )
        cycle_weights = tuple(
            self.law.weights[state_value & 1] for state_value in rotated_states
        )
        cycle_odd = sum(state_value & 1 for state_value in rotated_states)
        cycle_delta = sum(cycle_weights)
        if cycle_delta < 0:
            return None
        cycle_prefix = [
            sum(cycle_weights[:offset]) for offset in range(cycle_length + 1)
        ]
        remainder_weights = tuple(
            self.law.weights[cycle.states[(entry_phase + offset) % cycle_length] & 1]
            for offset in range(remainder)
        )
        tail_delta = cycles * cycle_delta + sum(remainder_weights)
        observed_prefix = (
            cycle_prefix
            if cycles
            else [sum(cycle_weights[:offset]) for offset in range(remainder + 1)]
        )
        tail_minimum = min(
            observed_prefix
            + [
                cycles * cycle_delta + sum(remainder_weights[:offset])
                for offset in range(remainder + 1)
            ]
        )
        tail_odd = cycles * cycle_odd + sum(
            cycle.states[(entry_phase + offset) % cycle_length] & 1
            for offset in range(remainder)
        )
        terminal = cycle.states[terminal_phase]
        cycle_summary = DyadicCycleSummary(
            0,
            entry_phase,
            cycles,
            remainder,
            terminal_phase,
            tail_odd,
            tail_delta,
            tail_minimum,
        )
        self._bump(
            "cycle_repeat_operand_bits",
            max(
                1,
                cycles.bit_length(),
                action_node.width.bit_length(),
                cycle_length.bit_length(),
            ),
        )
        transfer = SkewTransfer(0, terminal, 1)
        support = self._append_support(
            _SupportNode(
                action_node.width,
                source_node.residue,
                transfer,
                tail_odd,
                tail_delta,
                tail_minimum,
                None,
                None,
                cycle_summary,
            )
        )
        summary = DyadicImageSummary(
            action_node.width,
            source_node.residue,
            transfer,
            tail_delta,
            tail_minimum,
            tail_odd,
            support,
            cycle_summary,
        )
        payload = self._append_image(_ImageNode(source_id, action, summary))
        self._bump("cycle_compressions")
        return SourceImageCandidate(
            payload,
            action_node.width,
            (
                self.law.descriptor,
                "singleton-cycle",
                0,
                entry_phase,
                cycles,
                remainder,
                terminal_phase,
            ),
            precision=source_node.precision,
        )

    def apply_primitive(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_action(action)
        self.validate_payload(source.payload)
        assert type(action) is DyadicReturnActionID
        assert type(source.binding.source) is DyadicReturnSourceID
        node = self.action_node(action)
        source_node = self.source_node(source.binding.source)
        if (
            self.law.cycle is not None
            and source_node.exact
            and self._source_value(source_node) in self.law.cycle.states
        ):
            compressed = self._compressed_cycle_candidate(action, source)
            if compressed is not None:
                return compressed
        if node.children is not None or node.width > self.MAX_LEAF_STEPS:
            raise ValueError("dyadic return primitive must be a bounded leaf")
        if node.width == 0:
            return SourceImageCandidate(
                source.payload,
                0,
                (self.law.descriptor, 1, 0, 1, 0),
                precision=source_node.precision,
            )
        if source_node.precision != node.width:
            raise ValueError("dyadic return leaf received another demanded precision")
        from number_compiler.hashlife.execution.dyadic_return_transport import (
            residue_macro,
        )

        support = residue_macro(self, node.width, source_node.residue)
        macro = self.support_node(support)
        transfer = macro.transfer
        odd_steps, delta, minimum = macro.odd_steps, macro.delta, macro.minimum
        summary = DyadicImageSummary(
            node.width,
            source_node.residue,
            transfer,
            delta,
            minimum,
            odd_steps,
            support,
        )
        payload = self._append_image(_ImageNode(source.binding.source, action, summary))
        self._bump("leaf_steps", node.width)
        self._bump(
            "leaf_operand_bits",
            source_node.residue.bit_length() + transfer.offset.bit_length(),
        )
        return SourceImageCandidate(
            payload,
            node.width,
            (
                self.law.descriptor,
                transfer.upper,
                transfer.offset,
                transfer.lower,
                odd_steps,
            ),
            precision=node.width,
        )

    def first_child_source(
        self,
        parent_action: Hashable,
        parent_source: SourceImageView,
        before_action: Hashable,
        after_action: Hashable,
    ) -> DyadicReturnSourceID:
        self.validate_action(parent_action)
        self.validate_action(before_action)
        self.validate_action(after_action)
        assert type(parent_action) is DyadicReturnActionID
        assert type(before_action) is DyadicReturnActionID
        assert type(after_action) is DyadicReturnActionID
        assert type(parent_source.binding.source) is DyadicReturnSourceID
        if parent_source.binding.action != self.identity:
            raise ValueError("dyadic return parent source is not an identity context")
        parent = self.source_node(parent_source.binding.source)
        before_width = self.action_node(before_action).width
        after_width = self.action_node(after_action).width
        if (
            parent.precision != before_width + after_width
            or self.compose_actions(before_action, after_action) != parent_action
        ):
            raise ValueError("dyadic return parent has another precision split")
        parent_value = self._source_value(parent) if parent.exact else 0
        exact = parent.exact and self.law.cycle is not None
        lift = parent_value >> before_width if exact else 0
        return self._append_source(
            _SourceNode(
                _low_bits(parent.residue, before_width),
                before_width,
                lift,
                parent_source.binding.source,
                parent_action,
                None,
                1,
                exact,
            )
        )

    def second_child_source(
        self,
        parent_action: Hashable,
        parent_source: SourceImageView,
        before_result: SourceImageView,
        after_action: Hashable,
    ) -> DyadicReturnSourceID:
        self.validate_action(parent_action)
        self.validate_action(after_action)
        self.validate_payload(before_result.payload)
        assert type(parent_action) is DyadicReturnActionID
        assert type(after_action) is DyadicReturnActionID
        assert type(parent_source.binding.source) is DyadicReturnSourceID
        assert type(before_result.payload) is DyadicReturnImageID
        if parent_source.binding.action != self.identity:
            raise ValueError("dyadic return parent source is not an identity context")
        parent = self.source_node(parent_source.binding.source)
        before_image = self.image_node(before_result.payload)
        before = before_image.summary
        after_width = self.action_node(after_action).width
        children = self.action_node(parent_action).children
        if children is None or before_result.binding.action != children[0]:
            raise ValueError("dyadic return before image has another action")
        before_source_id = before_result.binding.source
        if type(before_source_id) is not DyadicReturnSourceID:
            raise TypeError("dyadic return before image has another source")
        before_source = self.source_node(before_source_id)
        if (
            before_source.parent is not parent_source.binding.source
            or before_source.parent_action != parent_action
            or before_source.side != 1
        ):
            raise ValueError("dyadic return before image lost parent authority")
        if parent.precision != before.width + after_width:
            raise ValueError("dyadic return second child has another precision")
        residue = self._transport_low(before.transfer, parent.residue, after_width)
        exact = False
        lift = 0
        if before_source.exact and self.law.cycle is not None:
            before_value = self._source_value(before_source)
            numerator = before.transfer.upper * before_value + before.transfer.offset
            if numerator % before.transfer.lower:
                raise ArithmeticError("dyadic return exact transport was not integral")
            after_value = numerator // before.transfer.lower
            self._bump(
                "transport_exact_operand_bits",
                max(
                    1,
                    before_value.bit_length(),
                    before.transfer.upper.bit_length(),
                    before.transfer.offset.bit_length(),
                    before.transfer.lower.bit_length(),
                    numerator.bit_length(),
                    after_value.bit_length(),
                ),
            )
            residue = _low_bits(after_value, after_width)
            lift = after_value >> after_width
            exact = True
        return self._append_source(
            _SourceNode(
                residue,
                after_width,
                lift,
                parent_source.binding.source,
                parent_action,
                before_result.payload,
                2,
                exact,
            )
        )

    def compose_chronological(
        self,
        action: Hashable,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        self.validate_payload(before.payload)
        self.validate_payload(after.payload)
        assert type(action) is DyadicReturnActionID
        assert type(source.binding.source) is DyadicReturnSourceID
        assert type(before.binding.source) is DyadicReturnSourceID
        assert type(after.binding.source) is DyadicReturnSourceID
        assert type(before.payload) is DyadicReturnImageID
        assert type(after.payload) is DyadicReturnImageID
        if source.binding.action != self.identity:
            raise ValueError(
                "dyadic return composition source is not an identity context"
            )
        parent = self.source_node(source.binding.source)
        before_source = self.source_node(before.binding.source)
        after_source = self.source_node(after.binding.source)
        left = self.image_node(before.payload).summary
        right = self.image_node(after.payload).summary
        if (
            before_source.parent is not source.binding.source
            or before_source.parent_action != action
            or before_source.before_image is not None
            or before_source.side != 1
            or after_source.parent is not source.binding.source
            or after_source.parent_action != action
            or after_source.before_image != before.payload
            or after_source.side != 2
            or parent.precision != left.width + right.width
            or self.compose_actions(before.binding.action, after.binding.action)
            != action
        ):
            raise ValueError("dyadic return child contexts lost parent authority")
        transported = self._transport_low(left.transfer, parent.residue, right.width)
        if transported != after_source.residue:
            raise ArithmeticError("dyadic return transported source was changed")
        transfer = left.transfer.then(right.transfer, multiply=mul, add=add)
        if left.support is None or right.support is None:
            raise ValueError("nonempty dyadic return composition lost support")
        cycle = (
            None
            if right.cycle is None
            else DyadicCycleSummary(
                left.width + right.cycle.entry_steps,
                right.cycle.cycle_phase,
                right.cycle.cycles,
                right.cycle.remainder,
                right.cycle.terminal_phase,
                right.cycle.odd_steps,
                right.cycle.delta,
                right.cycle.minimum,
            )
        )
        support = self._append_support(
            _SupportNode(
                left.width + right.width,
                parent.residue,
                transfer,
                left.odd_steps + right.odd_steps,
                left.delta + right.delta,
                min(left.minimum, left.delta + right.minimum),
                None,
                (left.support, right.support),
                cycle,
            )
        )
        summary = DyadicImageSummary(
            left.width + right.width,
            parent.residue,
            transfer,
            left.delta + right.delta,
            min(left.minimum, left.delta + right.minimum),
            left.odd_steps + right.odd_steps,
            support,
            cycle,
        )
        payload = self._append_image(_ImageNode(source.binding.source, action, summary))
        self._bump(
            "composition_operand_bits",
            parent.residue.bit_length() + transfer.offset.bit_length(),
        )
        return SourceImageCandidate(
            payload,
            summary.width,
            (
                self.law.descriptor,
                transfer.upper,
                transfer.offset,
                transfer.lower,
                summary.odd_steps,
            ),
            precision=summary.width,
        )

    def admitted_input_key(
        self, action: Hashable, source: SourceImageView
    ) -> Hashable | None:
        from number_compiler.hashlife.execution.dyadic_return_reuse import (
            admitted_input_key,
        )

        return admitted_input_key(self, action, source)

    def transport_reuse(
        self,
        action: Hashable,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        from number_compiler.hashlife.execution.dyadic_return_reuse import (
            transport_reuse,
        )

        return transport_reuse(self, action, cached_source, cached_result, source)

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        self.validate_payload(image.payload)
        if (
            demand.name in {"physical-summary", "arithmetic-summary", "dyadic-summary"}
            and not demand.parameters
        ):
            return SourceImageProjection(image.payload)
        raise ValueError("unsupported dyadic return image demand")

    def first_failure(self, image: SourceImageView) -> int | None:
        from number_compiler.hashlife.execution.dyadic_return_observers import (
            first_failure,
        )

        return first_failure(self, image)

    def summary(self) -> DyadicImageSummary:
        from number_compiler.hashlife.execution.dyadic_return_observers import summary

        return summary(self)

    def endpoint(self) -> int:
        from number_compiler.hashlife.execution.dyadic_return_observers import endpoint

        return endpoint(self)

    def odd_steps(self) -> int:
        from number_compiler.hashlife.execution.dyadic_return_observers import odd_steps

        return odd_steps(self)

    def delta(self) -> int:
        from number_compiler.hashlife.execution.dyadic_return_observers import delta

        return delta(self)

    def minimum(self) -> int:
        from number_compiler.hashlife.execution.dyadic_return_observers import minimum

        return minimum(self)

    def branch_segments(self) -> Iterator[tuple[int, int, int]]:
        from number_compiler.hashlife.execution.dyadic_return_observers import (
            branch_segments,
        )

        yield from branch_segments(self)

    def leaf_summaries(self) -> Iterator[tuple[int, DyadicImageSummary, int]]:
        from number_compiler.hashlife.execution.dyadic_return_observers import (
            leaf_summaries,
        )

        yield from leaf_summaries(self)

    def leaf_summaries_for(
        self, payload: DyadicReturnImageID
    ) -> Iterator[tuple[int, DyadicImageSummary, int]]:
        from number_compiler.hashlife.execution.dyadic_return_observers import (
            leaf_summaries_for,
        )

        yield from leaf_summaries_for(self, payload)

    def first_failure_index(self) -> int | None:
        from number_compiler.hashlife.execution.dyadic_return_observers import (
            first_failure_index,
        )

        return first_failure_index(self)

    def _first_failure(self, summary: DyadicImageSummary) -> int | None:
        from number_compiler.hashlife.execution.dyadic_return_observers import (
            _first_failure,
        )

        return _first_failure(self, summary)

    def validate(self) -> None:
        from number_compiler.hashlife.execution.dyadic_return_validation import (
            validate_workspace,
        )

        validate_workspace(self)


__all__ = [
    "DyadicCycleSummary",
    "DyadicImageSummary",
    "DyadicReturnActionID",
    "DyadicReturnCycle",
    "DyadicReturnImageID",
    "DyadicReturnImageWorkspace",
    "DyadicReturnLaw",
    "DyadicReturnSourceID",
    "DyadicReturnSupportID",
    "_ActionNode",
    "_ImageNode",
    "_SourceNode",
    "_SupportNode",
    "_low_bits",
]
