"""Independent retained-payload audit for shared dyadic return images."""

from __future__ import annotations

from itertools import accumulate
from operator import add, mul

from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_transport import (
    cycle_phase_summaries,
)
from number_compiler.resources.dyadic_return_balanced_audit import (
    _balanced_saturated_audit,
    audit_collatz_d8_payloads,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.physical_support_payload_audit import (
    PhysicalSupportPayloadAudit,
)


def audit_dyadic_return_payloads(
    ledger: ResourceLedger,
) -> PhysicalSupportPayloadAudit:
    """Check exact stores, seals, and composition laws without trusting a family."""
    from number_compiler.hashlife.execution.dyadic_return_images import (
        DyadicCycleSummary,
        DyadicImageSummary,
        DyadicReturnActionID,
        DyadicReturnCycle,
        DyadicReturnImageID,
        DyadicReturnImageWorkspace,
        DyadicReturnLaw,
        DyadicReturnSourceID,
        DyadicReturnSupportID,
        _ActionNode,
        _identity_transfer,
        _ImageNode,
        _low_bits,
        _SourceNode,
        _SupportNode,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.resources.tile_scheduler_inventory_support import (
        valid_source_only_scheduler,
    )

    roots = tuple(ledger.iter_execution_roots())
    containers = dict(ledger.iter_containers())
    inventory = {row.owner: row for row in ledger.inventory()}
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()

    local_tables = audit_collatz_d8_payloads(ledger)
    approved.update(local_tables.approved)
    invalid.update(local_tables.invalid)

    for root in roots:
        if not isinstance(root, DyadicReturnImageWorkspace):
            continue
        raw_owner = getattr(root, "image_owner", -1)
        owner = raw_owner if type(raw_owner) is int else -1
        root_approved: set[int] = set()
        try:
            from number_compiler.sequences.antihydra.arithmetic_images import (
                AntihydraArithmeticImageWorkspace,
            )
            from number_compiler.sequences.collatz.physical_images import (
                CollatzPhysicalImageWorkspace,
            )

            if type(root) not in (
                DyadicReturnImageWorkspace,
                AntihydraArithmeticImageWorkspace,
                CollatzPhysicalImageWorkspace,
            ):
                raise TypeError("unrecognized dyadic return workspace adapter")

            def action_node(
                identity: DyadicReturnActionID,
                workspace: DyadicReturnImageWorkspace = root,
            ) -> _ActionNode:
                return DyadicReturnImageWorkspace.action_node(workspace, identity)

            def source_node(
                identity: DyadicReturnSourceID,
                workspace: DyadicReturnImageWorkspace = root,
            ) -> _SourceNode:
                return DyadicReturnImageWorkspace.source_node(workspace, identity)

            def support_node(
                identity: DyadicReturnSupportID,
                workspace: DyadicReturnImageWorkspace = root,
            ) -> _SupportNode:
                return DyadicReturnImageWorkspace.support_node(workspace, identity)

            def image_node(
                identity: DyadicReturnImageID,
                workspace: DyadicReturnImageWorkspace = root,
            ) -> _ImageNode:
                return DyadicReturnImageWorkspace.image_node(workspace, identity)

            def transfer_matches(
                retained: SkewTransfer[int],
                reconstructed: SkewTransfer[int],
                admitted: _SourceNode,
                workspace: DyadicReturnImageWorkspace = root,
            ) -> bool:
                """Compare full affine laws or an authenticated Collatz singleton."""
                if (
                    retained.upper < 0
                    or reconstructed.upper < 0
                    or retained.lower <= 0
                    or reconstructed.lower <= 0
                ):
                    return False
                collatz = (
                    workspace.law.gains,
                    workspace.law.offsets,
                    workspace.law.weights,
                ) == (
                    (1, 6),
                    (0, 2),
                    (0, 1),
                )
                if retained.upper == 0 and reconstructed.upper != 0:
                    if (
                        not collatz
                        or not admitted.exact
                        or retained.lower != 1
                        or reconstructed.upper <= 0
                    ):
                        return False
                    exact_source = admitted.residue + (
                        admitted.lift << admitted.precision
                    )
                    numerator = (
                        reconstructed.upper * exact_source + reconstructed.offset
                    )
                    ledger.bump(
                        "dyadic_payload_audit_operand_bits",
                        exact_source.bit_length()
                        + abs(numerator).bit_length()
                        + reconstructed.lower.bit_length()
                        + abs(retained.offset).bit_length(),
                    )
                    return (
                        numerator % reconstructed.lower == 0
                        and numerator // reconstructed.lower == retained.offset
                    )
                return (
                    retained.upper * reconstructed.lower
                    == reconstructed.upper * retained.lower
                    and retained.offset * reconstructed.lower
                    == reconstructed.offset * retained.lower
                )

            owners = (
                root.action_owner,
                root.source_owner,
                root.support_owner,
                root.image_owner,
                root.width_owner,
                root.construction_owner,
                root.action_snapshot_owner,
                root.source_snapshot_owner,
                root.support_snapshot_owner,
                root.image_snapshot_owner,
                root.macro_owner,
                root.macro_stack_owner,
            )
            antihydra = root.law.family.startswith("antihydra")
            stores = (
                (
                    root.action_owner,
                    root.actions,
                    "arithmetic_action" if antihydra else "dyadic_return_action",
                    1,
                ),
                (
                    root.source_owner,
                    root.sources,
                    "arithmetic_source" if antihydra else "dyadic_return_source",
                    1,
                ),
                (
                    root.support_owner,
                    root.support,
                    "arithmetic_cylinder_support"
                    if antihydra
                    else "dyadic_return_support",
                    1,
                ),
                (
                    root.image_owner,
                    root.images,
                    "arithmetic_image" if antihydra else "dyadic_return_image",
                    1,
                ),
                (root.width_owner, root.by_width, "dyadic_return_action_index", 0),
                (root.construction_owner, root.construction_stack, "workspace", 1),
                (root.action_snapshot_owner, root.action_snapshots, "workspace", 1),
                (root.source_snapshot_owner, root.source_snapshots, "workspace", 1),
                (root.support_snapshot_owner, root.support_snapshots, "workspace", 1),
                (root.image_snapshot_owner, root.image_snapshots, "workspace", 1),
                (root.macro_owner, root.macros, "dyadic_return_macro_index", 1),
                (root.macro_stack_owner, root.macro_stack, "workspace", 1),
                (root.balanced_stack_owner, root.balanced_stack, "workspace", 1),
                (
                    root.demanded_support_owner,
                    root.demanded_support,
                    "dyadic_return_support_demand_index",
                    0,
                ),
            )
            scheduler_valid, core = valid_source_only_scheduler(
                root.scheduler, ledger, containers, roots
            )
            DyadicReturnLaw.__post_init__(root.law)
            if root.law.cycle is not None:
                DyadicReturnCycle.validate(root.law.cycle, root.law)
            valid = (
                root.ledger is ledger
                and type(root.seed) is int
                and root.seed >= 0
                and type(root.steps) is int
                and root.steps >= 0
                and type(root.law) is DyadicReturnLaw
                and root._law_snapshot == root.law.descriptor
                and root.family == root.law.family
                and root.semantic_version == root.law.semantic_version
                and type(root._closed) is bool
                and not root._closed
                and type(root.scheduler) is TileScheduler
                and scheduler_valid
                and core is not None
                and core._adapters.get((root.family, root.semantic_version)) is root
                and len(set(owners)) == len(owners)
                and all(type(store_owner) is int for store_owner in owners)
                and not root.construction_stack
                and not root.macro_stack
                and not root.balanced_stack
                and not root.macros
                and all(
                    containers.get(store_owner) is store
                    and inventory[store_owner].role == role
                    and inventory[store_owner].entries == len(store)
                    and inventory[store_owner].nodes == nodes * len(store)
                    and inventory[store_owner].accounting_delta == 0
                    for store_owner, store, role, nodes in stores
                )
                and len(root.action_snapshots) == len(root.actions)
                and len(root.source_snapshots) == len(root.sources)
                and len(root.support_snapshots) == len(root.support)
                and len(root.image_snapshots) == len(root.images)
                and len(root.by_width) == len(root.actions)
            )

            for index, action_record in enumerate(root.actions):
                action_id = DyadicReturnActionID(root.owner, root._ACTION_KIND, index)
                bound = type(action_record) is _ActionNode
                if bound:
                    resolved = action_node(action_id)
                    bound &= (
                        resolved is action_record
                        and type(action_record.width) is int
                        and action_record.width >= 0
                    )
                if bound and action_record.children is None:
                    bound &= action_record.width <= root.MAX_LEAF_STEPS
                elif bound:
                    assert action_record.children is not None
                    before_id, after_id = action_record.children
                    bound &= (
                        type(before_id) is DyadicReturnActionID
                        and type(after_id) is DyadicReturnActionID
                        and before_id.local_id < index
                        and after_id.local_id < index
                        and action_node(before_id).width + action_node(after_id).width
                        == action_record.width
                        and action_record.width > root.MAX_LEAF_STEPS
                    )
                bound &= root.by_width.get(action_record.width) == action_id
                valid &= bound
                if bound:
                    root_approved.update((id(action_record), id(action_id)))
                    if action_record.children is not None:
                        root_approved.update(map(id, action_record.children))

            for index, source_record in enumerate(root.sources):
                source_id = DyadicReturnSourceID(root.owner, root._SOURCE_KIND, index)
                bound = type(source_record) is _SourceNode
                if bound:
                    DyadicReturnImageWorkspace.validate_source(root, source_id)
                    bound &= (
                        source_node(source_id) is source_record
                        and type(source_record.side) is int
                        and type(source_record.parent)
                        in (DyadicReturnSourceID, type(None))
                        and type(source_record.parent_action)
                        in (DyadicReturnActionID, type(None))
                        and type(source_record.before_image)
                        in (DyadicReturnImageID, type(None))
                    )
                if bound and source_record.side == 0:
                    bound &= (
                        source_record.parent is None
                        and source_record.parent_action is None
                        and source_record.before_image is None
                        and source_id == root.root_source
                    )
                elif bound:
                    bound &= (
                        type(source_record.parent) is DyadicReturnSourceID
                        and source_record.parent.local_id < index
                        and type(source_record.parent_action) is DyadicReturnActionID
                    )
                    if bound:
                        assert type(source_record.parent) is DyadicReturnSourceID
                        assert type(source_record.parent_action) is DyadicReturnActionID
                        parent = source_node(source_record.parent)
                        parent_action = action_node(source_record.parent_action)
                        bound &= parent_action.children is not None
                        if bound:
                            assert parent_action.children is not None
                            before_action, after_action = parent_action.children
                            if source_record.side == 1:
                                expected_exact = (
                                    parent.exact and root.law.cycle is not None
                                )
                                expected_lift = (
                                    root._source_value(parent)
                                    >> action_node(before_action).width
                                    if expected_exact
                                    else 0
                                )
                                bound &= (
                                    source_record.before_image is None
                                    and source_record.precision
                                    == action_node(before_action).width
                                    and source_record.residue
                                    == _low_bits(
                                        parent.residue, source_record.precision
                                    )
                                    and source_record.lift == expected_lift
                                    and source_record.exact == expected_exact
                                )
                            elif source_record.side == 2:
                                bound &= (
                                    type(source_record.before_image)
                                    is DyadicReturnImageID
                                    and source_record.precision
                                    == action_node(after_action).width
                                )
                                if bound:
                                    assert (
                                        type(source_record.before_image)
                                        is DyadicReturnImageID
                                    )
                                    previous_image = image_node(
                                        source_record.before_image
                                    )
                                    previous = previous_image.summary
                                    numerator = (
                                        previous.transfer.upper * parent.residue
                                        + previous.transfer.offset
                                    )
                                    bound &= (
                                        previous_image.action == before_action
                                        and source_node(previous_image.source).parent
                                        == source_record.parent
                                        and source_node(previous_image.source).side == 1
                                        and numerator % previous.transfer.lower == 0
                                        and source_record.residue
                                        == _low_bits(
                                            numerator // previous.transfer.lower,
                                            source_record.precision,
                                        )
                                    )
                                    expected_exact = False
                                    expected_lift = 0
                                    if (
                                        bound
                                        and root.law.cycle is not None
                                        and source_node(previous_image.source).exact
                                    ):
                                        exact_source = source_node(
                                            previous_image.source
                                        )
                                        exact_value = root._source_value(exact_source)
                                        exact_numerator = (
                                            previous.transfer.upper * exact_value
                                            + previous.transfer.offset
                                        )
                                        bound &= (
                                            exact_numerator % previous.transfer.lower
                                            == 0
                                        )
                                        if bound:
                                            exact_output = (
                                                exact_numerator
                                                // previous.transfer.lower
                                            )
                                            expected_exact = True
                                            expected_lift = (
                                                exact_output >> source_record.precision
                                            )
                                    bound &= (
                                        source_record.exact == expected_exact
                                        and source_record.lift == expected_lift
                                    )
                valid &= bound
                if bound:
                    root_approved.update((id(source_record), id(source_id)))
                    for reference in (
                        source_record.parent,
                        source_record.parent_action,
                        source_record.before_image,
                    ):
                        if reference is not None:
                            root_approved.add(id(reference))

            for index, support_record in enumerate(root.support):
                support_id = DyadicReturnSupportID(
                    root.owner, root._SUPPORT_KIND, index
                )
                bound = type(support_record) is _SupportNode
                if bound:
                    bound &= (
                        support_node(support_id) is support_record
                        and all(
                            type(value) is int
                            for value in (
                                support_record.width,
                                support_record.residue,
                                support_record.odd_steps,
                                support_record.delta,
                                support_record.minimum,
                            )
                        )
                        and type(support_record.transfer) is SkewTransfer
                        and type(support_record.branch_word) in (int, type(None))
                        and type(support_record.children) in (tuple, type(None))
                        and type(support_record.cycle)
                        in (DyadicCycleSummary, type(None))
                        and type(support_record.saturated) is bool
                    )
                if bound and support_record.saturated:
                    bound &= (
                        (root.law.gains, root.law.offsets, root.law.weights)
                        in (((1, 6), (0, 2), (0, 1)), ((3, 3), (0, -1), (2, -1)))
                        and support_record.branch_word is None
                        and support_record.children is None
                        and support_record.width > 0
                        and support_record.transfer.upper >= 0
                        and support_record.transfer.lower > 0
                        and 0 <= support_record.odd_steps <= support_record.width
                        and support_record.minimum <= min(0, support_record.delta)
                    )
                elif bound and support_record.branch_word is not None:
                    bound &= 0 < support_record.width <= root.MAX_LEAF_STEPS
                    if not bound:
                        valid = False
                        continue
                    state = support_record.residue
                    transfer = _identity_transfer()
                    odd_steps = delta = minimum = 0
                    branch_word = 0
                    for offset in range(support_record.width):
                        bit = state & 1
                        branch_word |= bit << offset
                        odd_steps += bit
                        gain = root.law.gains[bit]
                        shift = root.law.offsets[bit]
                        ledger.bump("dyadic_payload_audit_branch_steps")
                        ledger.bump(
                            "dyadic_payload_audit_operand_bits",
                            state.bit_length()
                            + gain.bit_length()
                            + shift.bit_length()
                            + transfer.upper.bit_length()
                            + transfer.offset.bit_length()
                            + transfer.lower.bit_length(),
                        )
                        numerator = gain * state + shift
                        if numerator % 2:
                            bound = False
                            break
                        state = numerator // 2
                        transfer = transfer.then(
                            SkewTransfer(gain, shift, 2), multiply=mul, add=add
                        )
                        delta += root.law.weights[bit]
                        minimum = min(minimum, delta)
                    bound &= (
                        support_record.children is None
                        and 0 < support_record.width <= root.MAX_LEAF_STEPS
                        and support_record.branch_word == branch_word
                        and support_record.odd_steps == odd_steps
                        and support_record.delta == delta
                        and support_record.minimum == minimum
                        and support_record.transfer == transfer
                        and support_record.cycle is None
                    )
                elif (
                    bound
                    and support_record.cycle is not None
                    and support_record.children is None
                ):
                    cycle = support_record.cycle
                    law_cycle = root.law.cycle
                    bound &= law_cycle is not None and all(
                        type(value) is int
                        for value in (
                            cycle.entry_steps,
                            cycle.cycle_phase,
                            cycle.cycles,
                            cycle.remainder,
                            cycle.terminal_phase,
                            cycle.odd_steps,
                            cycle.delta,
                            cycle.minimum,
                        )
                    )
                    if bound:
                        assert law_cycle is not None
                        ledger.bump("dyadic_payload_audit_cycle_checks")
                        ledger.bump(
                            "dyadic_payload_audit_operand_bits",
                            sum(
                                value.bit_length()
                                for value in (
                                    cycle.cycles,
                                    cycle.remainder,
                                    cycle.cycle_phase,
                                    support_record.width,
                                    support_record.residue,
                                    *law_cycle.states,
                                    *root.law.weights,
                                )
                            ),
                        )
                        length = len(law_cycle.states)
                        bound &= (
                            cycle.entry_steps == 0
                            and 0 <= cycle.cycle_phase < length
                            and cycle.cycles >= 0
                            and 0 <= cycle.remainder < length
                            and support_record.width
                            == cycle.cycles * length + cycle.remainder
                            and support_record.residue
                            == _low_bits(
                                law_cycle.states[cycle.cycle_phase],
                                support_record.width,
                            )
                            and cycle.terminal_phase
                            == (cycle.cycle_phase + cycle.remainder) % length
                        )
                    if bound:
                        assert law_cycle is not None
                        rotated = tuple(
                            law_cycle.states[
                                (cycle.cycle_phase + offset) % len(law_cycle.states)
                            ]
                            for offset in range(len(law_cycle.states))
                        )
                        weights = tuple(
                            root.law.weights[state & 1] for state in rotated
                        )
                        prefixes = tuple(accumulate(weights, initial=0))
                        ledger.bump(
                            "dyadic_payload_audit_prefix_additions", len(weights)
                        )
                        ledger.bump(
                            "dyadic_payload_audit_operand_bits",
                            sum(value.bit_length() for value in prefixes),
                        )
                        cycle_delta = prefixes[-1]
                        remainder_prefixes = prefixes[: cycle.remainder + 1]
                        expected_delta = (
                            cycle.cycles * cycle_delta + remainder_prefixes[-1]
                        )
                        expected_minimum = min(
                            (min(prefixes) + min(0, (cycle.cycles - 1) * cycle_delta))
                            if cycle.cycles
                            else min(remainder_prefixes),
                            cycle.cycles * cycle_delta + min(remainder_prefixes),
                        )
                        expected_odd = cycle.cycles * sum(
                            state & 1 for state in rotated
                        ) + sum(state & 1 for state in rotated[: cycle.remainder])
                        terminal = law_cycle.states[cycle.terminal_phase]
                        bound &= (
                            cycle.delta == expected_delta
                            and cycle.minimum == expected_minimum
                            and cycle.odd_steps == expected_odd
                            and support_record.delta == expected_delta
                            and support_record.minimum == expected_minimum
                            and support_record.odd_steps == expected_odd
                            and support_record.transfer == SkewTransfer(0, terminal, 1)
                            and support_record.branch_word is None
                        )
                elif bound and support_record.children is not None:
                    left_id, right_id = support_record.children
                    bound &= (
                        type(left_id) is DyadicReturnSupportID
                        and type(right_id) is DyadicReturnSupportID
                        and left_id.local_id < index
                        and right_id.local_id < index
                    )
                    if bound:
                        left = support_node(left_id)
                        right = support_node(right_id)
                        ledger.bump("dyadic_payload_audit_compositions")
                        ledger.bump(
                            "dyadic_payload_audit_operand_bits",
                            sum(
                                value.bit_length()
                                for value in (
                                    support_record.residue,
                                    left.width,
                                    right.width,
                                    left.transfer.upper,
                                    left.transfer.lower,
                                    left.transfer.offset,
                                    right.transfer.upper,
                                    right.transfer.lower,
                                    right.transfer.offset,
                                    left.delta,
                                    right.delta,
                                    left.minimum,
                                    right.minimum,
                                )
                            ),
                        )
                        numerator = (
                            left.transfer.upper * support_record.residue
                            + left.transfer.offset
                        )
                        bound &= (
                            numerator % left.transfer.lower == 0
                            and right.residue
                            == _low_bits(numerator // left.transfer.lower, right.width)
                            and support_record.width == left.width + right.width
                            and support_record.transfer
                            == left.transfer.then(right.transfer, multiply=mul, add=add)
                            and support_record.odd_steps
                            == left.odd_steps + right.odd_steps
                            and support_record.delta == left.delta + right.delta
                            and support_record.minimum
                            == min(left.minimum, left.delta + right.minimum)
                            and _low_bits(support_record.residue, left.width)
                            == left.residue
                        )
                        expected_cycle = (
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
                        bound &= support_record.cycle == expected_cycle
                else:
                    bound = False
                valid &= bound
                if bound:
                    root_approved.update(
                        (
                            id(support_record),
                            id(support_id),
                            id(support_record.transfer),
                        )
                    )
                    if support_record.children is not None:
                        root_approved.update(map(id, support_record.children))
                    if support_record.cycle is not None:
                        root_approved.add(id(support_record.cycle))

            for index, image_record in enumerate(root.images):
                image_id = DyadicReturnImageID(root.owner, root._IMAGE_KIND, index)
                bound = (
                    type(image_record) is _ImageNode
                    and type(image_record.summary) is DyadicImageSummary
                )
                if bound:
                    DyadicReturnImageWorkspace.validate_payload(root, image_id)
                    image_action = action_node(image_record.action)
                    image_source = source_node(image_record.source)
                    summary = image_record.summary
                    bound &= (
                        all(
                            type(value) is int
                            for value in (
                                summary.width,
                                summary.residue,
                                summary.delta,
                                summary.minimum,
                                summary.odd_steps,
                            )
                        )
                        and summary.width == image_action.width
                        and summary.residue == image_source.residue
                        and type(summary.transfer) is SkewTransfer
                        and type(summary.support) in (DyadicReturnSupportID, type(None))
                        and type(summary.cycle) in (DyadicCycleSummary, type(None))
                        and (
                            image_action.width == 0
                            or image_source.precision == image_action.width
                        )
                    )
                    if summary.support is None:
                        bound &= (
                            summary.width == 0
                            and summary.transfer == _identity_transfer()
                            and summary.cycle is None
                            and summary.delta
                            == summary.minimum
                            == summary.odd_steps
                            == 0
                        )
                    else:
                        retained = support_node(summary.support)
                        bound &= (
                            summary.width == retained.width
                            and summary.residue == retained.residue
                            and summary.transfer == retained.transfer
                            and summary.delta == retained.delta
                            and summary.minimum == retained.minimum
                            and summary.odd_steps == retained.odd_steps
                            and summary.cycle == retained.cycle
                        )
                        if bound and retained.saturated:
                            if retained.cycle is None:
                                expanded_id = root.demanded_support.get(image_id)
                                expanded = (
                                    None
                                    if expanded_id is None
                                    else support_node(expanded_id)
                                )
                                if (
                                    expanded is not None
                                    and id(expanded) in root_approved
                                    and not expanded.saturated
                                    and expanded.cycle is None
                                    and expanded.width == retained.width
                                    and expanded.residue == image_source.residue
                                ):
                                    # The preceding support pass independently
                                    # reconstructed these leaves and joins.
                                    # Reuse that demanded-support witness, not
                                    # the saturated record's own claimed effect.
                                    expected = (
                                        expanded.transfer,
                                        expanded.odd_steps,
                                        expanded.delta,
                                        expanded.minimum,
                                    )
                                    ledger.bump(
                                        "dyadic_payload_audit_reconstruction_hits"
                                    )
                                else:
                                    expected = _balanced_saturated_audit(
                                        root.law,
                                        image_source.residue,
                                        retained.width,
                                        ledger,
                                    )
                            else:
                                metadata = retained.cycle
                                law_cycle = root.law.cycle
                                bound &= (
                                    image_source.exact
                                    and law_cycle is not None
                                    and 0 < metadata.entry_steps <= 4096
                                    and metadata.entry_steps <= retained.width
                                )
                                if bound:
                                    assert law_cycle is not None
                                    prefix = _balanced_saturated_audit(
                                        root.law,
                                        image_source.residue,
                                        metadata.entry_steps,
                                        ledger,
                                    )
                                    source_value = image_source.residue
                                    if image_source.lift:
                                        source_value += (
                                            1 << image_source.precision
                                        ) * image_source.lift
                                    numerator = (
                                        prefix[0].upper * source_value
                                        + prefix[0].offset
                                    )
                                    bound &= numerator % prefix[0].lower == 0
                                if bound:
                                    assert law_cycle is not None
                                    assert metadata is not None
                                    entry_value = numerator // prefix[0].lower
                                    length = len(law_cycle.states)
                                    bound &= (
                                        0 <= metadata.cycle_phase < length
                                        and entry_value
                                        == law_cycle.states[metadata.cycle_phase]
                                        and metadata.cycles >= 0
                                        and 0 <= metadata.remainder < length
                                        and metadata.entry_steps
                                        + metadata.cycles * length
                                        + metadata.remainder
                                        == retained.width
                                    )
                                if bound:
                                    assert law_cycle is not None
                                    (
                                        safety,
                                        cycle_odd,
                                        remainder_safety,
                                        remainder_odd,
                                    ) = cycle_phase_summaries(
                                        root.law,
                                        metadata.cycle_phase,
                                        metadata.remainder,
                                    )
                                    tail = safety.repeat(metadata.cycles).then(
                                        remainder_safety
                                    )
                                    tail_odd = (
                                        metadata.cycles * cycle_odd + remainder_odd
                                    )
                                    terminal_phase = (
                                        metadata.cycle_phase + metadata.remainder
                                    ) % length
                                    bound &= (
                                        metadata.terminal_phase == terminal_phase
                                        and metadata.odd_steps == tail_odd
                                        and metadata.delta == tail.delta
                                        and metadata.minimum == tail.minimum
                                    )
                                    expected = (
                                        SkewTransfer(
                                            0, law_cycle.states[terminal_phase], 1
                                        ),
                                        prefix[1] + tail_odd,
                                        prefix[2] + tail.delta,
                                        min(prefix[3], prefix[2] + tail.minimum),
                                    )
                            if bound:
                                bound &= (
                                    transfer_matches(
                                        retained.transfer, expected[0], image_source
                                    )
                                    and retained.odd_steps == expected[1]
                                    and retained.delta == expected[2]
                                    and retained.minimum == expected[3]
                                )
                        if summary.cycle is not None:
                            cycle_length = (
                                len(root.law.cycle.states)
                                if root.law.cycle is not None
                                else 0
                            )
                            bound &= (
                                image_source.exact
                                and cycle_length > 0
                                and summary.transfer.upper == 0
                                and summary.cycle.entry_steps
                                + summary.cycle.cycles * cycle_length
                                + summary.cycle.remainder
                                == summary.width
                            )
                valid &= bound
                if bound:
                    root_approved.update(
                        (
                            id(image_record),
                            id(image_record.summary),
                            id(image_record.summary.transfer),
                            id(image_record.source),
                            id(image_record.action),
                            id(image_id),
                        )
                    )
                    if image_record.summary.support is not None:
                        root_approved.add(id(image_record.summary.support))
                    if image_record.summary.cycle is not None:
                        root_approved.add(id(image_record.summary.cycle))

            for image_id, support_id in root.demanded_support.items():
                image = image_node(image_id)
                original = image.summary.support
                completed = support_node(support_id)
                valid &= (
                    original is not None
                    and support_node(original).saturated
                    and completed.width == image.summary.width
                    and completed.residue == image.summary.residue
                    and transfer_matches(
                        image.summary.transfer,
                        completed.transfer,
                        source_node(image.source),
                    )
                    and completed.odd_steps == image.summary.odd_steps
                    and completed.delta == image.summary.delta
                    and completed.minimum == image.summary.minimum
                    and completed.cycle == image.summary.cycle
                )
                root_approved.update((id(image_id), id(support_id)))

            root_precision = root.steps
            root_residue = _low_bits(root.seed, root_precision)
            root_lift = (
                0
                if root_precision and root.seed.bit_length() <= root_precision
                else root.seed >> root_precision
                if root_precision
                else root.seed
            )
            root_source = source_node(root.root_source)
            root_image = image_node(root.root_payload)
            valid &= (
                root.identity == DyadicReturnActionID(root.owner, root._ACTION_KIND, 0)
                and action_node(root.identity) == _ActionNode(0, None)
                and action_node(root.root_action).width == root.steps
                and root_source
                == _SourceNode(
                    root_residue,
                    root.steps,
                    root_lift,
                    None,
                    None,
                    None,
                    0,
                    True,
                )
                and root_image.source == root.root_source
                and root_image.action == root.root_action
            )

            for store in (
                root.by_width,
                root.action_snapshots,
                root.source_snapshots,
                root.support_snapshots,
                root.image_snapshots,
            ):
                for key, value in store.items():
                    root_approved.update((id(key), id(value)))
            if valid:
                if root.law.cycle is not None:
                    root_approved.update(
                        (id(root.law.cycle), id(root.law.cycle.states))
                    )
                root_approved.update(
                    (
                        id(root),
                        id(root.law),
                        id(root._law_snapshot),
                        id(root.scheduler),
                        id(root.owner),
                        id(root.identity),
                        id(root.root_action),
                        id(root.root_source),
                        id(root.root_image),
                        id(root.root_payload),
                        *(id(store) for _, store, _, _ in stores),
                    )
                )
                approved.update(root_approved)
            else:
                invalid.add((owner, id(root)))
        except (
            AttributeError,
            ArithmeticError,
            IndexError,
            KeyError,
            TypeError,
            ValueError,
        ):
            invalid.add((owner, id(root)))

    return PhysicalSupportPayloadAudit(frozenset(approved), frozenset(invalid))


__all__ = ["audit_dyadic_return_payloads"]
