"""Canonical action and source record checks for dyadic return payload audits."""

from __future__ import annotations

from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnActionID,
    DyadicReturnImageID,
    DyadicReturnImageWorkspace,
    DyadicReturnSourceID,
)
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnActionRecord,
    DyadicReturnSourceRecord,
)
from number_compiler.hashlife.execution.dyadic_return_transport import low_bits


def audit_action_records(
    workspace: DyadicReturnImageWorkspace, root_approved: set[int]
) -> bool:
    """Validate action node ordering, widths, and canonical width ownership."""
    section_valid = True
    for index, action_record in enumerate(workspace.actions):
        action_id = DyadicReturnActionID(workspace.owner, workspace.ACTION_KIND, index)
        bound = type(action_record) is DyadicReturnActionRecord
        if bound:
            resolved = DyadicReturnImageWorkspace.action_node(workspace, action_id)
            bound &= (
                resolved is action_record
                and type(action_record.width) is int
                and action_record.width >= 0
            )
        if bound and action_record.children is None:
            bound &= action_record.width <= workspace.MAX_LEAF_STEPS
        elif bound:
            assert action_record.children is not None
            before_id, after_id = action_record.children
            bound &= (
                type(before_id) is DyadicReturnActionID
                and type(after_id) is DyadicReturnActionID
                and before_id.local_id < index
                and after_id.local_id < index
                and DyadicReturnImageWorkspace.action_node(workspace, before_id).width
                + DyadicReturnImageWorkspace.action_node(workspace, after_id).width
                == action_record.width
                and action_record.width > workspace.MAX_LEAF_STEPS
            )
        bound &= workspace.by_width.get(action_record.width) == action_id
        section_valid &= bound
        if bound:
            root_approved.update((id(action_record), id(action_id)))
            if action_record.children is not None:
                root_approved.update(map(id, action_record.children))
    return section_valid


def audit_source_records(
    workspace: DyadicReturnImageWorkspace, root_approved: set[int]
) -> bool:
    """Validate source lineage, exact lifts, and image-derived residues."""
    section_valid = True
    for index, source_record in enumerate(workspace.sources):
        source_id = DyadicReturnSourceID(workspace.owner, workspace.SOURCE_KIND, index)
        bound = type(source_record) is DyadicReturnSourceRecord
        if bound:
            DyadicReturnImageWorkspace.validate_source(workspace, source_id)
            bound &= (
                DyadicReturnImageWorkspace.source_node(workspace, source_id)
                is source_record
                and type(source_record.side) is int
                and type(source_record.parent) in (DyadicReturnSourceID, type(None))
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
                and source_id == workspace.root_source
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
                parent = DyadicReturnImageWorkspace.source_node(
                    workspace, source_record.parent
                )
                parent_action = DyadicReturnImageWorkspace.action_node(
                    workspace, source_record.parent_action
                )
                bound &= parent_action.children is not None
                if bound:
                    assert parent_action.children is not None
                    before_action, after_action = parent_action.children
                    if source_record.side == 1:
                        expected_exact = (
                            parent.exact and workspace.law.cycle is not None
                        )
                        expected_lift = (
                            workspace._source_value(parent)
                            >> DyadicReturnImageWorkspace.action_node(
                                workspace, before_action
                            ).width
                            if expected_exact
                            else 0
                        )
                        bound &= (
                            source_record.before_image is None
                            and source_record.precision
                            == DyadicReturnImageWorkspace.action_node(
                                workspace, before_action
                            ).width
                            and source_record.residue
                            == low_bits(parent.residue, source_record.precision)
                            and source_record.lift == expected_lift
                            and source_record.exact == expected_exact
                        )
                    elif source_record.side == 2:
                        bound &= (
                            type(source_record.before_image) is DyadicReturnImageID
                            and source_record.precision
                            == DyadicReturnImageWorkspace.action_node(
                                workspace, after_action
                            ).width
                        )
                        if bound:
                            assert (
                                type(source_record.before_image) is DyadicReturnImageID
                            )
                            previous_image = DyadicReturnImageWorkspace.image_node(
                                workspace, source_record.before_image
                            )
                            previous = previous_image.summary
                            numerator = (
                                previous.transfer.upper * parent.residue
                                + previous.transfer.offset
                            )
                            bound &= (
                                previous_image.action == before_action
                                and DyadicReturnImageWorkspace.source_node(
                                    workspace, previous_image.source
                                ).parent
                                == source_record.parent
                                and DyadicReturnImageWorkspace.source_node(
                                    workspace, previous_image.source
                                ).side
                                == 1
                                and numerator % previous.transfer.lower == 0
                                and source_record.residue
                                == low_bits(
                                    numerator // previous.transfer.lower,
                                    source_record.precision,
                                )
                            )
                            expected_exact = False
                            expected_lift = 0
                            if (
                                bound
                                and workspace.law.cycle is not None
                                and DyadicReturnImageWorkspace.source_node(
                                    workspace, previous_image.source
                                ).exact
                            ):
                                exact_source = DyadicReturnImageWorkspace.source_node(
                                    workspace, previous_image.source
                                )
                                exact_value = workspace._source_value(exact_source)
                                exact_numerator = (
                                    previous.transfer.upper * exact_value
                                    + previous.transfer.offset
                                )
                                bound &= exact_numerator % previous.transfer.lower == 0
                                if bound:
                                    exact_output = (
                                        exact_numerator // previous.transfer.lower
                                    )
                                    expected_exact = True
                                    expected_lift = (
                                        exact_output >> source_record.precision
                                    )
                            bound &= (
                                source_record.exact == expected_exact
                                and source_record.lift == expected_lift
                            )
        section_valid &= bound
        if bound:
            root_approved.update((id(source_record), id(source_id)))
            for reference in (
                source_record.parent,
                source_record.parent_action,
                source_record.before_image,
            ):
                if reference is not None:
                    root_approved.add(id(reference))
    return section_valid


__all__ = ["audit_action_records", "audit_source_records"]
