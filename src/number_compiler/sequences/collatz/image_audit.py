"""Validation for published Collatz physical source-image ports."""

from __future__ import annotations

from collections.abc import Hashable
from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnActionID,
    DyadicReturnImageID,
    DyadicReturnSourceID,
)
from number_compiler.hashlife.execution.source_bound_images import SourceImageBinding
from number_compiler.hashlife.execution.source_image_seals import _typed_equal
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointRunAction,
)
from number_compiler.sequences.collatz.tape_width import CollatzTapeWidthSummary

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.physical_images import (
        CollatzPhysicalImageWorkspace,
    )


def audit_image_binding(
    root: CollatzPhysicalImageWorkspace,
    binding: SourceImageBinding,
    payload: Hashable,
    failure_prefix: Hashable | None,
    tape_width_port: str,
    joint_cocycle_port: str,
    boundary_macro_port: str,
) -> tuple[Hashable, ...]:
    """Validate the exact Collatz image and its optional family observations."""
    if type(binding) is not SourceImageBinding:
        raise TypeError("Collatz image audit requires its exact binding")
    root.validate_source(binding.source)
    root.validate_action(binding.action)
    root.validate_payload(payload)
    source_id = binding.source
    action_id = binding.action
    if (
        type(source_id) is not DyadicReturnSourceID
        or type(action_id) is not DyadicReturnActionID
    ):
        raise TypeError("Collatz binding needs local source and action IDs")
    source = root.source_node(source_id)
    action = root.action_node(action_id)
    # Exact-source images retain the resolution of that authenticated
    # source even when a compressed cycle/composite spans more steps.
    # A non-exact cylinder image instead carries the temporal width that
    # its low-bit source prefix certifies. The identity action preserves
    # source precision in either case.
    expected_precision = (
        source.precision if source.exact or action.width == 0 else action.width
    )
    if (
        binding.family != root.family
        or binding.semantic_version != root.semantic_version
        or binding.extent != action.width
        or binding.orientation != 1
        or binding.radix != 2
        or binding.precision != expected_precision
        or failure_prefix is not None
    ):
        raise ValueError("Collatz source-image authority differs from root")
    if type(payload) is not DyadicReturnImageID:
        raise TypeError("Collatz source image has another payload")
    image = root.image_node(payload)
    if image.source != source_id or image.action != action_id:
        raise ValueError("Collatz source image payload differs from its binding")
    summary = image.summary
    root.validate_payload(payload)

    width_ports: list[tuple[object, ...]] = []
    joint_ports: list[tuple[object, ...]] = []
    boundary_macro_ports: list[tuple[object, ...]] = []
    for port in binding.boundary_ports:
        if (
            type(port) is tuple
            and port
            and type(port[0]) is str
            and port[0] == tape_width_port
        ):
            if len(port) != 2:
                raise ValueError("Collatz width port has an invalid shape")
            width_ports.append(port)
        if (
            type(port) is tuple
            and port
            and type(port[0]) is str
            and port[0] == joint_cocycle_port
        ):
            if len(port) != 2:
                raise ValueError("Collatz joint port has an invalid shape")
            joint_ports.append(port)
        if (
            type(port) is tuple
            and port
            and type(port[0]) is str
            and port[0] == boundary_macro_port
        ):
            if len(port) != 2:
                raise ValueError("Collatz boundary macro port has an invalid shape")
            boundary_macro_ports.append(port)
    if len(width_ports) > 1:
        raise ValueError("Collatz root has duplicate width ports")
    if len(joint_ports) > 1:
        raise ValueError("Collatz root has duplicate joint ports")
    if len(boundary_macro_ports) > 1:
        raise ValueError("Collatz root has duplicate boundary macro ports")
    if not boundary_macro_ports and (
        root._first_boundary_macro_snapshot is not None
        or root._boundary_macro_memo is not None
        and "root" in root._boundary_macro_memo
    ):
        raise ValueError("Collatz boundary macro snapshot was not published")

    ordinary = tuple(
        port
        for port in binding.boundary_ports
        if all(
            port is not removed
            for removed in (*width_ports, *joint_ports, *boundary_macro_ports)
        )
    )
    cycle = summary.cycle
    expected_transfer_port = (
        root.law.descriptor,
        summary.transfer.upper,
        summary.transfer.offset,
        summary.transfer.lower,
        summary.odd_steps,
    )
    valid_port = _typed_equal(ordinary, expected_transfer_port)
    if cycle is not None:
        expected_cycle_port = (
            root.law.descriptor,
            "singleton-cycle",
            cycle.entry_steps,
            cycle.cycle_phase,
            cycle.cycles,
            cycle.remainder,
            cycle.terminal_phase,
        )
        valid_port = valid_port or _typed_equal(ordinary, expected_cycle_port)
    if not valid_port:
        raise ValueError("Collatz image transfer/cycle port is inconsistent")

    if not width_ports and not joint_ports and not boundary_macro_ports:
        return ()
    if source_id != root.root_source or action_id != root.root_action:
        raise ValueError("Collatz optional summary belongs only to its root image")

    numerator = summary.transfer.upper * root.seed + summary.transfer.offset
    endpoint, remainder = divmod(numerator, summary.transfer.lower)
    if remainder or endpoint < 0:
        raise ValueError("Collatz root transfer is not an exact endpoint")
    width_record: tuple[object, ...] | None = None
    if width_ports:
        if (
            not root._include_width_spine
            or source_id != root.root_source
            or action_id != root.root_action
            or not source.exact
        ):
            raise ValueError("unrequested Collatz width summary was published")
        port = width_ports[0]
        width = port[1]
        if type(width) is not CollatzTapeWidthSummary:
            raise TypeError("Collatz width port has another summary sort")
        width.__post_init__()
        if (
            width.source_width != root.seed.bit_length()
            or width.target_width != endpoint.bit_length()
            or width.physical_ticks != root.steps
            or width.odd_steps != summary.odd_steps
            or width.normalized_symbols + width.odd_steps != root.steps
        ):
            raise ValueError("Collatz width port disagrees with its exact image")
        width_record = (port, width, width.blank)
    joint_record: tuple[object, ...] | None = None
    if joint_ports:
        if (
            not root._include_joint_cocycle
            or source_id != root.root_source
            or action_id != root.root_action
            or not source.exact
        ):
            raise ValueError("unrequested Collatz joint action was published")
        payload = joint_ports[0][1]
        if type(payload) is not tuple or payload != root._joint_action_snapshot:
            raise ValueError("Collatz joint port is not producer-issued by this root")
        joint = CollatzJointRunAction._from_admitted_root_payload(payload)
        normalized_endpoint = (
            endpoint
            if joint.phase == 0
            else (endpoint - 1) // 3
            if endpoint % 3 == 1
            else -1
        )
        if (
            joint.source != root.seed
            or joint.endpoint != endpoint
            or joint.normalized_endpoint != normalized_endpoint
            or joint.physical_ticks != root.steps
            or joint.normalized_steps + summary.odd_steps != root.steps
            or joint.odd_symbols + joint.phase != summary.odd_steps
            or joint.fields.endpoint(root.seed) != normalized_endpoint
            or not joint.fields.certifies(root.seed)
        ):
            raise ValueError("Collatz joint port differs from root source action")
        joint_record = (joint_ports[0],)
    boundary_macro_record: tuple[object, ...] | None = None
    if boundary_macro_ports:
        if not root._include_innovation_tape or not source.exact:
            raise ValueError("unrequested Collatz boundary macro was published")
        payload = boundary_macro_ports[0][1]
        if (
            type(payload) is not tuple
            or len(payload) != 2
            or type(payload[0]) is not int
            or payload[0] < 0
            or type(payload[1]) is not tuple
            or not _typed_equal(payload, root._first_boundary_macro_snapshot)
        ):
            raise ValueError("Collatz boundary macro is not producer-issued")
        start_tick = payload[0]
        macro = root._retained_boundary_macro()
        if macro is None or not _typed_equal(macro.structural_payload(), payload[1]):
            raise ValueError("Collatz boundary macro occurrence was altered")
        if start_tick + macro.physical_ticks > root.steps:
            raise ValueError("Collatz boundary macro exceeds its source action")
        boundary_macro_record = (boundary_macro_ports[0],)
    approved: list[Hashable] = []
    if width_record is not None:
        approved.extend(width_record)
    if joint_record is not None:
        approved.extend(joint_record)
    if boundary_macro_record is not None:
        approved.extend(boundary_macro_record)
    return tuple(approved)
