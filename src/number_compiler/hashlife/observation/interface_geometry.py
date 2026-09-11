"""Store-free interface geometry operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
)
from number_compiler.hashlife.execution.field_images import (
    SourceCellID,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_interfaces import (
        SemanticLocalInterfaceCompiler,
    )


def _observe_geometry(
    self: SemanticLocalInterfaceCompiler,
    source: SourceCellID,
    kernel: ActionProgramID,
    channel: str,
    left: int,
    right: int,
    coordinate: int,
) -> int:
    """Observe geometry by iteratively descending immutable source cells."""
    root = (source, channel, left, right, coordinate)
    values: dict[tuple[SourceCellID, str, int, int, int], int] = {}
    pending: list[tuple[bool, SourceCellID, str, int, int, int]] = [(False, *root)]
    while pending:
        (
            finishing,
            current,
            current_channel,
            current_left,
            current_right,
            current_coordinate,
        ) = pending.pop()
        key = (
            current,
            current_channel,
            current_left,
            current_right,
            current_coordinate,
        )
        if not finishing and key in values:
            continue
        node = self.sources.resolve(current)
        laws = self.primitives.compile(kernel)
        width = node.width
        if type(current_coordinate) is not int or current_coordinate < 0:
            raise ValueError("coordinate must be a nonnegative exact integer")
        if current_channel in ("output", "frame") and current_coordinate >= width:
            raise IndexError(current_coordinate)
        if not finishing and node.level == 0:
            symbol = self.sources.symbol(current)
            effect = self.kernels.kernel(kernel).effect
            emitted = effect.emit(current_left, symbol, current_right)
            if current_channel in ("output", "normalization"):
                values[key] = emitted
            elif current_channel == "frame":
                values[key] = current_coordinate
            else:
                active = emitted != laws.blank
                if current_channel == "activity":
                    values[key] = int(active)
                elif current_channel in ("first_active", "last_active"):
                    values[key] = 0 if active else 1
                elif current_channel == "extent":
                    values[key] = int(active)
                elif current_channel == "growth":
                    values[key] = 1 + int(active) - int(symbol != laws.blank)
                elif current_channel == "termination":
                    values[key] = int(not active)
                elif current_channel in ("halo_left", "halo_right"):
                    values[key] = emitted
                else:
                    raise ValueError("unknown geometry channel")
            continue
        if not finishing:
            child_left, child_right = self.sources.children(current)
            half = self.sources.resolve(child_left).width
            left_interface = self._source_interfaces[(kernel, child_left)]
            right_interface = self._source_interfaces[(kernel, child_right)]
            left_mid = self._finite_observe(
                left_interface, "boundary_left", current_left, current_right
            )
            right_mid = self._finite_observe(
                right_interface, "boundary_right", current_left, current_right
            )
            dependencies: list[tuple[SourceCellID, str, int, int, int]] = []
            if current_channel in (
                "activity",
                "termination",
                "first_active",
                "last_active",
            ):
                dependencies.extend(
                    (
                        (child_left, "activity", current_left, right_mid, 0),
                        (child_right, "activity", left_mid, current_right, 0),
                    )
                )
                if current_channel == "first_active":
                    dependencies.extend(
                        (
                            (
                                child_left,
                                "first_active",
                                current_left,
                                right_mid,
                                0,
                            ),
                            (
                                child_right,
                                "first_active",
                                left_mid,
                                current_right,
                                0,
                            ),
                        )
                    )
                elif current_channel == "last_active":
                    dependencies.extend(
                        (
                            (child_left, "last_active", current_left, right_mid, 0),
                            (
                                child_right,
                                "last_active",
                                left_mid,
                                current_right,
                                0,
                            ),
                        )
                    )
            elif current_channel in ("output", "normalization"):
                if current_coordinate < half:
                    dependencies.append(
                        (
                            child_left,
                            current_channel,
                            current_left,
                            right_mid,
                            current_coordinate,
                        )
                    )
                else:
                    dependencies.append(
                        (
                            child_right,
                            current_channel,
                            left_mid,
                            current_right,
                            current_coordinate - half,
                        )
                    )
            elif current_channel == "extent":
                dependencies.extend(
                    (
                        (child_left, "activity", current_left, right_mid, 0),
                        (child_right, "activity", left_mid, current_right, 0),
                        (child_right, "extent", left_mid, current_right, 0),
                        (child_left, "extent", current_left, right_mid, 0),
                    )
                )
            elif current_channel == "growth":
                dependencies.extend(
                    ((current, "extent", current_left, current_right, 0),)
                )
            elif current_channel == "halo_left":
                dependencies.append((current, "output", current_left, current_right, 0))
            elif current_channel == "halo_right":
                dependencies.append(
                    (current, "output", current_left, current_right, width - 1)
                )
            elif current_channel == "frame":
                values[key] = current_coordinate
                continue
            else:
                raise ValueError("unknown geometry channel")
            pending.append(
                (
                    True,
                    current,
                    current_channel,
                    current_left,
                    current_right,
                    current_coordinate,
                )
            )
            for dependency in reversed(dependencies):
                pending.append((False, *dependency))
            continue
        child_left, child_right = self.sources.children(current)
        half = self.sources.resolve(child_left).width
        left_interface = self._source_interfaces[(kernel, child_left)]
        right_interface = self._source_interfaces[(kernel, child_right)]
        left_mid = self._finite_observe(
            left_interface, "boundary_left", current_left, current_right
        )
        right_mid = self._finite_observe(
            right_interface, "boundary_right", current_left, current_right
        )

        def get(dep: tuple[SourceCellID, str, int, int, int]) -> int:
            return values[(dep[0], dep[1], dep[2], dep[3], dep[4])]

        if current_channel == "activity":
            left_activity = bool(
                get((child_left, "activity", current_left, right_mid, 0))
            )
            right_activity = bool(
                get((child_right, "activity", left_mid, current_right, 0))
            )
            values[key] = int(left_activity or right_activity)
        elif current_channel in ("output", "normalization"):
            if current_coordinate < half:
                values[key] = get(
                    (
                        child_left,
                        current_channel,
                        current_left,
                        right_mid,
                        current_coordinate,
                    )
                )
            else:
                values[key] = get(
                    (
                        child_right,
                        current_channel,
                        left_mid,
                        current_right,
                        current_coordinate - half,
                    )
                )
        elif current_channel == "frame":
            values[key] = current_coordinate
        elif current_channel == "first_active":
            left_activity = bool(
                get((child_left, "activity", current_left, right_mid, 0))
            )
            right_activity = bool(
                get((child_right, "activity", left_mid, current_right, 0))
            )
            if left_activity:
                values[key] = get(
                    (child_left, "first_active", current_left, right_mid, 0)
                )
            elif right_activity:
                values[key] = half + get(
                    (child_right, "first_active", left_mid, current_right, 0)
                )
            else:
                values[key] = width
        elif current_channel == "last_active":
            left_activity = bool(
                get((child_left, "activity", current_left, right_mid, 0))
            )
            right_activity = bool(
                get((child_right, "activity", left_mid, current_right, 0))
            )
            if right_activity:
                values[key] = half + get(
                    (child_right, "last_active", left_mid, current_right, 0)
                )
            elif left_activity:
                values[key] = get(
                    (child_left, "last_active", current_left, right_mid, 0)
                )
            else:
                values[key] = width
        elif current_channel == "extent":
            right_activity = bool(
                get((child_right, "activity", left_mid, current_right, 0))
            )
            if right_activity:
                values[key] = half + get(
                    (child_right, "extent", left_mid, current_right, 0)
                )
            else:
                values[key] = get((child_left, "extent", current_left, right_mid, 0))
        elif current_channel == "growth":
            extent = get((current, "extent", current_left, current_right, 0))
            values[key] = (
                width
                + extent
                - self._source_extent(
                    source,
                    laws,
                    kernel,
                )
            )
        elif current_channel == "termination":
            left_activity = bool(
                get((child_left, "activity", current_left, right_mid, 0))
            )
            right_activity = bool(
                get((child_right, "activity", left_mid, current_right, 0))
            )
            values[key] = int(not (left_activity or right_activity))
        elif current_channel == "halo_left":
            values[key] = get((current, "output", current_left, current_right, 0))
        elif current_channel == "halo_right":
            values[key] = get(
                (current, "output", current_left, current_right, width - 1)
            )
        else:
            raise ValueError("unknown geometry channel")
    return values[(source, channel, left, right, coordinate)]
