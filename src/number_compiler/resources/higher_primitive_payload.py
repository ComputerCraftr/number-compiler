"""Narrow payload validation for bounded primitive higher-kernel memos."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_primitive_tables import (
    HigherPrimitiveTables,
)
from number_compiler.resources.higher_readonly import audit_validate_action
from number_compiler.resources.payload_containers import audit_mapping_items


def valid_higher_primitive_table(
    root: HigherPrimitiveTables,
    operation: str,
    container: object,
) -> bool:
    if operation not in ("step", "emit", "interface") or not isinstance(
        container, Mapping
    ):
        return False
    for key, result in audit_mapping_items(container):
        if operation == "interface":
            if (
                type(key) is not FieldCellActionID
                or type(result) is not tuple
                or len(result) != 3
                or any(type(item) is not int for item in result)
            ):
                return False
            try:
                audit_validate_action(root.schema, key)
                if root.schema.kind(key) != "primitive" or result != (
                    root.schema.state_count(key, 0),
                    root.schema.state_count(key, 1),
                    root.schema.alphabet(key)[1],
                ):
                    return False
            except (TypeError, ValueError, IndexError, AttributeError):
                return False
            continue
        if (
            type(key) is not tuple
            or len(key) != 4
            or type(key[0]) is not FieldCellActionID
            or any(type(item) is not int for item in key[1:])
            or type(result) is not int
        ):
            return False
        action = key[0]
        first, second, third = key[1:]
        try:
            audit_validate_action(root.schema, action)
            _, blank = root.schema.alphabet(action)
            if operation == "step":
                state_count = root.schema.state_count(action, first)
                valid = (
                    first in (0, 1)
                    and 0 <= second < state_count
                    and 0 <= third <= blank
                    and 0 <= result < state_count
                )
            else:
                left_count = root.schema.state_count(action, 0)
                right_count = root.schema.state_count(action, 1)
                valid = (
                    0 <= first < left_count
                    and 0 <= second <= blank
                    and 0 <= third < right_count
                    and 0 <= result <= blank
                )
        except (TypeError, ValueError, IndexError, AttributeError):
            return False
        if not valid:
            return False
    return True


__all__ = ["valid_higher_primitive_table"]
