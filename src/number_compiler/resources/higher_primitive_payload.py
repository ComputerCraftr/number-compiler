"""Narrow payload validation for bounded primitive higher-kernel memos."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_integer_tuple,
    is_exact_object_tuple,
    object_mapping,
)
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
    mapping = object_mapping(container)
    if operation not in ("step", "emit", "interface") or mapping is None:
        return False
    for key, result in audit_mapping_items(mapping):
        if operation == "interface":
            if (
                type(key) is not FieldCellActionID
                or not is_exact_integer_tuple(result)
                or len(result) != 3
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
        if not is_exact_object_tuple(key) or len(key) != 4:
            return False
        action = key[0]
        first, second, third = key[1], key[2], key[3]
        if (
            type(action) is not FieldCellActionID
            or type(first) is not int
            or type(second) is not int
            or type(third) is not int
            or type(result) is not int
        ):
            return False
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
