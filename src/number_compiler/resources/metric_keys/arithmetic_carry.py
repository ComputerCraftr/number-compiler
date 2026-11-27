"""Stable counter names for arithmetic carry execution."""

from typing import Final

REFLECTED_H_PRIMITIVE_TRANSITIONS: Final = "reflected_h_primitive_transitions"
REFLECTED_H_COMPUTED_CONES: Final = "reflected_h_computed_cones"
REFLECTED_H_REUSED_CONES: Final = "reflected_h_reused_cones"
REFLECTED_H_PACKED_ROW_EVALUATIONS: Final = "reflected_h_packed_row_evaluations"
REFLECTED_H_PACKED_ROW_OPERAND_BITS: Final = "reflected_h_packed_row_operand_bits"

REVERSE_PORT_CARRY_COMPOSITIONS: Final = "reverse_port_carry_compositions"
REVERSE_PORT_FUNCTION_COMPOSITIONS: Final = "reverse_port_function_compositions"
REVERSE_PORT_FUNCTION_OBSERVATIONS: Final = "reverse_port_function_observations"
REVERSE_PORT_PREDICATE_STATE_EVALUATIONS: Final = (
    "reverse_port_predicate_state_evaluations"
)
REVERSE_PORT_PRIMITIVE_OUTPUT_EVALUATIONS: Final = (
    "reverse_port_primitive_output_evaluations"
)
