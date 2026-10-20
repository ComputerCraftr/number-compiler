"""Independent container inventories and retained-payload audits for lazy indices."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class PayloadAudit:
    forbidden_future_payloads: int
    unbounded_future_integers: int
    unknown_payloads: int


DIGIT_FIELDS = frozenset(
    {
        "digits",
        "tail",
        "pair",
        "word",
        "limbs",
        "radix_digits",
        "coefficients",
        "span",
        "pair_span",
        "tail_span",
        "output_span",
        "carry_span",
        "event_span",
        "future_word",
        "whole_word",
        "normalized_tail",
        "affine_b",
        "complete_b",
        "offset_ports",
        "tile_ports",
    }
)
HISTORY_FIELDS = frozenset(
    {
        "carry_row",
        "carry_rows",
        "carry_tape",
        "carry_outputs",
        "live_rows",
        "low_payload",
        "high_payload",
        "packed_history",
        "activity_mask",
        "h_row",
        "h_rows",
        "slab",
        "cut",
    }
)

AGGREGATE_EXEMPT_PAYLOAD_ROLES = frozenset(
    {
        "exact_source",
        "exact_endpoint",
        "explicit_lowering",
        "lowering",
        "exact_microblock",
        "radix_image_binding",
        "image_input_reference",
        "image_input_reference_interner",
        "image_input_reference_binding",
        "future_behavior_admission",
        "future_behavior_publication_snapshot",
    }
)


def normalize_payload_role(role: str) -> str:
    return role.lower().replace("-", "_")


__all__ = [
    "AGGREGATE_EXEMPT_PAYLOAD_ROLES",
    "DIGIT_FIELDS",
    "HISTORY_FIELDS",
    "PayloadAudit",
    "normalize_payload_role",
]
