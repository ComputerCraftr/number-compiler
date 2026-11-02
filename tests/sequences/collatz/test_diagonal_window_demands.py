"""Demand separation and accounting for bounded Collatz source windows."""

from __future__ import annotations

from collections.abc import Callable

import pytest

from number_compiler.sequences.collatz.diagonal_source_window import (
    CollatzDiagonalWindow,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalEndpointAction,
    DyadicTerminalFieldAction,
)


def _issue(
    source: int,
    physical_budget: int,
    *,
    retain_parity_mask: bool = False,
    retain_field_action: bool = True,
    record_work: Callable[[int], None] | None = None,
) -> CollatzDiagonalWindow:
    return CollatzDiagonalWindow.from_source_window(
        source,
        physical_budget,
        max_normalized=64,
        retain_parity_mask=retain_parity_mask,
        retain_field_action=retain_field_action,
        record_step=lambda: None,
        reserve_bits=lambda _bits: None,
        record_work=(lambda _bits: None) if record_work is None else record_work,
    )


def _normalized_states(source: int, steps: int) -> tuple[tuple[int, ...], int]:
    states: list[int] = []
    mask = 0
    current = source
    for index in range(steps):
        odd = current & 1
        if odd:
            mask |= 1 << index
            current = (3 * current + 1) // 2
        else:
            current //= 2
        states.append(current)
    return tuple(states), mask


def test_endpoint_only_window_never_constructs_full_field(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = (1 << 90) + 321

    def forbidden_create(
        _cls: type[DyadicTerminalFieldAction], *_coefficients: int
    ) -> DyadicTerminalFieldAction:
        raise AssertionError("endpoint-only source scan constructed full fields")

    monkeypatch.setattr(
        DyadicTerminalFieldAction,
        "_create",
        classmethod(forbidden_create),
    )
    window = _issue(source, 200, retain_field_action=False)
    states, _mask = _normalized_states(source, window.action.steps)
    assert type(window.action) is DyadicTerminalEndpointAction
    assert not hasattr(window.action, "sum_gain")
    assert window.normalized_endpoint == states[-1]
    with pytest.raises(ValueError, match="endpoint arithmetic only"):
        window.require_field_action()


def test_full_field_demand_matches_independent_endpoint_and_sum() -> None:
    source = 95 * (1 << 80) - 1
    full = _issue(source, 240)
    endpoint_only = _issue(source, 240, retain_field_action=False)
    states, _mask = _normalized_states(source, full.action.steps)

    action = full.require_field_action()
    assert type(action) is DyadicTerminalFieldAction
    assert type(endpoint_only.action) is DyadicTerminalEndpointAction
    assert (
        action.coefficient_snapshot()[:3] == endpoint_only.action.coefficient_snapshot()
    )
    assert full.normalized_endpoint == endpoint_only.normalized_endpoint == states[-1]
    assert action.sum_mod(source, 101) == sum(states) % 101


def test_window_certificate_rejects_action_variant_and_coefficient_tampering() -> None:
    source = (1 << 85) + 157
    endpoint_only = _issue(source, 180, retain_field_action=False)
    full = _issue(source, 180)

    original_action = endpoint_only.action
    object.__setattr__(endpoint_only, "action", full.action)
    with pytest.raises(ValueError, match="changed after issuance"):
        endpoint_only.require_issued()
    object.__setattr__(endpoint_only, "action", original_action)
    endpoint_only.require_issued()

    original_offset = original_action.offset
    object.__setattr__(original_action, "offset", original_offset + 1)
    with pytest.raises(ValueError, match="changed after issuance"):
        endpoint_only.require_issued()
    object.__setattr__(original_action, "offset", original_offset)
    endpoint_only.require_issued()


def test_parity_mask_charges_shift_and_or_operand_work_exactly() -> None:
    source = (1 << 88) + 931386509544713451
    base_work: list[int] = []
    parity_work: list[int] = []
    unmasked = _issue(
        source,
        220,
        retain_field_action=False,
        record_work=base_work.append,
    )
    masked = _issue(
        source,
        220,
        retain_parity_mask=True,
        retain_field_action=False,
        record_work=parity_work.append,
    )
    assert (
        masked.action.coefficient_snapshot() == unmasked.action.coefficient_snapshot()
    )

    _states, expected_mask = _normalized_states(source, masked.action.steps)
    expected_extra = 0
    partial_mask = 0
    for position in range(masked.action.steps):
        if expected_mask & (1 << position):
            shifted_bit = 1 << position
            updated_mask = partial_mask | shifted_bit
            expected_extra += (
                1
                + position.bit_length()
                + partial_mask.bit_length()
                + shifted_bit.bit_length()
                + updated_mask.bit_length()
            )
            partial_mask = updated_mask

    assert masked.parity_mask == expected_mask
    assert sum(parity_work) - sum(base_work) == expected_extra
