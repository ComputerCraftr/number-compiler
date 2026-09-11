"""Retained callbacks cannot hide exact future digit geometry."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.fields.dyadic_tile import source_span
from number_compiler.resources.callback_payload_audit import (
    audit_callback_future_payloads,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerDict, LedgerList


class _CallbackHolder:
    def __init__(self, callback: Callable[[], object]) -> None:
        self.callback = callback


@dataclass(frozen=True)
class _OriginalDigits:
    digits: tuple[int, ...]


def test_callback_captured_future_tail_is_forbidden() -> None:
    ledger = ResourceLedger()
    future_tail = source_span((1, 0, 1), blank=0, logical_length=3)

    def retained_callback() -> int:
        return future_tail.length

    holder = _CallbackHolder(retained_callback)
    ledger.register_execution_root(holder)
    assert collect_ledger_metrics(ledger).forbidden_future_payloads > 0


def test_callback_captured_immutable_source_is_permitted() -> None:
    ledger = ResourceLedger()
    original_source = ExactSource((1, 0, 1), 2)

    def retained_callback() -> int | None:
        return original_source.extent

    holder = _CallbackHolder(retained_callback)
    ledger.register_execution_root(holder)
    report = collect_ledger_metrics(ledger)
    assert report.forbidden_future_payloads == 0


def test_accounting_callback_does_not_claim_ledger_owned_source_digits() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("original-digits", "exact_source")
    records: LedgerList[object]
    records = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    records.append(_OriginalDigits((1, 0, 1)))
    ledger.register_container(owner, records, payloads=lambda: records)

    def retained_callback() -> int:
        return ledger.entries

    ledger.register_execution_root(_CallbackHolder(retained_callback))
    assert not audit_callback_future_payloads(ledger)


def test_registered_store_cannot_hide_a_suspicious_future_capture() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("query", "query_memo")
    future_word: LedgerDict[object, object]
    future_word = ledger.make_dict(owner)
    ledger.reserve(owner, entries=1)
    future_word[0] = 1
    ledger.register_container(owner, future_word, payloads=future_word.items)

    holder = _CallbackHolder(lambda: len(future_word))
    ledger.register_execution_root(holder)

    assert audit_callback_future_payloads(ledger)


def _future_payload_callback(payload_name: str) -> Callable[[], int]:
    value = (1 << 255) + 1
    if payload_name == "affine_b":
        affine_b = value
        return lambda: affine_b
    if payload_name == "complete_b":
        complete_b = value
        return lambda: complete_b
    if payload_name == "whole_word":
        whole_word = value
        return lambda: whole_word
    if payload_name == "carry_outputs":
        carry_outputs = value
        return lambda: carry_outputs
    h_rows = value
    return lambda: h_rows


@pytest.mark.parametrize(
    "payload_name",
    ("affine_b", "complete_b", "whole_word", "carry_outputs", "h_rows"),
)
def test_callback_cannot_hide_named_future_integer_payloads(payload_name: str) -> None:
    ledger = ResourceLedger()
    holder = _CallbackHolder(_future_payload_callback(payload_name))
    ledger.register_execution_root(holder)
    assert collect_ledger_metrics(ledger).forbidden_future_payloads > 0
