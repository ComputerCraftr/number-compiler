"""An exact source suffix can be an exact future endpoint, even re-encoded."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.projection.radix_original_source import (
    OriginalRadixArena,
    OriginalRadixKey,
    OriginalRadixSource,
)
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


def digits(value: int, radix: int) -> tuple[int, ...]:
    result: list[int] = []
    while value:
        value, digit = divmod(value, radix)
        result.append(digit)
    return tuple(result or [0])


@pytest.mark.parametrize("radix", (2, 3, 6, 12, 1 << 63))
@pytest.mark.parametrize("shift", (1, 4, 6))
def test_correctly_encoded_original_suffix_is_forbidden_retained_payload(
    radix: int, shift: int
) -> None:
    # For even input54, shift1 is the actual C1 endpoint27. Every injected
    # digit is mathematically correct; provenance alone does not admit a tail.
    term = PoweredCollatzTerm(54, 1)
    arena = OriginalRadixArena(term.resource_ledger)
    original = arena.encode(term.original_source_construction, radix)
    assert original.binary_start == 0
    key = OriginalRadixKey(term.original_source_construction, radix, shift)
    record = OriginalRadixSource(
        term.original_source_construction, radix, digits(54 >> shift, radix), shift
    )
    term.resource_ledger.reserve(arena.owner, entries=1, nodes=len(record.digits) + 1)
    arena.sources[key] = record
    before = term.resource_ledger.snapshot()
    report = collect_ledger_metrics(term.resource_ledger)
    assert term.resource_ledger.snapshot() == before
    assert report.forbidden_future_payloads > 0
    assert report.representation_boundary_complete == 0


@pytest.mark.parametrize("target", ("key", "record"))
def test_source_start_boolean_cannot_alias_full_original_coordinate(
    target: str,
) -> None:
    term = PoweredCollatzTerm(54, 1)
    arena = OriginalRadixArena(term.resource_ledger)
    record = arena.encode(term.original_source_construction, 3)
    key = next(iter(arena.sources))
    del arena.sources[key]
    malformed_key = replace(key, binary_start=False) if target == "key" else key
    malformed_record = (
        replace(record, binary_start=False) if target == "record" else record
    )
    arena.sources[malformed_key] = malformed_record
    before = term.resource_ledger.snapshot()
    assert collect_ledger_metrics(term.resource_ledger).forbidden_future_payloads > 0
    assert term.resource_ledger.snapshot() == before


def test_many_wide_radix_parameters_are_engine_keys_not_an_encoded_word() -> None:
    from number_compiler.projection.lazy_radix import collatz_radix_digit

    term = PoweredCollatzTerm((1 << 253) + 127, 2)
    for radix in (3, 6, 12, 3 << 61, (1 << 63) - 25):
        collatz_radix_digit(term, radix, 0)
    before = term.resource_ledger.snapshot()
    report = collect_ledger_metrics(term.resource_ledger)
    assert report.forbidden_future_payloads == 0
    assert term.resource_ledger.snapshot() == before


def test_radix_parameter_map_cannot_alias_a_different_execution_context() -> None:
    from number_compiler.projection.lazy_radix import collatz_radix_digit

    term = PoweredCollatzTerm(54, 1)
    collatz_radix_digit(term, 3, 0)
    snapshot = term.radix_projection_audit_source(term.resource_ledger)
    assert snapshot is not None
    store = snapshot.projections
    assert isinstance(store, LedgerDict)
    term.resource_ledger.reserve(store.owner, entries=1)
    store[6] = store[3]
    before = term.resource_ledger.snapshot()
    assert collect_ledger_metrics(term.resource_ledger).forbidden_future_payloads > 0
    assert term.resource_ledger.snapshot() == before
