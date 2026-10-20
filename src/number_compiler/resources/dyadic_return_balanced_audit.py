"""Independent bounded-leaf audit for saturated dyadic support."""

from __future__ import annotations

from operator import add, mul
from typing import TypeAlias, cast

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
)
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_records import DyadicReturnLaw
from number_compiler.hashlife.execution.dyadic_return_transport import low_bits
from number_compiler.resources.ledger import ResourceLedger, ResourceScope
from number_compiler.resources.metric_keys import resources as _resources_keys
from number_compiler.resources.physical_support_payload_audit import (
    PhysicalSupportPayloadAudit,
)

AuditEffect: TypeAlias = tuple[SkewTransfer[int], int, int, int]


def balanced_saturated_audit(
    law: DyadicReturnLaw,
    source: int,
    width: int,
    ledger: ResourceLedger,
) -> tuple[SkewTransfer[int], int, int, int]:
    """Independently check a Collatz image by bounded leaves and balanced joins.

    The audit reads the authenticated source cylinder.  Each source bit is
    classified once in a leaf of at most 64 steps; joins operate on matching
    dyadic intervals.  This keeps the explicit audit's charged precision work
    below the old growing-prefix replay while still detecting a forged effect.
    """
    if width <= 0:
        raise ValueError("saturated audit needs a positive extent")

    # The audit has no ledger-owned retention: its short local postorder stack
    # is charged as transient work, and every classification/join is counted.
    stack: list[tuple[int, int, AuditEffect | None]] = []
    span, residue = width, low_bits(source, width)
    while True:
        if span <= 64:
            state = residue
            transfer = SkewTransfer(1, 0, 1)
            odd = delta = minimum = 0
            for _ in range(span):
                bit = state & 1
                gain = law.gains[bit]
                shift = law.offsets[bit]
                next_numerator = gain * state + shift
                if next_numerator % 2:
                    raise ArithmeticError("audited dyadic leaf was not integral")
                state = next_numerator // 2
                transfer = transfer.then(
                    SkewTransfer(gain, shift, 2), multiply=mul, add=add
                )
                odd += bit
                delta += law.weights[bit]
                minimum = min(minimum, delta)
                ledger.bump(_resources_keys.DYADIC_PAYLOAD_AUDIT_BRANCH_STEPS)
                ledger.bump(
                    _resources_keys.DYADIC_PAYLOAD_AUDIT_OPERAND_BITS,
                    state.bit_length()
                    + transfer.upper.bit_length()
                    + abs(transfer.offset).bit_length()
                    + transfer.lower.bit_length(),
                )
            result: AuditEffect = (transfer, odd, delta, minimum)
        else:
            stack.append((span, residue, None))
            ledger.bump(
                _resources_keys.DYADIC_PAYLOAD_AUDIT_OPERAND_BITS,
                span.bit_length() + residue.bit_length(),
            )
            span = 1 << ((span - 1).bit_length() - 1)
            residue = low_bits(residue, span)
            continue

        while stack:
            parent_span, parent_residue, left = stack.pop()
            if left is None:
                stack.append((parent_span, parent_residue, result))
                ledger.bump(
                    _resources_keys.DYADIC_PAYLOAD_AUDIT_OPERAND_BITS,
                    parent_span.bit_length()
                    + parent_residue.bit_length()
                    + sum(
                        abs(value).bit_length()
                        for value in (
                            result[0].upper,
                            result[0].offset,
                            result[0].lower,
                        )
                    ),
                )
                span = parent_span - (1 << ((parent_span - 1).bit_length() - 1))
                numerator = result[0].upper * parent_residue + result[0].offset
                if numerator % result[0].lower:
                    raise ArithmeticError("audited dyadic seam was not integral")
                residue = low_bits(numerator // result[0].lower, span)
                break
            right = result
            transfer = left[0].then(right[0], multiply=mul, add=add)
            ledger.bump(_resources_keys.DYADIC_PAYLOAD_AUDIT_COMPOSITIONS)
            ledger.bump(
                _resources_keys.DYADIC_PAYLOAD_AUDIT_OPERAND_BITS,
                sum(
                    abs(value).bit_length()
                    for value in (
                        parent_residue,
                        left[0].upper,
                        left[0].offset,
                        left[0].lower,
                        right[0].upper,
                        right[0].offset,
                        right[0].lower,
                    )
                ),
            )
            result = (
                transfer,
                left[1] + right[1],
                left[2] + right[2],
                min(left[3], left[2] + right[3]),
            )
        else:
            return result


def audit_collatz_d8_payloads(ledger: ResourceLedger) -> PhysicalSupportPayloadAudit:
    """Independently authenticate the bounded local D8 coefficient store."""
    containers = dict(ledger.iter_containers())
    inventory = {row.owner: row for row in ledger.inventory()}
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    canonical_rows: dict[int, tuple[int, int]] = {}
    # A D8 table is finite source-residue algebra, not an unbounded itinerary.
    # Reconstruct each retained row on two independent small scalar lifts so
    # neither its claimed odd count nor its target origin is trusted.
    from number_compiler.resources.stores import LedgerDict

    def exact_table(value: object) -> LedgerDict[object, object] | None:
        value_object = value
        if type(value_object) is not LedgerDict:
            return None
        return cast(LedgerDict[object, object], value_object)

    for table_owner, table_inventory in inventory.items():
        if table_inventory.role != "collatz_d8_local_table":
            continue
        table = containers.get(table_owner)
        table_store = exact_table(table)
        local_table_approved: set[int] = set()
        try:
            table_valid = (
                table_store is not None
                and table_store.ledger is ledger
                and table_store.owner == table_owner
                and table_store.write_once
                and table_store.nodes_per_entry == 3
                and ledger.is_factory_container(table_store)
                and table_inventory.name == "collatz-physical-d8-local-table"
                and table_inventory.scope == ResourceScope.ENGINE_OWNED
                and table_inventory.accounting_delta == 0
                and not table_inventory.disposed
                and table_inventory.entries == len(table_store)
                and table_inventory.nodes == 3 * len(table_store)
                and len(table_store) <= 256
            )
            if table_valid:
                assert table_store is not None
                for residue, record in table_store.items():
                    if (
                        type(residue) is not int
                        or not 0 <= residue < 256
                        or not is_exact_object_tuple(record)
                        or len(record) != 2
                        or any(type(value) is not int for value in record)
                    ):
                        table_valid = False
                        break
                    values = cast(tuple[int, int], record)
                    low, high, ones = residue, residue + 256, 0
                    for _ in range(8):
                        bit = low & 1
                        ones += bit
                        low = (3 * low + 1) // 2 if bit else low // 2
                        high = (3 * high + 1) // 2 if high & 1 else high // 2
                    ledger.bump(
                        _resources_keys.COLLATZ_D8_PAYLOAD_AUDIT_LOCAL_SYMBOLS, 16
                    )
                    if values != (ones, low) or high - low != 3**ones:
                        table_valid = False
                        break
                    local_table_approved.add(id(record))
                    canonical_rows[residue] = values
            if table_valid:
                approved.update(local_table_approved)
                approved.add(id(table_store))
            else:
                invalid.add((table_owner, id(table)))
        except (AttributeError, ArithmeticError, KeyError, TypeError, ValueError):
            invalid.add((table_owner, id(table)))

    for table_owner, table_inventory in inventory.items():
        if table_inventory.role != "collatz_d8_width_prefix_table":
            continue
        table = containers.get(table_owner)
        table_store = exact_table(table)
        table_approved: set[int] = set()
        try:
            table_valid = (
                table_store is not None
                and table_store.ledger is ledger
                and table_store.owner == table_owner
                and table_store.write_once
                and table_store.nodes_per_entry == 24
                and ledger.is_factory_container(table_store)
                and table_inventory.name == "collatz-physical-d8-width-prefix-table"
                and table_inventory.scope == ResourceScope.ENGINE_OWNED
                and table_inventory.accounting_delta == 0
                and not table_inventory.disposed
                and table_inventory.entries == len(table_store)
                and table_inventory.nodes == 24 * len(table_store)
                and len(table_store) <= 256
            )
            if table_valid:
                assert table_store is not None
                for residue, record in table_store.items():
                    if type(residue) is not int or not 0 <= residue < 256:
                        table_valid = False
                        break
                    row = canonical_rows.get(residue)
                    if (
                        row is None
                        or not is_exact_object_tuple(record)
                        or len(record) != 2
                        or not is_exact_object_tuple(record[0])
                        or len(record[0]) != 9
                        or any(
                            not is_exact_object_tuple(prefix)
                            or len(prefix) != 2
                            or any(type(value) is not int for value in prefix)
                            for prefix in record[0]
                        )
                        or type(record[1]) is not int
                        or not 0 <= record[1] < 256
                    ):
                        table_valid = False
                        break
                    prefixes = cast(tuple[tuple[int, int], ...], record[0])
                    odd_mask = record[1]
                    low, high, ones = residue + 256, residue + 512, 0
                    expected: list[tuple[int, int]] = [(1, 0)]
                    multiplier, offset = 1, 0
                    for step in range(8):
                        bit = low & 1
                        ones += bit
                        if bit:
                            low = (3 * low + 1) // 2
                            high = (3 * high + 1) // 2
                            multiplier, offset = (
                                3 * multiplier,
                                3 * offset + (1 << step),
                            )
                        else:
                            low //= 2
                            high //= 2
                        expected.append((multiplier, offset))
                    ledger.bump(
                        _resources_keys.COLLATZ_D8_PAYLOAD_AUDIT_LOCAL_SYMBOLS, 16
                    )
                    if (
                        prefixes != tuple(expected)
                        or odd_mask.bit_count() != ones
                        or (odd_mask >> 8) != 0
                        or row[0] != ones
                        or row[1] != low - 3**ones
                        or high - low != 3**ones
                        or (prefixes[8][0] * residue + prefixes[8][1]) // 256 != row[1]
                        or (prefixes[8][0] * residue + prefixes[8][1]) % 256
                    ):
                        table_valid = False
                        break
                    for source in (residue + 256, residue + 512):
                        state = source
                        for step, (gain, shift) in enumerate(expected):
                            numerator = gain * source + shift
                            if (
                                numerator % (1 << step)
                                or numerator // (1 << step) != state
                            ):
                                table_valid = False
                                break
                            if step < 8:
                                state = (
                                    (3 * state + 1) // 2
                                    if (odd_mask >> step) & 1
                                    else state // 2
                                )
                        if not table_valid:
                            break
                    if not table_valid:
                        break
                    table_approved.update((id(record), id(prefixes)))
                    table_approved.update(map(id, prefixes))
            if table_valid:
                approved.update(table_approved)
                approved.add(id(table_store))
            else:
                invalid.add((table_owner, id(table)))
        except (AttributeError, ArithmeticError, KeyError, TypeError, ValueError):
            invalid.add((table_owner, id(table)))

    return PhysicalSupportPayloadAudit(frozenset(approved), frozenset(invalid))
