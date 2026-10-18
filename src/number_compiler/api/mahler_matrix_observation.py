"""Bounded, explicitly demanded center transfer from an issued Mahler source."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.metric_keys import antihydra as keys
from number_compiler.sequences.antihydra.runtime import ArithmeticResult


def center_matrix_packet(result: ArithmeticResult, steps: int) -> dict[str, object]:
    """Authenticate the pointed source before constructing a finite future window."""
    from number_compiler.sequences.antihydra.mahler_center_depth_matrix import (
        MahlerCertifiedCenterDepthTransfer,
    )

    require_integer(steps, "center matrix physical ticks", 1, 32)
    result.require_source()
    source = result.h - 1
    if source <= 0 or source >= 10**256:
        return {
            "status": "unavailable",
            "reason": "center matrix requires a positive source with at most 256 digits",
            "temporal_repeat_certified": False,
        }
    ledger = result.ledger
    # One reusable empty account belongs to this query ledger. Reservations,
    # not the account, own each demand's scratch lifetime; disposing the account
    # would invalidate a later retry because register reuses the name.
    owner = ledger.register("mahler-center-matrix", "observer-scratch")
    # Three bitset matrices, transient row products and at most two candidate
    # paths per complete source fiber. At 32 ticks there are <=256 seam records,
    # 32 low-carry records, 16 radix-4 records and 32 pair separators, covered
    # by the fixed 2048 nodes. This charge is released on every exit.
    scratch = 2048 + 2 * (steps + 1) * (16 + (source.bit_length() + steps + 63) // 64)
    with ledger.reservation(owner, nodes=scratch):
        ledger.bump(keys.MAHLER_CENTER_MATRIX_DEMANDS)
        certificate = MahlerCertifiedCenterDepthTransfer.powered_from_source(
            source, steps, initial_ledger=result.balance
        )
        packet = certificate.packet()
        ledger.bump(keys.MAHLER_CENTER_MATRIX_PHYSICAL_STEPS, steps)
        del certificate
    packet["source_prefix_ledger_safe"] = result.first_failure_index is None
    packet["source_first_failure_index"] = result.first_failure_index
    packet["source_first_failure_index_unit"] = "one-based-macro-return"
    packet["source_minimum_ledger"] = result.minimum
    # This observer starts from a total arithmetic image. A safe suffix cannot
    # reinstate physical execution after an earlier ledger failure.
    packet["physical_continuation_authorized"] = False
    return packet
