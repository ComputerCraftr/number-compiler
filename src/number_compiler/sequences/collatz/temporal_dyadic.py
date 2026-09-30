"""Ledger-owned finite D8 source-section transducer.

A row is determined by all eight low source bits and retains only the odd
count and target origin. At fixed width, the centered action is 3**odd;
the target origin belongs to the occurrence. Cold discovery evaluates eight
local normalized symbols and is explicitly counted; it never evaluates the unbounded source.
This finite leaf table does not identify arbitrary continuation sections.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import cast

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict

# odd symbols, target origin: nine centered actions, 127 translated effects.
D8Row = tuple[int, int]


@dataclass(frozen=True, slots=True)
class D8CylinderFrame:
    """Transient affine view of one unconsumed exact source cylinder.

    Its value is ``origin + gain * (source >> consumed)``. Advancing the
    consumed coordinate avoids copying the full high fiber at each byte.
    This frame is not a semantic action or a retained occurrence identity.
    """

    source: int
    consumed: int = 0
    origin: int = 0
    gain: int = 1
    _local_word: int = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (self.source, self.consumed, self.origin, self.gain)
        ):
            raise TypeError("D8 cylinder frame requires exact integers")
        if self.source <= 0 or min(self.consumed, self.origin) < 0 or self.gain <= 0:
            raise ValueError("D8 cylinder frame has an invalid coordinate")
        if self.consumed >= self.source.bit_length():
            byte = 0
        else:
            byte = (self.source & (255 << self.consumed)) >> self.consumed
        object.__setattr__(self, "_local_word", self.origin + self.gain * byte)

    def local_word(self) -> int:
        return self._local_word

    def materialize(self) -> int:
        return self.origin + self.gain * (self.source >> self.consumed)

    def above_cycle(self) -> bool:
        # A high fiber at least four excludes normalized cycle states 1/2.
        if self.source.bit_length() > self.consumed + 2:
            return True
        # Here the remaining high fiber has at most two bits; this is a
        # bounded cycle probe rather than a full source-lift multiplication.
        return self.origin + self.gain * (self.source >> self.consumed) > 2


def d8_row(residue: int) -> D8Row:
    """Construct one finite alphabet row, independently of source magnitude."""
    if type(residue) is not int or not 0 <= residue < 256:
        raise ValueError("D8 source residue must be an eight-bit integer")
    current, ones = residue, 0
    for _ in range(8):
        if current & 1:
            ones += 1
            current = (3 * current + 1) >> 1
        else:
            current >>= 1
    return ones, current


class D8TemporalTable:
    """At most 256 exact residue rows, shared only within one resource ledger."""

    NODES_PER_ROW = 3

    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        self.owner = ledger.register(
            "collatz-physical-d8-local-table", "collatz_d8_local_table"
        )
        retained = ledger.registered_container(self.owner)
        if retained is None:
            self.rows: LedgerDict[int, D8Row] = ledger.make_dict(
                self.owner, nodes_per_entry=self.NODES_PER_ROW, write_once=True
            )
        elif type(retained) is LedgerDict:
            self.rows = cast(LedgerDict[int, D8Row], retained)
        else:
            raise ValueError("D8 table has another resource owner")

    @classmethod
    def for_ledger(cls, ledger: ResourceLedger) -> D8TemporalTable:
        return cls(ledger)

    def select(self, source: int) -> D8Row:
        if type(source) is not int or source <= 0:
            raise ValueError("D8 source must be a positive exact integer")
        if (
            type(self.rows) is not LedgerDict
            or self.rows.ledger is not self.ledger
            or self.rows.owner != self.owner
            or not self.rows.write_once
            or self.rows.nodes_per_entry != self.NODES_PER_ROW
            or self.ledger.registered_container(self.owner) is not self.rows
        ):
            raise ValueError("D8 table belongs to another resource owner")
        residue = source & 255
        found = self.rows.get(residue)
        if found is not None:
            self.ledger.bump("collatz_physical_temporal_d8_table_hits")
            return found
        self.ledger.reserve(self.owner, entries=1, nodes=self.NODES_PER_ROW)
        # Charge the admitted fixed discovery bound even if construction fails;
        # successful publication is a separate event, never a work proxy.
        self.ledger.bump("collatz_physical_temporal_d8_discovery_requests")
        self.ledger.bump("collatz_physical_temporal_d8_discovery_symbols", 8)
        try:
            found = d8_row(residue)
            self.rows[residue] = found
        except BaseException:
            self.ledger.bump("collatz_physical_temporal_d8_discovery_failures")
            self.ledger.release(self.owner, entries=1, nodes=self.NODES_PER_ROW)
            raise
        self.ledger.bump("collatz_physical_temporal_d8_table_publications")
        return found

    def transition(
        self, frame: D8CylinderFrame
    ) -> tuple[D8CylinderFrame, int, int, int]:
        """Apply the exact byte transition without forming its full endpoint."""
        if type(frame) is not D8CylinderFrame:
            raise TypeError("D8 transition requires its exact cylinder frame")
        local = frame.local_word()
        residue = local & 255
        ones, target_origin = self.select(residue + 256)
        multiplier = 3**ones
        result = D8CylinderFrame(
            frame.source,
            frame.consumed + 8,
            target_origin + multiplier * (local >> 8),
            multiplier * frame.gain,
        )
        self.ledger.bump("collatz_physical_temporal_d8_cylinder_transitions")
        self.ledger.bump("collatz_physical_temporal_d8_source_window_bits", 8)
        self.ledger.bump(
            "collatz_physical_temporal_d8_frame_operand_bits",
            local.bit_length()
            + frame.gain.bit_length()
            + result.origin.bit_length()
            + result.gain.bit_length(),
        )
        # Include attempted/rejected transitions in the existing arithmetic
        # work account. Both finite D8 row coefficients have a 13-bit bound.
        self.ledger.bump(
            "collatz_physical_temporal_run_operand_bits",
            local.bit_length()
            + frame.gain.bit_length()
            + result.origin.bit_length()
            + result.gain.bit_length()
            + 26,
        )
        return result, ones, residue, target_origin
