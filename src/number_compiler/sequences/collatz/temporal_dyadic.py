"""Ledger-owned finite D8 source-section transducer.

A row is determined by all eight low source bits and retains only the odd
count and target origin. At fixed width, the centered action is 3**odd;
the target origin belongs to the occurrence. Cold discovery evaluates eight
local normalized symbols and is explicitly counted; it never evaluates the unbounded source.
This finite leaf table does not identify arbitrary continuation sections.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.fields.affine_width import nonnegative_affine_width
from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.tape_width import (
    CollatzTapeWidthSummary,
    compose_width_ledger,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.innovation_input_tape import (
        _D8ParityTransition,
    )

# Odd symbols and target origin: nine centered actions, 127 translated effects.
D8Prefix = tuple[int, int]
D8Row = tuple[int, int]
D8_VISIBLE_ROW = tuple[int, int]
D8WidthRow = tuple[tuple[D8Prefix, ...], int]
D8_ROOT_BATCH_MIN_SOURCE_BITS = 131_072


def d8_root_batch_admitted(source: int, remaining: int) -> bool:
    """Keep the bounded D8 frame route on the source's large root fiber."""
    return source.bit_length() > D8_ROOT_BATCH_MIN_SOURCE_BITS and remaining >= 32


def bounded_run_length(residue: int) -> int:
    """Return the exact homogeneous run capped by one D8 source window."""
    if residue & 1:
        return v2_positive(residue + 1)
    return 8 if residue == 0 else v2_positive(residue)


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
    _source_byte: int = field(init=False, repr=False, compare=False)
    _high_fiber_mod5: int | None = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (self.source, self.consumed, self.origin, self.gain)
        ):
            raise TypeError("D8 cylinder frame requires exact integers")
        if self.source <= 0 or min(self.consumed, self.origin) < 0 or self.gain <= 0:
            raise ValueError("D8 cylinder frame has an invalid coordinate")
        byte = self._read_source_byte(self.source, self.consumed)
        object.__setattr__(self, "_source_byte", byte)
        object.__setattr__(self, "_high_fiber_mod5", None)
        object.__setattr__(self, "_local_word", self.origin + self.gain * byte)

    @staticmethod
    def _read_source_byte(source: int, consumed: int) -> int:
        if consumed >= source.bit_length():
            return 0
        return (source & (255 << consumed)) >> consumed

    @staticmethod
    def _compute_high_fiber_mod5(source: int, consumed: int) -> int:
        return (source >> consumed) % 5

    def _after_eight(self, *, origin: int, gain: int) -> D8CylinderFrame:
        """Advance one byte while transporting the high fiber's F5 residue."""
        if type(self) is not D8CylinderFrame:
            raise TypeError("D8 residue transport requires an exact cylinder frame")
        if type(origin) is not int or origin < 0 or type(gain) is not int or gain <= 0:
            raise ValueError("advanced D8 frame has invalid affine coordinates")
        result = object.__new__(D8CylinderFrame)
        consumed = self.consumed + 8
        source_byte = self._read_source_byte(self.source, consumed)
        object.__setattr__(result, "source", self.source)
        object.__setattr__(result, "consumed", consumed)
        object.__setattr__(result, "origin", origin)
        object.__setattr__(result, "gain", gain)
        object.__setattr__(result, "_source_byte", source_byte)
        high_fiber_mod5 = self._high_fiber_mod5
        object.__setattr__(
            result,
            "_high_fiber_mod5",
            None
            if high_fiber_mod5 is None
            else (high_fiber_mod5 - self._source_byte) % 5,
        )
        object.__setattr__(result, "_local_word", origin + gain * source_byte)
        return result

    def local_word(self) -> int:
        return self._local_word

    def materialize(self) -> int:
        return self.origin + self.gain * (self.source >> self.consumed)

    def residue(self, modulus: int) -> int:
        """Read an exact bounded residue without materializing the high fiber."""
        if type(modulus) is not int or modulus < 1 or 160 % modulus:
            raise ValueError("D8 frame residue modulus must divide 160")
        low = self._source_byte & 31
        high_fiber_mod5 = self._high_fiber_mod5
        if high_fiber_mod5 is None:
            high_fiber_mod5 = self._compute_high_fiber_mod5(self.source, self.consumed)
            object.__setattr__(self, "_high_fiber_mod5", high_fiber_mod5)
        high = low + 32 * (((high_fiber_mod5 - low) * 3) % 5)
        return (self.origin % modulus + (self.gain % modulus) * high) % modulus

    def above_cycle(self) -> bool:
        # A high fiber at least four excludes normalized cycle states 1/2.
        if self.source.bit_length() > self.consumed + 2:
            return True
        # Here the remaining high fiber has at most two bits; this is a
        # bounded cycle probe rather than a full source-lift multiplication.
        return self.origin + self.gain * (self.source >> self.consumed) > 2


@dataclass(frozen=True, slots=True)
class D8TransitionAdmission:
    """Endpoint demand and cycle admission for one accepted D8 transition."""

    endpoint: int | None
    survives: bool


def admit_d8_transition(
    source: int,
    advanced: D8CylinderFrame | None,
    *,
    target_origin: int,
    odd_symbols: int,
    retain_joint_action: bool,
    materialize_frame: bool,
    ledger: ResourceLedger,
) -> D8TransitionAdmission:
    """Resolve only the endpoint form required by the active consumer."""
    if retain_joint_action:
        if advanced is None:
            raise ValueError("joint D8 admission needs its receiving cylinder frame")
        endpoint = None
        survives = advanced.above_cycle()
    else:
        if materialize_frame:
            if advanced is None:
                raise ValueError("D8 frame materialization needs its receiving frame")
            endpoint = advanced.materialize()
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_FRAME_MATERIALIZATIONS
            )
        else:
            endpoint = target_origin + 3**odd_symbols * (source >> 8)
        ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_ENDPOINT_EVALUATIONS)
        survives = endpoint > 2
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
        source.bit_length()
        + (endpoint.bit_length() if endpoint is not None else 0)
        + 26,
    )
    return D8TransitionAdmission(endpoint, survives)


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


def d8_width_row(residue: int) -> D8WidthRow:
    """Build finite affine prefixes on demand for a real width consumer."""
    if type(residue) is not int or not 0 <= residue < 256:
        raise ValueError("D8 source residue must be an eight-bit integer")
    current, multiplier, offset, odd_mask = residue + 256, 1, 0, 0
    prefixes: list[D8Prefix] = [(multiplier, offset)]
    for step in range(8):
        if current & 1:
            odd_mask |= 1 << step
            current = (3 * current + 1) >> 1
            multiplier, offset = 3 * multiplier, 3 * offset + (1 << step)
        else:
            current >>= 1
        prefixes.append((multiplier, offset))
    return tuple(prefixes), odd_mask


class D8TemporalTable:
    """At most 256 exact residue rows, shared only within one resource ledger."""

    NODES_PER_ROW = 3
    WIDTH_PREFIX_NODES_PER_ROW = 24

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
        self.width_owner = ledger.register(
            "collatz-physical-d8-width-prefix-table", "collatz_d8_width_prefix_table"
        )
        width_retained = ledger.registered_container(self.width_owner)
        if width_retained is None:
            self.width_prefixes: LedgerDict[int, D8WidthRow] = ledger.make_dict(
                self.width_owner,
                nodes_per_entry=self.WIDTH_PREFIX_NODES_PER_ROW,
                write_once=True,
            )
        elif type(width_retained) is LedgerDict:
            self.width_prefixes = cast(LedgerDict[int, D8WidthRow], width_retained)
        else:
            raise ValueError("D8 width table has another resource owner")

    @classmethod
    def for_ledger(cls, ledger: ResourceLedger) -> D8TemporalTable:
        return cls(ledger)

    @classmethod
    def release_if_unleased(
        cls, ledger: ResourceLedger, *, has_live_collatz_workspace: bool
    ) -> None:
        """Release shared D8 rows after the last live Collatz image owner.

        The ledger owns the stores, so wrapper objects are not leases. Live
        execution roots are the leases: an interleaved workspace keeps the
        shared rows available, while the last workspace returns their exact
        reservations. Empty registrations are harmless and remain reusable.
        """
        if type(ledger) is not ResourceLedger:
            raise TypeError("D8 lifecycle requires its resource ledger")
        if type(has_live_collatz_workspace) is not bool:
            raise TypeError("D8 lifecycle lease state must be Boolean")
        if has_live_collatz_workspace:
            return

        table_accounts = {
            account.name: account
            for account in ledger.inventory()
            if account.name
            in (
                "collatz-physical-d8-local-table",
                "collatz-physical-d8-width-prefix-table",
            )
        }
        for name, role, nodes_per_entry in (
            (
                "collatz-physical-d8-local-table",
                "collatz_d8_local_table",
                cls.NODES_PER_ROW,
            ),
            (
                "collatz-physical-d8-width-prefix-table",
                "collatz_d8_width_prefix_table",
                cls.WIDTH_PREFIX_NODES_PER_ROW,
            ),
        ):
            account = table_accounts.get(name)
            if account is None:
                continue
            if account.role != role:
                raise ValueError("D8 lifecycle found another resource owner")
            store = ledger.registered_container(account.owner)
            if store is None:
                continue
            if (
                type(store) is not LedgerDict
                or store.ledger is not ledger
                or store.owner != account.owner
                or store.nodes_per_entry != nodes_per_entry
                or not store.write_once
            ):
                raise ValueError("D8 lifecycle found another retained store")
            for key, value in tuple(store.items()):
                if not store._rollback_unpublished(key, value):
                    raise ValueError("D8 lifecycle lost a reserved row")

    def _select_row(self, source: int) -> D8Row:
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
            if (
                type(found) is not tuple
                or len(found) != 2
                or type(found[0]) is not int
                or type(found[1]) is not int
            ):
                raise ValueError("D8 row is malformed")
            self.ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_TABLE_HITS)
            return found
        self.ledger.reserve(self.owner, entries=1, nodes=self.NODES_PER_ROW)
        # Charge the admitted fixed discovery bound even if construction fails;
        # successful publication is a separate event, never a work proxy.
        self.ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_DISCOVERY_REQUESTS)
        self.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_DISCOVERY_SYMBOLS, 8
        )
        # The cache owner opts into this diagnostic lane at construction.
        # Record attempts here, including failures and abandoned root probes,
        # without creating a cache lane for callers that disabled shared reuse.
        if _collatz_keys.COLLATZ_HASHLIFE_PRIMITIVE_STEPS in self.ledger.counters:
            self.ledger.bump(_collatz_keys.COLLATZ_HASHLIFE_PRIMITIVE_STEPS, 8)
        try:
            found = d8_row(residue)
            self.rows[residue] = found
        except BaseException:
            self.ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_DISCOVERY_FAILURES
            )
            self.ledger.release(self.owner, entries=1, nodes=self.NODES_PER_ROW)
            raise
        self.ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_TABLE_PUBLICATIONS)
        return found

    def _select_width_row(self, source: int, endpoint_row: D8Row) -> D8WidthRow:
        residue = source & 255
        if (
            type(self.width_prefixes) is not LedgerDict
            or self.width_prefixes.ledger is not self.ledger
            or self.width_prefixes.owner != self.width_owner
            or not self.width_prefixes.write_once
            or self.width_prefixes.nodes_per_entry != self.WIDTH_PREFIX_NODES_PER_ROW
            or self.ledger.registered_container(self.width_owner)
            is not self.width_prefixes
        ):
            raise ValueError("D8 width table belongs to another resource owner")
        found = self.width_prefixes.get(residue)
        if found is not None:
            self._validate_width_row(found, endpoint_row, residue)
            self.ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_WIDTH_PREFIX_HITS
            )
            return found
        self.ledger.reserve(
            self.width_owner,
            entries=1,
            nodes=self.WIDTH_PREFIX_NODES_PER_ROW,
        )
        self.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_WIDTH_PREFIX_DISCOVERIES
        )
        self.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_WIDTH_PREFIX_SYMBOLS, 8
        )
        try:
            found = d8_width_row(residue)
            self._validate_width_row(found, endpoint_row, residue)
            self.width_prefixes[residue] = found
        except BaseException:
            self.ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_WIDTH_PREFIX_FAILURES
            )
            self.ledger.release(
                self.width_owner,
                entries=1,
                nodes=self.WIDTH_PREFIX_NODES_PER_ROW,
            )
            raise
        self.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_WIDTH_PREFIX_PUBLICATIONS
        )
        return found

    @staticmethod
    def _validate_width_row(row: D8WidthRow, endpoint_row: D8Row, residue: int) -> None:
        if type(row) is not tuple or len(row) != 2:
            raise ValueError("D8 width-prefix row differs from endpoint row")
        prefixes, odd_mask = row
        if (
            type(prefixes) is not tuple
            or len(prefixes) != 9
            or type(odd_mask) is not int
            or any(
                type(prefix) is not tuple
                or len(prefix) != 2
                or any(type(value) is not int for value in prefix)
                for prefix in prefixes
            )
        ):
            raise ValueError("D8 width-prefix row differs from endpoint row")
        final_gain, final_offset = prefixes[8]
        numerator = final_gain * residue + final_offset
        representative = residue + 256
        for step, (gain, offset) in enumerate(prefixes[:-1]):
            divisor = 1 << step
            prefix_numerator = gain * representative + offset
            if prefix_numerator % divisor or ((prefix_numerator // divisor) & 1) != (
                (odd_mask >> step) & 1
            ):
                raise ValueError("D8 width-prefix word differs from its affine rows")
        if (
            not 0 <= odd_mask < 256
            or odd_mask.bit_count() != endpoint_row[0]
            or prefixes[0] != (1, 0)
            or final_gain != 3 ** endpoint_row[0]
            or numerator % 256
            or numerator // 256 != endpoint_row[1]
        ):
            raise ValueError("D8 width-prefix row differs from endpoint row")

    def select(self, source: int) -> D8_VISIBLE_ROW:
        """Return the historical endpoint pair from the richer admitted row."""
        row = self._select_row(source)
        return row[0], row[1]

    def select_with_joint_action(
        self, source: int
    ) -> tuple[D8Row, DyadicTerminalFieldAction]:
        """Select the endpoint and joint action from one authenticated row."""
        selected = self._select_row(source)
        return selected, self._joint_action_for_row(source, selected)

    def _joint_action_for_row(
        self, source: int, selected: D8Row
    ) -> DyadicTerminalFieldAction:
        residue = source & 255
        prefixes, odd_mask = self._select_width_row(source, selected)
        return self._action_from_width_row(
            residue,
            selected,
            (prefixes, odd_mask),
        )

    def transition(
        self, frame: D8CylinderFrame
    ) -> tuple[D8CylinderFrame, int, int, int]:
        """Apply the exact byte transition without forming its full endpoint."""
        advanced, ones, residue, target_origin, _width, _action = self._transition(
            frame, with_width=False, with_joint=False
        )
        return advanced, ones, residue, target_origin

    def transition_with_width(
        self, frame: D8CylinderFrame
    ) -> tuple[D8CylinderFrame, int, int, int, CollatzTapeWidthSummary]:
        """Apply one D8 child and project its exact receiving-fiber width spine."""
        advanced, ones, residue, target_origin, width, _action = self._transition(
            frame, with_width=True, with_joint=False
        )
        if width is None:
            raise AssertionError("D8 width transition did not produce its spine")
        return advanced, ones, residue, target_origin, width

    def transition_with_joint_action(
        self, frame: D8CylinderFrame, *, with_width: bool = False
    ) -> tuple[
        D8CylinderFrame,
        int,
        int,
        int,
        CollatzTapeWidthSummary | None,
        DyadicTerminalFieldAction,
    ]:
        """Select one checked D8 row for endpoint, width and joint action."""
        advanced, ones, residue, target_origin, width, action = self._transition(
            frame, with_width=with_width, with_joint=True
        )
        if action is None:
            raise AssertionError("joint D8 transition did not produce its action")
        return advanced, ones, residue, target_origin, width, action

    def transition_with_parity_word(
        self,
        frame: D8CylinderFrame,
        *,
        with_width: bool = False,
        with_joint: bool = False,
    ) -> tuple[
        D8CylinderFrame,
        int,
        int,
        int,
        CollatzTapeWidthSummary | None,
        _D8ParityTransition,
    ]:
        """Issue the exact eight-bit word with the same admitted D8 action."""
        if type(frame) is not D8CylinderFrame:
            raise TypeError("D8 parity projection requires its exact cylinder frame")
        if type(with_width) is not bool or type(with_joint) is not bool:
            raise TypeError("D8 parity demand flags must be Boolean")
        local = frame.local_word()
        advanced, ones, residue, origin, width, action = self._transition(
            frame, with_width=with_width, with_joint=with_joint
        )
        row = self._select_row(residue + 256)
        prefixes, odd_mask = self._select_width_row(residue + 256, row)
        checked_action = (
            action
            if action is not None
            else DyadicTerminalFieldAction.from_prefixes(prefixes)
        )
        endpoint_local = advanced.local_word()
        if (
            (action is not None and checked_action != action)
            or odd_mask.bit_count() != ones
            or ((odd_mask & 1) != (local & 1))
        ):
            raise ValueError("D8 parity word differs from the admitted transition")
        from number_compiler.sequences.collatz.innovation_input_tape import (
            _D8ParityTransition,
        )

        self.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_WORD_VALIDATION_STEPS, 8
        )
        transition = _D8ParityTransition._issue(
            local, endpoint_local, odd_mask, checked_action, frame, advanced
        )
        return advanced, ones, residue, origin, width, transition

    def _width_summary_for_transition(
        self,
        frame: D8CylinderFrame,
        advanced: D8CylinderFrame,
        ones: int,
        source_width: int,
    ) -> CollatzTapeWidthSummary:
        """Project an already accepted transition without repeating its endpoint work."""
        if type(frame) is not D8CylinderFrame or type(advanced) is not D8CylinderFrame:
            raise TypeError("D8 width projection requires exact cylinder frames")
        if (
            type(ones) is not int
            or not 0 <= ones <= 8
            or type(source_width) is not int
            or source_width <= 0
        ):
            raise ValueError("D8 width projection has an invalid odd count")
        local = frame.local_word()
        residue = local & 255
        row = self._select_row(residue + 256)
        multiplier = 3 ** row[0]
        expected = frame._after_eight(
            origin=row[1] + multiplier * (local >> 8),
            gain=multiplier * frame.gain,
        )
        if (
            row[0] != ones
            or advanced.source != expected.source
            or advanced.consumed != expected.consumed
            or advanced.origin != expected.origin
            or advanced.gain != expected.gain
        ):
            raise ValueError("D8 width projection is detached from its transition")
        return self._width_spine(
            frame,
            ones,
            self._select_width_row(local, row),
            source_width=source_width,
        )

    def _transition(
        self, frame: D8CylinderFrame, *, with_width: bool, with_joint: bool
    ) -> tuple[
        D8CylinderFrame,
        int,
        int,
        int,
        CollatzTapeWidthSummary | None,
        DyadicTerminalFieldAction | None,
    ]:
        if type(frame) is not D8CylinderFrame:
            raise TypeError("D8 transition requires its exact cylinder frame")
        local = frame.local_word()
        residue = local & 255
        row = self._select_row(residue + 256)
        ones, target_origin = row
        multiplier = 3**ones
        result = frame._after_eight(
            origin=target_origin + multiplier * (local >> 8),
            gain=multiplier * frame.gain,
        )
        self.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_CYLINDER_TRANSITIONS
        )
        self.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_SOURCE_WINDOW_BITS, 8
        )
        self.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_FRAME_OPERAND_BITS,
            local.bit_length()
            + frame.gain.bit_length()
            + result.origin.bit_length()
            + result.gain.bit_length(),
        )
        # Include attempted/rejected transitions in the existing arithmetic
        # work account. Both finite D8 row coefficients have a 13-bit bound.
        self.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
            local.bit_length()
            + frame.gain.bit_length()
            + result.origin.bit_length()
            + result.gain.bit_length()
            + 26,
        )
        width_row = (
            self._select_width_row(local, row) if with_width or with_joint else None
        )
        width_summary = (
            self._width_spine(frame, ones, width_row)
            if with_width and width_row is not None
            else None
        )
        action = (
            self._action_from_width_row(residue, row, width_row)
            if with_joint and width_row is not None
            else None
        )
        return result, ones, residue, target_origin, width_summary, action

    def _action_from_width_row(
        self, residue: int, endpoint_row: D8Row, width_row: D8WidthRow
    ) -> DyadicTerminalFieldAction:
        prefixes, odd_mask = width_row
        action = DyadicTerminalFieldAction.from_prefixes(prefixes)
        ones, target_origin = endpoint_row
        if (
            action.steps != 8
            or action.source_residue != residue
            or action.endpoint(residue + 256) != target_origin + 3**ones
            or odd_mask.bit_count() != ones
        ):
            raise ValueError("D8 joint action differs from its endpoint publisher")
        self.ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_JOINT_ACTION_BUILDS)
        self.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_JOINT_ACTION_OPERAND_BITS,
            sum(max(1, value.bit_length()) for prefix in prefixes for value in prefix),
        )
        return action

    def _width_spine(
        self,
        frame: D8CylinderFrame,
        ones: int,
        width_row: D8WidthRow,
        *,
        source_width: int | None = None,
    ) -> CollatzTapeWidthSummary:
        local = frame.local_word()
        width_work_bits = (
            8
            * (
                frame.source.bit_length()
                + frame.gain.bit_length()
                + local.bit_length()
                + 64
            )
            + 512
        )
        self.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_WIDTH_OPERAND_BITS,
            width_work_bits,
        )
        nodes = 16 + (width_work_bits + 63) // 64
        # Scratch is reserved on the owner of the width table so inventory
        # observes both the retained prefix rows and the temporary workspace.
        with self.ledger.reservation(self.width_owner, nodes=nodes):
            return self._width_spine_reserved(
                frame, ones, width_row, local, source_width=source_width
            )

    def _width_spine_reserved(
        self,
        frame: D8CylinderFrame,
        ones: int,
        width_row: D8WidthRow,
        local: int,
        *,
        source_width: int | None,
    ) -> CollatzTapeWidthSummary:
        prefixes, odd_mask = width_row
        if (
            len(prefixes) != 9
            or not 0 <= odd_mask < 256
            or odd_mask.bit_count() != ones
        ):
            raise ValueError("D8 width spine is malformed")
        shift = frame.consumed + 8
        widths = []
        if source_width is None:
            divisor = 1 << 0
            numerator = prefixes[0][0] * local + prefixes[0][1]
            coefficient = prefixes[0][0] * frame.gain * (1 << 8)
            widths.append(
                nonnegative_affine_width(
                    frame.source, shift, coefficient, numerator // divisor, self.ledger
                )
            )
        else:
            if type(source_width) is not int or source_width <= 0:
                raise ValueError("D8 width source must be a positive exact width")
            widths.append(source_width)
        for step, (numerator_gain, numerator_offset) in enumerate(
            prefixes[1:], start=1
        ):
            divisor = 1 << step
            numerator = numerator_gain * local + numerator_offset
            if numerator < 0 or numerator % divisor:
                raise ArithmeticError("D8 prefix does not preserve integrality")
            coefficient = numerator_gain * frame.gain * (1 << (8 - step))
            offset = numerator // divisor
            widths.append(
                nonnegative_affine_width(
                    frame.source, shift, coefficient, offset, self.ledger
                )
            )
        result = BlankLedger()
        for step in range(8):
            before_width = widths[step]
            after_width = widths[step + 1]
            if (odd_mask >> step) & 1:
                # For odd x, 3*x+1 is even, so bit_length(3*x+1)
                # equals bit_length((3*x+1)//2)+1 exactly.
                raw_width = after_width + 1
                raw = BlankLedger(
                    raw_width - before_width,
                    min(0, raw_width - before_width),
                    max(0, raw_width - before_width),
                )
                result = compose_width_ledger(self.ledger, result, raw)
                normalized = BlankLedger(
                    after_width - raw_width,
                    min(0, after_width - raw_width),
                    max(0, after_width - raw_width),
                )
                result = compose_width_ledger(self.ledger, result, normalized)
            else:
                normalized = BlankLedger(
                    after_width - before_width,
                    min(0, after_width - before_width),
                    max(0, after_width - before_width),
                )
                result = compose_width_ledger(self.ledger, result, normalized)
        self.ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_WIDTH_PREFIX_STEPS, 8
        )
        return CollatzTapeWidthSummary(
            widths[0],
            widths[8],
            8 + ones,
            8,
            ones,
            result,
        )
