"""Certified radix re-encodings of preissued original binary inputs only.

This API receives no replacement digits, callbacks, or future program. It does
not open a tree-construction scope. Every mutable conversion cell represents an
original-input prefix, and every arithmetic intermediate fits one 64-bit limb.
"""

from __future__ import annotations

from collections.abc import MutableMapping
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import projection as _projection_keys


@dataclass(slots=True)
class _OriginalAffineWorkspaceInventory:
    """Live logical slots used while one immutable summary is compiled."""

    entries: int = 0
    nodes: int = 0

    def __len__(self) -> int:
        return self.entries


@dataclass(frozen=True, slots=True)
class OriginalRadixKey:
    construction: OriginalSourceConstruction
    radix: int
    binary_start: int = 0


@dataclass(frozen=True, slots=True)
class OriginalRadixSource:
    construction: OriginalSourceConstruction
    radix: int
    digits: tuple[int, ...]
    binary_start: int = 0


@dataclass(frozen=True, slots=True)
class OriginalShiftTransfer:
    """Bounded affine carry law for one original-source interval."""

    modulus: int
    multiplier: int
    offset: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (self.modulus, self.multiplier, self.offset)
        ):
            raise TypeError("original shift transfer requires exact integers")
        if not 1 <= self.modulus <= 1 << 62:
            raise ValueError("original shift transfer has an invalid modulus")
        if (
            not 0 <= self.multiplier < self.modulus
            or not 0 <= self.offset < self.modulus
        ):
            raise ValueError("original shift transfer must be reduced")


@dataclass(frozen=True, slots=True)
class OriginalThreeCarryAction:
    """One canonical endomorphism of the three affine carry states."""

    outputs: tuple[int, int, int]

    def __post_init__(self) -> None:
        if type(self.outputs) is not tuple or len(self.outputs) != 3:
            raise TypeError("affine carry action requires three outputs")
        if any(type(value) is not int or not 0 <= value < 3 for value in self.outputs):
            raise ValueError("affine carry action leaves its three-state port")


@dataclass(frozen=True, slots=True)
class OriginalAffineSummaryKey:
    source: OriginalRadixKey
    shift: int

    def __post_init__(self) -> None:
        if type(self.source) is not OriginalRadixKey:
            raise TypeError("affine summary requires an original source key")
        if type(self.shift) is not int or not 0 <= self.shift <= 62:
            raise ValueError("affine summary shift requires 0..62 bits")


@dataclass(frozen=True, slots=True)
class OriginalAffineSummary:
    """Canonical dyadic source summaries; no shifted or affine digits are stored."""

    width: int
    size: int
    shift_tree: tuple[int, ...]
    carry_tree: tuple[int, ...]

    def __post_init__(self) -> None:
        if any(type(value) is not int for value in (self.width, self.size)):
            raise TypeError("affine summary geometry requires exact integers")
        if self.width < 1 or self.size < 1 or self.size & (self.size - 1):
            raise ValueError("affine summary has invalid dyadic geometry")
        if (
            type(self.shift_tree) is not tuple
            or type(self.carry_tree) is not tuple
            or len(self.shift_tree) != 2 * self.size
            or len(self.carry_tree) != 2 * self.size
            or any(type(value) is not int or value < 0 for value in self.shift_tree)
            or any(type(value) is not int or value < 0 for value in self.carry_tree)
        ):
            raise ValueError("affine summary has malformed canonical node references")


class OriginalRadixArena:
    """Immutable original-source encodings charged to the query's shared ledger."""

    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        self.owner = ledger.register(
            f"original-radix-{len(ledger.inventory())}", "exact_source"
        )
        self.sources: MutableMapping[OriginalRadixKey, OriginalRadixSource] = (
            ledger.make_dict(self.owner)
        )
        prefix = f"original-radix-{len(ledger.inventory())}"
        self._shift_owner = ledger.register(prefix + "-shift-actions", "source_summary")
        self._shift_key_owner = ledger.register(
            prefix + "-shift-action-ids", "source_summary_interner"
        )
        self._carry_owner = ledger.register(prefix + "-carry-actions", "source_summary")
        self._carry_key_owner = ledger.register(
            prefix + "-carry-action-ids", "source_summary_interner"
        )
        self._summary_owner = ledger.register(
            prefix + "-affine-summaries", "source_summary"
        )
        self._workspace_owner = ledger.register(
            prefix + "-affine-workspace", "source_summary_workspace"
        )
        self._workspace = _OriginalAffineWorkspaceInventory()
        self._shift_nodes: MutableMapping[int, OriginalShiftTransfer] = (
            ledger.make_dict(self._shift_owner)
        )
        self._shift_keys: MutableMapping[OriginalShiftTransfer, int] = ledger.make_dict(
            self._shift_key_owner
        )
        self._carry_nodes: MutableMapping[int, OriginalThreeCarryAction] = (
            ledger.make_dict(self._carry_owner)
        )
        self._carry_keys: MutableMapping[OriginalThreeCarryAction, int] = (
            ledger.make_dict(self._carry_key_owner)
        )
        self._affine_summaries: MutableMapping[
            OriginalAffineSummaryKey, OriginalAffineSummary
        ] = ledger.make_dict(self._summary_owner)
        self._next_shift = 0
        self._next_carry = 0
        ledger.register_container(
            self.owner,
            self.sources,
            node_count=lambda: sum(
                1 + len(record.digits) for record in self.sources.values()
            ),
            payloads=lambda: self.sources.items(),
        )
        ledger.register_container(
            self._shift_owner,
            self._shift_nodes,
            node_count=lambda: len(self._shift_nodes),
            payloads=self._shift_nodes.items,
        )
        ledger.register_container(
            self._carry_owner,
            self._carry_nodes,
            node_count=lambda: len(self._carry_nodes),
            payloads=self._carry_nodes.items,
        )
        ledger.register_container(
            self._shift_key_owner,
            self._shift_keys,
            payloads=self._shift_keys.items,
        )
        ledger.register_container(
            self._carry_key_owner,
            self._carry_keys,
            payloads=self._carry_keys.items,
        )
        ledger.register_container(
            self._summary_owner,
            self._affine_summaries,
            node_count=lambda: sum(
                1 + len(summary.shift_tree) + len(summary.carry_tree)
                for summary in self._affine_summaries.values()
            ),
            payloads=self._affine_summaries.items,
        )
        ledger.register_container(
            self._workspace_owner,
            self._workspace,
            node_count=lambda: self._workspace.nodes,
            payloads=lambda: (),
        )
        ledger.register_execution_root(self)

    @staticmethod
    def _validate(
        construction: OriginalSourceConstruction, radix: int, binary_start: int = 0
    ) -> ExactSource:
        if type(construction) is not OriginalSourceConstruction:
            raise TypeError(
                "original radix encoding requires preissued source authority"
            )
        source = construction.validate_source()
        if (
            type(radix) is not int
            or not 2 <= radix <= 1 << 63
            or source.base != 2
            or not source.digits
            or any(bit not in (0, 1) for bit in source.digits)
        ):
            raise ValueError(
                "original radix encoding requires binary input and a bounded target radix"
            )
        if type(binary_start) is not int or binary_start != 0:
            raise ValueError(
                "retained original radix encoding requires source coordinate zero"
            )
        return source

    def encode(
        self,
        construction: OriginalSourceConstruction,
        radix: int,
        *,
        binary_start: int = 0,
    ) -> OriginalRadixSource:
        source = self._validate(construction, radix, binary_start)
        key = OriginalRadixKey(construction, radix, binary_start)
        existing = self.sources.get(key)
        if existing is not None:
            self.ledger.bump(_projection_keys.ORIGINAL_RADIX_ENCODING_HITS)
            return existing
        # A base>=2 encoding has no more digits than its binary input. Reserve
        # before work; release the conservative source-cell allowance afterward.
        allowance = len(source.digits) + 1
        self.ledger.reserve(self.owner, entries=1, nodes=allowance)
        try:
            digits = [0]
            # Only the complete original input may become a retained encoding.
            for position in range(len(source.digits) - 1, -1, -1):
                carry = source.digits[position]
                for index, digit in enumerate(digits):
                    total = self.ledger.observe_arithmetic(2 * digit + carry)
                    carry, digits[index] = divmod(total, radix)
                    self.ledger.bump(_projection_keys.ORIGINAL_RADIX_LIMB_OPERATIONS)
                if carry:
                    digits.append(carry)
                self.ledger.bump(_projection_keys.ORIGINAL_RADIX_SOURCE_BIT_READS)
                self.ledger.bump(
                    _projection_keys.ORIGINAL_RADIX_WORKSPACE_LIMBS_PEAK,
                    max(
                        0,
                        len(digits)
                        - self.ledger.counters.get(
                            _projection_keys.ORIGINAL_RADIX_WORKSPACE_LIMBS_PEAK, 0
                        ),
                    ),
                )
            result = OriginalRadixSource(
                construction, radix, tuple(digits), binary_start
            )
            self.sources[key] = result
        except BaseException:
            self.ledger.release(self.owner, entries=1, nodes=allowance)
            raise
        self.ledger.release(self.owner, nodes=allowance - len(result.digits) - 1)
        return result

    def _owned(self, source: OriginalRadixSource) -> None:
        if type(source) is not OriginalRadixSource:
            raise ValueError("original radix point requires an owned encoding")
        self._validate(source.construction, source.radix, source.binary_start)
        if (
            self.sources.get(
                OriginalRadixKey(source.construction, source.radix, source.binary_start)
            )
            is not source
        ):
            raise ValueError("original radix encoding belongs to another arena")

    def point(self, source: OriginalRadixSource, index: int) -> int:
        self._owned(source)
        if type(index) is not int:
            raise ValueError("original radix point requires an integer coordinate")
        if not 0 <= index < len(source.digits):
            raise IndexError(index)
        self.ledger.bump(_projection_keys.ORIGINAL_RADIX_POINT_QUERIES)
        return source.digits[index]

    def bounded_shifted_point(
        self,
        construction: OriginalSourceConstruction,
        radix: int,
        shift: int,
        index: int,
    ) -> int | None:
        """Read one original-source digit when its modulus fits one limb.

        The observation keeps only ``source mod radix**(index+1)``.  It neither
        constructs nor retains the complete radix encoding.  ``None`` means
        the requested modulus exceeds the bounded arithmetic interface.
        """
        source = self._validate(construction, radix)
        if type(shift) is not int or not 0 <= shift < len(source.digits):
            raise ValueError("bounded original shift exceeds the source")
        if type(index) is not int or index < 0:
            raise ValueError("bounded original point requires a nonnegative coordinate")
        lower, modulus = 1, 1
        for power in range(index + 1):
            if modulus > ((1 << 64) - 1) // radix:
                return None
            modulus = self.ledger.observe_arithmetic(modulus * radix)
            if power < index:
                lower = modulus
        highest = next(
            (
                position
                for position in range(len(source.digits) - 1, shift - 1, -1)
                if source.digits[position]
            ),
            None,
        )
        if highest is None:
            if index:
                raise IndexError(index)
        else:
            binary_width = highest - shift + 1
            if binary_width < lower.bit_length():
                raise IndexError(index)
            if binary_width == lower.bit_length():
                exact = 0
                for position in range(highest, shift - 1, -1):
                    exact = self.ledger.observe_arithmetic(
                        (exact << 1) | source.digits[position]
                    )
                if exact < lower:
                    raise IndexError(index)
        residue = 0
        midpoint = (modulus + 1) >> 1
        for position in range(len(source.digits) - 1, shift - 1, -1):
            # Compute (2*r + bit) mod modulus without forming a 65-bit
            # temporary when modulus itself occupies the full machine limb.
            if residue >= midpoint:
                residue = self.ledger.observe_arithmetic(
                    2 * (residue - midpoint) + (modulus & 1),
                )
            else:
                residue = self.ledger.observe_arithmetic(residue << 1)
            residue += source.digits[position]
            if residue >= modulus:
                residue -= modulus
            residue = self.ledger.observe_arithmetic(residue)
            self.ledger.bump(_projection_keys.ORIGINAL_RADIX_BOUNDED_SOURCE_BIT_READS)
        self.ledger.bump(_projection_keys.ORIGINAL_RADIX_BOUNDED_POINT_QUERIES)
        return residue // lower

    def _mod_multiply(self, left: int, right: int, modulus: int) -> int:
        """Multiply two at-most-62-bit residues without a wide product."""
        result = 0
        while right:
            if right & 1:
                result = self.ledger.observe_arithmetic(result + left) % modulus
                self.ledger.bump(
                    _projection_keys.ORIGINAL_AFFINE_SUMMARY_LIMB_OPERATIONS
                )
            right >>= 1
            if right:
                left = self.ledger.observe_arithmetic(left + left) % modulus
                self.ledger.bump(
                    _projection_keys.ORIGINAL_AFFINE_SUMMARY_LIMB_OPERATIONS
                )
        return result

    def _compose_shift(
        self,
        before: OriginalShiftTransfer,
        after: OriginalShiftTransfer,
    ) -> OriginalShiftTransfer:
        if before.modulus != after.modulus:
            raise ValueError("shift summaries have different finite carry ports")
        modulus = before.modulus
        multiplier = self._mod_multiply(after.multiplier, before.multiplier, modulus)
        transported = self._mod_multiply(after.multiplier, before.offset, modulus)
        offset = self.ledger.observe_arithmetic(transported + after.offset) % modulus
        self.ledger.bump(_projection_keys.ORIGINAL_AFFINE_SHIFT_COMPOSITIONS)
        return OriginalShiftTransfer(modulus, multiplier, offset)

    @staticmethod
    def _compose_carry(
        before: OriginalThreeCarryAction,
        after: OriginalThreeCarryAction,
    ) -> OriginalThreeCarryAction:
        return OriginalThreeCarryAction(
            (
                after.outputs[before.outputs[0]],
                after.outputs[before.outputs[1]],
                after.outputs[before.outputs[2]],
            )
        )

    def _triple_digit(self, digit: int, carry: int, radix: int) -> tuple[int, int]:
        """Return one 3*x+carry digit while observing only bounded limbs."""
        self.ledger.bump(
            _projection_keys.ORIGINAL_AFFINE_SUMMARY_TRANSITION_EVALUATIONS
        )
        upper, doubled = divmod(self.ledger.observe_arithmetic(2 * digit), radix)
        extra, partial = divmod(self.ledger.observe_arithmetic(doubled + digit), radix)
        carry_extra, output = divmod(
            self.ledger.observe_arithmetic(partial + carry), radix
        )
        return self.ledger.observe_arithmetic(upper + extra + carry_extra), output

    def _build_affine_summary_nodes(
        self,
        source: OriginalRadixSource,
        shift: int,
        size: int,
    ) -> tuple[
        int,
        list[OriginalShiftTransfer],
        list[OriginalThreeCarryAction],
    ]:
        modulus = 1 << shift
        shift_identity = OriginalShiftTransfer(modulus, 1 % modulus, 0)
        carry_identity = OriginalThreeCarryAction((0, 1, 2))
        shift_nodes = [shift_identity] * (2 * size)
        carry_nodes = [carry_identity] * (2 * size)
        division_carry = 0
        width = 1
        active = False
        for position in range(len(source.digits) - 1, -1, -1):
            digit = source.digits[position]
            quotient, division_carry = self._divide_cell(
                division_carry, source.radix, digit, shift
            )
            self.ledger.bump(_projection_keys.ORIGINAL_AFFINE_SUMMARY_DIVISION_CELLS)
            if quotient and not active:
                width, active = position + 1, True
            shift_nodes[size + position] = OriginalShiftTransfer(
                modulus,
                source.radix % modulus,
                digit % modulus,
            )
            carry_nodes[size + position] = OriginalThreeCarryAction(
                (
                    self._triple_digit(quotient, 0, source.radix)[0],
                    self._triple_digit(quotient, 1, source.radix)[0],
                    self._triple_digit(quotient, 2, source.radix)[0],
                )
            )
            self.ledger.bump(_projection_keys.ORIGINAL_AFFINE_SUMMARY_SOURCE_CELLS)
            self.ledger.bump(_projection_keys.RADIX_ORIGINAL_AFFINE_CARRY_CELLS)
        for node in range(size - 1, 0, -1):
            low, high = 2 * node, 2 * node + 1
            shift_nodes[node] = self._compose_shift(shift_nodes[high], shift_nodes[low])
            carry_nodes[node] = self._compose_carry(carry_nodes[low], carry_nodes[high])
            self.ledger.bump(_projection_keys.ORIGINAL_AFFINE_SUMMARY_PARENT_CELLS)
        return width, shift_nodes, carry_nodes

    def _affine_summary(
        self, source: OriginalRadixSource, shift: int
    ) -> OriginalAffineSummary:
        """Build one source-bound dyadic summary with no derived digit tape."""
        self._owned(source)
        if type(shift) is not int or not 0 <= shift <= 62:
            raise ValueError("original affine shift requires 0..62 bits")
        source_key = next(key for key, value in self.sources.items() if value is source)
        key = OriginalAffineSummaryKey(source_key, shift)
        self.ledger.bump(_projection_keys.ORIGINAL_AFFINE_SUMMARY_REQUESTS)
        found = self._affine_summaries.get(key)
        if found is not None:
            self.ledger.bump(_projection_keys.ORIGINAL_AFFINE_SUMMARY_HITS)
            return found
        count = len(source.digits)
        size = 1
        while size < count:
            size <<= 1
        summary_reservation = (self._summary_owner, 1, 1 + 4 * size)
        # Reserve the complete construction envelope before allocating the
        # trees, uniqueness sets, or action staging lists.  At most every tree
        # slot denotes a distinct action.  The workspace allowance also covers
        # the list/set references and the result tuples while they overlap.
        workspace_reservation = (self._workspace_owner, 4 * size, 12 * size)
        action_allowances = (
            (self._shift_owner, 2 * size, 2 * size),
            (self._shift_key_owner, 2 * size, 0),
            (self._carry_owner, 2 * size, 2 * size),
            (self._carry_key_owner, 2 * size, 0),
        )
        reservations = (summary_reservation, workspace_reservation, *action_allowances)
        try:
            self.ledger.reserve_many(reservations)
            self._workspace.entries = workspace_reservation[1]
            self._workspace.nodes = workspace_reservation[2]
            self.ledger.bump(
                _projection_keys.ORIGINAL_AFFINE_SUMMARY_WORKSPACE_SLOTS_PEAK,
                max(
                    0,
                    self._workspace.entries
                    + self._workspace.nodes
                    - self.ledger.counters.get(
                        _projection_keys.ORIGINAL_AFFINE_SUMMARY_WORKSPACE_SLOTS_PEAK,
                        0,
                    ),
                ),
            )
        except BaseException:
            self.ledger.bump(_projection_keys.ORIGINAL_AFFINE_SUMMARY_FAILURES)
            raise
        try:
            width, shift_nodes, carry_nodes = self._build_affine_summary_nodes(
                source, shift, size
            )
            modulus = 1 << shift
            shift_identity = OriginalShiftTransfer(modulus, 1 % modulus, 0)
            carry_identity = OriginalThreeCarryAction((0, 1, 2))
            unique_shift = tuple(dict.fromkeys(shift_nodes))
            unique_carry = tuple(dict.fromkeys(carry_nodes))
            new_shift = tuple(
                shift_action
                for shift_action in unique_shift
                if shift_action not in self._shift_keys
            )
            new_carry = tuple(
                carry_action
                for carry_action in unique_carry
                if carry_action not in self._carry_keys
            )
        except BaseException:
            self._workspace.entries = self._workspace.nodes = 0
            for owner, entries, nodes in reversed(reservations):
                self.ledger.release(owner, entries=entries, nodes=nodes)
            self.ledger.bump(_projection_keys.ORIGINAL_AFFINE_SUMMARY_FAILURES)
            raise
        shift_ids: list[int] = []
        carry_ids: list[int] = []
        try:
            for shift_action in new_shift:
                local_id = self._next_shift
                self._next_shift += 1
                self._shift_nodes[local_id] = shift_action
                self._shift_keys[shift_action] = local_id
                shift_ids.append(local_id)
            for carry_action in new_carry:
                local_id = self._next_carry
                self._next_carry += 1
                self._carry_nodes[local_id] = carry_action
                self._carry_keys[carry_action] = local_id
                carry_ids.append(local_id)
            result = OriginalAffineSummary(
                width,
                size,
                tuple(
                    self._shift_keys[shift_identity]
                    if index == 0
                    else self._shift_keys[item]
                    for index, item in enumerate(shift_nodes)
                ),
                tuple(
                    self._carry_keys[carry_identity]
                    if index == 0
                    else self._carry_keys[item]
                    for index, item in enumerate(carry_nodes)
                ),
            )
            self._affine_summaries[key] = result
        except BaseException:
            for local_id in shift_ids:
                shift_action = self._shift_nodes.pop(local_id)
                self._shift_keys.pop(shift_action, None)
            for local_id in carry_ids:
                carry_action = self._carry_nodes.pop(local_id)
                self._carry_keys.pop(carry_action, None)
            for owner, entries, nodes in reversed(reservations):
                self.ledger.release(owner, entries=entries, nodes=nodes)
            self._workspace.entries = self._workspace.nodes = 0
            self.ledger.bump(_projection_keys.ORIGINAL_AFFINE_SUMMARY_FAILURES)
            raise
        self.ledger.release(
            self._shift_owner,
            entries=2 * size - len(new_shift),
            nodes=2 * size - len(new_shift),
        )
        self.ledger.release(self._shift_key_owner, entries=2 * size - len(new_shift))
        self.ledger.release(
            self._carry_owner,
            entries=2 * size - len(new_carry),
            nodes=2 * size - len(new_carry),
        )
        self.ledger.release(self._carry_key_owner, entries=2 * size - len(new_carry))
        self.ledger.release(
            self._workspace_owner,
            entries=workspace_reservation[1],
            nodes=workspace_reservation[2],
        )
        self._workspace.entries = self._workspace.nodes = 0
        self.ledger.bump(_projection_keys.ORIGINAL_AFFINE_SUMMARY_PUBLICATIONS)
        return result

    def affine_shifted_point(
        self,
        source: OriginalRadixSource,
        shift: int,
        index: int,
        incoming: int,
    ) -> int:
        """Observe 3*(source/2**shift)+incoming through dyadic summaries."""
        if type(index) is not int or index < 0:
            raise ValueError("original affine point requires a nonnegative coordinate")
        if type(incoming) is not int or not 0 <= incoming < 3:
            raise ValueError("original affine carry lies outside its three-state port")
        summary = self._affine_summary(source, shift)
        if index > summary.width + 1:
            raise IndexError(index)
        self.ledger.bump(_projection_keys.RADIX_ORIGINAL_AFFINE_DIGIT_QUERIES)
        carry = incoming
        # [0,index) has a left-to-right dyadic cover given by the set bits of
        # its length.  Visit it directly, without allocating a per-query list.
        position = 0
        remaining = min(index, summary.width)
        while remaining:
            block = 1 << (remaining.bit_length() - 1)
            node = summary.carry_tree[(summary.size + position) // block]
            carry = self._carry_nodes[node].outputs[carry]
            self.ledger.bump(_projection_keys.ORIGINAL_AFFINE_PREFIX_SUMMARY_VISITS)
            position += block
            remaining -= block
        if index >= summary.width:
            extra = carry if index == summary.width else carry // source.radix
            if not extra:
                raise IndexError(index)
            return extra % source.radix
        division_carry = 0
        # Visit [index+1,width) from high to low.  Choosing the largest aligned
        # block ending at ``stop`` gives the reverse dyadic cover directly.
        start = index + 1
        stop = len(source.digits)
        while stop > start:
            block = stop & -stop
            while block > stop - start:
                block >>= 1
            node = summary.shift_tree[(summary.size + stop - block) // block]
            transfer = self._shift_nodes[node]
            product = self._mod_multiply(
                transfer.multiplier, division_carry, transfer.modulus
            )
            division_carry = (
                self.ledger.observe_arithmetic(product + transfer.offset)
                % transfer.modulus
            )
            self.ledger.bump(_projection_keys.ORIGINAL_AFFINE_SHIFT_SUMMARY_VISITS)
            stop -= block
        quotient, _ = self._divide_cell(
            division_carry, source.radix, source.digits[index], shift
        )
        return self._triple_digit(quotient, carry, source.radix)[1]

    def _limb(self, value: int) -> int:
        self.ledger.bump(_projection_keys.ORIGINAL_RADIX_SHIFT_LIMB_OPERATIONS)
        return self.ledger.observe_arithmetic(value)

    def _divide_cell(
        self, carry: int, radix: int, digit: int, shift: int
    ) -> tuple[int, int]:
        """Return quotient digit/remainder of c*b+d without a wide integer.

        c<2**shift, b<=2**63, shift<=62 imply quotient<b. Four 32-bit
        limbs suffice; multiplication plus both incoming words is <=2**64-1.
        """
        if radix.bit_length() + shift <= 64:
            total = self._limb(self._limb(carry * radix) + digit)
            self.ledger.bump(_projection_keys.ORIGINAL_RADIX_SHIFT_SMALL_CELLS)
            return self._limb(total >> shift), self._limb(total & ((1 << shift) - 1))
        mask = (1 << 32) - 1
        left = (self._limb(carry & mask), self._limb(carry >> 32))
        right = (self._limb(radix & mask), self._limb(radix >> 32))
        limbs = [self._limb(digit & mask), self._limb(digit >> 32), 0, 0]
        self.ledger.bump(
            _projection_keys.ORIGINAL_RADIX_SHIFT_PRODUCT_BUFFER_LIMBS_PEAK,
            max(
                0,
                len(limbs)
                - self.ledger.counters.get(
                    _projection_keys.ORIGINAL_RADIX_SHIFT_PRODUCT_BUFFER_LIMBS_PEAK,
                    0,
                ),
            ),
        )
        self.ledger.bump(
            _projection_keys.ORIGINAL_RADIX_SHIFT_OPERAND_LIMBS_PEAK,
            max(
                0,
                len(left)
                + len(right)
                - self.ledger.counters.get(
                    _projection_keys.ORIGINAL_RADIX_SHIFT_OPERAND_LIMBS_PEAK, 0
                ),
            ),
        )
        for i, a in enumerate(left):
            incoming = 0
            for j, b in enumerate(right):
                product = self._limb(a * b)
                total = self._limb(self._limb(product + limbs[i + j]) + incoming)
                limbs[i + j], incoming = (
                    self._limb(total & mask),
                    self._limb(total >> 32),
                )
                self.ledger.bump(
                    _projection_keys.ORIGINAL_RADIX_SHIFT_WORD_MULTIPLICATIONS
                )
            limbs[i + 2] = self._limb(limbs[i + 2] + incoming)
        word, bit = divmod(shift, 32)
        # Extract two quotient words directly. Never assemble the 126-bit total.
        quotient_words = []
        for index in (word, word + 1):
            low = self._limb(limbs[index] >> bit)
            high = self._limb(limbs[index + 1] << (32 - bit)) if bit else 0
            quotient_words.append(self._limb(low | (high & mask)))
        quotient = self._limb(self._limb(quotient_words[1] << 32) | quotient_words[0])
        remainder = self._limb(limbs[0] & ((1 << min(shift, 32)) - 1))
        if shift > 32:
            upper = self._limb((limbs[1] & ((1 << (shift - 32)) - 1)) << 32)
            remainder = self._limb(remainder | upper)
        self.ledger.bump(
            _projection_keys.ORIGINAL_RADIX_SHIFT_QUOTIENT_BUFFER_LIMBS_PEAK,
            max(
                0,
                len(quotient_words)
                - self.ledger.counters.get(
                    _projection_keys.ORIGINAL_RADIX_SHIFT_QUOTIENT_BUFFER_LIMBS_PEAK,
                    0,
                ),
            ),
        )
        self.ledger.bump(
            _projection_keys.ORIGINAL_RADIX_SHIFT_LIVE_BUFFER_LIMBS_PEAK,
            max(
                0,
                len(left)
                + len(right)
                + len(limbs)
                + len(quotient_words)
                - self.ledger.counters.get(
                    _projection_keys.ORIGINAL_RADIX_SHIFT_LIVE_BUFFER_LIMBS_PEAK, 0
                ),
            ),
        )
        self.ledger.bump(_projection_keys.ORIGINAL_RADIX_SHIFT_WIDE_CELLS)
        return quotient, remainder

    def _shifted(
        self, source: OriginalRadixSource, shift: int, index: int | None
    ) -> int:
        self._owned(source)
        if type(shift) is not int or not 0 <= shift <= 62:
            raise ValueError("transient original shift requires 0..62 bits")
        if index is not None and (type(index) is not int or index < 0):
            raise ValueError("shifted point requires a nonnegative integer coordinate")
        if index is not None and index >= len(source.digits):
            raise IndexError(index)
        self.ledger.bump(
            "original_radix_shift_width_queries"
            if index is None
            else "original_radix_shift_point_queries"
        )
        if not shift:
            return len(source.digits) if index is None else self.point(source, index)
        carry, active = 0, False
        for position in range(len(source.digits) - 1, -1, -1):
            digit = self._limb(source.digits[position])
            self.ledger.bump(_projection_keys.ORIGINAL_RADIX_SHIFT_SOURCE_DIGIT_READS)
            quotient, carry = self._divide_cell(carry, source.radix, digit, shift)
            self.ledger.bump(_projection_keys.ORIGINAL_RADIX_SHIFT_DIVISION_CELLS)
            if quotient:
                active = True
                if index is None:
                    return position + 1
            if index is not None and position == index:
                if not active and index > 0:
                    raise IndexError(index)
                return quotient
        # The canonical zero encoding contains one zero digit.
        return 1

    def shifted_point(self, source: OriginalRadixSource, shift: int, index: int) -> int:
        """Observe one digit of original/2**shift; never retain shifted digits."""
        return self._shifted(source, shift, index)

    def shifted_width(self, source: OriginalRadixSource, shift: int) -> int:
        """Find the first nonzero quotient digit, retaining only a finite carry."""
        return self._shifted(source, shift, None)


__all__ = ["OriginalRadixArena", "OriginalRadixKey", "OriginalRadixSource"]
