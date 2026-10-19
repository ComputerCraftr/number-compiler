"""Bounded radix-4 source interfaces for Collatz parent observations.

The retained record is the complete three-carry transfer together with output
witnesses and the first mismatch from the 2-adic root ``...1111_4``.  Source
bindings are separate from semantic identities, so equal subtrees share one
interface.  Construction is iterative and never creates a future digit word.
"""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.iterative_queries import defer_binary_children
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.execution.field_images import (
    SourceBindingID,
    SourceCellArena,
    SourceCellID,
    SourceForestID,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
    PayloadAuditStoreBinding,
    register_payload_audit_contract,
)
from number_compiler.resources.stores import append_indexed_node


@dataclass(frozen=True, slots=True)
class CollatzCarryRow:
    exit_carry: int
    first_nonzero: int | None
    last_nonzero: int | None


@dataclass(frozen=True, slots=True)
class CollatzRadix4Range:
    length: int
    rows: tuple[CollatzCarryRow, CollatzCarryRow, CollatzCarryRow]
    first_root_mismatch: int | None
    mismatch_symbol: int | None

    def __post_init__(self) -> None:
        if type(self.length) is not int or self.length < 1:
            raise ValueError("Collatz range length must be positive")
        if type(self.rows) is not tuple or len(self.rows) != 3:
            raise ValueError("Collatz range requires all three carry rows")
        for row in self.rows:
            if type(row) is not CollatzCarryRow or not 0 <= row.exit_carry < 3:
                raise ValueError("invalid Collatz carry row")
            if (row.first_nonzero is None) != (row.last_nonzero is None):
                raise ValueError("Collatz carry witnesses disagree on emptiness")
            if row.first_nonzero is not None and not (
                row.last_nonzero is not None
                and 0 <= row.first_nonzero <= row.last_nonzero < self.length
            ):
                raise ValueError("Collatz carry witness lies outside the range")
        if (self.first_root_mismatch is None) != (self.mismatch_symbol is None):
            raise ValueError("Collatz root mismatch witnesses disagree")
        if self.first_root_mismatch is not None and not (
            0 <= self.first_root_mismatch < self.length
            and type(self.mismatch_symbol) is int
            and 0 <= self.mismatch_symbol < 4
            and self.mismatch_symbol != 1
        ):
            raise ValueError("invalid Collatz root mismatch")

    @staticmethod
    def atom(symbol: int) -> CollatzRadix4Range:
        if type(symbol) is not int or not 0 <= symbol < 4:
            raise ValueError("Collatz radix-4 atom is outside its alphabet")
        rows: list[CollatzCarryRow] = []
        for carry in range(3):
            value = 3 * symbol + carry
            emitted = value & 3
            rows.append(
                CollatzCarryRow(
                    value >> 2,
                    0 if emitted else None,
                    0 if emitted else None,
                )
            )
        mismatch = None if symbol == 1 else 0
        return CollatzRadix4Range(
            1,
            (rows[0], rows[1], rows[2]),
            mismatch,
            None if mismatch is None else symbol,
        )

    def then(self, high: CollatzRadix4Range) -> CollatzRadix4Range:
        if type(high) is not CollatzRadix4Range:
            raise TypeError("Collatz ranges compose with ranges")
        rows: list[CollatzCarryRow] = []
        for low_row in self.rows:
            high_row = high.rows[low_row.exit_carry]
            first = low_row.first_nonzero
            if first is None and high_row.first_nonzero is not None:
                first = self.length + high_row.first_nonzero
            last = low_row.last_nonzero
            if high_row.last_nonzero is not None:
                last = self.length + high_row.last_nonzero
            rows.append(CollatzCarryRow(high_row.exit_carry, first, last))
        mismatch: int | None
        mismatch_symbol: int | None
        if self.first_root_mismatch is not None:
            mismatch, mismatch_symbol = self.first_root_mismatch, self.mismatch_symbol
        elif high.first_root_mismatch is not None:
            mismatch = self.length + high.first_root_mismatch
            mismatch_symbol = high.mismatch_symbol
        else:
            mismatch = mismatch_symbol = None
        return CollatzRadix4Range(
            self.length + high.length,
            (rows[0], rows[1], rows[2]),
            mismatch,
            mismatch_symbol,
        )


@dataclass(frozen=True, slots=True)
class CollatzRadix4RangeID(ArenaHandle):
    """Scoped semantic ID for one bounded range effect."""


class CollatzRadix4RangeArena:
    """Canonical bottom-up source summaries with no coordinate payload cache."""

    _KIND = "collatz-radix4-range"

    def __init__(self, sources: SourceCellArena) -> None:
        self.sources = sources
        self.ledger: ResourceLedger = sources.ledger
        self.owner = ArenaToken("collatz-radix4-ranges")
        prefix = f"collatz-radix4-range-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(prefix + "-nodes", "finite_port")
        self._key_owner = self.ledger.register(prefix + "-keys", "transfer_interner")
        self._binding_owner = self.ledger.register(
            prefix + "-bindings", "spatial_binding"
        )
        self._nodes: MutableSequence[CollatzRadix4Range] = self.ledger.make_list(
            self._node_owner
        )
        self._keys: MutableMapping[CollatzRadix4Range, int] = self.ledger.make_dict(
            self._key_owner
        )
        self._bindings: OwnedMemo[SourceCellID, CollatzRadix4RangeID] = OwnedMemo(
            self.ledger,
            self._binding_owner,
            evictable=True,
        )
        self._audit_bindings = self._bindings.audit_snapshot().container
        self.ledger.register_container(
            self._node_owner,
            self._nodes,
            node_count=lambda: len(self._nodes),
            payloads=lambda: self._nodes,
        )
        self.ledger.register_container(
            self._key_owner, self._keys, payloads=self._keys.items
        )
        self.ledger.register_execution_root(self)

        self.register_payload_audit()

    def resolve(self, reference: CollatzRadix4RangeID) -> CollatzRadix4Range:
        if type(reference) is not CollatzRadix4RangeID:
            raise TypeError("expected a scoped Collatz range ID")
        reference.validate(self.owner, self._KIND, size=len(self._nodes))
        return self._nodes[reference.local_id]

    def _intern(self, value: CollatzRadix4Range) -> CollatzRadix4RangeID:
        found = self._keys.get(value)
        if found is not None:
            self.ledger.bump(_collatz_keys.COLLATZ_RANGE_SEMANTIC_ALIAS_HITS)
            return CollatzRadix4RangeID(self.owner, self._KIND, found)
        local = append_indexed_node(
            self.ledger,
            self._nodes,
            self._keys,
            self._node_owner,
            self._key_owner,
            value,
            value,
        )
        return CollatzRadix4RangeID(self.owner, self._KIND, local)

    def summarize(self, source: SourceCellID) -> CollatzRadix4RangeID:
        """Summarize an aligned binary subtree as radix-4 cells."""
        self.sources.resolve(source)
        found = self._bindings.get(source)
        if found is not None:
            self.resolve(found)
            self.ledger.bump(_collatz_keys.COLLATZ_RANGE_PARENT_HITS)
            return found
        blank = self.sources.alphabet()[1]
        pending: list[tuple[SourceCellID, bool]] = [(source, False)]
        built: dict[int, CollatzRadix4RangeID] = {}
        while pending:
            current, ready = pending.pop()
            cached = self._bindings.get(current)
            if cached is not None:
                built[current.local_id] = cached
                continue
            node = self.sources.resolve(current)
            if node.level > 1 and not ready:
                defer_binary_children(pending, current, self.sources.children)
                continue
            if node.level == 0:
                low_symbol = self.sources.symbol(current)
                symbol = 0 if low_symbol == blank else low_symbol
                result = self._intern(CollatzRadix4Range.atom(symbol))
            elif node.level == 1:
                low_cell, high_cell = self.sources.children(current)
                lo = self.sources.symbol(low_cell)
                hi = self.sources.symbol(high_cell)
                symbol = (0 if lo == blank else lo) + 2 * (0 if hi == blank else hi)
                result = self._intern(CollatzRadix4Range.atom(symbol))
            else:
                left, right = self.sources.children(current)
                result = self._intern(
                    self.resolve(built[left.local_id]).then(
                        self.resolve(built[right.local_id])
                    )
                )
            self._bindings[current] = result
            built[current.local_id] = result
            self.ledger.bump(_collatz_keys.COLLATZ_RANGE_PARENT_PUBLICATIONS)
        return built[source.local_id]

    def summarize_binding(
        self,
        source: SourceBindingID,
    ) -> CollatzRadix4RangeID:
        """Compose the canonical dyadic cover without a source-shaped key."""
        if type(source) is SourceCellID:
            return self.summarize(source)
        if type(source) is not SourceForestID:
            raise TypeError("Collatz range requires a scoped source binding")
        cells = self.sources.resolve_forest(source).cells
        result = self.summarize(cells[0])
        for cell in cells[1:]:
            result = self._intern(
                self.resolve(result).then(self.resolve(self.summarize(cell))),
            )
            self.ledger.bump(_collatz_keys.COLLATZ_RANGE_FOREST_COMPOSITIONS)
        return result

    def register_payload_audit(self) -> None:
        root = self

        if type(root) is not CollatzRadix4RangeArena:
            raise TypeError("Collatz range audit requires its exact arena")
        stores = (
            PayloadAuditStoreBinding(root._node_owner, "_nodes", "finite_port"),
            PayloadAuditStoreBinding(root._key_owner, "_keys", "transfer_interner"),
            PayloadAuditStoreBinding(
                root._binding_owner,
                "_audit_bindings",
                "spatial_binding",
            ),
        )
        register_payload_audit_contract(
            root.ledger, root, "collatz", stores, audit_collatz_range
        )

    def audit_payload(self, ledger: object, root: object) -> PayloadAuditContribution:
        """Validate exact radix-4 range nodes, interning, and source bindings."""
        if root is not self:
            raise TypeError("payload audit callback received another owner")
        from number_compiler.hashlife.execution.field_images import SourceCellID
        from number_compiler.resources.ledger import ResourceLedger

        if (
            type(ledger) is not ResourceLedger
            or type(root) is not CollatzRadix4RangeArena
        ):
            raise TypeError("Collatz range audit received a foreign owner")
        arena = root
        approved: list[PayloadAuditEntry] = []
        invalid: list[PayloadAuditEntry] = []

        def record(owner: int, value: object, valid: bool) -> None:
            entry = PayloadAuditEntry(owner, value)
            (approved if valid else invalid).append(entry)

        if arena.ledger is not ledger:
            invalid.append(PayloadAuditEntry(arena._node_owner, arena))
            return PayloadAuditContribution((), tuple(invalid))

        for index, value in enumerate(arena._nodes):
            try:
                if type(value) is not CollatzRadix4Range:
                    raise TypeError("invalid Collatz range node type")
                value.__post_init__()
                valid = arena._keys.get(value) == index
                reference = CollatzRadix4RangeID(arena.owner, arena._KIND, index)
                valid &= arena.resolve(reference) is value
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            record(arena._node_owner, value, valid)

        for value, index in arena._keys.items():
            valid = type(value) is CollatzRadix4Range and type(index) is int
            valid &= 0 <= index < len(arena._nodes)
            if valid:
                valid &= arena._nodes[index] == value
            record(arena._key_owner, value, valid)
            record(arena._key_owner, index, valid)

        for source, result in arena._bindings.items():
            try:
                valid = type(source) is SourceCellID
                arena.sources.resolve(source)
                valid &= type(result) is CollatzRadix4RangeID
                arena.resolve(result)
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            record(arena._binding_owner, source, valid)
            record(arena._binding_owner, result, valid)

        return PayloadAuditContribution(tuple(approved), tuple(invalid))


__all__ = [
    "CollatzCarryRow",
    "CollatzRadix4Range",
    "CollatzRadix4RangeArena",
    "CollatzRadix4RangeID",
]


def audit_collatz_range(ledger: object, root: object) -> PayloadAuditContribution:
    """Closure-free ledger entry point for its exact family owner."""
    if type(root) is not CollatzRadix4RangeArena:
        raise TypeError("Collatz payload audit received another owner")
    return root.audit_payload(ledger, root)
