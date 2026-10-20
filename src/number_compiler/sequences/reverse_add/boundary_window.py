"""Source-scoped finite-window observations for reverse/add and 2*reverse.

The window relation tracks exact leading and trailing digits while allowing
both carry values from the unknown interior. It certifies edge observations
only when every retained branch agrees; it never represents the complete
successor pair word or integer endpoint.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable, Iterator
from dataclasses import dataclass
from functools import partial
from typing import TYPE_CHECKING, Literal

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.owned_memo import OwnedMemoAuditSnapshot
from number_compiler.resources.payload_contracts import PayloadAuditStoreBinding
from number_compiler.sequences.reverse_add.boundary_window_store import (
    BoundaryOperation,
    BoundaryRelationRecord,
    BoundaryRelationStore,
    WindowRelationBudgetExceeded,
    WindowTile,
    _RelationKey,
    audit_reverse_boundary_window_owner,
)

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.source_workspace import (
        ReverseSourceImageWorkspace,
    )


@dataclass(frozen=True, slots=True)
class ReverseBoundaryWindowObservation:
    """Source/index-bound edge certificate; it never claims a full endpoint."""

    status: Literal["available", "unavailable"]
    seed: int
    steps: int
    target_width: int | None
    prefix: str
    suffix: str
    window_digits: int | None
    boundary_states: int
    relation_cache_hits: int
    relation_cache_misses: int
    relation_operations: int
    reason: str | None
    full_integer_powered: Literal[False] = False

    def __post_init__(self) -> None:
        require_integer(self.seed, "boundary source", 0)
        require_integer(self.steps, "boundary steps", 0)
        require_integer(self.boundary_states, "boundary state count", 0)
        require_integer(self.relation_cache_hits, "boundary cache hits", 0)
        require_integer(self.relation_cache_misses, "boundary cache misses", 0)
        require_integer(self.relation_operations, "boundary relation operations", 0)
        if self.status not in ("available", "unavailable"):
            raise ValueError("unknown boundary observation status")
        if self.full_integer_powered is not False:
            raise ValueError(
                "a boundary observation cannot claim full integer powering"
            )
        if self.status == "available":
            if (
                type(self.target_width) is not int
                or self.target_width < 1
                or type(self.window_digits) is not int
                or self.window_digits < 2
                or self.boundary_states < 1
                or self.reason is not None
            ):
                raise ValueError("available boundary observation is incomplete")
            if (
                type(self.prefix) is not str
                or type(self.suffix) is not str
                or len(self.prefix) > self.window_digits
                or len(self.suffix) > self.window_digits
                or not self.prefix.isdigit()
                or not self.suffix.isdigit()
            ):
                raise ValueError("available boundary digits are malformed")
        elif (
            self.target_width is not None
            or self.prefix != ""
            or self.suffix != ""
            or type(self.reason) is not str
            or not self.reason
        ):
            raise ValueError("unavailable boundary observation must explain refusal")


@dataclass(frozen=True, slots=True)
class BoundaryObservationCacheRecord:
    """Immutable result and mutation snapshot stored as one audited payload."""

    observation: ReverseBoundaryWindowObservation
    fields: tuple[object, ...]


class FiniteBoundaryWindow:
    """Exact finite relation on K leading/trailing digits.

    An exact source carry is used for the first transition. Every later step
    admits both possible inner carries, so no source-only carry becomes a
    future oracle. Relation powers are built by an explicit worklist.
    """

    def __init__(
        self,
        digits: int,
        *,
        operation: BoundaryOperation,
        relation_store: BoundaryRelationStore,
        max_states: int,
    ) -> None:
        self.digits = require_integer(digits, "window digits", 1)
        if self.digits > 64:
            raise ValueError("boundary windows are limited to 64 digits")
        if operation == "reverse-add":
            canonical_operation: BoundaryOperation = operation
        elif operation == "double-reverse":
            canonical_operation = operation
        else:
            raise ValueError("unsupported boundary operation")
        self.operation: BoundaryOperation = canonical_operation
        if type(relation_store) is not BoundaryRelationStore:
            raise TypeError("boundary relations require a bounded owned store")
        self.relation_store = relation_store
        self.max_states = require_integer(max_states, "boundary state limit", 1)
        self.modulus = 10**self.digits
        self.minimum_prefix = 10 ** (self.digits - 1)
        self.expanded_relations = 0
        self.composition_operations = 0
        self.transition_evaluations = 0
        self.cache_hits = 0
        self.cache_misses = 0
        self._call_operations = 0
        self._operation_limit = 0

    def reverse_block(self, word: int) -> int:
        if type(word) is not int or not 0 <= word < self.modulus:
            raise ValueError("word outside fixed-width boundary tile")
        result = 0
        for _ in range(self.digits):
            result = result * 10 + word % 10
            word //= 10
        return result

    def source_tile(self, source_digits_lsd: tuple[int, ...]) -> WindowTile:
        self._validate_source_digits(source_digits_lsd)
        return self.source_tile_from_validated_digits(source_digits_lsd)

    def _check_source_geometry(self, source_digits_lsd: tuple[int, ...]) -> None:
        if type(source_digits_lsd) is not tuple:
            raise TypeError("authenticated boundary digits must be an immutable tuple")
        if len(source_digits_lsd) < 2 * self.digits + 1:
            raise ValueError("source width must be at least 2K+1")

    def source_tile_from_validated_digits(
        self, source_digits_lsd: tuple[int, ...]
    ) -> WindowTile:
        """Extract edge windows from digits validated by the owning caller."""
        self._check_source_geometry(source_digits_lsd)
        prefix = 0
        for digit in reversed(source_digits_lsd[-self.digits :]):
            prefix = prefix * 10 + digit
        suffix = 0
        place = 1
        for digit in source_digits_lsd[: self.digits]:
            suffix += digit * place
            place *= 10
        if prefix < self.minimum_prefix:
            raise ValueError("source prefix does not occupy the fixed K-digit window")
        return WindowTile(prefix, suffix)

    def source_inner_carry(self, source_digits_lsd: tuple[int, ...]) -> int:
        """Fold the authentic source through all pairs before its top K digits."""
        self._validate_source_digits(source_digits_lsd)
        return self.source_inner_carry_from_validated_digits(source_digits_lsd)

    def source_inner_carry_from_validated_digits(
        self, source_digits_lsd: tuple[int, ...]
    ) -> int:
        """Compute source carry from digits validated by the owning caller."""
        self._check_source_geometry(source_digits_lsd)
        carry = 0
        if self.operation == "reverse-add":
            self.relation_store.ledger.bump(
                _reverse_add_keys.REVERSE_BOUNDARY_WINDOW_SOURCE_INNER_SCAN_READS,
                2 * (len(source_digits_lsd) - self.digits),
            )
            for index in range(len(source_digits_lsd) - self.digits):
                pair = source_digits_lsd[index] + source_digits_lsd[-1 - index]
                carry = apply_carry_fn(value_carry_fn(pair, 10), carry)
            return carry
        # In 2*reverse, the reversed source is consumed from the original MSD.
        # The low K output digits and the unknown middle determine this carry.
        self.relation_store.ledger.bump(
            _reverse_add_keys.REVERSE_BOUNDARY_WINDOW_SOURCE_INNER_SCAN_READS,
            len(source_digits_lsd) - self.digits,
        )
        for digit in reversed(source_digits_lsd[self.digits :]):
            # Doubling one source digit maps the incoming Boolean carry by
            # c ↦ [2*digit+c >= 10].  Use the shared value-carry law directly;
            # reconstructing the same map from its two output ports duplicated
            # the carry classification on every scanned digit.
            transfer = value_carry_fn(2 * digit, 10)
            carry = apply_carry_fn(transfer, carry)
        return carry

    def boundary_pair_word(self, tile: WindowTile) -> tuple[int, ...]:
        """Known symmetric pair coefficients, ordered from the LSD edge."""
        self._validate_tile(tile)
        prefix_digits: list[int] = []
        suffix_digits: list[int] = []
        prefix = tile.prefix
        suffix = tile.suffix
        for _ in range(self.digits):
            prefix_digits.append(prefix % 10)
            suffix_digits.append(suffix % 10)
            prefix //= 10
            suffix //= 10
        return tuple(
            suffix_digits[index] + prefix_digits[self.digits - 1 - index]
            for index in range(self.digits)
        )

    def edge_carry_interface(self, tile: WindowTile) -> tuple[int, tuple[int, int]]:
        """Return the exact low carry and high-window Boolean response map."""
        if self.operation != "reverse-add":
            raise ValueError("symmetric pair interfaces belong to reverse/add")
        last: tuple[int, int, tuple[int, int]] | None = None
        for interface in self._iter_carry_interfaces(tile):
            last = interface
        if last is None:
            raise AssertionError("a positive-width boundary has no carry interface")
        return last[1], last[2]

    def _iter_carry_interfaces(
        self, tile: WindowTile
    ) -> Iterator[tuple[int, int, tuple[int, int]]]:
        """Yield carry projections for each LSD-prefix in one spatial pass.

        The low fold appends a symbol, so it composes ``new ∘ old``. The high
        response describes the reflected prefix, so a new symbol is prepended
        and composes ``old ∘ new``. Keeping both accumulators here avoids
        rebuilding the pair word and refolding every nested prefix.
        """
        if self.operation != "reverse-add":
            raise ValueError("symmetric pair interfaces belong to reverse/add")
        self._validate_tile(tile)
        prefix_digits: list[int] = []
        prefix = tile.prefix
        for _ in range(self.digits):
            prefix_digits.append(prefix % 10)
            prefix //= 10

        suffix = tile.suffix
        low = CarryFn.ID
        high = CarryFn.ID
        for index in range(self.digits):
            pair = suffix % 10 + prefix_digits[self.digits - 1 - index]
            suffix //= 10
            effect = value_carry_fn(pair, 10)
            low = compose_carry_fn(effect, low)
            high = compose_carry_fn(high, effect)
            yield (
                index + 1,
                apply_carry_fn(low, 0),
                (apply_carry_fn(high, 0), apply_carry_fn(high, 1)),
            )

    def nested_carry_interfaces(
        self, tile: WindowTile
    ) -> tuple[tuple[int, int, tuple[int, int]], ...]:
        """Exact dyadic spatial summaries of the known symmetric boundary pairs."""
        if self.operation != "reverse-add":
            raise ValueError("symmetric pair interfaces belong to reverse/add")
        spans: list[int] = []
        span = 1
        while span < self.digits:
            spans.append(span)
            span *= 2
        if not spans or spans[-1] != self.digits:
            spans.append(self.digits)
        result: list[tuple[int, int, tuple[int, int]]] = []
        next_span = 0
        for interface in self._iter_carry_interfaces(tile):
            if interface[0] == spans[next_span]:
                result.append(interface)
                next_span += 1
                if next_span == len(spans):
                    break
        return tuple(result)

    def next_tiles(
        self,
        prefix: int,
        suffix: int,
        *,
        admitted_inner: tuple[int, ...] = (0, 1),
    ) -> frozenset[WindowTile]:
        self._validate_boundary(prefix, suffix)
        if type(admitted_inner) is not tuple or not admitted_inner:
            raise ValueError("at least one exact inner carry is required")
        if self.operation == "double-reverse" and suffix % 10 == 0:
            raise WindowRelationBudgetExceeded("2*reverse zero tail may shrink width")
        reversed_prefix = self.reverse_block(prefix)
        reversed_suffix = self.reverse_block(suffix)
        if self.operation == "reverse-add":
            new_suffix = (suffix + reversed_prefix) % self.modulus
            raw_high = prefix + reversed_suffix
        else:
            new_suffix = (2 * reversed_prefix) % self.modulus
            raw_high = 2 * reversed_suffix
        with self.relation_store.transient_states() as outcomes:
            for carry in admitted_inner:
                if type(carry) is not int or carry not in (0, 1):
                    raise ValueError("interior carry options must be Boolean integers")
                self.transition_evaluations += 1
                self._charge_operation()
                high = raw_high + carry
                growth = int(high >= self.modulus)
                new_prefix = high // 10 if growth else high
                if not self.minimum_prefix <= new_prefix < self.modulus:
                    raise WindowRelationBudgetExceeded("boundary width is unresolved")
                if self.operation == "double-reverse" and new_suffix % 10 == 0:
                    raise WindowRelationBudgetExceeded(
                        "2*reverse successor has zero tail"
                    )
                outcomes.add(WindowTile(new_prefix, new_suffix, growth))
                if len(outcomes) > self.max_states:
                    raise WindowRelationBudgetExceeded("boundary state limit exceeded")
            return outcomes.freeze()

    def advance(
        self,
        tiles: frozenset[WindowTile],
        distance: int,
        *,
        initial_inner: int | None = None,
        max_operations: int,
    ) -> frozenset[WindowTile]:
        if type(tiles) is not frozenset or not tiles:
            raise ValueError("boundary advance requires nonempty immutable states")
        distance = require_integer(distance, "boundary temporal distance", 0)
        max_operations = require_integer(max_operations, "boundary operation limit", 0)
        self._operation_limit = max_operations
        self._call_operations = 0
        self.relation_store.ledger.bump(
            _reverse_add_keys.REVERSE_BOUNDARY_WINDOW_QUERIES
        )
        result = tiles
        try:
            if initial_inner is not None:
                if distance < 1:
                    raise ValueError("a source carry requires a first transition")
                result = self._direct_step(result, (initial_inner,))
                distance -= 1
            level = 0
            while distance:
                if distance & 1:
                    result = self._join_outcomes(
                        result, partial(self._power_for_tile, level)
                    )
                distance >>= 1
                level += 1
            return result
        finally:
            self.composition_operations += self._call_operations

    def _join_outcomes(
        self,
        parents: Iterable[WindowTile],
        children: Callable[[WindowTile], Iterable[WindowTile]],
    ) -> frozenset[WindowTile]:
        """Compose parent/child relations and account for every joined state."""
        with self.relation_store.transient_states() as results:
            for parent in parents:
                for child in children(parent):
                    self._charge_composition()
                    results.add(
                        WindowTile(
                            child.prefix,
                            child.suffix,
                            parent.growth + child.growth,
                        )
                    )
                    if len(results) > self.max_states:
                        raise WindowRelationBudgetExceeded(
                            "boundary state limit exceeded"
                        )
            return results.freeze()

    def _power_for_tile(self, level: int, tile: WindowTile) -> frozenset[WindowTile]:
        return self._power(tile.prefix, tile.suffix, level)

    def _direct_step(
        self, tiles: frozenset[WindowTile], carries: tuple[int, ...]
    ) -> frozenset[WindowTile]:
        with self.relation_store.transient_states() as result:
            for tile in tiles:
                for target in self.next_tiles(
                    tile.prefix, tile.suffix, admitted_inner=carries
                ):
                    result.add(
                        WindowTile(
                            target.prefix,
                            target.suffix,
                            tile.growth + target.growth,
                        )
                    )
            if len(result) > self.max_states:
                raise WindowRelationBudgetExceeded("boundary state limit exceeded")
            return result.freeze()

    def _power(self, prefix: int, suffix: int, level: int) -> frozenset[WindowTile]:
        root: _RelationKey = (self.digits, self.operation, prefix, suffix, level)
        found = self._cache_get(root)
        if found is not None:
            return found
        with self.relation_store.charged_frontier() as work:
            work.push((root, False))
            while work:
                key, expanded = work.pop()
                if self._cache_get(key) is not None:
                    continue
                key_digits = key[0]
                key_operation: BoundaryOperation = key[1]
                key_prefix = key[2]
                key_suffix = key[3]
                key_level = key[4]
                if key_level == 0:
                    self._cache_store(
                        key,
                        self.next_tiles(key_prefix, key_suffix, admitted_inner=(0, 1)),
                    )
                    self.expanded_relations += 1
                    continue
                first_key = (
                    key_digits,
                    key_operation,
                    key_prefix,
                    key_suffix,
                    key_level - 1,
                )
                first = self._cache_get(first_key)
                if not expanded:
                    work.push((key, True))
                    if first is None:
                        work.push((first_key, False))
                    continue
                if first is None:
                    work.push((key, True))
                    work.push((first_key, False))
                    continue
                unique_child_keys: dict[_RelationKey, None] = {}
                for tile in first:
                    child_key: _RelationKey = (
                        key_digits,
                        key_operation,
                        tile.prefix,
                        tile.suffix,
                        key_level - 1,
                    )
                    unique_child_keys.setdefault(child_key, None)
                missing = tuple(
                    child
                    for child in unique_child_keys
                    if self._cache_get(child) is None
                )
                if missing:
                    work.push((key, True))
                    work.extend((child, False) for child in reversed(missing))
                    continue

                def second_half(
                    middle: WindowTile,
                    *,
                    digits: int = key_digits,
                    operation: BoundaryOperation = key_operation,
                    level: int = key_level,
                ) -> Iterable[WindowTile]:
                    second_key = (
                        digits,
                        operation,
                        middle.prefix,
                        middle.suffix,
                        level - 1,
                    )
                    second = self._cache_get(second_key)
                    if second is None:
                        raise AssertionError(
                            "boundary power dependency was not published"
                        )
                    return second

                self._cache_store(key, self._join_outcomes(first, second_half))
                self.expanded_relations += 1
        result = self._cache_get(root)
        if result is None:
            raise AssertionError("boundary power root was not published")
        return result

    def _cache_get(self, key: _RelationKey) -> frozenset[WindowTile] | None:
        memo = self.relation_store.memo
        memo.ledger.bump(_reverse_add_keys.REVERSE_BOUNDARY_WINDOW_RELATION_LOOKUPS)
        try:
            record = memo[key]
        except KeyError:
            self.cache_misses += 1
            memo.ledger.bump(_reverse_add_keys.REVERSE_BOUNDARY_WINDOW_RELATION_MISSES)
            return None
        if (
            type(record) is not BoundaryRelationRecord
            or type(record.outcomes) is not frozenset
            or len(record.outcomes) > self.max_states
            or any(
                type(tile) is not WindowTile
                or type(tile.prefix) is not int
                or type(tile.suffix) is not int
                or type(tile.growth) is not int
                or not self.minimum_prefix <= tile.prefix < self.modulus
                or not 0 <= tile.suffix < self.modulus
                or not 0 <= tile.growth <= 1 << key[4]
                or tile.growth.bit_length() > 64
                for tile in record.outcomes
            )
        ):
            raise ValueError("cached boundary relation is malformed")
        result = record.outcomes
        self.cache_hits += 1
        memo.ledger.bump(_reverse_add_keys.REVERSE_BOUNDARY_WINDOW_RELATION_HITS)
        return result

    def _cache_store(self, key: _RelationKey, value: frozenset[WindowTile]) -> None:
        if self.relation_store.publish(key, value):
            self.relation_store.ledger.bump(
                _reverse_add_keys.REVERSE_BOUNDARY_WINDOW_RELATION_PUBLICATIONS
            )

    def _charge_composition(self) -> None:
        self._charge_operation()
        self.relation_store.ledger.bump(
            _reverse_add_keys.REVERSE_BOUNDARY_WINDOW_COMPOSITIONS
        )

    def _charge_operation(self) -> None:
        self._call_operations += 1
        if self._call_operations > self._operation_limit:
            raise WindowRelationBudgetExceeded("boundary work limit exceeded")

    def _validate_tile(self, tile: WindowTile) -> None:
        if (
            type(tile) is not WindowTile
            or not self.minimum_prefix <= tile.prefix < self.modulus
            or not 0 <= tile.suffix < self.modulus
        ):
            raise ValueError("invalid fixed-width boundary tile")

    @staticmethod
    def _validate_source_digits(source_digits_lsd: tuple[int, ...]) -> None:
        if type(source_digits_lsd) is not tuple or not source_digits_lsd:
            raise ValueError("boundary source digits must be a nonempty tuple")
        if any(
            type(digit) is not int or not 0 <= digit <= 9 for digit in source_digits_lsd
        ):
            raise ValueError("boundary source digits must be decimal digits")

    def _validate_boundary(self, prefix: int, suffix: int) -> None:
        if (
            type(prefix) is not int
            or type(suffix) is not int
            or not self.minimum_prefix <= prefix < self.modulus
            or not 0 <= suffix < self.modulus
        ):
            raise WindowRelationBudgetExceeded("invalid fixed-width boundary tile")


class ReverseBoundaryWindowObserver:
    """Request-owned 196 edge observer with one bounded relation store."""

    def __init__(
        self,
        seed: int,
        generation: int,
        ledger: ResourceLedger,
        *,
        max_relation_entries: int = 8192,
        max_relation_states: int = 32_768,
        max_states: int = 4096,
        max_compositions: int = 50_000,
        source_workspace: ReverseSourceImageWorkspace | None = None,
    ) -> None:
        self.seed = require_integer(seed, "boundary source", 0)
        self.generation = require_integer(generation, "boundary generation", 0)
        if type(ledger) is not ResourceLedger:
            raise TypeError("boundary observer requires its term resource ledger")
        if source_workspace is not None:
            from number_compiler.sequences.reverse_add.source_workspace import (
                ReverseSourceImageWorkspace,
            )

            if type(source_workspace) is not ReverseSourceImageWorkspace:
                raise TypeError("boundary observer requires the exact source workspace")
            source_workspace.check_request(self.seed, self.generation, 10)
            if source_workspace.ledger is not ledger:
                raise ValueError("boundary source workspace belongs to another ledger")
        self.ledger = ledger
        self.source_workspace = source_workspace
        self.binding = (self.seed, self.generation, 10)
        self.max_relation_entries = require_integer(
            max_relation_entries, "boundary relation entry limit", 1
        )
        self.max_relation_states = require_integer(
            max_relation_states, "boundary retained-state limit", 1
        )
        self.max_states = require_integer(max_states, "boundary state limit", 1)
        self.max_compositions = require_integer(
            max_compositions, "boundary work limit", 0
        )
        self._relations = BoundaryRelationStore(
            ledger,
            max_entries=self.max_relation_entries,
            max_states=self.max_relation_states,
        )
        self._relation_data = self._relations.memo
        observation_owner = ledger.register(
            f"reverse-boundary-observation-{ledger.owner_count}",
            "reverse_boundary_window_observation",
        )
        self._observation_memo: OwnedMemo[
            tuple[int, int, int],
            BoundaryObservationCacheRecord,
        ] = OwnedMemo(ledger, observation_owner, nodes_per_entry=16)
        self._observation_data = self._observation_memo.audit_container
        self._state_tiles_binding = self._relations.state_tiles_binding
        self._state_owner = self._relations.state_owner
        self._authority = (
            ledger,
            self.binding,
            self.max_relation_entries,
            self.max_relation_states,
            self.max_states,
            self.max_compositions,
            self._relations,
            self._relations.memo,
            self._relation_data,
            self._observation_memo,
            self._observation_data,
            self._state_tiles_binding,
            self._state_owner,
            source_workspace,
        )
        ledger.register_execution_root(self)
        ledger.register_payload_audit_contract(
            self,
            "reverse_add",
            (
                PayloadAuditStoreBinding(
                    self._relations.memo.owner,
                    "_relation_data",
                    "reverse_boundary_window_relation",
                ),
                PayloadAuditStoreBinding(
                    self._observation_memo.owner,
                    "_observation_data",
                    "reverse_boundary_window_observation",
                ),
                PayloadAuditStoreBinding(
                    self._state_owner,
                    "_state_tiles_binding",
                    "reverse_boundary_window_states",
                ),
            ),
            audit_reverse_boundary_window_owner,
        )

    @property
    def relations(self) -> BoundaryRelationStore:
        return self._relations

    def observation_audit_snapshot(
        self,
    ) -> OwnedMemoAuditSnapshot[tuple[int, int, int], BoundaryObservationCacheRecord]:
        """Expose exact cache ownership metadata through a read-only snapshot."""
        return self._observation_memo.audit_snapshot()

    def validate_authority(self) -> None:
        if type(self._relations) is not BoundaryRelationStore:
            raise ValueError("boundary observer relation store changed")
        memo = self._relations.memo
        authority = self._authority
        if (
            type(authority) is not tuple
            or len(authority) != 14
            or self.ledger is not authority[0]
            or self.binding != authority[1]
            or (self.seed, self.generation, 10) != self.binding
            or self.max_relation_entries != authority[2]
            or self.max_relation_states != authority[3]
            or self.max_states != authority[4]
            or self.max_compositions != authority[5]
            or self._relations is not authority[6]
            or memo is not authority[7]
            or self._relation_data is not authority[8]
            or self._relations.ledger is not self.ledger
            or self._relations.max_entries != self.max_relation_entries
            or self._relations.max_states != self.max_relation_states
            or memo.ledger is not self.ledger
            or memo is not self._relation_data
            or self.ledger.registered_container(memo.owner) is not self._relation_data
            or self._observation_memo is not authority[9]
            or self._observation_data is not authority[10]
            or self._observation_memo.ledger is not self.ledger
            or self._observation_memo.audit_container is not self._observation_data
            or self.ledger.registered_container(self._observation_memo.owner)
            is not self._observation_data
            or self._state_tiles_binding is not authority[11]
            or self._state_owner != authority[12]
            or self._state_tiles_binding is not self._relations.state_tiles_binding
            or self._state_owner != self._relations.state_owner
            or not self._relations.stores_registered()
            or self.source_workspace is not authority[13]
        ):
            raise ValueError("boundary observer authority or ledger changed")
        if self.source_workspace is not None:
            self.source_workspace.check_request(self.seed, self.generation, 10)
            if self.source_workspace.ledger is not self.ledger:
                raise ValueError("boundary source workspace belongs to another ledger")
        cached = self.cached_record()
        if cached is not None:
            result = cached.observation
            if type(result) is not ReverseBoundaryWindowObservation:
                raise ValueError("boundary observation cache has another result type")
            if observation_fields(result) != cached.fields:
                raise ValueError("boundary observation cache was changed")
            try:
                result.__post_init__()
            except (TypeError, ValueError) as exc:
                raise ValueError("boundary observation cache was changed") from exc
            if result.seed != self.seed or result.steps != self.generation:
                raise ValueError("boundary observation cache was changed")

    def observe(
        self, *, seed: int, generation: int, base: int
    ) -> ReverseBoundaryWindowObservation:
        self.validate_authority()
        if (seed, generation, base) != self.binding:
            raise ValueError("boundary observer source or index binding changed")
        cached = self.cached_record()
        if cached is not None:
            self.ledger.bump(
                _reverse_add_keys.REVERSE_BOUNDARY_WINDOW_OBSERVATION_CACHE_HITS
            )
            return cached.observation
        self.ledger.bump(
            _reverse_add_keys.REVERSE_BOUNDARY_WINDOW_OBSERVATION_CACHE_MISSES
        )
        source_ports = None
        if self.source_workspace is None:
            source_digits = digits_lsd(seed, 10)
            exact_source = None
            self.ledger.bump(
                _reverse_add_keys.REVERSE_BOUNDARY_WINDOW_SOURCE_DIGIT_DECODES,
                len(source_digits),
            )
        else:
            exact_source = self.source_workspace.actions.source(
                self.source_workspace.source
            )
            if exact_source.base != 10:
                raise ValueError("boundary source workspace is not decimal")
            source_digits = exact_source.digits
        width = len(source_digits)
        candidates = tuple(digits for digits in (2, 4, 8) if 2 * digits + 1 <= width)
        if not candidates:
            result = self._unavailable(
                "source is too narrow for a two-digit boundary window"
            )
            self._cache_observation(result)
            return result
        last_reason = "no boundary window was admissible"
        engines: list[FiniteBoundaryWindow] = []
        work_before = self._work_counters(engines)
        for window_digits in candidates:
            engine = self._engine(window_digits)
            engines.append(engine)
            try:
                self.ledger.bump(
                    _reverse_add_keys.REVERSE_BOUNDARY_WINDOW_SOURCE_DIGIT_READS,
                    2 * window_digits,
                )
                initial = engine.source_tile_from_validated_digits(source_digits)
                source_carry = None
                if generation and self.source_workspace is None:
                    source_carry = engine.source_inner_carry_from_validated_digits(
                        source_digits
                    )
                elif generation and self.source_workspace is not None:
                    source_ports = self.source_workspace.boundary_source_ports()
                    source = source_ports.source
                    source_ports.check_source(source)
                    if (
                        source is not exact_source
                        or source.base != 10
                        or source_ports.ledger is not self.ledger
                    ):
                        raise ValueError(
                            "boundary source carry ports are not decimal and owned"
                        )
                    source_carry = source_ports.carry(width - window_digits)
                used_before = sum(self._engine_work(item) for item in engines)
                remaining = max(
                    0, self.max_compositions - (used_before - work_before[2])
                )
                outcomes = engine.advance(
                    frozenset({initial}),
                    generation,
                    initial_inner=source_carry,
                    max_operations=remaining,
                )
                growths = {tile.growth for tile in outcomes}
                msds = {tile.prefix // engine.minimum_prefix for tile in outcomes}
                lsds = {tile.suffix % 10 for tile in outcomes}
                if len(growths) != 1 or len(msds) != 1 or len(lsds) != 1:
                    raise WindowRelationBudgetExceeded(
                        "admissible interior carries disagree on width or edge digits"
                    )
                prefix, suffix = _common_boundary_digits(outcomes, window_digits)
                result = ReverseBoundaryWindowObservation(
                    "available",
                    self.seed,
                    self.generation,
                    width + next(iter(growths)),
                    prefix,
                    suffix,
                    window_digits,
                    len(outcomes),
                    self._relations_hits_since(engines, work_before[0]),
                    self._relations_misses_since(engines, work_before[1]),
                    sum(self._engine_work(item) for item in engines) - work_before[2],
                    None,
                )
                self._cache_observation(result)
                return result
            except WindowRelationBudgetExceeded as exc:
                last_reason = str(exc)
                continue
        result = self._unavailable(last_reason, work_before, engines)
        self._cache_observation(result)
        return result

    def _cache_observation(self, result: ReverseBoundaryWindowObservation) -> None:
        result.__post_init__()
        self._observation_memo[self.binding] = BoundaryObservationCacheRecord(
            result, observation_fields(result)
        )

    def cached_record(
        self,
    ) -> BoundaryObservationCacheRecord | None:
        return self._observation_memo.get(self.binding)

    def _engine(self, digits: int) -> FiniteBoundaryWindow:
        return FiniteBoundaryWindow(
            digits,
            operation="reverse-add",
            relation_store=self._relations,
            max_states=self.max_states,
        )

    def _work_counters(
        self, engines: list[FiniteBoundaryWindow]
    ) -> tuple[int, int, int]:
        return (
            sum(engine.cache_hits for engine in engines),
            sum(engine.cache_misses for engine in engines),
            sum(self._engine_work(engine) for engine in engines),
        )

    @staticmethod
    def _engine_work(engine: FiniteBoundaryWindow) -> int:
        return engine.composition_operations + engine.transition_evaluations

    def _relations_hits_since(
        self, engines: list[FiniteBoundaryWindow], before: int
    ) -> int:
        return sum(engine.cache_hits for engine in engines) - before

    def _relations_misses_since(
        self, engines: list[FiniteBoundaryWindow], before: int
    ) -> int:
        return sum(engine.cache_misses for engine in engines) - before

    def _unavailable(
        self,
        reason: str,
        before: tuple[int, int, int] | None = None,
        engines: list[FiniteBoundaryWindow] | None = None,
    ) -> ReverseBoundaryWindowObservation:
        values = self._work_counters([] if engines is None else engines)
        start = (0, 0, 0) if before is None else before
        return ReverseBoundaryWindowObservation(
            "unavailable",
            self.seed,
            self.generation,
            None,
            "",
            "",
            None,
            0,
            values[0] - start[0],
            values[1] - start[1],
            values[2] - start[2],
            reason,
        )


def _common_boundary_digits(
    tiles: frozenset[WindowTile], digits: int
) -> tuple[str, str]:
    prefixes = tuple(f"{tile.prefix:0{digits}d}" for tile in tiles)
    suffixes = tuple(f"{tile.suffix:0{digits}d}" for tile in tiles)
    common_prefix = prefixes[0]
    common_suffix = suffixes[0]
    for candidate in prefixes[1:]:
        length = 0
        while (
            length < len(common_prefix) and common_prefix[length] == candidate[length]
        ):
            length += 1
        common_prefix = common_prefix[:length]
    for candidate in suffixes[1:]:
        length = 0
        while (
            length < len(common_suffix)
            and common_suffix[-length - 1] == candidate[-length - 1]
        ):
            length += 1
        common_suffix = common_suffix[len(common_suffix) - length :]
    return common_prefix, common_suffix


def observation_fields(
    result: ReverseBoundaryWindowObservation,
) -> tuple[object, ...]:
    return (
        result.status,
        result.seed,
        result.steps,
        result.target_width,
        result.prefix,
        result.suffix,
        result.window_digits,
        result.boundary_states,
        result.relation_cache_hits,
        result.relation_cache_misses,
        result.relation_operations,
        result.reason,
        result.full_integer_powered,
    )


__all__ = [
    "BoundaryRelationStore",
    "FiniteBoundaryWindow",
    "ReverseBoundaryWindowObservation",
    "ReverseBoundaryWindowObserver",
    "WindowRelationBudgetExceeded",
    "WindowTile",
    "observation_fields",
]
