"""Ownership and source checks for cached finite 2rev10 carry refinements."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)
from number_compiler.sequences.double_reverse.boundary_cycles import (
    candidate_component,
    is_edge_tuple,
)
from number_compiler.sequences.double_reverse.temporal_carry_safety import (
    ComponentSafetyProof,
    SourceCarrySafety,
    component_layers,
    component_safety_from_layers,
    lift_from_slp,
    source_carry_safety_from_layers,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    DoubleReverseSourcePrefix,
)

if TYPE_CHECKING:
    from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
    from number_compiler.sequences.double_reverse.source_adapter import (
        DoubleReverseSource,
        DoubleReverseSourceAdapter,
    )


CarrySafetyCacheKey = tuple[str, int, int, int, int]
CarrySafetyResult = tuple[int, SourceCarrySafety, tuple[ComponentSafetyProof, ...]]
CARRY_SAFETY_CONSUMER = "temporal.carry-safety"
_COMPONENT_PROOF_SHAPES = (
    (900, True, None, (900,)),
    (600, False, 5, (600, 550, 470, 270, 170, 120, 0)),
    (600, False, 5, (600, 500, 460, 360, 160, 60, 0)),
    (400, False, 4, (400, 300, 240, 80, 30, 0)),
)


@dataclass(frozen=True, slots=True)
class IssuedCarrySafety:
    """A term-issued immutable result with a complete field snapshot."""

    issuer: ArenaToken
    key: CarrySafetyCacheKey
    result: CarrySafetyResult
    snapshot: tuple[object, ...]


def _typed_scalar(value: object) -> tuple[type[object], object]:
    return type(value), value


def _typed_tuple(value: object) -> tuple[type[object], tuple[object, ...]]:
    if not is_exact_object_tuple(value):
        raise ValueError("carry-safety payload contains a non-tuple sequence")
    return tuple, tuple(_typed_scalar(item) for item in value)


def _typed_edges(value: object) -> tuple[type[object], tuple[object, ...]]:
    if not is_exact_object_tuple(value):
        raise ValueError("carry-safety edges are not an immutable tuple")
    return tuple, tuple(_typed_tuple(edge) for edge in value)


def carry_safety_payload_snapshot(value: object) -> tuple[object, ...]:
    """Capture every public result field with exact types, without recursion."""
    if not is_exact_object_tuple(value) or len(value) != 3:
        raise ValueError("carry-safety result has an invalid outer record")
    prefix, source, proofs = value
    if type(source) is not SourceCarrySafety or not is_exact_object_tuple(proofs):
        raise ValueError("carry-safety result has invalid typed records")
    source_fields = (
        _typed_tuple(source.source_edge),
        _typed_tuple(source.high3),
        _typed_tuple(source.low3),
        _typed_scalar(source.component),
        _typed_scalar(source.current_forced_carry),
        _typed_scalar(source.next_forced_carry),
        _typed_edges(source.possible_next_edges),
        _typed_scalar(source.shrinking_frontier),
        _typed_scalar(source.source_maximum_internal_transitions),
        _typed_scalar(source.component_maximum_internal_transitions),
        _typed_scalar(source.universally_closed_component),
        _typed_scalar(source.exact_width_change),
        _typed_scalar(source.unconditional_entry_or_shrink_bound),
    )
    proof_rows: list[object] = []
    for proof in proofs:
        if type(proof) is not ComponentSafetyProof:
            raise ValueError("carry-safety proof has an invalid record type")
        proof_rows.append(
            (
                _typed_scalar(proof.component),
                _typed_scalar(proof.lifted_states),
                _typed_scalar(proof.universally_closed),
                _typed_scalar(proof.maximum_internal_transitions),
                _typed_tuple(proof.surviving_state_counts),
            )
        )
    return (
        _typed_scalar(prefix),
        (SourceCarrySafety, source_fields),
        (tuple, tuple(proof_rows)),
    )


def issue_carry_safety(
    issuer: ArenaToken, key: CarrySafetyCacheKey, result: CarrySafetyResult
) -> IssuedCarrySafety:
    """Seal a fully computed result before its ledger-owned publication."""
    if type(issuer) is not ArenaToken:
        raise TypeError("carry-safety issuer is not an arena token")
    if type(key) is not tuple or len(key) != 5:
        raise TypeError("carry-safety cache key has an invalid shape")
    return IssuedCarrySafety(issuer, key, result, carry_safety_payload_snapshot(result))


def validate_issued_carry_safety(
    issued: object,
    key: CarrySafetyCacheKey,
    issuer: ArenaToken,
) -> CarrySafetyResult:
    """Check source issuance and every sealed field before returning a hit."""
    if (
        type(issued) is not IssuedCarrySafety
        or issued.issuer is not issuer
        or type(issued.key) is not tuple
        or len(issued.key) != 5
        or type(issued.key[0]) is not str
        or any(type(item) is not int for item in issued.key[1:])
        or issued.key != key
        or type(issued.snapshot) is not tuple
    ):
        raise ValueError("carry-safety cache entry failed its source seal")
    try:
        snapshot = carry_safety_payload_snapshot(issued.result)
    except (AttributeError, TypeError, ValueError):
        raise ValueError("carry-safety cache entry was altered after issue") from None
    if snapshot != issued.snapshot:
        raise ValueError("carry-safety cache entry was altered after issue")
    return issued.result


def carry_safety_result_node_cost(
    _key: CarrySafetyCacheKey, value: IssuedCarrySafety
) -> int:
    """Account for the report and its sealed duplicate field snapshot."""
    _prefix, source, proofs = value.result
    return 1 + 2 * (
        len(source.possible_next_edges)
        + sum(len(proof.surviving_state_counts) for proof in proofs)
        + 13
        + 5 * len(proofs)
    )


__all__ = [
    "CARRY_SAFETY_CONSUMER",
    "CarrySafetyCacheKey",
    "CarrySafetyResult",
    "audit_double_reverse_carry_safety",
    "carry_safety_result_node_cost",
]


class CarrySafetyAuditBase:
    """Source-bound computations and audits owned by the slotted term."""

    __slots__ = ()
    _source: DoubleReverseSource
    _arena: LedgerSLPArena
    _adapter: DoubleReverseSourceAdapter
    _issuer: ArenaToken
    _scratch_owner: int
    _carry_safety_cache: OwnedMemo[CarrySafetyCacheKey, IssuedCarrySafety]
    _carry_safety_owner: int
    _audit_carry_safety: object
    generation: int

    @property
    def resource_ledger(self) -> ResourceLedger:
        raise NotImplementedError

    def _certified_prefix_entry(
        self, *, max_prefix: int, require_even_remainder: bool
    ) -> DoubleReverseSourcePrefix:
        raise NotImplementedError

    def _validate_source_binding(self) -> None:
        raise NotImplementedError

    def carry_safety_entries(
        self,
    ) -> tuple[tuple[CarrySafetyCacheKey, IssuedCarrySafety], ...]:
        """Capture the currently retained immutable refinement records."""
        return tuple(self._carry_safety_cache.items())

    @property
    def carry_safety_owner(self) -> int:
        return self._carry_safety_owner

    def compute_carry_safety(self) -> CarrySafetyResult:
        """Build or reuse the source-bound finite carry report for one term."""
        analysis_root = self._source.root
        prefix = 0
        if self._arena.nodes[analysis_root].length < 5:
            entry = self._certified_prefix_entry(
                max_prefix=min(32, self.generation),
                require_even_remainder=False,
            )
            prefix = entry.physical_steps
            analysis_root = self._adapter.temporal_hashlife.root_of(entry.target)
        cache_key: CarrySafetyCacheKey = (
            CARRY_SAFETY_CONSUMER,
            self.generation,
            self._source.root,
            analysis_root,
            prefix,
        )
        cached = self._carry_safety_cache.get(cache_key)
        if cached is not None:
            result = validate_issued_carry_safety(cached, cache_key, self._issuer)
            if result[0] != prefix:
                raise ValueError("carry-safety cache has a stale source prefix")
            return result

        lifted = lift_from_slp(self._arena, analysis_root)
        width = self._arena.nodes[analysis_root].length
        trailing_zeros = self._adapter.trailing_zero_count(analysis_root)
        least_nonzero = symbol_at(
            self._arena, analysis_root, width - trailing_zeros - 1
        )
        exact_width_change = -trailing_zeros + int(least_nonzero >= 5)
        with self.resource_ledger.reservation(
            self._scratch_owner, entries=9000, nodes=9000
        ):
            layers = tuple(component_layers(index) for index in range(4))
            component = candidate_component(lifted.edge)
            safety = source_carry_safety_from_layers(
                lifted, None if component is None else layers[component]
            )
            if (
                safety.exact_width_change is not None
                and safety.exact_width_change != exact_width_change
            ):
                raise AssertionError(
                    "lifted border disagrees with exact width arithmetic"
                )
            proofs = tuple(
                component_safety_from_layers(index, layers[index]) for index in range(4)
            )
        result = (
            prefix,
            replace(safety, exact_width_change=exact_width_change),
            proofs,
        )
        self._carry_safety_cache[cache_key] = issue_carry_safety(
            self._issuer, cache_key, result
        )
        return result

    def valid_carry_safety_result(
        self,
        key: object,
        value: object,
    ) -> bool:
        if (
            not is_exact_object_tuple(key)
            or len(key) != 5
            or type(key[0]) is not str
            or key[0] != CARRY_SAFETY_CONSUMER
            or any(type(item) is not int for item in key[1:])
            or type(value) is not IssuedCarrySafety
            or type(value.key) is not tuple
            or len(value.key) != 5
        ):
            return False
        consumer, generation, source_root, analysis_root, prefix = cast(
            CarrySafetyCacheKey, key
        )
        try:
            cached_prefix, source, proofs = validate_issued_carry_safety(
                value, cast(CarrySafetyCacheKey, key), self._issuer
            )
        except (AttributeError, TypeError, ValueError):
            return False
        if (
            value.key != key
            or consumer != CARRY_SAFETY_CONSUMER
            or generation != self.generation
            or source_root != self._source.root
            or analysis_root < 0
            or analysis_root >= len(self._arena.nodes)
            or prefix < 0
            or prefix > generation
            or cached_prefix != prefix
            or self._arena.nodes[analysis_root].length < 5
            or type(source) is not SourceCarrySafety
            or not is_exact_object_tuple(proofs)
            or len(proofs) != len(_COMPONENT_PROOF_SHAPES)
        ):
            return False
        if prefix == 0:
            if analysis_root != source_root:
                return False
        else:
            issued = self._adapter.temporal_hashlife.source_prefix()
            if (
                issued is None
                or issued.physical_steps != prefix
                or self._adapter.temporal_hashlife.root_of(issued.target)
                != analysis_root
            ):
                return False

        try:
            lifted = lift_from_slp(self._arena, analysis_root)
        except (IndexError, TypeError, ValueError):
            return False
        if (
            not is_edge_tuple(source.source_edge)
            or type(source.high3) is not tuple
            or len(source.high3) != 3
            or any(
                type(digit) is not int or not 0 <= digit <= 9 for digit in source.high3
            )
            or type(source.low3) is not tuple
            or len(source.low3) != 3
            or any(
                type(digit) is not int or not 0 <= digit <= 9 for digit in source.low3
            )
            or (source.component is not None and type(source.component) is not int)
            or type(source.current_forced_carry) is not int
            or type(source.next_forced_carry) is not int
            or type(source.possible_next_edges) is not tuple
            or any(not is_edge_tuple(edge) for edge in source.possible_next_edges)
            or type(source.shrinking_frontier) is not bool
            or type(source.universally_closed_component) is not bool
            or (
                source.source_maximum_internal_transitions is not None
                and (
                    type(source.source_maximum_internal_transitions) is not int
                    or source.source_maximum_internal_transitions < 0
                )
            )
            or (
                source.component_maximum_internal_transitions is not None
                and (
                    type(source.component_maximum_internal_transitions) is not int
                    or source.component_maximum_internal_transitions < 0
                )
            )
            or (
                source.exact_width_change is not None
                and type(source.exact_width_change) is not int
            )
            or (
                source.unconditional_entry_or_shrink_bound is not None
                and type(source.unconditional_entry_or_shrink_bound) is not int
            )
        ):
            return False
        if (
            source.source_edge != lifted.edge
            or source.high3 != lifted.high
            or source.low3 != lifted.low
            or source.component != candidate_component(lifted.edge)
            or source.current_forced_carry != lifted.forced_inward_carry
            or source.next_forced_carry != lifted.forced_next_inward_carry
        ):
            return False
        for index, proof in enumerate(proofs):
            if type(proof) is not ComponentSafetyProof:
                return False
            expected = _COMPONENT_PROOF_SHAPES[index]
            if (
                type(proof.component) is not int
                or proof.component != index
                or type(proof.lifted_states) is not int
                or proof.lifted_states != expected[0]
                or type(proof.universally_closed) is not bool
                or proof.universally_closed is not expected[1]
                or (
                    proof.maximum_internal_transitions is not None
                    and type(proof.maximum_internal_transitions) is not int
                )
                or proof.maximum_internal_transitions != expected[2]
                or type(proof.surviving_state_counts) is not tuple
                or any(type(count) is not int for count in proof.surviving_state_counts)
                or proof.surviving_state_counts != expected[3]
            ):
                return False
        return True

    def audit_carry_safety(self, ledger: ResourceLedger) -> PayloadAuditContribution:
        self._validate_source_binding()
        memo = self._carry_safety_cache
        account = ledger.account_status(memo.owner)
        if (
            memo.ledger is not ledger
            or memo.owner != self._carry_safety_owner
            or memo.audit_snapshot().container is not self._audit_carry_safety
            or account.container_identity != id(self._audit_carry_safety)
            or account.role != "double_reverse_temporal_memo"
            or account.disposed
            or memo.nodes_per_entry != 0
            or memo.node_cost is not carry_safety_result_node_cost
            or memo.audit_snapshot().dynamic_nodes != account.nodes
            or account.entries != len(memo)
        ):
            raise ValueError("2rev10 carry-safety memo owner is invalid")

        approved: list[PayloadAuditEntry] = []
        invalid: list[PayloadAuditEntry] = []
        retained_nodes = 0
        for key, value in memo.items():
            valid = self.valid_carry_safety_result(key, value)
            destination = approved if valid else invalid
            destination.extend(
                (
                    PayloadAuditEntry(memo.owner, key),
                    PayloadAuditEntry(memo.owner, value),
                )
            )
            if valid:
                retained_nodes += memo.entry_nodes(key, value)
        if retained_nodes != account.nodes:
            invalid.extend(
                PayloadAuditEntry(memo.owner, member)
                for key, value in memo.items()
                for member in (key, value)
            )
            approved.clear()
        return PayloadAuditContribution(tuple(approved), tuple(invalid))


def temporal_carry_safety_for_term(root: DoubleReverseTerm) -> CarrySafetyResult:
    return root.compute_carry_safety()


def audit_double_reverse_carry_safety(
    ledger_value: object, root_value: object
) -> PayloadAuditContribution:
    """Dispatch only an exact live source-bound term to its owner audit."""
    from number_compiler.sequences.double_reverse.power import DoubleReverseTerm

    if type(ledger_value) is not ResourceLedger:
        raise TypeError("2rev10 carry-safety auditor received a foreign ledger")
    if type(root_value) is not DoubleReverseTerm:
        raise TypeError("2rev10 carry-safety auditor received a foreign owner")
    return root_value.audit_carry_safety(ledger_value)
