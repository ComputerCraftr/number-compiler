"""Exact contextual temporal composition without primitive successor replay.

A finite interface includes all changing value, domain and extent ports.
Composition substitutes their output functions simultaneously and pulls back
admissibility. It never enumerates a trajectory or materializes midpoint values.
This bounded interface algebra does not discover a recursive spatial interface.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import cast

from devtools.experiments.reverse_add.threshold_cocycle import (
    ThresholdCocycleArena,
    ThresholdCocycleResidualID,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bit_transforms import (
    CompleteFiniteTransform,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.owned_memo import OwnedMemoAuditSnapshot


@dataclass(frozen=True, slots=True)
class CocycleAction:
    ports: tuple[FinitePort, ...]
    outputs: tuple[FactoredFunctionID, ...]
    cocycles: tuple[ThresholdCocycleResidualID, ...]
    admissible: FactoredFunctionID
    events: int = field(compare=False)


@dataclass(frozen=True, slots=True)
class CocycleCompositionKey:
    """Complete scoped identity of one ordered temporal composition."""

    before_ports: tuple[FinitePort, ...]
    before_outputs: tuple[FactoredFunctionID, ...]
    before_cocycles: tuple[ThresholdCocycleResidualID, ...]
    before_admissible: FactoredFunctionID
    before_events: int
    after_ports: tuple[FinitePort, ...]
    after_outputs: tuple[FactoredFunctionID, ...]
    after_cocycles: tuple[ThresholdCocycleResidualID, ...]
    after_admissible: FactoredFunctionID
    after_events: int


@dataclass(frozen=True, slots=True)
class CocycleCompositionEntry:
    """Authenticated value retained for one complete composition key."""

    key: CocycleCompositionKey
    entry_id: int
    result: CocycleAction


@dataclass(frozen=True, slots=True)
class CocycleTemporalAuditSnapshot:
    """Exact owner and cache references for non-mutating forensic checks."""

    ledger: ResourceLedger
    bits: BitFunctionArena
    cocycles: ThresholdCocycleArena
    primitive_successors: int
    temporal_compositions: int
    temporal_composition_cache_hits: int
    composition_cache: OwnedMemoAuditSnapshot[
        CocycleCompositionKey, CocycleCompositionEntry
    ]
    composition_seals: OwnedMemoAuditSnapshot[CocycleCompositionKey, tuple[object, ...]]
    composition_cache_identity: object
    composition_seals_identity: object
    next_composition_entry: int
    composition_cache_limit: int
    root_fields: frozenset[str]


class CocycleTemporalArena:
    _COMPOSITION_CACHE_LIMIT = 1024

    def __init__(self, cocycles: ThresholdCocycleArena) -> None:
        if type(cocycles) is not ThresholdCocycleArena:
            raise TypeError("temporal cocycles require their semantic arena")
        self.cocycles = cocycles
        self.bits = cocycles.bits
        self.ledger = self.bits.ledger
        self.primitive_successors = 0
        self.temporal_compositions = 0
        self.temporal_composition_cache_hits = 0
        owner = self.ledger.register(
            f"cocycle-temporal-{len(self.ledger.inventory())}-compositions",
            "query_memo",
        )
        seal_owner = self.ledger.register(
            f"cocycle-temporal-{len(self.ledger.inventory())}-composition-seals",
            "query_memo",
        )
        self._composition_cache: OwnedMemo[
            CocycleCompositionKey, CocycleCompositionEntry
        ] = OwnedMemo(self.ledger, owner, evictable=True)
        self._composition_seals: OwnedMemo[
            CocycleCompositionKey, tuple[object, ...]
        ] = OwnedMemo(self.ledger, seal_owner, evictable=True)
        self._next_composition_entry = 0
        self.ledger.register_execution_root(self)

    @staticmethod
    def _entry_seal(entry: CocycleCompositionEntry) -> tuple[object, ...]:
        """Return the complete immutable publication witness for an entry."""
        result = entry.result
        return (
            CocycleTemporalArena._snapshot_key(entry.key),
            CocycleTemporalArena._snapshot(entry.entry_id),
            CocycleTemporalArena._snapshot(result.ports),
            CocycleTemporalArena._snapshot(result.outputs),
            CocycleTemporalArena._snapshot(result.cocycles),
            CocycleTemporalArena._snapshot(result.admissible),
            CocycleTemporalArena._snapshot(result.events),
        )

    @staticmethod
    def _snapshot(value: object) -> object:
        pending: list[tuple[object, bool]] = [(value, False)]
        results: list[object] = []
        while pending:
            current, expanded = pending.pop()
            if type(current) is tuple:
                items = cast(tuple[object, ...], current)
                if expanded:
                    count = len(items)
                    children = tuple(results[-count:]) if count else ()
                    if count:
                        del results[-count:]
                    results.append(children)
                else:
                    widened_current: object = current
                    pending.append((widened_current, True))
                    pending.extend((item, False) for item in reversed(items))
                continue
            if type(current) is PortVariable:
                results.append(
                    (
                        type(current),
                        (type(current.time), current.time),
                        (type(current.side), current.side),
                        (type(current.role), current.role),
                        (type(current.bit), current.bit),
                    )
                )
                continue
            if type(current) is FinitePort:
                variable = current.variable
                results.append(
                    (
                        type(current),
                        (
                            type(variable),
                            (type(variable.time), variable.time),
                            (type(variable.side), variable.side),
                            (type(variable.role), variable.role),
                            (type(variable.bit), variable.bit),
                        ),
                        (type(current.cardinality), current.cardinality),
                    )
                )
                continue
            if type(current) is FactoredFunctionID:
                results.append(
                    (
                        type(current),
                        type(current.owner),
                        id(current.owner),
                        (type(current.kind), current.kind),
                        (type(current.local_id), current.local_id),
                    )
                )
                continue
            if type(current) is ThresholdCocycleResidualID:
                function = current.function
                if type(function) is not FactoredFunctionID:
                    raise TypeError("unsupported temporal publication field")
                results.append(
                    (
                        type(current),
                        (
                            type(function),
                            type(function.owner),
                            id(function.owner),
                            (type(function.kind), function.kind),
                            (type(function.local_id), function.local_id),
                        ),
                    )
                )
                continue
            if type(current) in (bool, int, str, type(None)):
                results.append((type(current), current))
                continue
            raise TypeError("unsupported temporal publication field")
        if len(results) != 1:
            raise ValueError("temporal publication snapshot did not close")
        return results[0]

    @staticmethod
    def _exact_equal(left: object, right: object) -> bool:
        pending = [(left, right)]
        while pending:
            current_left, current_right = pending.pop()
            if type(current_left) is not type(current_right):
                return False
            if type(current_left) is tuple:
                left_items = cast(tuple[object, ...], current_left)
                right_items = cast(tuple[object, ...], current_right)
                if len(left_items) != len(right_items):
                    return False
                pending.extend(zip(left_items, right_items, strict=True))
            elif current_left != current_right:
                return False
        return True

    @staticmethod
    def _key_fields(key: CocycleCompositionKey) -> tuple[object, ...]:
        return (
            key.before_ports,
            key.before_outputs,
            key.before_cocycles,
            key.before_admissible,
            key.before_events,
            key.after_ports,
            key.after_outputs,
            key.after_cocycles,
            key.after_admissible,
            key.after_events,
        )

    @staticmethod
    def _snapshot_key(key: CocycleCompositionKey) -> tuple[object, ...]:
        return cast(
            tuple[object, ...],
            CocycleTemporalArena._snapshot(CocycleTemporalArena._key_fields(key)),
        )

    def _normal_form(
        self,
        ports: tuple[FinitePort, ...],
        outputs: tuple[FactoredFunctionID, ...],
        cocycles: tuple[ThresholdCocycleResidualID, ...],
        admissible: FactoredFunctionID,
        events: int,
    ) -> CocycleAction:
        # FunctionSignature supplies canonical ordered-port validation.
        FunctionSignature(ports, BOOL)
        if type(events) is not int or events < 1:
            raise ValueError("temporal event metadata must be a positive exact integer")
        if not ports or len(outputs) != len(ports) or not cocycles:
            raise ValueError("a temporal action needs a complete nonempty interface")
        if self.bits.resolve(admissible).signature.output != BOOL:
            raise ValueError("temporal admissibility must be Boolean")
        allowed = set(ports)
        for port, output in zip(ports, outputs, strict=True):
            node = self.bits.resolve(output)
            if getattr(node.signature.output, "cardinality", None) != port.cardinality:
                raise ValueError("temporal output changes its input port sort")
            if not set(node.signature.inputs) <= allowed:
                raise ValueError("temporal output contains an undeclared context port")
        for function in (admissible, *(self.cocycles.resolve(k) for k in cocycles)):
            if not set(self.bits.resolve(function).signature.inputs) <= allowed:
                raise ValueError(
                    "temporal residual contains an undeclared context port"
                )
        residual_functions = tuple(self.cocycles.resolve(k) for k in cocycles)
        saturated, restricted_residuals = self.bits.complete_transform(
            ports, outputs, admissible, retained=residual_functions
        )
        return CocycleAction(
            saturated.ports,
            saturated.outputs,
            tuple(self.cocycles.intern(f) for f in restricted_residuals),
            saturated.admissible,
            events,
        )

    def primitive(
        self,
        ports: tuple[FinitePort, ...],
        outputs: tuple[FactoredFunctionID, ...],
        cocycles: tuple[ThresholdCocycleResidualID, ...],
        admissible: FactoredFunctionID,
    ) -> CocycleAction:
        result = self._normal_form(ports, outputs, cocycles, admissible, 1)
        self.primitive_successors += 1
        return result

    def _validate(self, action: CocycleAction) -> None:
        if type(action) is not CocycleAction:
            raise TypeError("temporal composition requires contextual actions")
        FunctionSignature(action.ports, BOOL)
        if type(action.events) is not int or action.events < 1:
            raise ValueError("invalid temporal event metadata")
        if (
            not action.ports
            or len(action.outputs) != len(action.ports)
            or not action.cocycles
        ):
            raise ValueError("incomplete contextual action")
        admitted = self.bits.resolve(action.admissible)
        if admitted.signature != FunctionSignature(action.ports, BOOL):
            raise ValueError("action admissibility has another context")
        for port, function in zip(action.ports, action.outputs, strict=True):
            node = self.bits.resolve(function)
            if (
                node.signature.inputs != action.ports
                or getattr(node.signature.output, "cardinality", None)
                != port.cardinality
            ):
                raise ValueError("action output has another complete interface")
            if node.valid != admitted.bits[0]:
                raise ValueError("action output has inconsistent definedness")
        for residual in action.cocycles:
            node = self.bits.resolve(self.cocycles.resolve(residual))
            if node.signature.inputs != action.ports or node.valid != admitted.bits[0]:
                raise ValueError(
                    "action cocycle has inconsistent context or definedness"
                )

    def audit_snapshot(self) -> CocycleTemporalAuditSnapshot:
        """Expose exact read-only cache bindings for resource forensics.

        This snapshot does not normalize actions, resolve handles, or update
        counters. The memo snapshots retain the exact registered containers.
        """
        return CocycleTemporalAuditSnapshot(
            ledger=self.ledger,
            bits=self.bits,
            cocycles=self.cocycles,
            primitive_successors=self.primitive_successors,
            temporal_compositions=self.temporal_compositions,
            temporal_composition_cache_hits=self.temporal_composition_cache_hits,
            composition_cache=self._composition_cache.audit_snapshot(),
            composition_seals=self._composition_seals.audit_snapshot(),
            composition_cache_identity=self._composition_cache,
            composition_seals_identity=self._composition_seals,
            next_composition_entry=self._next_composition_entry,
            composition_cache_limit=self._COMPOSITION_CACHE_LIMIT,
            root_fields=frozenset(vars(self)),
        )

    def audit_validate_action(self, action: CocycleAction) -> None:
        """Validate an existing action without changing counters or stores."""
        self._validate(action)

    def audit_validate_entry(
        self,
        key: CocycleCompositionKey,
        entry: CocycleCompositionEntry,
        seal: tuple[object, ...],
        next_entry_id: int,
    ) -> bool:
        """Check a retained row's exact binding without publishing any work."""
        if (
            type(key) is not CocycleCompositionKey
            or type(entry) is not CocycleCompositionEntry
            or type(entry.key) is not CocycleCompositionKey
            or type(entry.entry_id) is not int
            or type(next_entry_id) is not int
            or type(seal) is not tuple
            or type(entry.result) is not CocycleAction
            or type(entry.result.events) is not int
        ):
            return False
        if (
            entry.key != key
            or entry.entry_id < 0
            or entry.entry_id >= next_entry_id
            or not self._exact_equal(
                self._snapshot_key(entry.key), self._snapshot_key(key)
            )
            or not self._exact_equal(seal, self._entry_seal(entry))
            or entry.result.events != key.before_events + key.after_events
        ):
            return False
        before_action = CocycleAction(
            key.before_ports,
            key.before_outputs,
            key.before_cocycles,
            key.before_admissible,
            key.before_events,
        )
        after_action = CocycleAction(
            key.after_ports,
            key.after_outputs,
            key.after_cocycles,
            key.after_admissible,
            key.after_events,
        )
        self.audit_validate_action(before_action)
        self.audit_validate_action(after_action)
        self.audit_validate_action(entry.result)
        return True

    def saturated(self, action: CocycleAction) -> CompleteFiniteTransform:
        """Project complete finite functions, omitting event and cocycle identity.

        The action was already normalized against its retained cocycles. This
        projection does not assert source or recursive spatial admission.
        """
        self._validate(action)
        result = CompleteFiniteTransform(
            action.ports, action.outputs, action.admissible
        )
        self.bits.validate_complete_transform(result)
        return result

    def compose(self, before: CocycleAction, after: CocycleAction) -> CocycleAction:
        """Return NF(after ∘ before), including intermediate definedness."""
        self.ledger.bump("temporal_composition_requests")
        if type(before) is not CocycleAction or type(after) is not CocycleAction:
            raise TypeError("temporal composition requires contextual actions")
        self.ledger.bump("temporal_composition_validation_attempts")
        self._validate(before)
        self.ledger.bump("temporal_composition_validation_attempts")
        self._validate(after)
        if before.ports != after.ports:
            raise ValueError("temporal composition needs the same complete interface")
        key = CocycleCompositionKey(
            before.ports,
            before.outputs,
            before.cocycles,
            before.admissible,
            before.events,
            after.ports,
            after.outputs,
            after.cocycles,
            after.admissible,
            after.events,
        )
        cached = self._composition_cache.get(key)
        seal = self._composition_seals.get(key)
        if (cached is None) != (seal is None):
            raise ValueError("temporal composition cache publication is incomplete")
        if cached is not None and seal is not None:
            if type(cached) is not CocycleCompositionEntry or type(seal) is not tuple:
                raise ValueError("temporal composition cache payload is invalid")
            if type(cached.key) is not CocycleCompositionKey:
                raise ValueError("temporal composition cache key is invalid")
            if not self._exact_equal(
                self._snapshot_key(cached.key), self._snapshot_key(key)
            ):
                raise ValueError("temporal composition cache key is invalid")
            if (
                type(cached.entry_id) is not int
                or cached.entry_id < 0
                or cached.entry_id >= self._next_composition_entry
                or type(cached.result) is not CocycleAction
                or type(cached.result.events) is not int
            ):
                raise ValueError("temporal composition cache entry is invalid")
            if not self._exact_equal(seal, self._entry_seal(cached)):
                raise ValueError("temporal composition cache seal is invalid")
            if cached.result.events != before.events + after.events:
                raise ValueError("temporal composition cache chronology is invalid")
            self.ledger.bump("temporal_composition_validation_attempts")
            self._validate(cached.result)
            self.temporal_composition_cache_hits += 1
            return cached.result
        after_residuals = tuple(self.cocycles.resolve(k) for k in after.cocycles)
        saturated, retained = self.bits.compose_complete_transform(
            self.saturated(before),
            self.saturated(after),
            retained=after_residuals,
        )
        result = CocycleAction(
            saturated.ports,
            saturated.outputs,
            tuple(self.cocycles.intern(f) for f in retained),
            saturated.admissible,
            before.events + after.events,
        )
        if result.events != before.events + after.events:
            raise ValueError("temporal composition produced invalid chronology")
        entry = CocycleCompositionEntry(key, self._next_composition_entry, result)
        self._next_composition_entry += 1
        entry_seal = self._entry_seal(entry)
        if len(self._composition_cache) >= self._COMPOSITION_CACHE_LIMIT:
            oldest = next(iter(self._composition_cache))
            if oldest not in self._composition_seals:
                raise ValueError("temporal composition cache publication is incomplete")
            del self._composition_seals[oldest]
            del self._composition_cache[oldest]
        self._composition_seals[key] = entry_seal
        try:
            self._composition_cache[key] = entry
        except BaseException:
            del self._composition_seals[key]
            raise
        self.temporal_compositions += 1
        return result

    def nodes(self, functions: tuple[FactoredFunctionID, ...]) -> int:
        return len(
            {
                node
                for function in functions
                for root in (
                    *self.bits.resolve(function).bits,
                    self.bits.resolve(function).valid,
                )
                for node in self.bits.functions.iter_reachable(root)
            }
        )
