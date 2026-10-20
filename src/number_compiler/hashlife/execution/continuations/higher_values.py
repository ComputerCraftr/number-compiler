"""Ledger-owned runtime values for higher boundary observations."""

from __future__ import annotations

from collections.abc import Callable, MutableMapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING, Literal, TypeAlias, cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_audit_views import (
        RuntimeValueAuditSnapshot,
    )
    from number_compiler.hashlife.execution.continuations.higher_summaries import (
        HigherSummaryID,
    )
    from number_compiler.hashlife.execution.continuations.higher_types import (
        HigherActionSchema,
        HigherFunction,
        HigherFunctionID,
    )


@dataclass(frozen=True, slots=True)
class RuntimeValueID(ArenaHandle):
    """Scoped canonical structured value produced during observation."""


RuntimeAtom: TypeAlias = int | RuntimeValueID


@dataclass(frozen=True, slots=True)
class RuntimeEnvironment:
    bindings: tuple[tuple[int, RuntimeAtom], ...]


@dataclass(frozen=True, slots=True)
class RuntimeFunction:
    function: HigherFunctionID
    environment: int


@dataclass(frozen=True, slots=True)
class RuntimeActionFunction:
    """Constant-size continuation of a composed concrete field state."""

    kind: Literal["constant", "step"]
    action: FieldCellActionID
    side: int
    anchor: RuntimeAtom
    continuation: RuntimeValueID | None
    symbol: int


@dataclass(frozen=True, slots=True)
class RuntimeTableFunction:
    """Extensional continuation over one bounded primitive state domain.

    This is used only for a composition whose two children are primitive.
    Keeping the complete finite function here removes derivation-sensitive
    ``RuntimeActionFunction`` chains at the bottom temporal diamond without
    attempting to enumerate a recursively composed wreath-product domain.
    """

    action: FieldCellActionID
    side: int
    outputs: tuple[int, ...]

    def apply(self, argument: RuntimeAtom) -> RuntimeAtom:
        if type(argument) is not int or not 0 <= argument < len(self.outputs):
            raise ValueError("bounded function argument is outside its domain")
        return self.outputs[argument]


@dataclass(frozen=True, slots=True)
class RuntimeTransferredState:
    """A canonical K-summary applied to an as-yet unexpanded boundary."""

    summary: HigherSummaryID
    incoming: RuntimeAtom


@dataclass(frozen=True, slots=True)
class RuntimeContextState:
    """A canonical U-summary with concrete ports bound only by reference."""

    summary: HigherSummaryID
    left: RuntimeAtom
    right: RuntimeAtom
    incoming: RuntimeAtom
    side: int


@dataclass(frozen=True, slots=True)
class RuntimeSummaryFunction:
    """Continuation produced by temporal K decomposition.

    The outer boundary remains in ``anchor`` and the argument is supplied only
    when a downstream observation crosses this interface.
    """

    context: HigherSummaryID
    opposite: HigherSummaryID
    side: int
    anchor: RuntimeAtom
    continuation: RuntimeValueID


@dataclass(frozen=True, slots=True)
class RuntimePair:
    anchor: RuntimeAtom
    continuation: RuntimeValueID


RuntimeRecord: TypeAlias = (
    RuntimeFunction
    | RuntimeActionFunction
    | RuntimeTableFunction
    | RuntimeTransferredState
    | RuntimeContextState
    | RuntimeSummaryFunction
    | RuntimePair
)


class RuntimeValueArena:
    """Canonical evictable query values with monotonic, non-recycled IDs."""

    _KIND = "higher-runtime-value"

    def __init__(
        self, ledger: ResourceLedger, schema: HigherActionSchema | None = None
    ) -> None:
        if schema is not None and schema.ledger is not ledger:
            raise ValueError("runtime values require their index schema")
        self.schema = schema
        self.ledger = ledger
        self.owner = ArenaToken("higher-runtime-values")
        ledger.register_execution_root(self)
        prefix = f"higher-runtime-values-{len(ledger.inventory())}"
        self._record_owner = ledger.register(
            prefix + "-records", "runtime_query_state_memo"
        )
        self._key_owner = ledger.register(prefix + "-keys", "query_memo")
        self._environment_owner = ledger.register(
            prefix + "-environments", "runtime_query_environment_memo"
        )
        self._environment_key_owner = ledger.register(
            prefix + "-environment-keys", "query_memo"
        )
        self._memo_owner = ledger.register(prefix + "-evaluations", "query_memo")
        self._operation_owner = ledger.register(
            prefix + "-operation-values", "runtime_operation_memo"
        )
        self._projection_owner = ledger.register(
            prefix + "-environment-projections",
            "query_memo",
        )
        self._projection_pattern_owner = ledger.register(
            prefix + "-projection-patterns",
            "query_memo",
        )
        self._records: MutableMapping[int, RuntimeRecord] = ledger.make_dict(
            self._record_owner
        )
        self._keys: MutableMapping[RuntimeRecord, int] = ledger.make_dict(
            self._key_owner
        )
        self._environments: MutableMapping[int, RuntimeEnvironment] = ledger.make_dict(
            self._environment_owner,
        )
        self._environment_keys: MutableMapping[RuntimeEnvironment, int] = (
            ledger.make_dict(
                self._environment_key_owner,
            )
        )
        self.evaluations: MutableMapping[tuple[int, int], RuntimeAtom] = (
            ledger.make_dict(
                self._memo_owner,
            )
        )
        self.operations: MutableMapping[tuple[object, ...], RuntimeAtom] = (
            ledger.make_dict(
                self._operation_owner,
            )
        )
        self._projections: MutableMapping[tuple[int, int], int] = ledger.make_dict(
            self._projection_owner
        )
        self._projection_patterns: MutableMapping[tuple[int, ...], int] = (
            ledger.make_dict(self._projection_pattern_owner)
        )
        ledger.register_container(
            self._record_owner,
            self._records,
            payloads=self._records.items,
            node_count=lambda: len(self._records),
            evict=self.clear,
        )
        ledger.register_container(
            self._key_owner, self._keys, payloads=self._keys.items
        )
        ledger.register_container(
            self._environment_owner,
            self._environments,
            node_count=lambda: len(self._environments),
            payloads=self._environments.items,
        )
        ledger.register_container(
            self._environment_key_owner,
            self._environment_keys,
            payloads=self._environment_keys.items,
        )
        ledger.register_container(
            self._memo_owner,
            self.evaluations,
            payloads=self.evaluations.items,
        )
        ledger.register_container(
            self._operation_owner,
            self.operations,
            payloads=self.operations.items,
        )
        ledger.register_container(
            self._projection_owner,
            self._projections,
            payloads=self._projections.items,
        )
        ledger.register_container(
            self._projection_pattern_owner,
            self._projection_patterns,
            payloads=self._projection_patterns.items,
        )
        self._next_value = 0
        self._next_environment = 0
        self._function_validate: Callable[[HigherFunctionID], object] | None = None
        self._summary_validate: Callable[[HigherSummaryID], object] | None = None

    def bind_function_validator(
        self,
        validate: Callable[[HigherFunctionID], object],
    ) -> None:
        if not callable(validate):
            raise TypeError("runtime function validation requires a callable")
        if self._function_validate not in (None, validate):
            raise ValueError("runtime values already use another semantic arena")
        self._function_validate = validate

    def value_id(self, local_id: int) -> RuntimeValueID:
        """Return an allocated runtime-value ID for an exact local index."""
        if (
            type(local_id) is not int
            or not 0 <= local_id < self._next_value
            or local_id not in self._records
        ):
            raise IndexError("runtime value index is outside the arena")
        return RuntimeValueID(self.owner, self._KIND, local_id)

    def audit_snapshot(self) -> RuntimeValueAuditSnapshot:
        """Expose immutable views of retained values and their exact stores."""
        from number_compiler.hashlife.execution.continuations.higher_audit_views import (
            RuntimeValueAuditSnapshot,
        )

        return RuntimeValueAuditSnapshot(
            ledger=self.ledger,
            owner=self.owner,
            record_owner=self._record_owner,
            records=MappingProxyType(self._records),
            record_store=self._records,
            key_owner=self._key_owner,
            keys=MappingProxyType(self._keys),
            key_store=self._keys,
            environment_owner=self._environment_owner,
            environments=MappingProxyType(self._environments),
            environment_store=self._environments,
            environment_key_owner=self._environment_key_owner,
            environment_keys=MappingProxyType(self._environment_keys),
            environment_key_store=self._environment_keys,
            memo_owner=self._memo_owner,
            evaluations=MappingProxyType(self.evaluations),
            evaluation_store=self.evaluations,
            operation_owner=self._operation_owner,
            operations=MappingProxyType(self.operations),
            operation_store=self.operations,
            projection_owner=self._projection_owner,
            projections=MappingProxyType(self._projections),
            projection_store=self._projections,
            projection_pattern_owner=self._projection_pattern_owner,
            projection_patterns=MappingProxyType(self._projection_patterns),
            projection_pattern_store=self._projection_patterns,
        )

    def validate_function(self, function: HigherFunctionID) -> None:
        from number_compiler.hashlife.execution.continuations.higher_types import (
            HigherFunctionID,
        )

        if type(function) is not HigherFunctionID:
            raise TypeError("runtime function requires a scoped semantic function")
        if self._function_validate is None:
            raise RuntimeError("runtime function validation is not configured")
        self._function_validate(function)

    def bind_summary_validator(
        self,
        validate: Callable[[HigherSummaryID], object],
    ) -> None:
        if not callable(validate):
            raise TypeError("runtime summary validation requires a callable")
        if self._summary_validate not in (None, validate):
            raise ValueError("runtime values already use another summary arena")
        self._summary_validate = validate

    def validate_summary(
        self,
        summary: HigherSummaryID,
        *,
        kind: Literal["unary", "context"] | None = None,
    ) -> object:
        from number_compiler.hashlife.execution.continuations.higher_summaries import (
            HigherSummaryID,
            RuntimeContextSummary,
            RuntimeUnarySummary,
        )

        if type(summary) is not HigherSummaryID:
            raise TypeError("runtime summary value requires a scoped summary ID")
        if self._summary_validate is None:
            raise RuntimeError("runtime summary validation is not configured")
        record = self._summary_validate(summary)
        if kind == "unary" and type(record) is not RuntimeUnarySummary:
            raise ValueError("runtime transfer requires a unary summary")
        if kind == "context" and type(record) is not RuntimeContextSummary:
            raise ValueError("runtime context requires a context summary")
        return record

    def validate_action_atom(
        self,
        action: FieldCellActionID,
        side: int,
        atom: RuntimeAtom,
    ) -> None:
        """Validate a concrete or deferred value against one action port sort."""
        from number_compiler.hashlife.execution.continuations.higher_summaries import (
            RuntimeContextSummary,
            RuntimeUnarySummary,
        )
        from number_compiler.hashlife.execution.continuations.higher_types import (
            FieldFunctionSort,
            FieldStateSort,
        )

        if self.schema is None:
            raise ValueError("action state validation requires a bound schema")
        if type(side) is not int or side not in (0, 1):
            raise TypeError("action state validation requires a direction")
        pending = [(action, side, atom)]
        seen: set[RuntimeValueID] = set()
        while pending:
            current, current_side, current_atom = pending.pop()
            self.schema.validate_action(current)
            self.validate_atom(current_atom)
            children = self.schema.children(current)
            if type(current_atom) is int:
                if children is not None:
                    raise ValueError(
                        "composed action state requires a structured value"
                    )
                count = self.schema.state_count(current, current_side)
                if type(count) is not int or not 1 <= count <= 1 << 64:
                    raise ValueError("action state has an invalid primitive sort")
                if not 0 <= current_atom < count:
                    raise ValueError("action state is outside its primitive sort")
                continue
            reference = cast(RuntimeValueID, current_atom)
            if reference in seen:
                raise ValueError("action state contains a cyclic anchor")
            seen.add(reference)
            record = self.resolve(reference)
            if type(record) is RuntimeTransferredState:
                summary = self.validate_summary(record.summary, kind="unary")
                if type(summary) is not RuntimeUnarySummary or (
                    summary.action,
                    summary.side,
                ) != (current, current_side):
                    raise ValueError("deferred transfer has another boundary sort")
                continue
            if type(record) is RuntimeContextState:
                summary = self.validate_summary(record.summary, kind="context")
                if type(summary) is not RuntimeContextSummary or (
                    summary.consumer,
                    record.side,
                ) != (current, current_side):
                    raise ValueError("deferred context has another boundary sort")
                continue
            if children is None or type(record) is not RuntimePair:
                raise ValueError("action state is outside its declared port sort")
            pending.append((children[0], current_side, record.anchor))
            function = self.resolve(record.continuation)
            if type(function) is RuntimeActionFunction:
                if (function.action, function.side) != (current, current_side):
                    raise ValueError("pair continuation has another boundary sort")
                continue
            if type(function) is RuntimeTableFunction:
                if (function.action, function.side) != (current, current_side):
                    raise ValueError("pair continuation has another boundary sort")
                continue
            if type(function) is RuntimeSummaryFunction:
                context = self.validate_summary(function.context, kind="context")
                opposite = self.validate_summary(function.opposite, kind="unary")
                if (
                    type(context) is not RuntimeContextSummary
                    or type(opposite) is not RuntimeUnarySummary
                    or (context.provider, context.consumer) != children
                    or (opposite.action, opposite.side)
                    != (children[0], 1 - current_side)
                    or function.side != current_side
                ):
                    raise ValueError("summary continuation has another boundary sort")
                continue
            if type(function) is RuntimeFunction:
                syntax = self._validate_function_record(function.function)
                expected_signature = FieldFunctionSort(
                    FieldStateSort(children[0], 1 - current_side),
                    FieldStateSort(children[1], current_side),
                )
                if syntax.signature != expected_signature:
                    raise ValueError("syntax continuation has another boundary sort")
                continue
            raise ValueError("pair continuation is not an admitted function")

    def _validate_function_record(self, function: HigherFunctionID) -> HigherFunction:
        from number_compiler.hashlife.execution.continuations.higher_types import (
            HigherFunction,
        )

        self.validate_function(function)
        if self._function_validate is None:
            raise RuntimeError("runtime function validation is not configured")
        record = self._function_validate(function)
        if type(record) is not HigherFunction:
            raise ValueError("runtime function validator returned another record")
        return record

    def clear(self) -> None:
        counts = (
            (self._record_owner, len(self._records), True),
            (self._key_owner, len(self._keys), False),
            (self._environment_owner, len(self._environments), True),
            (self._environment_key_owner, len(self._environment_keys), False),
            (self._memo_owner, len(self.evaluations), False),
            (self._operation_owner, len(self.operations), False),
            (self._projection_owner, len(self._projections), False),
            (self._projection_pattern_owner, len(self._projection_patterns), False),
        )
        self._records.clear()
        self._keys.clear()
        self._environments.clear()
        self._environment_keys.clear()
        self.evaluations.clear()
        self.operations.clear()
        self._projections.clear()
        self._projection_patterns.clear()
        for owner, count, owns_nodes in counts:
            self.ledger.release(
                owner,
                entries=count,
                nodes=count if owns_nodes else 0,
            )

    def intern_record(self, record: RuntimeRecord) -> RuntimeValueID:
        found = self._keys.get(record)
        if found is not None:
            return RuntimeValueID(self.owner, self._KIND, found)
        self.ledger.reserve_many(((self._record_owner, 1, 1), (self._key_owner, 1, 0)))
        local_id = self._next_value
        self._next_value += 1
        self._records[local_id] = record
        self._keys[record] = local_id
        return RuntimeValueID(self.owner, self._KIND, local_id)

    def function(self, function: HigherFunctionID, environment: int) -> RuntimeValueID:
        from number_compiler.hashlife.execution.continuations.higher_types import (
            HigherFunctionID,
        )

        if type(function) is not HigherFunctionID or type(environment) is not int:
            raise TypeError(
                "runtime function requires scoped syntax and environment IDs"
            )
        if environment < -1:
            raise ValueError("runtime function has an invalid empty environment")
        self.validate_function(function)
        if environment >= 0:
            self.environment(environment)
        return self.intern_record(RuntimeFunction(function, environment))

    def action_function(
        self,
        kind: Literal["constant", "step"],
        action: FieldCellActionID,
        side: int,
        anchor: RuntimeAtom,
        continuation: RuntimeValueID | None,
        symbol: int,
    ) -> RuntimeValueID:
        from number_compiler.hashlife.actions.field_actions import FieldCellActionID

        if (
            type(kind) is not str
            or kind not in ("constant", "step")
            or type(action) is not FieldCellActionID
            or type(side) is not int
            or side not in (0, 1)
            or type(symbol) is not int
        ):
            raise TypeError("runtime action continuation has invalid metadata")
        if self.schema is None:
            raise ValueError("action continuations require a bound schema")
        self.schema.validate_action(action)
        children = self.schema.children(action)
        if children is None:
            raise ValueError("action continuations require a composed action")
        self.validate_atom(anchor)
        if kind == "constant":
            if continuation is not None or symbol != -1:
                raise ValueError("constant continuation has step metadata")
            expected = children[1]
        else:
            _base, blank = self.schema.alphabet(action)
            if (
                type(continuation) is not RuntimeValueID
                or type(blank) is not int
                or not 0 <= symbol <= blank
            ):
                raise ValueError("step continuation has invalid input metadata")
            function = self.resolve(continuation)
            if type(function) not in (
                RuntimeFunction,
                RuntimeActionFunction,
                RuntimeTableFunction,
                RuntimeSummaryFunction,
            ):
                raise ValueError("step continuation does not reference a function")
            expected = children[0]
        self.validate_action_atom(expected, side, anchor)
        self.ledger.bump(_execution_keys.HIGHER_ACTION_CONTINUATION_REQUESTS)
        return self.intern_record(
            RuntimeActionFunction(
                kind,
                action,
                side,
                anchor,
                continuation,
                symbol,
            )
        )

    def table_function(
        self,
        action: FieldCellActionID,
        side: int,
        outputs: tuple[int, ...],
    ) -> RuntimeValueID:
        """Intern one complete primitive-domain continuation."""
        from number_compiler.hashlife.actions.field_actions import FieldCellActionID

        if (
            type(action) is not FieldCellActionID
            or type(side) is not int
            or side not in (0, 1)
            or type(outputs) is not tuple
            or not outputs
            or any(type(value) is not int for value in outputs)
        ):
            raise TypeError("runtime table function has invalid bounded semantics")
        if self.schema is None:
            raise ValueError("finite continuations require a bound schema")
        self.schema.validate_action(action)
        children = self.schema.children(action)
        if children is None or any(
            self.schema.children(child) is not None for child in children
        ):
            raise ValueError("finite continuations require primitive temporal children")
        domain = self.schema.state_count(children[0], 1 - side)
        codomain = self.schema.state_count(children[1], side)
        if (
            type(domain) is not int
            or type(codomain) is not int
            or not 1 <= domain <= 64
            or not 1 <= codomain <= 1 << 64
            or len(outputs) != domain
            or any(not 0 <= value < codomain for value in outputs)
        ):
            raise ValueError("finite continuation has another bounded port domain")
        return self.intern_record(RuntimeTableFunction(action, side, outputs))

    def transferred_state(
        self,
        summary: HigherSummaryID,
        incoming: RuntimeAtom,
    ) -> RuntimeValueID:
        self.validate_summary(summary, kind="unary")
        self.validate_atom(incoming)
        return self.intern_record(
            RuntimeTransferredState(
                summary,
                self.canonical_atom(incoming),
            )
        )

    def context_state(
        self,
        summary: HigherSummaryID,
        left: RuntimeAtom,
        right: RuntimeAtom,
        incoming: RuntimeAtom,
        side: int,
    ) -> RuntimeValueID:
        self.validate_summary(summary, kind="context")
        if type(side) is not int or side not in (0, 1):
            raise TypeError("context state requires a scoped U summary and direction")
        for value in (left, right, incoming):
            self.validate_atom(value)
        return self.intern_record(
            RuntimeContextState(
                summary,
                self.canonical_atom(left),
                self.canonical_atom(right),
                self.canonical_atom(incoming),
                side,
            )
        )

    def summary_function(
        self,
        context: HigherSummaryID,
        opposite: HigherSummaryID,
        side: int,
        anchor: RuntimeAtom,
        continuation: RuntimeValueID,
    ) -> RuntimeValueID:
        self.validate_summary(context, kind="context")
        self.validate_summary(opposite, kind="unary")
        if type(side) is not int or side not in (0, 1):
            raise TypeError("summary continuation has invalid metadata")
        self.validate_atom(anchor)
        self.resolve(continuation)
        return self.intern_record(
            RuntimeSummaryFunction(
                context,
                opposite,
                side,
                self.canonical_atom(anchor),
                continuation,
            )
        )

    def pair(self, anchor: RuntimeAtom, continuation: RuntimeValueID) -> RuntimeValueID:
        self.validate_atom(anchor)
        function = self.resolve(continuation)
        if type(function) not in (
            RuntimeFunction,
            RuntimeActionFunction,
            RuntimeTableFunction,
            RuntimeSummaryFunction,
        ):
            raise ValueError("runtime pair continuation is not a function")
        return self.intern_record(
            RuntimePair(self.canonical_atom(anchor), continuation)
        )

    def resolve(self, value: RuntimeValueID) -> RuntimeRecord:
        if type(value) is not RuntimeValueID:
            raise TypeError("expected a scoped higher runtime value")
        value.validate(self.owner, self._KIND, size=self._next_value)
        try:
            return self._records[value.local_id]
        except KeyError as exc:
            raise ValueError("stale higher runtime value") from exc

    def validate_atom(self, value: RuntimeAtom) -> None:
        if type(value) is int:
            return
        if type(value) is RuntimeValueID:
            self.resolve(value)
            return
        raise TypeError("higher runtime atoms are integers or scoped value IDs")

    def canonical_atom(self, value: RuntimeAtom) -> RuntimeAtom:
        """Use an already resolved boundary before publishing another binding."""
        self.validate_atom(value)
        if type(value) is RuntimeValueID:
            resolved = self.operations.get(("force", value))
            if resolved is not None:
                self.validate_atom(resolved)
                self.ledger.bump(_execution_keys.HIGHER_BOUNDARY_RESOLUTION_HITS)
                return resolved
        return value

    def intern_environment(self, parent: int, binding: int, value: RuntimeAtom) -> int:
        if (
            type(parent) is not int
            or type(binding) is not int
            or min(parent, binding) < -1
        ):
            raise ValueError("invalid higher runtime environment key")
        if parent >= 0:
            existing = self.environment(parent).bindings
        else:
            existing = ()
        self.validate_atom(value)
        bindings = dict(existing)
        bindings[binding] = value
        return self._intern_environment(tuple(sorted(bindings.items())))

    def _intern_environment(
        self,
        bindings: tuple[tuple[int, RuntimeAtom], ...],
    ) -> int:
        if not bindings:
            return -1
        record = RuntimeEnvironment(bindings)
        found = self._environment_keys.get(record)
        if found is not None:
            return found
        self.ledger.reserve_many(
            (
                (self._environment_owner, 1, 1),
                (self._environment_key_owner, 1, 0),
            )
        )
        local_id = self._next_environment
        self._next_environment += 1
        self._environments[local_id] = record
        self._environment_keys[record] = local_id
        return local_id

    def environment(self, local_id: int) -> RuntimeEnvironment:
        if type(local_id) is not int or local_id < 0:
            raise ValueError("invalid higher runtime environment ID")
        try:
            return self._environments[local_id]
        except KeyError as exc:
            raise ValueError("stale higher runtime environment") from exc

    def lookup(self, environment: int, binding: int) -> RuntimeAtom | None:
        if environment < 0:
            return None
        for candidate, value in self.environment(environment).bindings:
            if candidate == binding:
                return value
        return None

    def project_environment(
        self,
        environment: int,
        bindings: tuple[int, ...],
        *,
        projection: int | None = None,
    ) -> int:
        """Discard bindings irrelevant to an expression's exact free ports."""
        if type(bindings) is not tuple or any(
            type(value) is not int for value in bindings
        ):
            raise TypeError("higher environment projection requires integer bindings")
        if environment < 0 or not bindings:
            return -1
        if projection is not None and type(projection) is not int:
            raise TypeError("higher environment projection ID must be exact")
        pattern = self._projection_patterns.get(bindings)
        if pattern is None:
            self.ledger.reserve(self._projection_pattern_owner, entries=1)
            pattern = len(self._projection_patterns)
            self._projection_patterns[bindings] = pattern
        key = environment, pattern
        cached = self._projections.get(key)
        if cached is not None:
            return cached
        wanted = set(bindings)
        current = self.environment(environment).bindings
        selected = tuple(item for item in current if item[0] in wanted)
        result = (
            environment
            if len(selected) == len(current)
            else self._intern_environment(selected)
        )
        self.ledger.reserve(self._projection_owner, entries=1)
        self._projections[key] = result
        return result

    def publish_evaluation(
        self,
        expression: int,
        environment: int,
        value: RuntimeAtom,
    ) -> None:
        self.validate_atom(value)
        key = expression, environment
        if key in self.evaluations:
            return
        self.ledger.reserve(self._memo_owner, entries=1)
        self.evaluations[key] = value

    def publish_operation(self, key: tuple[object, ...], value: RuntimeAtom) -> None:
        self.validate_atom(value)
        if key in self.operations:
            return
        self.ledger.reserve(self._operation_owner, entries=1)
        self.operations[key] = value


__all__ = [
    "RuntimeActionFunction",
    "RuntimeAtom",
    "RuntimeContextState",
    "RuntimeEnvironment",
    "RuntimeFunction",
    "RuntimePair",
    "RuntimeSummaryFunction",
    "RuntimeTableFunction",
    "RuntimeTransferredState",
    "RuntimeValueArena",
    "RuntimeValueID",
]
