"""Transaction-owned Boolean circuits and their transient substitution workspace."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
    SemanticRequest,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.interfaces.boolean_composition import CompositionKey
from number_compiler.hashlife.interfaces.semantic_bit_records import (
    FactoredFunction,
    PendingFunction,
)
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)


class BooleanCircuit:
    def __init__(
        self,
        functions: SemanticFunctionArena,
        inputs: tuple[FinitePort, ...],
        transaction: _Transaction | None = None,
    ) -> None:
        if transaction is not None and transaction.arena is not functions:
            raise ValueError("circuit transaction belongs to another semantic arena")
        self.tx = _Transaction(functions) if transaction is None else transaction
        self.inputs = inputs
        self.signature = FunctionSignature(inputs, BOOL)
        self._admitted: int | None = None
        self._substitutions: dict[
            tuple[tuple[PortVariable, int], ...], dict[int, int]
        ] = {}
        self._substitution_entries = 0
        self._fused_substitutions: dict[CompositionKey, int] = {}
        self._fused_retained_bindings = 0
        self._fused_projections: dict[tuple[int, int], tuple[int, ...]] = {}
        self._fused_projection_slots = 0
        self._fused_splits: dict[
            tuple[int, ...], tuple[PortVariable, tuple[int, ...], tuple[int, ...]]
        ] = {}
        self._cofactor_circuits: dict[tuple[FinitePort, ...], BooleanCircuit] = {}
        self.zero = self.tx.terminal(self.signature, SemanticTerminal("atom", 0))
        self.one = self.tx.terminal(self.signature, SemanticTerminal("atom", 1))

    @property
    def admitted_root(self) -> int | None:
        """Return the already constructed root for this circuit's admission."""
        return self._admitted

    def choose(self, condition: int, yes: int, no: int) -> int:
        # Circuit predicates are total Boolean functions: invalid numeric
        # inputs live in a separate validity bit, never an invalid terminal.
        if condition == self.one:
            self.tx.arena.ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_CONSTANT_CHOICE_REDUCTIONS
            )
            return yes
        if condition == self.zero:
            self.tx.arena.ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_CONSTANT_CHOICE_REDUCTIONS
            )
            return no
        if yes == no:
            self.tx.arena.ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_EQUAL_BRANCH_REDUCTIONS
            )
            return yes
        # These identities apply to the circuit's total Boolean predicates.
        # Apply them before the general Shannon scheduler, whose partial
        # functions must retain their separate invalid-terminal semantics.
        if (yes == self.one or yes == condition) and no == self.zero:
            self.tx.arena.ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_BOOLEAN_IDENTITY_REDUCTIONS
            )
            return condition
        if yes == self.one and no == condition:
            self.tx.arena.ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_BOOLEAN_IDENTITY_REDUCTIONS
            )
            return condition
        if yes == self.zero and no == condition:
            self.tx.arena.ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_BOOLEAN_ABSORPTION_REDUCTIONS
            )
            return self.zero
        if yes == condition and no == self.one:
            self.tx.arena.ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_BOOLEAN_ABSORPTION_REDUCTIONS
            )
            return self.one
        return self.tx.choose(condition, yes, no)

    def join_branch(
        self, values: list[tuple[int, ...]], variable: PortVariable
    ) -> None:
        """Replace two completed cofactors by their common decision node."""
        high, low = values.pop(), values.pop()
        values.append(self.branch(variable, low, high))

    def branch(
        self, variable: PortVariable, low: tuple[int, ...], high: tuple[int, ...]
    ) -> tuple[int, ...]:
        return tuple(
            self.tx.decision(self.signature, variable, a, b)
            for a, b in zip(low, high, strict=True)
        )

    def negate(self, value: int) -> int:
        return self.choose(value, self.zero, self.one)

    def conjunction(self, first: int, second: int) -> int:
        return self.choose(first, second, self.zero)

    def xor(self, first: int, second: int) -> int:
        return self.choose(first, self.negate(second), second)

    def subtract_constant(
        self, bits: tuple[int, ...], value: int
    ) -> tuple[tuple[int, ...], int]:
        borrow = self.zero
        result: list[int] = []
        for bit, item in enumerate(bits):
            constant = (value >> bit) & 1
            parity = self.xor(item, borrow)
            result.append(self.negate(parity) if constant else parity)
            inverse = self.negate(item)
            borrow = (
                self.choose(inverse, self.one, borrow)
                if constant
                else self.conjunction(inverse, borrow)
            )
        return tuple(result), borrow

    def admitted(self) -> int:
        if self._admitted is not None:
            self.tx.arena.ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_ADMISSIBILITY_REUSES
            )
            return self._admitted
        arena = self.tx.arena
        request = SemanticRequest("bit-admissibility", (), self.inputs)
        arena.ledger.bump(_interfaces_keys.SEMANTIC_BIT_ADMISSIBILITY_REQUESTS)
        cached = arena.memo.get(request)
        if cached is not None:
            node = arena.resolve(cached)
            if node.signature != self.signature:
                raise ValueError("cached port admission has another signature")
            self._admitted = cached.local_id
            arena.ledger.bump(_interfaces_keys.SEMANTIC_BIT_ADMISSIBILITY_EARLY_HITS)
            return self._admitted
        arena.ledger.bump(_interfaces_keys.SEMANTIC_BIT_ADMISSIBILITY_EVALUATIONS)
        valid = self.one
        # Build the total padding predicate directly in variable order.  A
        # numeric subtraction also constructs all difference bits, although
        # admission needs only x < cardinality.  Reading the low bit reduces
        # that inequality to ceil(cardinality / 2) or floor(cardinality / 2)
        # on the remaining bits.  At each level there are at most two such
        # residual thresholds, independent of the port's finite cardinality.
        for port in reversed(self.inputs):
            if port.cardinality == 1 << port.bits:
                continue
            valid = self._admitted_port(port, valid)
        self._admitted = valid
        return valid

    def _admitted_port(self, port: FinitePort, success: int) -> int:
        ledger = self.tx.arena.ledger
        # At depth b only floor(C/2**b) and ceil(C/2**b) can occur.
        # Build those two residuals bottom-up using four bounded references,
        # instead of retaining a search stack and dictionary of thresholds.
        self.tx.reserve_workspace(entries=4)
        counter = "semantic_bit_admissibility_threshold_workspace_peak"
        ledger.bump(counter, max(0, 4 - ledger.counters.get(counter, 0)))
        lower, upper = self.zero, success
        try:
            for bit in range(port.bits - 1, -1, -1):
                next_floor = port.cardinality >> (bit + 1)
                floor = port.cardinality >> bit
                ceiling = (port.cardinality + (1 << bit) - 1) >> bit
                next_lower, next_upper = lower, upper
                for role, limit in ((0, floor), (1, ceiling)):
                    ledger.bump(
                        _interfaces_keys.SEMANTIC_BIT_ADMISSIBILITY_THRESHOLD_FRAMES
                    )
                    if limit <= 0:
                        value = self.zero
                    elif limit >= 1 << (port.bits - bit):
                        value = success
                    elif role and floor == ceiling:
                        value = next_lower
                        ledger.bump(
                            _interfaces_keys.SEMANTIC_BIT_ADMISSIBILITY_THRESHOLD_SHARED_HITS
                        )
                    else:
                        variable = PortVariable(
                            port.variable.time,
                            port.variable.side,
                            port.variable.role,
                            bit,
                        )
                        ledger.bump(
                            _interfaces_keys.SEMANTIC_BIT_ADMISSIBILITY_THRESHOLD_DECISIONS
                        )
                        value = self.tx.decision(
                            self.signature,
                            variable,
                            lower if (limit + 1) // 2 == next_floor else upper,
                            lower if limit // 2 == next_floor else upper,
                        )
                    if role:
                        next_upper = value
                    else:
                        next_lower = value
                lower, upper = next_lower, next_upper
            return lower
        finally:
            if self.tx.is_open:
                self.tx.release_workspace(entries=4)

    def imported(self, function: FactoredFunction) -> tuple[tuple[int, ...], int]:
        bits = tuple(
            self.tx.resign(bit.local_id, self.signature) for bit in function.bits
        )
        valid = self.tx.resign(function.valid.local_id, self.signature)
        return bits, valid

    def normalized(
        self, signature: FunctionSignature, bits: tuple[int, ...], valid: int
    ) -> PendingFunction:
        if (
            type(signature.output) is not AtomSort
            or len(bits) != (signature.output.cardinality - 1).bit_length()
        ):
            raise ValueError("factored output width does not match its sort")
        return PendingFunction(
            signature, tuple(self.conjunction(valid, bit) for bit in bits), valid
        )

    def substitute(self, root: int, replacements: Mapping[PortVariable, int]) -> int:
        """Simultaneous substitution shared across all roots in this self.

        The memo is transient, scoped to one immutable semantic transaction and
        complete substitution environment. It contains no source/coordinate keys.
        """
        transaction = self.tx
        ledger = transaction.arena.ledger
        key = tuple(sorted(replacements.items()))
        done = self._substitutions.setdefault(key, {})

        def retain(identity: int, value: int) -> None:
            done[identity] = value
            self._substitution_entries += 1

        pending = [(root, False)]
        changed = frozenset(replacements)
        while pending:
            ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_SUBSTITUTION_WORKSPACE_PEAK,
                max(
                    0,
                    len(pending)
                    + self._substitution_entries
                    - ledger.counters.get(
                        _interfaces_keys.SEMANTIC_BIT_SUBSTITUTION_WORKSPACE_PEAK,
                        0,
                    ),
                ),
            )
            current, ready = pending.pop()
            ledger.bump(_interfaces_keys.SEMANTIC_BIT_SUBSTITUTION_FRAMES)
            if current in done:
                ledger.bump(_interfaces_keys.SEMANTIC_BIT_SUBSTITUTION_SHARED_HITS)
                continue
            node = transaction.node(current)
            if node.signature == self.signature and not changed.intersection(
                node.support
            ):
                retain(current, current)
                ledger.bump(_interfaces_keys.SEMANTIC_BIT_SUBSTITUTION_UNCHANGED_ROOTS)
            elif node.terminal is not None:
                retain(current, transaction.terminal(self.signature, node.terminal))
            else:
                assert node.variable is not None
                condition = replacements.get(node.variable)
                if condition in (self.zero, self.one):
                    child = node.high if condition == self.one else node.low
                    if child in done:
                        retain(current, done[child])
                    else:
                        ledger.bump(
                            _interfaces_keys.SEMANTIC_BIT_SUBSTITUTION_COFACTOR_PRUNES
                        )
                        pending.extend(((current, True), (child, False)))
                elif ready:
                    if condition is None:
                        retain(
                            current,
                            transaction.rebuilt_decision(
                                self.signature,
                                node.variable,
                                done[node.low],
                                done[node.high],
                            ),
                        )
                    else:
                        retain(
                            current,
                            self.choose(condition, done[node.high], done[node.low]),
                        )
                else:
                    pending.extend(
                        ((current, True), (node.high, False), (node.low, False))
                    )
        return done[root]

    def substitute_fused(
        self, root: int, replacements: Mapping[PortVariable, int]
    ) -> int:
        """Compose correlated inputs by one ordered external-variable traversal.

        This cofactoring explores reduced function DAGs, never integer assignments
        or a Cartesian port universe. Only final ordered nodes are constructed.
        """
        tx, ledger = self.tx, self.tx.arena.ledger
        done = self._fused_substitutions

        def project(
            before: int, after: int, environment: tuple[int, ...]
        ) -> tuple[int, ...]:
            if before == after:
                return environment
            pair = before, after
            indices = self._fused_projections.get(pair)
            ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_REQUESTS)
            if indices is None:
                source, target = tx.node(before).support, tx.node(after).support
                selected: list[int] = []
                cursor = 0
                for variable in target:
                    while cursor < len(source) and source[cursor] < variable:
                        cursor += 1
                        ledger.bump(
                            _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_SUPPORT_VISITS
                        )
                    ledger.bump(
                        _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_SUPPORT_VISITS
                    )
                    if cursor == len(source) or source[cursor] != variable:
                        raise AssertionError(
                            "cofactor support must be a subset of its canonical parent"
                        )
                    selected.append(cursor)
                indices = tuple(selected)
                ledger.bump(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_BUILD_SLOTS_PEAK,
                    max(
                        0,
                        len(selected)
                        + len(indices)
                        - ledger.counters.get(
                            _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_BUILD_SLOTS_PEAK,
                            0,
                        ),
                    ),
                )
                self._fused_projections[pair] = indices
                self._fused_projection_slots += len(indices)
                ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_EVALUATIONS)
                ledger.bump(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_CACHE_ENTRIES_PEAK,
                    max(
                        0,
                        len(self._fused_projections)
                        - ledger.counters.get(
                            _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_CACHE_ENTRIES_PEAK,
                            0,
                        ),
                    ),
                )
                ledger.bump(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_INDEX_SLOTS_PEAK,
                    max(
                        0,
                        self._fused_projection_slots
                        - ledger.counters.get(
                            _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_INDEX_SLOTS_PEAK,
                            0,
                        ),
                    ),
                )
            else:
                ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_HITS)
            result = tuple(environment[index] for index in indices)
            ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_ARGUMENT_VISITS,
                len(indices),
            )
            ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_FUSED_ENVIRONMENT_BINDINGS_CREATED,
                len(result),
            )
            ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_FUSED_NORMALIZATION_BINDINGS_PEAK,
                max(
                    0,
                    len(environment)
                    + len(result)
                    - ledger.counters.get(
                        _interfaces_keys.SEMANTIC_BIT_FUSED_NORMALIZATION_BINDINGS_PEAK,
                        0,
                    ),
                ),
            )
            return result

        def normalized(identity: int, environment: tuple[int, ...]) -> CompositionKey:
            node = tx.node(identity)
            while node.variable is not None:
                # Ordered BDD nodes put their own split first in their support.
                argument = tx.node(environment[0])
                ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_NORMALIZATION_VISITS)
                ledger.bump(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_NORMALIZATION_BINDING_VISITS
                )
                if argument.terminal is None:
                    break
                if argument.terminal.kind != "atom":
                    raise AssertionError(
                        "factored argument bits must be total Boolean functions"
                    )
                child = node.high if argument.terminal.value else node.low
                environment = project(identity, child, environment)
                identity, node = child, tx.node(child)
            return CompositionKey(identity, environment)

        original = tx.node(root)
        constants = tuple(
            (variable, tx.node(value).terminal)
            for variable, value in replacements.items()
            if tx.node(value).terminal is not None
        )
        if constants:
            primitive = self._cofactor_circuits.get(original.signature.inputs)
            if primitive is None:
                primitive = BooleanCircuit(tx.arena, original.signature.inputs, tx)
                self._cofactor_circuits[original.signature.inputs] = primitive
                ledger.bump(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_COFACTOR_CONTEXTS_PEAK,
                    max(
                        0,
                        len(self._cofactor_circuits)
                        - ledger.counters.get(
                            _interfaces_keys.SEMANTIC_BIT_FUSED_COFACTOR_CONTEXTS_PEAK,
                            0,
                        ),
                    ),
                )
            constant_mapping: dict[PortVariable, int] = {}
            for variable, terminal in constants:
                if terminal is None or terminal.kind != "atom":
                    raise AssertionError(
                        "factored argument bits must be total Boolean functions"
                    )
                constant_mapping[variable] = (
                    primitive.one if terminal.value else primitive.zero
                )
            root = primitive.substitute(root, constant_mapping)
            original = tx.node(root)
        environment = tuple(
            replacements[variable]
            if variable in replacements
            else tx.bit(self.inputs, variable)
            for variable in original.support
        )
        ledger.bump(
            _interfaces_keys.SEMANTIC_BIT_FUSED_ENVIRONMENT_BINDINGS_CREATED,
            len(environment),
        )
        first = normalized(root, environment)
        pending = [(first, False)]
        children: dict[
            CompositionKey, tuple[PortVariable, CompositionKey, CompositionKey]
        ] = {}
        while pending:
            ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_FUSED_WORKSPACE_PEAK,
                max(
                    0,
                    len(pending)
                    + len(done)
                    + len(children)
                    - ledger.counters.get(
                        _interfaces_keys.SEMANTIC_BIT_FUSED_WORKSPACE_PEAK, 0
                    ),
                ),
            )
            ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_FUSED_RETAINED_ENVIRONMENT_BINDINGS_PEAK,
                max(
                    0,
                    self._fused_retained_bindings
                    - ledger.counters.get(
                        _interfaces_keys.SEMANTIC_BIT_FUSED_RETAINED_ENVIRONMENT_BINDINGS_PEAK,
                        0,
                    ),
                ),
            )
            key, ready = pending.pop()
            ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_FRAMES)
            if key in done:
                ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_SHARED_HITS)
                continue
            node = tx.node(key.root)
            if node.terminal is not None:
                done[key] = tx.terminal(self.signature, node.terminal)
                self._fused_retained_bindings += len(key.environment)
            elif ready:
                variable, low, high = children.pop(key)
                done[key] = tx.decision(self.signature, variable, done[low], done[high])
                self._fused_retained_bindings += len(key.environment)
            else:
                split = self._fused_splits.get(key.environment)
                ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_SPLIT_REQUESTS)
                if split is None:
                    arguments = tuple(tx.node(value) for value in key.environment)
                    ledger.bump(
                        _interfaces_keys.SEMANTIC_BIT_FUSED_BRANCH_NODE_REFERENCES_PEAK,
                        max(
                            0,
                            len(arguments)
                            - ledger.counters.get(
                                _interfaces_keys.SEMANTIC_BIT_FUSED_BRANCH_NODE_REFERENCES_PEAK,
                                0,
                            ),
                        ),
                    )
                    variable = min(
                        argument.variable
                        for argument in arguments
                        if argument.variable is not None
                    )
                    low_environment = tuple(
                        argument.low if argument.variable == variable else value
                        for value, argument in zip(
                            key.environment, arguments, strict=True
                        )
                    )
                    high_environment = tuple(
                        argument.high if argument.variable == variable else value
                        for value, argument in zip(
                            key.environment, arguments, strict=True
                        )
                    )
                    split = variable, low_environment, high_environment
                    self._fused_splits[key.environment] = split
                    ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_SPLIT_EVALUATIONS)
                    ledger.bump(
                        _interfaces_keys.SEMANTIC_BIT_FUSED_SPLIT_CACHE_ENTRIES_PEAK,
                        max(
                            0,
                            len(self._fused_splits)
                            - ledger.counters.get(
                                _interfaces_keys.SEMANTIC_BIT_FUSED_SPLIT_CACHE_ENTRIES_PEAK,
                                0,
                            ),
                        ),
                    )
                    ledger.bump(
                        _interfaces_keys.SEMANTIC_BIT_FUSED_ENVIRONMENT_BINDINGS_CREATED,
                        len(low_environment) + len(high_environment),
                    )
                    ledger.bump(
                        _interfaces_keys.SEMANTIC_BIT_FUSED_BRANCH_ENVIRONMENT_BINDINGS_PEAK,
                        max(
                            0,
                            len(key.environment)
                            + len(low_environment)
                            + len(high_environment)
                            - ledger.counters.get(
                                _interfaces_keys.SEMANTIC_BIT_FUSED_BRANCH_ENVIRONMENT_BINDINGS_PEAK,
                                0,
                            ),
                        ),
                    )
                else:
                    ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_SPLIT_HITS)
                variable, low_environment, high_environment = split
                low = normalized(key.root, low_environment)
                high = normalized(key.root, high_environment)
                children[key] = variable, low, high
                pending.extend(((key, True), (high, False), (low, False)))
        ledger.bump(
            _interfaces_keys.SEMANTIC_BIT_FUSED_RETAINED_ENVIRONMENT_BINDINGS_PEAK,
            max(
                0,
                self._fused_retained_bindings
                - ledger.counters.get(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_RETAINED_ENVIRONMENT_BINDINGS_PEAK,
                    0,
                ),
            ),
        )
        return done[first]
