"""Source-independent expression programs with at most three typed ports.

A call keeps its body opaque to outer binders.  Only its explicit arguments
participate in outer substitution; the body is instantiated on demand by the
shared evaluator.  This prevents parent construction from distributing every
higher temporal expression into every spatial child.
"""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
        BoundaryExpressionArena,
        ExpressionSort,
        ExprID,
    )


@dataclass(frozen=True, slots=True)
class ClosureProgramID(ArenaHandle):
    """One arena's complete typed expression program, not a bound result."""


@dataclass(frozen=True, slots=True)
class ClosureProgram:
    parameters: tuple[ExprID, ...]
    body: ExprID
    support: tuple[ExprID, ...]

    def __post_init__(self) -> None:
        from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID

        if (
            type(self.parameters) is not tuple
            or not 1 <= len(self.parameters) <= 3
            or len(set(self.parameters)) != len(self.parameters)
            or type(self.body) is not ExprID
            or self.body.kind != "diamond-boundary-expression"
            or type(self.support) is not tuple
            or len(set(self.support)) != len(self.support)
            or any(
                type(value) is not ExprID
                or value.owner is not self.body.owner
                or value.kind != self.body.kind
                for value in self.parameters + self.support
            )
            or any(value not in self.parameters for value in self.support)
        ):
            raise ValueError(
                "closure requires at most three scoped, distinct explicit ports"
            )


class ExpressionClosures:
    def __init__(self, expressions: BoundaryExpressionArena) -> None:
        self.expressions = expressions
        self.ledger = expressions.ledger
        self.ledger.register_execution_root(self)
        self.token = ArenaToken("diamond-expression-closures")
        prefix = f"diamond-expression-closures-{len(self.ledger.inventory())}"
        self.node_owner = self.ledger.register(
            prefix + "-nodes", "macro_transfer_program"
        )
        self.id_owner = self.ledger.register(
            prefix + "-ids", "macro_transfer_program_interner"
        )
        self.nodes: MutableSequence[ClosureProgram] = self.ledger.make_list(
            self.node_owner
        )
        self.ids: MutableMapping[ClosureProgram, ClosureProgramID] = (
            self.ledger.make_dict(self.id_owner)
        )

    def resolve(self, program: ClosureProgramID) -> ClosureProgram:
        if type(program) is not ClosureProgramID:
            raise ValueError("expected a scoped expression closure")
        program.validate(self.token, "diamond-expression-closure", size=len(self.nodes))
        return self.nodes[program.local_id]

    def result_sort(self, program: ClosureProgramID) -> ExpressionSort:
        return self.expressions.node(self.resolve(program).body).sort

    def intern(self, parameters: tuple[ExprID, ...], body: ExprID) -> ClosureProgramID:
        from number_compiler.hashlife.interfaces.diamond_boundary_expr import StateSort

        arena = self.expressions
        if (
            type(parameters) is not tuple
            or not 1 <= len(parameters) <= 3
            or len(set(parameters)) != len(parameters)
        ):
            raise ValueError(
                "closure arity must be between one and three distinct ports"
            )
        for parameter in parameters:
            node = arena.node(parameter)
            if node.kind != "port" or type(node.sort) is not StateSort:
                raise ValueError("closure parameters must be explicit state ports")
        arena.node(body)
        pending = [body.local_id]
        visited: set[int] = set()
        support: set[ExprID] = set()
        peak = frames = 0
        while pending:
            peak = max(peak, len(pending) + len(visited))
            index = pending.pop()
            frames += 1
            if index in visited:
                continue
            visited.add(index)
            node = arena.nodes[index]
            if node.kind == "port":
                reference = arena.scoped_handle(index)
                if reference not in parameters:
                    raise ValueError("closure body contains an undeclared free port")
                support.add(reference)
            pending.extend(node.children)
        canonical = tuple(
            arena.variable(arena.node(parameter).sort, f"closure-parameter-{index}")
            for index, parameter in enumerate(parameters)
        )
        normalized = arena.substitute(
            body, dict(zip(parameters, canonical, strict=True))
        )
        canonical_support = tuple(
            canonical[index]
            for index, parameter in enumerate(parameters)
            if parameter in support
        )
        record = ClosureProgram(canonical, normalized, canonical_support)
        # Failed admission has not changed any ledger counters or stores.
        self.ledger.bump(
            _execution_keys.EXPRESSION_CLOSURE_ADMISSION_VISITS,
            len(visited),
        )
        self.ledger.bump(
            _execution_keys.EXPRESSION_CLOSURE_ADMISSION_FRAME_VISITS,
            frames,
        )
        self.ledger.bump(
            _execution_keys.EXPRESSION_CLOSURE_ADMISSION_WORKSPACE_PEAK,
            max(
                0,
                peak
                - self.ledger.counters.get(
                    _execution_keys.EXPRESSION_CLOSURE_ADMISSION_WORKSPACE_PEAK,
                    0,
                ),
            ),
        )
        self.ledger.bump(_execution_keys.EXPRESSION_CLOSURE_INTERNER_REQUESTS)
        return self._publish(record)

    def intern_canonical(
        self,
        parameters: tuple[ExprID, ...],
        body: ExprID,
    ) -> ClosureProgramID:
        """Intern a closure whose formal ports are already canonical.

        Higher macrocell construction obtains its parameters from the stable
        ``HigherContextArena`` port constructors.  Re-alpha-normalizing those
        ports by substituting through the complete prior expression DAG made a
        chain of otherwise opaque macrocell calls quadratic in its retained
        syntax.  This entry point verifies the same closed-over-port contract
        from the expression node's bounded ``free_ports`` summary and publishes
        the existing body directly.

        Arbitrary callers continue to use :meth:`intern`, which performs full
        alpha normalization.  Keeping the two contracts separate prevents a
        caller-selected port name from becoming semantic identity here.
        """
        from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
            ExprID,
            FormalPort,
            StateSort,
        )

        if (
            type(parameters) is not tuple
            or not 1 <= len(parameters) <= 3
            or len(set(parameters)) != len(parameters)
            or type(body) is not ExprID
        ):
            raise ValueError(
                "canonical closure requires one to three distinct scoped ports"
            )
        parameter_ports: list[FormalPort] = []
        for parameter in parameters:
            node = self.expressions.node(parameter)
            if node.kind != "port" or type(node.sort) is not StateSort:
                raise ValueError("canonical closure parameters must be state ports")
            parameter_ports.append(node.free_ports[0])
        body_node = self.expressions.node(body)
        allowed = frozenset(parameter_ports)
        if any(port not in allowed for port in body_node.free_ports):
            raise ValueError("closure body contains an undeclared free port")
        support = tuple(
            parameter
            for parameter, port in zip(parameters, parameter_ports, strict=True)
            if port in body_node.free_ports
        )
        record = ClosureProgram(parameters, body, support)
        self.ledger.bump(_execution_keys.EXPRESSION_CLOSURE_CANONICAL_REQUESTS)
        self.ledger.bump(
            _execution_keys.EXPRESSION_CLOSURE_ADMISSION_VISITS,
            len(body_node.free_ports),
        )
        return self._publish(record)

    def _publish(self, record: ClosureProgram) -> ClosureProgramID:
        found = self.ids.get(record)
        if found is not None:
            self.ledger.bump(_execution_keys.EXPRESSION_CLOSURE_INTERNER_HITS)
            return found
        self.ledger.reserve_many(((self.node_owner, 1, 1), (self.id_owner, 1, 0)))
        result = ClosureProgramID(
            self.token, "diamond-expression-closure", len(self.nodes)
        )
        self.nodes.append(record)
        self.ids[record] = result
        self.ledger.bump(_execution_keys.EXPRESSION_CLOSURE_INTERNER_EVALUATIONS)
        return result

    def validate_arguments(
        self, program: ClosureProgramID, arguments: Sequence[ExprID]
    ) -> ClosureProgram:
        record = self.resolve(program)
        if len(arguments) != len(record.parameters):
            raise ValueError("closure argument arity disagrees")
        for parameter, argument in zip(record.parameters, arguments, strict=True):
            if (
                self.expressions.node(parameter).sort
                != self.expressions.node(argument).sort
            ):
                raise ValueError("closure argument has another state interface")
        return record

    def effective_arguments(
        self, program: ClosureProgramID, arguments: Sequence[ExprID]
    ) -> tuple[ExprID, ...]:
        record = self.validate_arguments(program, arguments)
        return tuple(
            arguments[record.parameters.index(parameter)]
            for parameter in record.support
        )

    def _effective(
        self, program: ClosureProgramID, arguments: Sequence[ExprID]
    ) -> ClosureProgram:
        record = self.resolve(program)
        if len(arguments) != len(record.support):
            raise ValueError("effective closure argument arity disagrees")
        for parameter, argument in zip(record.support, arguments, strict=True):
            if (
                self.expressions.node(parameter).sort
                != self.expressions.node(argument).sort
            ):
                raise ValueError(
                    "effective closure argument has another state interface"
                )
        return record

    def reduce_effective(
        self, program: ClosureProgramID, arguments: Sequence[ExprID]
    ) -> ExprID | None:
        record = self._effective(program, arguments)
        if not record.support:
            self.ledger.bump(_execution_keys.EXPRESSION_CLOSURE_CONSTANT_REDUCTIONS)
            return record.body
        if record.body in record.support:
            self.ledger.bump(_execution_keys.EXPRESSION_CLOSURE_IDENTITY_REDUCTIONS)
            return arguments[record.support.index(record.body)]
        node = self.expressions.node(record.body)
        if node.kind in ("anchor", "continuation", "finite_apply"):
            child = self.expressions.scoped_handle(node.children[0])
            if child in record.support:
                argument = arguments[record.support.index(child)]
                self.ledger.bump(
                    _execution_keys.EXPRESSION_CLOSURE_PROJECTION_REDUCTIONS
                )
                if node.kind == "anchor":
                    return self.expressions.anchor(argument)
                if node.kind == "continuation":
                    return self.expressions.continuation(argument)
                from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
                    StateSort,
                )

                assert isinstance(node.sort, StateSort) and node.function is not None
                return self.expressions.finite_apply(
                    node.sort.action, node.sort.side, node.function, argument
                )
        return None

    def reduction(
        self, program: ClosureProgramID, arguments: Sequence[ExprID]
    ) -> ExprID | None:
        return self.reduce_effective(
            program, self.effective_arguments(program, arguments)
        )

    def expand(self, program: ClosureProgramID, arguments: Sequence[ExprID]) -> ExprID:
        record = self._effective(program, arguments)
        self.ledger.bump(_execution_keys.EXPRESSION_CLOSURE_INSTANTIATIONS)
        return self.expressions.substitute(
            record.body, dict(zip(record.support, arguments, strict=True))
        )

    def instantiate(
        self, program: ClosureProgramID, arguments: Sequence[ExprID]
    ) -> ExprID:
        return self.expand(program, self.effective_arguments(program, arguments))
