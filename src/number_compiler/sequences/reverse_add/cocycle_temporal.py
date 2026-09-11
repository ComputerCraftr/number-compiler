"""Exact contextual temporal composition without primitive successor replay.

A finite interface includes all changing value, domain and extent ports.
Composition substitutes their output functions simultaneously and pulls back
admissibility. It never enumerates a trajectory or materializes midpoint values.
This bounded interface algebra does not discover a recursive spatial interface.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
)
from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID
from number_compiler.sequences.reverse_add.threshold_cocycle import (
    ThresholdCocycleArena,
    ThresholdCocycleResidualID,
)


@dataclass(frozen=True, slots=True)
class CocycleAction:
    ports: tuple[FinitePort, ...]
    outputs: tuple[FactoredFunctionID, ...]
    cocycles: tuple[ThresholdCocycleResidualID, ...]
    admissible: FactoredFunctionID
    events: int = field(compare=False)


class CocycleTemporalArena:
    def __init__(self, cocycles: ThresholdCocycleArena) -> None:
        if type(cocycles) is not ThresholdCocycleArena:
            raise TypeError("temporal cocycles require their semantic arena")
        self.cocycles = cocycles
        self.bits = cocycles.bits
        self.primitive_successors = 0
        self.temporal_compositions = 0

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
        false = self.bits.constant(FunctionSignature((), BOOL), 0)
        full = self.bits.constant(FunctionSignature(ports, BOOL), 1)
        admissible = self.bits.select(full, admissible, false)
        for function in (*outputs, *(self.cocycles.resolve(k) for k in cocycles)):
            admissible = self.bits.select(
                admissible, self.bits.domain_predicate(function), false
            )
        return CocycleAction(
            ports,
            tuple(self.bits.restrict(f, admissible) for f in outputs),
            tuple(self.cocycles.restrict(k, admissible) for k in cocycles),
            admissible,
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

    def compose(self, before: CocycleAction, after: CocycleAction) -> CocycleAction:
        """Return NF(after ∘ before), including intermediate definedness."""
        if type(before) is not CocycleAction or type(after) is not CocycleAction:
            raise TypeError("temporal composition requires contextual actions")
        self._validate(before)
        self._validate(after)
        if before.ports != after.ports:
            raise ValueError("temporal composition needs the same complete interface")
        mapping = dict(
            zip((p.variable for p in before.ports), before.outputs, strict=True)
        )

        # Restrict mappings to actual signatures: dropped ports must not be
        # silently reintroduced as independent midpoint variables.
        def pull(function: FactoredFunctionID) -> FactoredFunctionID:
            inputs = self.bits.resolve(function).signature.inputs
            return self.bits.substitute(
                function, {p.variable: mapping[p.variable] for p in inputs}
            )

        admitted_after = pull(after.admissible)
        false = self.bits.constant(FunctionSignature((), BOOL), 0)
        admissible = self.bits.select(before.admissible, admitted_after, false)
        outputs = tuple(pull(f) for f in after.outputs)
        residuals = []
        for k in after.cocycles:
            inputs = self.bits.resolve(self.cocycles.resolve(k)).signature.inputs
            residuals.append(
                self.cocycles.compose_temporal(
                    k,
                    {p.variable: mapping[p.variable] for p in inputs},
                    before.cocycles[0],
                )
            )
        result = self._normal_form(
            before.ports,
            outputs,
            tuple(residuals),
            admissible,
            before.events + after.events,
        )
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
