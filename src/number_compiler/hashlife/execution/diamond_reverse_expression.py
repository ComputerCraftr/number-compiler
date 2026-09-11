"""Per-index Boolean realization of the certified decimal T² output section."""

from __future__ import annotations

from collections.abc import MutableSequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, Literal

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.execution.diamond_reverse_kernel import (
    DecimalT2Factorization,
    load_decimal_t2_factorization,
    validate_decimal_t2_factorization,
)
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import _valid_argument
from number_compiler.resources.ledger import OwnedMemo

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena


LookupName = Literal[
    "left-anchor", "right-anchor", "left-continuation", "right-continuation"
]


@dataclass(frozen=True, slots=True)
class FactorLookup:
    parameters: tuple[TransferSummaryID, ...]
    function: TransferSummaryID


class DecimalT2Emitter:
    """Four complete lookup functions, not a Cartesian T² output table."""

    def __init__(self, arena: DiamondKernelArena) -> None:
        self.arena, self.ledger = arena, arena.ledger
        definition = load_decimal_t2_factorization()
        if not validate_decimal_t2_factorization(definition):
            raise ValueError(
                "factorized emitter requires the certified immutable definition"
            )
        prefix = f"decimal-t2-emitter-{len(self.ledger.inventory())}"
        self.definition_owner = self.ledger.register(
            prefix + "-definition", "finite_kernel"
        )
        self._definitions: MutableSequence[DecimalT2Factorization] = (
            self.ledger.make_list(self.definition_owner)
        )
        self.ledger.reserve(self.definition_owner, entries=1, nodes=1)
        self._definitions.append(definition)
        self.template_owner = self.ledger.register(
            prefix + "-lookups", "finite_kernel_template"
        )
        self.templates: OwnedMemo[LookupName, FactorLookup] = OwnedMemo(
            self.ledger,
            self.template_owner,
            nodes_per_entry=1,
        )
        self.base = arena.intern(BaseBlockEffect(10))
        base = arena.kernel(self.base)
        if base.left != base.effect.boundary_universe(
            BoundarySide.LEFT
        ) or base.right != base.effect.boundary_universe(BoundarySide.RIGHT):
            raise ValueError("factorization and Base port enumerations disagree")
        self.ledger.register_execution_root(self)

    @property
    def definition(self) -> DecimalT2Factorization:
        return self._definitions[0]

    @staticmethod
    def _domains(name: LookupName) -> tuple[tuple[int, ...], int]:
        if name == "left-anchor":
            return (757,), 43
        if name == "right-anchor":
            return (179,), 5
        if name == "left-continuation":
            return (757, 5), 43
        if name == "right-continuation":
            return (179, 43), 5
        raise ValueError("unknown certified section lookup")

    def _value(self, name: LookupName, values: list[int]) -> int:
        self.ledger.bump("decimal_t2_lookup_reads")
        section = (
            self.definition.left if name.startswith("left") else self.definition.right
        )
        entry = section[values[0]]
        return (
            entry.anchor if name.endswith("anchor") else entry.continuation[values[1]]
        )

    def _build(self, name: LookupName) -> FactorLookup:
        from number_compiler.hashlife.interfaces.diamond_kernel import FiniteExpression

        domains, output = self._domains(name)
        parameters = tuple(
            self.arena.variable(domain, PortVariable(0, index, "decimal-t2-" + name, 0))
            for index, domain in enumerate(domains)
        )
        coordinates = []
        for argument, parameter in enumerate(parameters):
            for bit, handle in enumerate(self.arena.expression(parameter).bits):
                variable = self.arena.functions._nodes[
                    self.arena.functions._resolve(handle)
                ].variable
                assert variable is not None
                coordinates.append((variable, argument, bit))
        coordinates.sort()
        values = [0] * len(domains)
        frames: list[tuple[int, tuple[int, ...] | None]] = []
        depth = 0
        while True:
            admissible = all(
                value < domain for value, domain in zip(values, domains, strict=True)
            )
            if admissible and depth < len(coordinates):
                frames.append((depth, None))
                self.ledger.bump("decimal_t2_lookup_branches")
                peak = self.ledger.counters.get("decimal_t2_lookup_stack_peak", 0)
                self.ledger.bump(
                    "decimal_t2_lookup_stack_peak", max(0, len(frames) - peak)
                )
                depth += 1
                continue
            value = (
                self.ledger.observe_arithmetic(self._value(name, values))
                if admissible
                else 0
            )
            result = tuple(
                (value >> bit) & 1 for bit in range((output - 1).bit_length())
            )
            while frames:
                position, low = frames.pop()
                variable, argument, bit = coordinates[position]
                if low is None:
                    frames.append((position, result))
                    values[argument] = self.ledger.observe_arithmetic(
                        values[argument] | (1 << bit)
                    )
                    depth = position + 1
                    break
                values[argument] &= ~(1 << bit)
                if result != low:
                    result = tuple(
                        self.arena.functions._intern(variable, first, second)
                        for first, second in zip(low, result, strict=True)
                    )
            else:
                function = self.arena._intern_expression(
                    FiniteExpression(
                        output,
                        tuple(self.arena.functions._handle(bit) for bit in result),
                    )
                )
                self.ledger.bump("decimal_t2_lookup_templates")
                return FactorLookup(parameters, function)

    def _lookup(
        self, name: LookupName, arguments: tuple[TransferSummaryID, ...]
    ) -> TransferSummaryID:
        domains, _ = self._domains(name)
        nodes = tuple(self.arena.expression(argument) for argument in arguments)
        if tuple(node.domain for node in nodes) != domains:
            raise ValueError("section lookup argument has another finite domain")
        template = self.templates.get(name)
        if template is None:
            template = self._build(name)
            self.templates[name] = template
        replacements = {}
        for parameter, argument in zip(template.parameters, nodes, strict=True):
            for handle, value in zip(
                self.arena.expression(parameter).bits, argument.bits, strict=True
            ):
                variable = self.arena.functions._nodes[
                    self.arena.functions._resolve(handle)
                ].variable
                assert variable is not None
                replacements[variable] = value
        return self.arena.substitute(template.function, replacements)

    def emit(
        self,
        left: TransferSummaryID,
        symbol: TransferSummaryID,
        right: TransferSummaryID,
    ) -> TransferSummaryID:
        arguments = (left, symbol, right)
        if tuple(self.arena.expression(argument).domain for argument in arguments) != (
            757,
            20,
            179,
        ):
            raise ValueError("factorized emit requires the verified T² port domains")
        if not validate_decimal_t2_factorization(self.definition):
            raise ValueError(
                "factorization definition no longer matches its certificate"
            )
        left_anchor = self._lookup("left-anchor", (left,))
        right_anchor = self._lookup("right-anchor", (right,))
        first = self._base_emit(left_anchor, symbol, right_anchor)
        right_argument = self.arena.advance_expression(
            self.base, BoundarySide.RIGHT, right_anchor, symbol
        )
        left_argument = self.arena.advance_expression(
            self.base, BoundarySide.LEFT, left_anchor, symbol
        )
        next_left = self._lookup("left-continuation", (left, right_argument))
        next_right = self._lookup("right-continuation", (right, left_argument))
        result = self._base_emit(next_left, first, next_right)
        valid = self.arena.functions.constant(True)
        for argument in arguments:
            valid = self.arena.functions.choose(
                _valid_argument(self.arena, argument),
                valid,
                self.arena.functions.constant(False),
            )
        self.ledger.bump("decimal_t2_factorized_emit_applications")
        return self.arena.choose(valid, result, self.arena.constant(20, 0))

    def _base_emit(
        self,
        left: TransferSummaryID,
        symbol: TransferSummaryID,
        right: TransferSummaryID,
    ) -> TransferSummaryID:
        """Cofactor correlated port expressions and intern output functions early."""
        from number_compiler.hashlife.interfaces.diamond_kernel import FiniteExpression

        nodes = tuple(self.arena.expression(value) for value in (left, symbol, right))
        widths = tuple(len(node.bits) for node in nodes)
        roots = tuple(
            self.arena.functions._resolve(bit) for node in nodes for bit in node.bits
        )
        results: dict[tuple[int, ...], tuple[int, ...]] = {}
        reduced: dict[
            tuple[PortVariable, tuple[int, ...], tuple[int, ...]], tuple[int, ...]
        ] = {}
        frames: list[
            tuple[
                tuple[int, ...],
                PortVariable | None,
                tuple[int, ...] | None,
                tuple[int, ...] | None,
            ]
        ] = [(roots, None, None, None)]
        peak = self.ledger.counters.get("decimal_t2_cofactor_frames_peak", 0)
        self.ledger.bump("decimal_t2_cofactor_frames_peak", max(0, 1 - peak))
        while frames:
            key, variable, low, high = frames.pop()
            if key in results:
                continue
            self.ledger.bump("decimal_t2_cofactor_visits")
            if variable is not None:
                assert low is not None and high is not None
                lower, upper = results[low], results[high]
                if lower == upper:
                    results[key] = lower
                    self.ledger.bump("decimal_t2_output_identity_reductions")
                    continue
                signature = variable, lower, upper
                canonical = reduced.get(signature)
                if canonical is None:
                    canonical = tuple(
                        a if a == b else self.arena.functions._intern(variable, a, b)
                        for a, b in zip(lower, upper, strict=True)
                    )
                    reduced[signature] = canonical
                    self.ledger.bump("decimal_t2_output_reduction_evaluations")
                else:
                    self.ledger.bump("decimal_t2_output_reduction_early_hits")
                results[key] = canonical
                continue
            variables = [
                self.arena.functions._nodes[bit].variable for bit in key if bit >= 2
            ]
            if not variables:
                values, offset = [], 0
                for width in widths:
                    values.append(
                        self.ledger.observe_arithmetic(
                            sum(key[offset + bit] << bit for bit in range(width))
                        )
                    )
                    offset += width
                value = (
                    self.arena.kernel(self.base).emit(*values)
                    if all(
                        value < node.domain
                        for value, node in zip(values, nodes, strict=True)
                    )
                    else 0
                )
                results[key] = tuple((value >> bit) & 1 for bit in range(5))
                continue
            variable = min(value for value in variables if value is not None)
            low = tuple(
                self.arena.functions._nodes[bit].low
                if self.arena.functions._nodes[bit].variable == variable
                else bit
                for bit in key
            )
            high = tuple(
                self.arena.functions._nodes[bit].high
                if self.arena.functions._nodes[bit].variable == variable
                else bit
                for bit in key
            )
            frames.extend(
                (
                    (key, variable, low, high),
                    (high, None, None, None),
                    (low, None, None, None),
                )
            )
            for name, count in (
                ("decimal_t2_cofactor_frames_peak", len(frames)),
                ("decimal_t2_cofactor_results_peak", len(results)),
                ("decimal_t2_output_reduction_workspace_peak", len(reduced)),
            ):
                previous = self.ledger.counters.get(name, 0)
                self.ledger.bump(name, max(0, count - previous))
        peak = self.ledger.counters.get("decimal_t2_cofactor_results_peak", 0)
        self.ledger.bump(
            "decimal_t2_cofactor_results_peak", max(0, len(results) - peak)
        )
        return self.arena._intern_expression(
            FiniteExpression(
                20,
                tuple(self.arena.functions._handle(bit) for bit in results[roots]),
            )
        )
