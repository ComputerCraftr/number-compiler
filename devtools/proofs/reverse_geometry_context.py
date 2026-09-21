"""Source-independent bounded reverse/add action with spatial threshold cells.

This research circuit avoids capacity-wide Boolean truth-function expansion.
It retains exact F5/parity expressions and all branch/extent predicates. Its
structural residual IDs must not be promoted as complete semantic cache keys.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from devtools.experiments.reverse_add.factored_carrier import DOMAINS
from devtools.proofs.growth_coboundary import GROWTH_SYMBOLS
from devtools.proofs.reverse_threshold_geometry import (
    DOMAIN_TABLE,
    ThresholdGeometry,
    ThresholdGeometryID,
)
from devtools.proofs.threshold_expressions import Expr, ThresholdExpressions
from number_compiler.arithmetic.automata import program_word as words
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_cocycle_coordinates,
    decimal_cocycle_value,
    decimal_pair_carry_action,
)


@dataclass(frozen=True, slots=True)
class GeometryAction:
    sizes: tuple[int, ...]
    outputs: tuple[Expr, ...]
    admitted: Expr
    geometry: ThresholdGeometryID
    events: int = field(compare=False)


@dataclass(frozen=True, slots=True)
class GeometryConsumer:
    """Demanded output functions on a free interface, not an extensional ID.

    Inputs are still coordinate functions; no selected source occurrence is
    part of this record. Structural equality alone does not prove equality on
    the complete admitted domain.
    """

    sizes: tuple[int, ...]
    outputs: tuple[Expr, ...]
    admitted: Expr


class ReverseGeometryContext:
    def __init__(
        self,
        capacity: int,
        *,
        max_nodes: int = 30000,
        max_work: int = 1000000,
        growth_quotient: bool = False,
        value_quotient: str = "crt",
    ) -> None:
        if type(capacity) is not int or not 1 <= capacity <= 512:
            raise ValueError("geometry experiment capacity must lie in 1..512")
        if type(growth_quotient) is not bool:
            raise ValueError("growth quotient mode must be Boolean")
        if value_quotient not in ("crt", "mod9") or (
            growth_quotient and value_quotient == "mod9"
        ):
            raise ValueError("choose CRT/growth or the replacement mod9 carrier")
        self.value_quotient = value_quotient
        self.stride = 2 if value_quotient == "mod9" else 3
        self.coordinate_roles = (
            ("domain", "mod9") if self.stride == 2 else ("domain", "f5", "parity")
        )
        self.growth_quotient = growth_quotient
        self.capacity = capacity
        self.slots = (capacity + 1) // 2
        self.expressions = ThresholdExpressions(max_nodes=max_nodes, max_work=max_work)
        self.geometry = ThresholdGeometry(self.expressions)
        sorts = (3, 9) if self.stride == 2 else (3, 5, 2)
        self.sizes = (capacity + 1, *(sorts * self.slots))
        self.inputs = tuple(
            self.expressions.variable(size, i) for i, size in enumerate(self.sizes)
        )
        self.zero = self.expressions.constant(2, 0)
        self.one = self.expressions.constant(2, 1)
        self.primitive_successors = 0
        self.temporal_compositions = 0
        self.consumer_pullbacks = 0
        self.growth_generic_parity_tables = 0

    def _audit_growth_parity(
        self, value: Expr, boundaries: frozenset[int] = frozenset()
    ) -> None:
        """Transport is affine after the four fixed coboundary parity views."""
        e = self.expressions
        allowed = {
            tuple((q + d) % 2 for q, d in GROWTH_SYMBOLS),
            tuple(q % 2 for q, _ in GROWTH_SYMBOLS),
            tuple(2 * q % 2 for q, _ in GROWTH_SYMBOLS),
        }
        pending, seen = [value.index], set()
        while pending:
            index = pending.pop()
            if index in seen or index in boundaries:
                continue
            seen.add(index)
            e.tick()
            node = e.nodes[index]
            if node.kind == "growth_symbol":
                continue
            if node.kind == "table":
                schema = e.consumer_program(e.handle(index))
                if schema[0] != 12 or schema[2] not in allowed:
                    self.growth_generic_parity_tables += 1
            pending.extend(node.args)

    def _and(self, a: Expr, b: Expr) -> Expr:
        return self.expressions.select(a, b, self.zero)

    def _not(self, value: Expr) -> Expr:
        return self.expressions.table(value, 2, (1, 0))

    def _eq(self, value: Expr, target: int) -> Expr:
        e = self.expressions
        return e.table(
            value, 2, tuple(int(i == target) for i in range(e.resolve(value).size))
        )

    def _residue(self, alpha: Expr, epsilon: Expr) -> Expr:
        e = self.expressions
        parity = e.table(alpha, 2, (0, 1, 0, 1, 0))
        beta = e.affine(2, ((parity, 1), (epsilon, 1)))
        return e.affine(10, ((alpha, 1), (e.table(beta, 6, (0, 5)), 1)))

    def _action(
        self, outputs: tuple[Expr, ...], admitted: Expr, events: int
    ) -> GeometryAction:
        return GeometryAction(
            self.sizes,
            outputs,
            admitted,
            ThresholdGeometryID(
                self.geometry.owner,
                words.from_values(v.index for v in outputs[1 :: self.stride]),
            ),
            events,
        )

    def _mirror_outputs(
        self, alpha: Expr, epsilon: Expr, left_carry: Expr, right_carry: Expr
    ) -> tuple[Expr, Expr, Expr]:
        """No-growth correlated pair; old parity cancels before substitution."""
        e = self.expressions
        carry_sum = e.affine(3, ((left_carry, 1), (right_carry, 1)))
        domain = e.mirror_pair(
            self._residue(alpha, epsilon), carry_sum, domain_only=True
        )
        return (
            domain,
            e.affine(5, ((alpha, 2), (left_carry, 1), (right_carry, 1))),
            e.affine(2, ((left_carry, 1), (right_carry, 1))),
        )

    def _growth_outputs(
        self,
        m: int,
        residues: tuple[Expr, ...],
        carry: tuple[Expr, ...],
        alpha: tuple[Expr, ...],
        epsilon: tuple[Expr, ...],
    ) -> list[tuple[Expr, Expr, Expr]]:
        e = self.expressions
        if m >= self.capacity:
            return []
        if not self.growth_quotient:
            digits = tuple(
                e.affine(10, ((residues[min(i, m - 1 - i)], 1), (carry[i], 1)))
                for i in range(m)
            ) + (e.constant(10, 1),)
            domains = self.geometry.coordinates(
                self.geometry.compare(digits, digits[::-1])
            )
            normal_alpha = tuple(
                e.affine(5, ((alpha[min(i, m - 1 - i)], 1), (carry[i], 1)))
                for i in range(m)
            ) + (e.constant(5, 1),)
            normal_epsilon = tuple(
                e.affine(2, ((epsilon[min(i, m - 1 - i)], 1), (carry[i], 1)))
                for i in range(m)
            ) + (self.one,)
            outputs = []
            ports = frozenset(v.index for v in (*epsilon, *carry))
            for i in range((m + 2) // 2):
                f2 = e.affine(2, ((normal_epsilon[i], 1), (normal_epsilon[m - i], 1)))
                self._audit_growth_parity(f2, ports)
                outputs.append(
                    (
                        domains[i],
                        e.affine(5, ((normal_alpha[i], 1), (normal_alpha[m - i], 1))),
                        f2,
                    )
                )
            return outputs
        symbols = tuple(
            e.growth_symbol(residues[i], carry[i + 1], carry[m - i])
            for i in range((m + 1) // 2)
        )
        outputs = []
        for i in range((m + 2) // 2):
            if i == 0 or (m % 2 == 0 and i == m // 2):
                symbol = symbols[0] if i == 0 else symbols[-1]
                values = tuple(q + d if i == 0 else 2 * q for q, d in GROWTH_SYMBOLS)
                outputs.append(
                    (
                        e.table(symbol, 3, tuple(DOMAIN_TABLE[v % 19] for v in values)),
                        e.table(symbol, 5, tuple(v % 5 for v in values)),
                        e.table(symbol, 2, tuple(v % 2 for v in values)),
                    )
                )
            else:
                outputs.append(e.growth_channels(symbols[i - 1], symbols[i]))
            self._audit_growth_parity(outputs[-1][2])
        return outputs

    def primitive(self) -> GeometryAction:
        if self.value_quotient == "mod9":
            from devtools.proofs.reverse_mod9_context import primitive_mod9

            return primitive_mod9(self)
        e, capacity = self.expressions, self.capacity
        e.work = 0
        self.growth_generic_parity_tables = 0
        width = self.inputs[0]
        width_is = tuple(self._eq(width, m) for m in range(1, capacity + 1))
        domain_inputs, alpha_inputs, epsilon_inputs = (
            self.inputs[1::3],
            self.inputs[2::3],
            self.inputs[3::3],
        )
        residues = tuple(
            self._residue(alpha, epsilon)
            for alpha, epsilon in zip(alpha_inputs, epsilon_inputs, strict=True)
        )
        admitted = self._not(self._eq(width, 0))
        blank_domain, blank_alpha = e.constant(3, 0), e.constant(5, 0)
        for i, (domain, alpha, epsilon) in enumerate(
            zip(domain_inputs, alpha_inputs, epsilon_inputs, strict=True)
        ):
            residue = residues[i]
            valid = self._not(
                e.affine(2, ((self._eq(domain, 1), 1), (self._eq(residue, 9), 1)))
            )
            padding = self._and(
                self._eq(domain, 0), self._and(self._eq(alpha, 0), self._not(epsilon))
            )
            inactive = e.table(
                width, 2, tuple(int(m <= 2 * i) for m in range(capacity + 1))
            )
            admitted = self._and(admitted, e.select(inactive, padding, valid))
            admitted = self._and(
                admitted, e.select(width_is[2 * i], self._not(epsilon), self.one)
            )
        domains: list[Expr] = []
        for i in range(capacity):
            domain = blank_domain
            for m, condition in enumerate(width_is, 1):
                if i < m:
                    orbit = min(i, m - 1 - i)
                    domain = e.select(condition, domain_inputs[orbit], domain)
            domains.append(domain)
        source_geometry = self.geometry.from_domains(tuple(domains))
        carry = tuple(
            self.geometry.carry_at(source_geometry, i, self.zero)
            for i in range(capacity + 1)
        )
        growth = self.zero
        for m, condition in enumerate(width_is, 1):
            growth = e.select(condition, carry[m], growth)
        extended_width = e.affine(capacity + 2, ((width, 1), (growth, 1)))
        admitted = self._and(
            admitted, self._not(self._eq(extended_width, capacity + 1))
        )
        next_width = e.table(extended_width, capacity + 1, (*range(capacity + 1), 0))
        out_domain = [blank_domain] * self.slots
        out_alpha = [blank_alpha] * self.slots
        out_epsilon = [self.zero] * self.slots
        for m, condition in enumerate(width_is, 1):
            high_outputs = self._growth_outputs(
                m, residues, carry, alpha_inputs, epsilon_inputs
            )
            for i in range(min((m + 2) // 2, self.slots)):
                if i < (m + 1) // 2:
                    low_domain, low_alpha, low_epsilon = self._mirror_outputs(
                        alpha_inputs[i], epsilon_inputs[i], carry[i], carry[m - 1 - i]
                    )
                else:
                    low_domain, low_alpha, low_epsilon = (
                        blank_domain,
                        blank_alpha,
                        self.zero,
                    )
                if high_outputs:
                    high_domain, high_alpha, high_epsilon = high_outputs[i]
                    chosen_domain = e.select(carry[m], high_domain, low_domain)
                    chosen_alpha = e.select(carry[m], high_alpha, low_alpha)
                    chosen_epsilon = e.select(carry[m], high_epsilon, low_epsilon)
                else:
                    chosen_domain, chosen_alpha, chosen_epsilon = (
                        low_domain,
                        low_alpha,
                        low_epsilon,
                    )
                out_domain[i] = e.select(condition, chosen_domain, out_domain[i])
                out_alpha[i] = e.select(condition, chosen_alpha, out_alpha[i])
                out_epsilon[i] = e.select(condition, chosen_epsilon, out_epsilon[i])
        outputs = (
            next_width,
            *(
                v
                for triple in zip(out_domain, out_alpha, out_epsilon, strict=True)
                for v in triple
            ),
        )
        action = self._action(outputs, admitted, 1)
        self.primitive_successors += 1
        return action

    def _validate(self, action: GeometryAction) -> None:
        if (
            type(action) is not GeometryAction
            or action.sizes != self.sizes
            or len(action.outputs) != len(self.sizes)
        ):
            raise ValueError("incomplete geometry action interface")
        if type(action.events) is not int or action.events < 1:
            raise ValueError("invalid action event count")
        e = self.expressions
        if (
            tuple(e.resolve(v).size for v in action.outputs) != self.sizes
            or e.resolve(action.admitted).size != 2
        ):
            raise ValueError("geometry action changes coordinate sorts")
        if (
            action.geometry
            != self._action(action.outputs, action.admitted, action.events).geometry
        ):
            raise ValueError("geometry does not describe action outputs")
        for index in e.reachable((*action.outputs, action.admitted)):
            node = e.nodes[index]
            if node.kind == "variable" and (
                node.data[0] >= len(self.sizes) or self.sizes[node.data[0]] != node.size
            ):
                raise ValueError("action contains an undeclared input")

    def compose(self, before: GeometryAction, after: GeometryAction) -> GeometryAction:
        self._validate(after)
        pulled = self.pullback(
            before, GeometryConsumer(after.sizes, after.outputs, after.admitted)
        )
        result = self._action(
            pulled.outputs,
            pulled.admitted,
            before.events + after.events,
        )
        self.temporal_compositions += 1
        return result

    def project(
        self, action: GeometryAction, output_indices: tuple[int, ...]
    ) -> GeometryConsumer:
        """Select demanded outputs before any temporal substitution work."""
        self._validate(action)
        if type(output_indices) is not tuple or any(
            type(i) is not int or not 0 <= i < len(self.sizes) for i in output_indices
        ):
            raise ValueError("consumer projection requires declared output slots")
        return GeometryConsumer(
            self.sizes,
            tuple(action.outputs[i] for i in output_indices),
            action.admitted,
        )

    def pullback(
        self, before: GeometryAction, consumer: GeometryConsumer
    ) -> GeometryConsumer:
        """Compose only demanded functions; eliminate midpoint variables now.

        This reuses simultaneous substitution. It creates neither a midpoint
        input port nor a complete second endpoint merely to observe one part.
        The admission predicate remains observable, including capacity exit.
        """
        e = self.expressions
        e.work = 0
        self._validate(before)
        if type(consumer) is not GeometryConsumer or consumer.sizes != self.sizes:
            raise ValueError("consumer has another free interface")
        if e.resolve(consumer.admitted).size != 2:
            raise ValueError("consumer admission must be Boolean")
        roots = (*consumer.outputs, consumer.admitted)
        for index in e.reachable(roots):
            node = e.nodes[index]
            if node.kind == "variable" and (
                node.data[0] >= len(self.sizes) or self.sizes[node.data[0]] != node.size
            ):
                raise ValueError("consumer contains an undeclared input")
        with e.construction_transaction():
            pulled = e.substitute(roots, dict(enumerate(before.outputs)))
            result = GeometryConsumer(
                self.sizes, pulled[:-1], self._and(before.admitted, pulled[-1])
            )
        self.consumer_pullbacks += 1
        return result

    def binding(self, field: tuple[int, ...]) -> tuple[int, ...]:
        if (
            type(field) is not tuple
            or not 1 <= len(field) <= self.capacity
            or field != field[::-1]
        ):
            raise ValueError("source must be an admitted symmetric field")
        if len(field) % 2 and field[len(field) // 2] % 2:
            raise ValueError("odd center must have even pair parity")
        half = field[: (len(field) + 1) // 2]
        result = [len(field)]
        for value in half + (0,) * (self.slots - len(half)):
            if self.stride == 2:
                domain = decimal_pair_carry_action(value)
                result.extend((DOMAINS.index(domain), value % 9))
            else:
                domain, alpha, epsilon = decimal_cocycle_coordinates(value)
                result.extend((DOMAINS.index(domain), alpha, epsilon))
        return tuple(result)

    def observe(
        self, action: GeometryAction, binding: tuple[int, ...]
    ) -> tuple[int, ...] | None:
        self._validate(action)
        if len(binding) != len(self.sizes):
            raise ValueError("incomplete source binding")
        values = self.expressions.evaluate((action.admitted, *action.outputs), binding)
        if not values[0]:
            return None
        width = values[1]
        result = []
        for i in range(width):
            orbit = min(i, width - 1 - i)
            if self.stride == 2:
                from devtools.proofs.skew_residue_laws import skew_pair_value

                domain, residue = values[2 + 2 * orbit : 4 + 2 * orbit]
                result.append(skew_pair_value(domain, residue))
            else:
                domain, alpha, epsilon = values[2 + 3 * orbit : 5 + 3 * orbit]
                result.append(decimal_cocycle_value(DOMAINS[domain], alpha, epsilon))
        return tuple(result)

    def metrics(self, action: GeometryAction) -> dict[str, int]:
        e = self.expressions
        reached = e.reachable((*action.outputs, action.admitted))
        return {
            "events": action.events,
            "mod9_enabled": int(self.stride == 2),
            "reachable_residue10_nodes": sum(
                e.nodes[i].size == 10
                and e.nodes[i].kind not in ("variable", "constant")
                # Capacity9 uses a ten-element WIDTH sort, not a digit view.
                and not (
                    self.capacity == 9
                    and e.nodes[i].kind == "table"
                    and e.consumer_program(e.handle(i)) == (11, 10, (*range(10), 0))
                )
                for i in reached
            ),
            "reachable_q_view_nodes": sum(
                e.nodes[i].kind == "growth_symbol" for i in reached
            ),
            "independent_reset_nodes": 0,
            "independent_carry_vector_nodes": 0,
            "mod9_nodes": len(e.reachable(action.outputs[2::2]))
            if self.stride == 2
            else 0,
            "skew_domain_consumers": sum(
                e.nodes[i].kind == "skew_pair_domain" for i in reached
            ),
            "growth_coboundary_enabled": int(self.growth_quotient),
            "growth_gauge_alias_hits": e.growth_gauge_alias_hits,
            "retained_expression_nodes": len(e.nodes),
            "retained_schema_nodes": len(e.schemas),
            "retained_total_nodes": len(e.nodes) + len(e.schemas) + e.auxiliary_nodes,
            "retained_auxiliary_nodes": e.auxiliary_nodes,
            "reachable_expression_nodes": len(reached),
            "unresolved_tables": sum(e.nodes[i].kind == "table" for i in reached),
            "unresolved_threshold_consumers": sum(
                e.nodes[i].kind
                in (
                    "mirror_domain",
                    "decimal_sum_domain",
                    "growth_domain",
                    "skew_pair_domain",
                )
                or e.nodes[i].kind == "table"
                and e.consumer_program(e.handle(i))[2] == DOMAIN_TABLE
                for i in reached
            ),
            "retained_argument_edges": sum(len(node.args) for node in e.nodes),
            "retained_table_entries": sum(len(schema.table) for schema in e.schemas),
            "retained_range_atoms": sum(len(node.possible) for node in e.nodes),
            "affine_nodes": sum(e.nodes[i].kind == "affine" for i in reached),
            "derived_carry_nodes": sum(
                e.nodes[i].kind in ("carry_apply", "carry_compose") for i in reached
            ),
            "mirror_pair_nodes": sum(
                e.nodes[i].kind in ("mirror_pair", "mirror_domain") for i in reached
            ),
            "growth_generic_parity_tables": self.growth_generic_parity_tables,
            "growth_full19_value_fallbacks": sum(
                e.nodes[i].kind == "mirror_pair"
                or e.nodes[i].kind == "affine"
                and e.nodes[i].size == 19
                and all(e.nodes[j].size == 10 for j in e.nodes[i].args)
                for i in reached
            ),
            "growth_coboundary_families": sum(
                e.nodes[i].kind == "growth_symbol" for i in reached
            ),
            "growth_residual_families": sum(
                e.nodes[i].kind == "growth_domain" for i in reached
            ),
            "growth_source_binding_families": len(
                {e.nodes[i].args for i in reached if e.nodes[i].kind == "growth_symbol"}
            ),
            "nogrowth_residual_families": sum(
                e.nodes[i].kind == "mirror_domain" for i in reached
            ),
            "direct_decimal_domain_nodes": sum(
                e.nodes[i].kind == "decimal_sum_domain" for i in reached
            ),
            "f5_nodes": len(e.reachable(action.outputs[2::3]))
            if self.stride == 3
            else 0,
            "f2_nodes": len(e.reachable(action.outputs[3::3]))
            if self.stride == 3
            else 0,
            "domain_nodes": len(e.reachable(action.outputs[1 :: self.stride])),
            "geometry_word_nodes": words.word_metrics(action.geometry.word)["nodes"],
            "derived_geometry_summary_cache_entries": len(self.geometry._carry_actions),
            "primitive_successors": self.primitive_successors,
            "temporal_compositions": self.temporal_compositions,
            "consumer_pullbacks": self.consumer_pullbacks,
            "substitution_select_branches_skipped": e.substitution_select_branches_skipped,
            "discarded_failed_nodes": e.discarded_failed_nodes,
            "discarded_failed_schemas": e.discarded_failed_schemas,
            "construction_work": e.work,
        }
