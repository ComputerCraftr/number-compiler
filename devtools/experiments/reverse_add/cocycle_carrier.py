"""Exact reverse/add carrier with F5 residue and decimal parity planes.

Both value planes have affine spatial transport.  Decimal carry domains still
drive normalization and the nonlinear threshold cocycle, so this primitive
endpoint carrier does not claim powered closure or public point-cache admission.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.experiments.reverse_add.factored_carrier import (
    DOMAINS,
    FactoredReverseCarrier,
)
from devtools.experiments.reverse_add.factored_planes import PlaneGate, PlaneID
from number_compiler.arithmetic.automata.program_word import (
    prune_stale_program_word_memos,
)
from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.exact_tree_context import (
    require_endpoint_construction,
)
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_cocycle_coordinates,
    decimal_cocycle_domain,
    decimal_cocycle_kappa,
    decimal_cocycle_value,
    decimal_normalize_cocycle,
)
from number_compiler.arithmetic.polynomials.f2_transport import (
    F2AffineTransport,
    F2SpatialTransport,
)
from number_compiler.arithmetic.polynomials.f5_transport import (
    F5AffineTransport,
    F5SpatialTransport,
)


def _valid_carrier(domain: int, alpha: int, epsilon: int) -> int:
    try:
        decimal_cocycle_value(DOMAINS[domain], alpha, epsilon)
    except ValueError:
        return 0
    return 1


def _domain_or_undefined(alpha: int, epsilon: int, kappa: int) -> int | None:
    try:
        domain = decimal_cocycle_domain(alpha, epsilon, kappa)
    except ValueError:
        return None
    return DOMAINS.index(domain)


_NORMAL_ALPHA = PlaneGate.build(
    "cocycle-normal-alpha",
    ("f5", "bool"),
    "f5",
    lambda alpha, carry: decimal_normalize_cocycle(alpha, 0, carry)[0],
)
_NORMAL_EPSILON = PlaneGate.build(
    "cocycle-normal-epsilon",
    ("bool", "bool"),
    "bool",
    lambda epsilon, carry: decimal_normalize_cocycle(0, epsilon, carry)[1],
)
_KAPPA = PlaneGate.build(
    "decimal-threshold-cocycle",
    ("f5", "bool", "f5", "bool"),
    "bool",
    lambda a, e, b, f: decimal_cocycle_kappa((a, e), (b, f)),
)
_DOMAIN = PlaneGate.build(
    "cocycle-next-domain",
    ("f5", "bool", "bool"),
    "domain",
    _domain_or_undefined,
)
_VALID = PlaneGate.build(
    "valid-cocycle-carrier", ("domain", "f5", "bool"), "bool", _valid_carrier
)
_BOOL_ADD = PlaneGate.build(
    "cocycle-F2-add",
    ("bool", "bool"),
    "bool",
    lambda left, right: decimal_normalize_cocycle(0, left, right)[1],
)
_F5_CARRY = PlaneGate.build(
    "cocycle-carry-to-F5",
    ("bool",),
    "f5",
    lambda carry: decimal_normalize_cocycle(0, 0, carry)[0],
)


@dataclass(frozen=True, slots=True)
class CocycleCell:
    domain: PlaneID
    f5: PlaneID
    epsilon: PlaneID


@dataclass(frozen=True, slots=True)
class CocycleActions:
    """Exact source-bound affine actions for the two additive planes."""

    f5: F5AffineTransport[PlaneID]
    epsilon: F2AffineTransport[PlaneID]


class CocycleReverseCarrier:
    """Primitive exact carrier for ``(domain, alpha mod 5, parity)``."""

    def __init__(self, *, max_work: int = 1_000_000) -> None:
        self._factored = FactoredReverseCarrier(max_work=max_work)
        self.planes = self._factored.planes
        self.primitive_successors = 0
        self.nonlinear_gate_requests = 0

    def _shape(self, cell: CocycleCell) -> int:
        if type(cell) is not CocycleCell:
            raise TypeError("cocycle successor requires a CocycleCell")
        roots = tuple(
            self.planes.resolve(plane, kind)
            for plane, kind in zip(
                (cell.domain, cell.f5, cell.epsilon),
                ("domain", "f5", "bool"),
                strict=True,
            )
        )
        width = roots[0].length
        if width <= 0 or any(root.length != width for root in roots):
            raise ValueError("cocycle planes must have one positive common width")
        return width

    def validate(self, cell: CocycleCell) -> int:
        width = self._shape(cell)
        p = self.planes
        valid = p.apply(_VALID, cell.domain, cell.f5, cell.epsilon)
        if p.resolve(valid).symbol != 1:
            raise ValueError("cocycle channels disagree on decimal domain")
        if any(
            p.reverse(plane) != plane for plane in (cell.domain, cell.f5, cell.epsilon)
        ):
            raise ValueError("reverse pair cocycle carrier must be symmetric")
        if width % 2 and p.atom(cell.epsilon, width // 2):
            raise ValueError("odd-width pair center must be even")
        return width

    def encode(self, values: tuple[int, ...]) -> CocycleCell:
        """Import an exact symmetric pair field into three scalar coordinates."""
        require_endpoint_construction()
        if type(values) is not tuple or not values:
            raise ValueError("source must be an immutable nonempty pair field")
        coordinates = tuple(decimal_cocycle_coordinates(value) for value in values)
        p = self.planes
        p.clear_work()
        try:
            cell = CocycleCell(
                p.from_values(
                    "domain", tuple(DOMAINS.index(g) for g, _, _ in coordinates)
                ),
                p.from_values("f5", tuple(a for _, a, _ in coordinates)),
                p.from_values("bool", tuple(e for _, _, e in coordinates)),
            )
            self.validate(cell)
            return cell
        finally:
            p.clear_work()

    def source(self, values: tuple[int, ...]) -> CocycleCell:
        return self.encode(values)

    def uniform(
        self, domain: CarryFn, alpha: int, epsilon: int, width: int
    ) -> CocycleCell:
        require_endpoint_construction()
        decimal_cocycle_value(domain, alpha, epsilon)
        p = self.planes
        p.clear_work()
        try:
            cell = CocycleCell(
                p.constant("domain", DOMAINS.index(domain), width),
                p.constant("f5", alpha, width),
                p.constant("bool", epsilon, width),
            )
            self.validate(cell)
            return cell
        finally:
            p.clear_work()

    def _bool_add(self, left: PlaneID, right: PlaneID) -> PlaneID:
        return self.planes.apply(_BOOL_ADD, left, right)

    def _add(self, left: PlaneID, right: PlaneID) -> PlaneID:
        return self._factored._add(left, right)

    def _scale(self, plane: PlaneID, scalar: int) -> PlaneID:
        return self._factored._scale(plane, scalar)

    def successor_with_action(
        self, cell: CocycleCell
    ) -> tuple[CocycleCell, int, F5AffineTransport[PlaneID]]:
        """The common macro interface; parity remains in the complete output."""
        output, growth, actions = self.successor_with_actions(cell)
        return output, growth, actions.f5

    def successor(self, cell: CocycleCell) -> tuple[CocycleCell, int]:
        output, growth, _actions = self.successor_with_actions(cell)
        return output, growth

    def successor_with_emission(
        self, cell: CocycleCell
    ) -> tuple[CocycleCell, int, F5AffineTransport[PlaneID], tuple[PlaneID, PlaneID]]:
        output, growth, actions, emission = self._advance(cell)
        return output, growth, actions.f5, emission

    def successor_with_actions(
        self, cell: CocycleCell
    ) -> tuple[CocycleCell, int, CocycleActions]:
        output, growth, actions, _emission = self._advance(cell)
        return output, growth, actions

    def _advance(
        self, cell: CocycleCell
    ) -> tuple[CocycleCell, int, CocycleActions, tuple[PlaneID, PlaneID]]:
        """Advance once and expose both exact source-bound affine actions."""
        require_endpoint_construction()
        p = self.planes
        p.clear_work()
        p.memo_prune_visits += prune_stale_program_word_memos(amortized=True)
        try:
            self.validate(cell)
            carry, growth = p.carry_prefix(cell.domain)
            normal_alpha = p.apply(_NORMAL_ALPHA, cell.f5, carry)
            normal_epsilon = p.apply(_NORMAL_EPSILON, cell.epsilon, carry)
            source_alpha = cell.f5
            source_epsilon = cell.epsilon
            if growth:
                normal_alpha = p.concat(normal_alpha, p.constant("f5", 1, 1))
                normal_epsilon = p.concat(normal_epsilon, p.constant("bool", 1, 1))
                source_alpha = p.concat(source_alpha, p.constant("f5", 0, 1))
                source_epsilon = p.concat(source_epsilon, p.constant("bool", 0, 1))
                carry = p.concat(carry, p.constant("bool", 1, 1))

            reflected_carry = p.reverse(carry)
            f5_forcing = self._factored._add(
                p.apply(_F5_CARRY, carry), p.apply(_F5_CARRY, reflected_carry)
            )
            epsilon_forcing = self._bool_add(carry, reflected_carry)
            f5_linear = F5SpatialTransport(1 - growth, growth)
            epsilon_linear = F2SpatialTransport(1 - growth, growth)
            alpha = f5_linear.apply_with_output_forcing(
                source_alpha,
                f5_forcing,
                shift=p.shift,
                add=self._factored._add,
                scale=self._factored._scale,
            )
            epsilon = epsilon_linear.apply_with_output_forcing(
                source_epsilon,
                epsilon_forcing,
                shift=p.shift,
                add=self._bool_add,
            )

            # The growth frame combines mirrored decimal digits D_i and
            # D_(m-i); it is not a forward-neighbor threshold approximation.
            reflected_alpha = p.reverse(normal_alpha)
            reflected_epsilon = p.reverse(normal_epsilon)
            kappa = p.apply(
                _KAPPA,
                normal_alpha,
                normal_epsilon,
                reflected_alpha,
                reflected_epsilon,
            )
            domains = p.apply(_DOMAIN, alpha, epsilon, kappa)
            result = CocycleCell(domains, alpha, epsilon)
            self.primitive_successors += 1
            self.nonlinear_gate_requests += 2
            return (
                result,
                growth,
                CocycleActions(
                    F5AffineTransport(f5_linear, f5_forcing),
                    F2AffineTransport(epsilon_linear, epsilon_forcing),
                ),
                (normal_alpha, normal_epsilon),
            )
        finally:
            p.clear_work()

    def decode(self, cell: CocycleCell) -> tuple[int, ...]:
        """Explicit bounded oracle/export boundary, never used by successor."""
        require_endpoint_construction()
        p = self.planes
        p.clear_work()
        try:
            width = self.validate(cell)
            return tuple(
                decimal_cocycle_value(
                    DOMAINS[p.atom(cell.domain, i)],
                    p.atom(cell.f5, i),
                    p.atom(cell.epsilon, i),
                )
                for i in range(width)
            )
        finally:
            p.clear_work()

    def metrics(self, cell: CocycleCell) -> dict[str, object]:
        return {
            "width": self._shape(cell),
            "domain": self.planes.metrics(cell.domain),
            "f5": self.planes.metrics(cell.f5),
            "epsilon": self.planes.metrics(cell.epsilon),
            "primitive_successors": self.primitive_successors,
            "nonlinear_gate_requests": self.nonlinear_gate_requests,
        }


__all__ = ["CocycleActions", "CocycleCell", "CocycleReverseCarrier"]
