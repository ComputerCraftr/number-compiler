"""Self-advancing exact reverse/add carrier with three independent planes.

Output residuals identify the normalized output planes, never source tuples,
histories, or sampled future traces. Equality is exact; compression is measured,
not assumed. This endpoint-only API is not a public tile-cache admission gate.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.experiments.reverse_add.factored_planes import (
    PlaneAlgebra,
    PlaneGate,
    PlaneID,
)
from number_compiler.arithmetic.automata.program_word import (
    prune_stale_program_word_memos,
)
from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.exact_tree_context import (
    require_endpoint_construction,
)
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_add_normalized,
    decimal_factored_coordinates,
    decimal_factored_value,
    decimal_normalize_factored,
)
from number_compiler.arithmetic.polynomials.f5_transport import (
    F5AffineTransport,
    F5SpatialTransport,
)

DOMAINS = (CarryFn.CONST0, CarryFn.ID, CarryFn.CONST1)
_NORMAL_ALPHA = PlaneGate.build(
    "normalize-alpha",
    ("f5", "bool"),
    "f5",
    lambda a, c: decimal_normalize_factored(a, 0, c)[0],
)
_NORMAL_BETA = PlaneGate.build(
    "normalize-beta",
    ("f5", "bool", "bool"),
    "bool",
    lambda a, b, c: decimal_normalize_factored(a, b, c)[1],
)
_ADD = PlaneGate.build(
    "f5-add", ("f5", "f5"), "f5", lambda a, b: decimal_add_normalized((a, 0), (b, 0))[0]
)
_THRESHOLD = PlaneGate.build(
    "phase-carry",
    ("f5", "f5"),
    "bool",
    lambda a, b: decimal_add_normalized((a, 0), (b, 0))[1],
)
_BETA = PlaneGate.build(
    "half-xor",
    ("bool", "bool", "bool"),
    "bool",
    lambda a, b, u: decimal_add_normalized((4 * u, a), (u, b))[1],
)
_NU = PlaneGate.build(
    "half-majority",
    ("bool", "bool", "bool"),
    "bool",
    lambda a, b, u: decimal_add_normalized((4 * u, a), (u, b))[2],
)
_DOMAIN = PlaneGate.build(
    "next-domain",
    ("f5", "bool", "bool"),
    "domain",
    lambda a, b, n: 2 if n else int(a == 4 and b == 1),
)
_CAST = PlaneGate.build("bool-to-f5", ("bool",), "f5", lambda c: c)
_VALID = PlaneGate.build(
    "valid-carrier",
    ("domain", "f5", "bool"),
    "bool",
    lambda g, a, b: int((g == 1) == (a == 4 and b == 1)),
)
_SCALES = tuple(
    PlaneGate.build(f"f5-scale-{k}", ("f5",), "f5", lambda a, k=k: (k * a) % 5)
    for k in range(5)
)


@dataclass(frozen=True, slots=True)
class TemporalCell:
    domain: PlaneID
    f5: PlaneID
    half: PlaneID


@dataclass(frozen=True, slots=True)
class OutputResidualID:
    """Normal form of the interacted output; no source identity is retained."""

    domain: PlaneID
    f5: PlaneID
    half: PlaneID


class FactoredReverseCarrier:
    def __init__(self, *, max_work: int = 1_000_000) -> None:
        self.planes = PlaneAlgebra(max_work=max_work)
        self.successor_evaluations = 0

    def _shape(self, cell: TemporalCell) -> int:
        if type(cell) is not TemporalCell:
            raise TypeError("factored successor requires a TemporalCell")
        roots = tuple(
            self.planes.resolve(p, k)
            for p, k in zip(
                (cell.domain, cell.f5, cell.half), ("domain", "f5", "bool"), strict=True
            )
        )
        width = roots[0].length
        if width <= 0 or any(root.length != width for root in roots):
            raise ValueError("carrier planes must have one positive common width")
        return width

    def validate(self, cell: TemporalCell) -> int:
        width = self._shape(cell)
        p = self.planes
        valid = p.apply(_VALID, cell.domain, cell.f5, cell.half)
        if p.resolve(valid).symbol != 1:
            raise ValueError("carrier channels disagree on decimal domain")
        if any(
            p.reverse(plane) != plane for plane in (cell.domain, cell.f5, cell.half)
        ):
            raise ValueError("reverse pair carrier must be symmetric")
        if (
            width % 2
            and (p.atom(cell.f5, width // 2) + p.atom(cell.half, width // 2)) % 2
        ):
            raise ValueError("odd-width pair center must be even")
        return width

    def source(self, values: tuple[int, ...]) -> TemporalCell:
        """Import caller-supplied pair coefficients, before successor execution."""
        require_endpoint_construction()
        if type(values) is not tuple or not values:
            raise ValueError("source must be an immutable nonempty pair field")
        coordinates = tuple(decimal_factored_coordinates(v) for v in values)
        p = self.planes
        p.clear_work()
        try:
            cell = TemporalCell(
                p.from_values(
                    "domain", tuple(DOMAINS.index(g) for g, _, _ in coordinates)
                ),
                p.from_values("f5", tuple(a for _, a, _ in coordinates)),
                p.from_values("bool", tuple(b for _, _, b in coordinates)),
            )
            self.validate(cell)
            return cell
        finally:
            p.clear_work()

    def uniform(
        self, domain: CarryFn, alpha: int, beta: int, width: int
    ) -> TemporalCell:
        """Admit a counted source directly in its three coordinate alphabets."""
        require_endpoint_construction()
        decimal_factored_value(domain, alpha, beta)
        p = self.planes
        p.clear_work()
        try:
            cell = TemporalCell(
                p.constant("domain", DOMAINS.index(domain), width),
                p.constant("f5", alpha, width),
                p.constant("bool", beta, width),
            )
            self.validate(cell)
            return cell
        finally:
            p.clear_work()

    def _add(self, left: PlaneID, right: PlaneID) -> PlaneID:
        return self.planes.apply(_ADD, left, right)

    def _scale(self, plane: PlaneID, scalar: int) -> PlaneID:
        return self.planes.apply(_SCALES[scalar], plane)

    def successor(self, cell: TemporalCell) -> tuple[TemporalCell, int]:
        """Advance through domain prefix actions and channel-native gates only."""
        output, growth, _ = self.successor_with_action(cell)
        return output, growth

    def successor_with_action(
        self, cell: TemporalCell
    ) -> tuple[TemporalCell, int, F5AffineTransport[PlaneID]]:
        output, growth, action, _emission = self.successor_with_emission(cell)
        return output, growth, action

    def successor_with_emission(
        self, cell: TemporalCell
    ) -> tuple[TemporalCell, int, F5AffineTransport[PlaneID], tuple[PlaneID, PlaneID]]:
        """Also expose exact source-bound affine forcing for temporal composition."""
        require_endpoint_construction()
        p = self.planes
        p.clear_work()
        p.memo_prune_visits += prune_stale_program_word_memos(amortized=True)
        try:
            self.validate(cell)
            carry, growth = p.carry_prefix(cell.domain)
            normal_alpha = p.apply(_NORMAL_ALPHA, cell.f5, carry)
            normal_beta = p.apply(_NORMAL_BETA, cell.f5, cell.half, carry)
            source_alpha = cell.f5
            if growth:
                normal_alpha = p.concat(normal_alpha, p.constant("f5", 1, 1))
                normal_beta = p.concat(normal_beta, p.constant("bool", 0, 1))
                source_alpha = p.concat(source_alpha, p.constant("f5", 0, 1))
                carry = p.concat(carry, p.constant("bool", 1, 1))
            forcing = p.apply(_CAST, carry)
            forcing = self._add(forcing, p.reverse(forcing))
            transport = F5SpatialTransport(no_growths=1 - growth, growths=growth)
            alpha = transport.apply_with_output_forcing(
                source_alpha, forcing, shift=p.shift, add=self._add, scale=self._scale
            )
            threshold = p.apply(_THRESHOLD, normal_alpha, p.reverse(normal_alpha))
            reflected_beta = p.reverse(normal_beta)
            beta = p.apply(_BETA, normal_beta, reflected_beta, threshold)
            nu = p.apply(_NU, normal_beta, reflected_beta, threshold)
            domains = p.apply(_DOMAIN, alpha, beta, nu)
            result = TemporalCell(domains, alpha, beta)
            self.successor_evaluations += 1
            return (
                result,
                growth,
                F5AffineTransport(transport, forcing),
                (normal_alpha, normal_beta),
            )
        finally:
            p.clear_work()

    def residual(self, output: TemporalCell) -> OutputResidualID:
        require_endpoint_construction()
        p = self.planes
        p.clear_work()
        try:
            self.validate(output)
            return OutputResidualID(output.domain, output.f5, output.half)
        finally:
            p.clear_work()

    def decode(self, cell: TemporalCell) -> tuple[int, ...]:
        """Explicit bounded oracle/export boundary, never called by successor."""
        require_endpoint_construction()
        p = self.planes
        p.clear_work()
        try:
            width = self.validate(cell)
            return tuple(
                decimal_factored_value(
                    DOMAINS[p.atom(cell.domain, i)],
                    p.atom(cell.f5, i),
                    p.atom(cell.half, i),
                )
                for i in range(width)
            )
        finally:
            p.clear_work()

    def metrics(self, cell: TemporalCell) -> dict[str, object]:
        result: dict[str, object] = {
            "width": self._shape(cell),
            "domain": self.planes.metrics(cell.domain),
            "f5": self.planes.metrics(cell.f5),
            "bool_half": self.planes.metrics(cell.half),
            "combined_residual_components": 3,
        }
        # Count interacted macrocell normal forms without producing pair atoms.
        pending = [cell]
        seen: set[OutputResidualID] = set()
        p = self.planes
        p.clear_work()
        try:
            while pending:
                current = pending.pop()
                residual = OutputResidualID(current.domain, current.f5, current.half)
                if residual in seen:
                    continue
                seen.add(residual)
                planes = current.domain, current.f5, current.half
                width = self._shape(current)
                if all(p.resolve(plane).symbol is not None for plane in planes):
                    continue
                split = width // 2
                for start, length in ((0, split), (split, width - split)):
                    pending.append(
                        TemporalCell(
                            *(p.slice(plane, start, length) for plane in planes)
                        )
                    )
            result["combined_residual_nodes"] = len(seen)
            return result
        finally:
            p.clear_work()
