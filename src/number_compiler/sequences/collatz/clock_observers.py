"""Lazy projections of the existing Collatz event DAG's matrix M(s,z).

This consumes supplied valuation actions. It neither discovers future events
nor substitutes sampled projections for the admitted occurrence/action identity.
Every query folds shared nodes once, with no exact source or affine lowering.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TYPE_CHECKING, TypeVar, cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.morphism_core import modular_power
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.arithmetic.fields.tropical import TropicalMatrix
from number_compiler.arithmetic.fields.tropical_divisor import TropicalDivisorState
from number_compiler.arithmetic.polynomials.cyclotomic_ring import CyclotomicRing
from number_compiler.sequences.collatz.hensel_cylinders import (
    MAX_CYLINDER_BITS,
    HenselCylinder,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.power import (
        CollatzEventArena,
        CollatzEventNode,
    )

T = TypeVar("T")


@dataclass(frozen=True, slots=True)
class SArithmeticClock:
    events: int
    divisions: int

    def __post_init__(self) -> None:
        if any(type(v) is not int or v < 0 for v in (self.events, self.divisions)):
            raise ValueError("clock counts must be exact nonnegative integers")

    @property
    def physical_ticks(self) -> int:
        return self.events + self.divisions

    @property
    def real_prime_exponents(self) -> tuple[int, int]:
        """Exact slope 2**(-K) * 3**N, without floating logarithms."""
        return -self.divisions, self.events

    @property
    def two_adic_exponent(self) -> int:
        return self.divisions

    @property
    def three_adic_exponent(self) -> int:
        return -self.events


class CollatzClockObservers:
    """Views are downstream queries, never fields of the event node key.

    Cache at most 16 demanded specializations for this arena; each retains only
    observed nodes. Eviction changes work, never action identity or results.
    """

    def __init__(self, arena: CollatzEventArena) -> None:
        self.arena = arena
        self._views: dict[tuple[object, ...], dict[int, object]] = {}
        self.node_evaluations = 0
        self.compositions = 0
        self.ring_power_compositions = 0

    def _fold(
        self,
        root: CollatzEventNode,
        *,
        key: tuple[object, ...],
        identity: T,
        event: Callable[[int], T],
        compose: Callable[[T, T], T],
    ) -> T:
        self.arena.validate_node(root)
        if key not in self._views and len(self._views) >= 16:
            del self._views[next(iter(self._views))]
        values = self._views.setdefault(key, {})
        stack = [(root, False)]
        while stack:
            node, ready = stack.pop()
            if node.node_id in values:
                continue
            if node.kind == "identity":
                value = identity
            elif node.kind == "event":
                assert node.valuation is not None
                value = event(node.valuation)
            else:
                assert node.left is not None and node.right is not None
                if not ready:
                    stack.extend(
                        ((node, True), (node.right, False), (node.left, False))
                    )
                    continue
                value = compose(
                    cast(T, values[node.left.node_id]),
                    cast(T, values[node.right.node_id]),
                )
                self.compositions += 1
            values[node.node_id] = value
            self.node_evaluations += 1
        return cast(T, values[root.node_id])

    def modular(
        self,
        root: CollatzEventNode,
        modulus: int,
        *,
        s: int = 3,
        z: int = 2,
    ) -> SkewTransfer[int]:
        if any(type(v) is not int for v in (modulus, s, z)):
            raise TypeError("matrix specialization requires exact integers")
        if modulus < 2:
            raise ValueError("modulus must exceed one")

        def atom(k: int) -> SkewTransfer[int]:
            power = modular_power(z, k, modulus)
            self.ring_power_compositions += power.compositions
            return SkewTransfer(s % modulus, 1, power.value)

        return self._fold(
            root,
            key=("modular", modulus, s % modulus, z % modulus),
            identity=SkewTransfer(1, 0, 1),
            event=atom,
            compose=lambda a, b: a.then(
                b,
                multiply=lambda x, y: x * y % modulus,
                add=lambda x, y: (x + y) % modulus,
            ),
        )

    def polynomial(
        self,
        root: CollatzEventNode,
        ring: CyclotomicRing,
        *,
        s: int = 3,
        z: tuple[int, ...] = (0, 1),
    ) -> SkewTransfer[tuple[int, ...]]:
        """Evaluate P in the demanded ring, including arbitrary repeated factors."""

        def atom(k: int) -> SkewTransfer[tuple[int, ...]]:
            power = ring.power_residue(ring.reduce(z), k)
            self.ring_power_compositions += power.compositions
            return SkewTransfer(ring.reduce((s,)), ring.one, power.value)

        return self._fold(
            root,
            key=("polynomial", ring.module_key, s % ring.modulus, ring.reduce(z)),
            identity=SkewTransfer(ring.one, ring.zero, ring.one),
            event=atom,
            compose=lambda a, b: a.then(b, multiply=ring.multiply, add=ring.add),
        )

    def hasse(
        self,
        root: CollatzEventNode,
        *,
        degree: int,
        modulus: int,
        s: int = 3,
    ) -> tuple[int, ...]:
        """Coefficients of P(s,1+y) mod y**degree, i.e. Hasse derivatives."""
        if type(degree) is not int or degree < 1:
            raise ValueError("Hasse degree must be positive")
        ring = CyclotomicRing(1, modulus, factor=(0,) * degree + (1,))
        return self.polynomial(root, ring, s=s, z=(1, 1)).offset

    def twisted(
        self,
        root: CollatzEventNode,
        *,
        width: int,
        sign: int,
        modulus: int,
        s: int = 3,
    ) -> tuple[int, ...]:
        if (
            type(width) is not int
            or width < 1
            or type(sign) is not int
            or sign not in (-1, 1)
        ):
            raise ValueError("expected a positive width and cylinder twist +/-1")
        ring = CyclotomicRing(1, modulus, factor=(-sign,) + (0,) * (width - 1) + (1,))
        return self.polynomial(root, ring, s=s).offset

    def hensel_pullback(
        self, root: CollatzEventNode, target: HenselCylinder
    ) -> HenselCylinder:
        self.arena.validate_node(root)
        bits = root.effect.shift + target.bits
        if bits > MAX_CYLINDER_BITS:
            raise BlockContextBudgetExceeded("Hensel precision budget exceeded")
        if bits == 0:
            return target
        transfer = self.modular(root, 1 << bits)
        return target.pullback_modular(
            multiplier=transfer.upper,
            offset=transfer.offset,
            divisions=root.effect.shift,
        )

    def tropical(
        self, root: CollatzEventNode, *, s_weight: int, z_weight: int
    ) -> int | None:
        """Minimum alpha*(N-1-j)+beta*K_j over the positive support of P."""
        if type(s_weight) is not int or type(z_weight) is not int:
            raise TypeError("tropical weights must be exact integers")
        value = self._fold(
            root,
            key=("tropical", s_weight, z_weight),
            identity=TropicalMatrix.identity(2),
            event=lambda k: TropicalMatrix(((s_weight, 0), (None, z_weight * k))),
            compose=lambda a, b: b.compose(a),
        )
        return value.rows[0][1]

    def clock(self, root: CollatzEventNode) -> SArithmeticClock:
        self.arena.validate_node(root)
        return SArithmeticClock(root.effect.events, root.effect.shift)

    def factor_observation(
        self, root: CollatzEventNode, modulus: int
    ) -> TropicalDivisorState:
        """gcd(N,P(3,2)) from a modular query; a proper split is conditional."""
        return TropicalDivisorState.observe(modulus, self.modular(root, modulus).offset)
