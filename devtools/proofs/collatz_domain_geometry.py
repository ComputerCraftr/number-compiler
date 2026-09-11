"""Research adapter for deriving Collatz carry ports from domain geometry.

The radix-64 Collatz domain alphabet has five actions on the three reachable
carry values.  ``ThresholdGeometry`` already owns the recursive prefix-action
calculation for a Boolean carry function, so this module only changes the
five-action alphabet into the two Boolean wire alphabets.  It does not retain
an additional carry vector or materialize a represented word.

This is a bounded research interface.  It deliberately exposes the two wire
expressions separately; their pair is the exact staircase encoding of a
carry in ``{0, 1, 2}``.
"""

from __future__ import annotations

from dataclasses import dataclass
from devtools.proofs.reverse_threshold_geometry import (
    ThresholdGeometry,
    ThresholdGeometryID,
)
from devtools.proofs.threshold_expressions import Expr, ThresholdExpressions
from number_compiler.arithmetic.automata import program_word as words
from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.carry.collatz_carry_wires import (
    CollatzCarryWires,
    collatz_digit_carry_wires,
)
from number_compiler.arithmetic.carry.collatz_output_quotient import (
    DOMAIN_ACTIONS,
    radix64_domain,
)


_CARRY_FUNCTIONS = tuple(CarryFn)


def _function_index(function: CarryFn) -> int:
    return _CARRY_FUNCTIONS.index(function)


# The index is the existing DOMAIN_ACTIONS index, not a newly learned class.
# Build it from the canonical two-wire digit law so this adapter shares the
# production theorem table with the output morphism.
def _wires_for_action(action: tuple[int, int, int]) -> CollatzCarryWires:
    for digit in range(64):
        wires = collatz_digit_carry_wires(digit, base=64)
        if wires.outputs == action:
            return wires
    raise AssertionError("DOMAIN_ACTIONS contains an unknown wire action")


_ACTION_WIRES: tuple[CollatzCarryWires, ...] = tuple(
    _wires_for_action(action) for action in DOMAIN_ACTIONS
)
_LOWER_TABLE = tuple(_function_index(wires.lower) for wires in _ACTION_WIRES)
_UPPER_TABLE = tuple(_function_index(wires.upper) for wires in _ACTION_WIRES)


@dataclass(frozen=True, slots=True)
class CollatzPortPair:
    """The lower and upper expressions of one exact two-wire port.

    For a domain action both expressions have sort three and denote a
    ``CarryFn``.  For a queried carry both have sort two and denote output
    bits.  Keeping this as a pair avoids introducing an integer carry variable.
    """

    lower: Expr
    upper: Expr


@dataclass(frozen=True, slots=True)
class CollatzDomainGeometryID:
    """A shared immutable spatial geometry and its two derived wire roots."""

    owner: object
    lower: ThresholdGeometryID
    upper: ThresholdGeometryID
    width: int


class CollatzDomainGeometry:
    """Derive Collatz carry ports from five-way radix-64 domain actions."""

    def __init__(
        self,
        expressions: ThresholdExpressions,
        *,
        geometry: ThresholdGeometry | None = None,
    ) -> None:
        if type(expressions) is not ThresholdExpressions:
            raise TypeError("Collatz geometry requires an owned expression arena")
        if geometry is not None and type(geometry) is not ThresholdGeometry:
            raise TypeError("Collatz geometry requires an owned threshold geometry")
        if geometry is not None and geometry.expressions is not expressions:
            raise ValueError("threshold geometry belongs to another expression arena")
        self.expressions = expressions
        self.geometry = geometry or ThresholdGeometry(expressions)
        self.owner = object()

    def _check(self, value: CollatzDomainGeometryID) -> None:
        if type(value) is not CollatzDomainGeometryID or value.owner is not self.owner:
            raise ValueError("foreign Collatz domain geometry")
        if type(value.width) is not int or value.width < 1:
            raise ValueError("invalid Collatz geometry width")
        if (
            value.lower.owner is not self.geometry.owner
            or value.upper.owner is not self.geometry.owner
        ):
            raise ValueError("foreign threshold geometry")
        if (
            value.lower.word.length != value.width
            or value.upper.word.length != value.width
        ):
            raise ValueError("wire geometry widths disagree")

    def _wire_expressions(
        self, domains: tuple[Expr, ...]
    ) -> tuple[ThresholdGeometryID, ThresholdGeometryID]:
        e = self.expressions
        if type(domains) is not tuple or not domains:
            raise ValueError("nonempty immutable five-way domain coordinates required")
        if any(e.resolve(domain).size != len(DOMAIN_ACTIONS) for domain in domains):
            raise ValueError("Collatz domain expressions require the five-way sort")
        lower = tuple(e.table(domain, 3, _LOWER_TABLE) for domain in domains)
        upper = tuple(e.table(domain, 3, _UPPER_TABLE) for domain in domains)
        return (
            self._make_root(lower),
            self._make_root(upper),
        )

    def _make_root(self, domains: tuple[Expr, ...]) -> ThresholdGeometryID:
        return self.geometry.from_domains(domains)

    def _make_uniform_root(self, domain: Expr, width: int) -> ThresholdGeometryID:
        # A run is already the canonical spatial carrier.  Calling
        # from_domains here would expand it into one expression per cell.
        return ThresholdGeometryID(
            self.geometry.owner,
            words.run(domain.index, width),
        )

    def _make_id(
        self,
        lower: ThresholdGeometryID,
        upper: ThresholdGeometryID,
        width: int,
    ) -> CollatzDomainGeometryID:
        result = CollatzDomainGeometryID(self.owner, lower, upper, width)
        self._check(result)
        return result

    def from_domains(self, domains: tuple[Expr, ...]) -> CollatzDomainGeometryID:
        """Build geometry from five-way action expressions.

        Each expression has sort five and uses ``DOMAIN_ACTIONS`` order.  The
        two sort-three wire words are derived with finite tables and then
        handed to the existing ``ThresholdGeometry`` owner.
        """

        lower, upper = self._wire_expressions(domains)
        return self._make_id(lower, upper, len(domains))

    def from_action_indices(self, actions: tuple[int, ...]) -> CollatzDomainGeometryID:
        """Build fixed geometry from already classified action indices."""

        if type(actions) is not tuple or not actions:
            raise ValueError("nonempty immutable action geometry required")
        if any(
            type(action) is not int or not 0 <= action < len(DOMAIN_ACTIONS)
            for action in actions
        ):
            raise ValueError("Collatz action index outside DOMAIN_ACTIONS")
        domains = tuple(
            self.expressions.constant(len(DOMAIN_ACTIONS), action) for action in actions
        )
        return self.from_domains(domains)

    def from_digits(
        self, digits: tuple[int, ...], *, base: int = 64
    ) -> CollatzDomainGeometryID:
        """Classify a fixed radix-64 digit word once, then derive its wires."""

        if type(digits) is not tuple or not digits:
            raise ValueError("nonempty immutable radix digit geometry required")
        if type(base) is not int or base != 64:
            raise ValueError("Collatz domain geometry currently requires radix 64")
        if any(type(digit) is not int or not 0 <= digit < base for digit in digits):
            raise ValueError("radix-64 digit outside its finite alphabet")
        return self.from_action_indices(
            tuple(radix64_domain(digit) for digit in digits)
        )

    def from_uniform_action(
        self, action: int | Expr, width: int
    ) -> CollatzDomainGeometryID:
        """Build a counted uniform action without expanding its cells."""

        if type(width) is not int or width < 1:
            raise ValueError("positive uniform geometry width required")
        e = self.expressions
        action_expr: Expr
        if type(action) is int:
            if not 0 <= action < len(DOMAIN_ACTIONS):
                raise ValueError("Collatz action index outside DOMAIN_ACTIONS")
            action_expr = e.constant(len(DOMAIN_ACTIONS), action)
        else:
            if type(action) is not Expr:
                raise TypeError("uniform action requires an action expression or index")
            action_expr = action
            if e.resolve(action_expr).size != len(DOMAIN_ACTIONS):
                raise ValueError("uniform action requires the five-way sort")
        lower = e.table(action_expr, 3, _LOWER_TABLE)
        upper = e.table(action_expr, 3, _UPPER_TABLE)
        return self._make_id(
            self._make_uniform_root(lower, width),
            self._make_uniform_root(upper, width),
            width,
        )

    def from_uniform_digit(self, digit: int, width: int) -> CollatzDomainGeometryID:
        if type(digit) is not int or not 0 <= digit < 64:
            raise ValueError("radix-64 digit outside its finite alphabet")
        return self.from_uniform_action(radix64_domain(digit), width)

    def prefix_action(
        self, value: CollatzDomainGeometryID, stop: int
    ) -> CollatzPortPair:
        """Compose the two wire actions for the prefix ``[0, stop)``."""

        self._check(value)
        if type(stop) is not int or not 0 <= stop <= value.width:
            raise ValueError("carry boundary outside Collatz geometry")
        return CollatzPortPair(
            self.geometry.prefix_action(value.lower, stop),
            self.geometry.prefix_action(value.upper, stop),
        )

    def compose_actions(
        self, after: CollatzPortPair, before: CollatzPortPair
    ) -> CollatzPortPair:
        """Compose two sort-three wire actions through the native monoid."""

        e = self.expressions
        for pair in (after, before):
            if type(pair) is not CollatzPortPair:
                raise TypeError("Collatz action requires two wire expressions")
            if e.resolve(pair.lower).size != 3 or e.resolve(pair.upper).size != 3:
                raise ValueError("Collatz action composition requires domain wires")
        return CollatzPortPair(
            e.carry_compose(after.lower, before.lower),
            e.carry_compose(after.upper, before.upper),
        )

    def carry_at(
        self, value: CollatzDomainGeometryID, position: int, incoming: int
    ) -> CollatzPortPair:
        """Query one exact carry port without materializing the geometry."""

        self._check(value)
        if type(position) is not int or not 0 <= position <= value.width:
            raise ValueError("carry position outside Collatz geometry")
        if type(incoming) is not int or incoming not in (0, 1, 2):
            raise ValueError("Collatz incoming carry must be zero, one, or two")
        e = self.expressions
        lower, upper = int(incoming >= 1), int(incoming == 2)
        return CollatzPortPair(
            self.geometry.carry_at(value.lower, position, e.constant(2, lower)),
            self.geometry.carry_at(value.upper, position, e.constant(2, upper)),
        )

    def apply_action(self, action: CollatzPortPair, incoming: int) -> CollatzPortPair:
        """Apply a composed sort-three wire action to one carry port."""

        if type(action) is not CollatzPortPair:
            raise TypeError("Collatz action requires two wire expressions")
        if type(incoming) is not int or incoming not in (0, 1, 2):
            raise ValueError("Collatz incoming carry must be zero, one, or two")
        e = self.expressions
        if e.resolve(action.lower).size != 3 or e.resolve(action.upper).size != 3:
            raise ValueError("carry application requires domain wires")
        lower, upper = int(incoming >= 1), int(incoming == 2)
        return CollatzPortPair(
            e.carry_apply(action.lower, e.constant(2, lower)),
            e.carry_apply(action.upper, e.constant(2, upper)),
        )

    def evaluate(
        self, ports: CollatzPortPair, binding: tuple[int, ...] = ()
    ) -> tuple[int, int]:
        """Explicitly observe a pair of output bits in the owned arena."""

        if type(ports) is not CollatzPortPair:
            raise TypeError("Collatz ports require a CollatzPortPair")
        e = self.expressions
        if e.resolve(ports.lower).size != 2 or e.resolve(ports.upper).size != 2:
            raise ValueError("carry observations require Boolean wire outputs")
        observed = e.evaluate((ports.lower, ports.upper), binding)
        return observed[0], observed[1]

    def evaluate_carry(
        self,
        value: CollatzDomainGeometryID,
        position: int,
        incoming: int,
        binding: tuple[int, ...] = (),
    ) -> int:
        lower, upper = self.evaluate(self.carry_at(value, position, incoming), binding)
        if (lower, upper) not in ((0, 0), (1, 0), (1, 1)):
            raise AssertionError("Collatz wire staircase escaped")
        return lower + upper


__all__ = [
    "CollatzDomainGeometry",
    "CollatzDomainGeometryID",
    "CollatzPortPair",
]
