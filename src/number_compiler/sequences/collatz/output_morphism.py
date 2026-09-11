"""Geometry-first quotient control with composable directional value wires.

Only unary primitive alphabets are enumerated. Composed guards operate on
reduced bit functions, never on sets of possible digits or concrete register
valuations. These arrows do not certify a whole powered Collatz controller.
"""

from __future__ import annotations

from number_compiler.arithmetic.carry.collatz_output_quotient import (
    RADIX64_DIRECTIONAL_DOMAIN_COUNTS,
    RADIX64_DIRECTIONAL_DOMAIN_TABLES,
    RADIX64_FREE_CARRY_ACTIONS,
    RADIX64_FREE_GROWTH_TABLE,
    RADIX64_LEFT_VIEW_CLASSES,
    RADIX64_RIGHT_VIEW_CLASSES,
    radix64_correction,
    radix64_domain,
    radix64_growth_edge,
    radix64_free_directional_row,
    radix64_join_shift_views,
    radix64_raw_class,
    radix64_shift,
    radix64_shift_views,
    CORRECTIONS,
    DOMAIN_ACTIONS,
)
from number_compiler.arithmetic.functions.finite_function_types import BOOL, AtomSort
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)

DIGIT = AtomSort("collatz-radix64-digit", 64)
CARRY = AtomSort("collatz-mul3-carry", 3)
DOMAIN = AtomSort("collatz-two-wire-domain", 5)
RESIDUAL_SHIFT = AtomSort("collatz-residual-shift", 6)
FREE_CARRY_ACTION = AtomSort(
    "collatz-free-directional-carry-action", len(RADIX64_FREE_CARRY_ACTIONS)
)
RAW_CLASS = AtomSort("collatz-radix64-raw-output-class", 17)
CORRECTION = AtomSort("collatz-radix64-carry-correction", 9)
QUOTIENT_VIEW = tuple(
    AtomSort(f"collatz-directional-quotient-e{shift}", 64 >> shift)
    for shift in range(6)
)
REMAINDER_VIEW = tuple(
    AtomSort(f"collatz-directional-remainder-e{shift}", 1 << shift)
    for shift in range(6)
)
LEFT_DOMAIN_VIEW = tuple(
    AtomSort(f"collatz-left-domain-view-e{shift}", counts[0])
    for shift, counts in enumerate(RADIX64_DIRECTIONAL_DOMAIN_COUNTS)
)
RIGHT_DOMAIN_VIEW = tuple(
    AtomSort(f"collatz-right-domain-view-e{shift}", counts[1])
    for shift, counts in enumerate(RADIX64_DIRECTIONAL_DOMAIN_COUNTS)
)


class CollatzOutputMorphism:
    """Stateless operations owned by the caller's finite-function arena."""

    def __init__(self, bits: BitFunctionArena) -> None:
        if type(bits) is not BitFunctionArena:
            raise TypeError("Collatz output requires an owned bit-function arena")
        self.bits = bits

    def _domain(self, value: FactoredFunctionID, sort: AtomSort) -> None:
        if self.bits.resolve(value).signature.output != sort:
            raise ValueError("Collatz output function has another channel sort")

    def classify(self, digit: FactoredFunctionID) -> FactoredFunctionID:
        """Seventeen-way diagnostic observer; excluded from action construction."""
        self._domain(digit, DIGIT)
        return self.bits.map_atoms(
            digit, RAW_CLASS, tuple(radix64_raw_class(d) for d in range(64))
        )

    def domain(self, digit: FactoredFunctionID) -> FactoredFunctionID:
        self._domain(digit, DIGIT)
        return self.bits.map_atoms(
            digit, DOMAIN, tuple(radix64_domain(d) for d in range(64))
        )

    def _select_carry(
        self, carry: FactoredFunctionID, branches: tuple[FactoredFunctionID, ...]
    ) -> FactoredFunctionID:
        one = self.bits.map_atoms(carry, BOOL, (0, 1, 0))
        two = self.bits.map_atoms(carry, BOOL, (0, 0, 1))
        return self.bits.select(
            two, branches[2], self.bits.select(one, branches[1], branches[0])
        )

    def _select_index(
        self,
        index: FactoredFunctionID,
        branches: tuple[FactoredFunctionID, ...],
    ) -> FactoredFunctionID:
        node = self.bits.resolve(index)
        if (
            type(node.signature.output) is not AtomSort
            or len(branches) != node.signature.output.cardinality
            or not branches
        ):
            raise ValueError("directional pairing requires one branch per view")
        result = branches[0]
        for choice in range(1, len(branches)):
            predicate = self.bits.map_atoms(
                index,
                BOOL,
                tuple(int(value == choice) for value in range(len(branches))),
            )
            result = self.bits.select(predicate, branches[choice], result)
        return result

    def carry_apply(
        self, domain: FactoredFunctionID, incoming: FactoredFunctionID
    ) -> FactoredFunctionID:
        """Compose a five-domain controller with a symbolic incoming carry."""
        self._domain(domain, DOMAIN)
        self._domain(incoming, CARRY)
        branches = tuple(
            self.bits.map_atoms(domain, CARRY, tuple(a[c] for a in DOMAIN_ACTIONS))
            for c in range(3)
        )
        return self._select_carry(incoming, branches)

    def raw(
        self, digit: FactoredFunctionID, carry: FactoredFunctionID
    ) -> tuple[FactoredFunctionID, FactoredFunctionID]:
        """Derive carry from geometry, then form the exact post-carry value."""
        self._domain(carry, CARRY)
        outgoing = self.carry_apply(self.domain(digit), carry)
        transported = self.bits.map_atoms(
            digit, DIGIT, tuple(3 * d % 64 for d in range(64))
        )
        value = self.bits.add(transported, carry, DIGIT, wrap=True)
        self.bits.ledger.bump("collatz_output_morphism_raw_compositions")
        return outgoing, value

    def correction(
        self, carry: FactoredFunctionID, outgoing: FactoredFunctionID
    ) -> FactoredFunctionID:
        """Index in the nine-valued carry correction alphabet."""
        self._domain(carry, CARRY)
        self._domain(outgoing, CARRY)
        base = self.bits.map_atoms(
            outgoing,
            CORRECTION,
            tuple(CORRECTIONS.index(radix64_correction(0, c)) for c in range(3)),
        )
        return self.bits.add(base, carry, CORRECTION)

    def shift(
        self, raw: FactoredFunctionID, adjacent: FactoredFunctionID, shift: int
    ) -> FactoredFunctionID:
        """Join adjacent directional value streams into one exact digit."""
        self._domain(raw, DIGIT)
        self._domain(adjacent, DIGIT)
        left = self.quotient_view(raw, shift)
        right = self.remainder_view(adjacent, shift)
        return self.join_directional(left, right, shift)

    def join_directional(
        self,
        quotient: FactoredFunctionID,
        adjacent_remainder: FactoredFunctionID,
        shift: int,
    ) -> FactoredFunctionID:
        """Join already-composed neighboring value streams at one position."""
        radix64_shift_views(0, shift)
        self._domain(quotient, QUOTIENT_VIEW[shift])
        self._domain(adjacent_remainder, REMAINDER_VIEW[shift])
        widened = self.bits.map_atoms(quotient, DIGIT, tuple(range(64 >> shift)))
        high = self.bits.map_atoms(
            adjacent_remainder,
            DIGIT,
            tuple(
                radix64_join_shift_views(0, remainder, shift)
                for remainder in range(1 << shift)
            ),
        )
        return self.bits.add(widened, high, DIGIT)

    def quotient_view(self, raw: FactoredFunctionID, shift: int) -> FactoredFunctionID:
        """The left-moving exact value stream ``raw >> shift``."""
        self._domain(raw, DIGIT)
        radix64_shift_views(0, shift)  # Validate before publication.
        return self.bits.map_atoms(
            raw,
            QUOTIENT_VIEW[shift],
            tuple(radix64_shift_views(d, shift)[0] for d in range(64)),
        )

    def remainder_view(self, raw: FactoredFunctionID, shift: int) -> FactoredFunctionID:
        """The right-moving exact value stream ``raw mod 2**shift``."""
        self._domain(raw, DIGIT)
        radix64_shift_views(0, shift)  # Validate before publication.
        return self.bits.map_atoms(
            raw,
            REMAINDER_VIEW[shift],
            tuple(radix64_shift_views(d, shift)[1] for d in range(64)),
        )

    def directional(
        self, raw: FactoredFunctionID, shift: int
    ) -> tuple[FactoredFunctionID, FactoredFunctionID]:
        """Split an exact digit into independently composable shift views."""
        return self.quotient_view(raw, shift), self.remainder_view(raw, shift)

    def left_domain_view(
        self, raw: FactoredFunctionID, shift: int
    ) -> FactoredFunctionID:
        """Reduce one left-moving value to its next-domain response class."""
        quotient = self.quotient_view(raw, shift)
        return self.bits.map_atoms(
            quotient, LEFT_DOMAIN_VIEW[shift], RADIX64_LEFT_VIEW_CLASSES[shift]
        )

    def right_domain_view(
        self, raw: FactoredFunctionID, shift: int
    ) -> FactoredFunctionID:
        """Reduce one right-moving value to its next-domain response class."""
        remainder = self.remainder_view(raw, shift)
        return self.bits.map_atoms(
            remainder, RIGHT_DOMAIN_VIEW[shift], RADIX64_RIGHT_VIEW_CLASSES[shift]
        )

    def directional_domain_views(
        self, raw: FactoredFunctionID, shift: int
    ) -> tuple[FactoredFunctionID, FactoredFunctionID]:
        """Reduce one exact post-carry value into separate domain consumers."""
        return self.left_domain_view(raw, shift), self.right_domain_view(raw, shift)

    def free_directional_actions(
        self,
        digit: FactoredFunctionID,
        incoming: FactoredFunctionID,
        shift: FactoredFunctionID,
    ) -> tuple[FactoredFunctionID, FactoredFunctionID]:
        """Pull back both consumers while carry and root shift remain free.

        The exact digit is an occurrence input. No exact raw midpoint or bound
        ``(carry, shift)`` fiber is published by this action.
        """
        self._domain(digit, DIGIT)
        self._domain(incoming, CARRY)
        self._domain(shift, RESIDUAL_SHIFT)
        left_by_carry = []
        right_by_carry = []
        for carry in range(3):
            left_by_shift = []
            right_by_shift = []
            for phase in range(6):
                actions = radix64_free_directional_row(phase, carry)
                left_by_shift.append(
                    self.bits.map_atoms(
                        digit,
                        FREE_CARRY_ACTION,
                        tuple(action[0] for action in actions),
                    )
                )
                right_by_shift.append(
                    self.bits.map_atoms(
                        digit,
                        FREE_CARRY_ACTION,
                        tuple(action[1] for action in actions),
                    )
                )
            left_by_carry.append(self._select_index(shift, tuple(left_by_shift)))
            right_by_carry.append(self._select_index(shift, tuple(right_by_shift)))
        result = (
            self._select_carry(incoming, tuple(left_by_carry)),
            self._select_carry(incoming, tuple(right_by_carry)),
        )
        self.bits.ledger.bump("collatz_free_consumer_compilations")
        return result

    def shift_domain(
        self, raw: FactoredFunctionID, adjacent: FactoredFunctionID, shift: int
    ) -> FactoredFunctionID:
        """Compute the next domain from directional streams, without a digit leaf."""
        left = self.left_domain_view(raw, shift)
        right = self.right_domain_view(adjacent, shift)
        return self.pair_domain_views(left, right, shift)

    def pair_domain_views(
        self,
        left: FactoredFunctionID,
        adjacent_right: FactoredFunctionID,
        shift: int,
    ) -> FactoredFunctionID:
        """Pair already-composed domain views without an intermediate digit."""
        radix64_shift(0, 0, shift)
        self._domain(left, LEFT_DOMAIN_VIEW[shift])
        self._domain(adjacent_right, RIGHT_DOMAIN_VIEW[shift])
        rows = RADIX64_DIRECTIONAL_DOMAIN_TABLES[shift]
        branches = tuple(
            self.bits.map_atoms(adjacent_right, DOMAIN, row) for row in rows
        )
        result = self._select_index(left, branches)
        self.bits.ledger.bump("collatz_directional_domain_compositions")
        return result

    def growth(self, carry: FactoredFunctionID, shift: int) -> FactoredFunctionID:
        """A three-valued output edge, with no generic terminal digit state."""
        self._domain(carry, CARRY)
        radix64_growth_edge(0, shift)
        return self.bits.map_atoms(
            carry, DIGIT, tuple(radix64_growth_edge(c, shift) for c in range(3))
        )

    def free_growth(
        self, carry: FactoredFunctionID, shift: FactoredFunctionID
    ) -> FactoredFunctionID:
        """Defer the growth edge until the root query supplies its shift."""
        self._domain(carry, CARRY)
        self._domain(shift, RESIDUAL_SHIFT)
        branches = tuple(
            self.bits.map_atoms(carry, DIGIT, table)
            for table in RADIX64_FREE_GROWTH_TABLE
        )
        return self._select_index(shift, branches)
