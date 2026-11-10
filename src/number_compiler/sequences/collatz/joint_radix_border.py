"""Source-bound radix-6 / CRT state for Collatz border selection.

The Moore output is only a finite candidate classification. Exact source
valuation guards and the producer-issued affine action remain responsible for
admitting every macro. F5 is transported through that same action before the
following candidate is inspected.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.three_power_radix import (
    ThreePowerRadixOrbit,
    difference_power_block,
)
from number_compiler.arithmetic.fields.walsh import walsh64_mod5
from number_compiler.arithmetic.functions.finite_observer import (
    minimize_finite_observer,
    partition_quotient_rows,
    partition_representatives,
)
from number_compiler.sequences.collatz.border_identity import (
    BOUNDARY_SELECTOR_IDENTITIES,
    BoundaryActionIdentity,
    CollatzSegmentIdentity,
    selector_guard_for,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.temporal_f5_observer import (
    CollatzF5AffineAction,
    project_dyadic_fields_f5,
)

_RADIX6_CELLS = 6**5


@dataclass(frozen=True, slots=True)
class JointRadix6Source:
    """Exact source with transported F5 state and finite low radix-6 cells."""

    source: int
    residue5: int
    low_binary: int
    low_radix6: int
    tripling_events: int = 0
    halving_events: int = 0

    def __post_init__(self) -> None:
        if type(self.source) is not int or self.source <= 0:
            raise ValueError("joint radix source must be a positive integer")
        if type(self.residue5) is not int or self.residue5 != self.source % 5:
            raise ValueError("source F5 register is inconsistent")
        if (
            type(self.low_radix6) is not int
            or self.low_radix6 != self.source % _RADIX6_CELLS
        ):
            raise ValueError("source radix-6 cells are inconsistent")
        if type(self.low_binary) is not int or self.low_binary != self.low_radix6 & 31:
            raise ValueError("source 2-adic register is inconsistent")
        if (
            type(self.tripling_events) is not int
            or self.tripling_events < 0
            or type(self.halving_events) is not int
            or self.halving_events < 0
            or self.tripling_events > self.halving_events
        ):
            raise ValueError("source event clock is inconsistent")

    @classmethod
    def from_source(cls, source: int) -> JointRadix6Source:
        if type(source) is not int or source <= 0:
            raise ValueError("source must be a positive integer")
        return cls(source, source % 5, source & 31, source % _RADIX6_CELLS)

    def require_source(self, source: int) -> None:
        if type(source) is not int or source != self.source:
            raise ValueError("foreign source for radix-6 border cursor")

    def binary_residue(self, bits: int) -> int:
        if type(bits) is not int or bits < 0:
            raise ValueError("2-adic precision must be nonnegative")
        if bits <= 5:
            return self.low_radix6 & ((1 << bits) - 1)
        if bits >= self.source.bit_length():
            return self.source
        return self.source & ((1 << bits) - 1)

    def decimal_residue(self, modulus: int) -> int:
        """Recover a 2**k*5 residue from the authenticated CRT coordinates."""
        if type(modulus) is not int or modulus not in (10, 20, 40, 80, 160):
            raise ValueError("selector accepts only its proved CRT guard moduli")
        power2 = modulus // 5
        low = self.binary_residue(power2.bit_length() - 1)
        correction = ((self.residue5 - low) * pow(power2, -1, 5)) % 5
        result = low + power2 * correction
        if result % modulus != self.source % modulus:
            raise AssertionError("CRT register did not recover its source residue")
        return result

    def radix6_digit(self, position: int) -> int:
        if type(position) is not int or position < 0:
            raise ValueError("radix-6 cell index must be nonnegative")
        if position < 5:
            return int((self.low_radix6 // 6**position) % 6)
        if 6**position > self.source:
            return 0
        return int((self.source // 6**position) % 6)

    def demand_v2_affine(self, scale: int, offset: int) -> int:
        if type(scale) is not int or type(offset) is not int:
            raise TypeError("2-adic valuation requires exact coefficients")
        numerator = scale * self.source + offset
        if numerator <= 0:
            raise ValueError("2-adic valuation requires a positive integer")
        return (numerator & -numerator).bit_length() - 1

    @property
    def even(self) -> bool:
        return self.low_binary & 1 == 0

    def after_action(
        self,
        action: DyadicTerminalFieldAction,
        endpoint: int,
        odd_symbols: int,
    ) -> JointRadix6Source:
        """Transport F5 before the next source-bound selector runs."""
        if type(action) is not DyadicTerminalFieldAction or not action.producer_issued:
            raise ValueError("radix successor requires producer-issued affine action")
        if (
            type(endpoint) is not int
            or endpoint <= 0
            or not action.certifies(self.source)
        ):
            raise ValueError("radix successor requires a certified positive endpoint")
        if action.endpoint(self.source) != endpoint:
            raise ValueError("radix successor endpoint disagrees with issued action")
        if type(odd_symbols) is not int or not 0 <= odd_symbols <= action.steps:
            raise ValueError("radix successor has an invalid event clock")
        projected = project_dyadic_fields_f5(action)
        next_f5 = projected.apply(self.residue5)
        if next_f5 != endpoint % 5:
            raise AssertionError("transported F5 action disagrees with exact endpoint")
        return JointRadix6Source(
            endpoint,
            next_f5,
            endpoint & 31,
            endpoint % _RADIX6_CELLS,
            self.tripling_events + odd_symbols,
            self.halving_events + action.steps,
        )

    def after_normalized(
        self, branch: int, count: int, endpoint: int
    ) -> JointRadix6Source:
        """Advance one compressed normalized branch inside a 6305 return."""
        if type(branch) is not int or branch not in (0, 1):
            raise ValueError("invalid normalized Collatz branch")
        if type(count) is not int or count < 1:
            raise ValueError("normalized branch length must be positive")
        if type(endpoint) is not int or endpoint <= 0:
            raise ValueError("normalized branch endpoint must be positive")
        if branch:
            projected = CollatzF5AffineAction(4, 3).power(count)
        else:
            projected = CollatzF5AffineAction(pow(3, count, 5), 0)
        next_f5 = projected.apply(self.residue5)
        if next_f5 != endpoint % 5:
            raise AssertionError("compressed F5 action disagrees with exact endpoint")
        return JointRadix6Source(
            endpoint,
            next_f5,
            endpoint & 31,
            endpoint % _RADIX6_CELLS,
            self.tripling_events + count * branch,
            self.halving_events + count,
        )

    @property
    def candidate_family(self) -> BoundaryActionIdentity | None:
        """Return the exact finite candidate from CRT residues.

        The complete Moore quotient is a finite audit helper below; ordinary
        selectors do not construct or refine that graph.
        """
        residue160 = self.decimal_residue(160)
        return candidate_family_for_residue160(residue160)

    @property
    def border_parent_candidate(self) -> bool:
        """Exact residue precheck shared with border-parent admission."""
        return has_border_parent_from_residue160(self.decimal_residue(160))

    @property
    def moore_guard_class(self) -> int:
        """Finite-audit class only; not used by production selectors."""
        return border_crt_moore().control(self)

    def demanded_difference_ports(
        self, base: int, places: int, *, walsh: bool = False
    ) -> dict[str, object]:
        """Demand homogeneous 3**q ports; these never authorize parity words."""
        if self.tripling_events < 1:
            raise ValueError("difference sequence requires one tripling event")
        if walsh and (base != 64 or places != 64):
            raise ValueError("Walsh64 requires 64 radix-64 carry positions")
        orbit = ThreePowerRadixOrbit("ordinary", self.tripling_events, base)
        ports = orbit.compact_ordinary_ports(places, include_source_boundaries=True)
        source_boundaries = ports.source_boundaries
        if source_boundaries is None:
            raise AssertionError("requested source-boundary projection was omitted")
        pivot = ports.difference_xor_mask
        return {
            "exponent": self.tripling_events,
            "base": base,
            "places": places,
            "tripling_carries": ports.carry_word,
            "add_borrow_mask": ports.add_borrow_mask,
            "successive_innovation_borrow_mask": ports.forward_borrow_mask,
            "difference_xor_mask": pivot,
            "tripling_high_mask": ports.high_mask,
            "tripling_low_mask": ports.low_mask,
            "walsh64_mod5": walsh64_mod5(pivot) if walsh else None,
            "source_boundaries": source_boundaries,
            "scope": "homogeneous tripling field; not a parity source guard",
        }

    def demanded_power_block(self, gap: int, modulus: int) -> tuple[int, int, int]:
        return difference_power_block(self.tripling_events, gap, modulus)


# Semantic registry table, not a source- or occurrence-keyed cache.  Its
# entries are immutable expected guard triples, with no retained source data.
# Only the selected identity is authenticated on lookup; a table row is never
# permission to execute a macro or bypass its valuation and parity cylinder.
_BORDER_CANDIDATE_SNAPSHOT = tuple(
    (identity, identity.structural_key(), selector_guard_for(identity).wire_value())
    for identity in BOUNDARY_SELECTOR_IDENTITIES
)
_BORDER_CANDIDATE_BY_RESIDUE: tuple[int | None, ...] = tuple(
    next(
        (
            index
            for index, (_identity, _key, (wanted, modulus, _lower)) in enumerate(
                _BORDER_CANDIDATE_SNAPSHOT
            )
            if residue % modulus == wanted
        ),
        None,
    )
    for residue in range(160)
)


def candidate_family_for_residue160(
    residue160: int,
) -> BoundaryActionIdentity | None:
    """Return one authenticated candidate without rescanning every cycle."""
    if type(residue160) is not int or not 0 <= residue160 < 160:
        raise ValueError("candidate projection requires a radix-160 residue")
    index = _BORDER_CANDIDATE_BY_RESIDUE[residue160]
    if index is None:
        return None
    identity, structural_key, guard_wire = _BORDER_CANDIDATE_SNAPSHOT[index]
    # Detect forged mutations, even via object.__setattr__ on frozen ports.
    if (
        identity.structural_key() != structural_key
        or selector_guard_for(identity).wire_value() != guard_wire
        or residue160 % guard_wire[1] != guard_wire[0]
    ):
        raise ValueError("registered Collatz border guard changed after admission")
    return identity


def has_border_parent_from_residue160(residue160: int) -> bool:
    """Whether the border-return producer has one of its exact entry residues."""
    if type(residue160) is not int or not 0 <= residue160 < 160:
        raise ValueError("border-parent projection requires a radix-160 residue")
    return residue160 % 10 in (0, 3, 5) or residue160 % 20 == 6


def candidate_family_guard(
    identity: CollatzSegmentIdentity,
) -> tuple[int, int, int]:
    """Return the exact selector class and minimum source for one label.

    The residue modulus is the coarsest congruence on which the complete
    classifier has this one typed output.  It is used only alongside the
    issued action's exact parity cylinder.  The final component retains the
    one noncongruence selector condition: ENTRY_421 requires source > 4.
    """
    for candidate in BOUNDARY_SELECTOR_IDENTITIES:
        if identity == candidate:
            guard = selector_guard_for(candidate)
            return guard.residue, guard.modulus, guard.minimum_source
    raise ValueError("identity is not a radix-6 candidate-family output")


@dataclass(frozen=True, slots=True)
class BorderCRTMoore:
    """Complete finite candidate Moore machine over the two CRT lift bits."""

    class_ids: tuple[int, ...]
    outputs: tuple[BoundaryActionIdentity | None, ...]
    successors: tuple[tuple[int, int], ...]
    rounds: int

    @property
    def classes(self) -> int:
        return len(self.outputs)

    def control(self, source: JointRadix6Source) -> int:
        if type(source) is not JointRadix6Source:
            raise TypeError("CRT Moore control requires a source-bound state")
        return self.class_ids[source.decimal_residue(160)]

    def family(self, source: JointRadix6Source) -> BoundaryActionIdentity | None:
        return self.outputs[self.control(source)]


def border_crt_moore() -> BorderCRTMoore:
    """Refine every residue and both lift-bit inputs on demand."""
    rows: list[tuple[int, int]] = []
    for residue in range(160):
        successors: list[int] = []
        for high_lift_bit in (0, 1):
            lifted = residue + 160 * high_lift_bit
            next_source = lifted // 2 if lifted % 2 == 0 else (3 * lifted + 1) // 2
            successors.append(next_source % 160)
        rows.append((successors[0], successors[1]))
    labels = tuple(candidate_family_for_residue160(residue) for residue in range(160))
    result = minimize_finite_observer(tuple(rows), labels)
    representatives = partition_representatives(result.class_ids, result.classes)
    transitions = partition_quotient_rows(rows, result.class_ids, result.classes)
    if any(len(row) != 2 for row in transitions):
        raise AssertionError("CRT Moore lost a source-lift input")
    typed_transitions: list[tuple[int, int]] = []
    for row in transitions:
        if len(row) != 2:
            raise AssertionError("CRT Moore lost a source-lift input")
        left, right = row
        if left is None or right is None:
            raise AssertionError("CRT Moore quotient has an unresolved transition")
        typed_transitions.append((left, right))
    return BorderCRTMoore(
        result.class_ids,
        tuple(labels[representative] for representative in representatives),
        tuple(typed_transitions),
        result.rounds,
    )


__all__ = [
    "BorderCRTMoore",
    "JointRadix6Source",
    "border_crt_moore",
    "candidate_family_for_residue160",
    "candidate_family_guard",
    "has_border_parent_from_residue160",
]
