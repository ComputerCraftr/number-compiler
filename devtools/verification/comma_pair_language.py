"""Bounded differential audit of punctured comma pair-block observations.

This is not a production constructor or branch certificate. Exact endpoints
and weights remain occurrence data. In particular, a complete even block can
share its reduced response while its first partial block cannot.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    centered_carry_fn,
    compose_carry_fn,
)
from number_compiler.arithmetic.functions.finite_observer import (
    minimize_finite_observer,
)
from number_compiler.sequences.comma.arithmetic import (
    comma_port_next,
    comma_port_previous,
    punctured_digit_port,
)
from number_compiler.sequences.comma.cycle_spatial import CycleSpatialState


@dataclass(frozen=True, slots=True)
class PairLanguage:
    """Recursive observation with a phase, not a retained literal word.

    ``first is None`` is the all-neutral predicate. It is not stored twice.
    The length phase routes the F5 skew product; it is not an exact width.
    """

    phase: int
    carry: CarryFn
    f2: int
    f5: int
    first: int | None

    @classmethod
    def leaf(cls, pair_sum: int) -> PairLanguage:
        if type(pair_sum) is not int or not 0 <= pair_sum <= 18:
            raise ValueError("pair language leaf requires a decimal sum in 0..18")
        defect = pair_sum - 9
        return cls(
            1,
            centered_carry_fn(defect),
            defect % 2,
            defect % 5,
            None if defect == 0 else pair_sum // 2 % 5,
        )

    def then(self, right: PairLanguage) -> PairLanguage:
        """Concatenate left then right, preserving the ordered puncture."""
        return PairLanguage(
            (self.phase + right.phase) % 4,
            compose_carry_fn(right.carry, self.carry),
            (self.f2 + right.f2) % 2,
            (self.f5 + pow(2, self.phase, 5) * right.f5) % 5,
            self.first if self.first is not None else right.first,
        )

    @property
    def residue_key(self) -> tuple[CarryFn, int, int]:
        return self.carry, self.f2, self.f5


PAIR_IDENTITY = PairLanguage(0, CarryFn.ID, 0, 0, None)


@dataclass(frozen=True, slots=True)
class PairBlock:
    """Exact physical occurrence; endpoint must not be replaced by a class ID."""

    leading: int
    source: int
    endpoint: int
    width: int
    weight: int
    language: PairLanguage
    midpoint: int

    def then(self, right: PairBlock) -> PairBlock:
        if self.leading != right.leading or self.endpoint != right.source:
            raise ValueError("comma pair blocks have different seam bindings")
        if self.width != right.width:
            raise ValueError("midpoint publication requires equally sized children")
        return PairBlock(
            self.leading,
            self.source,
            right.endpoint,
            self.width + right.width,
            self.weight + right.weight,
            self.language.then(right.language),
            pair_center(self.leading, self.endpoint),
        )


def even_port_key(leading: int, digit: int) -> tuple[int, int]:
    """Canonical complete-even-response key; never an exact occurrence handle."""
    comma_port_previous(leading, digit)  # Validate the physical port domain.
    return leading, digit - 5 if leading == 5 and digit > 5 else digit


def pair_center(leading: int, digit: int) -> int:
    return (digit + comma_port_previous(leading, digit)) // 2 % 5


def physical_port_leaf(leading: int, digit: int) -> PairBlock:
    """Include physical zero as the HOL trace does; live ports omit zero."""
    previous = comma_port_previous(leading, digit)
    weight = punctured_digit_port(leading, digit).dwell if digit else int(leading == 9)
    return PairBlock(
        leading,
        digit,
        comma_port_next(leading, digit),
        1,
        weight,
        PairLanguage.leaf(digit + previous),
        pair_center(leading, digit),
    )


def pair_block_levels(depth: int) -> tuple[tuple[PairBlock, ...], ...]:
    """Audit powers by completed-child joins over the declared 90-port universe."""
    if type(depth) is not int or not 0 <= depth <= 10:
        raise ValueError("finite pair audit supports levels 0..10")
    layer = tuple(physical_port_leaf(f, d) for f in range(1, 10) for d in range(10))
    levels = [layer]
    for _ in range(depth):
        layer = tuple(
            left.then(layer[(left.leading - 1) * 10 + left.endpoint]) for left in layer
        )
        levels.append(layer)
    return tuple(levels)


@dataclass(frozen=True, slots=True)
class PairQuotientAudit:
    width: int
    exact_occurrences: int
    reduced_actions: int
    candidate_classes: int
    midpoint_classes: int
    first_defect_classes: int
    bare_residue_conflicts: int
    punctured_conflicts: int
    endpoint_conflicts: int


def audit_pair_quotients(depth: int = 10) -> tuple[PairQuotientAudit, ...]:
    """Refine output (sector, source Q19, weight) under the block endpoint.

    Counts are measured, never used to define an action or authorize a merge.
    The exact endpoint remains outside this reduced Moore observation.
    """
    q19 = {
        (f, d): CycleSpatialState.from_port(f, d)
        for f in range(1, 10)
        for d in range(10)
    }
    rows = []
    for layer in pair_block_levels(depth):
        outputs = tuple((b.leading, q19[b.leading, b.source], b.weight) for b in layer)
        minimized = minimize_finite_observer(
            tuple(((b.leading - 1) * 10 + b.endpoint,) for b in layer), outputs
        )
        candidates: dict[tuple[int, CycleSpatialState, int], set[int]] = defaultdict(
            set
        )
        endpoints: dict[tuple[int, CycleSpatialState, int], set[int]] = defaultdict(set)
        bare: dict[object, set[int]] = defaultdict(set)
        punctured: dict[object, set[int]] = defaultdict(set)
        firsts: dict[object, set[int]] = defaultdict(set)
        for block, action in zip(layer, minimized.class_ids, strict=True):
            f, d = block.leading, block.source
            key = (f, q19[f, d], pair_center(f, d))
            candidates[key].add(action)
            endpoints[key].add(block.endpoint)
            prefix = (f, q19[f, d], block.language.residue_key)
            bare[prefix].add(action)
            punctured[prefix, block.midpoint].add(action)
            firsts[prefix, block.language.first].add(action)
        rows.append(
            PairQuotientAudit(
                layer[0].width,
                len({(b.leading, b.endpoint, b.weight) for b in layer}),
                minimized.classes,
                len(candidates),
                len(punctured),
                len(firsts),
                sum(len(values) > 1 for values in bare.values()),
                sum(len(values) > 1 for values in punctured.values())
                + sum(len(values) > 1 for values in firsts.values())
                + sum(len(values) > 1 for values in candidates.values()),
                sum(len(values) > 1 for values in endpoints.values()),
            )
        )
    return tuple(rows)
