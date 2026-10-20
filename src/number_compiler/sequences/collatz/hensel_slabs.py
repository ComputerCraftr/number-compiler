"""Reduced labelled 2-adic cylinder unions and admitted branch composition.

Labels denote idempotent forcing observations, not an ordered event trace.
Different labels remain simultaneously observable on overlaps. Transport and
its admitted branch domain accompany the slab; the slab alone is not a whole
Collatz occurrence or a production temporal-cache key.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from itertools import chain

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.exact_tree_context import (
    require_endpoint_construction,
)
from number_compiler.arithmetic.functions.decision import MultiTerminalDecisionArena
from number_compiler.sequences.collatz.hensel_cylinders import (
    HenselAffineBlock,
    HenselCylinder,
)

Atom = tuple[int, HenselCylinder]


def normalize_cylinders(
    cylinders: Iterable[HenselCylinder], *, max_work: int = 1000000
) -> tuple[HenselCylinder, ...]:
    """Unique maximal prefix cover, removing subsumption and equal siblings."""
    if type(max_work) is not int or max_work < 1:
        raise ValueError("Hensel normalization needs a positive work budget")
    work = 0
    unique: set[HenselCylinder] = set()
    for cylinder in cylinders:
        if type(cylinder) is not HenselCylinder:
            raise TypeError("Hensel normalization needs cylinders")
        work += 2 * (cylinder.bits + 1)
        if work > max_work:
            raise BlockContextBudgetExceeded(
                "Hensel prefix normalization work budget exceeded"
            )
        unique.add(cylinder)
    live: set[HenselCylinder] = set()
    for cylinder in sorted(unique):
        if any(
            HenselCylinder(q, cylinder.residue) in live
            for q in range(cylinder.bits + 1)
        ):
            continue
        current = cylinder
        while current.bits:
            sibling = HenselCylinder(
                current.bits, current.residue ^ (1 << (current.bits - 1))
            )
            if sibling not in live:
                break
            live.remove(sibling)
            current = HenselCylinder(current.bits - 1, current.residue)
        live.add(current)
    return tuple(sorted(live))


@dataclass(frozen=True, slots=True)
class HenselSlabID:
    owner: object
    index: int


@dataclass(frozen=True, slots=True)
class _Slab:
    atoms: tuple[Atom, ...]
    roots: tuple[tuple[int, int], ...]


class HenselSlabArena:
    """Bounded research algebra; the existing decision arena owns DAG reduction.

    Each label has one Boolean membership DAG. Equal siblings, subsumed atoms,
    and identical subtries merge; no Cartesian assignments are sampled. A
    separate maximal cylinder cover makes affine pullback exact without
    expanding skipped decision levels into assignment tables.
    """

    def __init__(
        self,
        *,
        max_precision: int = 2048,
        max_atoms: int = 4096,
        max_work: int = 1000000,
    ) -> None:
        require_endpoint_construction()
        if any(
            type(n) is not int or n < 1 for n in (max_precision, max_atoms, max_work)
        ):
            raise ValueError("Hensel slab limits must be positive exact integers")
        HenselCylinder(max_precision, 0)
        self.max_precision, self.max_atoms, self.max_work = (
            max_precision,
            max_atoms,
            max_work,
        )
        self._owner = object()
        self._nodes: list[_Slab] = []
        self._keys: dict[tuple[Atom, ...], HenselSlabID] = {}
        self._graphs: dict[tuple[HenselCylinder, ...], int] = {}
        self.decisions = MultiTerminalDecisionArena((2,) * max_precision)
        self.primitive_constructions = 0
        self.temporal_compositions = 0

    def resolve(self, slab: HenselSlabID) -> _Slab:
        if (
            type(slab) is not HenselSlabID
            or slab.owner is not self._owner
            or type(slab.index) is not int
            or not 0 <= slab.index < len(self._nodes)
        ):
            raise ValueError("foreign Hensel slab identity")
        return self._nodes[slab.index]

    def intern(self, atoms: Iterable[Atom]) -> HenselSlabID:
        require_endpoint_construction()
        groups: dict[int, list[HenselCylinder]] = {}
        for count, (label, cylinder) in enumerate(atoms, start=1):
            if count > self.max_atoms:
                raise BlockContextBudgetExceeded("Hensel slab atom budget exceeded")
            if (
                type(label) is not int
                or label < 0
                or type(cylinder) is not HenselCylinder
            ):
                raise ValueError(
                    "forcing atoms need exact nonnegative labels and cylinders"
                )
            if cylinder.bits > self.max_precision:
                raise BlockContextBudgetExceeded(
                    "Hensel slab precision budget exceeded"
                )
            groups.setdefault(label, []).append(cylinder)
        canonical = tuple(
            (label, c)
            for label, group in sorted(groups.items())
            for c in normalize_cylinders(group, max_work=self.max_work)
        )
        if canonical in self._keys:
            return self._keys[canonical]
        if len(self._nodes) >= self.max_atoms:
            raise BlockContextBudgetExceeded("Hensel slab interner budget exceeded")
        roots: list[tuple[int, int]] = []
        for label in sorted(groups):
            cover = tuple(c for effect, c in canonical if effect == label)
            root = self._graphs.get(cover)
            if root is None:
                # Bound the constructor's coordinate/generator workspace and
                # worst-case added DAG nodes before invoking the shared owner.
                cost = sum(c.bits + 1 for c in cover)
                if cost + self.decisions.node_count > self.max_work:
                    raise BlockContextBudgetExceeded(
                        "Hensel decision construction budget exceeded"
                    )
                root = self.decisions.build_prefix_union(
                    tuple((c.residue >> i) & 1 for i in range(c.bits)) for c in cover
                )
                self._graphs[cover] = root
            roots.append((label, root))
        result = HenselSlabID(self._owner, len(self._nodes))
        self._nodes.append(_Slab(canonical, tuple(roots)))
        self._keys[canonical] = result
        return result

    def union(self, left: HenselSlabID, right: HenselSlabID) -> HenselSlabID:
        return self.intern((*self.resolve(left).atoms, *self.resolve(right).atoms))

    def restrict(
        self, slab: HenselSlabID, domain: HenselCylinder | None
    ) -> HenselSlabID:
        if domain is None:
            self.resolve(slab)
            return self.intern(())
        return self.intern(
            (label, cut)
            for label, c in self.resolve(slab).atoms
            if (cut := c.intersect(domain)) is not None
        )

    def pullback(self, slab: HenselSlabID, block: HenselAffineBlock) -> HenselSlabID:
        return self.intern(self._pulled_atoms(slab, block))

    def _pulled_atoms(
        self, slab: HenselSlabID, block: HenselAffineBlock
    ) -> Iterable[Atom]:
        return ((label, c.pullback(block)) for label, c in self.resolve(slab).atoms)

    def evaluate(self, slab: HenselSlabID, value: int) -> frozenset[int]:
        if type(value) is not int:
            raise TypeError("forcing input must be an exact integer")
        return frozenset(
            label for label, c in self.resolve(slab).atoms if c.contains(value)
        )

    def metrics(self, slab: HenselSlabID) -> dict[str, int]:
        node = self.resolve(slab)
        pending = [root for _label, root in node.roots]
        seen: set[int] = set()
        while pending:
            index = pending.pop()
            if index in seen:
                continue
            seen.add(index)
            pending.extend(self.decisions.children_of(index))
        return {
            "atoms": len(node.atoms),
            "dag_nodes": len(seen),
            "labels": len(node.roots),
            "live_precision": max((c.bits for _, c in node.atoms), default=0),
            "retained_dag_nodes": self.decisions.node_count,
            "slab_ids": len(self._nodes),
        }

    def primitive(self, valuation: int, slab: HenselSlabID) -> HenselSlabBlock:
        """One exact accelerated-odd branch, not an inferred valuation choice."""
        self.resolve(slab)
        if type(valuation) is not int or valuation < 1:
            raise ValueError("accelerated branch valuation must be positive")
        if valuation + 1 > self.max_precision:
            raise BlockContextBudgetExceeded("branch domain exceeds slab precision")
        domain = HenselCylinder.from_root(valuation + 1, 1, 1 - (1 << valuation))
        return self.primitive_block(HenselAffineBlock(1, valuation, 1), domain, slab)

    def primitive_block(
        self,
        transport: HenselAffineBlock,
        domain: HenselCylinder | None,
        slab: HenselSlabID,
    ) -> HenselSlabBlock:
        """Admit one caller-specified integral affine map, without discovering branches."""
        result = HenselSlabBlock(transport, domain, slab)
        self._validate_block(result)
        self.primitive_constructions += 1
        return result

    def _validate_block(self, block: HenselSlabBlock) -> None:
        if (
            type(block) is not HenselSlabBlock
            or type(block.transport) is not HenselAffineBlock
        ):
            raise TypeError("Hensel composition needs an affine slab block")
        self.resolve(block.slab)
        if block.domain is not None:
            if type(block.domain) is not HenselCylinder:
                raise TypeError("Hensel branch domain must be a cylinder")
            if block.domain.bits > self.max_precision:
                raise BlockContextBudgetExceeded("branch domain exceeds slab precision")
            if not HenselCylinder(0, 0).pullback(block.transport).covers(block.domain):
                raise ValueError("branch domain admits nonintegral transport")

    def compose(
        self, before: HenselSlabBlock, after: HenselSlabBlock
    ) -> HenselSlabBlock:
        """Canon(G1 union PB_B1(G2)), retaining the complete branch domain.

        The slab records idempotent labels on integral inputs. Evaluation of a
        temporal block additionally requires its exact itinerary domain. Union
        does not by itself preserve the chronological order of event effects.
        """
        self._validate_block(before)
        self._validate_block(after)
        domain = None
        if before.domain is not None and after.domain is not None:
            domain = before.domain.intersect(after.domain.pullback(before.transport))
            if domain is not None and domain.bits > self.max_precision:
                raise BlockContextBudgetExceeded(
                    "composed branch domain exceeds precision"
                )
        # Normalize the interacted output before interning. A pulled atom can
        # disappear under a first-block atom; its temporary DAG must not survive.
        slab = self.intern(
            chain(
                self.resolve(before.slab).atoms,
                self._pulled_atoms(after.slab, before.transport),
            )
        )
        result = HenselSlabBlock(before.transport.then(after.transport), domain, slab)
        self.temporal_compositions += 1
        return result


@dataclass(frozen=True, slots=True)
class HenselSlabBlock:
    """An admitted affine branch; domain=None denotes the empty input set."""

    transport: HenselAffineBlock
    domain: HenselCylinder | None
    slab: HenselSlabID
