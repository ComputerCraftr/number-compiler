"""Source-independent symbolic innovations for reverse/add affine actions.

This module owns only the additive ``B`` in ``S -> M*S + B``.  It does not
own an authenticated source occurrence, threshold predicates, carry discovery,
or a temporal clause constructor.  Those authorities must remain in the
surrounding action/cylinder owner.

Innovations are hash-consed DAGs made from immutable primitive semantic atoms,
closed cylinder charts, radial multipliers, and locally normalized signed sums.  No coefficient
word, carry vector, event history, or future ``(time, index)`` query is stored.
Projection to the existing bounded cyclotomic owner is explicit and total: a
caller must supply every primitive atom's residue, and an unresolved atom is an
error rather than an opaque future callback.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from copy import deepcopy
from dataclasses import dataclass
from typing import TypeAlias

from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.arithmetic.polynomials.cyclotomic_ring import CyclotomicRing
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_radial_quotient,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList

MAX_PRIMITIVE_IDENTITY_UNITS = 256
MAX_PRIMITIVE_IDENTITY_DEPTH = 32
MAX_CYCLOTOMIC_PROJECTION_ORDER = 16
MAX_CYCLOTOMIC_PROJECTION_BITS = 64


def _validate_bounded_primitive_identity(identity: SemanticIdentity) -> None:
    pending: list[tuple[object, int]] = [(identity, 0)]
    seen: set[int] = set()
    identities: list[SemanticIdentity] = []
    units = 0
    while pending:
        value, depth = pending.pop()
        units += 1
        if units > MAX_PRIMITIVE_IDENTITY_UNITS:
            raise ValueError("primitive innovation identity exceeds its finite bound")
        if depth > MAX_PRIMITIVE_IDENTITY_DEPTH:
            raise ValueError("primitive innovation identity exceeds its depth bound")
        if value is None or type(value) is bool:
            continue
        if type(value) is int:
            if abs(value).bit_length() > 64:
                raise ValueError("primitive innovation identity embeds a wide integer")
            continue
        if isinstance(value, (str, bytes)):
            if len(value) > MAX_PRIMITIVE_IDENTITY_UNITS:
                raise ValueError("primitive innovation identity embeds a wide scalar")
            continue
        object_id = id(value)
        if object_id in seen:
            continue
        seen.add(object_id)
        if type(value) is tuple:
            pending.extend((child, depth + 1) for child in value)
        elif type(value) is SemanticIdentity:
            identities.append(value)
            pending.append((value.behavior, depth + 1))
        else:
            raise TypeError("primitive innovation identity has a nonsemantic payload")
    # Digest validation runs only after the complete reachable identity has
    # passed the finite structural bound above.
    for value in identities:
        value.validate()


@dataclass(frozen=True, slots=True)
class InnovationID(ArenaHandle):
    """Scoped arithmetic identity; source authority is deliberately absent."""

    seal: str = ""


@dataclass(frozen=True, slots=True)
class RadialMultiplier:
    """The unexpanded multiplier ``2**no_growth * (1+z)**growth``."""

    no_growth: int = 0
    growth: int = 0

    def __post_init__(self) -> None:
        if type(self.no_growth) is not int or type(self.growth) is not int:
            raise TypeError("radial exponents must be exact integers")
        if self.no_growth < 0 or self.growth < 0:
            raise ValueError("radial exponents must be nonnegative")

    @property
    def is_identity(self) -> bool:
        return self.no_growth == self.growth == 0

    def then(self, after: RadialMultiplier) -> RadialMultiplier:
        if type(after) is not RadialMultiplier:
            raise TypeError("radial composition requires a radial multiplier")
        self.__post_init__()
        after.__post_init__()
        return RadialMultiplier(
            self.no_growth + after.no_growth,
            self.growth + after.growth,
        )


@dataclass(frozen=True, slots=True)
class _Zero:
    pass


@dataclass(frozen=True, slots=True)
class _Atom:
    semantic: SemanticIdentity


@dataclass(frozen=True, slots=True)
class _Interval:
    """The exact window ``E_m = 1 + z + ... + z**(m-1)``."""

    length: int


@dataclass(frozen=True, slots=True)
class _Radial:
    multiplier: RadialMultiplier
    child: InnovationID


@dataclass(frozen=True, slots=True)
class _Charted:
    chart: CylinderChart
    child: InnovationID


@dataclass(frozen=True, slots=True)
class _Scale:
    coefficient: int
    child: InnovationID


@dataclass(frozen=True, slots=True)
class _Add:
    left: InnovationID
    right: InnovationID


_Node: TypeAlias = _Zero | _Atom | _Interval | _Radial | _Charted | _Scale | _Add


def _integer_limb_units(*values: int) -> int:
    """Return 64-bit ledger units for retained exact-integer metadata."""
    retained_bits = sum(max(1, abs(value).bit_length()) for value in values)
    return max(1, (retained_bits + 63) // 64)


def _node_units(node: _Node) -> int:
    """Ledger units retained by one node, including wide integer metadata."""
    if isinstance(node, _Interval):
        return _integer_limb_units(node.length)
    if isinstance(node, _Radial):
        return _integer_limb_units(node.multiplier.no_growth, node.multiplier.growth)
    if isinstance(node, _Charted):
        return _integer_limb_units(
            node.chart.slope,
            node.chart.offset,
            node.chart.extent_scale,
            node.chart.growth_scale,
        )
    if isinstance(node, _Scale):
        return _integer_limb_units(node.coefficient)
    return 1


@dataclass(frozen=True, slots=True)
class SymbolicRadialInnovation:
    """One source-free affine arithmetic component ``(M, B)``."""

    multiplier: RadialMultiplier
    innovation: InnovationID


class SymbolicInnovationArena:
    """Ledger-owned shared DAG for the exact formal innovation algebra.

    Signed-sum normalization visits only the direct operands supplied to one
    operation, combines equal DAG references, and removes zero coefficients.
    Existing addition nodes remain shared rather than being copied/flattened.
    The work is charged by ``symbolic_innovation_normalization_visits``.  This
    gives exact cancellation but is not a claimed bound for a full cylinder
    grammar or arbitrary sequential temporal construction.

    Equal formal polynomials can have different DAG identities. These local
    rewrites do not supply the canonical clause equality needed for pumping.
    """

    _KIND = "symbolic-innovation"

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("symbolic innovations require an index resource ledger")
        self.ledger = ledger
        self.ledger.register_execution_root(self)
        self.owner = ArenaToken("symbolic-innovation")
        self._closed = False
        prefix = f"symbolic-innovation-{len(ledger.inventory())}"
        self._node_owner = ledger.register(prefix + "-nodes", "innovation_action")
        self._key_owner = ledger.register(prefix + "-keys", "reverse_action_interner")
        self._projection = OwnedMemo[InnovationID, tuple[int, ...]](
            ledger,
            ledger.register(prefix + "-projection", "query_memo"),
        )
        self._f5_compositions: (
            OwnedMemo[tuple[InnovationID, InnovationID, int, int], InnovationID] | None
        ) = None
        self._nodes: LedgerList[_Node] = ledger.make_list(self._node_owner)
        self._keys: LedgerDict[_Node, InnovationID] = ledger.make_dict(self._key_owner)
        ledger.register_container(
            self._node_owner,
            self._nodes,
            node_count=lambda: sum(_node_units(node) for node in self._nodes),
            payloads=lambda: self._nodes,
        )
        ledger.register_container(
            self._key_owner,
            self._keys,
            node_count=lambda: 0,
            payloads=lambda: self._keys.items(),
        )
        self.zero = self._handle(0)
        try:
            self.zero = self._intern(_Zero())
        except BaseException:
            self.close()
            raise

    def _check_open(self) -> None:
        if self._closed:
            raise ValueError("disposed symbolic innovation arena")

    def _f5_composition_cache(
        self,
        minimum_nodes: int = 1,
    ) -> OwnedMemo[tuple[InnovationID, InnovationID, int, int], InnovationID]:
        """Lazy arithmetic-demand memo; it carries no source-image authority."""
        from number_compiler.arithmetic.fields.f5_innovation import composition_cache

        return composition_cache(self, minimum_nodes)

    @staticmethod
    def bind_chart(chart: CylinderChart, *, extent: int, growth: int) -> CylinderChart:
        """Bind an M/G-relative chart before it enters arithmetic identity."""
        if type(chart) is not CylinderChart:
            raise TypeError("innovation charts require a cylinder chart")
        shift = chart.shift(extent, growth)
        return CylinderChart(chart.slope, shift)

    @staticmethod
    def _closed_chart(chart: CylinderChart) -> CylinderChart:
        if type(chart) is not CylinderChart:
            raise TypeError("innovation charts require a cylinder chart")
        chart.__post_init__()
        if chart.extent_scale or chart.growth_scale:
            raise ValueError(
                "bind the chart extent/growth environment before interning"
            )
        return CylinderChart(chart.slope, chart.offset)

    def _intern(self, node: _Node) -> InnovationID:
        self._check_open()
        found = self._keys.get(node)
        if found is not None:
            return self._copy_ref(found)
        result = self._handle(len(self._nodes))
        units = _node_units(node)
        self.ledger.reserve_many(
            ((self._node_owner, 1, units), (self._key_owner, 1, 0))
        )
        self._nodes.append(node)
        self._keys[node] = self._copy_ref(result)
        if isinstance(node, _Interval):
            self.ledger.bump(
                "symbolic_innovation_interval_retained_bits",
                max(1, node.length.bit_length()),
            )
        return self._copy_ref(result)

    def _handle(self, local_id: int) -> InnovationID:
        return InnovationID(
            self.owner,
            self._KIND,
            local_id,
            f"{id(self.owner):x}:{local_id}",
        )

    @staticmethod
    def _copy_ref(reference: InnovationID) -> InnovationID:
        return InnovationID(
            reference.owner, reference.kind, reference.local_id, reference.seal
        )

    def resolve(self, reference: InnovationID) -> _Node:
        self._check_open()
        if type(reference) is not InnovationID:
            raise TypeError("expected a symbolic innovation ID")
        reference.validate(self.owner, self._KIND, size=len(self._nodes))
        if reference.seal != f"{id(self.owner):x}:{reference.local_id}":
            raise ValueError("symbolic innovation handle seal does not match its node")
        node = self._nodes[reference.local_id]
        interned = self._keys.get(node)
        if interned is None or interned != reference:
            raise ValueError("symbolic innovation node no longer matches its interner")
        if isinstance(node, _Atom):
            node.semantic.validate()
        return node

    def atom(self, semantic: SemanticIdentity) -> InnovationID:
        """Intern one finite primitive law, without source-occurrence authority."""
        if type(semantic) is not SemanticIdentity:
            raise TypeError("primitive innovations require a semantic identity")
        _validate_bounded_primitive_identity(semantic)
        retained = deepcopy(semantic)
        _validate_bounded_primitive_identity(retained)
        return self._intern(_Atom(retained))

    def interval(self, length: int) -> InnovationID:
        """Intern ``E_length = sum(z**i for i in range(length))`` unexpanded.

        ``E_0`` is the existing zero node.  Every positive length, including
        ``E_1``, has one canonical interval node; it is not a source atom or a
        source-admission certificate.
        """
        self._check_open()
        if type(length) is not int:
            raise TypeError("innovation interval length must be an exact integer")
        if length < 0:
            raise ValueError("innovation interval length must be nonnegative")
        if length == 0:
            return self._copy_ref(self.zero)
        return self._intern(_Interval(length))

    def close(self) -> None:
        """Release retained DAG stores and invalidate every issued handle."""
        if self._closed:
            return
        keys = len(self._keys)
        entries = len(self._nodes)
        nodes = sum(_node_units(node) for node in self._nodes)
        self._projection.dispose()
        if self._f5_compositions is not None:
            self._f5_compositions.dispose()
            self._f5_compositions = None
        self._keys.clear()
        self._nodes._rollback_unpublished(0)
        self.ledger.release(self._key_owner, entries=keys)
        self.ledger.release(self._node_owner, entries=entries, nodes=nodes)
        self.ledger.mark_disposed(self._key_owner)
        self.ledger.mark_disposed(self._node_owner)
        self.owner = ArenaToken("disposed-symbolic-innovation")
        self._closed = True

    def linear_combination(
        self, terms: Sequence[tuple[int, InnovationID]]
    ) -> InnovationID:
        """Normalize direct signed operands without flattening prior DAG sums."""
        coefficients: dict[InnovationID, int] = {}
        for coefficient, reference in terms:
            if type(coefficient) is not int:
                raise TypeError("innovation coefficients must be exact integers")
            node = self.resolve(reference)
            self.ledger.bump("symbolic_innovation_normalization_visits")
            if coefficient == 0 or isinstance(node, _Zero):
                continue
            if isinstance(node, _Scale):
                coefficient *= node.coefficient
                reference = node.child
            coefficients[reference] = coefficients.get(reference, 0) + coefficient
        normalized = tuple(
            self._scale(reference, coefficient)
            for reference, coefficient in sorted(
                coefficients.items(), key=lambda item: item[0].local_id
            )
            if coefficient
        )
        if not normalized:
            return self.zero
        current = list(normalized)
        while len(current) > 1:
            next_level: list[InnovationID] = []
            index = 0
            while index + 1 < len(current):
                next_level.append(self._add_node(current[index], current[index + 1]))
                index += 2
            if index < len(current):
                next_level.append(current[index])
            current = next_level
        return current[0]

    def _scale(self, reference: InnovationID, coefficient: int) -> InnovationID:
        node = self.resolve(reference)
        if coefficient == 0 or isinstance(node, _Zero):
            return self.zero
        while isinstance(node, _Scale):
            coefficient *= node.coefficient
            reference = node.child
            node = self.resolve(reference)
        if coefficient == 1:
            return reference
        return self._intern(_Scale(coefficient, self._copy_ref(reference)))

    def _add_node(self, first: InnovationID, second: InnovationID) -> InnovationID:
        first_node, second_node = self.resolve(first), self.resolve(second)
        if isinstance(first_node, _Zero):
            return second
        if isinstance(second_node, _Zero):
            return first
        if second.local_id < first.local_id:
            first, second = second, first
        return self._intern(_Add(self._copy_ref(first), self._copy_ref(second)))

    def add(self, first: InnovationID, second: InnovationID) -> InnovationID:
        return self.linear_combination(((1, first), (1, second)))

    def subtract(self, first: InnovationID, second: InnovationID) -> InnovationID:
        return self.linear_combination(((1, first), (-1, second)))

    def radial(
        self, reference: InnovationID, multiplier: RadialMultiplier
    ) -> InnovationID:
        """Apply an unexpanded radial multiplier as one shared DAG node."""
        if type(multiplier) is not RadialMultiplier:
            raise TypeError("innovation scaling requires a radial multiplier")
        multiplier = RadialMultiplier(multiplier.no_growth, multiplier.growth)
        node = self.resolve(reference)
        if isinstance(node, _Zero) or multiplier.is_identity:
            return reference
        if isinstance(node, _Radial):
            return self._intern(
                _Radial(node.multiplier.then(multiplier), self._copy_ref(node.child))
            )
        return self._intern(_Radial(multiplier, self._copy_ref(reference)))

    def chart(self, reference: InnovationID, chart: CylinderChart) -> InnovationID:
        """Apply a closed translation/reflection and its radial transport law."""
        chart = self._closed_chart(chart)
        if isinstance(self.resolve(reference), _Zero) or chart == CylinderChart():
            return reference
        radial = RadialMultiplier()
        while True:
            node = self.resolve(reference)
            if isinstance(node, _Charted):
                # chart(P, A), then chart(_, B), is P(A(B(i))).
                chart = chart.then(node.chart)
                reference = node.child
                continue
            if isinstance(node, _Radial):
                # R_d H^r = H^r R_(d-r); positive translations commute.
                if chart.slope == -1 and node.multiplier.growth:
                    chart = CylinderChart(-1, chart.offset - node.multiplier.growth)
                radial = node.multiplier.then(radial)
                reference = node.child
                continue
            break
        result = (
            reference
            if chart == CylinderChart()
            else self._intern(_Charted(chart, self._copy_ref(reference)))
        )
        return self.radial(result, radial)

    def identity(self) -> SymbolicRadialInnovation:
        return SymbolicRadialInnovation(RadialMultiplier(), self._copy_ref(self.zero))

    def substitute_many(
        self,
        roots: Sequence[InnovationID],
        replacements: Mapping[InnovationID, InnovationID],
    ) -> tuple[InnovationID, ...]:
        """Simultaneously substitute primitive atoms through shared expressions.

        Replacement expressions belong to the original environment: they are
        not recursively substituted. All roots share one iterative postorder
        traversal and memo. Rebuilding uses the existing chart, radial and
        signed-sum normalizers, without projection or coefficient evaluation.

        This arithmetic operation supplies no source admission, carry discovery
        or complete temporal return. Workspace is released on failure; any
        already interned arithmetic nodes remain valid and charged, but no
        result tuple is published. Work visits distinct reachable input nodes
        plus their edges; it does not bound temporal grammar growth.
        """
        from number_compiler.arithmetic.fields.innovation_substitution import (
            substitute_innovations,
        )

        return substitute_innovations(self, roots, replacements)

    def substitute_parity_many(
        self,
        roots: Sequence[InnovationID],
        replacements: Mapping[InnovationID, InnovationID],
    ) -> tuple[InnovationID, ...]:
        """Pull back coefficient parity, pruning even factors before descent.

        Returned expressions are equivalent only modulo 2. They must not
        replace exact output/carry expressions or grant source admission.
        Replacement expressions retain their original environment, as in
        substitute_many. This is not a canonical whole-cylinder quotient.
        """
        from number_compiler.arithmetic.fields.innovation_substitution import (
            substitute_innovations,
        )

        return substitute_innovations(self, roots, replacements, parity=True)

    def action(
        self, multiplier: RadialMultiplier, innovation: InnovationID
    ) -> SymbolicRadialInnovation:
        if type(multiplier) is not RadialMultiplier:
            raise TypeError("symbolic action requires a radial multiplier")
        multiplier = RadialMultiplier(multiplier.no_growth, multiplier.growth)
        self.resolve(innovation)
        return SymbolicRadialInnovation(multiplier, self._copy_ref(innovation))

    def then(
        self,
        before: SymbolicRadialInnovation,
        after: SymbolicRadialInnovation,
    ) -> SymbolicRadialInnovation:
        """Compose ``before`` then ``after`` by exact affine substitution."""
        if (
            type(before) is not SymbolicRadialInnovation
            or type(after) is not SymbolicRadialInnovation
        ):
            raise TypeError("symbolic substitution requires two affine actions")
        self.resolve(before.innovation)
        self.resolve(after.innovation)
        self.ledger.bump("symbolic_innovation_substitutions")
        return SymbolicRadialInnovation(
            before.multiplier.then(after.multiplier),
            self.add(
                self.radial(before.innovation, after.multiplier),
                after.innovation,
            ),
        )

    def power(
        self, action: SymbolicRadialInnovation, exponent: int
    ) -> SymbolicRadialInnovation:
        """Power one supplied formal action with the shared binary monoid law.

        This proves no source admission or pump invariant.  It only powers an
        already-supplied arithmetic expression DAG.
        """
        if type(action) is not SymbolicRadialInnovation:
            raise TypeError("symbolic power requires an affine action")
        self.resolve(action.innovation)
        return binary_power(
            action,
            exponent,
            identity=self.identity(),
            compose=self.then,
        ).value

    @property
    def node_count(self) -> int:
        self._check_open()
        return len(self._nodes)

    def project_cyclotomic(
        self,
        action: SymbolicRadialInnovation,
        *,
        order: int,
        bits: int,
        atoms: Mapping[SemanticIdentity, Sequence[int]],
    ) -> ReverseAddCyclotomicInnovationBlock:
        """Project a fully resolved formal action into the existing quotient owner.

        A radial multiplier intrinsic to the innovation DAG may be proved zero
        before its child is visited.  Unary scale/chart/radial chains are
        inspected together because scales and signed monomial substitutions
        preserve the cyclotomic radial factor's 2-adic content.  Consequently
        metadata wider than the ordinary live-observer limit is harmless when
        this exact proof already annihilates the whole occurrence.  The affine
        action multiplier is deliberately excluded: it acts on the incoming
        state, not on this innovation.
        """
        from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
            power_two_cyclotomic_transport,
        )

        if type(action) is not SymbolicRadialInnovation:
            raise TypeError("cyclotomic projection requires a symbolic action")
        self.resolve(action.innovation)
        if (
            type(order) is not int
            or not 2 <= order <= MAX_CYCLOTOMIC_PROJECTION_ORDER
            or order & (order - 1)
            or type(bits) is not int
            or not 1 <= bits <= MAX_CYCLOTOMIC_PROJECTION_BITS
        ):
            raise ValueError("cyclotomic projection exceeds its bounded observer")
        if (
            action.multiplier.no_growth.bit_length() > 64
            or action.multiplier.growth.bit_length() > 64
        ):
            raise ValueError("cyclotomic projection radial exponent is too wide")
        ring = CyclotomicRing(int(order), 1 << int(bits))
        memo = self._projection
        if len(memo):
            raise RuntimeError("symbolic innovation projection workspace is in use")

        # Temporary suffix facts share the already registered projection owner.
        # Each entry is explicitly reserved and released; the dictionary is not
        # published as retained arena state.
        summaries: dict[
            InnovationID, tuple[bool, int, int, bool, bool, bool, _Node]
        ] = {}
        summary_nodes = 0

        def retain_summary(
            reference: InnovationID,
            summary: tuple[bool, int, int, bool, bool, bool, _Node],
        ) -> tuple[bool, int, int, bool, bool, bool, _Node]:
            nonlocal summary_nodes
            existing = summaries.get(reference)
            if existing is not None:
                return existing
            units = 1 + _integer_limb_units(summary[1], summary[2])
            self.ledger.reserve(memo.owner, entries=1, nodes=units)
            try:
                summaries[reference] = summary
            except BaseException:
                self.ledger.release(memo.owner, entries=1, nodes=units)
                raise
            summary_nodes += units
            return summary

        def add_metadata(
            left_no_growth: int,
            left_growth: int,
            right_no_growth: int,
            right_growth: int,
        ) -> tuple[int, int]:
            units = _integer_limb_units(
                left_no_growth,
                left_growth,
                right_no_growth,
                right_growth,
            )
            # Reserve before constructing either potentially wider sum.
            self.ledger.reserve(memo.owner, nodes=units)
            try:
                result = (
                    left_no_growth + right_no_growth,
                    left_growth + right_growth,
                )
            finally:
                self.ledger.release(memo.owner, nodes=units)
            self.ledger.bump(
                "symbolic_innovation_projection_metadata_addition_bits",
                max(result[0].bit_length(), result[1].bit_length(), 1),
            )
            return result

        def suffix_summary(
            reference: InnovationID,
        ) -> tuple[bool, int, int, bool, bool, bool, _Node]:
            """Compute each unary suffix once, stopping immediately on zero."""
            found = summaries.get(reference)
            if found is not None:
                return found
            chain: list[tuple[InnovationID, _Node]] = []
            chain_nodes = 0
            current = reference
            prefix_no_growth = 0
            prefix_growth = 0
            try:
                while summaries.get(current) is None:
                    # Charge before validation so foreign, stale, and otherwise
                    # failed requests remain visible as completed work.
                    self.ledger.bump("symbolic_innovation_projection_dependency_visits")
                    node = self.resolve(current)
                    self.ledger.reserve(memo.owner, entries=1, nodes=1)
                    try:
                        chain.append((current, node))
                    except BaseException:
                        self.ledger.release(memo.owner, entries=1, nodes=1)
                        raise
                    chain_nodes += 1
                    if isinstance(node, _Radial):
                        prefix_no_growth, prefix_growth = add_metadata(
                            prefix_no_growth,
                            prefix_growth,
                            node.multiplier.no_growth,
                            node.multiplier.growth,
                        )
                        self.ledger.bump(
                            "symbolic_innovation_projection_radial_zero_checks"
                        )
                        if power_two_cyclotomic_transport(
                            order // 2, prefix_no_growth, prefix_growth
                        ).annihilated(bits):
                            self.ledger.bump(
                                "symbolic_innovation_projection_pruned_occurrences"
                            )
                            root_node = chain[0][1]
                            self.ledger.release(
                                memo.owner, entries=chain_nodes, nodes=chain_nodes
                            )
                            chain.clear()
                            chain_nodes = 0
                            return retain_summary(
                                reference,
                                (
                                    True,
                                    prefix_no_growth,
                                    prefix_growth,
                                    False,
                                    False,
                                    False,
                                    root_node,
                                ),
                            )
                        current = node.child
                        continue
                    if isinstance(node, (_Charted, _Scale)):
                        current = node.child
                        continue
                    retain_summary(current, (False, 0, 0, False, False, False, node))
                    break

                for item_reference, node in reversed(chain):
                    if summaries.get(item_reference) is not None:
                        continue
                    if not isinstance(node, (_Radial, _Charted, _Scale)):
                        continue
                    child = summaries[node.child]
                    dead, no_growth, growth, wide_radial, wide_chart, wide_scale, _ = (
                        child
                    )
                    if isinstance(node, _Radial):
                        no_growth, growth = add_metadata(
                            node.multiplier.no_growth,
                            node.multiplier.growth,
                            no_growth,
                            growth,
                        )
                        self.ledger.bump(
                            "symbolic_innovation_projection_radial_zero_checks"
                        )
                        dead = dead or power_two_cyclotomic_transport(
                            order // 2, no_growth, growth
                        ).annihilated(bits)
                        wide_radial = wide_radial or (
                            node.multiplier.no_growth.bit_length() > 64
                            or node.multiplier.growth.bit_length() > 64
                        )
                    elif isinstance(node, _Charted):
                        wide_chart = wide_chart or node.chart.offset.bit_length() > 64
                    else:
                        wide_scale = (
                            wide_scale or abs(node.coefficient).bit_length() > 64
                        )
                    retain_summary(
                        item_reference,
                        (
                            dead,
                            no_growth,
                            growth,
                            wide_radial,
                            wide_chart,
                            wide_scale,
                            node,
                        ),
                    )
                return summaries[reference]
            finally:
                if chain_nodes:
                    self.ledger.release(
                        memo.owner, entries=chain_nodes, nodes=chain_nodes
                    )

        try:
            pending: list[tuple[InnovationID, bool, _Node | None]] = []

            def push_frame(
                reference: InnovationID, expanded: bool, node: _Node | None
            ) -> None:
                self.ledger.reserve(memo.owner, entries=1, nodes=1)
                try:
                    pending.append((reference, expanded, node))
                except BaseException:
                    self.ledger.release(memo.owner, entries=1, nodes=1)
                    raise
                self.ledger.bump("symbolic_innovation_projection_workspace_frames")

            active_frames = 0
            push_frame(action.innovation, False, None)
            while pending:
                reference, expanded, retained_node = pending.pop()
                active_frames = 1
                if memo.get(reference) is not None:
                    self.ledger.release(memo.owner, entries=1, nodes=1)
                    active_frames = 0
                    continue
                if expanded:
                    if retained_node is None:
                        raise AssertionError("expanded projection frame lost its node")
                    node = retained_node
                else:
                    (
                        dead,
                        _,
                        _,
                        wide_radial,
                        wide_chart,
                        wide_scale,
                        node,
                    ) = suffix_summary(reference)
                    if dead:
                        self.ledger.bump("symbolic_innovation_projection_visits")
                        memo[reference] = tuple(ring.zero)
                        self.ledger.release(memo.owner, entries=1, nodes=1)
                        active_frames = 0
                        continue
                    if wide_radial:
                        raise ValueError(
                            "cyclotomic projection radial exponent is too wide"
                        )
                    if wide_chart:
                        raise ValueError("cyclotomic projection chart is too wide")
                    if wide_scale:
                        raise ValueError("cyclotomic projection scale is too wide")
                if isinstance(node, _Radial) and (
                    node.multiplier.no_growth.bit_length() > 64
                    or node.multiplier.growth.bit_length() > 64
                ):
                    raise ValueError(
                        "cyclotomic projection radial exponent is too wide"
                    )
                if isinstance(node, _Charted) and node.chart.offset.bit_length() > 64:
                    raise ValueError("cyclotomic projection chart is too wide")
                if isinstance(node, _Scale) and abs(node.coefficient).bit_length() > 64:
                    raise ValueError("cyclotomic projection scale is too wide")
                children: tuple[InnovationID, ...]
                if isinstance(node, (_Radial, _Charted, _Scale)):
                    children = (node.child,)
                elif isinstance(node, _Add):
                    children = (node.left, node.right)
                else:
                    children = ()
                if not expanded and any(memo.get(child) is None for child in children):
                    push_frame(reference, True, node)
                    for child_reference in reversed(children):
                        if memo.get(child_reference) is None:
                            push_frame(child_reference, False, None)
                    self.ledger.release(memo.owner, entries=1, nodes=1)
                    active_frames = 0
                    continue
                self.ledger.bump("symbolic_innovation_projection_visits")
                if isinstance(node, _Zero):
                    result = ring.zero
                elif isinstance(node, _Atom):
                    try:
                        supplied = atoms[node.semantic]
                    except KeyError as error:
                        raise ValueError(
                            "cyclotomic projection has an unresolved atom"
                        ) from error
                    if len(supplied) != ring.degree:
                        raise ValueError(
                            "primitive residue has the wrong cyclotomic degree"
                        )
                    if any(
                        type(value) is not int or abs(value).bit_length() > 64
                        for value in supplied
                    ):
                        raise ValueError(
                            "primitive residue exceeds its local word bound"
                        )
                    result = tuple(int(value) % ring.modulus for value in supplied)
                elif isinstance(node, _Interval):
                    # In the whole 2-power quotient, z**degree = -1, so
                    # z**order = 1 and every complete order-sized window
                    # cancels.  Only one bounded remainder contributes.
                    remainder = node.length % order
                    degree = ring.degree
                    self.ledger.bump(
                        "symbolic_innovation_interval_projection_operand_bits",
                        max(1, node.length.bit_length()),
                    )
                    self.ledger.bump(
                        "symbolic_innovation_interval_projection_coefficients",
                        degree,
                    )
                    result = tuple(
                        (int(index < remainder) - int(index + degree < remainder))
                        % ring.modulus
                        for index in range(degree)
                    )
                elif isinstance(node, _Radial):
                    radial = power_two_cyclotomic_radial_quotient(
                        order // 2,
                        node.multiplier.no_growth,
                        node.multiplier.growth,
                        bits=bits,
                    )
                    child = memo[node.child]
                    result = ring.multiply(child, radial.multiplier_residue())
                elif isinstance(node, _Charted):
                    source = memo[node.child]
                    result = ring.zero
                    for index, coefficient in enumerate(source):
                        exponent = (
                            node.chart.slope * index
                            - node.chart.slope * node.chart.offset
                        )
                        z_power = (
                            ring.power_residue(ring.reduce((0, 1)), exponent).value
                            if exponent >= 0
                            else _negative_z_power(ring, exponent)
                        )
                        result = ring.add(result, ring.scale(z_power, coefficient))
                elif isinstance(node, _Scale):
                    result = ring.scale(memo[node.child], node.coefficient)
                else:
                    result = ring.add(memo[node.left], memo[node.right])
                memo[reference] = tuple(result)
                self.ledger.release(memo.owner, entries=1, nodes=1)
                active_frames = 0

            innovation = memo[action.innovation]
            return ReverseAddCyclotomicInnovationBlock(
                order,
                bits,
                action.multiplier.no_growth + action.multiplier.growth,
                action.multiplier.growth,
                innovation,
            )
        finally:
            frames = len(pending) + active_frames
            if frames:
                self.ledger.release(memo.owner, entries=frames, nodes=frames)
                pending.clear()
            memo.clear()
            if summaries:
                self.ledger.release(
                    memo.owner, entries=len(summaries), nodes=summary_nodes
                )
                summaries.clear()


def _negative_z_power(ring: CyclotomicRing, exponent: int) -> tuple[int, ...]:
    """Return z**exponent in a whole power-of-two cyclotomic quotient."""
    if exponent >= 0:
        raise ValueError("negative-power helper requires a negative exponent")
    # Phi_(2^k)(z) = z^d + 1, so z^-1 = -z^(d-1).  The symbolic
    # innovation owner currently projects only to the whole power-1 quotient.
    if ring.factor is not None or ring.power != 1 or ring.order & (ring.order - 1):
        raise ValueError("negative chart projection requires a whole 2-power quotient")
    inverse = ring.reduce((0,) * (ring.degree - 1) + (-1,))
    return tuple(ring.power_residue(inverse, -exponent).value)


__all__ = [
    "MAX_CYCLOTOMIC_PROJECTION_BITS",
    "MAX_CYCLOTOMIC_PROJECTION_ORDER",
    "MAX_PRIMITIVE_IDENTITY_UNITS",
    "InnovationID",
    "RadialMultiplier",
    "SymbolicInnovationArena",
    "SymbolicRadialInnovation",
]
