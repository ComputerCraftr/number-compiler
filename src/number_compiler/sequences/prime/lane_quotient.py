"""Exact residual-divisor set morphism for finite prime blocks.

The packed congruence automaton is the right state for random access to one
candidate, but compiling a whole prime/composite block by descending that full
state still performs one residue transition per group per candidate-tree edge.
This module quotients earlier.

For candidates ``n_j = start + 2*j`` every irreducible divisor witness is one
progression ``j = phase (mod q)`` with a certified first hit.  Under a radix
partition of the index interval, a progression maps to either another local
progression, one local point, or the empty set.  Singleton witnesses discard
factor identity immediately because Boolean compositeness only needs their
union.  The resulting residual-set interface is hash-consed *before* its child
subtrees are constructed, and the final decision nodes are hash-consed by their
complete child tuple.

No prime bitmap and no per-candidate packed residue vector are materialized on
this path.  The initial factor basis is still discovered by the exact natural-
factor scan, and all containment/interface work is explicitly metered.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from math import prod

from number_compiler.arithmetic.fields.projection_field import BinomialMomentBlock
from number_compiler.arithmetic.fields.radix import bit_width, periodic_position_bases
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock
from number_compiler.arithmetic.polynomials.primary_jet import PrimaryJetBlock
from number_compiler.sequences.prime.set import (
    MultiplicativeLane,
    PrimeBlockSummary,
    canonical_multiplicative_lane_basis,
)
from number_compiler.sequences.prime.wheel_cyclotomic import (
    PrimeWheelCyclotomicAutomaton,
    build_prime_wheel_cyclotomic_automaton,
)


@dataclass(frozen=True, slots=True)
class ResidualDivisorInterface:
    """Canonical transformed source-lane interface for one local interval.

    ``periodic`` entries are ``(period, first_local_hit)`` and each has at
    least two hits in the represented interval.  ``points`` are singleton
    witness positions with factor identity quotiented away.
    """

    periodic: tuple[tuple[int, int], ...] = ()
    points: tuple[int, ...] = ()

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("residual-divisor-interface", self.periodic, self.points)

    def description_bits(self, size: int) -> int:
        size = int(size)
        pos_bits = bit_width(max(0, size - 1))
        return (
            bit_width(len(self.periodic))
            + bit_width(len(self.points))
            + sum(bit_width(q) + pos_bits for q, _first in self.periodic)
            + len(self.points) * pos_bits
        )


@dataclass(frozen=True, slots=True)
class PrimeLaneQuotientCompilation:
    start: int
    length: int
    base_period: tuple[int, ...]
    position_bases: tuple[int, ...]
    domain_size: int
    factor_candidates: int
    natural_lanes: int
    canonical_lanes: int
    factor_generator_gcd_calls: int
    factor_generator_groups: int
    factor_basis_description_bits: int
    semantic_interfaces: int
    max_interface_description_bits: int
    interface_cache_description_bits: int
    decision_nodes: int
    decision_references: int
    decision_description_bits: int
    lane_transform_checks: int
    lane_transform_cache_hits: int
    lane_transform_cache_misses: int
    point_transform_cache_hits: int
    point_transform_cache_misses: int
    summary: PrimeBlockSummary
    primary_jet: PrimaryJetBlock | None
    primary_jet_compositions: int
    terminal_prime_interfaces: int
    terminal_composite_interfaces: int
    terminal_outside_interfaces: int
    wheel_cyclotomic: PrimeWheelCyclotomicAutomaton | None = None
    binomial_moments: BinomialMomentBlock | None = None
    cyclotomic_projection: tuple[CyclotomicDigitBlock, ...] = ()
    projection_field_compositions: int = 0

    @property
    def summary_count(self) -> int:
        return self.summary.count

    @property
    def summary_first(self) -> int | None:
        return self.summary.first

    @property
    def transform_cache_hits(self) -> int:
        return self.lane_transform_cache_hits + self.point_transform_cache_hits

    @property
    def radix_projection_work(self) -> int:
        """Charged block-partition work after the factor basis is available."""
        return (
            self.lane_transform_checks
            + self.transform_cache_hits
            + self.primary_jet_compositions
            + self.projection_field_compositions
        )

    @property
    def projection_work(self) -> int:
        return (
            self.factor_candidates
            + self.factor_generator_gcd_calls
            + self.radix_projection_work
        )


def _initial_interface(
    lanes: Sequence[MultiplicativeLane], length: int
) -> tuple[ResidualDivisorInterface, int]:
    periodic: list[tuple[int, int]] = []
    points: set[int] = set()
    checks = 0
    for lane in lanes:
        checks += 1
        first = int(lane.first_index)
        if first >= length:
            continue
        hits = 1 + (length - 1 - first) // int(lane.factor)
        if hits == 1:
            points.add(first)
        else:
            periodic.append((int(lane.factor), first))
    return ResidualDivisorInterface(tuple(periodic), tuple(sorted(points))), checks


def canonical_prime_base_period(length: int) -> tuple[int, ...]:
    """Static work-oriented radix schedule for the residual-divisor projector.

    Small blocks keep the lower-overhead radix-4 partition.  Once the block has
    at least 1024 odd candidates, alternating radix 4/8 reduces charged lane
    transforms across the tested 10^6--10^8 ranges without compiling multiple
    candidate schedules at runtime.  This is a deterministic compiler policy,
    not an adaptive search whose rejected alternatives would hide work.
    """
    length = int(length)
    if length <= 0:
        raise ValueError(length)
    return (4, 8) if length >= 1024 else (4,)


def compile_prime_block_lane_quotient(
    start: int,
    length: int,
    *,
    base_period: Sequence[int] = (4,),
    jet_degree: int = 4,
    jet_modulus: int = 32,
    projection_algebra: bool = False,
    include_primary_jet: bool = True,
    include_wheel_cyclotomic: bool = False,
) -> PrimeLaneQuotientCompilation:
    """Compile a prime/composite decision DAG from residual divisor sets.

    Internal interfaces are exact transformed witness sets.  Internal decision
    nodes are a second, extensional quotient keyed only by their complete child
    behavior.  The prime-count/first-hole summary is always composed from the
    DAG traversal.  The ``(z+1)`` primary jet is an optional theorem channel so
    semantic callers that need only ``(count, first)`` do not pay its work.
    """
    start, length = int(start), int(length)
    period = tuple(map(int, base_period))
    if start < 3 or not (start & 1) or length <= 0:
        raise ValueError((start, length))
    bases = periodic_position_bases(length, period)
    domain = prod(bases)
    basis = canonical_multiplicative_lane_basis(start, length)
    wheel_cyclotomic = (
        build_prime_wheel_cyclotomic_automaton(basis.lanes)
        if include_wheel_cyclotomic
        else None
    )
    root_interface, initial_checks = _initial_interface(basis.lanes, length)

    # Terminals: 0 composite, 1 prime, 2 padded/outside.
    terminal_composite, terminal_prime, terminal_outside = 0, 1, 2
    next_node = 3
    structural_nodes: dict[tuple[int, ...], int] = {}
    node_children: dict[int, tuple[int, ...]] = {}
    interface_cache: dict[
        tuple[object, ...],
        tuple[
            int,
            PrimeBlockSummary,
            PrimaryJetBlock | None,
            BinomialMomentBlock | None,
            tuple[CyclotomicDigitBlock, ...],
        ],
    ] = {}
    # A single divisor lane has an exact radix-set morphism determined only by
    # its local period/phase and the current interval geometry.  Different
    # residual interfaces frequently contain the same lane action, so cache
    # that action *before* constructing child interfaces.  This is a genuine
    # quotient of projection work rather than a late decision-DAG cache hit.
    periodic_transform_cache: dict[
        tuple[int, int, int, int],
        tuple[tuple[str, int, int] | None, ...],
    ] = {}
    point_transform_cache: dict[tuple[int, int, int], tuple[int, int]] = {}

    lane_checks = initial_checks
    lane_transform_cache_hits = 0
    lane_transform_cache_misses = 0
    point_transform_cache_hits = 0
    point_transform_cache_misses = 0
    jet_calls = 0
    projection_field_calls = 0
    interface_bits_total = 0
    interface_bits_max = 0
    terminal_prime_interfaces = 0
    terminal_composite_interfaces = 0
    terminal_outside_interfaces = 0

    zero_digit: PrimaryJetBlock | None
    one_digit: PrimaryJetBlock | None
    empty_jet: PrimaryJetBlock | None
    empty_cyclotomic: tuple[CyclotomicDigitBlock, ...]
    zero_cyclotomic: tuple[CyclotomicDigitBlock, ...]
    one_cyclotomic: tuple[CyclotomicDigitBlock, ...]
    empty_binomial: BinomialMomentBlock | None
    zero_binomial: BinomialMomentBlock | None
    one_binomial: BinomialMomentBlock | None
    if include_primary_jet:
        zero_digit = PrimaryJetBlock.digit(0, degree=jet_degree, modulus=jet_modulus)
        one_digit = PrimaryJetBlock.digit(1, degree=jet_degree, modulus=jet_modulus)
        empty_jet = PrimaryJetBlock.identity(jet_degree, jet_modulus)
    else:
        zero_digit = one_digit = empty_jet = None
    if projection_algebra:
        empty_binomial = BinomialMomentBlock.identity(jet_degree, jet_modulus)
        zero_binomial = BinomialMomentBlock.digit(
            0, degree=jet_degree, modulus=jet_modulus
        )
        one_binomial = BinomialMomentBlock.digit(
            1, degree=jet_degree, modulus=jet_modulus
        )
        empty_cyclotomic = tuple(
            CyclotomicDigitBlock.identity(o, jet_modulus) for o in (2, 4, 8)
        )
        zero_cyclotomic = tuple(
            CyclotomicDigitBlock.digit(0, order=o, modulus=jet_modulus)
            for o in (2, 4, 8)
        )
        one_cyclotomic = tuple(
            CyclotomicDigitBlock.digit(1, order=o, modulus=jet_modulus)
            for o in (2, 4, 8)
        )
    else:
        empty_binomial = zero_binomial = one_binomial = None
        empty_cyclotomic = ()
        zero_cyclotomic = ()
        one_cyclotomic = ()

    def partition_interface(
        interface: ResidualDivisorInterface,
        *,
        size: int,
        base: int,
    ) -> tuple[ResidualDivisorInterface, ...]:
        """Apply the exact one-level radix set morphism to an interface.

        Periodic and singleton source lanes are transformed through their own
        canonical morphism caches.  Cache hits still count as one charged
        lookup in ``projection_work``; ``lane_transform_checks`` counts only
        the arithmetic child-membership work actually executed on cache
        misses (plus the root lane classification).
        """
        nonlocal lane_checks
        nonlocal lane_transform_cache_hits, lane_transform_cache_misses
        nonlocal point_transform_cache_hits, point_transform_cache_misses

        if size % base:
            raise AssertionError((size, base))
        child_size = size // base
        periodic_children: list[list[tuple[int, int]]] = [[] for _ in range(base)]
        point_children: list[set[int]] = [set() for _ in range(base)]

        for lane_period, first in interface.periodic:
            key = (lane_period, first, size, base)
            transformed = periodic_transform_cache.get(key)
            if transformed is None:
                lane_transform_cache_misses += 1
                # One arithmetic membership/first-hit calculation per radix
                # child.  This is exactly the work the old implementation
                # repeated independently in every parent interface.
                lane_checks += base
                entries: list[tuple[str, int, int] | None] = []
                for digit in range(base):
                    offset = digit * child_size
                    stop = offset + child_size
                    if first >= offset:
                        hit = first
                    else:
                        hit = (
                            first
                            + ((offset - first + lane_period - 1) // lane_period)
                            * lane_period
                        )
                    if hit >= stop:
                        entries.append(None)
                        continue
                    local = hit - offset
                    hits = 1 + (stop - 1 - hit) // lane_period
                    if hits == 1:
                        entries.append(("point", local, 0))
                    else:
                        entries.append(("periodic", lane_period, local))
                transformed = tuple(entries)
                periodic_transform_cache[key] = transformed
            else:
                lane_transform_cache_hits += 1

            for digit, entry in enumerate(transformed):
                if entry is None:
                    continue
                kind, a, b = entry
                if kind == "point":
                    point_children[digit].add(a)
                else:
                    periodic_children[digit].append((a, b))

        for point in interface.points:
            point_key = (point, size, base)
            transformed_point = point_transform_cache.get(point_key)
            if transformed_point is None:
                point_transform_cache_misses += 1
                lane_checks += 1
                digit, local = divmod(point, child_size)
                if not 0 <= digit < base:
                    raise AssertionError((point, size, base, digit))
                transformed_point = (digit, local)
                point_transform_cache[point_key] = transformed_point
            else:
                point_transform_cache_hits += 1
            digit, local = transformed_point
            point_children[digit].add(local)

        return tuple(
            ResidualDivisorInterface(
                tuple(periodic_children[digit]),
                tuple(sorted(point_children[digit])),
            )
            for digit in range(base)
        )

    root_args = (len(bases) - 1, domain, length, root_interface)
    # Explicit postorder frames replace recursive radix descent.  The cache key
    # remains the exact residual divisor interface, so no semantic state changes.
    stack: list[tuple[int, int, int, ResidualDivisorInterface, bool]] = [
        (*root_args, False)
    ]
    pending_children: dict[
        tuple[object, ...], tuple[tuple[int, int, int, ResidualDivisorInterface], ...]
    ] = {}
    while stack:
        pos, size, valid, interface, expanded = stack.pop()
        key = (pos, size, valid, interface.canonical_key)
        if key in interface_cache:
            continue

        if not expanded:
            ibits = interface.description_bits(size)
            interface_bits_total += ibits
            interface_bits_max = max(interface_bits_max, ibits)

        if valid <= 0:
            terminal_outside_interfaces += 1
            interface_cache[key] = (
                terminal_outside,
                PrimeBlockSummary.empty(),
                empty_jet,
                empty_binomial,
                empty_cyclotomic,
            )
            continue

        if pos < 0:
            if size != 1 or valid != 1:
                raise AssertionError((pos, size, valid))
            composite = bool(interface.periodic or interface.points)
            if composite:
                terminal_composite_interfaces += 1
                out: tuple[
                    int,
                    PrimeBlockSummary,
                    PrimaryJetBlock | None,
                    BinomialMomentBlock | None,
                    tuple[CyclotomicDigitBlock, ...],
                ] = (
                    terminal_composite,
                    PrimeBlockSummary.bit(False),
                    zero_digit,
                    zero_binomial,
                    zero_cyclotomic,
                )
            else:
                terminal_prime_interfaces += 1
                out = (
                    terminal_prime,
                    PrimeBlockSummary.bit(True),
                    one_digit,
                    one_binomial,
                    one_cyclotomic,
                )
            interface_cache[key] = out
            continue

        base = bases[pos]
        if size % base:
            raise AssertionError((size, base, bases))
        child_size = size // base
        child_specs = pending_children.get(key)
        if child_specs is None:
            child_interfaces = partition_interface(interface, size=size, base=base)
            built: list[tuple[int, int, int, ResidualDivisorInterface]] = []
            for digit, child_interface in enumerate(child_interfaces):
                child_offset = digit * child_size
                child_valid = max(0, min(child_size, valid - child_offset))
                built.append((pos - 1, child_size, child_valid, child_interface))
            child_specs = tuple(built)
            pending_children[key] = child_specs

        child_keys = tuple(
            (cp, cs, cv, ci.canonical_key) for cp, cs, cv, ci in child_specs
        )
        if not expanded and any(
            child_key not in interface_cache for child_key in child_keys
        ):
            stack.append((pos, size, valid, interface, True))
            for child in reversed(child_specs):
                cp, cs, cv, ci = child
                child_key = (cp, cs, cv, ci.canonical_key)
                if child_key not in interface_cache:
                    stack.append((cp, cs, cv, ci, False))
            continue

        children: list[int] = []
        summary = PrimeBlockSummary.empty()
        jet = empty_jet
        binomial = empty_binomial
        cyclotomic: tuple[CyclotomicDigitBlock, ...] = empty_cyclotomic
        for child_key in child_keys:
            child_node, child_summary, child_jet, child_binomial, child_cyclotomic = (
                interface_cache[child_key]
            )
            children.append(child_node)
            summary = summary.then(child_summary)
            if include_primary_jet:
                assert jet is not None and child_jet is not None
                jet = jet.then(child_jet)
                jet_calls += 1
            if projection_algebra:
                assert binomial is not None and child_binomial is not None
                binomial = binomial.then(child_binomial)
                projection_field_calls += 1
                cyclotomic = tuple(
                    a.then(b) for a, b in zip(cyclotomic, child_cyclotomic, strict=True)
                )
                projection_field_calls += len(cyclotomic)

        child_key_tuple = tuple(children)
        if all(child == child_key_tuple[0] for child in child_key_tuple):
            node = child_key_tuple[0]
        else:
            node = structural_nodes.get(child_key_tuple, -1)
            if node < 0:
                node = next_node
                next_node += 1
                structural_nodes[child_key_tuple] = node
                node_children[node] = child_key_tuple
        interface_cache[key] = (node, summary, jet, binomial, cyclotomic)
        pending_children.pop(key, None)

    root_key = (root_args[0], root_args[1], root_args[2], root_args[3].canonical_key)
    _root, summary, jet, binomial, cyclotomic = interface_cache[root_key]

    decision_nodes = len(node_children) + 3
    decision_refs = sum(len(children) for children in node_children.values())
    id_bits = bit_width(max(1, decision_nodes - 1))
    radix_payload = sum(bit_width(base - 1) for base in bases)
    decision_description = decision_nodes + decision_refs * id_bits + radix_payload
    factor_basis_bits = sum(
        bit_width(lane.factor) + bit_width(lane.phase) + bit_width(lane.first_index)
        for lane in basis.lanes
    )
    return PrimeLaneQuotientCompilation(
        start,
        length,
        period,
        bases,
        domain,
        basis.factor_candidates,
        basis.natural_lanes,
        len(basis.lanes),
        basis.generator_gcd_calls,
        basis.generator_groups,
        factor_basis_bits,
        len(interface_cache),
        interface_bits_max,
        interface_bits_total,
        decision_nodes,
        decision_refs,
        decision_description,
        lane_checks,
        lane_transform_cache_hits,
        lane_transform_cache_misses,
        point_transform_cache_hits,
        point_transform_cache_misses,
        summary,
        jet,
        jet_calls,
        terminal_prime_interfaces,
        terminal_composite_interfaces,
        terminal_outside_interfaces,
        wheel_cyclotomic,
        binomial if projection_algebra else None,
        cyclotomic if projection_algebra else (),
        (binomial.compositions + sum(block.compositions for block in cyclotomic))
        if projection_algebra and binomial is not None
        else 0,
    )


__all__ = [
    "PrimeLaneQuotientCompilation",
    "ResidualDivisorInterface",
    "canonical_prime_base_period",
    "compile_prime_block_lane_quotient",
]
