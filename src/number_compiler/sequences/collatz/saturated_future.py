"""Exact finite accelerated-Collatz safety actions on admitted source cylinders.

The source-free program is an operator descriptor. Binding it still runs one
finite radix-64 selector stage per event; the descriptor does not make source
application logarithmic. Published occurrences retain no valuation itinerary.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator
from dataclasses import dataclass
from itertools import islice
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational as Q
from number_compiler.arithmetic.fields.morphism_core import AffineCocycle
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.arithmetic.fields.threshold_envelope import ThresholdEnvelope
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.hensel_cylinders import (
    MAX_CYLINDER_BITS,
    HenselCylinder,
)
from number_compiler.sequences.collatz.parity import collatz_parity_inverse_residue
from number_compiler.sequences.collatz.radix64_transducer import compose_radix64_events

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.source_publisher import (
        CollatzPublishedPrefix,
    )

MAX_SOURCE_FREE_SELECTOR_EVENTS = 4096


def _integer_digits_lsd(value: int) -> Iterator[int]:
    while value:
        value, digit = divmod(value, 64)
        yield digit


def _apply(endpoint: SkewTransfer[int], value: int) -> int:
    numerator = endpoint.upper * value + endpoint.offset
    target, remainder = divmod(numerator, endpoint.lower)
    if remainder:
        raise ArithmeticError("admitted endpoint is not integral")
    return target


@dataclass(frozen=True, slots=True)
class SaturatedCollatzAction:
    """Endpoint plus complete finite first-descent threshold consumer."""

    endpoint: SkewTransfer[int]
    threshold: ThresholdEnvelope

    def __post_init__(self) -> None:
        if (
            type(self.endpoint) is not SkewTransfer
            or type(self.threshold) is not ThresholdEnvelope
        ):
            raise TypeError(
                "saturated action requires shared skew and threshold owners"
            )
        if any(
            type(v) is not int
            for v in (self.endpoint.upper, self.endpoint.offset, self.endpoint.lower)
        ):
            raise TypeError("saturated endpoint requires exact integer coefficients")
        if self.endpoint.upper <= 0 or self.endpoint.lower <= 0:
            raise ValueError("saturated endpoint must be positively oriented")

    def then(self, after: SaturatedCollatzAction) -> SaturatedCollatzAction:
        if type(after) is not SaturatedCollatzAction:
            raise TypeError("chronological composition requires a saturated action")
        return SaturatedCollatzAction(
            self.endpoint.then(
                after.endpoint, multiply=lambda a, b: a * b, add=lambda a, b: a + b
            ),
            self.threshold.then(self.endpoint, after.threshold),
        )


@dataclass(frozen=True, slots=True)
class SaturatedCollatzOccurrence:
    """A complete action admitted on one exact positive-odd source cylinder."""

    action: SaturatedCollatzAction
    domain: HenselCylinder
    events: int

    def __post_init__(self) -> None:
        if (
            type(self.action) is not SaturatedCollatzAction
            or type(self.domain) is not HenselCylinder
        ):
            raise TypeError(
                "saturated occurrence requires an action and a Hensel cylinder"
            )
        if type(self.events) is not int or self.events <= 0:
            raise ValueError("saturated occurrence duration must be positive")
        lower = self.action.endpoint.lower
        if (
            lower & (lower - 1)
            or self.domain.bits != lower.bit_length()
            or not self.domain.residue & 1
            or not _apply(self.action.endpoint, self.domain.residue) & 1
        ):
            raise ValueError(
                "saturated action is incompatible with its odd source cylinder"
            )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        transfer = self.action.endpoint
        return (
            "collatz-saturated-occurrence-v2",
            self.events,
            self.domain.bits,
            self.domain.residue,
            transfer.upper,
            transfer.offset,
            transfer.lower,
            self.action.threshold.lines,
        )

    def _admit_source(self, source: int) -> None:
        if (
            type(source) is not int
            or source <= 0
            or not source & 1
            or not self.domain.contains(source)
        ):
            raise ValueError("source is outside the positive-odd admitted cylinder")

    def apply_exact(self, source: int) -> int:
        self._admit_source(source)
        return _apply(self.action.endpoint, source)

    def reaches_below(self, source: int, threshold: int) -> bool:
        if type(threshold) is not int or threshold <= 0:
            raise ValueError("threshold must be a positive integer")
        self._admit_source(source)
        bound = self.action.threshold.evaluate(Q(threshold))
        return bound is not None and Q(source) < bound

    def descends(self, source: int) -> bool:
        return self.reaches_below(source, source)

    def source_high_fiber(self, source: int) -> int:
        self._admit_source(source)
        difference = source - self.domain.residue
        if difference < 0:
            raise ValueError("source precedes the natural cylinder origin")
        return difference >> self.domain.bits

    @property
    def target_origin(self) -> int:
        return _apply(self.action.endpoint, self.domain.residue)

    @property
    def odd_fiber_offset(self) -> int:
        origin = self.target_origin
        if not origin & 1:
            raise ArithmeticError("accelerated target origin must be odd")
        return (origin - 1) // 2

    @property
    def joint_multiplier(self) -> int:
        """High-fiber multiplier in the centered 2/3-adic chart."""
        return self.action.endpoint.upper

    def rebased_target_high_fiber(self, source: int) -> int:
        target = self.apply_exact(source)
        return (target - 1) // 2 - self.odd_fiber_offset

    def deck_image(self, deck: int) -> tuple[int, int]:
        """Return the deck and high-fiber increment for ``Y=deck+64H``."""
        if type(deck) is not int or not 0 <= deck < 64:
            raise ValueError("joint-adic deck must lie in 0..63")
        product = self.joint_multiplier * deck
        return product & 63, product >> 6

    def descent_fiber_start(self) -> int | None:
        """First natural cylinder fiber with a strict intermediate descent.

        Each threshold line is solved as an exact one-variable inequality;
        finite upper intervals and cap equality are handled explicitly.
        """
        modulus = 1 << self.domain.bits
        residue = self.domain.residue
        first_positive_k = 0 if residue > 0 else 1
        first_positive_x = residue + modulus * first_positive_k
        starts: list[int] = []
        for line in self.action.threshold.lines:
            slope = line.multiplier
            intercept = line.addend
            coefficient = Q(1) - slope
            if coefficient >= Q(0):
                if Q(first_positive_x) * coefficient < intercept:
                    starts.append(first_positive_k)
                continue
            boundary = intercept / coefficient
            required_x = boundary.numerator // boundary.denominator + 1
            k = max(first_positive_k, (required_x - residue + modulus - 1) // modulus)
            if Q(residue + modulus * k) * coefficient < intercept:
                starts.append(k)
        return min(starts) if starts else None


def publish_valuation_block(valuations: Iterable[int]) -> SaturatedCollatzOccurrence:
    """Use exact q choices transiently, then publish only their semantic action."""
    word = tuple(islice(valuations, 65))
    if not word or any(type(q) is not int or q <= 0 for q in word):
        raise ValueError("valuation block requires positive exact choices")
    if len(word) > 64:
        raise BlockContextBudgetExceeded("saturated valuation leaf exceeds 64 events")
    if sum(word) + 1 > MAX_CYLINDER_BITS:
        raise BlockContextBudgetExceeded("saturated leaf exceeds Hensel precision")
    divisions = 0
    offset = 0
    parity_word = 1
    multiplier = 1
    lines: list[AffineCocycle[Q]] = []
    for q in word:
        offset = 3 * offset + (1 << divisions)
        divisions += q
        parity_word |= 1 << divisions
        multiplier *= 3
        lines.append(
            AffineCocycle(Q(1 << divisions, multiplier), Q(-offset, multiplier))
        )
    bits = divisions + 1
    domain = HenselCylinder(bits, collatz_parity_inverse_residue(parity_word, bits))
    action = SaturatedCollatzAction(
        SkewTransfer(multiplier, offset, 1 << divisions),
        ThresholdEnvelope.normalize(tuple(lines)),
    )
    return SaturatedCollatzOccurrence(action, domain, len(word))


def compose_occurrences(
    before: SaturatedCollatzOccurrence, after: SaturatedCollatzOccurrence
) -> SaturatedCollatzOccurrence:
    if (
        type(before) is not SaturatedCollatzOccurrence
        or type(after) is not SaturatedCollatzOccurrence
    ):
        raise TypeError("source occurrence composition requires exact occurrences")
    endpoint = before.action.endpoint
    divisions = endpoint.lower.bit_length() - 1
    if 1 << divisions != endpoint.lower:
        raise ValueError("Collatz source pullback requires a dyadic denominator")
    pulled = after.domain.pullback_modular(
        multiplier=endpoint.upper, offset=endpoint.offset, divisions=divisions
    )
    domain = before.domain.intersect(pulled)
    if domain is None:
        raise ValueError("source cylinders are incompatible")
    return SaturatedCollatzOccurrence(
        before.action.then(after.action), domain, before.events + after.events
    )


@dataclass(frozen=True, slots=True)
class SaturatedCollatzPowerResult:
    occurrence: SaturatedCollatzOccurrence
    leaves: int
    compositions: int

    def __post_init__(self) -> None:
        if type(self.occurrence) is not SaturatedCollatzOccurrence:
            raise TypeError("saturated power requires one exact occurrence")
        if (
            type(self.leaves) is not int
            or self.leaves <= 0
            or type(self.compositions) is not int
            or self.compositions != self.leaves - 1
        ):
            raise ValueError("saturated power counters are inconsistent")


class _SaturatedFold:
    """One bounded q buffer and binary-counter fold of complete occurrences."""

    __slots__ = (
        "buffer",
        "compositions",
        "leaf_events",
        "leaves",
        "ledger",
        "levels",
        "reads",
    )

    def __init__(self, leaf_events: int, ledger: ResourceLedger | None = None) -> None:
        self.leaf_events = leaf_events
        self.ledger = ledger
        self.buffer: list[int] = []
        self.levels: list[SaturatedCollatzOccurrence | None] = []
        self.reads = 0
        self.leaves = 0
        self.compositions = 0

    def _charge(self, node: SaturatedCollatzOccurrence) -> None:
        ledger = self.ledger
        if ledger is None:
            return
        ledger.bump(
            "collatz_saturated_threshold_lines", len(node.action.threshold.lines)
        )
        ledger.bump(
            "collatz_saturated_coefficient_bits",
            sum(
                line.multiplier.numerator.bit_length()
                + line.multiplier.denominator.bit_length()
                + line.addend.numerator.bit_length()
                + line.addend.denominator.bit_length()
                for line in node.action.threshold.lines
            ),
        )

    def _compose(
        self, before: SaturatedCollatzOccurrence, after: SaturatedCollatzOccurrence
    ) -> SaturatedCollatzOccurrence:
        if self.ledger is not None:
            self.ledger.bump("collatz_saturated_composition_attempts")
        result = compose_occurrences(before, after)
        self.compositions += 1
        if self.ledger is not None:
            self.ledger.bump("collatz_saturated_compositions")
        self._charge(result)
        return result

    def _push(self, node: SaturatedCollatzOccurrence) -> None:
        self.leaves += 1
        if self.ledger is not None:
            self.ledger.bump("collatz_saturated_leaves")
        self._charge(node)
        level = 0
        while True:
            if level == len(self.levels):
                self.levels.append(node)
                return
            prior = self.levels[level]
            if prior is None:
                self.levels[level] = node
                return
            self.levels[level] = None
            node = self._compose(prior, node)
            level += 1

    def _publish_buffer(self) -> None:
        if not self.buffer:
            return
        if self.ledger is not None:
            self.ledger.bump("collatz_saturated_leaf_attempts")
        self._push(publish_valuation_block(self.buffer))
        self.buffer.clear()

    def accept(self, valuation: int) -> None:
        self.reads += 1
        if self.ledger is not None:
            self.ledger.bump("collatz_saturated_event_reads")
        self.buffer.append(valuation)
        if len(self.buffer) == self.leaf_events:
            self._publish_buffer()

    def finish(self, expected_events: int) -> SaturatedCollatzPowerResult:
        self._publish_buffer()
        result: SaturatedCollatzOccurrence | None = None
        for node in reversed(self.levels):
            if node is not None:
                result = node if result is None else self._compose(result, node)
        if (
            result is None
            or result.events != self.reads
            or self.reads != expected_events
        ):
            raise AssertionError("selector did not publish the requested duration")
        return SaturatedCollatzPowerResult(result, self.leaves, self.compositions)


@dataclass(frozen=True, slots=True)
class SourceFreeSaturatedCollatzProgram:
    """Finite operator schema; source binding is charged separately."""

    events: int

    def __post_init__(self) -> None:
        if type(self.events) is not int or self.events <= 0:
            raise ValueError("program duration must be a positive integer")

    @property
    def canonical_key(self) -> tuple[str, int]:
        return "collatz-source-free-saturated-v1", self.events

    @property
    def operator_nodes(self) -> int:
        return 1

    @property
    def description_bits(self) -> int:
        return self.events.bit_length()

    def then(
        self, after: SourceFreeSaturatedCollatzProgram
    ) -> SourceFreeSaturatedCollatzProgram:
        if type(after) is not SourceFreeSaturatedCollatzProgram:
            raise TypeError("source-free composition requires another program")
        return SourceFreeSaturatedCollatzProgram(self.events + after.events)

    def square(self) -> SourceFreeSaturatedCollatzProgram:
        return self.then(self)

    def power(self, exponent: int) -> SourceFreeSaturatedCollatzProgram:
        if type(exponent) is not int or exponent <= 0:
            raise ValueError("power exponent must be positive")
        return SourceFreeSaturatedCollatzProgram(self.events * exponent)

    def bind(
        self, source: int, *, leaf_events: int = 6, selector_event_budget: int = 64
    ) -> SaturatedCollatzPowerResult:
        """Select q once, publish bounded leaves, and compose a balanced result.

        This uses one stage per event, with digit flow through that pipeline;
        the application cost is not bounded by descriptor size. The result
        contains neither those stages nor a q history.
        """
        if type(source) is not int or source <= 0 or not source & 1:
            raise ValueError("binding needs a positive odd source")
        if source.bit_length() > MAX_CYLINDER_BITS:
            raise BlockContextBudgetExceeded("source exceeds Hensel precision")
        if type(leaf_events) is not int or not 1 <= leaf_events <= 64:
            raise ValueError("leaf duration must lie in 1..64")
        if type(selector_event_budget) is not int or selector_event_budget <= 0:
            raise ValueError("selector budget must be positive")
        if self.events > min(selector_event_budget, MAX_SOURCE_FREE_SELECTOR_EVENTS):
            raise BlockContextBudgetExceeded("radix-64 selector event budget exceeded")
        fold = _SaturatedFold(leaf_events)
        compose_radix64_events(
            _integer_digits_lsd(source),
            self.events,
            max_events=selector_event_budget,
            valuation_sink=fold.accept,
            collect_output=False,
        )
        return fold.finish(self.events)


def saturated_power_from_source(
    source: int,
    events: int,
    *,
    leaf_events: int = 6,
    selector_event_budget: int = 64,
) -> SaturatedCollatzPowerResult:
    return SourceFreeSaturatedCollatzProgram(events).bind(
        source, leaf_events=leaf_events, selector_event_budget=selector_event_budget
    )


def saturated_dyadic_power_from_source(
    source: int,
    level: int,
    *,
    leaf_events: int = 6,
    selector_event_budget: int = 64,
) -> SaturatedCollatzPowerResult:
    if type(level) is not int or level < 0:
        raise ValueError("dyadic level must be nonnegative")
    if type(selector_event_budget) is not int or selector_event_budget <= 0:
        raise ValueError("selector budget must be positive")
    if (
        level
        >= min(selector_event_budget, MAX_SOURCE_FREE_SELECTOR_EVENTS).bit_length()
    ):
        raise BlockContextBudgetExceeded("radix-64 selector event budget exceeded")
    return saturated_power_from_source(
        source,
        1 << level,
        leaf_events=leaf_events,
        selector_event_budget=selector_event_budget,
    )


def from_published_prefix(
    published: CollatzPublishedPrefix, *, leaf_events: int = 6
) -> SaturatedCollatzPowerResult | None:
    """Demand safety from an already admitted CLI event root without discovery.

    The source publisher remains the only q selector. This consumer traverses
    its authenticated chronology once, constructs bounded saturated leaves,
    and retains only their complete composed result. A zero-event prefix has
    no intermediate threshold and returns ``None``.
    """
    if type(leaf_events) is not int or not 1 <= leaf_events <= 64:
        raise ValueError("leaf duration must lie in 1..64")
    published.validate()
    if published.discovered_events == 0:
        return None
    ledger = published.owner.ledger
    owner = ledger.register(
        "collatz-saturated-temporary", "collatz_safety_construction"
    )
    # One source read and one candidate threshold line per finite event, plus
    # balanced leaves and joins. This is temporary construction capacity, not
    # a retained powered-state claim.
    temporary = 2 * published.discovered_events + 1
    ledger.bump("collatz_saturated_attempts")
    try:
        ledger.reserve(owner, entries=temporary, nodes=temporary)
    except BaseException:
        ledger.bump("collatz_saturated_failed_constructions")
        raise
    try:
        return _from_published_prefix_reserved(published, leaf_events=leaf_events)
    except BaseException:
        ledger.bump("collatz_saturated_failed_constructions")
        raise
    finally:
        ledger.release(owner, entries=temporary, nodes=temporary)


def _from_published_prefix_reserved(
    published: CollatzPublishedPrefix, *, leaf_events: int
) -> SaturatedCollatzPowerResult:
    """Construct under a temporary reservation owned by the source ledger."""
    arena = published.owner.events
    fold = _SaturatedFold(leaf_events, published.owner.ledger)
    stack = [published.event_root]
    while stack:
        node = stack.pop()
        arena.validate_node(node)
        if node.kind == "identity":
            continue
        if node.kind == "concat":
            assert node.left is not None and node.right is not None
            stack.extend((node.right, node.left))
            continue
        assert node.valuation is not None
        fold.accept(node.valuation)
    result = fold.finish(published.discovered_events)
    if not result.occurrence.domain.contains(published.source_seed):
        raise AssertionError("published event root is outside its composed cylinder")
    return result
