"""Source-bound publication of accelerated Collatz actions and support.

One admitted accelerated action has two canonical consumers: its valuation
action in :class:`CollatzEventArena` and the physical word ``O E**valuation``.
This owner discovers the source transition once and publishes both roots in
chronological lockstep.  It does not claim sublinear discovery of an arbitrary
Collatz source trajectory.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.automata.program_word import (
    CanonicalWord,
    from_values,
    iter_runs,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.frame import CollatzAffineSuffixGerm
from number_compiler.sequences.collatz.germ_cache import CollatzGermTransitionCache
from number_compiler.sequences.collatz.physical_support import (
    PhysicalSupport,
    PhysicalSupportArena,
)
from number_compiler.sequences.collatz.power import CollatzEventArena, CollatzEventNode


@dataclass(frozen=True, slots=True)
class CollatzPublishedPrefix:
    """Authenticated roots for one admitted source prefix."""

    owner: CollatzSourcePublisher = field(repr=False, compare=False)
    source_seed: int
    requested_events: int
    discovered_events: int
    event_root: CollatzEventNode
    physical_support: PhysicalSupport
    target: CollatzAffineSuffixGerm
    reached_one: bool
    discovery_digit_work: int
    admission_digit_comparisons: int

    def validate(self) -> None:
        self.owner.validate(self)


class CollatzSourcePublisher:
    """Own one source/action binding and its demanded projection roots.

    The source is an exact positive odd integer and ``requested_events`` is an
    upper bound.  Publication stops at the accelerated fixed point one, matching
    the CLI event selector.  Initial source digits are retained once; successor
    digit strings and parity itineraries are never materialized.
    """

    __slots__ = (
        "__weakref__",
        "_issued_snapshot",
        "_published",
        "events",
        "ledger",
        "max_digits",
        "max_events",
        "requested_events",
        "seed",
        "supports",
        "transitions",
    )

    def __init__(
        self,
        seed: int,
        requested_events: int,
        *,
        max_events: int,
        max_digits: int,
    ) -> None:
        seed = require_integer(seed, "seed", 1)
        requested_events = require_integer(
            requested_events, "accelerated event count", 0
        )
        max_events = require_integer(max_events, "event budget", 0)
        max_digits = require_integer(max_digits, "digit budget", 1)
        if not seed & 1:
            raise ValueError("accelerated event observations require an odd seed")
        if requested_events > max_events or seed.bit_length() > 2 * max_digits:
            raise ValueError("source observation budget exceeded")
        # Each discovered event retains one event atom/join and at most a
        # logarithmic number of run/normalization nodes in the physical word.
        # This is a capacity bound, not an allocation or a powered-work claim.
        support_nodes = 3 + requested_events * (8 + 4 * max(1, max_digits.bit_length()))
        event_nodes = 1 + requested_events * (
            4 + 2 * max(1, requested_events.bit_length())
        )
        total_nodes = support_nodes + event_nodes
        total_entries = 3 * support_nodes + 5 * event_nodes + 2 * requested_events
        self.seed = seed
        self.requested_events = requested_events
        self.max_events = max_events
        self.max_digits = max_digits
        self.ledger = ResourceLedger(total_nodes, total_entries)
        self.events = CollatzEventArena(ledger=self.ledger)
        self.supports = PhysicalSupportArena(
            max_nodes=max(3, support_nodes), ledger=self.ledger
        )
        self.transitions = CollatzGermTransitionCache(
            ledger=self.ledger, allow_power=False
        )
        self._published: CollatzPublishedPrefix | None = None
        self._issued_snapshot: tuple[object, ...] | None = None
        self.ledger.register_execution_root(self)

    @property
    def binding(self) -> tuple[object, ...]:
        return (
            "collatz-source-publisher-v1",
            self.seed,
            self.requested_events,
            self.max_events,
            self.max_digits,
        )

    @staticmethod
    def _word_leq_integer(word: CanonicalWord, limit: int) -> tuple[bool, int]:
        """Compare an LSD-first radix-4 word without lowering its integer.

        The scan is bounded by the already admitted source-digit budget and is
        local admission geometry.  It retains neither a digit vector nor a
        concrete Collatz endpoint.
        """
        if limit < 0:
            return False, 0
        limit_width = max(1, (limit.bit_length() + 1) // 2)
        if word.length != limit_width:
            return word.length < limit_width, 0
        position = word.length - 1
        comparisons = 0
        for symbol, count in reversed(tuple(iter_runs(word))):
            stop = position - count
            while position > stop:
                comparisons += 1
                boundary = (limit >> (2 * position)) & 3
                if symbol != boundary:
                    return symbol < boundary, comparisons
                position -= 1
        return True, comparisons

    @classmethod
    def _germ_fits_digits(
        cls, germ: CollatzAffineSuffixGerm, digits: int
    ) -> tuple[bool, int]:
        boundary = (1 << (2 * digits)) - 1
        if germ.offset > boundary:
            return False, 0
        if germ.multiplier == 0:
            return True, 0
        quotient = (boundary - germ.offset) // germ.multiplier
        return cls._word_leq_integer(germ.suffix, quotient)

    @classmethod
    def _germ_radix4_width(cls, germ: CollatzAffineSuffixGerm) -> tuple[int, int]:
        """Return exact endpoint width using at most three boundary queries."""
        if germ.multiplier == 0:
            return max(1, (germ.offset.bit_length() + 1) // 2), 0
        alpha_width = max(1, (germ.multiplier.bit_length() + 1) // 2)
        beta_width = (germ.offset.bit_length() + 1) // 2
        width = max(1, beta_width, germ.suffix.length + alpha_width - 1)
        upper = max(beta_width, germ.suffix.length + alpha_width) + 1
        comparisons = 0
        while width <= upper:
            fits, work = cls._germ_fits_digits(germ, width)
            comparisons += work
            if fits:
                return width, comparisons
            width += 1
        raise AssertionError("affine radix-4 width escaped its exact product bound")

    def publish(self) -> CollatzPublishedPrefix:
        found = self._published
        if found is not None:
            self.validate(found)
            return found

        source_digits = tuple(digits_lsd(self.seed, 4))
        germ = CollatzAffineSuffixGerm.from_word(from_values(source_digits))
        event_root = self.events.identity
        support = self.supports.identity
        discovered = 0
        digit_work = 0
        admission_comparisons = 0
        reached_one = self.seed == 1
        while discovered < self.requested_events and not reached_one:
            source_width, comparisons = self._germ_radix4_width(germ)
            admission_comparisons += comparisons
            self.ledger.bump("collatz_source_admission_digit_comparisons", comparisons)
            if source_width > self.max_digits:
                raise ValueError("source observation digit budget exceeded")
            advance = self.transitions.advance(germ)
            valuation = advance.valuation
            event_atom = self.events.event(valuation)
            support_atom = self.supports.event(valuation)
            # Both projections are committed only after both atoms were built.
            event_root = self.events.concat(event_root, event_atom)
            support = self.supports.concat(support, support_atom)
            discovered += 1
            digit_work += source_width
            self.ledger.bump("collatz_source_discovery_events")
            self.ledger.bump("collatz_source_discovery_digit_work", source_width)
            germ = advance.target
            reached_one = germ.multiplier == 0 and germ.offset == 1

        published = CollatzPublishedPrefix(
            self,
            self.seed,
            self.requested_events,
            discovered,
            event_root,
            support,
            germ,
            reached_one,
            digit_work,
            admission_comparisons,
        )
        self._published = published
        self._issued_snapshot = self._publication_snapshot(published)
        self.validate(published)
        return published

    def _publication_snapshot(
        self, published: CollatzPublishedPrefix
    ) -> tuple[object, ...]:
        published.target.__post_init__()
        self.events.validate_node(published.event_root)
        self.supports.validate(published.physical_support)
        return (
            id(published),
            published.source_seed,
            published.requested_events,
            published.discovered_events,
            id(published.event_root),
            published.event_root.node_id,
            published.event_root.effect,
            published.event_root.kind,
            published.event_root.valuation,
            id(published.event_root.left),
            id(published.event_root.right),
            id(published.physical_support),
            published.physical_support.node_id,
            published.physical_support.ticks,
            published.physical_support.odd_ticks,
            published.physical_support.parity,
            id(published.physical_support.left),
            id(published.physical_support.right),
            id(published.target),
            published.target.canonical_key,
            published.reached_one,
            published.discovery_digit_work,
            published.admission_digit_comparisons,
        )

    def validate(self, published: CollatzPublishedPrefix) -> None:
        if type(published) is not CollatzPublishedPrefix or published.owner is not self:
            raise ValueError("Collatz prefix belongs to another source publisher")
        if self._published is not published:
            raise ValueError("Collatz prefix is not the published source action")
        if (
            self._issued_snapshot is None
            or self._publication_snapshot(published) != self._issued_snapshot
        ):
            raise ValueError(
                "Collatz published prefix lost its issued source authority"
            )
        if (
            published.source_seed != self.seed
            or published.requested_events != self.requested_events
            or not 0 <= published.discovered_events <= self.requested_events
            or published.event_root.effect.events != published.discovered_events
            or published.physical_support.odd_ticks != published.discovered_events
            or published.physical_support.ticks
            != published.event_root.effect.physical_steps
            or published.discovery_digit_work < 0
            or published.admission_digit_comparisons < 0
        ):
            raise ValueError("Collatz published prefix has forged semantic fields")
        self.events.validate_node(published.event_root)
        self.supports.validate(published.physical_support)

    @property
    def separately_retained(self) -> dict[str, int]:
        """Legacy metric names; every reported store is ledger-accounted."""
        return {
            "collatz_event_arena_nodes": self.events.node_count,
            "collatz_transition_raw_states": self.transitions.raw_state_count,
            "collatz_transition_canonical_states": self.transitions.canonical_state_count,
            "ledger_accounted": 1,
        }


__all__ = ["CollatzPublishedPrefix", "CollatzSourcePublisher"]
