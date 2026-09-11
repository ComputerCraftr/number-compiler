"""Early canonical cache for Collatz 2-adic germ transitions.

This module owns the cache boundary between exact frame normalization and
valuation/event emission.  Matching rational-root prefixes are quotient gauge:
they are removed before lookup and returned only as valuation actions.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.automata.program_word import EMPTY, CanonicalWord
from number_compiler.arithmetic.automata.symmetry_powering import (
    BinaryLiftEngine,
    BinaryLiftMetrics,
)
from number_compiler.arithmetic.fields.morphism_core import AffineCocycle
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.sequences.collatz.frame import (
    CollatzAffineSuffixAdvance,
    CollatzAffineSuffixGerm,
)
from number_compiler.sequences.collatz.power import CollatzEventNode
from number_compiler.sequences.collatz.root_germs import (
    PadicAngularBoundaryGerm,
    RationalPadicRootGerm,
    RationalPadicRootMismatch,
)


@dataclass(frozen=True, slots=True)
class _CanonicalCollatzTransition:
    valuation: int
    target_multiplier: int
    target_offset: int
    target_suffix: CanonicalWord
    root: RationalPadicRootGerm | None
    mismatch: RationalPadicRootMismatch | None


@dataclass(frozen=True, slots=True)
class _CollatzTransitionAction:
    logical_steps: int
    valuation_offset: int
    fixed_v2: int
    matched_quarters: int
    original_root: RationalPadicRootGerm | None


@dataclass(frozen=True, slots=True)
class CollatzGermPowerAdvance:
    target: CollatzAffineSuffixGerm
    events: int
    valuation_sum: int
    lift_metrics: BinaryLiftMetrics


@dataclass(frozen=True, slots=True)
class CollatzGermEventPowerAdvance:
    target: CollatzAffineSuffixGerm
    events: int
    root: CollatzEventNode
    lift_metrics: BinaryLiftMetrics


class CollatzGermTransitionCache:
    """Early cache over normalized algebraic Collatz frame state.

    The cache key is formed *before* a root boundary is generated.  Complete
    low runs that agree with the pulled-back rational root are removed as a
    gauge action.  Their only retained effect is a valuation offset.  Thus two
    sources that differ only by an arbitrarily long matching frame share the
    same expensive boundary transition instead of first emitting different
    valuations and meeting later in ``CollatzEventArena``.
    """

    __slots__ = (
        "_event_power_engines",
        "_power_engine",
        "_raw_keys",
        "_values",
        "hits",
        "lookups",
        "misses",
        "normalized_quarters",
    )

    def __init__(self) -> None:
        self._values: dict[tuple[object, ...], _CanonicalCollatzTransition] = {}
        self._raw_keys: set[tuple[object, ...]] = set()
        self.lookups = 0
        self.hits = 0
        self.misses = 0
        self.normalized_quarters = 0
        self._power_engine: (
            BinaryLiftEngine[CollatzAffineSuffixGerm, tuple[int, int]] | None
        ) = None
        self._event_power_engines: dict[
            int,
            tuple[object, BinaryLiftEngine[CollatzAffineSuffixGerm, CollatzEventNode]],
        ] = {}

    @property
    def raw_state_count(self) -> int:
        return len(self._raw_keys)

    @property
    def canonical_state_count(self) -> int:
        return len(self._values)

    @property
    def algebraic_compression_ratio(self) -> float:
        return self.raw_state_count / max(1, self.canonical_state_count)

    @staticmethod
    def _transport(
        payload: _CanonicalCollatzTransition,
        action: _CollatzTransitionAction,
    ) -> CollatzAffineSuffixAdvance:
        target = CollatzAffineSuffixGerm(
            payload.target_multiplier,
            payload.target_offset,
            payload.target_suffix,
            action.logical_steps + 1,
        )
        mismatch = payload.mismatch
        if mismatch is not None and action.matched_quarters:
            mismatch = RationalPadicRootMismatch(
                mismatch.denominator_power,
                mismatch.matched_quarters + action.matched_quarters,
                mismatch.source_digit,
                mismatch.constant_at_mismatch,
            )
        return CollatzAffineSuffixAdvance(
            payload.valuation + action.valuation_offset,
            target,
            action.fixed_v2,
            action.original_root if payload.root is not None else None,
            mismatch,
        )

    def advance(self, germ: CollatzAffineSuffixGerm) -> CollatzAffineSuffixAdvance:
        if not isinstance(germ, CollatzAffineSuffixGerm):
            raise TypeError(type(germ))
        self.lookups += 1
        self._raw_keys.add(germ.canonical_key)

        if germ.multiplier == 0:
            key: tuple[object, ...] = ("collatz-germ-constant", germ.offset)
            action = _CollatzTransitionAction(germ.logical_steps, 0, 0, 0, None)

            def lower() -> _CanonicalCollatzTransition:
                numerator = 3 * germ.offset + 1
                valuation = v2_positive(numerator)
                return _CanonicalCollatzTransition(
                    valuation,
                    0,
                    numerator >> valuation,
                    EMPTY,
                    None,
                    None,
                )
        else:
            successor = germ.cocycle.then(
                AffineCocycle(3, 1),
                multiply=lambda a, b: a * b,
                add=lambda a, b: a + b,
            )
            alpha = successor.multiplier
            beta = successor.addend
            alpha_v2 = v2_positive(alpha)
            beta_v2 = v2_positive(beta)
            if beta_v2 < alpha_v2:
                key = (
                    "collatz-germ-fixed-v2",
                    alpha,
                    beta,
                    germ.suffix.node_id,
                    germ.suffix.length,
                )
                action = _CollatzTransitionAction(
                    germ.logical_steps,
                    0,
                    beta_v2,
                    0,
                    None,
                )

                def lower() -> _CanonicalCollatzTransition:
                    return _CanonicalCollatzTransition(
                        beta_v2,
                        alpha >> beta_v2,
                        beta >> beta_v2,
                        germ.suffix,
                        None,
                        None,
                    )
            else:
                base_shift = alpha_v2
                odd_denominator = alpha >> base_shift
                h = germ._pow3_exponent(odd_denominator)
                root = RationalPadicRootGerm(h, beta >> base_shift)
                matched, normalized_root, normalized_suffix = (
                    root.normalize_matching_prefix_word(
                        germ.suffix,
                    )
                )
                self.normalized_quarters += matched
                key = (
                    "collatz-germ-root-boundary",
                    normalized_root.canonical_key,
                    normalized_suffix.node_id,
                    normalized_suffix.length,
                )
                action = _CollatzTransitionAction(
                    germ.logical_steps,
                    base_shift + 2 * matched,
                    base_shift,
                    matched,
                    root,
                )

                def lower() -> _CanonicalCollatzTransition:
                    mismatch, suffix = normalized_root.first_mismatch_word(
                        normalized_suffix
                    )
                    angular = PadicAngularBoundaryGerm.from_mismatch(
                        normalized_root, mismatch
                    )
                    return _CanonicalCollatzTransition(
                        angular.valuation,
                        angular.multiplier,
                        angular.offset,
                        suffix,
                        normalized_root,
                        mismatch,
                    )

        try:
            payload = self._values[key]
        except KeyError:
            payload = lower()
            self._values[key] = payload
            self.misses += 1
        else:
            self.hits += 1
        return self._transport(payload, action)

    @staticmethod
    def _algebraic_state(germ: CollatzAffineSuffixGerm) -> CollatzAffineSuffixGerm:
        return CollatzAffineSuffixGerm(
            germ.multiplier,
            germ.offset,
            germ.suffix,
            0,
        )

    def _lift_engine(
        self,
    ) -> BinaryLiftEngine[CollatzAffineSuffixGerm, tuple[int, int]]:
        found = self._power_engine
        if found is not None:
            return found

        def step(
            germ: CollatzAffineSuffixGerm,
        ) -> tuple[CollatzAffineSuffixGerm, tuple[int, int]]:
            advance = self.advance(germ)
            target = self._algebraic_state(advance.target)
            return target, (1, int(advance.valuation))

        out = BinaryLiftEngine(
            step=step,
            key=lambda germ: germ.algebraic_key,
            identity_weight=(0, 0),
            combine_weight=lambda a, b: (int(a[0]) + int(b[0]), int(a[1]) + int(b[1])),
        )
        self._power_engine = out
        return out

    def advance_many(
        self,
        germ: CollatzAffineSuffixGerm,
        events: int,
    ) -> CollatzGermPowerAdvance:
        """Jump accelerated Collatz events through the shared binary-lift cache.

        Logical time is deliberately excluded from the semantic key; it is an
        additive action restored on the returned germ.  The valuation sum is
        accumulated as a second additive observer.
        """
        if not isinstance(germ, CollatzAffineSuffixGerm):
            raise TypeError(type(germ))
        events = int(events)
        if events < 0:
            raise ValueError(events)
        start_steps = int(germ.logical_steps)
        algebraic = self._algebraic_state(germ)
        target, weight = self._lift_engine().advance(algebraic, events)
        counted_events, valuation_sum = map(int, weight)
        if counted_events != events:
            raise AssertionError((counted_events, events))
        restored = CollatzAffineSuffixGerm(
            target.multiplier,
            target.offset,
            target.suffix,
            start_steps + events,
        )
        return CollatzGermPowerAdvance(
            restored,
            events,
            valuation_sum,
            self._lift_engine().metrics(),
        )

    def _event_lift_engine(
        self, arena: object
    ) -> BinaryLiftEngine[CollatzAffineSuffixGerm, CollatzEventNode]:
        """Return the shared lift specialized to one lazy event-monoid arena."""
        key = id(arena)
        found = self._event_power_engines.get(key)
        if found is not None and found[0] is arena:
            return found[1]
        from number_compiler.sequences.collatz.power import CollatzEventArena

        if not isinstance(arena, CollatzEventArena):
            raise TypeError(type(arena))

        def step(
            germ: CollatzAffineSuffixGerm,
        ) -> tuple[CollatzAffineSuffixGerm, CollatzEventNode]:
            advance = self.advance(germ)
            return self._algebraic_state(advance.target), arena.event(advance.valuation)

        engine = BinaryLiftEngine(
            step=step,
            key=lambda germ: germ.algebraic_key,
            identity_weight=arena.identity,
            combine_weight=arena.concat,
        )
        self._event_power_engines[key] = (arena, engine)
        return engine

    def advance_event_power(
        self,
        germ: CollatzAffineSuffixGerm,
        events: int,
        *,
        arena: object,
    ) -> CollatzGermEventPowerAdvance:
        """Jump events and construct their exact lazy event DAG as lift weight."""
        if not isinstance(germ, CollatzAffineSuffixGerm):
            raise TypeError(type(germ))
        events = int(events)
        if events < 0:
            raise ValueError(events)
        start_steps = int(germ.logical_steps)
        engine = self._event_lift_engine(arena)
        target, root = engine.advance(self._algebraic_state(germ), events)
        effect = getattr(root, "effect", None)
        if effect is None or int(effect.events) != events:
            raise AssertionError((None if effect is None else effect.events, events))
        restored = CollatzAffineSuffixGerm(
            target.multiplier,
            target.offset,
            target.suffix,
            start_steps + events,
        )
        return CollatzGermEventPowerAdvance(restored, events, root, engine.metrics())

    def metrics(self) -> dict[str, int | float]:
        direct_lift = (
            None if self._power_engine is None else self._power_engine.metrics()
        )
        event_lifts = [
            engine.metrics() for _arena, engine in self._event_power_engines.values()
        ]
        return {
            "raw_lookups": self.lookups,
            "raw_states": self.raw_state_count,
            "canonical_states": self.canonical_state_count,
            "canonical_hits": self.hits,
            "canonical_misses": self.misses,
            "normalized_quarters": self.normalized_quarters,
            "algebraic_compression_ratio": self.algebraic_compression_ratio,
            "power_jump_hits": 0 if direct_lift is None else direct_lift.jump_hits,
            "event_power_jump_hits": sum(metric.jump_hits for metric in event_lifts),
            "power_jump_entries": (
                (0 if direct_lift is None else direct_lift.jump_entries)
                + sum(metric.jump_entries for metric in event_lifts)
            ),
        }


__all__ = [
    "CollatzGermEventPowerAdvance",
    "CollatzGermPowerAdvance",
    "CollatzGermTransitionCache",
]
