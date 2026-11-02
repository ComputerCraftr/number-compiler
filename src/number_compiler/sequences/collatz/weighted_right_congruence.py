"""Source-certified weighted unary right congruence for repeated Collatz words.

The *control* identity records the residual right language for one authenticated
normalized parity word: how many copies remain and the first differing bit on
exit.  Historical add/subtract totals are weights, never class identifiers.
This is deliberately a unary, guarded future quotient, not a claim that all
Collatz border families form a globally finite automaton.

All future transitions are issued from exact field actions and the dyadic
exit congruence; no parity tape or occurrence-indexed bank is constructed.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Final, TypeAlias

from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.skew_cylinder_repeat import (
    RepeatedWordMooreCylinder,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    SourceCongruence,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.boundary_macros import (
        CollatzBoundaryMacro,
    )

WeightedRightKey: TypeAlias = tuple[str, tuple[int, int, int], int | None, int | None]
WEIGHTED_RIGHT_CLASS_TAG: Final[str] = "collatz-weighted-unary-right-v1"


@dataclass(frozen=True, slots=True)
class _WeightedRightTransitionSnapshot:
    origin: WeightedRightKey
    target: WeightedRightKey
    guard: tuple[int, int, int]
    target_guard: tuple[int, int, int]
    base_coefficients: tuple[int, ...]
    action_coefficients: tuple[int, ...]
    repetitions: int
    source_witness: int
    pointed_source: int | None


@dataclass(frozen=True, slots=True)
class _WeightedRightBindingSnapshot:
    future: WeightedRightKey
    guard: tuple[int, int, int]
    word_coefficients: tuple[int, ...]
    source_witness: int
    pointed_source: int | None


@dataclass(frozen=True, slots=True)
class CollatzDoubleWeight:
    """Two exact physical ledgers, derived from *one* powered field action.

    For each normalized step H0/H1, debit is the resulting normalized state.
    Credit is the value added by the odd 3n+1 operation (zero on H0).
    A pending final odd 3n+1 action contributes credit but no debit.
    """

    added: int
    subtracted: int
    normalized_endpoint: int
    physical_endpoint: int

    def check(self, source: int) -> None:
        if (
            type(source) is not int
            or source <= 0
            or type(self.added) is not int
            or type(self.subtracted) is not int
            or min(self.added, self.subtracted) < 0
            or source + self.added - self.subtracted != self.physical_endpoint
            or self.normalized_endpoint <= 0
        ):
            raise ValueError("Collatz double-accumulator conservation failed")


def exact_double_weight(
    action: DyadicTerminalFieldAction, source: int, *, phase: int = 0
) -> CollatzDoubleWeight:
    """Project full add/debit totals from the authenticated affine sum.

    This has no per-step work and does not retain another arithmetic engine.
    ``phase=1`` means a final odd G was executed without its H half-step.
    """
    if type(action) is not DyadicTerminalFieldAction or not action.producer_issued:
        raise TypeError("double weights require an authenticated field action")
    if type(phase) is not int or phase not in (0, 1):
        raise ValueError("pending Collatz phase must be zero or one")
    endpoint = action.endpoint(source)
    if phase and not (endpoint & 1):
        raise ValueError("an unmatched 3n+1 operation requires an odd endpoint")
    if action.steps:
        numerator = action.sum_gain * source + action.sum_offset
        successor_sum, remainder = divmod(numerator, 1 << action.steps)
        if remainder:
            raise ValueError("authenticated successor sum is not integral")
    else:
        successor_sum = 0
    added = successor_sum + endpoint - source
    physical = endpoint
    if phase:
        added += 2 * endpoint + 1
        physical = 3 * endpoint + 1
    result = CollatzDoubleWeight(added, successor_sum, endpoint, physical)
    result.check(source)
    return result


@dataclass(frozen=True, slots=True)
class WeightedRightClass:
    """Canonical residual future class for one repeated normalized word.

    Its signature has no pointed source and no accumulated history.  Two
    sources are equivalent *on this explicit unary parity/exit alphabet* if
    their word and remaining lifetime/exit offset agree.  Demanded decimal,
    upper, or carry ports require further source-guard intersections.
    """

    word: tuple[int, int, int]
    remaining: int | None
    exit_offset: int | None

    def __post_init__(self) -> None:
        if (
            type(self.word) is not tuple
            or len(self.word) != 3
            or any(type(v) is not int for v in self.word)
            or self.word[0] <= 0
            or self.word[1] <= 0
            or self.word[2] < 0
            or (
                self.remaining is not None
                and (type(self.remaining) is not int or self.remaining < 0)
            )
            or (
                self.exit_offset is not None
                and (
                    type(self.exit_offset) is not int
                    or not 0 <= self.exit_offset < self.word[0]
                )
            )
            or ((self.remaining is None) != (self.exit_offset is None))
        ):
            raise ValueError("weighted right-congruence class is malformed")

    @property
    def key(self) -> WeightedRightKey:
        return (
            WEIGHTED_RIGHT_CLASS_TAG,
            self.word,
            self.remaining,
            self.exit_offset,
        )


@dataclass(frozen=True, slots=True, init=False)
class WeightedRightTransition:
    """Original-source guarded representative transition and two-output weight."""

    origin: WeightedRightClass
    target: WeightedRightClass
    guard: SourceCongruence
    target_guard: SourceCongruence
    base_action: DyadicTerminalFieldAction
    action: DyadicTerminalFieldAction
    repetitions: int
    source_witness: int
    pointed_source: int | None
    _issuer: object
    _binding: _WeightedRightTransitionSnapshot

    def __init__(self) -> None:
        raise TypeError("weighted transitions require a source-checked issuer")

    @classmethod
    def issue_weighted_right_transition(
        cls,
        source_binding: object,
        repetitions: int,
        *,
        action_authority: CollatzBoundaryMacro | None = None,
        preflight: Callable[[int], None],
    ) -> WeightedRightTransition:
        if type(source_binding) is not WeightedRightBinding:
            raise TypeError("weighted transition requires an authenticated binding")
        source_binding.validate_issued()
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("repetition count must be a nonnegative integer")
        if not callable(preflight):
            raise TypeError("weighted powering requires a budget owner")
        origin = source_binding.future
        guard = source_binding.guard
        base_action = source_binding.word
        source_witness = source_binding.source_witness
        pointed_source = source_binding.pointed_source
        if origin.remaining is not None and repetitions > origin.remaining:
            raise ValueError("repetition exceeds exact right-congruence lifetime")
        duration = base_action.steps * repetitions
        # Reserve before constructing powered coefficients or the potentially
        # large target modulus. This check also covers an already-issued action
        # supplied by a family consumer, since its endpoint/guard projection
        # still performs the same large-integer work.
        preflight(8 * (source_witness.bit_length() + 4 * duration + 32))
        remaining = None if origin.remaining is None else origin.remaining - repetitions
        target = WeightedRightClass(origin.word, remaining, origin.exit_offset)
        target_guard = _lifetime_guard(base_action, remaining, origin.exit_offset)
        if origin.remaining is None:
            denominator = (1 << base_action.steps) - base_action.gain
            if (
                origin.exit_offset is not None
                or pointed_source != source_witness
                or denominator * source_witness - base_action.offset != 0
            ):
                raise ValueError(
                    "unbounded transition requires its exact pointed fixed point"
                )
        # A source-issued 89-entry boundary already carries the exact powered
        # field action. Reuse that action instead of rebuilding the same large
        # affine coefficients from its one-step word. This authority is
        # deliberately restricted to the one-run 89 macro; all other callers
        # continue to have the transition issuer construct the power itself.
        if action_authority is None:
            action = base_action.power(repetitions)
        else:
            from number_compiler.sequences.collatz.border_identity import (
                ENTRY_89_AT_NINE,
            )
            from number_compiler.sequences.collatz.boundary_macros import (
                CollatzBoundaryMacro,
                validate_boundary_macro,
            )

            if type(action_authority) is not CollatzBoundaryMacro:
                raise TypeError("weighted action authority is not an issued boundary")
            validate_boundary_macro(action_authority)
            canonical_one = DyadicTerminalFieldAction.one_run(1)
            if (
                action_authority.identity != ENTRY_89_AT_NINE
                or action_authority.source != source_witness
                or action_authority.repetitions != repetitions
                or base_action.coefficient_snapshot()
                != canonical_one.coefficient_snapshot()
                or action_authority.fields.steps != duration
            ):
                raise ValueError(
                    "weighted action authority does not certify this 89 transition"
                )
            action = action_authority.fields
        if action.steps != duration:
            raise ValueError("weighted transition has an inexact duration")
        if not guard.admits(source_witness):
            raise ValueError("weighted transition guard lost its source witness")
        expected_origin_guard = _lifetime_guard(
            base_action, origin.remaining, origin.exit_offset
        )
        if guard.meet(expected_origin_guard) != guard:
            raise ValueError("weighted transition guard exceeds its origin class")
        expected_target_guard = _lifetime_guard(
            base_action, remaining, origin.exit_offset
        )
        if target_guard.meet(expected_target_guard) != target_guard:
            raise ValueError("weighted transition target guard exceeds its class")
        if not target_guard.admits(action.endpoint(source_witness)):
            raise ValueError("weighted transition witness lost its target guard")
        transition = object.__new__(cls)
        for name, value in (
            ("origin", origin),
            ("target", target),
            ("guard", guard),
            ("target_guard", target_guard),
            ("base_action", base_action),
            ("action", action),
            ("repetitions", repetitions),
            ("source_witness", source_witness),
            ("pointed_source", pointed_source),
        ):
            object.__setattr__(transition, name, value)
        object.__setattr__(transition, "_issuer", transition)
        object.__setattr__(transition, "_binding", transition._snapshot())
        return transition

    def _snapshot(self) -> _WeightedRightTransitionSnapshot:
        return _WeightedRightTransitionSnapshot(
            self.origin.key,
            self.target.key,
            (self.guard.residue, self.guard.modulus, self.guard.minimum_source),
            (
                self.target_guard.residue,
                self.target_guard.modulus,
                self.target_guard.minimum_source,
            ),
            self.base_action.coefficient_snapshot(),
            self.action.coefficient_snapshot(),
            self.repetitions,
            self.source_witness,
            self.pointed_source,
        )

    def _require_issued(self) -> None:
        if (
            type(self) is not WeightedRightTransition
            or getattr(self, "_issuer", None) is not self
            or not isinstance(
                getattr(self, "_binding", None), _WeightedRightTransitionSnapshot
            )
            or self._binding != self._snapshot()
        ):
            raise ValueError("weighted transition changed after source issuance")

    def validate_issued(self) -> None:
        """Check the issued snapshot before another owner consumes this value."""
        self._require_issued()

    def evaluate(self, source: int) -> CollatzDoubleWeight:
        self._require_issued()
        if type(source) is not int or source <= 0:
            raise ValueError("weighted transition source must be a positive integer")
        if (
            self.pointed_source is not None and source != self.pointed_source
        ) or not self.guard.admits(source):
            raise ValueError(
                "source is outside this transition's original-source guard"
            )
        weight = exact_double_weight(self.action, source)
        if not self.target_guard.admits(weight.normalized_endpoint):
            raise ValueError("powered successor lost its exact exit guard")
        return weight


@dataclass(frozen=True, slots=True, init=False)
class WeightedRightBinding:
    """Source-to-class transport, without embedding the source into the ID."""

    future: WeightedRightClass
    guard: SourceCongruence
    word: DyadicTerminalFieldAction
    source_witness: int
    pointed_source: int | None
    _issuer: object = field(repr=False, compare=False)
    _binding: _WeightedRightBindingSnapshot = field(repr=False, compare=False)

    def __init__(self) -> None:
        raise TypeError("weighted bindings require source-word admission")

    @classmethod
    def issue_source_binding(
        cls,
        future: WeightedRightClass,
        guard: SourceCongruence,
        word: DyadicTerminalFieldAction,
        source_witness: int,
        pointed_source: int | None,
        *,
        preflight: Callable[[int], None] | None,
        source_transition: WeightedRightTransition | None = None,
    ) -> WeightedRightBinding:
        if (
            type(future) is not WeightedRightClass
            or type(guard) is not SourceCongruence
            or type(word) is not DyadicTerminalFieldAction
            or not word.producer_issued
            or type(source_witness) is not int
            or source_witness <= 0
            or (
                pointed_source is not None
                and (type(pointed_source) is not int or pointed_source <= 0)
            )
        ):
            raise TypeError("weighted binding admission is malformed")
        if source_transition is None:
            if preflight is None or not callable(preflight):
                raise TypeError("weighted binding admission requires a budget owner")
            # The checked action producer composes only valid normalized
            # parity transitions and seals all coefficient fields together.
            # Admission still charges source/action operands before the exact
            # cylinder check, but does not replay the parity word.
            preflight(8 * (source_witness.bit_length() + word.steps + 32))
            if not word.certifies(source_witness):
                raise ValueError("weighted word does not admit its source witness")
        else:
            if type(source_transition) is not WeightedRightTransition:
                raise TypeError("weighted successor needs an issued transition")
            # evaluate() validates the transition snapshot before consuming it.
            transported = source_transition.evaluate(
                source_transition.source_witness
            ).normalized_endpoint
            if (
                source_transition.base_action.coefficient_snapshot()
                != word.coefficient_snapshot()
                or source_transition.target != future
                or source_transition.target_guard != guard
                or transported != source_witness
                or source_transition.pointed_source != pointed_source
            ):
                raise ValueError("weighted binding lost its issued predecessor")
        if (
            not word.certifies(source_witness)
            or not guard.admits(source_witness)
            or _right_class_for_source(word, source_witness) != future
        ):
            raise ValueError("weighted binding has no exact source-to-class proof")
        if future.remaining is None:
            if (
                future.exit_offset is not None
                or pointed_source != source_witness
                or ((1 << word.steps) - word.gain) * source_witness - word.offset != 0
            ):
                raise ValueError(
                    "unbounded binding needs its exact pointed fixed point"
                )
        else:
            expected_guard = _lifetime_guard(word, future.remaining, future.exit_offset)
            if guard.meet(expected_guard) != guard:
                raise ValueError("weighted binding guard exceeds its future class")
            if pointed_source is not None and not guard.admits(pointed_source):
                raise ValueError("weighted pointed source is outside its guard")

        binding = object.__new__(cls)
        for name, value in (
            ("future", future),
            ("guard", guard),
            ("word", word),
            ("source_witness", source_witness),
            ("pointed_source", pointed_source),
        ):
            object.__setattr__(binding, name, value)
        object.__setattr__(binding, "_issuer", binding)
        object.__setattr__(binding, "_binding", binding._snapshot())
        return binding

    def _snapshot(self) -> _WeightedRightBindingSnapshot:
        return _WeightedRightBindingSnapshot(
            self.future.key,
            (self.guard.residue, self.guard.modulus, self.guard.minimum_source),
            self.word.coefficient_snapshot(),
            self.source_witness,
            self.pointed_source,
        )

    def _require_issued(self) -> None:
        if (
            type(self) is not WeightedRightBinding
            or getattr(self, "_issuer", None) is not self
            or not isinstance(
                getattr(self, "_binding", None), _WeightedRightBindingSnapshot
            )
            or self._binding != self._snapshot()
        ):
            raise ValueError("weighted binding changed after source admission")

    def validate_issued(self) -> None:
        """Check the source/class payload before another owner consumes it."""
        self._require_issued()

    def power(
        self,
        count: int,
        *,
        action_authority: CollatzBoundaryMacro | None = None,
        preflight: Callable[[int], None],
    ) -> WeightedRightTransition:
        return WeightedRightTransition.issue_weighted_right_transition(
            self,
            count,
            preflight=preflight,
            action_authority=action_authority,
        )


def transport_weighted_right_binding(
    transition: WeightedRightTransition, source: int
) -> WeightedRightBinding:
    """Transport a validated residual class across its exact returned action."""
    if type(transition) is not WeightedRightTransition:
        raise TypeError("weighted successor needs an issued transition")
    return WeightedRightBinding.issue_source_binding(
        transition.target,
        transition.target_guard,
        transition.base_action,
        source,
        transition.pointed_source,
        preflight=None,
        source_transition=transition,
    )


def _lifetime_guard(
    word: DyadicTerminalFieldAction, remaining: int | None, exit_offset: int | None
) -> SourceCongruence:
    """Exact future dyadic class, including the first changed parity position."""
    parity = SourceCongruence(word.source_residue, word.source_modulus)
    if remaining is None:
        # Fixed point of F has no finite exit.  A modular guard cannot prove
        # equality to the unique rational fixed point; the binding retains its
        # pointed source and never transports this infinite class broadly.
        return parity
    assert exit_offset is not None
    valuation = word.steps * remaining + exit_offset
    modulus = 1 << (valuation + 1)
    coefficient = (1 << word.steps) - word.gain  # odd
    residue = ((1 << valuation) + word.offset) * pow(coefficient, -1, modulus) % modulus
    exact = SourceCongruence(residue, modulus)
    # At lifetime zero the next word is *not* admitted: its first changed
    # bit occurs at exit_offset.  Intersecting a complete-word parity guard
    # at that endpoint would incorrectly eliminate the valid exit state.
    if remaining == 0:
        return exact
    joint = exact.meet(parity)
    if joint is None:
        raise AssertionError("repeated parity word disagrees with its exit cylinder")
    return joint


def _right_class_for_source(
    word: DyadicTerminalFieldAction, source: int
) -> WeightedRightClass:
    """Derive the exact repeated-word future class from its source witness."""
    if not word.certifies(source):
        raise ValueError("right-class source does not admit its parity word")
    denominator = (1 << word.steps) - word.gain
    defect = denominator * source - word.offset
    if defect == 0:
        return WeightedRightClass((word.steps, word.gain, word.offset), None, None)
    valuation = (abs(defect) & -abs(defect)).bit_length() - 1
    remaining, exit_offset = divmod(valuation, word.steps)
    return WeightedRightClass(
        (word.steps, word.gain, word.offset), remaining, exit_offset
    )


def bind_weighted_right_class(
    word: DyadicTerminalFieldAction,
    source: int,
    *,
    port_guard: SourceCongruence | None = None,
    preflight: Callable[[int], None],
) -> WeightedRightBinding:
    """Issue a source-authenticated unary future class before powering.

    A port guard may refine the class, but no foreign carry/clock port can be
    inferred from the dyadic future class alone.  The regular production
    budget owner supplies ``preflight``; no unbounded admission is implicit.
    The producer seal covers the parity-word composition and all coefficient
    fields, so admission checks the exact source cylinder without replaying
    each normalized step.
    """
    if type(word) is not DyadicTerminalFieldAction or not word.producer_issued:
        raise TypeError("weighted right class requires an issued normalized word")
    if type(source) is not int or source <= 0:
        raise ValueError("weighted right source must be a positive integer")
    cylinder = RepeatedWordMooreCylinder.from_action(word, source, preflight=preflight)
    if port_guard is not None and type(port_guard) is not SourceCongruence:
        raise TypeError("punctured port guard must be an exact congruence")
    future = WeightedRightClass(
        (word.steps, word.gain, word.offset),
        cylinder.remaining_repetitions,
        cylinder.exit_offset,
    )
    guard = _lifetime_guard(word, future.remaining, future.exit_offset)
    # D(x)=0 is an equality, not a finite CRT class.  Keep that fixed-point
    # source explicitly pointed rather than admitting foreign CRT fibers.
    pointed_source = source if cylinder.defect == 0 else None
    if port_guard is not None:
        narrowed = guard.meet(port_guard)
        if narrowed is None:
            raise ValueError("requested carry/clock port conflicts with source class")
        guard = narrowed
    if not guard.admits(source):
        raise AssertionError("weighted future class lost its pointed source")
    return WeightedRightBinding.issue_source_binding(
        future,
        guard,
        word,
        source,
        pointed_source,
        preflight=preflight,
    )


__all__ = [
    "CollatzDoubleWeight",
    "WeightedRightBinding",
    "WeightedRightClass",
    "WeightedRightTransition",
    "bind_weighted_right_class",
    "exact_double_weight",
    "transport_weighted_right_binding",
]
