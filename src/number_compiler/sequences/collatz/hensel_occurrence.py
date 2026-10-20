"""Live Collatz Hensel occurrences over an exact canonical radix-4 suffix.

An occurrence represents the odd value

    ``x = 2**a * 3**h * M + b``

with ``a`` in ``{1, 2}``.  The action contains only the bounded affine
coefficients; the canonical suffix and logical time belong to the occurrence.
The one-step Hensel/root algorithm remains owned by
``CollatzAffineSuffixGerm.next_step``.  This layer preserves the raw multiplier
metadata when the canonical suffix is empty, where the older germ intentionally
collapses an irrelevant multiplier to zero.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.automata.program_word import (
    EMPTY,
    SourceWord,
    from_runs,
    from_values,
    iter_runs,
    source_word_key,
    source_word_symbol_bounds,
    validate_source_word,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.exact_tree_context import (
    require_endpoint_construction,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.sequences.collatz.frame import (
    CollatzAffineSuffixAdvance,
    CollatzAffineSuffixGerm,
    normalize_collatz_frame_word,
)
from number_compiler.sequences.collatz.root_germs import (
    PadicAngularBoundaryGerm,
    RationalPadicRootGerm,
    RationalPadicRootMismatch,
)


def _word_value(word: SourceWord) -> int:
    require_endpoint_construction()
    if 2 * word.length > 16384:
        raise BlockContextBudgetExceeded("Hensel endpoint export exceeds bit budget")
    value = 0
    place = 1
    for digit, count in iter_runs(word):
        if count:
            value += digit * (4**count - 1) // 3 * place
            place *= 4**count
    return value


def _append_run(runs: list[tuple[int, int]], digit: int, count: int) -> None:
    if count <= 0:
        return
    if runs and runs[-1][0] == digit:
        previous, length = runs[-1]
        runs[-1] = previous, length + count
    else:
        runs.append((digit, count))


def _affine_radix4_suffix(
    suffix: SourceWord,
    scale: int,
    addend: int,
) -> SourceWord:
    """Return ``scale*M+addend`` by counted radix-four carry propagation."""
    validate_source_word(suffix)
    if type(scale) is not int or scale not in (1, 2):
        raise ValueError("affine suffix scale must be one or two")
    if type(addend) is not int or addend < 0:
        raise ValueError("affine suffix addend must be nonnegative")
    output: list[tuple[int, int]] = []
    carry = addend
    for digit, run_length in iter_runs(suffix):
        remaining = run_length
        while remaining:
            total = scale * digit + carry
            emitted, following = total & 3, total >> 2
            _append_run(output, emitted, 1)
            remaining -= 1
            carry = following
            if not remaining:
                break
            repeated = scale * digit + carry
            repeated_digit, repeated_carry = repeated & 3, repeated >> 2
            if repeated_carry == carry:
                _append_run(output, repeated_digit, remaining)
                remaining = 0
            # Otherwise the next iteration advances the bounded carry state.
    while carry:
        _append_run(output, carry & 3, 1)
        carry >>= 2
    return EMPTY if not output else from_runs(output)


@dataclass(frozen=True, slots=True)
class CollatzHenselAction:
    """The bounded affine action, independent of suffix and logical time."""

    a: int
    h: int
    b: int

    def __post_init__(self) -> None:
        if any(type(value) is not int for value in (self.a, self.h, self.b)):
            raise TypeError("Hensel action fields require exact integers")
        if self.a not in (1, 2):
            raise ValueError("Hensel action exponent a must be one or two")
        if not 0 <= self.h <= 40:
            raise ValueError("Hensel action exponent h must fit one 64-bit limb")
        if self.b <= 0 or not (self.b & 1):
            raise ValueError("Hensel action offset must be a positive odd integer")
        if self.b.bit_length() > 128:
            raise ValueError("Hensel action offset exceeds two bounded limbs")

    @property
    def multiplier(self) -> int:
        return int((1 << self.a) * (3**self.h))

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-hensel-action", self.a, self.h, self.b)


@dataclass(frozen=True, slots=True)
class CollatzHenselOccurrence:
    """One exact suffix occurrence of a bounded Hensel action."""

    action: CollatzHenselAction
    suffix: SourceWord
    logical_steps: int = 0

    @classmethod
    def from_components(
        cls,
        a: int,
        h: int,
        suffix: SourceWord,
        b: int,
        logical_steps: int = 0,
    ) -> CollatzHenselOccurrence:
        return cls(CollatzHenselAction(a, h, b), suffix, logical_steps)

    def __post_init__(self) -> None:
        if type(self.action) is not CollatzHenselAction:
            raise TypeError("Hensel occurrence requires its action type")
        bounds = source_word_symbol_bounds(self.suffix)
        if bounds is not None and not 0 <= bounds[0] <= bounds[1] < 4:
            raise ValueError("Hensel suffix must use radix-four symbols")
        if type(self.logical_steps) is not int or self.logical_steps < 0:
            raise ValueError("Hensel occurrence time must be a nonnegative integer")

    @property
    def multiplier(self) -> int:
        return self.action.multiplier

    @property
    def a(self) -> int:
        return self.action.a

    @property
    def h(self) -> int:
        return self.action.h

    @property
    def b(self) -> int:
        return self.action.b

    @property
    def M(self) -> SourceWord:
        """Compatibility spelling for the retained canonical suffix."""
        return self.suffix

    @property
    def suffix_value(self) -> int:
        return _word_value(self.suffix)

    @property
    def value(self) -> int:
        return self.multiplier * self.suffix_value + self.action.b

    @property
    def algebraic_key(self) -> tuple[object, ...]:
        """Exact action/suffix identity with logical time removed."""
        return (
            "collatz-hensel-algebraic-occurrence",
            self.action.canonical_key,
            source_word_key(self.suffix),
            self.suffix.length,
        )

    @property
    def occurrence_key(self) -> tuple[object, ...]:
        return (*self.algebraic_key, self.logical_steps)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return self.occurrence_key


def canonicalize_hensel_occurrence(
    occurrence: CollatzHenselOccurrence,
) -> CollatzHenselOccurrence:
    """Rebase an exact occurrence to coefficient ``2*3**h``.

    The removed dyadic factor and offset quotient are absorbed into the
    existing suffix occurrence. Logical time remains an external coordinate.
    """
    if type(occurrence) is not CollatzHenselOccurrence:
        raise TypeError("Hensel normalization requires an exact occurrence")
    coefficient = 2 * int(3**occurrence.h)
    quotient, offset = divmod(occurrence.b, coefficient)
    if occurrence.a == 1 and quotient == 0:
        return occurrence
    suffix = _affine_radix4_suffix(
        occurrence.suffix,
        1 << (occurrence.a - 1),
        quotient,
    )
    return CollatzHenselOccurrence(
        CollatzHenselAction(1, occurrence.h, offset),
        suffix,
        occurrence.logical_steps,
    )


@dataclass(frozen=True, slots=True)
class CollatzHenselStep:
    """One exact accelerated image and its valuation/root certificate."""

    valuation: int
    target: CollatzHenselOccurrence
    fixed_v2: int
    root: RationalPadicRootGerm | None
    mismatch: RationalPadicRootMismatch | None

    def __post_init__(self) -> None:
        if type(self.valuation) is not int or self.valuation <= 0:
            raise ValueError("Hensel valuation must be positive")
        if type(self.fixed_v2) is not int or not 0 <= self.fixed_v2 <= self.valuation:
            raise ValueError("Hensel fixed valuation is outside the step")
        if (self.root is None) != (self.mismatch is None):
            raise ValueError("Hensel root and mismatch must be paired")

    @property
    def image(self) -> CollatzHenselOccurrence:
        return self.target


def _suffix_to_germ(occurrence: CollatzHenselOccurrence) -> CollatzAffineSuffixGerm:
    """Bind the occurrence to the existing canonical next-step owner."""
    suffix = occurrence.suffix
    # Preserve the action metadata at M=0 while giving the root matcher an
    # explicit canonical zero cell. This keeps the empty source on the same
    # Hensel path as every other finite suffix.
    if suffix.length == 0:
        suffix = from_values((0,))
    return CollatzAffineSuffixGerm(
        occurrence.multiplier,
        occurrence.action.b,
        suffix,
        occurrence.logical_steps,
    )


def _raw_target_multiplier(
    occurrence: CollatzHenselOccurrence,
    advance: CollatzAffineSuffixAdvance,
) -> int:
    """Recover the action multiplier before empty-target canonical collapse."""
    root = advance.root
    mismatch = advance.mismatch
    if root is not None and mismatch is not None:
        return PadicAngularBoundaryGerm.from_mismatch(root, mismatch).multiplier
    fixed_v2 = advance.fixed_v2
    return (occurrence.multiplier * 3) >> fixed_v2


def _action_from_multiplier(
    occurrence: CollatzHenselOccurrence,
    multiplier: int,
    offset: int,
) -> CollatzHenselAction:
    h = occurrence.action.h + 1
    if h > 40:
        raise ValueError("Hensel action exponent h exceeds the 40-step bound")
    for a in (1, 2):
        if multiplier == (1 << a) * (3**h):
            return CollatzHenselAction(a, h, offset)
    raise AssertionError((occurrence, multiplier, offset, h))


def advance_hensel_occurrence(occurrence: CollatzHenselOccurrence) -> CollatzHenselStep:
    """Compute one accelerated image through the shared frame/root machinery."""
    if type(occurrence) is not CollatzHenselOccurrence:
        raise TypeError("Hensel next step requires a Hensel occurrence")
    require_endpoint_construction()
    if occurrence.h >= 40:
        raise ValueError("Hensel action exponent h exceeds the 40-step bound")
    germ = _suffix_to_germ(occurrence)
    advance = germ.next_step()
    raw_multiplier = _raw_target_multiplier(occurrence, advance)
    target_action = _action_from_multiplier(
        occurrence,
        raw_multiplier,
        advance.target.offset,
    )
    target = canonicalize_hensel_occurrence(
        CollatzHenselOccurrence(
            target_action,
            advance.target.suffix,
            occurrence.logical_steps + 1,
        )
    )
    return CollatzHenselStep(
        advance.valuation,
        target,
        advance.fixed_v2,
        advance.root,
        advance.mismatch,
    )


class CollatzHenselOccurrenceCarrier:
    """Intern exact occurrences while sharing action identities."""

    __slots__ = ("_actions", "_occurrences", "hits", "requests")

    def __init__(self) -> None:
        require_endpoint_construction()
        self._actions: dict[tuple[object, ...], CollatzHenselAction] = {}
        self._occurrences: dict[tuple[object, ...], CollatzHenselOccurrence] = {}
        self.requests = 0
        self.hits = 0

    @property
    def occurrence_count(self) -> int:
        """Return the number of exact occurrences currently interned."""
        return len(self._occurrences)

    def intern(
        self,
        action: CollatzHenselAction,
        suffix: SourceWord,
        logical_steps: int = 0,
    ) -> CollatzHenselOccurrence:
        require_endpoint_construction()
        if type(action) is not CollatzHenselAction:
            raise TypeError("Hensel carrier requires a Hensel action")
        normalized = canonicalize_hensel_occurrence(
            CollatzHenselOccurrence(action, suffix, logical_steps)
        )
        action, suffix = normalized.action, normalized.suffix
        action_key = action.canonical_key
        shared_action = self._actions.get(action_key, action)
        occurrence = CollatzHenselOccurrence(
            shared_action, suffix, normalized.logical_steps
        )
        self.requests += 1
        key = occurrence.occurrence_key
        found = self._occurrences.get(key)
        if found is not None:
            self.hits += 1
            return found
        if len(self._occurrences) >= 4096:
            raise BlockContextBudgetExceeded(
                "Hensel occurrence interner budget exceeded"
            )
        self._actions[action_key] = shared_action
        self._occurrences[key] = occurrence
        return occurrence

    def from_value(self, value: int) -> CollatzHenselOccurrence:
        if type(value) is not int:
            raise TypeError("Hensel source value requires an exact integer")
        if value <= 0 or not (value & 1):
            raise ValueError("Hensel source value must be positive and odd")
        # The canonical source section uses b=1; all remaining source value is
        # represented by the exact radix-4 suffix M=(value-1)/2.
        if value.bit_length() > 16384:
            raise BlockContextBudgetExceeded("Hensel source import exceeds bit budget")
        m = (value - 1) // 2
        suffix = EMPTY if m == 0 else from_values(digits_lsd(m, 4))
        return self.intern(CollatzHenselAction(1, 0, 1), suffix)

    def from_germ(self, germ: CollatzAffineSuffixGerm) -> CollatzHenselOccurrence:
        if type(germ) is not CollatzAffineSuffixGerm:
            raise TypeError("Hensel re-imaging requires an affine suffix germ")
        if germ.multiplier == 0:
            return self.intern(
                CollatzHenselAction(1, 0, germ.offset),
                germ.suffix,
                germ.logical_steps,
            )
        a = v2_positive(germ.multiplier)
        if a not in (1, 2):
            raise ValueError("affine germ multiplier is outside the Hensel a/h form")
        odd = germ.multiplier >> a
        h = 0 if odd == 1 else CollatzAffineSuffixGerm.pow3_exponent(odd)
        return self.intern(
            CollatzHenselAction(a, h, germ.offset), germ.suffix, germ.logical_steps
        )

    def next_step(self, occurrence: CollatzHenselOccurrence) -> CollatzHenselStep:
        step = advance_hensel_occurrence(occurrence)
        target = self.intern(
            step.target.action,
            step.target.suffix,
            step.target.logical_steps,
        )
        return CollatzHenselStep(
            step.valuation,
            target,
            step.fixed_v2,
            step.root,
            step.mismatch,
        )

    def image_second(
        self,
        source: int | SourceWord,
        *,
        logical_steps: int = 0,
    ) -> CollatzHenselOccurrence:
        return hensel_second_image(source, carrier=self, logical_steps=logical_steps)

    def reimage(
        self,
        action: CollatzHenselAction,
        suffix: SourceWord,
        logical_steps: int = 0,
    ) -> CollatzHenselOccurrence:
        return self.intern(action, suffix, logical_steps)


def hensel_second_image(
    source: int | SourceWord,
    *,
    carrier: CollatzHenselOccurrenceCarrier | None = None,
    logical_steps: int = 0,
) -> CollatzHenselOccurrence:
    """Return the direct two-accelerated-step image of an odd source.

    The first normalized radix-4 frame is stripped symbolically.  The second
    valuation is then the first mismatch against
    ``- (3 + 2**e) / 9`` on that normalized suffix, so no first successor word
    is built.  ``logical_steps`` is an occurrence coordinate and defaults to
    the two events represented by this image.
    """
    if type(logical_steps) is not int or logical_steps < 0:
        raise ValueError("image time must be a nonnegative integer")
    if carrier is None:
        carrier = CollatzHenselOccurrenceCarrier()
    if type(carrier) is not CollatzHenselOccurrenceCarrier:
        raise TypeError("image carrier has another type")

    require_endpoint_construction()
    word: SourceWord
    if type(source) is int:
        if source <= 0 or not source & 1:
            raise ValueError("image source must be positive and odd")
        if source.bit_length() > 16384:
            raise BlockContextBudgetExceeded("Hensel source import exceeds bit budget")
        word = from_values(digits_lsd(source, 4))
    elif isinstance(source, SourceWord):
        word = source
    else:
        raise TypeError("image source must be an odd integer or canonical word")
    _depth, local_shift, tail = normalize_collatz_frame_word(word)

    root = RationalPadicRootGerm(2, 3 + (1 << local_shift))
    root_word = from_values((0,)) if tail is EMPTY else tail
    mismatch, remaining = root.first_mismatch_word(root_word)
    angular = PadicAngularBoundaryGerm.from_mismatch(root, mismatch)
    action = CollatzHenselAction(2 - mismatch.digit_v2, 2, angular.offset)
    return carrier.intern(action, remaining, logical_steps + 2)


__all__ = [
    "CollatzHenselAction",
    "CollatzHenselOccurrence",
    "CollatzHenselOccurrenceCarrier",
    "CollatzHenselStep",
    "advance_hensel_occurrence",
    "canonicalize_hensel_occurrence",
    "hensel_second_image",
]
