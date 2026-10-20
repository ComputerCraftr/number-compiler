"""Authenticated finite Q19 seed-orbit morphisms with exact outer/inner ports.

Ported from 2rev10's source-root squaring *architecture*, not its local
radius-one stencil. Reverse/add advances the actual intermediate Q19 SLP
using the currently authorized T²/T⁴ pair producer. Consequently temporal
squaring is mathematically exact but does NOT yet reduce O(N/4) Q19 temporal
blocks to O(log N): a future source-closed Q19 dyadic operator is still needed.

The independent exterior fold evaluates normalized decimal digits by a
binary-carry finite transducer on the Q19 SLP, including reversed half and
possible leading carry. Neither an integer nor a guessed periodic word is
materialized for this fold.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING
from weakref import ReferenceType, ref

from number_compiler.arithmetic.automata.slp_interval import (
    fold_slp_dag,
    fold_slp_interval,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.sequences.reverse_add.pair_numeric_ports import (
    DecimalPairNumericPort,
)

from .temporal_residue99 import from_seed

if TYPE_CHECKING:
    from .power import ReverseAddPoweredTerm
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner


_ISSUER = object()


@dataclass(frozen=True, slots=True)
class _CarryModAction:
    """One MSD-oriented *value* fold over LSD-first Q19 pair coefficients.

    A(c)=(carry_out, mod99, mod198) for both incoming carries c in {0,1}.
    The generic paired carry/residue algebra is owned by
    ``DecimalPairNumericPort``; this wrapper keeps only the two modulus
    projections needed by this output consumer.
    """

    port99: DecimalPairNumericPort
    port198: DecimalPairNumericPort

    @property
    def length(self) -> int:
        return self.port99.length

    @property
    def carry(self) -> tuple[int, int]:
        return self.port99.outgoing

    @property
    def mod99(self) -> tuple[int, int]:
        return self.port99.forward

    @property
    def mod198(self) -> tuple[int, int]:
        return self.port198.forward

    @classmethod
    def identity(cls) -> _CarryModAction:
        return cls(
            DecimalPairNumericPort.identity(99),
            DecimalPairNumericPort.identity(198),
        )

    @classmethod
    def symbol(cls, coefficient: int) -> _CarryModAction:
        if type(coefficient) is not int or not 0 <= coefficient <= 18:
            raise ValueError("invalid Q19 pair coefficient")
        return cls(
            DecimalPairNumericPort.atom(coefficient, 99),
            DecimalPairNumericPort.atom(coefficient, 198),
        )

    @classmethod
    def top_carry(cls) -> _CarryModAction:
        """A virtual final digit emitting the carry at position pair_width."""
        return cls(
            DecimalPairNumericPort.atom(0, 99),
            DecimalPairNumericPort.atom(0, 198),
        )

    def then(self, later: _CarryModAction) -> _CarryModAction:
        if type(later) is not _CarryModAction:
            raise TypeError("carry action composition requires matching types")
        return _CarryModAction(
            self.port99.then(later.port99),
            self.port198.then(later.port198),
        )

    def power(self, n: int) -> _CarryModAction:
        if type(n) is not int or n < 0:
            raise ValueError("carry action repetition must be nonnegative")
        return binary_power(
            self,
            n,
            identity=_CarryModAction.identity(),
            compose=lambda first, second: first.then(second),
        ).value


@dataclass(frozen=True, slots=True)
class _BothDirections:
    forward: _CarryModAction
    backward: _CarryModAction

    def then(self, right: _BothDirections) -> _BothDirections:
        return _BothDirections(
            self.forward.then(right.forward),
            right.backward.then(self.backward),
        )

    def power(self, count: int) -> _BothDirections:
        return _BothDirections(self.forward.power(count), self.backward.power(count))


@dataclass(frozen=True, slots=True)
class Q19WordFiber:
    """Exact normalized target and its *independently folded* exterior ports."""

    occurrence: ReversePairOutputOccurrence = field(repr=False)
    generation: int
    root: int
    width: int
    pair_width: int
    center: tuple[int, ...]
    residue99: int
    residue198: int
    exterior99: int
    exterior198: int
    carry_into_center: int
    carry_out_of_center: int
    carry_out_of_pairs: int
    leading_carry_digit: int
    first_pair_sum: int
    border_pairs: int
    low_border_carry: int
    middle_carry_map: tuple[int, int]
    upper_border_ingress: int
    first_non9_from_upper: int | None

    @property
    def center_width(self) -> int:
        return len(self.center)

    def audit_binding(self) -> tuple[object, ...]:
        """Return a fresh read-only field tuple for cache integrity audits."""
        return (
            self.occurrence,
            self.generation,
            self.root,
            self.width,
            self.pair_width,
            self.center,
            self.residue99,
            self.residue198,
            self.exterior99,
            self.exterior198,
            self.carry_into_center,
            self.carry_out_of_center,
            self.carry_out_of_pairs,
            self.leading_carry_digit,
            self.first_pair_sum,
            self.border_pairs,
            self.low_border_carry,
            self.middle_carry_map,
            self.upper_border_ingress,
            self.first_non9_from_upper,
        )


def _fiber(
    owner: ReversePairQ19OutputOwner,
    seed: int,
    occurrence: ReversePairOutputOccurrence,
) -> Q19WordFiber:
    owner.validate_issued_occurrence(occurrence)
    key = (occurrence.root, occurrence.temporal_steps, seed)
    memo = owner.word_fiber_cache
    if key in memo:
        cached = memo[key]
        if (
            type(cached) is not tuple
            or len(cached) != 2
            or type(cached[0]) is not Q19WordFiber
            or cached[0].occurrence is not occurrence
            or cached[1] != cached[0].audit_binding()
        ):
            owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_WORD_FIBER_FAILED_WORK)
            raise ValueError("cached Q19 word fiber failed its source binding")
        owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_WORD_FIBER_CACHE_HITS)
        return cached[0]

    owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_WORD_FIBER_CACHE_MISSES)
    try:
        result = _compute_fiber(owner, seed, occurrence)
    except BaseException:
        owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_WORD_FIBER_FAILED_WORK)
        raise
    try:
        memo[key] = (result, result.audit_binding())
    except BlockContextBudgetExceeded:
        # The fiber is an optional observation cache. Its exact cold result is
        # still valid when the ledger cannot retain another memo entry.
        owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_WORD_FIBER_CACHE_BYPASSES)
    else:
        owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_WORD_FIBER_CACHE_PUBLICATIONS)
    return result


def _compute_fiber(
    owner: ReversePairQ19OutputOwner,
    seed: int,
    occurrence: ReversePairOutputOccurrence,
) -> Q19WordFiber:
    arena = owner.arena
    root = occurrence.root
    pair_width = occurrence.pair_width
    odd = pair_width & 1
    half = (pair_width + odd) // 2
    # Authenticated Q19 publication constructed this summary and all children.
    summary = owner.word_summary(root)
    if summary.symbols != half:
        raise AssertionError("Q19 semantic pair-half extent changed")
    z = _CarryModAction.identity()
    neutral = _BothDirections(z, z)
    with owner.ledger.reservation(
        owner.scratch_owner,
        entries=4 * (len(arena.nodes) + 1),
        nodes=8 * (len(arena.nodes) + 1),
    ):
        folds = fold_slp_dag(
            arena,
            root,
            empty_value=neutral,
            terminal_value=lambda sym: (
                _BothDirections(
                    _CarryModAction.symbol(sym), _CarryModAction.symbol(sym)
                )
                if 0 <= sym <= 18
                else neutral
            ),
            concatenate=lambda left, right: left.then(right),
            repeat=lambda value, n: value.power(n),
            on_reduce=lambda _node: owner.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_WORD_FIBER_DAG_NODES_VISITED
            ),
        )

        def half_interval(begin: int, end: int, *, backwards: bool) -> _CarryModAction:
            return fold_slp_interval(
                arena,
                root,
                begin,
                end,
                identity=z,
                length=lambda node: owner.published_word_summary(node).symbols,
                full_value=lambda node, rev: (
                    folds[node].backward if rev else folds[node].forward
                ),
                compose=lambda left, right: left.then(right),
                repeat=lambda value, n: value.power(n),
                reverse=backwards,
                on_visit=lambda: owner.ledger.bump(
                    _reverse_add_keys.REVERSE_Q19_WORD_FIBER_INTERVAL_NODES_VISITED
                ),
            )

        # Virtual top digit accounts for source-normalization carry on growth.
        width = occurrence.output_width
        grow = width - pair_width
        if grow not in (0, 1):
            raise AssertionError("Q19 normalized width has invalid growth")

        def section(a: int, b: int) -> _CarryModAction:
            if not 0 <= a <= b <= width:
                raise ValueError("Q19 pair-section outside normalized word")
            pieces: list[_CarryModAction] = []
            if a < min(b, half):
                pieces.append(half_interval(a, min(b, half), backwards=False))
            if b > half and a < pair_width:
                start = max(a, half)
                end = min(b, pair_width)
                if start < end:
                    pieces.append(
                        half_interval(
                            pair_width - end,
                            pair_width - start,
                            backwards=True,
                        )
                    )
            if grow and a <= pair_width < b:
                pieces.append(_CarryModAction.top_carry())
            result = z
            for piece in pieces:
                result = result.then(piece)
            if result.length != b - a:
                raise AssertionError("Q19 pair-section fold lost a semantic digit")
            return result

        cwidth = 1 if width & 1 else 2
        start = (width - cwidth) // 2
        low = section(0, start)
        middle = section(start, start + cwidth)
        high = section(start + cwidth, width)
        c_in = low.carry[0]
        c_out = middle.carry[c_in]
        middle_number = middle.mod198[c_in]  # <100 so modulo 198 is exact
        center = (
            (middle_number,)
            if cwidth == 1
            else (middle_number // 10, middle_number % 10)
        )
        full = low.then(middle).then(high)
        if full.length != width:
            raise AssertionError("Q19 full digit action has incorrect width")
        raw = section(0, pair_width)
        carry_out = raw.carry[0]
        # NC16's correlated lower/middle/upper carry word is represented
        # *as one exact port relation* over the issued Q19 source root.
        # This is not an independently guessed high or low carry mask.
        border_pairs = min(3, (pair_width - 1) // 2)
        lower_border = section(0, border_pairs)
        middle_border = section(border_pairs, pair_width - border_pairs)
        upper_border = section(pair_width - border_pairs, pair_width)
        low_border_carry = lower_border.carry[0]
        upper_border_ingress = middle_border.carry[low_border_carry]
        if upper_border.carry[upper_border_ingress] != carry_out:
            raise AssertionError("source Q19 bilateral carry map is inconsistent")
        mid_map = middle_border.carry
        if mid_map not in ((0, 0), (0, 1), (1, 1)):
            raise AssertionError("Q19 middle transfer is not a reset/identity map")
        # Full pair field is symmetric. Its final resetting coefficient in
        # the middle is the first non-9 seen inward from the upper tile.
        first_non9 = None
        if (
            border_pairs < half
            and owner.range_summary(root, border_pairs, half).domain != 0
        ):
            lo, hi = border_pairs, half
            while lo + 1 < hi:
                mid = (lo + hi) // 2
                if owner.range_summary(root, border_pairs, mid).domain != 0:
                    hi = mid
                else:
                    lo = mid
            first_non9 = lo if owner.pair_value_at(occurrence, lo) != 9 else hi - 1
            if owner.pair_value_at(occurrence, first_non9) == 9:
                raise AssertionError("non-9 reset position was not Q19-supported")
        if carry_out != grow or full.carry[0] != (0 if grow else carry_out):
            raise AssertionError("Q19 normalized leading carry disagrees with SLP")
        ex99 = (low.mod99[0] + pow(10, start + cwidth, 99) * high.mod99[c_out]) % 99
        ex198 = (
            low.mod198[0] + pow(10, start + cwidth, 198) * high.mod198[c_out]
        ) % 198
        digit_99 = full.mod99[0]
        digit_198 = full.mod198[0]
    # The global clock is independent of the Q19 weighted digit fold.
    prediction = from_seed(seed, occurrence.temporal_steps).target_mod99
    if digit_99 != prediction:
        raise AssertionError("Q19 digit fold disagrees with source mod-99 clock")
    center_lsd = sum(d * 10**i for i, d in enumerate(reversed(center)))
    if (ex99 + center_lsd * pow(10, start, 99)) % 99 != digit_99 or (
        ex198 + center_lsd * pow(10, start, 198)
    ) % 198 != digit_198:
        raise AssertionError("exterior/center SLP residues do not reconstruct source")
    for i, digit in enumerate(reversed(center)):
        if digit != owner.digit(occurrence, start + i):
            raise AssertionError("Q19 center carry-port disagrees with issued digit")
    return Q19WordFiber(
        occurrence,
        occurrence.temporal_steps,
        root,
        width,
        pair_width,
        center,
        digit_99,
        digit_198,
        ex99,
        ex198,
        c_in,
        c_out,
        carry_out,
        grow,
        owner.pair_value_at(occurrence, 0),
        border_pairs,
        low_border_carry,
        mid_map,
        upper_border_ingress,
        first_non9,
    )


def _advance(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
    steps: int,
) -> ReversePairOutputOccurrence:
    """Exact physical Q19 evolution; T4 is *not* mislabeled as dyadic Hashlife."""
    if type(steps) is not int or steps < 0:
        raise ValueError("Q19 physical advance steps must be nonnegative")
    owner.validate_issued_occurrence(occurrence)
    while steps >= 4:
        occurrence = owner.apply_punctured_pair_block(occurrence, steps=4)
        steps -= 4
    if steps >= 2:
        occurrence = owner.apply_punctured_pair_block(occurrence, steps=2)
        steps -= 2
    if steps:
        occurrence = owner.apply_pair_step(occurrence)
    return occurrence


@dataclass(frozen=True, slots=True, weakref_slot=True)
class CertifiedReverseAddSeedMorphism:
    """One real-source Q19 temporal action, with exact SLP-root seam.

    A `square` computes its second half from the *actual* intermediate root,
    never from a hypothetical periodic outer/inner carry driver. The class
    keeps its bounded Q19 cost explicit, rather than asserting O(log N).
    """

    _owner: ReversePairQ19OutputOwner = field(repr=False, compare=False)
    seed: int
    horizon: int
    first: Q19WordFiber
    last: Q19WordFiber
    q19_block_applications: int
    temporal_square_operations: int = 0
    physical_repeat_certified: bool = False
    logarithmic_q19_power_certified: bool = False
    terminal_occurrence_reused: bool = False
    _seal: object = field(default=None, repr=False, compare=False, init=False)
    _binding: tuple[object, ...] = field(
        default=(), repr=False, compare=False, init=False
    )
    # A self-weak-reference proves identity without retaining this packet in
    # an owner-side registry. ``copy.copy`` preserves the reference to the
    # original object, so a structurally identical clone fails validation.
    _issued_self: ReferenceType[CertifiedReverseAddSeedMorphism] | None = field(
        default=None, repr=False, compare=False, init=False
    )

    def publication_snapshot(self) -> tuple[object, ...]:
        # Flat scalar snapshot: even object.__setattr__ mutation of a nested
        # frozen fiber invalidates the outer issued record, rather than just
        # mutating the same referenced object on both sides of the comparison.
        return (
            self._owner,
            self.seed,
            self.horizon,
            self.first.audit_binding(),
            self.last.audit_binding(),
            self.q19_block_applications,
            self.temporal_square_operations,
            self.physical_repeat_certified,
            self.logarithmic_q19_power_certified,
            self.terminal_occurrence_reused,
        )

    @property
    def physical_interval(self) -> tuple[int, int]:
        self.validate()
        return self.first.generation, self.last.generation

    @property
    def duration(self) -> int:
        self.validate()
        return self.last.generation - self.first.generation

    @property
    def growth(self) -> int:
        self.validate()
        return self.last.width - self.first.width

    def validate(self) -> None:
        if self._issued_self is None or self._issued_self() is not self:
            raise ValueError("reverse/add temporal packet was not issued by this owner")
        if (
            self._seal is not _ISSUER
            or self._binding != self.publication_snapshot()
            or self.physical_repeat_certified
            or self.logarithmic_q19_power_certified
            or type(self.q19_block_applications) is not int
            or self.q19_block_applications < 0
            or type(self.temporal_square_operations) is not int
            or self.temporal_square_operations < 0
            or type(self.terminal_occurrence_reused) is not bool
            or self.first.generation < 1
            or self.last.generation <= self.first.generation
            or self.last.generation > self.horizon
        ):
            raise ValueError("reverse/add pointed temporal morphism is not certified")
        self._owner.validate_issued_occurrence(self.first.occurrence)
        self._owner.validate_issued_occurrence(self.last.occurrence)
        if (
            self.first.root != self.first.occurrence.root
            or self.last.root != self.last.occurrence.root
            or self.first.generation != self.first.occurrence.temporal_steps
            or self.last.generation != self.last.occurrence.temporal_steps
            or self.first.width != self.first.occurrence.output_width
            or self.last.width != self.last.occurrence.output_width
        ):
            raise ValueError("reverse/add pointed word root or temporal seam changed")

    def digit_at(self, lsd_index: int, *, after: bool = True) -> int:
        self.validate()
        if type(after) is not bool:
            raise TypeError("source/target selector must be Boolean")
        word = self.last if after else self.first
        if type(lsd_index) is not int or not 0 <= lsd_index < word.width:
            raise IndexError(lsd_index)
        return self._owner.digit(word.occurrence, lsd_index)

    def then(
        self,
        later: CertifiedReverseAddSeedMorphism,
    ) -> CertifiedReverseAddSeedMorphism:
        self.validate()
        later.validate()
        if (
            self._owner is not later._owner
            or self.seed != later.seed
            or self.horizon != later.horizon
            or self.last.occurrence is not later.first.occurrence
            or self.last != later.first
        ):
            raise ValueError("reverse/add temporal composition lacks exact root seam")
        return _issue(
            self._owner,
            self.seed,
            self.horizon,
            self.first,
            later.last,
            self.q19_block_applications + later.q19_block_applications,
            squares=self.temporal_square_operations + later.temporal_square_operations,
            terminal_occurrence_reused=(
                self.terminal_occurrence_reused or later.terminal_occurrence_reused
            ),
        )

    def square(self) -> CertifiedReverseAddSeedMorphism:
        self.validate()
        next_target = self.last.generation + self.duration
        if next_target > self.horizon:
            raise ValueError("temporal square exceeds the certified source horizon")
        target = _advance(self._owner, self.last.occurrence, self.duration)
        last = _fiber(self._owner, self.seed, target)
        second = _issue(
            self._owner,
            self.seed,
            self.horizon,
            self.last,
            last,
            _bounded_blocks(self.duration),
        )
        joined = self.then(second)
        return _issue(
            self._owner,
            self.seed,
            self.horizon,
            joined.first,
            joined.last,
            joined.q19_block_applications,
            squares=self.temporal_square_operations + 1,
            terminal_occurrence_reused=joined.terminal_occurrence_reused,
        )

    def extend(self, steps: int) -> CertifiedReverseAddSeedMorphism:
        """Append a genuine physical suffix from this actual terminal root."""
        self.validate()
        if type(steps) is not int or steps < 1:
            raise ValueError("physical suffix duration must be positive")
        if self.last.generation + steps > self.horizon:
            raise ValueError("Q19 source-root suffix exceeds original horizon")
        target = _advance(self._owner, self.last.occurrence, steps)
        last = _fiber(self._owner, self.seed, target)
        return self.then(
            _issue(
                self._owner,
                self.seed,
                self.horizon,
                self.last,
                last,
                _bounded_blocks(steps),
            )
        )


def _bounded_blocks(steps: int) -> int:
    return steps // 4 + (1 if steps % 4 >= 2 else 0) + steps % 2


def _issue(
    owner: ReversePairQ19OutputOwner,
    seed: int,
    horizon: int,
    first: Q19WordFiber,
    last: Q19WordFiber,
    applications: int,
    *,
    squares: int = 0,
    terminal_occurrence_reused: bool = False,
) -> CertifiedReverseAddSeedMorphism:
    record = CertifiedReverseAddSeedMorphism(
        owner,
        seed,
        horizon,
        first,
        last,
        applications,
        squares,
        terminal_occurrence_reused=terminal_occurrence_reused,
    )
    object.__setattr__(record, "_seal", _ISSUER)
    object.__setattr__(record, "_binding", record.publication_snapshot())
    object.__setattr__(record, "_issued_self", ref(record))
    record.validate()
    return record


def certified_reverse_add_seed_morphism(
    term: ReverseAddPoweredTerm,
    steps: int,
    *,
    start: int = 1,
) -> CertifiedReverseAddSeedMorphism:
    """Issue finite pointed Q19 action from the original source workspace."""
    term.validate_source_binding()
    if term.base != 10:
        raise ValueError(
            "reverse/add pointed temporal power needs a valid decimal term"
        )
    if (
        type(start) is not int
        or start < 1
        or type(steps) is not int
        or steps < 1
        or start + steps > term.generation
    ):
        raise ValueError("reverse/add temporal interval outside source horizon")
    workspace = term.source_workspace()
    owner = workspace.adapter.q19_output_owner(
        workspace.actions.source(workspace.source)
    )
    # An owner can be initialized before any scheduler image publication.
    # Refresh the workspace's source-payload contract so the new Q19 owner
    # remains an explicit authenticated dependency through the public API.
    workspace.register_source_payload_audit_contract()
    first_occurrence = _advance(owner, owner.initial, start - 1)
    first = _fiber(owner, term.seed, first_occurrence)
    final_occurrence = _advance(owner, first_occurrence, steps)
    last = _fiber(owner, term.seed, final_occurrence)
    return _issue(
        owner, term.seed, term.generation, first, last, _bounded_blocks(steps)
    )


def certified_completed_reverse_add_seed_morphism(
    term: ReverseAddPoweredTerm,
) -> CertifiedReverseAddSeedMorphism:
    """Observe the scheduler's exact terminal Q19 occurrence without replay.

    This is the CLI path: it shares the same completed image demanded by
    value, width, point, and stream consumers.  The packet's block count is
    the measured number of new Q19 temporal blocks this demand caused; a warm
    endpoint therefore reports zero and marks the published occurrence reuse.
    """
    term.validate_source_binding()
    if term.base != 10:
        raise ValueError("reverse/add endpoint observation needs a valid decimal term")
    if term.generation < 2:
        raise ValueError("reverse/add endpoint observation needs at least two terms")
    workspace = term.source_workspace()
    owner, last_occurrence, reused, applications = workspace.completed_q19_occurrence()
    first_occurrence = owner.initial
    owner.validate_issued_occurrence(first_occurrence)
    if (
        first_occurrence.temporal_steps != 1
        or last_occurrence.temporal_steps != term.generation
    ):
        raise ValueError("scheduler Q19 endpoint does not match the term interval")
    first = _fiber(owner, term.seed, first_occurrence)
    last = _fiber(owner, term.seed, last_occurrence)
    return _issue(
        owner,
        term.seed,
        term.generation,
        first,
        last,
        applications,
        terminal_occurrence_reused=reused,
    )


__all__ = [
    "CertifiedReverseAddSeedMorphism",
    "Q19WordFiber",
    "certified_completed_reverse_add_seed_morphism",
    "certified_reverse_add_seed_morphism",
]
