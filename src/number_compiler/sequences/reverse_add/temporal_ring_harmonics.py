"""NC16 source-issued reverse/add *open* temporal ring and bank harmonics.

Unlike `2rev10`, decimal reverse/add uses the RESET0/ID/RESET1 pair carry
monoid and shifts the mirrored Q19 pairing on growth. This module composes the
actual two-sided border ports with *all* active inward positions under one
finite source certificate. It never uses `2rev10` periods as input data.

The emitted phase/mask programs are exact or conservative must/may domains
for the authenticated *finite* horizon. Equal finite observations, even when
cyclic, do not authorize an unbounded source-to-source temporal REPEAT.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.carry.carry_monoid import apply_carry_fn
from number_compiler.arithmetic.functions.partial_count_action import ActionUniverse
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

from ._q19_issuance import issue_q19_record
from .macro_conditioned_harmonics import (
    CycleHarmonicAction,
    MacroPhaseInwardOrbit,
    _inward_orbit_at,
)
from .temporal_inward_constraints import ReverseInwardConstraints

if TYPE_CHECKING:
    from number_compiler.arithmetic.carry.carry_monoid import CarryFn

    from .border_carry_safety import BilateralCyclePort
    from .conditional_pair_ring import ConditionalRingPairAction
    from .diagonal_growth_bank import CertifiedDiagonalComparison, WidthGrowthBounds
    from .q19_border_control import CertifiedBorderGrowth
    from .q19_controlled_gt_bank import SourceGuardedGTBankAction
    from .symmetric_carry_filter import InwardCarryFilter

_ISSUER = object()
_BANKS = ("lt_low", "lt_high", "eq", "gt_low", "gt_high")
_RING_CHANNELS = (
    *_BANKS,
    "f5",
    "low_carry",
    "reflected_carry",
    "raw_borrow",
    "carry_xor",
    "carry_borrow_xor",
    "low_birth",
    "low_death",
    "high_birth",
    "high_death",
)


class ReverseTemporalRingRefused(ValueError):
    """A well-formed ring demand lies outside the admitted finite source window."""


def _scalar_harmonics(
    values: tuple[int | None, ...],
) -> tuple[int, int, int, int] | None:
    """F5 phase polynomial at nonzero arguments, only for forced lanes."""
    if any(v is None for v in values):
        return None
    forced = cast(tuple[int, ...], values)
    modes = tuple(
        sum(bit * pow(z, j, 5) for j, bit in enumerate(forced)) % 5
        for z in (1, 2, 3, 4)
    )
    return modes[0], modes[1], modes[2], modes[3]


def _finite_period(values: tuple[int | None, ...]) -> int | None:
    """Observed finite output period, requiring two whole copies."""
    if any(v is None for v in values):
        return None
    n = len(values)
    return next(
        (
            p
            for p in range(1, n // 2 + 1)
            if n % p == 0 and all(values[i] == values[i % p] for i in range(n))
        ),
        None,
    )


@dataclass(frozen=True, slots=True)
class RingPhaseHarmonic:
    """Finite bank output, with unknown bits distinct from zero."""

    position: int
    channel: str
    lanes: tuple[int | None, ...]
    f5_modes: tuple[int, int, int, int] | None
    candidate_period: int | None
    future_period_certified: bool = False

    @property
    def forced_count(self) -> int:
        return sum(x is not None for x in self.lanes)


@dataclass(frozen=True, slots=True)
class ReverseAddTemporalRingBank:
    """Authenticated finite source/border time window and inward orbit ports."""

    certificate: CertifiedBorderGrowth
    start: int
    duration: int
    positions: tuple[int, ...]
    widths: tuple[int, ...]
    output_orbits: tuple[MacroPhaseInwardOrbit, ...]
    # The target coefficient domain is the action's actual source-to-source
    # seam, not just a repeated outer cycle label or a scalar width.
    phase_pair_domains: tuple[tuple[tuple[int, ...], ...], ...]
    bank_words: tuple[RingPhaseHarmonic, ...]
    finite_moore_classes: tuple[int, ...]
    macro: CycleHarmonicAction | None
    rounds: int
    complete_integer_certified: bool = False
    temporal_repeat_certified: bool = False
    _seal: object = field(default=None, repr=False, compare=False)
    _binding: tuple[object, ...] = field(default=(), repr=False, compare=False)
    _registry_key: int = field(default=-1, repr=False, compare=False)

    def __post_init__(self) -> None:
        if (
            self._seal is not _ISSUER
            or self.complete_integer_certified
            or self.temporal_repeat_certified
            or self._binding != self._snapshot()
        ):
            raise ValueError("ring bank must be issued by a live border certificate")
        self._check()

    def _snapshot(self) -> tuple[object, ...]:
        return (
            self.certificate,
            self.certificate.owner,
            self.certificate.source,
            self.certificate._binding,
            self.start,
            self.duration,
            self.positions,
            self.widths,
            self.output_orbits,
            self.phase_pair_domains,
            self.bank_words,
            self.finite_moore_classes,
            self.macro,
            self.rounds,
            self.complete_integer_certified,
            self.temporal_repeat_certified,
            self._registry_key,
        )

    def _check(self) -> None:
        if (
            self._seal is not _ISSUER
            or self._binding != self._snapshot()
            or self.complete_integer_certified
            or self.temporal_repeat_certified
        ):
            raise ValueError("source-bound temporal ring bank was altered")
        self.certificate.validate(self.certificate.owner, self.certificate.source)
        self.certificate.owner._issuance_registry.validate_temporal_ring_bank(self)
        if (
            type(self.start) is not int
            or self.start < 0
            or type(self.duration) is not int
            or not 1 <= self.duration <= 128
            or type(self.positions) is not tuple
            or not self.positions
            or len(self.positions) > 64
            or any(type(pos) is not int or pos < 0 for pos in self.positions)
            or len(set(self.positions)) != len(self.positions)
            or type(self.widths) is not tuple
            or any(type(width) is not int or width < 1 for width in self.widths)
            or len(self.widths) != self.duration + 1
            or type(self.output_orbits) is not tuple
            or len(self.output_orbits) != len(self.positions)
            or type(self.phase_pair_domains) is not tuple
            or len(self.phase_pair_domains) != len(self.positions)
            or type(self.bank_words) is not tuple
            or type(self.finite_moore_classes) is not tuple
            or len(self.finite_moore_classes) != self.duration + 1
            or any(
                type(value) is not int or value < 0
                for value in self.finite_moore_classes
            )
            or any(len(row) != self.duration + 1 for row in self.phase_pair_domains)
        ):
            raise ValueError("invalid source-bound temporal ring")
        for position, orbit, domains in zip(
            self.positions, self.output_orbits, self.phase_pair_domains, strict=True
        ):
            if (
                orbit.position != position
                or len(domains) != self.duration + 1
                or any(
                    type(domain) is not tuple
                    or not domain
                    or any(
                        type(value) is not int or not 0 <= value <= 18
                        for value in domain
                    )
                    or tuple(sorted(set(domain))) != domain
                    for domain in domains
                )
            ):
                raise ValueError("temporal ring contains an invalid Q19 port domain")
        expected_words = tuple(
            (position, channel)
            for position in self.positions
            for channel in _RING_CHANNELS
        )
        if len(self.bank_words) != len(expected_words):
            raise ValueError("temporal ring output channel count changed")
        for word, (position, channel) in zip(
            self.bank_words, expected_words, strict=True
        ):
            if (
                type(word.position) is not int
                or word.position != position
                or type(word.channel) is not str
                or word.channel != channel
                or type(word.lanes) is not tuple
                or len(word.lanes) != self.duration
                or any(
                    value is not None
                    and (
                        type(value) is not int
                        or (
                            not 0 <= value < 5
                            if channel == "f5"
                            else value not in (0, 1)
                        )
                    )
                    for value in word.lanes
                )
                or word.future_period_certified
                or (
                    word.candidate_period is not None
                    and (
                        type(word.candidate_period) is not int
                        or not 1 <= word.candidate_period <= self.duration
                    )
                )
                or (
                    word.f5_modes is not None
                    and (
                        type(word.f5_modes) is not tuple
                        or len(word.f5_modes) != 4
                        or any(
                            type(value) is not int or not 0 <= value < 5
                            for value in word.f5_modes
                        )
                    )
                )
            ):
                raise ValueError("temporal ring contains an invalid output lane")
        for orbit in self.output_orbits:
            if type(orbit.position) is not int or any(
                type(getattr(orbit, name)) is not tuple
                or len(getattr(orbit, name)) != self.duration
                for name in (
                    "pair_f5",
                    "low_carries",
                    "reflected_carries",
                    "reflected_xor",
                    "raw_innovation_borrow",
                    "carry_borrow_xor",
                    "low_birth",
                    "low_death",
                    "reflected_birth",
                    "reflected_death",
                    "selected_bands",
                )
            ):
                raise ValueError("temporal ring contains an invalid inward orbit")
        if type(self.rounds) is not int or self.rounds < 0:
            raise ValueError("temporal ring has an invalid constraint work count")

    def source_pair_domain(self, position: int) -> tuple[int, ...]:
        """Authenticated finite action's entry Q19 coefficient domain."""
        self._check()
        return self.phase_pair_domains[self.positions.index(position)][0]

    def target_pair_domain(self, position: int) -> tuple[int, ...]:
        """Authenticated finite action's output Q19 coefficient domain."""
        self._check()
        return self.phase_pair_domains[self.positions.index(position)][-1]

    def validated_pair_domains(
        self,
    ) -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
        """Read all source/target domains after one complete authority check."""
        self._check()
        return tuple((row[0], row[-1]) for row in self.phase_pair_domains)

    def orbit(self, position: int) -> MacroPhaseInwardOrbit:
        self._check()
        return self.output_orbits[self.positions.index(position)]

    def harmonic(self, position: int, channel: str) -> RingPhaseHarmonic:
        self._check()
        return next(
            frame
            for frame in self.bank_words
            if frame.position == position and frame.channel == channel
        )

    def then(self, later: ReverseAddTemporalRingBank) -> ReverseAddTemporalRingBank:
        """Compose adjacent *already source-issued* finite phase programs.

        Unlike formal repetition, this requires a real matching physical
        width/source seam and preserves the exact conditional bit domains.
        """
        self._check()
        later._check()
        if (
            self.certificate is not later.certificate
            or self.start + self.duration != later.start
            or self.widths[-1] != later.widths[0]
            or self.positions != later.positions
        ):
            raise ValueError("ring programs require the same issued temporal seam")
        for pos in self.positions:
            if self.target_pair_domain(pos) != later.source_pair_domain(pos):
                raise ValueError("conditional Q19 source/target port seam mismatch")
        ledger = self.certificate.owner.ledger
        names = (
            "pair_f5",
            "low_carries",
            "reflected_carries",
            "reflected_xor",
            "raw_innovation_borrow",
            "carry_borrow_xor",
            "low_birth",
            "low_death",
            "reflected_birth",
            "reflected_death",
            "selected_bands",
        )
        orbits = tuple(
            MacroPhaseInwardOrbit(
                position,
                *(getattr(left, name) + getattr(right, name) for name in names),
            )
            for position, left, right in zip(
                self.positions, self.output_orbits, later.output_orbits, strict=True
            )
        )
        words = []
        for left in self.bank_words:
            right = later.harmonic(left.position, left.channel)
            ledger.bump(
                _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS,
                len(left.lanes) + len(right.lanes),
            )
            lanes = left.lanes + right.lanes
            words.append(
                RingPhaseHarmonic(
                    left.position,
                    left.channel,
                    lanes,
                    _scalar_harmonics(lanes),
                    _finite_period(lanes),
                )
            )
        result = tuple(words)
        pairs = tuple(
            a + b[1:]
            for a, b in zip(
                self.phase_pair_domains, later.phase_pair_domains, strict=True
            )
        )
        macro = None
        try:
            from .macro_conditioned_harmonics import authorize_finite_macro_window

            macro = authorize_finite_macro_window(
                self.certificate,
                start=self.start,
                duration=self.duration + later.duration,
            ).action
        except ValueError:
            pass  # Matching width does not prove an outer border return.
        return _issue_temporal_ring_bank(
            self.certificate,
            start=self.start,
            duration=self.duration + later.duration,
            positions=self.positions,
            widths=self.widths + later.widths[1:],
            output_orbits=orbits,
            phase_pair_domains=pairs,
            bank_words=result,
            finite_moore_classes=_finite_future_classes(
                result,
                self.duration + later.duration,
                on_lane_visit=lambda: ledger.bump(
                    _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS
                ),
            ),
            macro=macro,
            rounds=max(self.rounds, later.rounds),
        )

    def spatial_walsh64_mod5(
        self,
        channel: str,
        *,
        tick: int = 0,
        start_position: int = 0,
    ) -> tuple[int, ...]:
        """Exact Walsh64/F5 of 64 forced *spatial* Boolean bank lanes.

        A temporal F5 Fourier mode is a different object. This projection
        refuses a window with unknown lanes or missing active positions.
        """
        if channel not in (
            *_BANKS,
            "carry_xor",
            "carry_borrow_xor",
            "low_birth",
            "low_death",
            "high_birth",
            "high_death",
        ):
            raise ValueError("Walsh64 requires a Boolean bank channel")
        if type(tick) is not int or not 0 <= tick < self.duration:
            raise ValueError("Walsh tick outside certified time window")
        self._check()
        bits = []
        for pos in range(start_position, start_position + 64):
            lane = self.harmonic(pos, channel).lanes[tick]
            if lane not in (0, 1):
                raise ValueError("Walsh64 includes an unresolved bank lane")
            bits.append(lane)
        from number_compiler.arithmetic.fields.walsh import walsh64_mod5

        return walsh64_mod5(sum(bit << i for i, bit in enumerate(bits)))

    def conditional_input_action(self, position: int) -> ConditionalRingPairAction:
        """Compose this ring's *forced* physical carry/F5 inlet word.

        Refuses on the first unknown reflected carry or growth-adjacent pair.
        The result is an input-driven 19-state partial action with a five-band
        output writer. Formal squaring is not a physical repeat certificate.
        """
        self._check()
        from .conditional_pair_ring import (
            ConditionalRingPairAction,
            RingPairLetter,
        )

        orbit = self.orbit(position)
        source = self.phase_pair_domains[self.positions.index(position)]
        prefix = (
            self.phase_pair_domains[self.positions.index(position - 1)]
            if position > 0 and position - 1 in self.positions
            else None
        )
        action_owner = ActionUniverse(19, 6)
        action = ConditionalRingPairAction.identity(action_owner)
        for t in range(self.duration):
            a, b = orbit.low_carries[t], orbit.reflected_carries[t]
            growth = self.certificate.growth_word[self.start + t]
            if len(a) != 1 or len(b) != 1:
                raise ValueError("ring has unresolved inward carry inlet")
            prev = None
            if growth and position:
                if prefix is None or len(prefix[t]) != 1:
                    raise ValueError("growth ring requires a forced adjacent pair")
                prev = prefix[t][0]
            letter = RingPairLetter(position, growth, prev, a[0], b[0])
            # A source-conditioned letter must be supported by *some*
            # actual source/target pair along this certified finite seam.
            if not any(letter.successor(q) in source[t + 1] for q in source[t]):
                raise ValueError("ring inlet contradicts its Q19 successor")
            action = action.then(ConditionalRingPairAction.letter(letter, action_owner))
        if not any(action.targets[q] in source[-1] for q in source[0]):
            raise ValueError("composed ring inlet contradicts target Q19 seam")
        return action

    def formal_repeated_output(
        self,
        position: int,
        channel: str,
        repetitions: int,
    ) -> tuple[tuple[int | None, ...], int]:
        """Compressed *conditional* output word: (period, repeat count).

        This operation has no physical-source authority for times beyond
        this certificate. It can be used for algebraic/mask comparisons only.
        """
        self._check()
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("repeat count must be nonnegative")
        return self.harmonic(position, channel).lanes, repetitions

    def directed_growth_diagonal(
        self,
        other_start: int,
        *,
        window: int = 9,
        continuation: int = 0,
    ) -> CertifiedDiagonalComparison:
        """Compare this ring's growth window to another same-source window."""
        self._check()
        from .diagonal_growth_bank import certify_diagonal_comparison

        if type(other_start) is not int:
            raise ValueError("other source-window coordinate must be an integer")
        return certify_diagonal_comparison(
            self.certificate,
            first_start=self.start,
            second_start=other_start,
            window=window,
            continuation=continuation,
        )

    def universal_width_bounds(
        self,
        steps: int,
        *,
        max_states: int = 500,
        max_edges: int = 1500,
        max_composition_pairs: int = 2_000_000,
        max_relation_cells: int = 250_000,
    ) -> WidthGrowthBounds:
        """Demand finite all-middle-map width bounds at the source root."""
        self._check()
        from .diagonal_growth_bank import BorderWidthPowerRefused

        if self.start != 0:
            raise BorderWidthPowerRefused(
                "universal border power requires a source-root ring"
            )
        return self.certificate.universal_border_width_bounds(
            steps,
            max_states=max_states,
            max_edges=max_edges,
            max_composition_pairs=max_composition_pairs,
            max_relation_cells=max_relation_cells,
        )

    def constrain_inward_transfer(
        self,
        pair_domains: tuple[tuple[int, ...], ...],
        admitted_maps: tuple[CarryFn, ...],
        *,
        center: tuple[int, ...] | None = None,
    ) -> InwardCarryFilter:
        """Filter supplied finite symmetric domains by one carry relation."""
        self._check()
        from .symmetric_carry_filter import filter_symmetric_transfer

        return filter_symmetric_transfer(pair_domains, admitted_maps, center=center)

    def certified_phase_inward_transfer(
        self,
        tick: int,
        pair_domains: tuple[tuple[int, ...], ...],
        *,
        center: tuple[int, ...] | None = None,
    ) -> InwardCarryFilter:
        """Filter against a source-issued bilateral port at one physical tick."""
        self._check()
        if type(tick) is not int or not 0 <= tick < self.duration:
            raise ValueError("tick outside the authenticated ring interval")
        from .diagonal_growth_bank import source_growth_inlets

        inlet = source_growth_inlets(self.certificate, self.start + tick, 1)[0]
        if inlet.bilateral_port is None:
            raise ReverseTemporalRingRefused(
                "the selected tick has no exact bilateral border port"
            )
        return self.constrain_inward_transfer(
            pair_domains,
            inlet.bilateral_port.admitted_middle,
            center=center,
        )

    def conditional_ring_word(
        self, position: int, channel: str
    ) -> tuple[int | None, ...]:
        return self.harmonic(position, channel).lanes

    def diagnostic(self) -> dict[str, object]:
        """Small certificate summary, without claiming indefinite periodicity."""
        self._check()
        return {
            "steps": self.duration,
            "growth": self.certificate.growth_word[
                self.start : self.start + self.duration
            ],
            "entry_width": self.widths[0],
            "exit_width": self.widths[-1],
            "macro_return": self.macro is not None,
            "target_pair_singletons": sum(
                len(row[-1]) == 1 for row in self.phase_pair_domains
            ),
            "macro_f5_modes": (
                self.macro.phase_modes_mod5()[-1] if self.macro else None
            ),
            "forced_lanes": sum(h.forced_count for h in self.bank_words),
            "conditional_lanes": sum(
                self.duration - h.forced_count for h in self.bank_words
            ),
            "finite_future_classes": len(set(self.finite_moore_classes)),
            "temporal_repeat_certified": False,
            "complete_integer_certified": False,
        }


def _finite_future_classes(
    words: tuple[RingPhaseHarmonic, ...],
    duration: int,
    *,
    on_lane_visit: Callable[[], None] | None = None,
) -> tuple[int, ...]:
    """Coarsest suffix-output signatures on the finite certified path only.

    Unlike the `2rev10` source-input Moore automaton, these labels have NO
    defined transition beyond the finite final row. They cannot power a
    complete-root action; identical suffixes *inside* the window may merge.
    """
    codes: dict[tuple[object, ...], int] = {}
    result = [0] * (duration + 1)
    for t in range(duration - 1, -1, -1):
        lane_values = []
        for word in words:
            if on_lane_visit is not None:
                on_lane_visit()
            lane_values.append(word.lanes[t])
        signature = (tuple(lane_values), result[t + 1])
        result[t] = codes.setdefault(signature, len(codes) + 1)
    return tuple(result)


def _restrict_bilateral_port(
    system: ReverseInwardConstraints,
    t: int,
    k: int,
    port: BilateralCyclePort,
    source_width: int,
) -> None:
    """Intersect low overflow, one shared middle map and high ingress."""
    system.constrain_carry(t, k, port.low_carry)
    if not port.admitted_middle:
        raise ValueError("certified bilateral port has no middle transfer")
    system.constrain_middle_transfer(t, k, port.admitted_middle)
    high = {apply_carry_fn(fn, port.low_carry) for fn in port.admitted_middle}
    if len(high) == 1:
        system.constrain_carry(t, source_width - k, next(iter(high)))
    # The known high tile can reset the ingress into the leading digit even
    # when the middle transfer is still conditional.
    from .border_carry_safety import border_carry_port

    outer = border_carry_port(port.source)
    if outer.forced_msd_ingress is not None:
        system.constrain_carry(t, source_width - 1, outer.forced_msd_ingress)


def authorize_temporal_ring_bank(
    certificate: CertifiedBorderGrowth,
    *,
    start: int = 0,
    duration: int | None = None,
    positions: tuple[int, ...] = (0,),
    source_pair_prefix: int = 0,
    include_source_digits: bool = False,
    max_cells: int = 16384,
    bank_action: SourceGuardedGTBankAction | None = None,
) -> ReverseAddTemporalRingBank:
    """Source-certify finite macro-specific harmonics at *any* inward positions.

    No periodic source hypothesis, fixed period<=8, or literal `2rev10` clock
    is required. Every certified multi-digit border edge constrains one
    correlated low->middle->high carry circuit. The digit/Q19 F5/borrow
    restrictions are propagated forward AND backward across physical ticks.
    """
    certificate.validate(certificate.owner, certificate.source)
    if (
        type(start) is not int
        or start < 0
        or type(positions) is not tuple
        or not positions
        or any(type(i) is not int or i < 0 for i in positions)
        or len(positions) > 64
        or len(set(positions)) != len(positions)
    ):
        raise ValueError("invalid temporal macro range or ring positions")
    if duration is not None and (type(duration) is not int or duration < 1):
        raise ValueError("temporal ring duration must be a positive integer")
    if type(max_cells) is not int or not 1 <= max_cells <= 16384:
        raise ValueError("temporal ring cell budget must be in 1..16384")
    if type(include_source_digits) is not bool:
        raise TypeError("source digit inclusion flag must be Boolean")
    if type(source_pair_prefix) is not int or source_pair_prefix < 0:
        raise ValueError("invalid source-pair prefix")
    skip = int(certificate.source is not certificate.owner.initial)
    initial_width = (
        certificate.source.output_width if skip else certificate.source.pair_width
    )
    if source_pair_prefix > (initial_width + 1) // 2:
        raise ValueError("source-pair probe reaches beyond center")
    if bank_action is not None:
        from .q19_controlled_gt_bank import SourceGuardedGTBankAction

        if type(bank_action) is not SourceGuardedGTBankAction:
            raise TypeError("temporal ring requires a source-issued GT bank action")
        bank_action._validate()
        if (
            not bank_action.control_certified
            or bank_action.border_certificate is not certificate
            or bank_action.owner is not certificate.owner
            or bank_action.source is not certificate.source
            or bank_action.growth_control != certificate.growth_word
            or bank_action.steps != len(certificate.growth_word)
        ):
            raise ValueError("GT bank action does not match this border certificate")
    try:
        return _build_temporal_ring_bank(
            certificate,
            start=start,
            duration=duration,
            positions=positions,
            source_pair_prefix=source_pair_prefix,
            include_source_digits=include_source_digits,
            max_cells=max_cells,
            bank_action=bank_action,
            skip=skip,
            initial_width=initial_width,
        )
    except Exception:
        certificate.owner.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_FAILURES
        )
        raise


def _build_temporal_ring_bank(
    certificate: CertifiedBorderGrowth,
    *,
    start: int,
    duration: int | None,
    positions: tuple[int, ...],
    source_pair_prefix: int,
    include_source_digits: bool,
    max_cells: int,
    bank_action: SourceGuardedGTBankAction | None,
    skip: int,
    initial_width: int,
) -> ReverseAddTemporalRingBank:
    """Run a prevalidated request and charge only work reached by execution."""
    stop = len(certificate.growth_word) if duration is None else start + duration
    if type(stop) is not int or not start < stop <= len(certificate.growth_word):
        raise ReverseTemporalRingRefused(
            "ring exceeds the finite source-certified horizon"
        )
    if start < skip:
        raise ReverseTemporalRingRefused(
            "later Q19 occurrence's consumed growth is outside the ring window"
        )
    width = initial_width + sum(certificate.growth_word[skip:start])
    widths = [initial_width]
    for growth in certificate.growth_word[skip:]:
        widths.append(widths[-1] + growth)
    for j in range(start, stop):
        if any(position >= (width + 1) // 2 for position in positions):
            raise ReverseTemporalRingRefused(
                "ring position crosses the moving pair center"
            )
        width += certificate.growth_word[j]
    domain_cells = sum(widths)
    if domain_cells > max_cells:
        raise ValueError("requires finite, positive nonshrinking width tape")
    carry_cells = sum(w + 1 for w in widths[:-1])
    borrow_cells = sum(
        max(widths[t], widths[t + 1]) + 1 for t in range(len(widths) - 1)
    )
    certificate.owner.ledger.bump(
        _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_CONSTRAINT_CELLS,
        domain_cells + carry_cells + borrow_cells,
    )
    system = certificate.inward_temporal_constraints(
        max_cells=max_cells,
        source_pair_prefix=source_pair_prefix,
        include_source_digits=include_source_digits,
    )
    # Source-bound K-digit windows provide strictly stronger carry safety
    # than the one-digit border. Unproved windows are kept conditional.
    windows = certificate.bilateral_window_ports()
    coarse = certificate.bilateral_carry_ports()
    for j in range(start, stop):
        t = j - skip
        width = system.widths[t]
        # Apply both the unit border and the stronger admitted K-digit
        # window when available. The larger port refines the same inward
        # transfer factor; it does not replace or weaken the unit boundary.
        for port in (coarse[j], windows[j]):
            if port is not None and width >= 2 * port.source.k + 1:
                _restrict_bilateral_port(system, t, port.source.k, port, width)
    # The finite trace's outer return may be compiled with the same 96-cycle
    # exact homogeneous F5 action, but its *forcing* remains conditional.
    macro = None
    if (
        certificate.outer_pairs
        and all(pair is not None for pair in certificate.outer_pairs[start : stop + 1])
        and certificate.outer_pairs[start] == certificate.outer_pairs[stop]
    ):
        from .macro_conditioned_harmonics import authorize_finite_macro_window

        macro = authorize_finite_macro_window(
            certificate, start=start, duration=stop - start
        ).action
        system.constrain_macro_cycle(macro.cycle, start=start - skip)
    # A source-issued periodic bank already provides a complete, source-
    # aligned temporal output at its protected coordinate. Feed that action
    # BACK into the bilateral finite constraint system before propagation:
    # downstream F5/carry/bank masks must consume the same authenticated
    # coefficients instead of recomputing unrelated coarse domain guesses.
    # Only the specific owner-guarded coordinate is authorized here. No
    # extrapolation to adjacent positions, changing periods or future repeats.
    if bank_action is not None:
        position = bank_action.coordinate
        if position in positions:
            for j in range(start, stop + 1):
                source_time = j - skip
                if source_time < 0:
                    continue
                if position >= (system.widths[source_time] + 1) // 2:
                    raise ReverseTemporalRingRefused(
                        "GT bank coordinate reached the moving pair center"
                    )
                system.constrain_pair(source_time, position, bank_action.at(j))
    system.propagate(
        on_round=lambda: certificate.owner.ledger.bump(
            _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_PROPAGATION_ROUNDS
        )
    )
    duration = stop - start
    orbits = tuple(
        _inward_orbit_at(system, start - skip, duration, i) for i in positions
    )
    phase_pairs = tuple(
        tuple(system.pair_domain(t, i) for t in range(start - skip, stop - skip + 1))
        for i in positions
    )
    outputs: list[RingPhaseHarmonic] = []
    for position, orbit in zip(positions, orbits, strict=True):
        for channel in _RING_CHANNELS:
            if channel in _BANKS:
                bit_rows: list[int | None] = []
                for bands in orbit.selected_bands:
                    certificate.owner.ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS
                    )
                    possible = {int(channel == band) for band in bands}
                    bit_rows.append(
                        next(iter(possible)) if len(possible) == 1 else None
                    )
                bits = tuple(bit_rows)
            else:
                values = {
                    "f5": orbit.pair_f5,
                    "low_carry": orbit.low_carries,
                    "reflected_carry": orbit.reflected_carries,
                    "raw_borrow": orbit.raw_innovation_borrow,
                    "carry_xor": orbit.reflected_xor,
                    "carry_borrow_xor": orbit.carry_borrow_xor,
                    "low_birth": orbit.low_birth,
                    "low_death": orbit.low_death,
                    "high_birth": orbit.reflected_birth,
                    "high_death": orbit.reflected_death,
                }[channel]
                bit_rows = []
                for row in values:
                    certificate.owner.ledger.bump(
                        _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS
                    )
                    bit_rows.append(row[0] if len(row) == 1 else None)
                bits = tuple(bit_rows)
            outputs.append(
                RingPhaseHarmonic(
                    position,
                    channel,
                    bits,
                    _scalar_harmonics(bits),
                    _finite_period(bits),
                )
            )
    words = tuple(outputs)
    return _issue_temporal_ring_bank(
        certificate,
        start=start,
        duration=duration,
        positions=positions,
        widths=system.widths[start - skip : stop - skip + 1],
        output_orbits=orbits,
        phase_pair_domains=phase_pairs,
        bank_words=words,
        finite_moore_classes=_finite_future_classes(
            words,
            duration,
            on_lane_visit=lambda: certificate.owner.ledger.bump(
                _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS
            ),
        ),
        macro=macro,
        rounds=system.rounds,
    )


def _issue_temporal_ring_bank(
    certificate: CertifiedBorderGrowth,
    *,
    start: int,
    duration: int,
    positions: tuple[int, ...],
    widths: tuple[int, ...],
    output_orbits: tuple[MacroPhaseInwardOrbit, ...],
    phase_pair_domains: tuple[tuple[tuple[int, ...], ...], ...],
    bank_words: tuple[RingPhaseHarmonic, ...],
    finite_moore_classes: tuple[int, ...],
    macro: CycleHarmonicAction | None,
    rounds: int,
) -> ReverseAddTemporalRingBank:
    """Publish one owner-retained snapshot after exact source computation."""
    owner = certificate.owner
    certificate.validate(owner, certificate.source)
    registry = owner._issuance_registry
    key = registry.allocate_temporal_ring_bank_key()
    record = object.__new__(ReverseAddTemporalRingBank)
    values = {
        "certificate": certificate,
        "start": start,
        "duration": duration,
        "positions": positions,
        "widths": widths,
        "output_orbits": output_orbits,
        "phase_pair_domains": phase_pair_domains,
        "bank_words": bank_words,
        "finite_moore_classes": finite_moore_classes,
        "macro": macro,
        "rounds": rounds,
        "complete_integer_certified": False,
        "temporal_repeat_certified": False,
        "_registry_key": key,
    }
    issue_q19_record(record, values, _ISSUER)
    registry.retain_temporal_ring_bank(key, record)
    try:
        record.__post_init__()
    except BaseException:
        registry.discard_temporal_ring_bank(key, record)
        raise
    return record


__all__ = [
    "ReverseAddTemporalRingBank",
    "RingPhaseHarmonic",
    "authorize_temporal_ring_bank",
]
