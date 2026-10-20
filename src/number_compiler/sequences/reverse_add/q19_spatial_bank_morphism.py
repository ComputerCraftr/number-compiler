"""Source-bound spatial output morphism for reverse/add's powered LT/EQ/GT bank.

The 2rev10 morphism inspired the separation between (1) an authenticated,
spatially protected source period, (2) a future border-control input, and
(3) a compressed future output word.  The arithmetic here is *not* 2rev10:
its symbols are decimal symmetric pair sums 0..18, its carries are the
K0/ID/K1 monoid, and growth shifts the reflected digit only.

No result from this module licenses a whole-integer temporal shortcut. A
conditional control program can be queried but is never promoted to a physical
border certificate. The independent signed innovation-difference borrow is
not the same as the two conditional next-nongrowth local borrow responses.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.decimal_pair_partition import (
    DECIMAL_PAIR_BAND_NAMES,
    DecimalPairBand,
    decimal_pair_band,
)
from number_compiler.arithmetic.fields.walsh import walsh64_mod5

from ._q19_issuance import issue_q19_record
from .q19_bank_boolean import CoupledBooleanBankFrame
from .q19_controlled_gt_bank import SourceGuardedGTBankAction
from .q19_periodic_cone import periodic_guard
from .q19_uniform_cone import UniformConeNotAuthorized

if TYPE_CHECKING:
    from .border_carry_safety import BilateralCyclePort
    from .q19_border_control import CertifiedBorderGrowth
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner
    from .temporal_residue99 import ReverseAddResidue99

_BANDS = DECIMAL_PAIR_BAND_NAMES
_EXTRA = (
    "coefficient",
    "f5",
    "carry_xor",
    "carry_and",
    "pascal_parity",
    "gt_high_birth",
    "eq_birth",
    "quiet_borrow0",
    "quiet_borrow1",
)
_CHANNELS = frozenset((*_BANDS, *_EXTRA))
_BOOL_CHANNELS = frozenset((*_BANDS, *_EXTRA[2:]))
_SPATIAL_WINDOW_ISSUER = object()


@dataclass(frozen=True, slots=True)
class SpatialBankProgram:
    """CONCAT(REPEAT(period, repeats), prefix) without materializing cells.

    ``period`` is already rotated to output coordinate zero. This avoids the
    2rev10 final/entry-coordinate error: reverse/add's low-side *pair* index
    stays anchored to the LSD while its reflected high-side coordinate moves.
    """

    period: tuple[int, ...]
    length: int

    def __post_init__(self) -> None:
        if (
            type(self.period) is not tuple
            or not self.period
            or any(
                type(value) is not int or not 0 <= value <= 18 for value in self.period
            )
            or type(self.length) is not int
            or self.length < 0
        ):
            raise ValueError("invalid symbolic spatial output word")

    @property
    def repeats(self) -> int:
        return self.length // len(self.period)

    @property
    def suffix(self) -> tuple[int, ...]:
        return self.period[: self.length % len(self.period)]

    @property
    def nodes(self) -> int:
        return 3 if self.suffix and self.repeats else 2

    def at(self, index: int) -> int:
        if type(index) is not int or not 0 <= index < self.length:
            raise IndexError(index)
        return self.period[index % len(self.period)]

    def counts(self) -> int:
        full, tail = divmod(self.length, len(self.period))
        return full * sum(self.period) + sum(self.period[:tail])

    def slice(self, start: int, count: int) -> tuple[int, ...]:
        if (
            type(start) is not int
            or type(count) is not int
            or start < 0
            or count < 0
            or start + count > self.length
        ):
            raise IndexError("spatial output slice outside certified window")
        return tuple(self.at(start + i) for i in range(count))

    def walsh64_mod5(self, start: int) -> tuple[int, ...]:
        if type(start) is not int or start < 0 or self.length < start + 64:
            raise ValueError("64 requested lanes extend beyond protected output")
        if any(bit not in (0, 1) for bit in self.period):
            raise ValueError("Walsh64 requires a Boolean output channel")
        mask = sum(self.at(start + i) << i for i in range(64))
        return walsh64_mod5(mask)


@dataclass(frozen=True, slots=True)
class ReverseAddSpatialBankMorphism:
    """One issued action, one protected multi-cell output region.

    Each call validates the underlying source-bound Q19 action, so this cannot
    be used to forge an unconditional growth label or launder a foreign owner.
    """

    action: SourceGuardedGTBankAction
    start: int
    count: int
    halo: int
    _seal: object = field(default=None, init=False, repr=False, compare=False)
    _binding: tuple[object, ...] = field(init=False, repr=False, compare=False)
    _registry_key: int = field(default=-1, init=False, repr=False, compare=False)

    @property
    def registry_key(self) -> int:
        """Return the issuer slot; ownership is checked by the registry."""
        return self._registry_key

    def __post_init__(self) -> None:
        if type(self.action) is not SourceGuardedGTBankAction:
            raise TypeError("spatial morphism requires a source-issued GT bank")
        self.action.validate_source_authority()
        if self.halo != self.action.halo:
            raise ValueError("spatial morphism must preserve issued halo width")
        if type(self.start) is not int or type(self.count) is not int:
            raise TypeError("morphism start/count must be exact integers")
        if type(self.halo) is not int:
            raise TypeError("morphism halo must be an exact integer")
        if self.count < 1:
            raise ValueError("spatial morphism needs a nonempty output window")
        if self._seal is not _SPATIAL_WINDOW_ISSUER:
            raise ValueError("spatial morphism must be issued by its Q19 owner")
        if self._binding != self._snapshot():
            raise ValueError("source-bound spatial morphism was altered")
        self.action.owner.issuance_registry.validate_spatial_bank_window(self)

    def _snapshot(self) -> tuple[object, ...]:
        return (
            self.action.owner,
            self.action,
            self.start,
            self.count,
            self.halo,
            self._registry_key,
        )

    def publication_snapshot(self) -> tuple[object, ...]:
        """Return structural fields for the owning issuer's binding check."""
        return self._snapshot()

    def validate_source_authority(self) -> None:
        if type(self.action) is not SourceGuardedGTBankAction:
            raise TypeError("spatial morphism lost its source-issued GT bank")
        self.action.validate_source_authority()
        if (
            type(self.start) is not int
            or type(self.count) is not int
            or type(self.halo) is not int
            or self.count < 1
        ):
            raise ValueError("source-bound spatial morphism coordinates were altered")
        if (
            self._seal is not _SPATIAL_WINDOW_ISSUER
            or self._binding != self._snapshot()
            or self.halo != self.action.halo
        ):
            raise ValueError("source-bound spatial morphism was changed")
        self.action.owner.issuance_registry.validate_spatial_bank_window(self)

    @property
    def control_certified(self) -> bool:
        self.validate_source_authority()
        return self.action.control_certified

    @property
    def complete_integer_certified(self) -> bool:
        return False

    @property
    def final_width_if_certified(self) -> int | None:
        self.validate_source_authority()
        if not self.action.control_certified:
            return None
        return self.action.source.pair_width + self.action.growth_count

    def leading_carry_ports(self, tick: int) -> tuple[int, ...] | None:
        """Forward the source-bound leading safety cone, not bank mask bits."""
        self.validate_source_authority()
        return self.action.leading_carry_ports(tick)

    def bilateral_carry_port(self, tick: int) -> BilateralCyclePort | None:
        """Forward the same source-issued low-overflow/middle transfer constraint."""
        self.validate_source_authority()
        return self.action.bilateral_carry_port(tick)

    def bilateral_window_port(self, tick: int) -> BilateralCyclePort | None:
        """Forward the full K-window constraint when the finite tiles are fixed."""
        self.validate_source_authority()
        return self.action.bilateral_window_port(tick)

    def _periods(
        self, depth: int, channels: tuple[str, ...]
    ) -> dict[str, tuple[int, ...]]:
        self.validate_source_authority()
        if type(depth) is not int or not 0 <= depth <= self.action.steps:
            raise ValueError("temporal depth outside source-certified bank")
        if type(channels) is not tuple or not channels:
            raise TypeError("output channels must be a nonempty tuple")
        if any(
            type(channel) is not str or channel not in _CHANNELS for channel in channels
        ):
            raise ValueError("unknown output channel")
        if len(set(channels)) != len(channels):
            raise ValueError("output channels must be unique")
        if depth == 0:
            word = self.action.period
            result: dict[str, tuple[int, ...]] = {}
            for channel in channels:
                if channel == "coefficient":
                    result[channel] = word
                elif channel == "f5":
                    result[channel] = tuple(x % 5 for x in word)
                elif channel in _BANDS:
                    result[channel] = tuple(
                        int(_belongs(x, DecimalPairBand(channel))) for x in word
                    )
                else:
                    raise ValueError(
                        "conditional output ports require at least one tick"
                    )
            return result
        current = (
            self.action.period if depth == 1 else self.action.frame(depth - 2).target
        )
        packet = CoupledBooleanBankFrame.from_frame(
            current, self.action.frame(depth - 1)
        )
        result = {}
        for channel in channels:
            if channel == "coefficient":
                period = packet.target
            elif channel in (*_BANDS, "f5"):
                period = tuple(packet.target_bands[channel])
            elif channel == "carry_xor":
                period = packet.reflected_xor
            elif channel == "carry_and":
                period = packet.reflected_and
            elif channel == "pascal_parity":
                period = packet.pascal_parity
            elif channel == "gt_high_birth":
                period = packet.gt_high_birth
            elif channel == "eq_birth":
                period = packet.eq_birth
            elif channel in ("quiet_borrow0", "quiet_borrow1"):
                ingress = 0 if channel == "quiet_borrow0" else 1
                period = tuple(x[ingress] for x in packet.borrow_transfer_if_next_quiet)
            else:
                raise AssertionError("unreachable bank channel")
            result[channel] = period
        return result

    def _period(self, depth: int, channel: str) -> tuple[int, ...]:
        return self._periods(depth, (channel,))[channel]

    def output_words(
        self, channels: tuple[str, ...], *, depth: int | None = None
    ) -> dict[str, SpatialBankProgram]:
        """Project several channels from one authenticated temporal frame."""
        d = self.action.steps if depth is None else depth
        periods = self._periods(d, channels)
        words: dict[str, SpatialBankProgram] = {}
        for channel, period in periods.items():
            offset = self.start % len(period)
            words[channel] = SpatialBankProgram(
                period[offset:] + period[:offset], self.count
            )
        return words

    def output_word(
        self, channel: str, *, depth: int | None = None
    ) -> SpatialBankProgram:
        """Exact periodic spatial program after any authenticated time prefix.

        A conditional action returns a *conditional* program; callers must
        check ``control_certified`` before reporting physical future outputs.
        """
        return self.output_words((channel,), depth=depth)[channel]

    def at(self, position: int, *, channel: str = "coefficient") -> int:
        return self.output_word(channel).at(position)

    def counts(self, channel: str) -> int:
        return self.output_word(channel).counts()

    def walsh64_mod5(self, channel: str, *, start: int = 0) -> tuple[int, ...]:
        if channel not in _BOOL_CHANNELS:
            raise ValueError("Walsh64 bank must select a Boolean output")
        return self.output_word(channel).walsh64_mod5(start)

    def residue99(self) -> ReverseAddResidue99:
        """Exact scalar observer; never upgrades conditional bank authority."""
        self.validate_source_authority()
        return self.action.temporal_residue99()


def _belongs(s: int, channel: DecimalPairBand) -> bool:
    return decimal_pair_band(s) is channel


def _issue_spatial_bank_window(
    action: SourceGuardedGTBankAction, *, start: int, count: int
) -> ReverseAddSpatialBankMorphism:
    """Authenticate the complete output cone, then retain its exact record."""
    action.validate_source_authority()
    halo = action.halo
    owner = action.owner
    source = action.source
    lo = start - halo
    hi = start + count + halo
    # The evolving center is never treated as a periodic interior port.
    if lo < 0 or hi > source.pair_width // 2:
        raise UniformConeNotAuthorized(
            "morphism reaches an unproved growth, exterior or center seam"
        )
    if not periodic_guard(owner, source, lo, hi, action.period):
        raise UniformConeNotAuthorized(
            "spatial morphism source differs from authenticated Q19 period"
        )

    registry = owner.issuance_registry
    key = registry.allocate_spatial_bank_window_key()
    record = object.__new__(ReverseAddSpatialBankMorphism)
    values = {
        "action": action,
        "start": start,
        "count": count,
        "halo": halo,
        "_registry_key": key,
    }
    issue_q19_record(record, values, _SPATIAL_WINDOW_ISSUER)
    registry.retain_spatial_bank_window(key, record)
    try:
        record.__post_init__()
    except BaseException:
        registry.discard_spatial_bank_window(key, record)
        raise
    return record


def authorize_spatial_bank_morphism(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    steps: int,
    start: int,
    count: int,
    growth_control: tuple[int, ...] | CertifiedBorderGrowth,
    period_size: int = 2,
    max_states: int = 10000,
) -> ReverseAddSpatialBankMorphism:
    """Produce protected spatial output from a binary-squared GT/EQ/LT bank.

    Never guesses the width itinerary. For physical results pass an issued
    ``CertifiedBorderGrowth``. The Q19 pair grammar authenticates *all* source
    cells in the moving dependency halo, including repeats and center checks.
    """
    if type(start) is not int or type(count) is not int or count < 1:
        raise ValueError("bad spatial morphism interval")
    if type(steps) is not int or steps < 1:
        raise ValueError("bad temporal morphism depth")
    owner.validate_issued_occurrence(source)
    action = owner.authorize_controlled_gt_bank(
        source,
        steps=steps,
        coordinate=start,
        period_size=period_size,
        growth_control=growth_control,
        max_states=max_states,
    )
    try:
        return _issue_spatial_bank_window(action, start=start, count=count)
    except BaseException:
        owner.issuance_registry.discard_bank(action.registry_key, action)
        raise


__all__ = [
    "ReverseAddSpatialBankMorphism",
    "SpatialBankProgram",
    "authorize_spatial_bank_morphism",
]
