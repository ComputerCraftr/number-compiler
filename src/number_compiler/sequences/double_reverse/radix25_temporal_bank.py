"""Source-bound radix-2/5 projections and Walsh views of a protected bank.

Decimal reversal remains the SLP's decimal reversal. The `2` in 2rev10 is
handled as a binary shift for modular observations; long inputs stay in the
decimal CONCAT/REPEAT carry fold. A finite protected bank may provide exact
two-step output lanes, but its finite halo does not imply a global quotient.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.integer_congruence import join_congruences
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)

from ._temporal_bank_authority import (
    FrozenMap,
    SourceAuthorizedRecord,
    issue_source_record,
    require_same_source,
    validate_source_record,
)
from .protected_temporal_bank import (
    BANK_CHANNELS,
    BankChannel,
    ProtectedPeriodicBank,
    TemporalBankChannel,
    bank_channel_name,
    protected_periodic_bank,
)
from .temporal_ports import DecimalCarryPort, decimal_carry_port

WALSH64_LANES = 64
BOOL_CHANNELS: tuple[BankChannel, ...] = tuple(
    channel for channel in BANK_CHANNELS if channel is not TemporalBankChannel.F5
)


def _crt25(value2: int, value5: int, places: int) -> int:
    """Reconstruct modulo 10**places from the coprime 2- and 5-adic rings."""
    base2, base5 = int(1 << places), int(5**places)
    joined = join_congruences((value2 % base2, base2), (value5 % base5, base5))
    if joined is None or joined[1] != base2 * base5:
        raise AssertionError("radix-2 and radix-5 moduli should be coprime")
    return joined[0]


@dataclass(frozen=True, slots=True)
class Radix25ShiftPort(SourceAuthorizedRecord):
    """Exact one-step shift and guarded noncontracting two-step projection."""

    places: int
    width: int
    source_mod10: int
    reverse_mod2: int
    reverse_mod5: int
    shifted_mod2: int
    doubled_mod5: int
    next_mod10: int
    correction_mod10: int
    two_step_mod10: int | None
    first_digit: int
    last_digit: int
    final_carry: int
    carry_transfer: str

    @property
    def modulus(self) -> int:
        return int(10**self.places)


def radix25_shift_port(
    arena: SLPArena,
    root: int,
    *,
    places: int = 8,
    max_bits: int = 4096,
    physical_prefix: int = 0,
    ledger: ResourceLedger | None = None,
    scratch_owner: int | None = None,
) -> Radix25ShiftPort:
    """Project T(X)=2*reverse10(X), retaining SLP compression.

    The carry fold uses one extra decimal place to evaluate the exact
    correction term. A source ending in zero has a contraction seam, so its
    affine T-squared projection is deliberately absent.
    """
    if type(places) is not int or places < 1:
        raise ValueError("radix25 places must be a positive integer")
    if type(max_bits) is not int or max_bits < 1:
        raise ValueError("radix25 bit budget must be positive")
    if type(physical_prefix) is not int or physical_prefix < 0:
        raise ValueError("radix25 physical prefix must be nonnegative")
    if (3322 * (places + 1) + 999) // 1000 > max_bits:
        raise BlockContextBudgetExceeded("radix25 carry lift exceeds the bit budget")
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("radix25 requires a valid source SLP root")

    modulus = 10**places
    folded: DecimalCarryPort = decimal_carry_port(
        arena,
        root,
        modulus=10 * modulus,
        max_bits=max_bits,
        ledger=ledger,
        scratch_owner=scratch_owner,
    )
    if folded.first is None or folded.last is None:
        raise ValueError("radix25 source must contain a decimal digit")
    if folded.width > 1 and folded.first == 0:
        raise ValueError("radix25 source must use canonical decimal width")

    mod2, mod5 = 1 << places, 5**places
    reverse2, reverse5 = folded.reversed % mod2, folded.reversed % mod5
    shifted2 = (reverse2 << 1) % mod2
    doubled5 = (2 * reverse5) % mod5
    next_mod10 = _crt25(shifted2, doubled5, places)

    growth = int(folded.last >= 5)
    correction = (-99 * (folded.carry_word // 10) - 10 * growth) % modulus
    two_step: int | None = None
    if folded.last != 0:
        gain = 1 + 9 * growth
        two_step = (
            4 * gain * (folded.forward % modulus) + 2 * gain * correction + 2 * growth
        ) % modulus
    if next_mod10 != (2 * folded.reversed) % modulus:
        raise AssertionError("binary shift and decimal reversal CRT disagree")
    result = Radix25ShiftPort(
        places,
        folded.width,
        folded.forward % modulus,
        reverse2,
        reverse5,
        shifted2,
        doubled5,
        next_mod10,
        correction,
        two_step,
        folded.first,
        folded.last,
        growth,
        folded.transfer.value,
    )
    return issue_source_record(result, arena, root, source_generation=physical_prefix)


@dataclass(frozen=True, slots=True)
class Walsh64TemporalPort(SourceAuthorizedRecord):
    """One exact 64-frame transform over outputs from a protected bank."""

    start_tick: int
    lane_count: int
    masks: Mapping[str, int]
    transform_mod5: Mapping[str, tuple[int, ...]]
    f5_transform: tuple[int, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.masks, FrozenMap):
            object.__setattr__(self, "masks", FrozenMap(self.masks))
        if not isinstance(self.transform_mod5, FrozenMap):
            object.__setattr__(self, "transform_mod5", FrozenMap(self.transform_mod5))


def temporal_bank_walsh64(
    bank: ProtectedPeriodicBank, *, start_tick: int = 0
) -> Walsh64TemporalPort:
    """Transform Boolean bank ports and F5 values over 64 certified frames."""
    from number_compiler.arithmetic.fields.walsh import walsh64_mod5

    if type(bank) is not ProtectedPeriodicBank:
        raise TypeError("Walsh64 requires a protected source-bound temporal bank")
    if type(start_tick) is not int or start_tick < 0:
        raise ValueError("Walsh64 start tick must be nonnegative")
    if start_tick + WALSH64_LANES > bank.f_steps:
        raise ValueError("Walsh64 requires 64 source-certified two-step frames")

    frames, authority = bank.authorized_frames(start_tick, WALSH64_LANES)
    masks = {bank_channel_name(channel): 0 for channel in BOOL_CHANNELS}
    f5_masks = [0] * 5
    for lane, frame in enumerate(frames):
        for channel in BOOL_CHANNELS:
            bit = frame.scalar(channel)
            if bit not in (0, 1):
                raise AssertionError("Walsh64 Boolean output is not a bit")
            masks[bank_channel_name(channel)] |= bit << lane
        f5_masks[frame.f5] |= 1 << lane
    transformed = {name: walsh64_mod5(mask) for name, mask in masks.items()}
    f5_bands = tuple(walsh64_mod5(mask) for mask in f5_masks)
    f5_transform = tuple(
        sum(value * f5_bands[value][index] for value in range(5)) % 5
        for index in range(WALSH64_LANES)
    )
    result = Walsh64TemporalPort(
        start_tick, WALSH64_LANES, masks, transformed, f5_transform
    )
    arena = authority.arena
    if arena is None:
        raise ValueError("protected bank source arena has been released")
    return issue_source_record(
        result,
        arena,
        authority.root,
        parent=authority,
        source_generation=authority.source_generation,
    )


@dataclass(frozen=True, slots=True)
class JointRadix25TemporalBank:
    """Radix and temporal views issued from one certified source root."""

    physical_prefix: int
    source: Radix25ShiftPort
    protected: ProtectedPeriodicBank
    walsh64: Walsh64TemporalPort

    def __post_init__(self) -> None:
        source_authority = validate_source_record(self.source)
        bank_authority = validate_source_record(self.protected)
        walsh_authority = validate_source_record(self.walsh64)
        if (
            source_authority.source_generation != self.physical_prefix
            or bank_authority.source_generation != self.physical_prefix
        ):
            raise ValueError("radix and temporal bank have different owner generations")
        require_same_source(source_authority, bank_authority)
        require_same_source(bank_authority, walsh_authority)
        if walsh_authority.parent is not bank_authority:
            raise ValueError("Walsh transform is not issued from this protected bank")
        if self.physical_prefix != self.protected.physical_prefix:
            raise ValueError("radix and Walsh actions have different source prefixes")
        if self.source.width != self.protected.source_width:
            raise ValueError("radix and Walsh actions have different source widths")


def joint_radix25_temporal_bank(
    arena: SLPArena,
    root: int,
    phase: int,
    pair_position: int,
    f_steps: int,
    *,
    physical_prefix: int,
    period: int,
    places: int,
    max_bits: int,
    walsh_start: int,
    ledger: ResourceLedger,
    scratch_owner: int,
) -> JointRadix25TemporalBank:
    """Join a protected temporal bank, Walsh lanes and radix source port."""
    if type(f_steps) is not int or f_steps < WALSH64_LANES:
        raise ValueError("joint Walsh64 bank needs 64 two-step temporal frames")
    bank = protected_periodic_bank(
        arena,
        root,
        phase,
        pair_position,
        f_steps,
        period,
        physical_prefix=physical_prefix,
        ledger=ledger,
        scratch_owner=scratch_owner,
    )
    walsh = temporal_bank_walsh64(bank, start_tick=walsh_start)
    source = radix25_shift_port(
        arena,
        root,
        places=places,
        max_bits=max_bits,
        physical_prefix=physical_prefix,
        ledger=ledger,
        scratch_owner=scratch_owner,
    )
    ledger.bump(_double_reverse_keys.DOUBLE_REVERSE_WEIGHTED_CARRY_PORT_PUBLICATIONS)
    return JointRadix25TemporalBank(physical_prefix, source, bank, walsh)


__all__ = [
    "BOOL_CHANNELS",
    "WALSH64_LANES",
    "JointRadix25TemporalBank",
    "Radix25ShiftPort",
    "Walsh64TemporalPort",
    "joint_radix25_temporal_bank",
    "radix25_shift_port",
    "temporal_bank_walsh64",
]
