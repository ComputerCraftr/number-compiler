"""NC12 source-owned admission to the earlier coupled GT/LT temporal bank.

The spatial Q19 guard is authenticated from the live source SLP, while the
repeating border growth *input* remains a conditional port.  Matching a
spatial GT-high motif does not authenticate an infinite border trajectory.
The compiled action retains the EXACT five-band/F5, reflected-carry, oriented
digit, and next-nongrowth signed-borrow identity information and supports
binary temporal squaring without constructing intermediate Q19 occurrences.

This module does not authorize the complete integer or numerical global U,V.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Literal

from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

from ._q19_issuance import issue_q19_record
from .bank_width_clock import WidthMacro
from .mixed_periodic_bank import (
    ControlledMixedBank,
    IncompleteMixedBorder,
    MixedFrame,
    MixedOutputArena,
    MixedPeriodicCore,
    MixedTemporalAction,
    _controlled_bank_workspace,
    required_protected_halo,
)
from .q19_border_control import CertifiedBorderGrowth
from .q19_periodic_cone import _periodic_guard
from .q19_uniform_cone import UniformConeNotAuthorized
from .temporal_bank_actions import (
    ConditionalEQGrowthExit,
    conditional_first_growth_exit,
    power_alternating_outputs,
)
from .temporal_bulk_moore import AlternatingCore, UniformCarryCell

if TYPE_CHECKING:
    from .border_carry_safety import BilateralCyclePort
    from .conditional_f5_macro import SourceCertifiedF5Macro
    from .q19_bank_boolean import CoupledBooleanBankFrame
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner
    from .radix19_cochain import Radix19CarryBlock
    from .temporal_residue99 import ReverseAddResidue99
    from .temporal_ring_harmonics import ReverseAddTemporalRingBank

_ISSUER = object()


@dataclass(frozen=True, slots=True)
class SourceGuardedGTBankAction:
    """Q19-issued, spatially guarded *conditional* controlled bank power.

    `growth_control` is an input, not a predicted future border word.  The
    all-control future is NOT identical in general; the caller must supply an
    independent certified border itinerary before this can contribute to a
    whole-integer proof.  Accessors revalidate live Q19 ownership.
    """

    owner: ReversePairQ19OutputOwner
    source: ReversePairOutputOccurrence
    coordinate: int
    steps: int
    period: tuple[int, ...]
    growth_control: tuple[int, ...]
    halo: int
    action: MixedTemporalAction = field(repr=False, compare=False)
    full_integer_certified: Literal[False] = False
    control_certified: bool = False
    border_certificate: CertifiedBorderGrowth | None = field(
        default=None, repr=False, compare=False
    )
    _seal: object = field(default=None, repr=False, compare=False)
    _binding: tuple[object, ...] = field(default=(), repr=False, compare=False)
    _registry_key: int = field(default=-1, repr=False, compare=False)

    @property
    def registry_key(self) -> int:
        """Return the issuer slot; ownership is checked by the registry."""
        return self._registry_key

    def __post_init__(self) -> None:
        if self._seal is not _ISSUER or self._binding != self._snapshot():
            raise ValueError("conditional bank action must be issued by a Q19 owner")
        if self.full_integer_certified is not False:
            raise ValueError("pointed GT bank cannot publish a complete integer")
        if self.control_certified != (self.border_certificate is not None):
            raise ValueError(
                "growth authorization must come from a Q19 border certificate"
            )
        if self.border_certificate is not None:
            self.border_certificate.validate(self.owner, self.source)
            if self.border_certificate.growth_word != self.growth_control:
                raise ValueError("growth certificate does not match its bank program")
        self.owner._issuance_registry.validate_bank(self)

    def _snapshot(self) -> tuple[object, ...]:
        action = self.action
        arena = action.arena
        return (
            self.owner,
            self.source,
            self.coordinate,
            self.steps,
            self.period,
            self.growth_control,
            self.halo,
            action,
            action.source,
            action.source.coefficients,
            action.target,
            action.target.coefficients,
            action.steps,
            action.growth_pattern,
            action.output_root,
            arena,
            arena.nodes,
            action.orbit_states,
            action.moore_states,
            self.full_integer_certified,
            self.control_certified,
            self.border_certificate,
            self._registry_key,
        )

    def publication_snapshot(self) -> tuple[object, ...]:
        """Return structural fields for the owning issuer's binding check."""
        return self._snapshot()

    def validate_source_authority(self) -> None:
        action = self.action
        binding = self._binding
        snapshot = self._snapshot()
        if (
            self._seal is not _ISSUER
            or type(binding) is not tuple
            or len(binding) != len(snapshot)
            or binding[7] is not action
            or binding[8] is not action.source
            or binding[10] is not action.target
            or binding[15] is not action.arena
            or binding[16] is not action.arena.nodes
            or binding[21] is not self.border_certificate
            or binding != snapshot
        ):
            raise ValueError("issued conditional bank action was altered")
        self.owner._issuance_registry.validate_bank(self)
        self.owner.validate_issued_occurrence(self.source)
        if self.border_certificate is not None:
            self.border_certificate.validate(self.owner, self.source)

    def temporal_ring_bank(
        self,
        *,
        start: int = 0,
        duration: int | None = None,
        positions: tuple[int, ...] = (0,),
        source_pair_prefix: int = 0,
        include_source_digits: bool = False,
        max_cells: int = 16384,
    ) -> ReverseAddTemporalRingBank:
        """Demand the same authenticated macro-conditioned inward ring ports."""
        self.validate_source_authority()
        if self.border_certificate is None:
            raise ValueError("a live border certificate is required for ring authority")
        return self.border_certificate.temporal_ring_bank(
            start=start,
            duration=duration,
            positions=positions,
            source_pair_prefix=source_pair_prefix,
            include_source_digits=include_source_digits,
            max_cells=max_cells,
            bank_action=self,
        )

    def temporal_residue99(self) -> ReverseAddResidue99:
        """Independent mod-99 future output from the same issued pair source.

        For horizons >=6, this is unconditional even if the GT bank's growth
        input is only conditional; it does not certify the GT-bank output.
        """
        self.validate_source_authority()
        from .temporal_residue99 import from_issued_pair

        return from_issued_pair(
            self.owner,
            self.source,
            self.steps,
            growth_word=self.growth_control,
            border_certificate=self.border_certificate,
        )

    @property
    def output_nodes(self) -> int:
        self.validate_source_authority()
        return self.action.program_nodes

    @property
    def moore_states(self) -> int:
        self.validate_source_authority()
        return self.action.moore_states

    @property
    def growth_count(self) -> int:
        self.validate_source_authority()
        word = WidthMacro.from_bits(self.growth_control)
        whole, tail = divmod(self.steps, len(self.growth_control))
        return word.growth_count * whole + sum(self.growth_control[:tail])

    def at(self, depth: int) -> int:
        """Exact conditional pair coefficient for this protected coordinate."""
        self.validate_source_authority()
        if type(depth) is not int or not 0 <= depth <= self.steps:
            raise ValueError("temporal coordinate outside issued action")
        phase = self.coordinate % len(self.period)
        return (
            self.period[phase]
            if depth == 0
            else self.action.at(depth - 1).target[phase]
        )

    def frame(self, tick: int) -> MixedFrame:
        """Complete synchronized conditional GT/F5/borrow output at one tick."""
        self.validate_source_authority()
        return self.action.at(tick)

    def masks(self, tick: int) -> dict[str, tuple[int, ...]]:
        return self.frame(tick).masks()

    def boolean_frame(self, tick: int) -> CoupledBooleanBankFrame:
        """Publish the coupled LT/EQ/GT, F5, XOR and borrow truth tables.

        The preceding bank state is determined by the same immutable temporal
        output program. This performs no Q19 physical transition and does
        not promote the conditional borrow gate to a signed global borrow.
        """
        from .q19_bank_boolean import CoupledBooleanBankFrame

        current = self.period if tick == 0 else self.frame(tick - 1).target
        return CoupledBooleanBankFrame.from_frame(current, self.frame(tick))

    def conditional_next_quiet_borrow(self, tick: int) -> tuple[int, int]:
        """Return identity/reset for raw borrow 0 and 1 on the local port.

        This is valid only if the *following comparison* does not grow.  A
        growth-aligned subtraction requires its separate width-seam observer.
        """
        f = self.frame(tick)
        phase = self.coordinate % len(self.period)
        eta = MixedPeriodicCore(f.target).ingresses()[phase][1]
        target = f.target[phase]
        rho = int(target > 9 or (target == 9 and eta == 1))
        identity = f.borrow_identity_if_next_quiet[phase]
        return (0, 1) if identity else (rho, rho)

    def leading_carry_ports(self, tick: int) -> tuple[int, ...] | None:
        """Read the finite Q19-issued exterior carry constraint for one tick."""
        self.validate_source_authority()
        if type(tick) is not int or not 0 <= tick < self.steps:
            raise IndexError(tick)
        if self.border_certificate is None:
            raise ValueError("leading carry safety needs a live border certificate")
        return self.border_certificate.forced_leading_carry_ports()[tick]

    def bilateral_carry_port(self, tick: int) -> BilateralCyclePort | None:
        """Expose correlated low overflow and admissible middle transfers."""
        self.validate_source_authority()
        if type(tick) is not int or not 0 <= tick < self.steps:
            raise IndexError(tick)
        if self.border_certificate is None:
            raise ValueError("two-sided carry ports need a live border certificate")
        return self.border_certificate.bilateral_carry_ports()[tick]

    def bilateral_window_port(self, tick: int) -> BilateralCyclePort | None:
        """Return a full K-window port only when both finite tiles are known."""
        self.validate_source_authority()
        if type(tick) is not int or not 0 <= tick < self.steps:
            raise IndexError(tick)
        if self.border_certificate is None:
            raise ValueError("window carry ports need a live border certificate")
        return self.border_certificate.bilateral_window_ports()[tick]

    def conditional_f5_macro_action(
        self, *, start: int = 0, steps: int | None = None, z: int = 2
    ) -> SourceCertifiedF5Macro:
        """Project a certified border return into its conditional F5 action.

        This is tied to the bank's exact source and growth certificate.  It
        leaves source-specific affine corrections as explicit consumer inputs
        and does not authorize repeating the Q19 source.
        """
        self.validate_source_authority()
        certificate = self.border_certificate
        if certificate is None:
            raise ValueError("F5 macro action needs certified border control")
        if certificate.growth_word != self.growth_control:
            raise ValueError("bank growth word differs from its live certificate")
        return certificate.conditional_f5_macro_action(start=start, steps=steps, z=z)

    def source_radix19_cochain(
        self, *, z: int = 2, modulus: int = 5
    ) -> Radix19CarryBlock:
        """Read this action's authenticated source through the carry cochain."""
        self.validate_source_authority()
        return self.owner.radix19_cochain(self.source, z=z, modulus=modulus)

    def certified_walsh64_mod5(
        self, tick: int, *, channel: str, start: int
    ) -> tuple[int, ...]:
        """Transform 64 bank-output bits under a source-checked spatial halo."""
        from number_compiler.arithmetic.fields.walsh import walsh64_mod5

        from .q19_bank_boolean import CoupledBooleanBankFrame
        from .q19_periodic_cone import _periodic_guard

        self.validate_source_authority()
        if type(tick) is not int or not 0 <= tick < self.steps:
            raise ValueError("bank Walsh tick is outside the issued action")
        if type(start) is not int or start < 0:
            raise ValueError("Walsh64 start must be nonnegative")
        lo, hi = start - self.halo, start + 64 + self.halo
        if lo < 0 or hi > self.source.pair_width:
            raise ValueError("Walsh64 lanes lack a protected source halo")
        if self.border_certificate is None:
            raise ValueError("Walsh64 future bank needs certified border control")
        if not _periodic_guard(self.owner, self.source, lo, hi, self.period):
            raise ValueError("Walsh64 periodic word differs from the source SLP")
        current = self.period if tick == 0 else self.frame(tick - 1).target
        packet = CoupledBooleanBankFrame.from_frame(current, self.frame(tick))
        if channel not in packet.target_bands or channel == "f5":
            raise ValueError("Walsh64 channel must be one of the Boolean pair bands")
        bits = packet.target_bands[channel]
        mask = sum(int(bits[(start + lane) % len(bits)]) << lane for lane in range(64))
        return walsh64_mod5(mask)

    def certified_borrow_xor_walsh64_mod5(
        self, tick: int, *, start: int
    ) -> tuple[tuple[int, ...], tuple[int, ...]]:
        """Return both conditional borrow-ingress Walsh packets after quiet.

        The result is conditional on the raw borrow entering this 64-position
        window. It is not a signed global innovation tape. A following
        nongrowth comparison and the enlarged source halo are both required.
        """
        from number_compiler.arithmetic.fields.walsh import walsh64_mod5

        from .mixed_periodic_bank import MixedPeriodicCore
        from .q19_bank_boolean import CoupledBooleanBankFrame
        from .q19_periodic_cone import _periodic_guard

        self.validate_source_authority()
        if type(tick) is not int or not 0 <= tick < self.steps - 1:
            raise ValueError("following certified nongrowth event is required")
        if self.growth_control[tick + 1] != 0:
            raise ValueError("borrow/XOR Walsh requires a following nongrowth event")
        if type(start) is not int or start < 0:
            raise ValueError("Walsh64 start must be nonnegative")
        lo, hi = start - self.halo, start + 64 + self.halo
        if lo < 0 or hi > self.source.pair_width:
            raise ValueError("borrow/XOR lanes lack a protected source halo")
        if self.border_certificate is None or not _periodic_guard(
            self.owner, self.source, lo, hi, self.period
        ):
            raise ValueError("borrow/XOR Walsh lacks source-certified periodic control")
        current = self.period if tick == 0 else self.frame(tick - 1).target
        packet = CoupledBooleanBankFrame.from_frame(current, self.frame(tick))
        ingresses = MixedPeriodicCore(packet.target).ingresses()
        transformed = []
        for initial_borrow in (0, 1):
            borrow = initial_borrow
            mask = 0
            for lane in range(64):
                position = (start + lane) % len(self.period)
                coefficient = packet.target[position]
                carry_in, _reflected = ingresses[position]
                carry_out = int(coefficient > 9 or (coefficient == 9 and carry_in == 1))
                borrow = packet.borrow_transfer_if_next_quiet[position][borrow]
                mask |= (carry_out ^ borrow) << lane
            transformed.append(walsh64_mod5(mask))
        return transformed[0], transformed[1]

    def square(self, owner: ReversePairQ19OutputOwner) -> SourceGuardedGTBankAction:
        """Reissue a doubled controlled action under a doubled ORIGINAL halo.

        This does not authenticate that the source supplies the chosen input
        growth pattern.  It cannot be used to certify a full-root temporal
        action on the real 196 trajectory by itself.
        """
        self.validate_source_authority()
        if owner is not self.owner:
            raise ValueError("cannot square a foreign owner's conditional action")
        if self.border_certificate is not None:
            # A growth proof for D is NOT a proof for 2D. Re-run the exact
            # finite edge relation from the same original source. Refuse if
            # either its width or its carry branches stop being decisive.
            renewed = owner.certify_border_growth(
                self.source,
                steps=self.steps * 2,
                window_digits=self.border_certificate.window_digits,
            )
            control: tuple[int, ...] | CertifiedBorderGrowth = renewed
        else:
            control = self.growth_control
        return authorize_controlled_gt_bank(
            owner,
            self.source,
            steps=self.steps * 2,
            coordinate=self.coordinate,
            period_size=len(self.period),
            growth_control=control,
        )


def _source_period(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    steps: int,
    coordinate: int,
    period_size: int,
) -> tuple[tuple[int, ...], int]:
    owner.validate(source)
    if type(steps) is not int or steps < 1:
        raise ValueError("temporal bank requires at least one step")
    if type(period_size) is not int or not 1 <= period_size <= 32:
        raise ValueError("exact periodic bank requires a period of 1..32")
    if type(coordinate) is not int or not 0 <= coordinate < source.pair_width:
        raise IndexError(coordinate)
    halo = required_protected_halo(period_size, steps) + 2
    if coordinate - halo < 0 or coordinate + halo >= source.pair_width:
        raise UniformConeNotAuthorized(
            "conditional GT bank lacks a protected source halo"
        )
    anchor = coordinate - coordinate % period_size
    period = tuple(owner._pair_value_at(source, anchor + j) for j in range(period_size))
    if all(x == 9 for x in period):
        raise UniformConeNotAuthorized(
            "all-EQ band needs two future exterior carry ports"
        )
    if not _periodic_guard(
        owner, source, coordinate - halo, coordinate + halo + 1, period
    ):
        raise UniformConeNotAuthorized("exact LT/GT/F5 spatial bank guard mismatch")
    return period, halo


def _finite_proved_action(
    period: tuple[int, ...],
    word: tuple[int, ...],
    *,
    workspace_reserve: Callable[[int, int], None],
) -> MixedTemporalAction:
    """One finite border-certified port program if its cyclic bank has no orbit.

    This fallback does not claim a finite Moore quotient, and its work is
    linear in the already PROVED short control word. Unlike a physical
    chronological fallback, it never requests any intermediate Q19 source.
    """
    workspace_reserve(
        8 + len(word) * (8 + 8 * len(period)),
        2 * len(word) + 1,
    )
    arena = MixedOutputArena()
    current = MixedPeriodicCore(period)
    root = 0
    for bit in word:
        current, frame = current.advance(bit)
        root = arena.concat(root, arena.emit(frame))
    arena.freeze()
    return MixedTemporalAction(
        MixedPeriodicCore(period),
        current,
        len(word),
        word,
        root,
        arena,
        len(word) + 1,
        0,
    )


def authorize_controlled_gt_bank(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    *,
    steps: int,
    coordinate: int,
    period_size: int = 2,
    growth_control: tuple[int, ...] | CertifiedBorderGrowth,
    max_states: int = 10000,
) -> SourceGuardedGTBankAction:
    """Compile the full GT-high bank at a live Q19 source, CONDITIONAL on growth.

    A growth word is never a trust flag or a whole-integer theorem.  Only the
    spatial periodicity and its resetting halo are checked from the exact
    source SLP.  The width DFA rejects impossible control words and the bank
    refuses unresolved all-EQ exits, rather than fabricating carry ports.
    """
    border_certificate = (
        growth_control if type(growth_control) is CertifiedBorderGrowth else None
    )
    if border_certificate is not None:
        border_certificate.validate(owner, source)
        if steps != len(border_certificate.growth_word):
            raise ValueError("certified border depth does not match bank depth")
        word = border_certificate.growth_word
    elif type(growth_control) is tuple:
        word = growth_control
    else:
        raise TypeError(
            "growth control must be a tuple or an issued border certificate"
        )
    if not word or len(word) > 128:
        raise ValueError(
            "border word must be a finite nonempty tuple of at most 128 bits"
        )
    if any(type(bit) is not int or bit not in (0, 1) for bit in word):
        raise ValueError("border bits must be 0 or 1")
    # Refuse impossible run words BEFORE spending source-guard resources.
    whole, tail = divmod(steps, len(word))
    width = (
        WidthMacro.from_bits(word).repeat(whole).then(WidthMacro.from_bits(word[:tail]))
        if type(steps) is int and steps >= 0
        else None
    )
    if width is None or not width.admitted():
        raise IncompleteMixedBorder(
            "growth control violates the universal width theorem"
        )
    period, halo = _source_period(
        owner, source, steps=steps, coordinate=coordinate, period_size=period_size
    )
    with _controlled_bank_workspace(owner.ledger, owner._scratch_owner) as reserve:
        try:
            bank = ControlledMixedBank(
                MixedPeriodicCore(period),
                word,
                max_states=max_states,
                workspace_reserve=reserve,
            )
            action = bank.power(steps)
        except IncompleteMixedBorder:
            if border_certificate is None:
                raise
            action = _finite_proved_action(period, word, workspace_reserve=reserve)
        record = object.__new__(SourceGuardedGTBankAction)
        registry_key = owner._issuance_registry.allocate_bank_key()
        values = {
            "owner": owner,
            "source": source,
            "coordinate": coordinate,
            "steps": steps,
            "period": period,
            "growth_control": word,
            "halo": halo,
            "action": action,
            "full_integer_certified": False,
            "control_certified": border_certificate is not None,
            "border_certificate": border_certificate,
            "_registry_key": registry_key,
        }
        issue_q19_record(record, values, _ISSUER)
        owner._issuance_registry.retain_bank(registry_key, record)
        try:
            record.__post_init__()
        except BaseException:
            owner._issuance_registry.discard_bank(registry_key, record)
            raise
    owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_CONDITIONAL_GT_BANK_ISSUED)
    owner.ledger.bump(
        _reverse_add_keys.REVERSE_Q19_CONDITIONAL_GT_BANK_OUTPUT_NODES,
        action.program_nodes,
    )
    return record


def conditional_alternating_first_growth(
    source: AlternatingCore,
    *,
    quiet_steps: int,
) -> ConditionalEQGrowthExit | UniformCarryCell:
    """Port-parametric LT/GT bank exit, NOT a certified border itinerary.

    A genuine future border control must attest the first-growth index.
    All ten EQ-producing phase exits preserve four carry alternatives.
    """
    if type(quiet_steps) is not int or quiet_steps < 0:
        raise ValueError("quiet interval must be nonnegative")
    if not WidthMacro.from_bits((0,) * quiet_steps + (1,)).admitted():
        raise IncompleteMixedBorder(
            "first-growth control exceeds universal quiet bound"
        )
    # Power a protected quiet phase and only then take the conditional exit.
    power_alternating_outputs(source, quiet_steps, quiet_guarded=True)
    return conditional_first_growth_exit(source, quiet_steps, quiet_guarded=True)


__all__ = [
    "SourceGuardedGTBankAction",
    "authorize_controlled_gt_bank",
    "conditional_alternating_first_growth",
]
