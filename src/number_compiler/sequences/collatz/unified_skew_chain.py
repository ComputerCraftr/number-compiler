"""One guarded border/helix action across consecutive admitted macro seams.

Compose the exact action, 2-adic guards, prefix sums, signed parity input
program, physical/normalized clocks, width ledger, and (when demanded) the
skew-cylinder quadratic jet at the SAME seam. Only producer-issued border
and skew actions may advance the state. No speculative clock selects a branch.

This is a bounded opportunistic composer, with complete terminal certificates
when its endpoint is 1. Otherwise an authenticated prefix is applied and the
ordinary exact source selector handles the continuation. No universal terminal
or constant-work theorem is assumed.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import asdict, dataclass, field
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.radial_sturmian import (
    RadialSturmianClock,
    RadialSturmianPacket,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_89_AT_NINE,
    CollatzSegmentIdentity,
    NonBorderSegment,
)
from number_compiler.sequences.collatz.border_return_grammar import (
    BorderReturnMacro,
)
from number_compiler.sequences.collatz.boundary_macros import (
    CollatzBoundaryMacro,
    admit_boundary_macro_plan,
)
from number_compiler.sequences.collatz.boundary_templates import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.guarded_skew_power import (
    GuardedSkewCylinderPower,
)
from number_compiler.sequences.collatz.joint_radix_border import JointRadix6Source
from number_compiler.sequences.collatz.radial_boundary_coupling import (
    CollatzRadialBoundarySeam,
)
from number_compiler.sequences.collatz.terminal_preimage import (
    CollatzTerminalPower2Macro,
)
from number_compiler.sequences.collatz.unified_skew_clock import SkewQuadraticClock

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.skew_cylinder_repeat import (
        RepeatedWordMooreCylinder,
    )
    from number_compiler.sequences.collatz.source_closed_port_action import (
        SourceClosedPortAction,
    )

FactorSpecs = tuple[tuple[tuple[int, ...], int], ...]
BoundaryWitness = CollatzBoundaryMacro | BorderReturnMacro
SeamWitness = BoundaryWitness | CollatzTerminalPower2Macro
_ISSUER = object()


def _segment_observation(identity: CollatzSegmentIdentity) -> dict[str, object]:
    if isinstance(identity, NonBorderSegment):
        return {"kind": "segment", "value": identity.value}
    return identity.observation()


@dataclass(frozen=True, slots=True, init=False)
class UnifiedSkewChain:
    """One authenticated executable action; source remains occurrence payload."""

    source: int
    endpoint: int
    fields: DyadicTerminalFieldAction
    width_blank: BlankLedger
    clock: SkewQuadraticClock | None
    odd_symbols: int
    factors: FactorSpecs
    segment_identities: tuple[CollatzSegmentIdentity, ...]
    first_boundary: tuple[int, BoundaryWitness] | None
    seams: tuple[CollatzRadialBoundarySeam, ...]
    repeat_cylinder: RepeatedWordMooreCylinder | None
    _issuer: object = field(repr=False, compare=False)
    _binding: tuple[object, ...] = field(repr=False, compare=False)

    def __init__(self) -> None:
        raise TypeError("composed Collatz actions require source-certified admission")

    @classmethod
    def _issue(
        cls,
        source: int,
        endpoint: int,
        fields: DyadicTerminalFieldAction,
        width_blank: BlankLedger,
        clock: SkewQuadraticClock | None,
        odd_symbols: int,
        factors: FactorSpecs,
        segment_identities: tuple[CollatzSegmentIdentity, ...],
        first_boundary: tuple[int, BoundaryWitness] | None,
        seams: tuple[CollatzRadialBoundarySeam, ...],
        repeat_cylinder: RepeatedWordMooreCylinder | None = None,
    ) -> UnifiedSkewChain:
        chain = object.__new__(cls)
        binding = (
            source,
            endpoint,
            fields,
            width_blank,
            clock,
            odd_symbols,
            factors,
            segment_identities,
            first_boundary,
            seams,
            repeat_cylinder,
        )
        for name, value in zip(
            (
                "source",
                "endpoint",
                "fields",
                "width_blank",
                "clock",
                "odd_symbols",
                "factors",
                "segment_identities",
                "first_boundary",
                "seams",
                "repeat_cylinder",
            ),
            binding,
            strict=True,
        ):
            object.__setattr__(chain, name, value)
        object.__setattr__(chain, "_issuer", _ISSUER)
        chain.verify_issued()
        object.__setattr__(chain, "_binding", chain._snapshot())
        return chain

    def _snapshot(self) -> tuple[object, ...]:
        """Small immutable publication seal; later observations stay cheap."""
        f, w, c = self.fields, self.width_blank, self.clock
        return (
            self.source,
            self.endpoint,
            self.odd_symbols,
            self.factors,
            self.segment_identities,
            self.first_boundary,
            id(self.seams),
            tuple(
                (
                    id(seam),
                    seam.identity,
                    seam.source,
                    seam.endpoint,
                    seam.odd_symbols,
                    id(seam.action),
                    id(seam.witness),
                    seam.joint_source,
                    seam.joint_endpoint,
                )
                for seam in self.seams
            ),
            None
            if self.repeat_cylinder is None
            else (
                id(self.repeat_cylinder),
                self.repeat_cylinder.publication_snapshot(),
            ),
            (id(f), f.coefficient_snapshot()),
            (id(w), w.delta, w.minimum, w.maximum),
            None
            if c is None
            else (
                id(c),
                c.precision,
                c.steps,
                c.odds,
                c.value,
                c.linear,
                c.quadratic,
                c.position_sum,
                c.first_odd,
                c.last_odd,
            ),
        )

    @property
    def reaches_terminal(self) -> bool:
        return self.endpoint == 1

    @property
    def normalized_symbols(self) -> int:
        return self.fields.steps

    @property
    def physical_ticks(self) -> int:
        return self.fields.steps + self.odd_symbols

    def verify(self) -> None:
        if (
            type(self) is not UnifiedSkewChain
            or getattr(self, "_issuer", None) is not _ISSUER
        ):
            raise ValueError("unified skew publication seal is invalid")
        if self.repeat_cylinder is not None:
            from number_compiler.sequences.collatz.skew_cylinder_repeat import (
                RepeatedWordMooreCylinder,
            )

            if type(self.repeat_cylinder) is not RepeatedWordMooreCylinder:
                raise ValueError("unified skew repeat cylinder is not issued")
            self.repeat_cylinder.verify_for(self.fields, self.source)
        if self._binding != self._snapshot():
            raise ValueError("unified skew publication seal is invalid")

    def verify_issued(self) -> None:
        """Do the full source/action/clock proof once, before publication."""
        from number_compiler.sequences.collatz.skew_cylinder_repeat import (
            RepeatedWordMooreCylinder,
        )

        if (
            type(self.source) is not int
            or self.source <= 0
            or type(self.endpoint) is not int
            or self.endpoint <= 0
            or type(self.odd_symbols) is not int
            or self.odd_symbols < 0
            or type(self.fields) is not DyadicTerminalFieldAction
            or not self.fields.producer_issued
            or type(self.width_blank) is not BlankLedger
            or (self.clock is not None and type(self.clock) is not SkewQuadraticClock)
            or len(self.segment_identities) < 2
            or (
                self.repeat_cylinder is not None
                and type(self.repeat_cylinder) is not RepeatedWordMooreCylinder
            )
            or (self.clock is not None and self.odd_symbols != self.clock.odds)
            or (self.clock is not None and self.fields.steps != self.clock.steps)
            or self.width_blank.delta
            != self.endpoint.bit_length() - self.source.bit_length()
            or len(self.seams) != len(self.segment_identities)
            or sum(len(motif) * count for motif, count in self.factors)
            != self.fields.steps
            or sum(sum(motif) * count for motif, count in self.factors)
            != self.odd_symbols
        ):
            raise ValueError("unified skew action has inconsistent clocks")
        if self.repeat_cylinder is not None:
            self.repeat_cylinder.verify_for(self.fields, self.source)
            if not self.repeat_cylinder.admits(2):
                raise ValueError("unified skew repeat cylinder misses its square")
        if not self.fields.certifies(self.source):
            raise ValueError("unified skew fields do not certify their source")
        if self.fields.endpoint(self.source) != self.endpoint:
            raise ValueError("unified skew endpoint differs from its source action")
        if self.clock is not None:
            self.clock.verify(self.fields, self.source, self.endpoint)
            if (
                SkewQuadraticClock.factors(self.factors, self.clock.precision)
                != self.clock
            ):
                raise ValueError("unified skew factor grammar disagrees with its clock")
        current = self.source
        expected_radix_state = JointRadix6Source.from_source(self.source)
        seam_steps = seam_odds = 0
        for identity, seam in zip(self.segment_identities, self.seams, strict=True):
            seam.verify()
            if seam.identity != identity or seam.source != current:
                raise ValueError("unified skew seam does not continue its source guard")
            if seam.joint_source != expected_radix_state:
                raise ValueError("unified skew F5/CRT state lost seam continuity")
            expected_radix_state = expected_radix_state.after_action(
                seam.action, seam.endpoint, seam.odd_symbols
            )
            if seam.joint_endpoint != expected_radix_state:
                raise ValueError("unified skew F5/CRT action lost endpoint continuity")
            current = seam.endpoint
            seam_steps += seam.normalized_steps
            seam_odds += seam.odd_symbols
        if (
            current != self.endpoint
            or seam_steps != self.fields.steps
            or seam_odds != self.odd_symbols
        ):
            raise ValueError("unified skew seams disagree with the powered action")

    def radial_leading_binary(
        self, evaluator: GrowthArithmeticEvaluator, width: int = 8
    ) -> RadialSturmianPacket:
        """Join the certified macro with the exact multiplier rotation.

        This does not assert a prefix of ``endpoint``: the affine innovation
        must first be handled by a separate, source-bound carry/borrow port.
        A source-free finite rotation table can never authorize this chain.
        """
        self.verify()
        radial = RadialSturmianClock(
            HomogeneousGrowthScale(self.odd_symbols, self.fields.steps)
        )
        if self.clock is not None and self.clock.radial_sturmian_clock != radial:
            raise ValueError("unified skew macro radial port disagrees with clock")
        return radial.leading_binary(evaluator, width)

    def source_closed_port_action(
        self, *, ledger: ResourceLedger | None = None
    ) -> SourceClosedPortAction:
        """Compile issued seams into one exact finite source congruence."""
        from number_compiler.sequences.collatz.source_closed_port_action import (
            SourceClosedPortAction,
        )

        return SourceClosedPortAction.from_chain(self, ledger=ledger)

    def source_closed_temporal_power(
        self,
        repetitions: int,
        *,
        max_coefficient_bits: int = 8192,
        ledger: ResourceLedger | None = None,
    ) -> SourceClosedPortAction | None:
        """Power this recorded word only when all of its seam guards repeat."""
        return self.source_closed_port_action(ledger=ledger).power(
            repetitions,
            max_coefficient_bits=max_coefficient_bits,
            ledger=ledger,
        )

    def guarded_temporal_power(
        self,
        repetitions: int,
        *,
        preflight: Callable[[int], None],
    ) -> GuardedSkewCylinderPower:
        """Admit repetition of this exact normalized word from its source.

        The returned cylinder concerns this recorded parity word only. It
        does not repeat the named-family selectors at their later endpoints.
        Coefficient and endpoint construction remains a separate demanded,
        preflighted operation on the returned power.
        """

        self.verify()
        return GuardedSkewCylinderPower.from_chain(
            self, repetitions, preflight=preflight
        )

    def observation(
        self,
        *,
        radial_evaluator: GrowthArithmeticEvaluator | None = None,
        radial_prefix_width: int = 8,
        difference_places: int = 0,
        include_walsh64: bool = False,
        position_spectrum_requests: tuple[tuple[int, int], ...] = (),
        odd_position_moore_requests: tuple[tuple[int, int], ...] = (),
        position_moore_walsh64: bool = False,
        ledger: ResourceLedger | None = None,
    ) -> dict[str, object]:
        self.verify()
        from number_compiler.sequences.collatz.boundary_observation import (
            validate_position_requests,
        )

        validate_position_requests(
            position_spectrum_requests,
            odd_position_moore_requests,
            position_moore_walsh64,
        )
        clock = self.clock
        packet = (
            self.radial_leading_binary(radial_evaluator, radial_prefix_width)
            if radial_evaluator is not None
            else None
        )
        seam_packets: list[dict[str, object]] | None = None
        repeated: dict[str, object] | None = None
        if radial_evaluator is not None:
            seam_packets = []
            earlier_odds = earlier_halvings = 0
            for index, seam in enumerate(self.seams):
                seam_packets.append(
                    seam.observation(
                        radial_evaluator,
                        width=radial_prefix_width,
                        previous_odds=earlier_odds,
                        previous_halvings=earlier_halvings,
                        next_identity=(
                            self.seams[index + 1].identity
                            if index + 1 < len(self.seams)
                            else None
                        ),
                        difference_places=difference_places,
                        include_walsh64=include_walsh64,
                    )
                )
                earlier_odds += seam.odd_symbols
                earlier_halvings += seam.normalized_steps
            if (earlier_odds, earlier_halvings) != (
                self.odd_symbols,
                self.fields.steps,
            ):
                raise AssertionError("radial boundary seam count lost composition")

            cylinder, power = GuardedSkewCylinderPower.inspect_chain(
                self, 2, evaluator=radial_evaluator
            )
            repeated = {
                "fixed_point_denominator": cylinder.fixed_point_denominator,
                "two_adic_defect": cylinder.defect,
                "repeat_moore_class": cylinder.remaining_repetitions,
                "infinite_repeat_class": cylinder.defect == 0,
                "square_admitted": cylinder.admits_square,
                "scope": "repeat of the whole source-admitted parity word only",
            }
            if power is not None:
                repeated.update(power.observation(radial_evaluator))
        if type(difference_places) is not int or not 0 <= difference_places <= 64:
            raise ValueError("difference-port demand must be within 0..64")
        if type(include_walsh64) is not bool:
            raise TypeError("Walsh64 demand must be Boolean")
        guarded_ports = (
            self.source_closed_port_action(ledger=ledger)
            if difference_places or include_walsh64 or odd_position_moore_requests
            else None
        )
        conditional_position_moore = (
            tuple(
                guarded_ports.demanded_odd_position_moore(
                    self.source,
                    radix,
                    position,
                    include_walsh64=position_moore_walsh64,
                )
                for radix, position in odd_position_moore_requests
            )
            if guarded_ports is not None and odd_position_moore_requests
            else ()
        )
        returned_position_spectra: list[dict[str, object]] = []
        if position_spectrum_requests:
            from number_compiler.sequences.collatz.border_return_grammar import (
                BorderReturnMacro,
            )
            from number_compiler.sequences.collatz.boundary_macros import (
                CollatzBoundaryMacro,
            )

            for seam_index, seam in enumerate(self.seams):
                witness = seam.witness
                if type(witness) is BorderReturnMacro:
                    family = "6305R"
                    harmonic_method = witness.demanded_position_harmonics
                elif type(witness) is CollatzBoundaryMacro:
                    family = witness.display_label
                    harmonic_method = witness.demanded_motif_position_harmonics
                else:
                    continue
                for radix, position in position_spectrum_requests:
                    returned_position_spectra.append(
                        {
                            "seam_index": seam_index,
                            "family": family,
                            "harmonic": harmonic_method(radix, position).observation(),
                        }
                    )
        joint_difference = None
        if (
            guarded_ports is not None
            and guarded_ports.odd_events
            and (difference_places or include_walsh64)
        ):
            radix_places = (
                {
                    3: difference_places,
                    6: difference_places,
                    10: difference_places,
                    64: 64,
                }
                if include_walsh64 and difference_places
                else ({64: 64} if include_walsh64 else {6: difference_places})
            )
            joint_difference = guarded_ports.demanded_ports(
                self.source,
                base=64 if include_walsh64 else 6,
                places=64 if include_walsh64 else difference_places,
                walsh=include_walsh64,
                radix_places=radix_places,
                ledger=ledger,
            )
        return {
            **(
                {
                    "source_closed_cross_family_ports": {
                        "guard_modulus": guarded_ports.guard.modulus,
                        "guard_residue": guarded_ports.guard.residue,
                        "source_guard_admitted": guarded_ports.admits(self.source),
                        "source_trace_mod160": guarded_ports.source_trace,
                        "joint_radial_scale": (
                            guarded_ports.odd_events,
                            guarded_ports.action.steps,
                        ),
                        "root_difference_ports": joint_difference,
                        "scope": (
                            "same normalized word and finite seam guards; "
                            "not maximal named-family authority"
                        ),
                    }
                }
                if guarded_ports is not None
                else {}
            ),
            "coupled_radix6_selector": tuple(
                {
                    "source_f5": seam.joint_source.residue5,
                    "endpoint_f5": seam.joint_endpoint.residue5,
                    "next_candidate": (
                        _segment_observation(seam.joint_endpoint.candidate_family)
                        if seam.joint_endpoint.candidate_family is not None
                        else None
                    ),
                    "candidate_is_not_source_authority": True,
                }
                for seam in self.seams
                if seam.joint_source is not None and seam.joint_endpoint is not None
            ),
            **(
                {"coupled_radial_boundary_seams": seam_packets}
                if seam_packets is not None
                else {}
            ),
            **(
                {"conditional_odd_position_moore": conditional_position_moore}
                if odd_position_moore_requests
                else {}
            ),
            **(
                {"admitted_border_position_harmonics": tuple(returned_position_spectra)}
                if position_spectrum_requests
                else {}
            ),
            **({"repeated_skew_cylinder": repeated} if repeated is not None else {}),
            **({"radial_sturmian": asdict(packet)} if packet is not None else {}),
            "segments": tuple(
                _segment_observation(item) for item in self.segment_identities
            ),
            "physical_ticks": self.physical_ticks,
            "normalized_steps": self.normalized_symbols,
            "odd_symbols": self.odd_symbols,
            "guard_bits": self.fields.steps,
            "guard_residue": self.source % (1 << self.fields.steps),
            "quadratic_clock_published": clock is not None,
            "skew_ray_prefix": clock.ray_prefix if clock is not None else None,
            "quadratic_return_clock": clock.return_clock if clock is not None else None,
            "skew_linear": clock.linear if clock is not None else None,
            "skew_quadratic": clock.quadratic if clock is not None else None,
            "helix_precision": clock.precision if clock is not None else None,
            "endpoint": self.endpoint,
            "terminal_entry_certified": self.reaches_terminal,
            "scope": "source-certified compositional prefix; terminal only at exact 1",
        }

    @classmethod
    def select_from_source(
        cls,
        source: int,
        available_physical_ticks: int,
        *,
        templates: BoundaryActionTemplateMemo,
        max_segments: int = 12,
        precision: int = 32,
        preflight: Callable[[int], None] | None = None,
        ledger: ResourceLedger | None = None,
        include_quadratic_clock: bool = True,
        preserve_ordinary_mixed_parent: bool = False,
    ) -> UnifiedSkewChain | None:
        """Join certified macro segments before falling back to D8.

        Terminal equality is checked when reached; otherwise sufficiently long
        prefixes can still be applied as one guarded action. When requested, the
        quadratic jet verifies the SAME action; it is never a branch oracle.
        """
        if type(source) is not int or source <= 0:
            raise ValueError("skew chain requires a positive source")
        if type(available_physical_ticks) is not int or available_physical_ticks < 0:
            raise ValueError("skew chain physical budget must be nonnegative")
        if type(max_segments) is not int or not 2 <= max_segments <= 12:
            raise ValueError("skew chain requires a bounded join budget")
        if type(include_quadratic_clock) is not bool:
            raise TypeError("quadratic clock request must be Boolean")
        if type(preserve_ordinary_mixed_parent) is not bool:
            raise TypeError("mixed parent preference must be Boolean")
        from number_compiler.sequences.collatz.skew_cylinder_repeat import (
            RepeatedWordMooreCylinder,
        )
        from number_compiler.sequences.collatz.unified_skew_admission import (
            admit_next_unified_segment,
        )

        if ledger is not None and type(ledger) is not ResourceLedger:
            raise TypeError("unified skew selection requires its query ledger")
        if ledger is not None:
            ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_SELECTOR_CHECKS)

        # Admit a cheap parent before entering the multi-seam composer. This is
        # only a source/clock classification; exact family selectors below still
        # issue every action and endpoint guard.
        joint_state = JointRadix6Source.from_source(source)
        parent_plan = admit_boundary_macro_plan(
            source,
            available_physical_ticks,
            minimum_repetitions=1,
            radix_state=joint_state,
            ledger=ledger,
        )
        terminal_parent = False
        if source & 1 and source > 1:
            numerator = 3 * source + 1
            terminal_parent = (
                numerator & (numerator - 1) == 0
                and numerator.bit_length() <= available_physical_ticks
            )
        border_parent = (
            available_physical_ticks >= 4 and joint_state.border_parent_candidate
        )
        # Ordinary requests preserve the existing 989-to-mixed-cache precedence.
        # Observer requests still compose 989 when its clock, joint action, or tape
        # is needed; ordinary cacheable requests leave this family to its owner.
        if (
            preserve_ordinary_mixed_parent
            and parent_plan is not None
            and parent_plan.identity == ENTRY_89_AT_NINE
        ):
            if ledger is not None:
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_EXISTING_MIXED_PARENT_YIELDS
                )
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_SELECTION_OPERAND_BITS,
                    source.bit_length() + max(1, available_physical_ticks.bit_length()),
                )
            return None
        if parent_plan is None and not terminal_parent and not border_parent:
            if ledger is not None:
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_PARENT_REJECTIONS
                )
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_SELECTION_OPERAND_BITS,
                    source.bit_length() + max(1, available_physical_ticks.bit_length()),
                )
            return None
        if ledger is not None:
            ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_PARENT_ADMISSIONS)

        current = source
        used = 0
        fields = DyadicTerminalFieldAction.identity()
        width = BlankLedger()
        clock = (
            SkewQuadraticClock.identity(precision) if include_quadratic_clock else None
        )
        odd_symbols = 0
        factors: list[tuple[tuple[int, ...], int]] = []
        segment_identities: list[CollatzSegmentIdentity] = []
        seams: list[CollatzRadialBoundarySeam] = []
        first_boundary: tuple[int, BoundaryWitness] | None = None
        discarded_bits = 0
        repeat_cylinder: RepeatedWordMooreCylinder | None = None
        for segment_index in range(max_segments):
            if current == 1:
                break
            candidate_bits = current.bit_length() + max(
                1, (available_physical_ticks - used).bit_length()
            )
            if ledger is not None:
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_SELECTION_OPERAND_BITS,
                    candidate_bits,
                )
            admitted = admit_next_unified_segment(
                current,
                available_physical_ticks - used,
                templates,
                preflight,
                ledger=ledger,
                initial_plan=parent_plan if segment_index == 0 else None,
                initial_plan_checked=segment_index == 0,
                radix_state=joint_state,
            )
            if admitted is None:
                if ledger is not None:
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_REJECTED_PREFIXES
                    )
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_DISCARDED_OPERAND_BITS,
                        discarded_bits + current.bit_length(),
                    )
                break
            identity, odds, segment, blank, specs, witness = admitted
            segment_bits = (
                current.bit_length()
                + max(1, (available_physical_ticks - used).bit_length())
                + sum(
                    max(1, value.bit_length())
                    for value in (
                        segment.steps,
                        segment.gain,
                        segment.offset,
                        segment.sum_gain,
                        segment.sum_offset,
                        segment.previous_gain,
                        segment.previous_offset,
                    )
                )
            )
            if ledger is not None:
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_SELECTOR_SEGMENTS
                )
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_SELECTION_OPERAND_BITS,
                    segment_bits,
                )
            ticks = segment.steps + odds
            if ticks <= 0 or ticks > available_physical_ticks - used:
                if ledger is not None:
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_REJECTED_PREFIXES
                    )
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_DISCARDED_OPERAND_BITS,
                        discarded_bits + segment_bits,
                    )
                return None
            if not segment.certifies(current):
                raise AssertionError("composite producer admitted a foreign source")
            endpoint = segment.endpoint(current)
            next_joint_state = joint_state.after_action(segment, endpoint, odds)
            if clock is not None:
                subclock = SkewQuadraticClock.factors(specs, precision)
                subclock.verify(segment, current, endpoint)
                if ledger is not None:
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_CLOCK_CHECKS
                    )
            else:
                subclock = None
            if first_boundary is None and isinstance(
                witness, (CollatzBoundaryMacro, BorderReturnMacro)
            ):
                first_boundary = (used, witness)
            seams.append(
                CollatzRadialBoundarySeam(
                    identity,
                    current,
                    endpoint,
                    odds,
                    segment,
                    witness,
                    joint_state,
                    next_joint_state,
                )
            )
            # One chronological composition updates exact endpoint, accumulator,
            # predecessor, width, helix, innovation and both clocks together.
            # Reserve for the cumulative action before the exact composition can
            # allocate its larger integer coefficients.
            if preflight is not None:
                preflight(fields.steps + segment.steps)
            fields = fields.then(segment)
            width = width.then(blank)
            if clock is not None and subclock is not None:
                clock = clock.then(subclock)
            odd_symbols += odds
            used += ticks
            current = endpoint
            joint_state = next_joint_state
            factors.extend(specs)
            segment_identities.append(identity)
            discarded_bits += segment_bits
            if (
                preflight is not None
                and len(segment_identities) >= 2
                and used * 2 <= available_physical_ticks
            ):
                if ledger is not None:
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_REPEAT_GUARD_CHECKS
                    )
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_REPEAT_GUARD_OPERAND_BITS,
                        source.bit_length()
                        + fields.steps
                        + fields.gain.bit_length()
                        + abs(fields.offset).bit_length(),
                    )
                try:
                    repeat_candidate = RepeatedWordMooreCylinder.from_action(
                        fields, source, preflight=preflight
                    )
                except BlockContextBudgetExceeded:
                    if ledger is not None:
                        ledger.bump(
                            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_REPEAT_GUARD_BUDGET_REFUSALS
                        )
                else:
                    if repeat_candidate.admits(2):
                        repeat_cylinder = repeat_candidate
                        if ledger is not None:
                            ledger.bump(
                                _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_REPEAT_GUARD_ADMISSIONS
                            )
                        break
                    if ledger is not None:
                        ledger.bump(
                            _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_REPEAT_GUARD_REJECTIONS
                        )
            if (
                fields.steps + odd_symbols != used
                or (clock is not None and clock.physical_ticks != used)
                or fields.endpoint(source) != current
            ):
                raise AssertionError("combined border/helix clocks lost their seam")

        if len(segment_identities) < 2 or (
            current != 1 and used < 16 and repeat_cylinder is None
        ):
            if ledger is not None:
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_REJECTED_PREFIXES
                )
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_DISCARDED_OPERAND_BITS,
                    discarded_bits,
                )
            return None
        chain = cls._issue(
            source,
            current,
            fields,
            width,
            clock,
            odd_symbols,
            tuple(factors),
            tuple(segment_identities),
            first_boundary,
            tuple(seams),
            repeat_cylinder,
        )
        if ledger is not None:
            if clock is not None:
                ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_CLOCK_CHECKS, 2)
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_CHAIN_RETAINED_OPERAND_BITS,
                _chain_operand_bits(chain),
            )
        return chain


def select_unified_skew_chain(
    source: int,
    available_physical_ticks: int,
    *,
    templates: BoundaryActionTemplateMemo,
    max_segments: int = 12,
    precision: int = 32,
    preflight: Callable[[int], None] | None = None,
    ledger: ResourceLedger | None = None,
    include_quadratic_clock: bool = True,
    preserve_ordinary_mixed_parent: bool = False,
) -> UnifiedSkewChain | None:
    """Select a source-closed chain through the class-owned source factory."""
    return UnifiedSkewChain.select_from_source(
        source,
        available_physical_ticks,
        templates=templates,
        max_segments=max_segments,
        precision=precision,
        preflight=preflight,
        ledger=ledger,
        include_quadratic_clock=include_quadratic_clock,
        preserve_ordinary_mixed_parent=preserve_ordinary_mixed_parent,
    )


def _chain_operand_bits(chain: UnifiedSkewChain) -> int:
    """Count the integer payload bits retained by the composite certificate."""
    values: tuple[int, ...] = (
        chain.source,
        chain.endpoint,
        chain.fields.steps,
        chain.fields.gain,
        chain.fields.offset,
        chain.fields.sum_gain,
        chain.fields.sum_offset,
        chain.fields.previous_gain,
        chain.fields.previous_offset,
        chain.width_blank.delta,
        chain.width_blank.minimum,
        chain.width_blank.maximum,
    )
    clock_values: tuple[int, ...] = (
        ()
        if chain.clock is None
        else (
            chain.clock.precision,
            chain.clock.steps,
            chain.clock.odds,
            chain.clock.value,
            chain.clock.linear,
            chain.clock.quadratic,
            chain.clock.position_sum,
        )
    )
    retained_bits = 0
    for value in (*values, *clock_values):
        retained_bits += max(1, abs(value).bit_length())
    for motif, count in chain.factors:
        retained_bits += len(motif) + max(1, count.bit_length())
    return retained_bits


__all__ = ["UnifiedSkewChain", "select_unified_skew_chain"]
