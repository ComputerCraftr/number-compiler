"""Typed metadata for exact finite 2rev10 border-child paths."""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.hashlife.interfaces.border_macros import (
    BorderFamilyId,
    BorderMacroIdentity,
    BorderMacroKind,
    BorderMacroPhase,
    BorderSourceCursor,
    require_exact_border_join,
)

from .source_bound_bank import PointedBankSource
from .temporal_carry_safety import LiftedBorder, lift_from_slp, lifted_step
from .temporal_hashlife_types import DoubleReversePortAction
from .temporal_residue_quotient import (
    CertifiedResidueTemporalAction,
    certified_residue_action,
    decimal_residues_from_slp,
)


@dataclass(frozen=True, slots=True)
class ClockedBorderPhase:
    """One exact T-squared child with two lifted steps and clock guards."""

    phase: BorderMacroPhase
    ordinal: int
    source_border: LiftedBorder
    target_border: LiftedBorder
    fourth_digit_carries: tuple[int, int]
    growth: int
    residue_action: CertifiedResidueTemporalAction


@dataclass(frozen=True, slots=True)
class RegisteredBorderMacro:
    """A finite four-physical-tick word, identified by its actual edge path."""

    identity: BorderMacroIdentity
    start_phase: int
    end_phase: int
    width_in: int
    width_out: int
    mod99_in: int
    mod99_out: int
    mod198_in: int
    mod198_out: int
    physical_repeat_certified: bool = False


@dataclass(frozen=True, slots=True)
class SourceBorderMacroCatalogue:
    """Recomputable border evidence over exact owner-issued action children."""

    source: PointedBankSource = field(repr=False, compare=False)
    actions: tuple[DoubleReversePortAction, ...] = field(repr=False, compare=False)
    roots: tuple[int, ...]
    midpoint_roots: tuple[int, ...] = field(repr=False, compare=False)
    pair_depth: int
    phases: tuple[ClockedBorderPhase, ...]
    four_tick_macros: tuple[RegisteredBorderMacro, ...]
    residue99: tuple[int, ...]
    residue198: tuple[int, ...]
    widths: tuple[int, ...]

    def validate(self) -> None:
        from .source_bound_bank import PointedBankSource

        if type(self.source) is not PointedBankSource:
            raise TypeError("2rev10 border catalogue needs an existing source cursor")
        self.source.validate(require_issued_cursor=self.source.f_steps > 0)
        if (
            len(self.roots) != len(self.actions) + 1
            or len(self.midpoint_roots) != len(self.actions)
            or len(self.phases) != len(self.actions)
            or len(self.widths) != len(self.roots)
            or len(self.residue99) != len(self.roots)
            or len(self.residue198) != len(self.roots)
            or type(self.pair_depth) is not int
            or not 1 <= self.pair_depth <= 16
            or self.roots[0] != self.source.root
            or type(self.roots) is not tuple
            or any(type(root) is not int for root in self.roots)
            or type(self.midpoint_roots) is not tuple
            or any(type(root) is not int for root in self.midpoint_roots)
            or any(
                type(action) is not DoubleReversePortAction for action in self.actions
            )
            or self.widths[0] != self.source.width_in
        ):
            raise ValueError("2rev10 border catalogue lost its exact source root")
        initial_residues = decimal_residues_from_slp(
            self.source.arena,
            self.source.root,
            ledger=self.source.ledger,
            scratch_owner=self.source.scratch_owner,
        )
        if (self.residue99[0], self.residue198[0]) != initial_residues:
            raise ValueError("2rev10 border catalogue has a forged initial clock")
        engine = self.source.engine
        current_phase = self.source.phase
        for index, (action, phase) in enumerate(
            zip(self.actions, self.phases, strict=True)
        ):
            engine.validate_action(action)
            source_root, target_root = self.roots[index : index + 2]
            if (
                engine.root_of(action.source) != source_root
                or engine.root_of(action.target) != target_root
                or action.steps != 1
                or action.phase_in != current_phase
                or self.widths[index + 1] - self.widths[index]
                != action.left_births + action.right_births
                or self.widths[index] != self.source.arena.nodes[source_root].length
                or self.widths[index + 1] != self.source.arena.nodes[target_root].length
            ):
                raise ValueError("2rev10 action child is not an exact adjacent phase")
            clock = certified_residue_action(
                phase=action.phase_in,
                width=self.widths[index],
                duration=2,
                source_mod99=self.residue99[index],
                source_mod198=self.residue198[index],
            )
            if (self.residue99[index + 1], self.residue198[index + 1]) != (
                clock.target_mod99,
                clock.target_mod198,
            ):
                raise ValueError("2rev10 border catalogue clock seam was changed")
            if engine.advance_source_root(source_root) != self.midpoint_roots[index]:
                raise ValueError(
                    "2rev10 physical midpoint differs from its exact T child"
                )
            expected_phase = _make_phase(
                self.source,
                index,
                action,
                source_root,
                self.midpoint_roots[index],
                target_root,
                self.widths[index],
                self.residue99[index],
                self.residue198[index],
                clock.target_mod99,
                clock.target_mod198,
                self.pair_depth,
            )
            if (
                phase != expected_phase
                or phase.phase.source.root != source_root
                or phase.phase.target.root != target_root
                or phase.ordinal != index
                or phase.phase.source.pair_depth != self.pair_depth
                or phase.phase.target.pair_depth != self.pair_depth
            ):
                raise ValueError("border macro phase lost its exact owner roots")
            current_phase = action.phase_out
        for earlier, later in zip(self.phases, self.phases[1:]):
            require_exact_border_join(earlier.phase, later.phase)
        if self.four_tick_macros != _four_tick_macros(
            self.phases, self.widths, self.residue99, self.residue198
        ):
            raise ValueError("four-tick macro metadata differs from source phases")


def _state(border: LiftedBorder) -> tuple[object, ...]:
    return border.high, border.low, border.edge


def _make_phase(
    source: PointedBankSource,
    ordinal: int,
    action: DoubleReversePortAction,
    source_root: int,
    midpoint_root: int,
    target_root: int,
    width: int,
    residue99: int,
    residue198: int,
    target99: int,
    target198: int,
    pair_depth: int,
) -> ClockedBorderPhase:
    arena = source.arena
    owner = source.engine
    source_border = lift_from_slp(arena, source_root)
    if type(midpoint_root) is not int or not 0 <= midpoint_root < len(arena.nodes):
        raise ValueError("2rev10 physical midpoint root is outside its arena")
    middle_border = lift_from_slp(arena, midpoint_root)
    target_border = lift_from_slp(arena, target_root)
    source_width = arena.nodes[source_root].length
    middle_width = arena.nodes[midpoint_root].length
    target_width = arena.nodes[target_root].length
    fourth_digit = symbol_at(arena, source_root, source_width - 4)
    first_carry = int(fourth_digit >= 5)
    first_step = lifted_step(source_border, first_carry)
    growth = target_width - source_width
    if (
        first_step.target != middle_border
        or first_step.growth is None
        or middle_width - source_width != first_step.growth
    ):
        raise ValueError("exact 2rev10 border child crosses a shrinking frontier")
    middle_fourth_digit = symbol_at(arena, midpoint_root, middle_width - 4)
    second_carry = int(middle_fourth_digit >= 5)
    second_step = lifted_step(middle_border, second_carry)
    if (
        second_step.target != target_border
        or second_step.growth is None
        or first_step.growth + second_step.growth != growth
        or target_width - middle_width != second_step.growth
    ):
        raise ValueError("exact 2rev10 border child fails its lifted carry guard")
    if width != source_width or action.phase_in != owner.certify(source_root):
        raise ValueError("2rev10 border phase and temporal owner disagree")
    source_cursor = BorderSourceCursor(
        BorderFamilyId.TWO_REVERSE_TEN,
        owner,
        source_root,
        source.physical_prefix + 2 * ordinal,
        pair_depth,
        action.phase_in,
    )
    target_cursor = BorderSourceCursor(
        BorderFamilyId.TWO_REVERSE_TEN,
        owner,
        target_root,
        source.physical_prefix + 2 * (ordinal + 1),
        pair_depth,
        action.phase_out,
    )
    identity = BorderMacroIdentity(
        BorderFamilyId.TWO_REVERSE_TEN,
        BorderMacroKind.EDGE,
        (
            2,
            _state(source_border),
            _state(middle_border),
            _state(target_border),
            (first_carry, second_carry),
            growth,
        ),
    )
    metadata = BorderMacroPhase(
        identity,
        ordinal,
        source_cursor,
        target_cursor,
        _state(source_border),
        _state(target_border),
        source_width,
        target_width,
        (residue99, residue198),
        (target99, target198),
        physical_span=2,
    )
    from .temporal_residue_quotient import certified_residue_action

    clock = certified_residue_action(
        phase=action.phase_in,
        width=source_width,
        duration=2,
        source_mod99=residue99,
        source_mod198=residue198,
    )
    if (
        clock.width_out != target_width
        or clock.target_mod99 != target99
        or clock.target_mod198 != target198
    ):
        raise ValueError("2rev10 border child does not match its 99/198 clock")
    return ClockedBorderPhase(
        metadata,
        ordinal,
        source_border,
        target_border,
        (first_carry, second_carry),
        growth,
        clock,
    )


def _four_tick_macros(
    phases: tuple[ClockedBorderPhase, ...],
    widths: tuple[int, ...],
    residue99: tuple[int, ...],
    residue198: tuple[int, ...],
) -> tuple[RegisteredBorderMacro, ...]:
    macros: list[RegisteredBorderMacro] = []
    for start in range(0, len(phases) - 1, 2):
        word = phases[start : start + 2]
        signature = (
            tuple(_state(phase.source_border) for phase in word),
            tuple(_state(phase.target_border) for phase in word),
            tuple(phase.fourth_digit_carries for phase in word),
            tuple(phase.growth for phase in word),
        )
        identity = BorderMacroIdentity(
            BorderFamilyId.TWO_REVERSE_TEN,
            BorderMacroKind.BURST,
            (4, *signature),
        )
        macros.append(
            RegisteredBorderMacro(
                identity,
                start,
                start + 2,
                widths[start],
                widths[start + 2],
                residue99[start],
                residue99[start + 2],
                residue198[start],
                residue198[start + 2],
            )
        )
    return tuple(macros)


def source_border_macro_catalogue(
    source: PointedBankSource,
    roots: tuple[int, ...],
    actions: tuple[DoubleReversePortAction, ...],
    *,
    pair_depth: int,
) -> SourceBorderMacroCatalogue:
    """Register finite exact Hashlife children and their border/clock guards."""
    from .source_bound_bank import PointedBankSource

    if type(source) is not PointedBankSource:
        raise TypeError("2rev10 border catalogue requires PointedBankSource")
    source.validate(require_issued_cursor=source.f_steps > 0)
    if type(pair_depth) is not int or not 1 <= pair_depth <= 16:
        raise ValueError("pair depth must be in 1..16")
    if (
        type(roots) is not tuple
        or type(actions) is not tuple
        or len(roots) != len(actions) + 1
        or not actions
        or any(type(root) is not int for root in roots)
        or any(type(action) is not DoubleReversePortAction for action in actions)
    ):
        raise ValueError("2rev10 catalogue needs a nonempty exact child path")
    first99, first198 = decimal_residues_from_slp(
        source.arena,
        roots[0],
        ledger=source.ledger,
        scratch_owner=source.scratch_owner,
    )
    widths = [source.arena.nodes[root].length for root in roots]
    residue99 = [first99]
    residue198 = [first198]
    phases: list[ClockedBorderPhase] = []
    midpoint_roots: list[int] = []
    cursor_phase = source.phase
    for index, action in enumerate(actions):
        source.engine.validate_action(action)
        if (
            source.engine.root_of(action.source) != roots[index]
            or source.engine.root_of(action.target) != roots[index + 1]
            or action.steps != 1
            or action.phase_in != cursor_phase
        ):
            raise ValueError("action path does not join exact completed source roots")
        clock = certified_residue_action(
            phase=cursor_phase,
            width=widths[index],
            duration=2,
            source_mod99=residue99[index],
            source_mod198=residue198[index],
        )
        if (
            clock.width_out != widths[index + 1]
            or clock.growth != action.left_births + action.right_births
        ):
            raise ValueError("99/198 clock does not match the exact child width")
        residue99.append(clock.target_mod99)
        residue198.append(clock.target_mod198)
        midpoint_root = source.engine.advance_source_root(roots[index])
        midpoint_roots.append(midpoint_root)
        phases.append(
            _make_phase(
                source,
                index,
                action,
                roots[index],
                midpoint_root,
                roots[index + 1],
                widths[index],
                residue99[index],
                residue198[index],
                clock.target_mod99,
                clock.target_mod198,
                pair_depth,
            )
        )
        cursor_phase = action.phase_out
    phase_tuple = tuple(phases)
    width_tuple = tuple(widths)
    r99_tuple = tuple(residue99)
    r198_tuple = tuple(residue198)
    result = SourceBorderMacroCatalogue(
        source,
        actions,
        roots,
        tuple(midpoint_roots),
        pair_depth,
        phase_tuple,
        _four_tick_macros(phase_tuple, width_tuple, r99_tuple, r198_tuple),
        r99_tuple,
        r198_tuple,
        width_tuple,
    )
    return result


__all__ = [
    "ClockedBorderPhase",
    "RegisteredBorderMacro",
    "SourceBorderMacroCatalogue",
    "source_border_macro_catalogue",
]
