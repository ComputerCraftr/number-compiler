"""Structural metadata for exact finite reverse/add border transitions.

This module describes source-owner-issued child roots.  It does not issue new
source authority, schedule transitions, or treat an observed return as a
repeatable physical word.  Each phase carries its exact owner cursor and both
cyclotomic coordinates so consumers can join guards before matrix products.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import lru_cache
from itertools import pairwise
from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.hashlife.interfaces.border_macros import (
    BorderFamilyId,
    BorderMacroIdentity,
    BorderMacroKind,
    BorderMacroPhase,
    BorderSourceCursor,
    require_exact_border_join,
)

from .border_carry_safety import (
    BilateralCyclePort,
    BorderTile,
    enumerate_one_digit_cycles,
)

if TYPE_CHECKING:
    from .q19_border_control import CertifiedBorderGrowth
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner


def _tile_state(tile: BorderTile) -> tuple[int, int, int]:
    return tile.k, tile.high, tile.low


def _clock_values(
    owner: ReversePairQ19OutputOwner,
    occurrence: ReversePairOutputOccurrence,
) -> tuple[int, int, int]:
    """Read exact width and modular source coordinates from an issued root."""
    owner.validate_issued_occurrence(occurrence)
    width = occurrence.output_width
    residue99 = owner.radix19_cochain(occurrence, z=10, modulus=99).pairs
    parity = owner.digit(occurrence, 0) % 2
    residue198 = residue99 + 99 * ((parity - residue99) % 2)
    return width, residue99, residue198


def _target_clock(
    width: int, residue99: int, residue198: int, port: BilateralCyclePort
) -> tuple[int, int]:
    if residue198 % 99 != residue99 or residue198 % 2 != port.source.low % 2:
        raise ValueError("source border parity disagrees with its cyclotomic clock")
    target99 = residue99 * (2 if width % 2 else 11) % 99
    target_parity = port.target.low % 2
    target198 = target99 + 99 * ((target_parity - target99) % 2)
    return target99, target198


@dataclass(frozen=True, slots=True)
class ClockedBorderPhase:
    """One exact child edge with a typed structural identity and explicit phase."""

    phase: BorderMacroPhase
    tick: int
    width: int
    port: BilateralCyclePort
    residue99: int
    residue198: int
    target99: int
    target198: int

    @property
    def leading(self) -> str:
        return f"{self.port.source.high:0{self.port.source.k}d}"

    @property
    def trailing(self) -> str:
        return f"{self.port.source.low:0{self.port.source.k}d}"

    @property
    def edge_signature(self) -> tuple[object, ...]:
        return self.phase.identity.signature


@dataclass(frozen=True, slots=True)
class RegisteredBorderMacro:
    """An observed contiguous return, identified by its structural word."""

    identity: BorderMacroIdentity
    entry_phase: int
    start: int
    end: int
    phases: tuple[int, ...]
    width_start: int
    width_end: int
    mod99_start: int
    mod99_end: int
    mod198_start: int
    mod198_end: int
    finite_source_certified: bool = True
    physical_repeat_certified: bool = False

    def __post_init__(self) -> None:
        if type(self.identity) is not BorderMacroIdentity:
            raise TypeError("registered macro needs a typed structural identity")
        if type(self.entry_phase) is not int or self.entry_phase < 0:
            raise ValueError("canonical macro entry phase must be nonnegative")
        if self.identity.kind is BorderMacroKind.CYCLE:
            if self.entry_phase >= len(self.phases):
                raise ValueError("cycle entry phase lies outside its canonical word")
        elif self.entry_phase != 0:
            raise ValueError("non-cycle macro entry phase must be zero")

    @property
    def clocks_return(self) -> bool:
        return (
            self.mod99_start == self.mod99_end and self.mod198_start == self.mod198_end
        )


@dataclass(frozen=True, slots=True)
class RegisteredBorderEpisode:
    """A finite skew, growth, quiet, or exit word in exact source phases."""

    identity: BorderMacroIdentity
    kind: BorderMacroKind
    start: int
    end: int
    repeat_units: int
    width_births: int
    growth_word: tuple[int, ...]
    low_carry_word: tuple[int, ...]
    middle_maps: tuple[tuple[str, ...], ...]
    mod99_start: int
    mod99_end: int
    mod198_start: int
    mod198_end: int
    physical_repeat_certified: bool = False

    @property
    def clocks_return(self) -> bool:
        return (
            self.mod99_start == self.mod99_end and self.mod198_start == self.mod198_end
        )


def _edge_signature(port: BilateralCyclePort) -> EdgeSignature:
    return (
        port.source.k,
        _tile_state(port.source),
        _tile_state(port.target),
        port.growth,
        port.low_carry,
        tuple(fn.value for fn in port.admitted_middle),
    )


def _phase_identity(port: BilateralCyclePort) -> BorderMacroIdentity:
    return BorderMacroIdentity(
        BorderFamilyId.REVERSE_ADD,
        BorderMacroKind.EDGE,
        _edge_signature(port),
    )


def _clocked_phases(
    certificate: CertifiedBorderGrowth,
    children: tuple[ReversePairOutputOccurrence, ...],
    ports: tuple[BilateralCyclePort | None, ...],
    growth_word: tuple[int, ...],
    pair_depth: int,
) -> tuple[ClockedBorderPhase | None, ...]:
    from .q19_border_control import CertifiedBorderGrowth
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner

    if type(certificate) is not CertifiedBorderGrowth:
        raise TypeError("clocked phases require an existing Q19 border certificate")
    if (
        type(certificate.owner) is not ReversePairQ19OutputOwner
        or type(children) is not tuple
        or any(type(child) is not ReversePairOutputOccurrence for child in children)
        or type(ports) is not tuple
        or any(type(port) not in (BilateralCyclePort, type(None)) for port in ports)
        or type(growth_word) is not tuple
        or any(
            type(growth) is not int or growth not in (0, 1) for growth in growth_word
        )
    ):
        raise TypeError("clocked phases require exact typed owner records")
    if len(children) != len(ports) + 1 or len(ports) != len(growth_word):
        raise ValueError("source child chain does not cover the physical phases")
    owner = certificate.owner
    result: list[ClockedBorderPhase | None] = []
    for tick, port in enumerate(ports):
        source, target = children[tick], children[tick + 1]
        owner.validate_issued_occurrence(source)
        owner.validate_issued_occurrence(target)
        if target.temporal_steps != source.temporal_steps + 1:
            raise ValueError("reverse/add phase did not join an exact next child")
        if port is None:
            result.append(None)
            continue
        width, residue99, residue198 = _clock_values(owner, source)
        target_width, actual99, actual198 = _clock_values(owner, target)
        expected99, expected198 = _target_clock(width, residue99, residue198, port)
        if (
            width != source.output_width
            or target_width - width != port.growth
            or actual99 != expected99
            or actual198 != expected198
            or target_width - source.output_width != growth_word[tick]
        ):
            raise ValueError("border phase does not match its exact child and clock")
        source_cursor = BorderSourceCursor(
            BorderFamilyId.REVERSE_ADD,
            owner,
            source.root,
            source.temporal_steps,
            pair_depth,
            width % 2,
        )
        target_cursor = BorderSourceCursor(
            BorderFamilyId.REVERSE_ADD,
            owner,
            target.root,
            target.temporal_steps,
            pair_depth,
            target_width % 2,
        )
        signature = _edge_signature(port)
        identity = _phase_identity(port)
        phase = BorderMacroPhase(
            identity,
            tick,
            source_cursor,
            target_cursor,
            _tile_state(port.source),
            _tile_state(port.target),
            width,
            target_width,
            (residue99, residue198),
            (actual99, actual198),
        )
        if phase.identity.signature != signature:
            raise AssertionError("typed edge identity changed while registering")
        result.append(
            ClockedBorderPhase(
                phase, tick, width, port, residue99, residue198, actual99, actual198
            )
        )
    for earlier, later in pairwise(result):
        if earlier is not None and later is not None:
            require_exact_border_join(earlier.phase, later.phase)
    return tuple(result)


def _canonical_cycle(
    states: tuple[tuple[int, int], ...], growth: tuple[int, ...]
) -> tuple[tuple[tuple[int, int], ...], tuple[int, ...]]:
    variants = tuple(
        (
            states[offset:] + states[:offset],
            growth[offset:] + growth[:offset],
        )
        for offset in range(len(states))
    )
    return min(variants)


EdgeSignature = tuple[
    int,
    tuple[int, int, int],
    tuple[int, int, int],
    int,
    int,
    tuple[str, ...],
]


def _canonical_edge_cycle(
    edges: tuple[EdgeSignature, ...],
) -> tuple[tuple[EdgeSignature, ...], int]:
    """Return the full guarded edge word and its canonical rotation offset."""
    if not edges:
        raise ValueError("a canonical edge cycle cannot be empty")
    variants = tuple(
        (edges[offset:] + edges[:offset], offset) for offset in range(len(edges))
    )
    return min(variants)


@lru_cache(maxsize=1)
def _candidate_cycle_identities() -> frozenset[tuple[object, ...]]:
    return frozenset(
        _canonical_cycle(tuple(cycle.states), tuple(cycle.growth))
        for cycle in enumerate_one_digit_cycles()
    )


def _macro_identity(
    phases: tuple[ClockedBorderPhase, ...], kind: BorderMacroKind
) -> tuple[BorderMacroIdentity, int]:
    first = phases[0]
    source_states = tuple(
        (phase.port.source.high, phase.port.source.low) for phase in phases
    )
    growth = tuple(phase.port.growth for phase in phases)
    if kind is BorderMacroKind.CYCLE:
        if _canonical_cycle(source_states, growth) not in _candidate_cycle_identities():
            raise ValueError(
                "border word is absent from the canonical candidate catalogue"
            )
        edge_word = tuple(_edge_signature(phase.port) for phase in phases)
        canonical_edges, rotation = _canonical_edge_cycle(edge_word)
        # The first observed edge's phase is its position in the canonical
        # word, not the number of rotations needed to normalize the word.
        entry_phase = (-rotation) % len(phases)
        signature: tuple[object, ...] = (first.port.source.k, canonical_edges)
    else:
        signature = (
            first.port.source.k,
            source_states,
            tuple((p.port.target.high, p.port.target.low) for p in phases),
            growth,
            tuple(p.port.low_carry for p in phases),
            tuple(tuple(fn.value for fn in p.port.admitted_middle) for p in phases),
        )
        entry_phase = 0
    return BorderMacroIdentity(BorderFamilyId.REVERSE_ADD, kind, signature), entry_phase


def _find_returns(
    phases: tuple[ClockedBorderPhase | None, ...],
) -> tuple[RegisteredBorderMacro, ...]:
    result: list[RegisteredBorderMacro] = []
    for start, first in enumerate(phases):
        if first is None:
            continue
        for end in range(start + 1, len(phases) + 1):
            word = phases[start:end]
            if any(phase is None for phase in word):
                break
            concrete = tuple(phase for phase in word if phase is not None)
            if concrete[-1].port.target != first.port.source:
                continue
            source_states = tuple(
                (p.port.source.high, p.port.source.low) for p in concrete
            )
            growth = tuple(p.port.growth for p in concrete)
            kind = (
                BorderMacroKind.CYCLE
                if first.port.source.k == 1
                and len(set(source_states)) == len(source_states)
                and _canonical_cycle(source_states, growth)
                in _candidate_cycle_identities()
                else BorderMacroKind.PATH
            )
            result.append(
                RegisteredBorderMacro(
                    *_macro_identity(concrete, kind),
                    start,
                    end,
                    tuple(phase.tick for phase in concrete),
                    concrete[0].width,
                    concrete[-1].width + concrete[-1].port.growth,
                    concrete[0].residue99,
                    concrete[-1].target99,
                    concrete[0].residue198,
                    concrete[-1].target198,
                )
            )
    return tuple(result)


def _episode(
    phases: tuple[ClockedBorderPhase, ...],
    start: int,
    end: int,
    kind: BorderMacroKind,
    unit: int,
    descriptor: str,
) -> RegisteredBorderEpisode:
    word = phases[start:end]
    first, last = word[0], word[-1]
    signature = (
        descriptor,
        first.port.source.k,
        tuple((p.port.source.high, p.port.source.low) for p in word),
        tuple((p.port.target.high, p.port.target.low) for p in word),
        tuple(p.port.growth for p in word),
        tuple(p.port.low_carry for p in word),
        tuple(tuple(fn.value for fn in p.port.admitted_middle) for p in word),
    )
    return RegisteredBorderEpisode(
        BorderMacroIdentity(BorderFamilyId.REVERSE_ADD, kind, signature),
        kind,
        start,
        end,
        (end - start) // unit,
        sum(p.port.growth for p in word),
        tuple(p.port.growth for p in word),
        tuple(p.port.low_carry for p in word),
        tuple(tuple(fn.value for fn in p.port.admitted_middle) for p in word),
        first.residue99,
        last.target99,
        first.residue198,
        last.target198,
    )


def _find_episodes(
    phases: tuple[ClockedBorderPhase | None, ...],
) -> tuple[RegisteredBorderEpisode, ...]:
    concrete: list[ClockedBorderPhase] = []
    for phase in phases:
        if phase is None:
            break
        concrete.append(phase)
    word = tuple(concrete)
    found: list[RegisteredBorderEpisode] = []
    start = 0
    while start + 3 < len(word):
        first = word[start].port
        if first.source.k == 1 and (first.source.high, first.source.low) == (9, 8):
            end = start
            while end + 1 < len(word):
                grow, quiet = word[end : end + 2]
                if not (
                    (grow.port.source.high, grow.port.source.low) == (9, 8)
                    and (grow.port.target.high, grow.port.target.low) == (1, 7)
                    and grow.port.growth == 1
                    and grow.port.low_carry == 1
                    and (quiet.port.source.high, quiet.port.source.low) == (1, 7)
                    and (quiet.port.target.high, quiet.port.target.low) == (9, 8)
                    and quiet.port.growth == 0
                    and quiet.port.low_carry == 0
                    and CarryFn.CONST1 in quiet.port.admitted_middle
                ):
                    break
                end += 2
            if end - start >= 4:
                found.append(
                    _episode(
                        word,
                        start,
                        end,
                        BorderMacroKind.BURST,
                        2,
                        "alternating-98-17",
                    )
                )
                start = end
                continue
        start += 1
    index = 0
    while index < len(word):
        growth = word[index].port.growth
        end = index + 1
        while end < len(word) and word[end].port.growth == growth:
            end += 1
        if end - index >= 2:
            found.append(
                _episode(
                    word,
                    index,
                    end,
                    BorderMacroKind.PATH,
                    1,
                    "growth" if growth else "quiet",
                )
            )
        index = end
    if word and word[0].port.source.k == 1:
        for index, phase in enumerate(word):
            port = phase.port
            if (
                (port.source.high, port.source.low) == (1, 7)
                and (port.target.high, port.target.low) == (8, 8)
                and port.growth == 0
            ):
                found.append(
                    _episode(
                        word,
                        index,
                        index + 1,
                        BorderMacroKind.PATH,
                        1,
                        "17-exit-88",
                    )
                )
    return tuple(
        sorted(found, key=lambda item: (item.start, item.end, item.kind.value))
    )


@dataclass(frozen=True, slots=True)
class SourceBorderMacroCatalogue:
    """Recomputable metadata over one existing owner-issued finite source trace."""

    certificate: CertifiedBorderGrowth = field(repr=False, compare=False)
    children: tuple[ReversePairOutputOccurrence, ...] = field(repr=False, compare=False)
    pair_depth: int
    outer_phases: tuple[ClockedBorderPhase | None, ...]
    window_phases: tuple[ClockedBorderPhase | None, ...]
    outer_macros: tuple[RegisteredBorderMacro, ...]
    window_macros: tuple[RegisteredBorderMacro, ...]
    outer_episodes: tuple[RegisteredBorderEpisode, ...]
    window_episodes: tuple[RegisteredBorderEpisode, ...]

    def validate(self) -> None:
        from .q19_border_control import CertifiedBorderGrowth
        from .q19_occurrence import ReversePairOutputOccurrence
        from .q19_output import ReversePairQ19OutputOwner

        cert = self.certificate
        if type(cert) is not CertifiedBorderGrowth:
            raise TypeError("border metadata requires an existing Q19 certificate")
        if type(cert.owner) is not ReversePairQ19OutputOwner:
            raise TypeError("border certificate has a foreign source owner")
        cert.validate(cert.owner, cert.source)
        if (
            type(self.pair_depth) is not int
            or self.pair_depth < 1
            or self.pair_depth > 12
            or type(self.children) is not tuple
            or len(self.children) != len(cert.growth_word)
            or self.children[0] is not cert.source
            or any(
                type(child) is not ReversePairOutputOccurrence
                for child in self.children
            )
        ):
            raise ValueError("border metadata lost its source cursor")
        owner = cert.owner
        for earlier, later in zip(self.children, self.children[1:]):
            owner.validate_issued_occurrence(earlier)
            owner.validate_issued_occurrence(later)
            if later.temporal_steps != earlier.temporal_steps + 1:
                raise ValueError("source children are not adjacent")
        expected_outer = _clocked_phases(
            cert,
            self.children,
            cert.bilateral_carry_ports()[1:],
            cert.growth_word[1:],
            1,
        )
        expected_window = _clocked_phases(
            cert,
            self.children,
            cert.bilateral_window_ports()[1:],
            cert.growth_word[1:],
            self.pair_depth,
        )
        if (
            self.outer_phases != expected_outer
            or self.window_phases != expected_window
            or self.outer_macros != _find_returns(expected_outer)
            or self.window_macros != _find_returns(expected_window)
            or self.outer_episodes != _find_episodes(expected_outer)
            or self.window_episodes != _find_episodes(expected_window)
        ):
            raise ValueError("border metadata differs from the exact source trace")


def source_border_macro_catalogue(
    certificate: CertifiedBorderGrowth,
    children: tuple[ReversePairOutputOccurrence, ...],
    *,
    pair_depth: int,
) -> SourceBorderMacroCatalogue:
    """Describe a finite exact child chain using its original certificate."""
    from .q19_border_control import CertifiedBorderGrowth
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner

    if type(certificate) is not CertifiedBorderGrowth:
        raise TypeError("border metadata requires CertifiedBorderGrowth")
    if type(certificate.owner) is not ReversePairQ19OutputOwner:
        raise TypeError("border certificate has a foreign source owner")
    certificate.validate(certificate.owner, certificate.source)
    if type(pair_depth) is not int or not 1 <= pair_depth <= 12:
        raise ValueError("pair depth must be in 1..12")
    if (
        type(children) is not tuple
        or len(children) != len(certificate.growth_word)
        or any(type(child) is not ReversePairOutputOccurrence for child in children)
    ):
        raise ValueError("exact child roots must cover the certified horizon")
    # A Q19 certificate's leading edge records the already completed source
    # emission (the pair width is the predecessor width).  The query trace
    # begins at certificate.source, so join only the subsequent exact edges.
    future_growth = certificate.growth_word[1:]
    outer_ports = certificate.bilateral_carry_ports()[1:]
    window_ports = certificate.bilateral_window_ports()[1:]
    outer = _clocked_phases(certificate, children, outer_ports, future_growth, 1)
    window = _clocked_phases(
        certificate, children, window_ports, future_growth, pair_depth
    )
    result = SourceBorderMacroCatalogue(
        certificate,
        children,
        pair_depth,
        outer,
        window,
        _find_returns(outer),
        _find_returns(window),
        _find_episodes(outer),
        _find_episodes(window),
    )
    result.validate()
    return result


__all__ = [
    "ClockedBorderPhase",
    "RegisteredBorderEpisode",
    "RegisteredBorderMacro",
    "SourceBorderMacroCatalogue",
    "source_border_macro_catalogue",
]
