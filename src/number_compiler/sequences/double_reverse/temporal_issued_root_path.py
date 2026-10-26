"""Source-issued finite paths of adjacent 2rev10 temporal roots."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from ._temporal_bank_authority import (
    SourceAuthorizedRecord,
    SourceRecordAuthority,
    issue_source_record,
    validate_source_record,
)
from .temporal_hashlife import growth_ports
from .temporal_hashlife_types import DoubleReversePortAction

if TYPE_CHECKING:
    from .source_bound_bank import PointedBankSource


@dataclass(frozen=True, slots=True)
class SourceIssuedRootPath(SourceAuthorizedRecord):
    """Finite chronological roots produced by one prepared source owner.

    The path records only roots reached by authenticated adjacent actions. It
    lets a bounded consumer read an already materialized root instead of
    asking the temporal engine to rebuild the same cone. Its authority covers
    only this finite path.
    """

    physical_prefix: int
    source_root: int
    source_phase: int
    roots: tuple[int, ...]
    actions: tuple[DoubleReversePortAction, ...]
    root_offset: int = 0

    def validate_source_authority(self) -> SourceRecordAuthority:
        authority = validate_source_record(self)
        if (
            authority.root != self.source_root
            or authority.source_generation != self.physical_prefix
            or type(self.source_phase) is not int
            or self.source_phase not in (0, 1, 2, 3)
            or type(self.root_offset) is not int
            or self.root_offset < 0
            or type(self.roots) is not tuple
            or len(self.roots) < 2
            or (self.root_offset == 0 and self.roots[0] != self.source_root)
            or any(type(root) is not int or root < 0 for root in self.roots)
            or type(self.actions) is not tuple
            or len(self.actions) != len(self.roots) - 1
            or any(
                type(action) is not DoubleReversePortAction for action in self.actions
            )
        ):
            raise ValueError("source-issued root path has broken authority")
        return authority

    def validate_for_source(self, source: PointedBankSource) -> None:
        """Recheck every action/root seam against the live source owner."""
        from .source_bound_bank import PointedBankSource as BankSource

        if type(source) is not BankSource:
            raise TypeError("issued root path needs its prepared source")
        source.validate(require_issued_cursor=source.f_steps > 0)
        authority = self.validate_source_authority()
        if (
            authority.arena is not source.arena
            or self.source_root != source.root
            or self.physical_prefix != source.physical_prefix
            or self.source_phase != source.phase
            or self.root_offset + len(self.actions) > source.f_steps
        ):
            raise ValueError("issued root path belongs to another source or horizon")

        phase = (source.phase + 2 * self.root_offset) % 4
        for index, action in enumerate(self.actions):
            source.engine.validate_action(action)
            if (
                action.steps != 1
                or source.engine.root_of(action.source) != self.roots[index]
                or source.engine.root_of(action.target) != self.roots[index + 1]
                or action.phase_in != phase
                or action.phase_out != (phase + 2) % 4
                or source.engine.certify(self.roots[index]) != phase
                or source.engine.certify(self.roots[index + 1]) != action.phase_out
            ):
                raise ValueError("issued root path contains a broken adjacent seam")
            expected_width = source.width_in + sum(
                growth_ports(source.phase, self.root_offset + index)
            )
            if source.arena.nodes[self.roots[index]].length != expected_width:
                raise ValueError("issued root path has an invalid growth coordinate")
            phase = action.phase_out

        final_width = source.width_in + sum(
            growth_ports(source.phase, self.root_offset + len(self.actions))
        )
        if source.arena.nodes[self.roots[-1]].length != final_width:
            raise ValueError("issued root path has an invalid final width")

    def windows(
        self,
        source: PointedBankSource,
        ranges: tuple[tuple[int, int], ...],
    ) -> tuple[SourceIssuedRootPath, ...]:
        """Issue bounded validated slices from one authenticated full path.

        The complete path is checked once. Each returned record contains only
        one consumer window, so a matrix consumer does not rescan a long path
        for every bounded tile.
        """
        self.validate_for_source(source)
        if type(ranges) is not tuple:
            raise TypeError("root path windows must be an exact tuple")
        result: list[SourceIssuedRootPath] = []
        for start, count in ranges:
            if (
                type(start) is not int
                or type(count) is not int
                or start < 0
                or count < 1
                or start + count > len(self.actions)
            ):
                raise ValueError("root path window lies outside the issued path")
            record = SourceIssuedRootPath(
                self.physical_prefix,
                self.source_root,
                self.source_phase,
                self.roots[start : start + count + 1],
                self.actions[start : start + count],
                self.root_offset + start,
            )
            issued = issue_source_record(
                record,
                source.arena,
                source.root,
                source_generation=source.physical_prefix,
            )
            issued.validate_source_authority()
            result.append(issued)
        return tuple(result)


def source_issued_root_path(
    source: PointedBankSource,
    actions: tuple[DoubleReversePortAction, ...],
) -> SourceIssuedRootPath:
    """Seal owner-issued adjacent actions as one finite source path."""
    from .source_bound_bank import PointedBankSource as BankSource

    if type(source) is not BankSource:
        raise TypeError("root path requires a prepared source")
    source.validate(require_issued_cursor=source.f_steps > 0)
    if type(actions) is not tuple or not actions or len(actions) > source.f_steps:
        raise ValueError("issued root path lies outside the prepared horizon")

    phase = source.phase
    roots = [source.root]
    root = source.root
    for action in actions:
        source.engine.validate_action(action)
        if (
            action.steps != 1
            or source.engine.root_of(action.source) != root
            or action.phase_in != phase
            or action.phase_out != (phase + 2) % 4
        ):
            raise ValueError("root path contains an unissued or nonadjacent action")
        root = source.engine.root_of(action.target)
        phase = action.phase_out
        roots.append(root)

    issued = issue_source_record(
        SourceIssuedRootPath(
            source.physical_prefix,
            source.root,
            source.phase,
            tuple(roots),
            actions,
        ),
        source.arena,
        source.root,
        source_generation=source.physical_prefix,
    )
    issued.validate_for_source(source)
    return issued


__all__ = ["SourceIssuedRootPath", "source_issued_root_path"]
