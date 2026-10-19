"""Retryable ownership for completed-result tile roots."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from functools import partial
from typing import TYPE_CHECKING, NoReturn, Self

from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_result_records import (
    CompletedResult,
    PoweredResultKey,
)
from number_compiler.hashlife.tiles.tiles import TileID, TileLease
from number_compiler.resources.lifecycle import cleanup_all

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
    from number_compiler.resources.tile_runtime_audit_contracts import (
        ResultLeaseAuditSnapshot,
    )


@dataclass(frozen=True, slots=True)
class _IssuedResultBinding:
    """The immutable roots and action association issued by the result arena."""

    issuer: CompletedResultArena
    key: PoweredResultKey
    result: CompletedResult
    tile: TileLease
    boundary_tiles: tuple[TileLease, ...]
    operand_views: tuple[BoundaryTileView, ...]


def tile_lease_was_released(lease: TileLease) -> bool:
    """Trust only TileLease.close's completion flag, never an absent table key."""
    return lease.audit_snapshot().closed


class ResultLease:
    """A completed result whose roots remain pinned until close succeeds."""

    __slots__ = (
        "_boundary_accounted",
        "_boundary_closed",
        "_boundary_tiles",
        "_close_binding",
        "_closed",
        "_closing",
        "_issuer",
        "_issued_binding",
        "_key",
        "_operand_map_released",
        "_operand_views",
        "_operands_released",
        "_output_closed",
        "_result",
        "_tile",
    )

    def __init__(
        self,
        issuer: CompletedResultArena,
        key: PoweredResultKey,
        result: CompletedResult,
        tile: TileLease,
        seal: object,
        boundary_tiles: tuple[TileLease, ...] = (),
        operand_views: tuple[BoundaryTileView, ...] = (),
    ) -> None:
        from number_compiler.hashlife.tiles.tile_results import CompletedResultArena

        if type(
            issuer
        ) is not CompletedResultArena or not issuer.accepts_result_lease_seal(seal):
            raise TypeError("result leases must be issued by their arena")
        self._issuer, self._key = issuer, key
        if type(boundary_tiles) is not tuple or any(
            type(value) is not TileLease for value in boundary_tiles
        ):
            raise TypeError("result boundary leases require exact tile leases")
        self._result, self._tile = result, tile
        self._boundary_tiles, self._operand_views = boundary_tiles, operand_views
        self._issued_binding = _IssuedResultBinding(
            issuer, key, result, tile, boundary_tiles, operand_views
        )
        self._closed = self._closing = False
        self._close_binding: _IssuedResultBinding | None = None
        self._boundary_closed = 0
        self._boundary_accounted = 0
        self._output_closed = self._operands_released = False
        self._operand_map_released = False

    def _require_open(self) -> None:
        if (
            type(self._closed) is not bool
            or self._closed
            or type(self._closing) is not bool
            or self._closing
        ):
            raise ValueError("closed or malformed result lease")
        if (
            type(self._result) is not CompletedResult
            or type(self._tile) is not TileLease
        ):
            raise ValueError("malformed result lease")
        if type(self._boundary_tiles) is not tuple or any(
            type(value) is not TileLease for value in self._boundary_tiles
        ):
            raise ValueError("malformed result boundary leases")
        if type(self._operand_views) is not tuple or any(
            type(value) is not BoundaryTileView for value in self._operand_views
        ):
            raise ValueError("malformed result boundary operand inventory")
        from number_compiler.hashlife.tiles.tile_results import CompletedResultArena

        if type(self._issuer) is not CompletedResultArena:
            raise ValueError("malformed result lease issuer")
        binding = self._issued_binding
        if type(binding) is not _IssuedResultBinding:
            raise ValueError("malformed issued result lease binding")
        if self._tile is not binding.tile:
            raise ValueError("result lease pins another output lease")
        if self._issuer is not binding.issuer:
            raise ValueError("result lease issuer changed after issuance")
        # Run the issuer's semantic validation first so malformed substitutions
        # retain the precise authority error (for example, a foreign arena).
        # A structurally valid replacement is rejected below by issuance
        # identity, even when it happens to have the same semantic signature.
        self._issuer.validate_leased(
            self._key,
            self._result,
            self._tile,
            self._boundary_tiles,
            self._operand_views,
        )
        if not self._matches(binding):
            raise ValueError("result lease binding changed after issuance")

    def audit_snapshot(self) -> ResultLeaseAuditSnapshot:
        """Expose issued lease fields to read-only resource auditors."""
        from number_compiler.resources.tile_runtime_audit_contracts import (
            ResultLeaseAuditSnapshot,
        )

        return ResultLeaseAuditSnapshot(
            self._issuer,
            self._key,
            self._result,
            self._tile,
            self._boundary_tiles,
            self._operand_views,
            self._closed,
        )

    def _matches(self, binding: _IssuedResultBinding) -> bool:
        return (
            self._issuer is binding.issuer
            and self._key is binding.key
            and self._result is binding.result
            and self._tile is binding.tile
            and self._boundary_tiles is binding.boundary_tiles
            and self._operand_views is binding.operand_views
        )

    @property
    def result(self) -> CompletedResult:
        self._require_open()
        _ = self._tile.tile
        return self._result

    def validated_binding(
        self,
    ) -> tuple[PoweredResultKey, CompletedResult, object]:
        """Read the issued action and result after validating their live lease."""
        self._require_open()
        binding = self._issued_binding
        _ = binding.tile.tile
        return (
            binding.key,
            binding.result,
            binding.issuer.validated_action_authority(),
        )

    @property
    def output(self) -> TileID:
        self._require_open()
        tile = self._tile.tile
        if type(tile) is not TileID:
            raise ValueError("malformed output tile lease")
        return tile

    def close(self) -> None:
        if (
            type(self._closed) is not bool
            or type(self._closing) is not bool
            or type(self._boundary_closed) is not int
            or type(self._boundary_accounted) is not int
            or type(self._output_closed) is not bool
            or type(self._operands_released) is not bool
            or type(self._operand_map_released) is not bool
        ):
            raise ValueError("malformed result lease")
        binding = self._issued_binding
        if type(binding) is not _IssuedResultBinding:
            raise ValueError("malformed issued result lease binding")
        if (
            type(binding.boundary_tiles) is not tuple
            or self._boundary_closed < 0
            or self._boundary_accounted < 0
            or self._boundary_closed >> len(binding.boundary_tiles)
            or self._boundary_accounted & ~self._boundary_closed
        ):
            raise ValueError("malformed result lease cleanup progress")
        if self._closed:
            return
        if not self._closing:
            # A caller-mutated association is never used to release roots. The
            # caller may restore the exact issuance binding and retry close.
            self._require_open()
            self._close_binding = binding
            self._closing = True
        else:
            self._require_closing_binding()

        # cleanup_all runs callbacks in input order. Close boundary roots in
        # reverse acquisition order, then the output, then its operand census.
        # Progress is recorded per root so retry cannot release twice.
        cleanups: list[Callable[[], object]] = [
            partial(self._close_boundary, index)
            for index in reversed(range(len(binding.boundary_tiles)))
        ]
        cleanups.extend((self._close_output, self._release_operands_if_ready))
        cleanup_all(cleanups)
        if (
            self._output_closed
            and self._boundary_closed.bit_count() == len(binding.boundary_tiles)
            and self._boundary_accounted.bit_count() == len(binding.boundary_tiles)
            and self._operands_released
        ):
            self._closed = True

    def _require_closing_binding(self) -> None:
        binding = self._issued_binding
        if (
            type(binding) is not _IssuedResultBinding
            or self._close_binding is not binding
            or not self._matches(binding)
        ):
            raise ValueError("result lease cleanup binding changed")
        from number_compiler.hashlife.tiles.tile_results import CompletedResultArena

        if (
            type(binding.issuer) is not CompletedResultArena
            or type(binding.key) is not PoweredResultKey
            or type(binding.result) is not CompletedResult
            or type(binding.tile) is not TileLease
            or type(binding.boundary_tiles) is not tuple
            or any(type(lease) is not TileLease for lease in binding.boundary_tiles)
            or type(binding.operand_views) is not tuple
            or any(type(view) is not BoundaryTileView for view in binding.operand_views)
        ):
            raise ValueError("malformed result lease cleanup binding")

    def _close_boundary(self, index: int) -> None:
        lease = self._boundary_tiles[index]
        if not self._boundary_closed & (1 << index):
            try:
                lease.close()
            except BaseException:
                if tile_lease_was_released(lease):
                    self._boundary_closed |= 1 << index
                raise
            self._boundary_closed |= 1 << index
        if not self._boundary_accounted & (1 << index):
            self._issuer.release_boundary_leases(1, ())
            self._boundary_accounted |= 1 << index

    def _close_output(self) -> None:
        if self._output_closed:
            return
        try:
            self._tile.close()
        except BaseException:
            if tile_lease_was_released(self._tile):
                self._output_closed = True
            raise
        self._output_closed = True

    def _release_operands_if_ready(self) -> None:
        if self._operands_released:
            return
        if (
            not self._output_closed
            or self._boundary_closed.bit_count() != len(self._boundary_tiles)
            or self._boundary_accounted.bit_count() != len(self._boundary_tiles)
        ):
            return
        if self._operand_map_released:
            self._issuer.release_boundary_leases(0, (), operands_already_mutated=True)
        else:
            self._issuer.release_boundary_leases(
                0,
                self._operand_views,
                on_operands_mutated=self._mark_operand_map_released,
            )
        self._operands_released = True

    def _mark_operand_map_released(self) -> None:
        self._operand_map_released = True

    def __copy__(self) -> ResultLease:
        raise TypeError("result leases cannot be copied")

    def __deepcopy__(self, _memo: object) -> ResultLease:
        raise TypeError("result leases cannot be copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("result leases cannot be serialized")

    def __enter__(self) -> Self:
        _ = self.result
        return self

    def __exit__(self, *_exception: object) -> None:
        self.close()


__all__ = ["ResultLease", "tile_lease_was_released"]
