"""Bounded retained images of source-bound Antihydra cylinder projections."""

from __future__ import annotations

from collections.abc import MutableMapping
from dataclasses import dataclass

from number_compiler.resources.ledger import ResourceLedger

ProjectionFragmentSeal = tuple[
    tuple[int | tuple[int, int, int, int, int, int], ...],
    tuple[tuple[int, ...], ...],
    int,
]


def projection_key_snapshot(
    key: ProjectionFragmentKey,
) -> tuple[int | tuple[int, int, int, int, int, int], ...]:
    return (
        key.source_owner,
        key.requested,
        key.start,
        key.cylinder,
        key.spatial_width,
        key.temporal_width,
        key.spatial_sign,
        key.temporal_sign,
        key.modulus,
        key.head_phase,
        key.time_phase,
    )


@dataclass(frozen=True, slots=True)
class ProjectionFragmentKey:
    """Complete authority for one relative spacetime cylinder image."""

    source_owner: int
    requested: int
    start: int
    cylinder: tuple[int, int, int, int, int, int]
    spatial_width: int
    temporal_width: int
    spatial_sign: int
    temporal_sign: int
    modulus: int
    head_phase: int
    time_phase: int

    @property
    def area(self) -> int:
        return self.spatial_width * self.temporal_width


@dataclass(frozen=True, slots=True)
class ProjectionFragment:
    """Relative typed coefficients; no endpoint state or return itinerary."""

    key: ProjectionFragmentKey
    typed_ports: tuple[tuple[int, ...], ...]
    sampled_sweep_classes: int

    def validate(self) -> None:
        key = self.key
        if (
            type(key) is not ProjectionFragmentKey
            or type(self.typed_ports) is not tuple
            or len(self.typed_ports) != 12
            or any(
                type(row) is not tuple or len(row) != key.area
                for row in self.typed_ports
            )
            or any(
                type(value) is not int or not 0 <= value < key.modulus
                for row in self.typed_ports
                for value in row
            )
            or type(self.sampled_sweep_classes) is not int
            or self.sampled_sweep_classes < 0
        ):
            raise ValueError("invalid Antihydra projection fragment")


class ProjectionFragmentCache:
    """Deterministic 32-entry cache with independently sealed publications."""

    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        suffix = len(ledger.inventory())
        self.owner = ledger.register(
            f"antihydra.spacetime.fragments.{suffix}", "demanded_projection"
        )
        self.seal_owner = ledger.register(
            f"antihydra.spacetime.fragment-seals.{suffix}",
            "projection_binding",
        )
        self.fragments: MutableMapping[ProjectionFragmentKey, ProjectionFragment] = (
            ledger.make_dict(self.owner)
        )
        self.seals: MutableMapping[ProjectionFragmentKey, ProjectionFragmentSeal] = (
            ledger.make_dict(self.seal_owner)
        )
        ledger.register_container(
            self.owner,
            self.fragments,
            node_count=lambda: sum(12 * key.area + 1 for key in self.fragments),
            payloads=self.fragments.items,
        )
        ledger.register_container(
            self.seal_owner,
            self.seals,
            node_count=lambda: 2 * len(self.seals),
            payloads=self.seals.items,
        )
        ledger.register_execution_root(self)

    @staticmethod
    def _nodes(key: ProjectionFragmentKey) -> int:
        return 12 * key.area + 1

    def get(self, key: ProjectionFragmentKey) -> ProjectionFragment | None:
        found = self.fragments.get(key)
        if found is None:
            return None
        if not self.matches_seal(key, found):
            raise ValueError("Antihydra projection fragment binding was changed")
        found.validate()
        self.ledger.bump("spacetime_projection_fragment_hits")
        return found

    def put(
        self, image: object, capacity: int, *, issuer: object = None
    ) -> ProjectionFragment:
        """Compute from a live source image; never accept caller-supplied coefficients."""
        from number_compiler.hashlife.execution.source_bound_images import SourceImageID
        from number_compiler.sequences.antihydra.projection_core import (
            AntihydraProjectionDriver,
        )

        if (
            type(issuer) is not AntihydraProjectionDriver
            or type(image) is not SourceImageID
        ):
            raise ValueError(
                "Antihydra fragment requires an active source-image publication"
            )
        if type(capacity) is not int or not 1 <= capacity <= 32:
            raise ValueError("projection fragment capacity must be 1..32")
        fragment = issuer.project_fragment(self, image)
        fragment.validate()
        key = fragment.key
        found = self.fragments.get(key)
        if found is not None:
            if not self.matches_seal(key, found):
                raise ValueError("Antihydra projection fragment binding was changed")
            return found
        while len(self.fragments) >= capacity:
            victim = next(iter(self.fragments))
            self._drop(victim)
            self.ledger.bump("spacetime_projection_fragment_evictions")
        nodes = self._nodes(key)
        if (
            self.ledger.max_nodes is not None
            and self.ledger.nodes + nodes + 2 > self.ledger.max_nodes
        ) or (
            self.ledger.max_cache_entries is not None
            and self.ledger.entries + 2 > self.ledger.max_cache_entries
        ):
            self.ledger.bump("spacetime_projection_fragment_retention_refusals")
            return fragment
        self.ledger.reserve_many(((self.owner, 1, nodes), (self.seal_owner, 1, 2)))
        try:
            self.fragments[key] = fragment
            self.seals[key] = (
                projection_key_snapshot(fragment.key),
                fragment.typed_ports,
                fragment.sampled_sweep_classes,
            )
        except BaseException:
            self.fragments.pop(key, None)
            self.seals.pop(key, None)
            self.ledger.release(self.owner, entries=1, nodes=nodes)
            self.ledger.release(self.seal_owner, entries=1, nodes=2)
            raise
        self.ledger.bump("spacetime_projection_fragment_publications")
        return fragment

    def _drop(self, key: ProjectionFragmentKey) -> None:
        fragment = self.fragments.pop(key)
        if not self.matches_seal(key, fragment):
            raise ValueError("Antihydra projection fragment binding was changed")
        self.seals.pop(key)
        self.ledger.release(self.owner, entries=1, nodes=self._nodes(key))
        self.ledger.release(self.seal_owner, entries=1, nodes=2)

    def matches_seal(
        self, key: ProjectionFragmentKey, fragment: ProjectionFragment
    ) -> bool:
        """Check an independent field snapshot, never the publication identity."""
        return self.seals.get(key) == (
            projection_key_snapshot(fragment.key),
            fragment.typed_ports,
            fragment.sampled_sweep_classes,
        )

    def clear(self) -> None:
        for key in tuple(self.fragments):
            self._drop(key)


__all__ = [
    "projection_key_snapshot",
    "ProjectionFragment",
    "ProjectionFragmentCache",
    "ProjectionFragmentKey",
]
