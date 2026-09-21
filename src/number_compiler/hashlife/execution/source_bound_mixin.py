"""Tile-scheduler ownership surface for source-bound image execution."""

from __future__ import annotations

from collections.abc import Hashable

from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
    SourceBoundSchedulerCore,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
)
from number_compiler.resources.ledger import ResourceLedger


class SourceBoundImageMixin:
    """Methods inherited by ``TileScheduler`` without another executor facade."""

    ledger: ResourceLedger
    _source_images: SourceBoundSchedulerCore | None

    def _source_image_core(self) -> SourceBoundSchedulerCore:
        found = self._source_images
        if found is None:
            found = SourceBoundSchedulerCore(self.ledger)
            self._source_images = found
        return found

    def register_source_image_adapter(self, adapter: SourceBoundImageAdapter) -> None:
        self._source_image_core().register(adapter)

    def source_image(
        self,
        adapter: SourceBoundImageAdapter,
        source: Hashable,
        action: Hashable,
    ) -> SourceImageID:
        return self._source_image_core().apply(adapter, source, action)

    def source_image_demanded(
        self,
        adapter: SourceBoundImageAdapter,
        source: Hashable,
        action: Hashable,
        demand: SourceImageDemand,
    ) -> SourceImageID:
        return self._source_image_core().apply_demanded(adapter, source, action, demand)

    def source_projection(
        self,
        adapter: SourceBoundImageAdapter,
        image: SourceImageID,
        demand: SourceImageDemand,
    ) -> SourceImageProjection:
        return self._source_image_core().projection(adapter, image, demand)

    def source_first_failure(
        self,
        adapter: SourceBoundImageAdapter,
        image: SourceImageID,
    ) -> Hashable | None:
        return self._source_image_core().first_failure(adapter, image)

    def clear_source_images(self) -> None:
        if self._source_images is not None:
            self._source_images.clear()

    def dispose_source_images(self) -> None:
        """Release adapters and all images owned by this scheduler."""
        if self._source_images is not None:
            self._source_images.dispose()
            self._source_images = None


__all__ = ["SourceBoundImageMixin"]
