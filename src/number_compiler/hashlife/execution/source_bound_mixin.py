"""Tile-scheduler ownership surface for source-bound image execution."""

from __future__ import annotations

from collections.abc import Hashable

from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
    SourceBoundSchedulerCore,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger


class SourceBoundImageMixin:
    """Methods inherited by ``TileScheduler`` without another executor facade."""

    ledger: ResourceLedger
    _source_images: SourceBoundSchedulerCore | None

    @property
    def published_source_image_core(self) -> SourceBoundSchedulerCore | None:
        """Return an already-published source-image core without creating one."""
        return self._source_images

    def _source_image_core(self) -> SourceBoundSchedulerCore:
        found = self._source_images
        if found is None:
            found = SourceBoundSchedulerCore(self.ledger)
            self._source_images = found
        return found

    def register_source_image_adapter(self, adapter: SourceBoundImageAdapter) -> None:
        self._source_image_core().register(adapter)

    def source_image_origin(
        self, adapter: SourceBoundImageAdapter, source: Hashable
    ) -> SourceImageID:
        """Admit an original source without executing an identity action."""
        return self._source_image_core().origin(adapter, source)

    def source_image_view(
        self, adapter: SourceBoundImageAdapter, image: SourceImageID
    ) -> SourceImageView:
        """Inspect a published image after checking its issuing adapter."""
        return self._source_image_core().view_for_adapter(adapter, image)

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

    def cached_source_projection(
        self,
        adapter: SourceBoundImageAdapter,
        image: SourceImageID,
        demand: SourceImageDemand,
    ) -> SourceImageProjection | None:
        return self._source_image_core().cached_projection(adapter, image, demand)

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
