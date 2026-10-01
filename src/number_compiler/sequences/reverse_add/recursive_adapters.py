"""Authenticated completed-child adapters for bounded reverse/add images."""

from __future__ import annotations

from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    FieldCellActionID,
    FieldGeometryArena,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.continuations.higher_interfaces import (
    HigherLocalInterfaceArena,
)
from number_compiler.hashlife.execution.continuations.higher_macro_composer import (
    HigherSpatialMacroComposer,
    SourceBoundHigherMacro,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.provider_absorption import (
    ProviderAbsorptionArena,
)
from number_compiler.hashlife.execution.continuations.provider_image_input import (
    ProviderImageInput,
)
from number_compiler.hashlife.execution.field_executor import (
    FieldImageCandidate,
)
from number_compiler.hashlife.execution.field_image_summaries import (
    ParametricFieldImageSummary,
    ParametricFieldRangeSummary,
)
from number_compiler.hashlife.execution.field_images import (
    FieldImageID,
    RecursiveFieldImageArena,
    SourceCellArena,
    SourceCellID,
)
from number_compiler.hashlife.execution.recursive_outputs import (
    RecursiveCoordinateMorphismArena,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.sequences.reverse_add.field_action import (
    ReverseFieldActionArena,
)
from number_compiler.sequences.reverse_add.higher_interface import (
    ReverseHigherInterfaceCompiler,
)


class _ReverseRecursiveFieldAdapter:
    _geometries: FieldGeometryArena
    """Compile leaves and join nonleaf actions from completed child images."""

    direct_temporal_images = False

    def __init__(
        self,
        ledger: ResourceLedger,
        actions: ReverseFieldActionArena,
        sources: SourceCellArena,
        semantics: HigherSemanticArena,
        runtime: HigherBimachineRuntime,
        interfaces: HigherLocalInterfaceArena,
        outputs: RecursiveCoordinateMorphismArena,
        compiler: ReverseHigherInterfaceCompiler,
        *,
        blank: int,
    ) -> None:
        self.ledger = ledger
        self.actions = actions
        self.sources = sources
        self.semantics = semantics
        self.runtime = runtime
        self.interfaces = interfaces
        self.outputs = outputs
        self.compiler = compiler
        if type(blank) is not int or blank < 0:
            raise ValueError(
                "reverse recursive adapter requires a nonnegative blank symbol"
            )
        self.blank = blank
        self._images: RecursiveFieldImageArena | None = None
        composer_owner = ledger.register(
            f"reverse-recursive-composers-{ledger.owner_count}",
            "reverse_recursive_composer_memo",
        )
        signature_owner = ledger.register(
            f"reverse-recursive-signatures-{ledger.owner_count}",
            "reverse_recursive_signature_memo",
        )
        self._composers: OwnedMemo[FieldCellActionID, HigherSpatialMacroComposer] = (
            OwnedMemo(ledger, composer_owner)
        )
        self._signatures: OwnedMemo[tuple[FieldCellActionID, int], PortSignatureID] = (
            OwnedMemo(ledger, signature_owner)
        )
        source_extent_owner = ledger.register(
            f"reverse-recursive-source-extents-{ledger.owner_count}",
            "reverse_recursive_source_extent_memo",
        )
        self._source_extents: OwnedMemo[SourceCellID, int] = OwnedMemo(
            ledger, source_extent_owner
        )
        self.ledger.register_execution_root(self)

    def validate_action(self, action: FieldCellActionID) -> None:
        self.actions.validate_action(action)

    def compose_actions(
        self, before: FieldCellActionID, after: FieldCellActionID
    ) -> FieldCellActionID:
        return self.actions.compose(before, after)

    def signature(
        self, action: FieldCellActionID, geometry: FieldGeometryID
    ) -> PortSignatureID:
        self.validate_action(action)
        self._validate_geometry(action, geometry)
        level = self._geometries.resolve(geometry).spatial_level
        key = action, level
        found = self._signatures.get(key)
        if found is not None:
            return found
        probe = self.sources.intern(0, level)
        macro = self._composer(action).compile(probe)
        found = self.interfaces.resolve(macro.interface).signature
        self._signatures[key] = found
        return found

    def action_children(
        self, action: FieldCellActionID
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        self.validate_action(action)
        return self.actions.action_children(action)

    def _validate_geometry(
        self, action: FieldCellActionID, geometry: FieldGeometryID
    ) -> None:
        record = self._geometries.resolve(geometry)
        phase_count = self.actions.resolve(action).geometry.phase_count
        if record.phase_count != phase_count:
            raise ValueError("reverse recursive geometry has another phase domain")

    def bind_geometries(self, geometries: FieldGeometryArena) -> None:
        if hasattr(self, "_geometries"):
            if self._geometries is not geometries:
                raise ValueError("reverse recursive adapter geometry arena changed")
            return
        if geometries.ledger is not self.ledger:
            raise ValueError("reverse recursive geometry belongs to another ledger")
        self._geometries = geometries

    def bind_images(self, images: RecursiveFieldImageArena) -> None:
        """Bind the canonical image arena used to authenticate completed children."""
        if (
            type(images) is not RecursiveFieldImageArena
            or images.ledger is not self.ledger
        ):
            raise ValueError("reverse recursive image arena belongs to another ledger")
        if self._images not in (None, images):
            raise ValueError("reverse recursive adapter image arena changed")
        self._images = images

    def _source_extent(self, source: SourceCellID) -> int:
        """Return the active prefix extent from the immutable source tree."""
        found = self._source_extents.get(source)
        if found is not None:
            return found
        pending: list[tuple[SourceCellID, bool]] = [(source, False)]
        while pending:
            current, ready = pending.pop()
            if self._source_extents.get(current) is not None:
                continue
            record = self.sources.resolve(current)
            if record.uniform_symbol is not None:
                self._source_extents[current] = (
                    0 if record.uniform_symbol == self.blank else record.width
                )
                self.ledger.bump("reverse_uniform_source_extent_resolutions")
                continue
            if record.level == 0:
                if record.source_tile.symbol is None:
                    raise AssertionError("reverse source leaf has no symbol")
                self._source_extents[current] = int(
                    record.source_tile.symbol != self.blank
                )
                continue
            left, right = self.sources.children(current)
            if not ready:
                pending.append((current, True))
                if self._source_extents.get(right) is None:
                    pending.append((right, False))
                if self._source_extents.get(left) is None:
                    pending.append((left, False))
                continue
            left_extent = self._source_extents.get(left)
            right_extent = self._source_extents.get(right)
            if left_extent is None or right_extent is None:
                raise AssertionError("reverse source extent lost a completed child")
            left_width = self.sources.resolve(left).width
            self._source_extents[current] = (
                left_width + right_extent if right_extent else left_extent
            )
        found = self._source_extents.get(source)
        if found is None:
            raise AssertionError("reverse source extent was not published")
        return found

    def _macro_from_completed(
        self,
        image: FieldImageID,
        source: SourceCellID,
        action: FieldCellActionID,
        geometry: FieldGeometryID,
        active_extent: int | None,
    ) -> SourceBoundHigherMacro:
        """Recover one macro *only* from its completed image plus source geometry."""
        if self._images is None:
            raise RuntimeError("reverse recursive adapter has no bound image arena")
        self._images.validate_occurrence(image, source, action, active_extent)
        image_record = self._images.resolve(image)
        source_record = self.sources.resolve(source)
        if image_record.geometry != geometry:
            raise ValueError("reverse completed child has another geometry admission")
        if image_record.level != source_record.level:
            raise ValueError("reverse completed child has another spatial level")
        if type(image_record.summary) is not ParametricFieldImageSummary:
            raise TypeError("reverse completed child requires a parametric summary")
        if image_record.summary.extent_bound != source_record.width:
            raise ValueError("reverse completed child has another extent bound")
        summary = image_record.summary
        summary.validate_range(self.interfaces)
        range_summary = summary.range_summary
        if range_summary is None:
            raise ValueError("reverse completed child lost its exact range summary")
        return SourceBoundHigherMacro(
            image_record.interface,
            image_record.output,
            source_record.width,
            self._source_extent(source),
            range_summary.activity,
            range_summary.first_active,
            range_summary.last_active,
            range_summary.extent,
            range_summary.growth,
        )

    def _join_completed(
        self,
        action: FieldCellActionID,
        source: SourceCellID,
        left: FieldImageID,
        right: FieldImageID,
        geometry: FieldGeometryID,
        left_extent: int | None = None,
        right_extent: int | None = None,
    ) -> FieldImageCandidate:
        """Publish a parent extensionally from the two completed child images."""
        self.validate_action(action)
        self._validate_geometry(action, geometry)
        if type(left) is not FieldImageID or type(right) is not FieldImageID:
            raise TypeError("reverse recursive join requires canonical child images")
        source_record = self.sources.resolve(source)
        if source_record.level == 0:
            raise ValueError("reverse completed-child join cannot target a source leaf")
        left_source, right_source = self.sources.children(source)
        left_geometry = self._geometries.child(geometry, 0)
        right_geometry = self._geometries.child(geometry, 1)
        left_macro = self._macro_from_completed(
            left, left_source, action, left_geometry, left_extent
        )
        right_macro = self._macro_from_completed(
            right, right_source, action, right_geometry, right_extent
        )
        self.signature(action, geometry)
        macro = self._composer(action).combine(left_macro, right_macro)
        if macro.width != source_record.width:
            raise AssertionError("reverse completed-child parent width mismatch")
        if macro.source_extent != self._source_extent(source):
            raise AssertionError("reverse completed-child source extent mismatch")
        self.ledger.bump("reverse_recursive_completed_child_joins")
        return self._candidate(macro)

    def _composer(self, action: FieldCellActionID) -> HigherSpatialMacroComposer:
        self.validate_action(action)
        found = self._composers.get(action)
        if found is not None:
            return found
        compiled = self.compiler.compile(action)
        found = HigherSpatialMacroComposer(
            self.semantics,
            self.interfaces,
            self.outputs,
            self.sources,
            action,
            compiled.interface,
            compiled.left,
            compiled.symbol,
            compiled.right,
            source_backed_temporal=False,
        )
        self._composers[action] = found
        return found

    def _candidate(self, macro: SourceBoundHigherMacro) -> FieldImageCandidate:
        range_summary = ParametricFieldRangeSummary(
            macro.activity,
            macro.first_active,
            macro.last_active,
            macro.extent,
            macro.growth,
        )
        summary = ParametricFieldImageSummary(
            macro.interface,
            macro.width,
            range_summary,
        )
        return FieldImageCandidate(
            macro.interface,
            macro.output,
            summary,
        )

    def _compile(
        self, action: FieldCellActionID, source: SourceCellID
    ) -> FieldImageCandidate:
        macro = self._composer(action).compile(source)
        return self._candidate(macro)

    def leaf(
        self, action: FieldCellActionID, source: SourceCellID, geometry: FieldGeometryID
    ) -> FieldImageCandidate:
        self.signature(action, geometry)
        return self._compile(action, source)

    def join(
        self,
        action: FieldCellActionID,
        source: SourceCellID,
        left: FieldImageID,
        right: FieldImageID,
        geometry: FieldGeometryID,
    ) -> FieldImageCandidate:
        return self._join_completed(action, source, left, right, geometry)

    def temporal(
        self,
        action: FieldCellActionID,
        before: FieldCellActionID,
        after: FieldCellActionID,
        source: SourceCellID,
        before_image: FieldImageID | None,
        left: FieldImageID | None,
        right: FieldImageID | None,
        geometry: FieldGeometryID,
    ) -> FieldImageCandidate:
        del before_image, left, right, action, before, after, source, geometry
        raise TypeError(
            "reverse temporal images require provider substitution over completed children"
        )

    def point(self, image: FieldImageID, coordinate: int) -> int:
        raise TypeError("reverse observations require an authenticated occurrence")

    def forest(self, *_args: object, **_kwargs: object) -> FieldImageCandidate:
        raise TypeError("reverse recursive cutover uses a power-of-two source cell")

    def clear_construction_memos(self) -> None:
        for composer in self._composers.values():
            composer.clear()
        self.compiler.clear()

    def dispose(self) -> None:
        self.clear_construction_memos()
        self._composers.dispose()
        self._signatures.dispose()
        self._source_extents.dispose()


class _ReverseProviderAdapter:
    """Substitute providers without observing midpoint symbols."""

    def __init__(
        self,
        core: _ReverseRecursiveFieldAdapter,
        providers: ProviderAbsorptionArena,
    ) -> None:
        self.core, self.providers = core, providers

    def _validate_provider(
        self,
        complete: FieldCellActionID,
        provider: ProviderImageInput,
        geometry: FieldGeometryID,
    ) -> tuple[SourceCellID, SourceCellID] | None:
        core = self.core
        images = core._images
        if images is None:
            raise RuntimeError("reverse provider adapter has no bound image arena")
        bound = self.providers.validate_occurrence(provider.binding)
        if (
            provider.context is not None
            or provider.binding.context is not None
            or provider.request.context is not None
            or provider.binding.source != provider.source
            or provider.binding.image != provider.image
            or provider.request.source != provider.source
            or provider.request.action != bound.action
            or provider.request.geometry != geometry
            or provider.request.active_extent != provider.binding.active_extent
        ):
            raise ValueError(
                "reverse provider parent has another source/action admission"
            )
        images.validate_binding(provider.request, provider.image)
        source_record = core.sources.resolve(provider.source)
        image_record = images.resolve(provider.image)
        if (
            source_record.level != provider.level
            or image_record.level != provider.level
            or image_record.geometry != geometry
            or provider.active_extent < 0
            or provider.active_extent > source_record.width
        ):
            raise ValueError("reverse provider parent has another geometry/extent")
        core._validate_geometry(complete, geometry)
        if not provider.level:
            return None
        return core.sources.children(provider.source)

    def validate_action(self, action: FieldCellActionID) -> None:
        self.core.validate_action(action)

    def compose_actions(
        self, before: FieldCellActionID, after: FieldCellActionID
    ) -> FieldCellActionID:
        return self.core.compose_actions(before, after)

    def signature(
        self, action: FieldCellActionID, geometry: FieldGeometryID
    ) -> PortSignatureID:
        return self.core.signature(action, geometry)

    def compile_leaf(
        self,
        complete: FieldCellActionID,
        consumer: FieldCellActionID,
        provider: ProviderImageInput,
        geometry: FieldGeometryID,
        signature: object,
    ) -> FieldImageCandidate:
        self.validate_action(consumer)
        self._validate_provider(complete, provider, geometry)
        if provider.level != 0:
            raise ValueError("reverse provider leaf substitution received a parent")
        if self.signature(complete, geometry) != signature:
            raise ValueError("reverse provider leaf has another complete signature")
        self.core.ledger.bump("reverse_provider_leaf_substitutions")
        return self.core._compile(complete, provider.source)

    def join(
        self,
        complete: FieldCellActionID,
        provider: ProviderImageInput,
        left: FieldImageID,
        right: FieldImageID,
        geometry: FieldGeometryID,
        signature: object,
    ) -> FieldImageCandidate:
        children = self._validate_provider(complete, provider, geometry)
        if children is None:
            raise ValueError("reverse provider parent substitution received a leaf")
        if self.signature(complete, geometry) != signature:
            raise ValueError("reverse provider parent has another complete signature")
        if type(left) is not FieldImageID or type(right) is not FieldImageID:
            raise TypeError("reverse provider parent requires complete child images")
        left_source = children[0]
        left_width = self.core.sources.resolve(left_source).width
        left_extent = min(provider.active_extent, left_width)
        right_extent = max(0, provider.active_extent - left_width)
        self.core.ledger.bump("reverse_provider_parent_substitutions")
        return self.core._join_completed(
            complete,
            provider.source,
            left,
            right,
            geometry,
            left_extent,
            right_extent,
        )
