"""Conditional parent-first traversal over completed provider inputs.

This module supplies a generic executor, not a family successor constructor.
Completeness depends on the adapter's source-bound composition and join laws.
"""

from __future__ import annotations

from typing import Protocol

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    FieldCellActionID,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.continuations.provider_absorption import (
    ProviderAbsorptionArena,
)
from number_compiler.hashlife.execution.continuations.provider_image_input import (
    ProviderImageInput,
    ProviderImageInputArena,
    ProviderImageInputID,
)
from number_compiler.hashlife.execution.field_executor import FieldImageCandidate
from number_compiler.hashlife.execution.field_images import (
    FieldImageID,
    FieldImageRecord,
    ImageRequestKey,
    RecursiveFieldImageArena,
)
from number_compiler.hashlife.execution.source_image_seals import (
    require_immutable_key,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)


class ProviderFieldImageAdapter(Protocol):
    """Output-complete substitution law for one consumer over a provider."""

    def validate_action(self, action: FieldCellActionID) -> None: ...

    def compose_actions(
        self,
        before: FieldCellActionID,
        after: FieldCellActionID,
    ) -> FieldCellActionID: ...

    def signature(
        self,
        action: FieldCellActionID,
        geometry: FieldGeometryID,
    ) -> PortSignatureID: ...

    def compile_leaf(
        self,
        complete: FieldCellActionID,
        consumer: FieldCellActionID,
        provider: ProviderImageInput,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> FieldImageCandidate: ...

    def join(
        self,
        complete: FieldCellActionID,
        provider: ProviderImageInput,
        left: FieldImageID,
        right: FieldImageID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> FieldImageCandidate: ...


class _ProviderImageWork:
    """Charged transient traversal state, released even if publication fails."""

    def __init__(self, ledger: ResourceLedger, owner: int) -> None:
        self.ledger, self.owner = ledger, owner
        self.stack: list[
            tuple[
                ProviderImageInputID,
                FieldGeometryID,
                bool,
                tuple[object | None, object | None] | None,
            ]
        ] = []
        self.built: dict[
            tuple[ProviderImageInputID, FieldGeometryID], FieldImageID
        ] = {}

    def push(
        self,
        frame: tuple[
            ProviderImageInputID,
            FieldGeometryID,
            bool,
            tuple[object | None, object | None] | None,
        ],
    ) -> None:
        self.ledger.reserve(self.owner, entries=1, nodes=1)
        try:
            self.stack.append(frame)
        except BaseException:
            self.ledger.release(self.owner, entries=1, nodes=1)
            raise

    def pop(
        self,
    ) -> tuple[
        ProviderImageInputID,
        FieldGeometryID,
        bool,
        tuple[object | None, object | None] | None,
    ]:
        frame = self.stack.pop()
        self.ledger.release(self.owner, entries=1, nodes=1)
        self.ledger.bump(_execution_keys.PROVIDER_FIELD_IMAGE_FRAME_VISITS)
        return frame

    def remember(
        self, key: tuple[ProviderImageInputID, FieldGeometryID], image: FieldImageID
    ) -> None:
        fresh = key not in self.built
        if fresh:
            self.ledger.reserve(self.owner, entries=1, nodes=1)
        try:
            self.built[key] = image
        except BaseException:
            if fresh:
                self.ledger.release(self.owner, entries=1, nodes=1)
            raise

    def close(self) -> None:
        count = len(self.stack) + len(self.built)
        self.stack.clear()
        self.built.clear()
        self.ledger.release(self.owner, entries=count, nodes=count)


class ProviderFieldImageExecutor:
    """Traverse completed images using an adapter's full substitution law.

    The executor itself never reads midpoint symbols. Its adapter must supply
    normalized chronological composition, leaf substitution and spatial joins;
    this traversal does not derive those laws from carry-only projections or
    establish that a family CLI has adopted the adapter.
    """

    def __init__(
        self,
        providers: ProviderAbsorptionArena,
        inputs: ProviderImageInputArena,
        images: RecursiveFieldImageArena,
        adapter: ProviderFieldImageAdapter,
    ) -> None:
        if (
            providers is not inputs.providers
            or inputs.images is not images
            or providers.ledger is not images.ledger
        ):
            raise ValueError("provider field execution requires one index runtime")
        self.providers, self.inputs, self.images, self.adapter = (
            providers,
            inputs,
            images,
            adapter,
        )
        self.ledger = images.ledger
        self._workspace_owner = self.ledger.register(
            f"provider-field-work-{self.ledger.owner_count}", "provider_image_workspace"
        )
        self.ledger.register_execution_root(self)

    def image(
        self,
        consumer: FieldCellActionID,
        provider: ProviderImageInputID,
        geometry: FieldGeometryID,
    ) -> FieldImageID:
        """Compile a complete spatial parent, probing normalized IDs first."""
        self.images.geometries.resolve(geometry)
        self.adapter.validate_action(consumer)
        root = self.inputs.resolve(provider)
        before = self.providers.validate_occurrence(root.binding).action
        complete = self.adapter.compose_actions(before, consumer)
        self.adapter.validate_action(complete)
        signature = self.adapter.signature(complete, geometry)
        self._validate_context(complete, root, geometry)
        root_key = ImageRequestKey(
            complete,
            root.source,
            geometry,
            signature,
            root.active_extent,
            root.context,
        )
        cached = self.images.probe(root_key)
        self.ledger.bump(_execution_keys.PROVIDER_FIELD_IMAGE_REQUESTS)
        if cached is not None:
            self.ledger.bump(_execution_keys.PROVIDER_FIELD_IMAGE_EARLY_HITS)
            return cached

        work = _ProviderImageWork(self.ledger, self._workspace_owner)
        try:
            work.push((provider, geometry, False, None))
            while work.stack:
                current, current_geometry, ready, child_contexts = work.pop()
                record = self.inputs.resolve(current)
                self._validate_context(complete, record, current_geometry)
                current_signature = self.adapter.signature(complete, current_geometry)
                key = ImageRequestKey(
                    complete,
                    record.source,
                    current_geometry,
                    current_signature,
                    record.active_extent,
                    record.context,
                )
                found = self.images.probe(key)
                if found is not None:
                    work.remember((current, current_geometry), found)
                    continue
                if record.level and not ready:
                    child_contexts = self._child_contexts(
                        complete, record, current_geometry
                    )
                    left, right = self.inputs.children(
                        current,
                        child_contexts,
                        complete=complete,
                        geometry=current_geometry,
                    )
                    work.push((current, current_geometry, True, child_contexts))
                    work.push(
                        (
                            right,
                            self.images.geometries.child(current_geometry, 1),
                            False,
                            None,
                        )
                    )
                    work.push(
                        (
                            left,
                            self.images.geometries.child(current_geometry, 0),
                            False,
                            None,
                        )
                    )
                    continue
                left_image: FieldImageID | None
                right_image: FieldImageID | None
                if record.level:
                    if child_contexts is None:
                        raise ValueError("ready provider frame lost its child contexts")
                    left, right = self.inputs.children(
                        current,
                        child_contexts,
                        complete=complete,
                        geometry=current_geometry,
                    )
                    left_image = work.built[
                        left, self.images.geometries.child(current_geometry, 0)
                    ]
                    right_image = work.built[
                        right, self.images.geometries.child(current_geometry, 1)
                    ]
                    candidate = self.adapter.join(
                        complete,
                        record,
                        left_image,
                        right_image,
                        current_geometry,
                        current_signature,
                    )
                else:
                    candidate = self.adapter.compile_leaf(
                        complete,
                        consumer,
                        record,
                        current_geometry,
                        current_signature,
                    )
                    left_image = right_image = None
                node = FieldImageRecord(
                    record.level,
                    left_image,
                    right_image,
                    candidate.interface,
                    candidate.output,
                    current_geometry,
                    candidate.summary,
                )
                work.remember(
                    (current, current_geometry), self.images.publish(key, node)
                )
                self.ledger.bump(_execution_keys.PROVIDER_FIELD_IMAGE_EVALUATIONS)
            return work.built[provider, geometry]
        finally:
            work.close()

    def _validate_context(
        self,
        complete: FieldCellActionID,
        provider: ProviderImageInput,
        geometry: FieldGeometryID,
    ) -> None:
        context = provider.context
        if context is None:
            return
        self.ledger.bump(_execution_keys.PROVIDER_FIELD_CONTEXT_VALIDATION_ATTEMPTS)
        validator = getattr(self.adapter, "validate_context", None)
        if not callable(validator):
            self.ledger.bump(_execution_keys.PROVIDER_FIELD_CONTEXT_VALIDATION_FAILURES)
            raise TypeError(
                "context-qualified provider execution requires context validation"
            )
        try:
            validator(context, complete, provider, geometry)
        except BaseException:
            self.ledger.bump(_execution_keys.PROVIDER_FIELD_CONTEXT_VALIDATION_FAILURES)
            raise
        self.ledger.bump(_execution_keys.PROVIDER_FIELD_CONTEXT_VALIDATION_EVALUATIONS)

    def _child_contexts(
        self,
        complete: FieldCellActionID,
        provider: ProviderImageInput,
        geometry: FieldGeometryID,
    ) -> tuple[object | None, object | None]:
        derive = getattr(self.adapter, "child_contexts", None)
        if not callable(derive):
            if provider.context is not None:
                self.ledger.bump(
                    _execution_keys.PROVIDER_FIELD_CHILD_CONTEXT_DERIVATION_ATTEMPTS
                )
                self.ledger.bump(
                    _execution_keys.PROVIDER_FIELD_CHILD_CONTEXT_DERIVATION_FAILURES
                )
                raise TypeError(
                    "context-qualified provider execution requires explicit child contexts"
                )
            return None, None
        self.ledger.bump(
            _execution_keys.PROVIDER_FIELD_CHILD_CONTEXT_DERIVATION_ATTEMPTS
        )
        try:
            result: object = derive(complete, provider, geometry)
            if not is_exact_object_tuple(result) or len(result) != 2:
                raise TypeError(
                    "provider adapter must return an exact child context pair"
                )
            contexts = result
            for context in contexts:
                if context is not None:
                    require_immutable_key(context, "provider child image context")
        except BaseException:
            self.ledger.bump(
                _execution_keys.PROVIDER_FIELD_CHILD_CONTEXT_DERIVATION_FAILURES
            )
            raise
        self.ledger.bump(
            _execution_keys.PROVIDER_FIELD_CHILD_CONTEXT_DERIVATION_EVALUATIONS
        )
        return contexts


__all__ = ["ProviderFieldImageAdapter", "ProviderFieldImageExecutor"]
