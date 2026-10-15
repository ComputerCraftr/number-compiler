"""Postorder application implementation owned by SourceBoundSchedulerCore.

Split contexts refine arithmetic precision inside this same scheduler. They do
not authorize equality of projections as equality of successor occurrences.
"""

from __future__ import annotations

from collections.abc import Hashable
from contextlib import AbstractContextManager, nullcontext
from typing import Protocol, runtime_checkable

from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundCompositeAdapter,
    SourceBoundImageAdapter,
    SourceBoundSchedulerCore,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageView,
    _ApplyFrame,
    _ApplyKey,
    _RelativeKey,
)
from number_compiler.hashlife.execution.source_image_seals import _typed_equal
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)


@runtime_checkable
class SourceBoundSplitContextAdapter(Protocol):
    """Issue exact child source contexts for total arithmetic refinement.

    Each hook must issue an authenticated source in the adapter's own arena.
    The first child may discard precision only when the parent retains the
    information needed to transport the second child and reconstruct its image.
    Guarded failure-index transport is not provided by this contract.
    """

    def first_child_source(
        self,
        parent_action: Hashable,
        parent_source: SourceImageView,
        before_action: Hashable,
        after_action: Hashable,
    ) -> Hashable: ...

    def second_child_source(
        self,
        parent_action: Hashable,
        parent_source: SourceImageView,
        before_result: SourceImageView,
        after_action: Hashable,
    ) -> Hashable: ...


@runtime_checkable
class SourceBoundCompositeTransactionalAdapter(Protocol):
    """Keep adapter candidate records provisional through scheduler publication."""

    def composite_transaction(self) -> AbstractContextManager[None]: ...


def apply_source_image(
    self: SourceBoundSchedulerCore,
    adapter: SourceBoundImageAdapter,
    source: Hashable,
    action: Hashable,
    *,
    demand: SourceImageDemand | None,
) -> SourceImageID:
    adapter_key = self._registered(adapter)
    self._validate_key(source, "source image source")
    self._validate_key(action, "source image action")
    adapter.validate_action(action)
    self.ledger.bump(_execution_keys.SOURCE_IMAGE_APPLICATION_REQUESTS)
    split = adapter if isinstance(adapter, SourceBoundSplitContextAdapter) else None
    transaction_factory = (
        adapter.composite_transaction
        if isinstance(adapter, SourceBoundCompositeTransactionalAdapter)
        else None
    )

    def candidate_transaction() -> AbstractContextManager[None]:
        return nullcontext() if transaction_factory is None else transaction_factory()

    origin = self._origin(adapter, source)
    workspace = self._workspace
    if workspace.running or len(workspace):
        raise RuntimeError("source image workspace is already active")
    workspace_credit = 0

    def push_frame(frame: _ApplyFrame) -> None:
        nonlocal workspace_credit
        self.ledger.reserve(self._workspace_owner, entries=1, nodes=1)
        try:
            workspace.push_frame(frame)
        except BaseException:
            self.ledger.release(self._workspace_owner, entries=1, nodes=1)
            raise
        workspace_credit += 1

    def push_value(image: SourceImageID) -> None:
        nonlocal workspace_credit
        self.ledger.reserve(self._workspace_owner, entries=1, nodes=1)
        try:
            workspace.push_value(image)
        except BaseException:
            self.ledger.release(self._workspace_owner, entries=1, nodes=1)
            raise
        workspace_credit += 1

    def release_workspace() -> None:
        nonlocal workspace_credit
        self.ledger.release(self._workspace_owner, entries=1, nodes=1)
        workspace_credit -= 1

    try:
        workspace.running = True
        push_frame(_ApplyFrame(origin, action))
        while workspace.has_frames():
            peak = len(workspace)
            previous = self.ledger.counters.get(
                _execution_keys.SOURCE_IMAGE_WORKSPACE_PEAK, 0
            )
            if peak > previous:
                self.ledger.bump(
                    _execution_keys.SOURCE_IMAGE_WORKSPACE_PEAK,
                    peak - previous,
                )
            self.ledger.bump(_execution_keys.SOURCE_IMAGE_POSTORDER_FRAMES)
            frame = workspace.pop_frame()
            release_workspace()
            apply_key = _ApplyKey(adapter_key, frame.source, frame.action)
            action_key = adapter_key[0], adapter_key[1], frame.action
            if frame.stage == 0:
                self.ledger.bump(_execution_keys.SOURCE_IMAGE_APPLICATION_ATTEMPTS)
                if (
                    split is not None
                    and self.view(frame.source).failure_prefix is not None
                ):
                    raise ValueError("split contexts cannot transport guarded failure")
                found = self._applications.get(apply_key)
                if found is not None:
                    self._validate_application_binding(adapter, apply_key, found)
                    if (
                        split is not None
                        and self.view(found).failure_prefix is not None
                    ):
                        raise ValueError(
                            "split contexts cannot transport guarded failure"
                        )
                    push_value(found)
                    self.ledger.bump(_execution_keys.SOURCE_IMAGE_APPLICATION_HITS)
                    continue
                source_view = self.view(frame.source)
                admitted_input = adapter.admitted_input_key(frame.action, source_view)
                relative_key = None
                if admitted_input is not None:
                    self._validate_key(admitted_input, "source image admitted input")
                    relative_key = _RelativeKey(
                        adapter_key, frame.action, admitted_input
                    )
                    cached = self._relative.get(relative_key)
                    if cached is not None:
                        cached_source = self.view(cached.source)
                        cached_result = self.view(cached.result)
                        if not _typed_equal(
                            adapter.admitted_input_key(frame.action, cached_source),
                            admitted_input,
                        ):
                            raise ValueError(
                                "relative transfer has another admitted input"
                            )
                        self._validate_application_binding(
                            adapter,
                            _ApplyKey(adapter_key, cached.source, frame.action),
                            cached.result,
                        )
                        with candidate_transaction():
                            candidate = adapter.transport_reuse(
                                frame.action,
                                cached_source,
                                cached_result,
                                source_view,
                            )
                            result = _publish_candidate(
                                self,
                                adapter,
                                apply_key,
                                source_view,
                                frame.action,
                                candidate,
                                None,
                                split is not None,
                            )
                        push_value(result)
                        self.ledger.bump(
                            _execution_keys.SOURCE_IMAGE_RELATIVE_TRANSFER_HITS
                        )
                        continue
                self.ledger.bump(_execution_keys.SOURCE_IMAGE_APPLICATION_MISSES)
                children = adapter.action_children(frame.action)
                if children is None:
                    with candidate_transaction():
                        candidate = adapter.apply_primitive(frame.action, source_view)
                        result = _publish_candidate(
                            self,
                            adapter,
                            apply_key,
                            source_view,
                            frame.action,
                            candidate,
                            relative_key,
                            split is not None,
                        )
                    push_value(result)
                    self.ledger.bump(
                        _execution_keys.SOURCE_IMAGE_PRIMITIVE_APPLICATIONS
                    )
                    continue
                if type(children) is not tuple or len(children) != 2:
                    raise TypeError(
                        "source image action requires before/after children"
                    )
                before, after = children
                adapter.validate_action(before)
                adapter.validate_action(after)
                if frame.action in children:
                    raise ValueError(
                        "source image action cannot directly contain itself"
                    )
                if workspace.contains_active(action_key):
                    raise ValueError("source image action graph contains a cycle")
                if not _typed_equal(
                    adapter.compose_actions(before, after), frame.action
                ):
                    raise ValueError(
                        "source image children do not compose to their parent"
                    )
                if isinstance(adapter, SourceBoundCompositeAdapter):
                    with candidate_transaction():
                        composite_candidate = adapter.apply_composite(
                            frame.action, source_view, demand
                        )
                        if composite_candidate is not None:
                            composite_result = _publish_candidate(
                                self,
                                adapter,
                                apply_key,
                                source_view,
                                frame.action,
                                composite_candidate,
                                relative_key,
                                split is not None,
                            )
                    if composite_candidate is not None:
                        push_value(composite_result)
                        self.ledger.bump(
                            "source_image_composite_applications"
                            if demand is None
                            else "source_image_demanded_composite_applications"
                        )
                        continue
                self.ledger.reserve(self._workspace_owner, entries=1, nodes=1)
                try:
                    workspace.add_active(action_key)
                except BaseException:
                    self.ledger.release(self._workspace_owner, entries=1, nodes=1)
                    raise
                workspace_credit += 1
                frame.stage, frame.children, frame.relative_key = (
                    1,
                    children,
                    relative_key,
                )
                frame.before_source = (
                    frame.source
                    if split is None
                    else self._origin(
                        adapter,
                        split.first_child_source(
                            frame.action, source_view, before, after
                        ),
                    )
                )
                if split is not None:
                    self.ledger.bump(_execution_keys.SOURCE_IMAGE_FIRST_CHILD_CONTEXTS)
                push_frame(frame)
                push_frame(_ApplyFrame(frame.before_source, before))
                continue
            if frame.stage == 1:
                if (
                    frame.children is None
                    or frame.before_source is None
                    or not workspace.has_values()
                ):
                    raise AssertionError("source image frame lost its before result")
                before_image = workspace.pop_value()
                release_workspace()
                if split is not None:
                    self._validate_application_binding(
                        adapter,
                        _ApplyKey(adapter_key, frame.before_source, frame.children[0]),
                        before_image,
                    )
                frame.stage, frame.before = 2, before_image
                frame.after_source = (
                    before_image
                    if split is None
                    else self._origin(
                        adapter,
                        split.second_child_source(
                            frame.action,
                            self.view(frame.source),
                            self.view(before_image),
                            frame.children[1],
                        ),
                    )
                )
                if split is not None:
                    self.ledger.bump(_execution_keys.SOURCE_IMAGE_SECOND_CHILD_CONTEXTS)
                push_frame(frame)
                push_frame(_ApplyFrame(frame.after_source, frame.children[1]))
                continue
            if (
                frame.children is None
                or frame.before is None
                or frame.after_source is None
                or not workspace.has_values()
            ):
                raise AssertionError(
                    "source image frame lost chronological dependencies"
                )
            after_image = workspace.pop_value()
            release_workspace()
            source_view = self.view(frame.source)
            before_view = self.view(frame.before)
            after_view = self.view(after_image)
            if split is not None:
                self._validate_application_binding(
                    adapter,
                    _ApplyKey(adapter_key, frame.after_source, frame.children[1]),
                    after_image,
                )
            expected = adapter.compose_actions(source_view.binding.action, frame.action)
            if split is None and not _typed_equal(after_view.binding.action, expected):
                raise ValueError(
                    "source image chronology produced another action binding"
                )
            candidate = adapter.compose_chronological(
                frame.action, source_view, before_view, after_view
            )
            if split is not None and any(
                view.failure_prefix is not None
                for view in (source_view, before_view, after_view)
            ):
                raise ValueError("split contexts cannot transport guarded failure")
            if candidate.failure_prefix != after_view.failure_prefix:
                raise ValueError(
                    "source image composition discarded its chronological failure"
                )
            result = self._publish_application_result(
                apply_key,
                source_view.binding.source,
                expected,
                candidate,
                relative_key=frame.relative_key,
            )
            if not workspace.contains_active(action_key):
                raise AssertionError("source image action lost its active frame")
            workspace.remove_active(action_key)
            release_workspace()
            push_value(result)
            self.ledger.bump(_execution_keys.SOURCE_IMAGE_CHRONOLOGICAL_COMPOSITIONS)
        if workspace.value_count() != 1:
            raise AssertionError("source image scheduler produced multiple results")
        result = workspace.pop_value()
        release_workspace()
        return result
    finally:
        diverged = workspace_credit != len(workspace)
        workspace.clear()
        if workspace_credit:
            self.ledger.release(
                self._workspace_owner,
                entries=workspace_credit,
                nodes=workspace_credit,
            )
        if diverged:
            raise AssertionError("source image workspace accounting diverged")


def _publish_candidate(
    core: SourceBoundSchedulerCore,
    adapter: SourceBoundImageAdapter,
    key: _ApplyKey,
    source: SourceImageView,
    action: Hashable,
    candidate: SourceImageCandidate,
    relative_key: _RelativeKey | None,
    total: bool,
) -> SourceImageID:
    """Admit totality and cumulative action identically for primitive/composite publication."""
    if total and candidate.failure_prefix is not None:
        raise ValueError("split contexts require total arithmetic")
    cumulative = adapter.compose_actions(source.binding.action, action)
    return core._publish_application_result(
        key, source.binding.source, cumulative, candidate, relative_key=relative_key
    )
