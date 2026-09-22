"""Reuse complete admitted dyadic effects while retaining occurrence authority.

Low source bits determine the affine action, branch support and prefix weights.
Singleton cycle shortcuts also depend on the high fiber. Those use an exact
key unless a positive lower bound excludes the cycle throughout the block.
Carry/F5 projections never serve as complete-effect identities here.
"""

from __future__ import annotations

from collections.abc import Hashable
from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnActionID,
    DyadicReturnImageID,
    DyadicReturnSourceID,
    _ImageNode,
)
from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageCandidate,
    SourceImageView,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_images import (
        DyadicReturnImageWorkspace,
    )


def _require_published_view(
    workspace: DyadicReturnImageWorkspace, view: SourceImageView
) -> None:
    """Bind all view fields to the scheduler's sealed image publication."""
    published = workspace.scheduler._source_image_core().view(view.identity)
    # Dataclass equality would accept bool/float aliases for integer fields.
    # The sealed record owns these immutable objects; a copied view has no
    # authority to replace them, even when its values compare equal.
    if (
        type(view) is not SourceImageView
        or view.binding is not published.binding
        or view.payload is not published.payload
        or type(view.failure_prefix) is not type(published.failure_prefix)
        or view.failure_prefix != published.failure_prefix
    ):
        raise ValueError("dyadic return reuse view differs from its publication")


def admitted_input_key(
    workspace: DyadicReturnImageWorkspace, action: Hashable, source: SourceImageView
) -> tuple[str, int, int] | tuple[str, int, int, int] | None:
    _require_published_view(workspace, source)
    workspace.validate_action(action)
    workspace.validate_payload(source.payload)
    workspace.validate_source(source.binding.source)
    assert type(action) is DyadicReturnActionID
    assert type(source.binding.source) is DyadicReturnSourceID
    assert type(source.payload) is DyadicReturnImageID
    admitted = workspace.image_node(source.payload)
    if (
        admitted.source != source.binding.source
        or admitted.action != source.binding.action
        or source.binding.family != workspace.family
        or source.binding.semantic_version != workspace.semantic_version
    ):
        raise ValueError("dyadic return reuse source view lost its occurrence binding")
    node = workspace.source_node(source.binding.source)
    width = workspace.action_node(action).width
    if (
        source.binding.action != workspace.identity
        or width != node.precision
        or not width
    ):
        return None
    # The scheduler namespaces this key by adapter version and exact action ID.
    cycle = workspace.law.cycle
    if cycle is not None and node.exact:
        # Each branch is >= x/2 when both offsets are nonnegative. The high
        # fiber bounds every state through this width, so no singleton shortcut
        # can be reached if it is above every cycle state.
        excludes_cycle = min(workspace.law.offsets) >= 0 and node.lift > max(
            cycle.states
        )
        if not excludes_cycle:
            return ("singleton", node.residue, node.precision, node.lift)
    return ("cylinder", node.residue, node.precision)


def transport_reuse(
    workspace: DyadicReturnImageWorkspace,
    action: Hashable,
    cached_source: SourceImageView,
    cached_result: SourceImageView,
    source: SourceImageView,
) -> SourceImageCandidate:
    _require_published_view(workspace, cached_result)
    key = admitted_input_key(workspace, action, source)
    if key is None or key != admitted_input_key(workspace, action, cached_source):
        raise ValueError("dyadic return reuse requires the same admitted cylinder")
    workspace.validate_payload(cached_result.payload)
    assert type(action) is DyadicReturnActionID
    assert type(cached_result.payload) is DyadicReturnImageID
    assert type(source.binding.source) is DyadicReturnSourceID
    cached = workspace.image_node(cached_result.payload)
    if (
        cached.source != cached_source.binding.source
        or cached.action != action
        or cached_result.binding.source != cached.source
        or cached_result.binding.action != action
        or cached_result.failure_prefix is not None
    ):
        raise ValueError("dyadic return cached effect lost its source/action binding")
    summary = cached.summary
    if summary.cycle is not None and key[0] != "singleton":
        raise ValueError("a singleton cycle cannot represent a high-fiber cylinder")
    # Share complete immutable support; issue a new source-bound image. No
    # endpoint, branch word, spatial coefficient, or midpoint is rediscovered.
    payload = workspace._append_image(
        _ImageNode(source.binding.source, action, summary)
    )
    workspace._bump("complete_effect_reuses")
    workspace._bump("reused_temporal_extent", summary.width)
    transfer = summary.transfer
    return SourceImageCandidate(
        payload,
        summary.width,
        (
            workspace.law.descriptor,
            transfer.upper,
            transfer.offset,
            transfer.lower,
            summary.odd_steps,
        ),
        precision=summary.width,
    )
