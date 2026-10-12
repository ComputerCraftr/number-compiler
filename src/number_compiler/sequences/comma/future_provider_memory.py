"""Conservative ledger estimates for FutureCID provider memory ownership."""

from __future__ import annotations

from collections.abc import Mapping
from types import MappingProxyType
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.sequences.comma.future_provider import SemanticFutureProvider


def provider_node_cost(digest: str, provider: SemanticFutureProvider) -> int:
    if digest != provider.artifact_sha256:
        raise ValueError("future provider ledger key differs from its artifact digest")
    # Include the class signatures, slots, outer table and tuple bindings.
    return len(provider._source_classes) + 10 * len(provider._classes) + 7


def candidate_workspace_cost(record: Mapping[str, object], source_count: int) -> int:
    """Reserve decoded semantic tuples while candidate validation is active.

    The serialized byte limit bounds input size; this estimate does not claim
    to measure the parser's raw JSON object graph or process RSS peak.
    """
    if type(record) not in (dict, MappingProxyType):
        return 0
    controls = record.get("controls")
    if type(controls) is not list or not 0 < len(controls) <= source_count:
        return 0
    # Source IDs and their tuple coexist; class rows overlap their builder list.
    signature_nodes = 6 * len(controls) + 5
    return 2 * source_count + 5 * len(controls) + 2 + signature_nodes
