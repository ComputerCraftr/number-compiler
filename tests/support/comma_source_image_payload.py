"""Typed source-image access shared by comma consumer regressions."""

from number_compiler.hashlife.execution.source_image_inventory import SourceImageID
from number_compiler.sequences.comma.action_arena import CommaActionID
from number_compiler.sequences.comma.boundary_receipt import CommaImagePayload
from number_compiler.sequences.comma.image_adapter import (
    CommaOccurrenceID,
    CommaSource,
)
from number_compiler.sequences.comma.power import CommaTerm


def source_image_payload(
    term: CommaTerm,
    source: CommaSource | CommaOccurrenceID | SourceImageID,
    action: CommaActionID,
) -> CommaImagePayload:
    """Apply one source action and require its family-owned payload type."""
    image = term.scheduler.source_image(term.adapter, source, action)
    payload = term.scheduler.source_image_core().view(image).payload
    if type(payload) is not CommaImagePayload:
        raise AssertionError("comma source image returned a foreign payload")
    return payload
