"""The reverse image normalizer shares the exact carry-transfer owner."""

from __future__ import annotations

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_workspace import (
    ReverseSourceImageWorkspace,
)


def test_source_image_normalization_matches_exact_divmod_for_all_pair_symbols() -> None:
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 0, 0)
    try:
        for base in range(2, 20):
            for pair in range(2 * base - 1):
                for incoming in (0, 1):
                    quotient, digit = divmod(pair + incoming, base)
                    assert workspace.adapter._normalized(pair, incoming, base) == (
                        quotient,
                        digit,
                    )
    finally:
        workspace.dispose()
