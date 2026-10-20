"""Read-only description metrics for canonical run-length source words."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.radix import bit_width

if TYPE_CHECKING:
    from number_compiler.arithmetic.automata.program_word import (
        CanonicalWord,
        SourceWord,
    )


def word_metrics(root: SourceWord) -> dict[str, int]:
    """Charge the retained RLE/SLP word, including references and run parameters."""
    from number_compiler.arithmetic.automata.program_word import (
        SourceWordSuffix,
        validate_source_word,
    )

    if isinstance(root, SourceWordSuffix):
        validate_source_word(root)
        stack = [root.source, *root.parts]
        cursor_nodes = 1
        cursor_refs = 1 + len(root.parts)
        cursor_bits = (
            bit_width(root.start) + bit_width(root.length) + bit_width(root.run_count)
        )
    else:
        validate_source_word(root)
        stack = [root]
        cursor_nodes = cursor_refs = cursor_bits = 0
    seen: dict[int, CanonicalWord] = {}
    while stack:
        node = stack.pop()
        if node.node_id in seen:
            continue
        seen[node.node_id] = node
        if node.left is not None:
            stack.append(node.left)
        if node.right is not None:
            stack.append(node.right)
    refs = cursor_refs + sum(
        int(node.left is not None) + int(node.right is not None)
        for node in seen.values()
    )
    param_bits = cursor_bits
    for node in seen.values():
        if node.run_count == 1:
            param_bits += bit_width(int(node.symbol or 0)) + bit_width(node.run_length)
        else:
            param_bits += bit_width(node.length) + bit_width(node.run_count)
    node_count = len(seen) + cursor_nodes
    id_bits = bit_width(node_count)
    return {
        "length": root.length,
        "runs": root.run_count,
        "nodes": node_count,
        "references": refs,
        "parameter_bits": param_bits,
        "description_bits": param_bits + node_count + refs * id_bits,
    }
