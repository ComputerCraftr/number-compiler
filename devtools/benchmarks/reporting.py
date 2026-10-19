"""Shared output plumbing for benchmark probes.

The probes keep their payload construction and naming independent; this module
only owns the repeated JSON-file/terminal emission mechanics.
"""

from __future__ import annotations

import json
from pathlib import Path


def write_json_report(path: Path, payload: object) -> None:
    """Create ``path``'s parent, persist a readable JSON payload, and print it."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps(payload, indent=2, sort_keys=True))


def write_markdown_json_report(
    markdown_path: Path, json_path: Path, markdown: str, payload: object
) -> None:
    """Persist a paired Markdown/JSON probe report and echo the Markdown."""
    markdown_path.write_text(markdown)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(markdown, end="")
