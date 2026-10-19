"""Keep CLI documentation aligned with the admitted parser without executing queries."""

from __future__ import annotations

import shlex
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path

from number_compiler.api.cli_requests import parse_request
from number_compiler.api.family_registry import CAPABILITIES

START = "<!-- cli-capabilities:start -->"
END = "<!-- cli-capabilities:end -->"


def capability_table() -> str:
    rows = [
        "| Family | Index unit | Parameters | Term information | Event information |",
        "| --- | --- | --- | --- | --- |",
    ]
    for family, capability in CAPABILITIES.items():
        parameters = ", ".join(f"`--{name}`" for name in capability.parameters) or "—"
        nth = ", ".join(f"`{name}`" for name in capability.nth_info)
        events = ", ".join(f"`{name}`" for name in capability.event_info) or "—"
        rows.append(
            f"| `{family}` | `{capability.unit}` | {parameters} | {nth} | {events} |"
        )
    return "\n".join(rows)


def check_cli_docs(root: Path) -> list[str]:
    errors: list[str] = []
    guide = root / "docs/cli.md"
    if guide.exists():
        text = guide.read_text()
        expected = f"{START}\n{capability_table()}\n{END}"
        if expected not in text:
            errors.append("docs/cli.md:1: generated CLI capability table is stale")
    for path in (root / "README.md", guide):
        if not path.exists():
            continue
        fenced = False
        pending = ""
        for number, line in enumerate(path.read_text().splitlines(), 1):
            if line.startswith("```"):
                fenced = not fenced
                continue
            if not fenced:
                continue
            command = pending + line.strip()
            if command.endswith("\\"):
                pending = command[:-1] + " "
                continue
            pending = ""
            if not command.startswith("number-compiler "):
                continue
            try:
                with redirect_stdout(StringIO()), redirect_stderr(StringIO()):
                    parse_request(shlex.split(command)[1:])
            except (SystemExit, ValueError) as error:
                if isinstance(error, SystemExit) and error.code == 0:
                    continue
                errors.append(
                    f"{path.relative_to(root)}:{number}: invalid CLI example: {error}"
                )
    return errors
