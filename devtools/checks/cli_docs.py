"""Keep CLI documentation aligned with the admitted parser without executing queries."""

from __future__ import annotations

import re
import shlex
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path

from number_compiler.api.cli_requests import parse_request
from number_compiler.api.family_registry import CAPABILITIES
from number_compiler.api.observation_views import VIEW_FLAGS

START = "<!-- cli-capabilities:start -->"
END = "<!-- cli-capabilities:end -->"
VIEWS_START = "<!-- cli-views:start -->"
VIEWS_END = "<!-- cli-views:end -->"


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


def observation_view_table() -> str:
    rows = [
        "| Category | View flag | Views |",
        "| --- | --- | --- |",
    ]
    for category, flag in VIEW_FLAGS.items():
        by_view: dict[str, list[str]] = {}
        for family, spec in CAPABILITIES.items():
            for view in spec.views:
                if view.category is category:
                    families = by_view.setdefault(view.view.label, [])
                    if family.value not in families:
                        families.append(family.value)
        if by_view:
            descriptions = ", ".join(
                f"`{label}` ({', '.join(families)})"
                for label, families in by_view.items()
            )
            rows.append(f"| `{category}` | `--{flag}` | {descriptions} |")
    return "\n".join(rows)


def check_cli_docs(root: Path) -> list[str]:
    errors: list[str] = []
    guide = root / "docs/cli.md"
    if guide.exists():
        text = guide.read_text()
        expected = f"{START}\n{capability_table()}\n{END}"
        if expected not in text:
            errors.append("docs/cli.md:1: generated CLI capability table is stale")
        expected = f"{VIEWS_START}\n{observation_view_table()}\n{VIEWS_END}"
        if expected not in text:
            errors.append(
                "docs/cli.md:1: generated CLI observation view table is stale"
            )
    for path in (root / "README.md", guide, root / "docs/development.md"):
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
            # Validate the installed CLI examples with native feature flags too.
            match = re.match(
                r"(?:NUMBER_COMPILER_[A-Z0-9_]+=[01]\s+)*number-compiler\s+", command
            )
            if match is None:
                continue
            try:
                with redirect_stdout(StringIO()), redirect_stderr(StringIO()):
                    parse_request(shlex.split(command[match.end() :]))
            except (SystemExit, ValueError) as error:
                if isinstance(error, SystemExit) and error.code == 0:
                    continue
                errors.append(
                    f"{path.relative_to(root)}:{number}: invalid CLI example: {error}"
                )
    return errors
