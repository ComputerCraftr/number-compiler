"""Validate maintained documentation without executing research or using the network."""

from __future__ import annotations

import argparse
import re
import subprocess
import tomllib
from collections import Counter
from datetime import date, timedelta
from pathlib import Path
from urllib.parse import unquote, urlsplit

from devtools.checks.sprint_scaffold import HEADINGS, refresh_index
from devtools.paths import repository_root

_LINK = re.compile(r"!?\[[^\]\n]*\]\((<[^>]+>|[^)\s]+)(?:\s+[^)]*)?\)")
_REFERENCE = re.compile(r"^\s*\[[^]]+\]:\s*(<[^>]+>|\S+)")
_RAW = {".log", ".json", ".xml", ".prof", ".pstats", ".jsonl"}
_STATUSES = {"current", "superseded", "historical", "rejected"}


def _lines(text: str) -> list[tuple[int, str]]:
    """Ignore fenced code, where Markdown-looking links are literal examples."""
    result: list[tuple[int, str]] = []
    fence = ""
    for number, line in enumerate(text.splitlines(), 1):
        stripped = line.lstrip()
        if stripped.startswith(("```", "~~~")):
            marker = stripped[:3]
            if not fence:
                fence = marker
            elif marker == fence:
                fence = ""
            continue
        if not fence:
            result.append((number, line))
    return result


def _anchors(text: str) -> set[str]:
    found: set[str] = set()
    counts: Counter[str] = Counter()
    for _number, line in _lines(text):
        if re.match(r"^#{1,6}\s", line):
            title = re.sub(r"^#+\s+|\s+#+\s*$", "", line).lower()
            title = re.sub(r"[^\w\s-]", "", title).replace(" ", "-")
            count = counts[title]
            found.add(title if not count else f"{title}-{count}")
            counts[title] += 1
        found.update(re.findall(r'<a\s+(?:name|id)=["\x27]([^"\x27]+)', line))
    return found


def _tracked(root: Path) -> set[str]:
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z"],
        capture_output=True,
        check=False,
    )
    return (
        {p.decode() for p in result.stdout.split(b"\0") if p}
        if result.returncode == 0
        else set()
    )


def _local_path(root: Path, value: str) -> Path | None:
    path = (root / value).resolve()
    return path if path.is_relative_to(root) else None


def _sprint_errors(name: str, kind: str, week_start: object, text: str) -> list[str]:
    """Weekly indexes and topics share an explicit Sunday calendar boundary."""
    prefix = f"{name}:1:"
    if not isinstance(week_start, str):
        return [f"{prefix} sprint requires an ISO date string in week_start"]
    try:
        start = date.fromisoformat(week_start)
    except ValueError:
        return [f"{prefix} invalid sprint week_start: {week_start}"]
    if start.weekday() != 6 or start.isoformat() != week_start:
        return [f"{prefix} sprint week_start must be a Sunday (YYYY-MM-DD)"]
    expected = f"docs/sprints/week-of-{week_start}"
    errors = []
    if Path(name).parent.as_posix() != expected:
        errors.append(f"{prefix} sprint folder must match week_start: {expected}")
    if kind == "sprint":
        period = (
            f"Period: {start} through {start + timedelta(days=6)} (Sunday–Saturday)."
        )
        if Path(name).name != "README.md" or period not in text.splitlines():
            errors.append(
                f"{prefix} sprint index must declare its Sunday–Saturday period"
            )
    elif kind == "sprint-topic":
        period = (
            f"Period: {start} through {start + timedelta(days=6)} (Sunday–Saturday)."
        )
        if period not in text.splitlines():
            errors.append(
                f"{prefix} sprint topic must declare its Sunday–Saturday period"
            )
        for heading in HEADINGS:
            if f"## {heading}" not in text.splitlines():
                errors.append(f"{prefix} missing sprint topic section: {heading}")
    return errors


def _link_errors(root: Path, path: Path, *, durable: bool) -> list[str]:
    errors: list[str] = []
    relative = path.relative_to(root)
    for number, line in _lines(path.read_text()):
        targets = [match.group(1) for match in _LINK.finditer(line)]
        reference = _REFERENCE.match(line)
        if reference:
            targets.append(reference.group(1))
        for target in targets:
            parts = urlsplit(target.strip("<>"))
            if parts.scheme or parts.netloc:
                continue
            destination = (path.parent / unquote(parts.path)).resolve()
            if not parts.path:
                destination = path
            prefix = f"{relative}:{number}:"
            if not destination.is_relative_to(root):
                errors.append(f"{prefix} link escapes repository: {target}")
            elif not destination.exists():
                errors.append(f"{prefix} missing local link: {target}")
            elif durable and destination.suffix in _RAW:
                errors.append(
                    f"{prefix} durable page links a raw run artifact: {target}"
                )
            elif (
                parts.fragment
                and destination.suffix == ".md"
                and unquote(parts.fragment) not in _anchors(destination.read_text())
            ):
                errors.append(f"{prefix} missing local heading: {target}")
    return errors


def check_docs(root: Path) -> tuple[str, ...]:
    """Check the reviewed catalog and current links; preserve archive text verbatim."""
    root = root.resolve()
    catalog = root / "docs/catalog.toml"
    if not catalog.is_file():
        return ("docs/catalog.toml:1: missing document catalog",)
    try:
        data = tomllib.loads(catalog.read_text())
    except tomllib.TOMLDecodeError as error:
        return (f"docs/catalog.toml:1: {error}",)
    records = data.get("document", [])
    if not isinstance(records, list):
        return ("docs/catalog.toml:1: document must be an array of tables",)
    errors: list[str] = []
    ids: dict[str, tuple[str, tuple[str, ...]]] = {}
    paths: set[str] = set()
    current: dict[str, str] = {}
    for record in records:
        if not isinstance(record, dict) or any(
            not isinstance(record.get(key), str) or not record[key]
            for key in ("id", "path", "kind", "topic", "status")
        ):
            errors.append("docs/catalog.toml:1: incomplete document record")
            continue
        identifier, name = str(record["id"]), str(record["path"])
        kind, status, topic = map(
            str, (record["kind"], record["status"], record["topic"])
        )
        if identifier in ids or name in paths:
            errors.append(
                f"docs/catalog.toml:1: duplicate document identity/path: {identifier}"
            )
        paths.add(name)
        supersedes = record.get("supersedes", [])
        if isinstance(supersedes, str):
            supersedes = [supersedes]
        if not isinstance(supersedes, list) or any(
            not isinstance(item, str) for item in supersedes
        ):
            errors.append(f"docs/catalog.toml:1: invalid supersedes: {identifier}")
            supersedes = []
        ids[identifier] = (name, tuple(supersedes))
        if status not in _STATUSES:
            errors.append(f"docs/catalog.toml:1: invalid status: {identifier}")
        if kind == "research" and status == "current":
            if topic in current:
                errors.append(
                    f"docs/catalog.toml:1: multiple current research papers: {topic}"
                )
            current[topic] = identifier
        path = _local_path(root, name)
        if path is None or not path.is_file():
            errors.append(f"docs/catalog.toml:1: missing or foreign document: {name}")
            continue
        if (
            kind in {"checkpoint", "sprint", "sprint-topic"}
            and "provenance" not in path.read_text().lower()
        ):
            errors.append(f"{name}:1: missing provenance section")
        if kind in {"sprint", "sprint-topic"}:
            sprint_errors = _sprint_errors(
                name, kind, record.get("week_start"), path.read_text()
            )
            errors.extend(sprint_errors)
            if kind == "sprint" and not sprint_errors:
                start = date.fromisoformat(str(record["week_start"]))
                if refresh_index(path.parent, start, check=True):
                    errors.append(
                        f"{name}:1: generated sprint topic links/counts are stale"
                    )
        if not name.startswith("docs/archive/"):
            errors.extend(
                _link_errors(
                    root,
                    path,
                    durable=name.startswith("docs/")
                    and not name.startswith("docs/sprints/"),
                )
            )
    # Iterative traversal also detects cycles without imposing a recursion limit.
    complete: set[str] = set()
    for identifier in ids:
        pending = [(identifier, False)]
        active: set[str] = set()
        while pending:
            item, expanded = pending.pop()
            if expanded:
                active.discard(item)
                complete.add(item)
            elif item not in ids:
                errors.append(
                    f"docs/catalog.toml:1: unknown superseded document: {item}"
                )
            elif item in active:
                errors.append(f"docs/catalog.toml:1: supersession cycle: {item}")
            elif item not in complete:
                active.add(item)
                pending.append((item, True))
                pending.extend((child, False) for child in ids[item][1])
    required = {
        path.relative_to(root).as_posix()
        for path in (root / "docs").rglob("*.md")
        if "archive" not in path.relative_to(root / "docs").parts
    }
    tracked = _tracked(root)
    required.update(
        name
        for name in tracked
        if name.startswith("results/")
        and name.endswith(".md")
        and (root / name).exists()
    )
    errors.extend(
        f"{name}:1: maintained document is not catalogued"
        for name in sorted(required - paths)
    )
    allowed = data.get("retained_fixture", [])
    if not isinstance(allowed, list) or any(not isinstance(p, str) for p in allowed):
        errors.append("docs/catalog.toml:1: retained_fixture must be a list of paths")
        allowed = []
    errors.extend(
        f"{name}:1: tracked raw result payload must be an explicit retained fixture"
        for name in sorted(tracked)
        if name.startswith("results/")
        and Path(name).suffix in _RAW
        and (root / name).exists()
        and name not in allowed
    )
    readme = root / "README.md"
    if readme.is_file() and "README.md" not in paths:
        errors.extend(_link_errors(root, readme, durable=True))
    if (root / "src/number_compiler/api/cli_requests.py").is_file():
        from devtools.checks.cli_docs import check_cli_docs

        errors.extend(check_cli_docs(root))
    return tuple(sorted(set(errors)))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=repository_root())
    args = parser.parse_args()
    errors = check_docs(args.root)
    for error in errors:
        print(error)
    if not errors:
        print("Documentation index and local links passed")
    return int(bool(errors))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
