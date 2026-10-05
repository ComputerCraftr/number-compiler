"""Create reviewed sprint topic scaffolds and refresh generated weekly navigation."""

from __future__ import annotations

import argparse
import re
import tomllib
from datetime import date, timedelta
from pathlib import Path

from devtools.paths import repository_root

HEADINGS = (
    "Objective",
    "Changes",
    "Established results",
    "Rejected approaches",
    "Validation provenance",
    "Remaining work",
)
START = "<!-- sprint-topics:start -->"
END = "<!-- sprint-topics:end -->"


def sunday(value: str) -> date:
    start = date.fromisoformat(value)
    if start.weekday() != 6 or start.isoformat() != value:
        raise ValueError("week-start must be a Sunday (YYYY-MM-DD)")
    return start


def topic_table(folder: Path) -> str:
    rows = ["| Topic | Records |", "| --- | ---: |"]
    for path in sorted(folder.glob("*.md")):
        if path.name == "README.md":
            continue
        text = path.read_text()
        title = text.splitlines()[0].removeprefix("# ")
        # Original records remain H2 sections, outside the standard scaffold.
        excluded = {*HEADINGS, "Records", "Provenance"}
        count = sum(
            line.startswith("## ") and line[3:] not in excluded
            for line in text.splitlines()
        )
        rows.append(f"| [{title}]({path.name}) | {count} |")
    if len(rows) == 2:
        return "No topic records have been authored for this week."
    return "\n".join(rows)


def refresh_index(folder: Path, start: date, *, check: bool = False) -> bool:
    path = folder / "README.md"
    block = f"{START}\n{topic_table(folder)}\n{END}"
    if path.exists():
        text = path.read_text()
        if START in text and END in text:
            updated = re.sub(
                re.escape(START) + r".*?" + re.escape(END),
                lambda _match: block,
                text,
                flags=re.DOTALL,
            )
        else:
            updated = re.sub(
                r"(## Topics\n).*?(?=\n## |\Z)",
                lambda match: match.group(1) + "\n" + block + "\n",
                text,
                count=1,
                flags=re.DOTALL,
            )
            if updated == text:
                updated = text.rstrip() + "\n\n## Topics\n\n" + block + "\n"
    else:
        updated = (
            f"# Week of {start}\n\nPeriod: {start} through "
            f"{start + timedelta(days=6)} (Sunday–Saturday).\n\n"
            "[Documentation index](../../index.md#sprint-history-and-provenance)\n\n"
            f"## Topics\n\n{block}\n\n## Provenance\n\n"
            "Topic records preserve original dates, source provenance, commands "
            "and outcomes. Raw evidence remains local or in CI.\n"
        )
    changed = not path.exists() or path.read_text() != updated
    if changed and not check:
        path.write_text(updated)
    return changed


def register(root: Path, path: Path, kind: str, topic: str, week: str) -> None:
    catalog = root / "docs/catalog.toml"
    text = catalog.read_text()
    records = tomllib.loads(text).get("document", [])
    relative = path.relative_to(root).as_posix()
    if any(record.get("path") == relative for record in records):
        return
    identifier = f"sprint-{week}-{topic}"
    if any(record.get("id") == identifier for record in records):
        raise ValueError("catalog identity already belongs to another path")
    catalog.write_text(
        text.rstrip()
        + (
            f'\n\n[[document]]\nid = "{identifier}"\npath = "{relative}"\n'
            f'kind = "{kind}"\ntopic = "{topic}"\nstatus = "current"\n'
            f'week_start = "{week}"\n'
        )
    )


def scaffold(root: Path, week: str, topic: str, title: str) -> Path:
    start = sunday(week)
    if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", topic) or topic == "readme":
        raise ValueError("topic must be a lowercase hyphenated name other than readme")
    if not title or "\n" in title or "\r" in title:
        raise ValueError("title must be one nonempty line")
    root = root.resolve()
    folder = root / "docs/sprints" / f"week-of-{week}"
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / f"{topic}.md"
    if not path.exists():
        sections = "\n\n".join(
            f"## {heading}\n\nPending authored record." for heading in HEADINGS
        )
        path.write_text(
            f"# {title}\n\nPeriod: {week} through {start + timedelta(days=6)} "
            f"(Sunday–Saturday).\n\n[Week index](README.md)\n\n{sections}\n"
        )
    refresh_index(folder, start)
    register(root, folder / "README.md", "sprint", "readme", week)
    register(root, path, "sprint-topic", topic, week)
    return path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=repository_root())
    parser.add_argument("--week-start", required=True)
    parser.add_argument("--topic")
    parser.add_argument("--title")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        start = sunday(args.week_start)
        if args.check:
            folder = args.root / "docs/sprints" / f"week-of-{start}"
            if not folder.is_dir() or refresh_index(folder, start, check=True):
                print("Sprint navigation requires regeneration")
                return 1
        else:
            if args.topic is None or args.title is None:
                parser.error("--topic and --title are required to scaffold a topic")
            print(scaffold(args.root, args.week_start, args.topic, args.title))
    except ValueError as error:
        parser.error(str(error))
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
