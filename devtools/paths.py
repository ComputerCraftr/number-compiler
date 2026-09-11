"""Locate the developer checkout without modifying Python's module search path."""

from pathlib import Path


def repository_root() -> Path:
    for candidate in Path(__file__).resolve().parents:
        if (candidate / "pyproject.toml").is_file():
            return candidate
    raise RuntimeError("developer tools require a number-compiler checkout")


def report_output(module: str, filename: str) -> Path:
    """Allocate a current report destination separate from immutable checkpoints."""
    parts = module.split(".")
    if (
        not parts
        or parts[0] != "devtools"
        or any(not part.isidentifier() for part in parts)
    ):
        raise ValueError("report module must have a canonical developer identity")
    if Path(filename).name != filename:
        raise ValueError("report filename must not contain a directory")
    destination = repository_root() / "results" / "current" / Path(*parts[1:])
    destination.mkdir(parents=True, exist_ok=True)
    return destination / filename
