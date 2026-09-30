"""Locate the developer checkout without modifying Python's module search path."""

from pathlib import Path
import tomllib


def repository_root() -> Path:
    for candidate in Path(__file__).resolve().parents:
        if (candidate / "pyproject.toml").is_file():
            return candidate
    raise RuntimeError("developer tools require a number-compiler checkout")


def isabelle_root(root: Path | None = None) -> Path:
    """The single authored formal-proof tree (never a generated report)."""
    return (root or repository_root()) / "proofs" / "isabelle"


def project_version() -> str:
    """Read checkout metadata instead of duplicating a current release version."""
    data = tomllib.loads((repository_root() / "pyproject.toml").read_text())
    value = data["project"]["version"]
    if not isinstance(value, str):
        raise ValueError("project version must be a string")
    return value


def report_directory(module: str) -> Path:
    """Return a module's namespace within the current fresh run."""
    parts = module.split(".")
    if (
        not parts
        or parts[0] != "devtools"
        or any(not part.isidentifier() for part in parts)
    ):
        raise ValueError("report module must have a canonical developer identity")
    from devtools.runs import report_run

    destination = report_run(repository_root()).path / Path(*parts[1:])
    destination.mkdir(parents=True, exist_ok=True)
    return destination


def report_output(module: str, filename: str) -> Path:
    """Allocate output inside this invocation’s fresh, manifested run."""
    if Path(filename).name != filename or filename in ("", ".", ".."):
        raise ValueError("report filename must not contain a directory")
    result = report_directory(module) / filename
    if result.exists() or result.is_symlink():
        raise FileExistsError("report output already exists; start a fresh run")
    return result
