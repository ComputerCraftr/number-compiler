"""Source text snapshots for architectural absence assertions."""

from pathlib import Path
from types import ModuleType


def module_sources(*modules: ModuleType) -> tuple[str, ...]:
    paths = []
    for module in modules:
        assert module.__file__ is not None
        paths.append(Path(module.__file__))
    return tuple(path.read_text() for path in paths)
