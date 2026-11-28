"""The installed CLI fixture refuses modules outside the wheel manifest."""

from importlib.metadata import Distribution
from pathlib import Path
from types import ModuleType
from typing import cast

import pytest

from tests.validation.reversal.installed_native_cli_fixture import (
    _manifest,
    _owned_module,
)

pytestmark = pytest.mark.validation


def test_distribution_owner_rejects_unlisted_module_in_same_directory(
    tmp_path: Path,
) -> None:
    class Installed:
        files = (Path("number_compiler/__init__.py"),)

        def locate_file(self, path: Path) -> Path:
            return tmp_path / path

    dist = cast(Distribution, Installed())
    owned = _manifest(dist)
    module = ModuleType("number_compiler")
    module.__file__ = str(tmp_path / "number_compiler/__init__.py")
    _owned_module(owned, module)
    module.__file__ = str(tmp_path / "number_compiler/kernels/decoy.so")
    with pytest.raises(AssertionError, match="not owned"):
        _owned_module(owned, module)
