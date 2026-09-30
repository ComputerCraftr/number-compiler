"""Distribution inventory comes from source, including non-Python resources."""

from pathlib import Path
from zipfile import ZipFile

import pytest

from devtools.checks.installed_distribution import validate_wheel_contents


@pytest.mark.parametrize("fault", ["extra", "missing", "stale", "proofs", "none"])
def test_wheel_rejects_obsolete_build_products(tmp_path: Path, fault: str) -> None:
    source = tmp_path / "src"
    package = source / "number_compiler"
    package.mkdir(parents=True)
    (package / "__init__.py").write_text("VALUE = 1\n")
    (package / "py.typed").write_text("")
    wheel = tmp_path / "package.whl"
    with ZipFile(wheel, "w") as archive:
        archive.writestr(
            "number_compiler/__init__.py",
            "VALUE = 2\n" if fault == "stale" else "VALUE = 1\n",
        )
        if fault != "missing":
            archive.writestr("number_compiler/py.typed", "")
        if fault == "proofs":
            archive.writestr(
                "proofs/isabelle/Test.thy", "theory Test imports Main begin end"
            )
        if fault == "extra":
            archive.writestr("number_compiler/obsolete.py", "")
    if fault == "none":
        assert len(validate_wheel_contents(wheel, source)) == 2
    else:
        with pytest.raises(ValueError):
            validate_wheel_contents(wheel, source)
