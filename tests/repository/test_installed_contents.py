"""Distribution inventory comes from source, including non-Python resources."""

import sys
from io import StringIO
from pathlib import Path
from zipfile import ZipFile

import pytest

from devtools.checks import installed_distribution
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


def test_wheel_verification_keeps_flushed_last_stage_on_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    wheel = tmp_path / "package.whl"
    wheel.touch()

    class FlushTrackingStderr(StringIO):
        flush_count = 0

        def flush(self) -> None:
            self.flush_count += 1
            super().flush()

    stderr = FlushTrackingStderr()

    def reject_contents(_wheel: Path, _source: Path) -> list[str]:
        raise ValueError("controlled content-validation failure")

    monkeypatch.setattr(sys, "stderr", stderr)
    monkeypatch.setattr(
        installed_distribution, "validate_wheel_contents", reject_contents
    )

    with pytest.raises(ValueError, match="controlled content-validation failure"):
        installed_distribution.verify_wheel(wheel)

    assert stderr.getvalue() == "package-stage: wheel-content-validation:start\n"
    assert stderr.flush_count == 1
