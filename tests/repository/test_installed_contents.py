"""Distribution inventory comes from source, including non-Python resources."""

import shutil
import subprocess
import sys
from hashlib import sha256
from io import StringIO
from pathlib import Path
from zipfile import ZipFile

import pytest

from devtools.checks import installed_distribution
from devtools.checks.installed_distribution import validate_wheel_contents
from devtools.paths import repository_root
from number_compiler.sequences.comma import future_provider
from number_compiler.sequences.comma.future_artifact import (
    FUTURE_NATIVE_EXPORT,
    FUTURE_PROVIDER_ASSET,
    RETIRED_FUTURE_PROVIDER_ASSET,
)


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


@pytest.mark.parametrize("fault", ("missing", "duplicate", "stale", "identical"))
def test_comma_release_binds_packaged_bytes_to_the_native_export(
    tmp_path: Path, fault: str
) -> None:
    export = tmp_path / "export"
    export.mkdir()
    asset = tmp_path / installed_distribution.COMMA_RELEASE_ASSET
    payload = b'{"artifact":"native fixture"}\n'
    asset.write_bytes(b"stale wheel data" if fault == "stale" else payload)
    if fault != "missing":
        (export / installed_distribution.COMMA_NATIVE_EXPORT).write_bytes(payload)
    if fault == "duplicate":
        other = export / "second-theory"
        other.mkdir()
        (other / installed_distribution.COMMA_NATIVE_EXPORT).write_bytes(payload)
    if fault == "identical":
        assert (
            installed_distribution.verify_comma_native_export(export, asset)
            == sha256(payload).hexdigest()
        )
    else:
        with pytest.raises(ValueError, match="native (build|export)"):
            installed_distribution.verify_comma_native_export(export, asset)


def test_comma_release_filename_is_shared_by_runtime_and_native_checks() -> None:
    assert future_provider.FUTURE_PROVIDER_ASSET == FUTURE_PROVIDER_ASSET
    assert installed_distribution.COMMA_RELEASE_ASSET == FUTURE_PROVIDER_ASSET
    assert installed_distribution.COMMA_NATIVE_EXPORT == FUTURE_NATIVE_EXPORT
    assert FUTURE_PROVIDER_ASSET != RETIRED_FUTURE_PROVIDER_ASSET


def test_wheel_packages_the_reviewed_comma_name_from_project_metadata(
    tmp_path: Path,
) -> None:
    """Exercise setuptools with both candidate names and inspect its wheel."""
    source = repository_root()
    stage = tmp_path / "source"
    stage.mkdir()
    for name in ("pyproject.toml", "README.md", "LICENSE"):
        shutil.copy2(source / name, stage / name)
    package = stage / "src" / "number_compiler"
    kernels = package / "kernels"
    kernels.mkdir(parents=True)
    (package / "__init__.py").write_text("", encoding="utf-8")
    (package / "py.typed").write_text("", encoding="utf-8")
    expected = b'{"untrusted":true}\n'
    (kernels / FUTURE_PROVIDER_ASSET).write_bytes(expected)
    (kernels / RETIRED_FUTURE_PROVIDER_ASSET).write_bytes(b"retired")
    wheels = tmp_path / "wheels"
    subprocess.run(
        (
            sys.executable,
            "-m",
            "pip",
            "wheel",
            "--no-index",
            "--no-deps",
            "--no-build-isolation",
            "--wheel-dir",
            str(wheels),
            str(stage),
        ),
        check=True,
        capture_output=True,
        text=True,
        timeout=45,
    )
    (built,) = wheels.glob("*.whl")
    with ZipFile(built) as archive:
        assert (
            archive.read(f"number_compiler/kernels/{FUTURE_PROVIDER_ASSET}") == expected
        )
        assert (
            f"number_compiler/kernels/{RETIRED_FUTURE_PROVIDER_ASSET}"
            not in archive.namelist()
        )
