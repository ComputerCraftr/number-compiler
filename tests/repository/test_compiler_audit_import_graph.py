"""Architecture audits must traverse canonical packages beyond root facades."""

from pathlib import Path

import pytest

import devtools.checks.dependency_graph as audit


def _write(root: Path, name: str, source: str) -> None:
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source)


def test_audit_follows_relative_absolute_and_package_alias_imports(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(audit, "SRC", tmp_path)
    _write(tmp_path, "entry.py", "from .api import compiler as implementation\n")
    _write(tmp_path, "api/__init__.py", "")
    _write(tmp_path, "api/compiler.py", "from ..runtime.scheduler import execute\n")
    _write(tmp_path, "runtime/__init__.py", "")
    _write(
        tmp_path,
        "runtime/scheduler.py",
        "import number_compiler.arithmetic.tokens as tokens\n",
    )
    _write(tmp_path, "arithmetic/tokens.py", "VALUE = 1\n")
    assert audit._reachable("entry") == {
        "entry",
        "api",
        "api.compiler",
        "runtime.scheduler",
        "arithmetic.tokens",
    }
    assert audit._module_path("api") == tmp_path / "api/__init__.py"


def test_type_checking_edges_do_not_hide_runtime_else_imports(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(audit, "SRC", tmp_path)
    _write(
        tmp_path,
        "entry.py",
        """from typing import TYPE_CHECKING
if TYPE_CHECKING:
    from .proof.oracle import Exact
else:
    from .runtime import engine
""",
    )
    _write(tmp_path, "proof/oracle.py", "")
    _write(tmp_path, "runtime/__init__.py", "")
    _write(tmp_path, "runtime/engine.py", "")
    assert audit._reachable("entry") == {"entry", "runtime", "runtime.engine"}


def test_temporal_probe_source_audits_use_executable_syntax(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from devtools.benchmarks import (
        collatz_temporal_power_probe,
        reverse_temporal_power_probe,
    )

    monkeypatch.setattr(collatz_temporal_power_probe, "ROOT", tmp_path)
    monkeypatch.setattr(reverse_temporal_power_probe, "ROOT", tmp_path)
    _write(
        tmp_path,
        "src/number_compiler/api/number_api.py",
        '"""collatz_orbit_formulas( and collatz_orbit_formulas_ternary"""\n',
    )
    _write(
        tmp_path,
        "src/number_compiler/sequences/collatz/block_power.py",
        '"""CollatzCausalSpacetimeEngine"""\n',
    )
    _write(
        tmp_path,
        "src/number_compiler/__init__.py",
        "# from .collatz_spacetime import Engine\n",
    )
    _write(
        tmp_path,
        "devtools/verification/block_runtime.py",
        "from .block_recursive import _RecursiveBoundaryState\n"
        '"""from ..program_word import CanonicalWord"""\n',
    )
    _write(
        tmp_path,
        "devtools/verification/block_spacetime_runtime.py",
        "# def _output_tile_macro and import SpacetimeBoundary\n",
    )
    _write(
        tmp_path,
        "devtools/verification/spacetime_boundary.py",
        "# class SpacetimeBoundary: pass\n",
    )
    _write(
        tmp_path,
        "src/number_compiler/hashlife/execution/bounded_application.py",
        "from .field_application import build_certified_field_application\n",
    )
    _write(
        tmp_path,
        "src/number_compiler/sequences/runtime_router.py",
        "# import number_compiler.hashlife.execution.diamond_runtime\n",
    )
    _write(
        tmp_path,
        "src/number_compiler/hashlife/observation/hashlife_projection.py",
        '"""def _partition3; def output_word; def point("""\n',
    )
    _write(
        tmp_path,
        "src/number_compiler/sequences/reverse_add/power.py",
        "# ReverseAddCausalSpacetimeEngine\n",
    )
    assert all(collatz_temporal_power_probe._source_audit().values())
    assert all(reverse_temporal_power_probe._source_audit().values())

    block = "src/number_compiler/sequences/collatz/block_power.py"
    _write(
        tmp_path, block, "from retired import CollatzCausalSpacetimeEngine as Fast\n"
    )
    with pytest.raises(AssertionError, match="powered_term_has_no_causal_engine"):
        collatz_temporal_power_probe._source_audit()
    _write(tmp_path, block, "")

    router = "src/number_compiler/sequences/runtime_router.py"
    for statement in (
        "from number_compiler.hashlife.execution import diamond_runtime as Fast\n",
        (
            "from importlib import import_module as load\n"
            'runtime = load("number_compiler.hashlife.execution.diamond_runtime")\n'
        ),
        "from importlib import import_module as load\nruntime = load(module_name)\n",
    ):
        _write(tmp_path, router, statement)
        with pytest.raises(
            AssertionError, match="certified_family_has_no_generic_executor_import"
        ):
            collatz_temporal_power_probe._source_audit()
        with pytest.raises(
            AssertionError, match="certified_family_has_no_generic_executor_import"
        ):
            reverse_temporal_power_probe._source_audit()
    _write(
        tmp_path,
        router,
        "import number_compiler.hashlife.execution.diamond_runtime\n",
    )
    with pytest.raises(
        AssertionError, match="certified_family_has_no_generic_executor_import"
    ):
        collatz_temporal_power_probe._source_audit()
    with pytest.raises(
        AssertionError, match="certified_family_has_no_generic_executor_import"
    ):
        reverse_temporal_power_probe._source_audit()

    _write(tmp_path, router, "")
    _write(
        tmp_path,
        "src/number_compiler/__init__.py",
        '__all__ = []\n__all__.append("unknown")\n',
    )
    with pytest.raises(ValueError, match="dynamic package export table"):
        collatz_temporal_power_probe._source_audit()
    _write(tmp_path, "src/number_compiler/__init__.py", "")

    _write(tmp_path, router, "")
    _write(
        tmp_path,
        "devtools/verification/block_runtime.py",
        "from .block_recursive import _RecursiveBoundaryState\n"
        "from ..program_word import CanonicalWord\n",
    )
    with pytest.raises(AssertionError, match="history_word_carrier_deleted"):
        collatz_temporal_power_probe._source_audit()
    with pytest.raises(AssertionError, match="history_word_carrier_deleted"):
        reverse_temporal_power_probe._source_audit()

    _write(
        tmp_path,
        "devtools/verification/block_runtime.py",
        "from .block_recursive import _RecursiveBoundaryState\n",
    )
    _write(
        tmp_path,
        "src/number_compiler/__init__.py",
        '__all__ = ["CollatzCausalSpacetimeEngine"]\n'
        '_EXPORT_MODULES = {"CollatzCausalSpacetimeEngine": '
        '"number_compiler.sequences.collatz.collatz_spacetime"}\n',
    )
    with pytest.raises(AssertionError, match="slow_causal_engine_not_public"):
        collatz_temporal_power_probe._source_audit()

    _write(tmp_path, "src/number_compiler/__init__.py", "")
    _write(
        tmp_path,
        router,
        "from importlib import import_module\n"
        'runtime = import_module("number_compiler.hashlife.execution.diamond_runtime")\n',
    )
    with pytest.raises(
        AssertionError, match="certified_family_has_no_generic_executor_import"
    ):
        collatz_temporal_power_probe._source_audit()
    with pytest.raises(
        AssertionError, match="certified_family_has_no_generic_executor_import"
    ):
        reverse_temporal_power_probe._source_audit()
