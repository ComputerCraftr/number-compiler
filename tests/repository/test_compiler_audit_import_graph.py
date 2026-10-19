"""Architecture audits must traverse canonical packages beyond root facades."""

from pathlib import Path

import pytest


def _write(root: Path, name: str, source: str) -> None:
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source)


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
    bounded_path = "src/number_compiler/hashlife/execution/bounded_application.py"
    bounded_source = (
        "from ..observation.tile_projection import build_tile_projection\n"
        "def validate_certified_application_inputs(): pass\n"
        "def build_bounded_application(): return build_tile_projection()\n"
    )
    _write(tmp_path, bounded_path, bounded_source)
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
    assert all(collatz_temporal_power_probe.source_audit().values())
    assert all(reverse_temporal_power_probe.source_audit().values())

    _write(
        tmp_path,
        bounded_path,
        "from .field_application import build_certified_field_application\n",
    )
    with pytest.raises(
        AssertionError, match="bounded_temporal_application_boundary_present"
    ):
        collatz_temporal_power_probe.source_audit()
    _write(tmp_path, bounded_path, bounded_source)

    block = "src/number_compiler/sequences/collatz/block_power.py"
    _write(
        tmp_path, block, "from retired import CollatzCausalSpacetimeEngine as Fast\n"
    )
    with pytest.raises(AssertionError, match="powered_term_has_no_causal_engine"):
        collatz_temporal_power_probe.source_audit()
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
            collatz_temporal_power_probe.source_audit()
        with pytest.raises(
            AssertionError, match="certified_family_has_no_generic_executor_import"
        ):
            reverse_temporal_power_probe.source_audit()
    _write(
        tmp_path,
        router,
        "import number_compiler.hashlife.execution.diamond_runtime\n",
    )
    with pytest.raises(
        AssertionError, match="certified_family_has_no_generic_executor_import"
    ):
        collatz_temporal_power_probe.source_audit()
    with pytest.raises(
        AssertionError, match="certified_family_has_no_generic_executor_import"
    ):
        reverse_temporal_power_probe.source_audit()

    _write(tmp_path, router, "")
    _write(
        tmp_path,
        "src/number_compiler/__init__.py",
        '__all__ = []\n__all__.append("unknown")\n',
    )
    with pytest.raises(ValueError, match="dynamic package export table"):
        collatz_temporal_power_probe.source_audit()
    _write(tmp_path, "src/number_compiler/__init__.py", "")

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
        collatz_temporal_power_probe.source_audit()

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
        collatz_temporal_power_probe.source_audit()
    with pytest.raises(
        AssertionError, match="certified_family_has_no_generic_executor_import"
    ):
        reverse_temporal_power_probe.source_audit()
