"""Small, current source-layout contracts that survive implementation moves."""

from __future__ import annotations

import ast
import tomllib

from devtools.paths import repository_root

ROOT = repository_root()


def _import_roots(path: str) -> frozenset[str]:
    tree = ast.parse((ROOT / path).read_text(encoding="utf-8"), filename=path)
    roots: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module:
            roots.add(node.module.split(".", 1)[0])
        elif isinstance(node, ast.Import):
            roots.update(alias.name.split(".", 1)[0] for alias in node.names)
    return frozenset(roots)


def test_distribution_exposes_one_python_package_and_one_cli_entry_point() -> None:
    source = ROOT / "src"
    packages = sorted(
        path.name
        for path in source.iterdir()
        if path.is_dir() and (path / "__init__.py").is_file()
    )
    assert packages == ["number_compiler"]
    assert not (source / "reverse_add").exists()

    metadata = tomllib.loads((ROOT / "pyproject.toml").read_text())
    assert metadata["project"]["scripts"] == {
        "number-compiler": "number_compiler.api.cli:main"
    }


def test_parser_renderer_and_term_compiler_have_separate_import_roles() -> None:
    parser = _import_roots("src/number_compiler/api/cli_requests.py")
    compiler = _import_roots("src/number_compiler/api/sequence_compiler.py")
    number_api = _import_roots("src/number_compiler/api/number_api.py")
    renderer = _import_roots("src/number_compiler/api/cli_render.py")

    assert "argparse" in parser
    assert "argparse" not in (compiler | number_api | renderer)


def test_196_trace_tower_uses_the_shared_quadratic_power() -> None:
    from number_compiler.arithmetic.fields.morphism_core import QuadraticPower
    from number_compiler.arithmetic.formula.symmetry_frame import (
        FixedRealCyclotomicGerm,
    )
    from number_compiler.arithmetic.polynomials.polynomial import (
        trace_square_polynomial,
    )

    seed: tuple[int, ...] = (-2, 1)
    assert FixedRealCyclotomicGerm.p8_coefficients() == QuadraticPower(
        1
    ).apply_iterated(
        seed,
        step=trace_square_polynomial,
    )
    assert FixedRealCyclotomicGerm.p16_coefficients() == QuadraticPower(
        2
    ).apply_iterated(
        seed,
        step=trace_square_polynomial,
    )
