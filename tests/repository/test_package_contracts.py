"""Canonical import ownership replaces handwritten migration inventories."""

import ast
import importlib
import importlib.util
import tomllib
from pathlib import Path

import pytest

from devtools.checks.package_contracts import module_inventory, package_violations
from devtools.paths import repository_root

ROOT = repository_root()


def test_package_ownership_is_derived_and_unambiguous() -> None:
    assert package_violations(ROOT) == ()
    modules = module_inventory(ROOT)
    assert len(modules) == len(set(modules.values()))


def test_universal_cascade_output_experiment_is_not_an_installed_constructor() -> None:
    assert (
        importlib.util.find_spec("number_compiler.hashlife.execution.cascade_output")
        is None
    )


@pytest.mark.parametrize(
    "removed",
    (
        "hashlife.actions.power",
        "hashlife.actions.native_power",
        "hashlife.execution.cascade",
        "hashlife.execution.cascade_power",
        "hashlife.execution.diamond_reverse_expression",
        "hashlife.execution.diamond_reverse_kernel",
        "hashlife.execution.powered_local_codec",
        "hashlife.execution.temporal_leaf_diamond",
        "hashlife.execution.continuations.virtual_field_provider",
        "sequences.reverse_add.source_carry",
        "sequences.reverse_add.source_length",
        "sequences.reverse_add.factored_planes",
        "sequences.reverse_add.factored_carrier",
        "sequences.reverse_add.factored_power",
        "sequences.reverse_add.cocycle_carrier",
        "sequences.reverse_add.coordinate_program",
        "sequences.reverse_add.field_action",
        "sequences.reverse_add.higher_schema",
        "sequences.reverse_add.higher_interface",
        "sequences.reverse_add.cocycle_temporal",
        "sequences.reverse_add.threshold_cocycle",
        "sequences.reverse_add.domain",
        "sequences.reverse_add.local_interface",
        "sequences.reverse_add.frobenius_sectors",
        "sequences.reverse_add.tile_sector_observation",
        "resources.cocycle_temporal_payload_audit",
    ),
)
def test_retired_reverse_constructors_are_absent_from_production(removed: str) -> None:
    assert importlib.util.find_spec("number_compiler." + removed) is None


def test_public_api_is_deliberate_and_has_no_dynamic_compatibility_dispatch() -> None:
    import number_compiler

    assert len(number_compiler.__all__) == len(set(number_compiler.__all__))
    assert {
        "NumberCompiler",
        "CanonicalSequenceCompiler",
        "ReverseAddPoweredTerm",
        "PoweredCollatzTerm",
    } <= set(number_compiler.__all__)
    assert not {
        "ComposedBlockEffect",
        "TileArena",
        "HigherSemanticArena",
        "ReverseAddCarrySlab",
    } & set(number_compiler.__all__)
    # Deferred loading may resolve only the same deliberate public exports;
    # it must never synthesize legacy aliases or dispatch arbitrary names.
    tree = ast.parse((ROOT / "src/number_compiler/__init__.py").read_text())
    table = next(
        node.value
        for node in tree.body
        if isinstance(node, ast.Assign)
        and any(
            isinstance(target, ast.Name) and target.id == "_EXPORT_MODULES"
            for target in node.targets
        )
    )
    owners = ast.literal_eval(table)
    assert set(owners) == set(number_compiler.__all__)
    resolver = next(
        node
        for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name == "__getattr__"
    )
    assert len(resolver.body) == 1
    assert ast.unparse(resolver.body[0]) == (
        "return _resolve_export(name, _EXPORT_MODULES, globals())"
    )
    for name in number_compiler.__all__:
        assert owners[name].startswith("number_compiler.")
        assert owners[name] not in {"number_compiler", "number_compiler.api"}
        assert getattr(number_compiler, name) is getattr(
            importlib.import_module(owners[name]), name
        )
    for name in (
        "ComposedBlockEffect",
        "TileArena",
        "HigherSemanticArena",
        "ReverseAddCarrySlab",
        "reverse_power",
        "not_a_public_export",
    ):
        with pytest.raises(AttributeError):
            getattr(number_compiler, name)
    for facade in (number_compiler, importlib.import_module("number_compiler.api")):
        with pytest.raises(AttributeError):
            _ = facade.resolve_export


def test_cli_entry_point_has_one_canonical_owner() -> None:
    config = tomllib.loads((ROOT / "pyproject.toml").read_text())
    assert (
        config["project"]["scripts"]["number-compiler"]
        == "number_compiler.api.cli:main"
    )
    assert callable(importlib.import_module("number_compiler.api.cli").main)


def test_old_forwarding_paths_do_not_resolve() -> None:
    for name in (
        "number_compiler.reverse_power",
        "number_compiler.semantic_structures",
        "number_compiler.block_power",
        "number_compiler.core",
        "number_compiler.runtime",
        "number_compiler.sequences.collatz.concrete_port",
        "number_compiler.sequences.collatz.higher_interface",
        "number_compiler.hashlife.execution.finite_tile_action",
    ):
        assert importlib.util.find_spec(name) is None


def test_discovery_detects_missing_developer_initializer(tmp_path: Path) -> None:
    module = tmp_path / "devtools" / "experiments" / "sample.py"
    module.parent.mkdir(parents=True)
    module.write_text("VALUE = 1\n")
    (tmp_path / "src/number_compiler").mkdir(parents=True)
    assert any(
        "missing package initializer" in item for item in package_violations(tmp_path)
    )


def test_discovery_rejects_initializer_alias_and_forwarding_module(
    tmp_path: Path,
) -> None:
    package = tmp_path / "src/number_compiler"
    api = package / "api"
    api.mkdir(parents=True)
    (package / "__init__.py").write_text('"""Public package."""\n')
    (api / "__init__.py").write_text('"""Public declarations."""\n')
    (api / "alias.py").write_text(
        '"""Obsolete forwarding path."""\n'
        "from number_compiler.api.__init__ import Example\n"
    )
    failures = package_violations(tmp_path)
    assert any("forwarding module without implementation" in item for item in failures)
    assert any("alternate initializer identity" in item for item in failures)


def test_search_path_and_module_identity_rules_use_exact_ast_shapes(
    tmp_path: Path,
) -> None:
    package = tmp_path / "src" / "number_compiler"
    api = package / "api"
    api.mkdir(parents=True)
    (package / "__init__.py").write_text('"""Package."""\n')
    (api / "__init__.py").write_text('"""API."""\n')
    (api / "shape.py").write_text(
        "import sys\n"
        "def move(value):\n"
        "    sys.path.insert(0, value)\n"
        "    sys.modules[__name__] = value\n"
    )
    failures = package_violations(tmp_path)
    assert sum("modifies module search path" in item for item in failures) == 1
    assert sum("redirects its module identity" in item for item in failures) == 1
    (api / "shape.py").write_text(
        "class Other:\n"
        "    path = []\n"
        "    modules = {}\n"
        "other = Other()\n"
        "other.path.insert(0, 1)\n"
        "other.modules['name'] = 1\n"
    )
    failures = package_violations(tmp_path)
    assert not any("modifies module search path" in item for item in failures)
    assert not any("redirects its module identity" in item for item in failures)
