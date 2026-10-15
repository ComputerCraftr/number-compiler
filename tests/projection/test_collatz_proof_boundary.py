"""Whole-orbit Collatz helpers remain explicit proof compatibility APIs."""

from __future__ import annotations

import ast
from typing import Never

import pytest

from devtools.paths import repository_root
from number_compiler.api.number_api import NumberCompiler, PoweredCollatzTermPayload
from number_compiler.api.query_types import CollatzTermQuery
from tests.support.production_ast import ProductionASTGraph

PACKAGE = repository_root() / "src" / "number_compiler"


def test_sequential_collatz_orbit_builders_have_one_explicit_output_owner(
    production_ast_graph: ProductionASTGraph,
) -> None:
    owners = {
        "collatz_orbit_formulas": "projection/collatz_orbits/binary.py",
        "collatz_orbit_formulas_ternary": "projection/collatz_orbits/radix.py",
        "collatz_orbit_formulas_local_composite_radix": (
            "projection/collatz_orbits/radix.py"
        ),
        "collatz_sentinel_orbit": "projection/collatz_orbits/sentinel.py",
        "collatz_orbit_formulas_sentinel_power4": "projection/collatz_orbits/sentinel.py",
    }
    loop_owners: dict[str, list[str]] = {name: [] for name in owners}
    for path, tree in production_ast_graph.under(PACKAGE).items():
        for node in tree.body:
            if (
                isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and node.name in loop_owners
                and any(
                    isinstance(child, (ast.For, ast.While)) for child in ast.walk(node)
                )
            ):
                loop_owners[node.name].append(path.relative_to(PACKAGE).as_posix())
    assert loop_owners == {name: [owner] for name, owner in owners.items()}


def test_powered_collatz_queries_cannot_select_orbit_helpers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.projection.collatz_orbits.binary as binary_proof
    import number_compiler.projection.collatz_orbits.radix as radix_proof
    import number_compiler.projection.collatz_orbits.sentinel as raw_proof
    import number_compiler.sequences.collatz.raw_field as raw
    from number_compiler.sequences.collatz import radix

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("sequential Collatz proof orbit entered powered query")

    names = (
        (binary_proof, "collatz_orbit_formulas"),
        (binary_proof, "collatz_values"),
        (radix, "collatz_orbit_formulas_ternary"),
        (radix, "collatz_orbit_formulas_local_composite_radix"),
        (radix_proof, "collatz_orbit_formulas_ternary"),
        (radix_proof, "collatz_orbit_formulas_local_composite_radix"),
        (raw, "collatz_sentinel_orbit"),
        (raw, "collatz_orbit_formulas_sentinel_power4"),
        (raw_proof, "collatz_sentinel_orbit"),
        (raw_proof, "collatz_orbit_formulas_sentinel_power4"),
    )
    for module, name in names:
        monkeypatch.setattr(module, name, forbidden)

    compiler = NumberCompiler()
    binary_term = compiler.project(CollatzTermQuery(12, seed=27, radix=2))
    assert isinstance(binary_term.payload, PoweredCollatzTermPayload)
    binary_width = binary_term.payload.term.width()
    assert isinstance(binary_width, int) and binary_width > 0
    binary_bits = binary_term.estimated_bit_length
    assert isinstance(binary_bits, int) and binary_bits > 0
    assert binary_term.digit(0) in (0, 1)
    ternary_term = compiler.project(CollatzTermQuery(12, seed=27, radix=3))
    assert isinstance(ternary_term.payload, PoweredCollatzTermPayload)
    ternary_width = ternary_term.payload.term.width()
    assert isinstance(ternary_width, int) and ternary_width > 0
    ternary_bits = ternary_term.estimated_bit_length
    assert isinstance(ternary_bits, int) and ternary_bits > 0
    assert ternary_term.digit(0) in (0, 1, 2)


def test_collatz_compatibility_facades_are_removed() -> None:
    for relative in (
        "collatz_radix.py",
        "collatz_raw_field.py",
        "projection/explicit_collatz_orbits.py",
    ):
        assert not (PACKAGE / relative).exists()
