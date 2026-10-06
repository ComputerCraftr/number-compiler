"""Ownership boundaries between shared and family-owned source."""

from __future__ import annotations

import ast
from pathlib import Path

import pytest

from devtools.checks.isabelle_syntax import Session
from devtools.checks.ownership_policy import (
    check_isabelle_resource_owner,
    isabelle_ownership_violations,
    ownership_policy_violations,
    python_ownership_violations,
)


def test_ml_resources_preserve_theory_ownership_direction(tmp_path: Path) -> None:
    shared = tmp_path / "shared/carry/core/Owner.thy"
    family = tmp_path / "families/comma/carry/evaluator.ML"
    with pytest.raises(ValueError, match="invalid ML resource ownership"):
        check_isabelle_resource_owner(tmp_path, shared, family)
    check_isabelle_resource_owner(tmp_path, family, shared.with_suffix(".ML"))
    integration = tmp_path / "integration/support/core/Bridge.thy"
    check_isabelle_resource_owner(tmp_path, integration, family)
    with pytest.raises(ValueError, match="release ML resource depends on audit"):
        check_isabelle_resource_owner(
            tmp_path,
            family,
            tmp_path / "families/comma/audit/check/evaluator.ML",
        )


def test_shared_ml_rejects_known_comma_structure_references(tmp_path: Path) -> None:
    shared = (
        tmp_path / "proofs/isabelle/shared/arithmetic/carry_dynamics/foreign_helper.ML"
    )
    shared.parent.mkdir(parents=True)
    shared.write_text(
        "(* Comma_Entry_Arithmetic.natural_context ctxt *)\n"
        'val diagnostic = "Comma_Proof_Profile.report"\n'
        "val context = Comma_Entry_Arithmetic.natural_context ctxt\n",
        encoding="utf-8",
    )

    violations = isabelle_ownership_violations(tmp_path, sessions=())

    assert violations == (
        (
            "proofs/isabelle/shared/arithmetic/carry_dynamics/foreign_helper.ML:3: "
            "shared ML references family-owned structure Comma_Entry_Arithmetic"
        ),
    )


@pytest.mark.parametrize(
    "reference", ["Reference", "Reference.Reference", "Reference.thy"]
)
def test_release_session_and_theory_cannot_import_audit_owner(
    tmp_path: Path, reference: str
) -> None:
    root = tmp_path / "proofs/isabelle"
    release = root / "families/comma/production/Production.thy"
    audit = root / "families/comma/audit/reference/Reference.thy"
    root.mkdir(parents=True)
    sessions = (
        Session(
            "Production",
            release.parent.relative_to(root),
            "Reference",
            (),
            ("Production",),
        ),
        Session("Reference", audit.parent.relative_to(root), "HOL", (), ("Reference",)),
    )
    violations = isabelle_ownership_violations(
        tmp_path,
        sessions=sessions,
        theory_headers={
            release: ("Production", (reference,)),
            audit: ("Reference", ("Main",)),
        },
    )
    assert violations == (
        "release session Production depends on audit session Reference",
        "release theory Production imports audit theory Reference",
    )


def test_python_policy_includes_type_only_and_local_relative_imports(
    tmp_path: Path,
) -> None:
    root = tmp_path
    source = root / "src/number_compiler/arithmetic/fields/reader.py"
    source.parent.mkdir(parents=True)
    text = (
        "from typing import TYPE_CHECKING\n"
        "if TYPE_CHECKING:\n"
        "    import number_compiler.sequences.collatz.actions\n"
        "\n"
        "def read() -> None:\n"
        "    from ...sequences.antihydra.mahler import Action\n"
        ""
    )
    source.write_text(text, encoding="utf-8")
    parsed = {source: ast.parse(text, filename=str(source))}

    violations = python_ownership_violations(root, parsed_sources=parsed)

    assert len(violations) == 2
    assert any(
        ":3: shared code imports sequence-family module "
        "number_compiler.sequences.collatz.actions" in item
        for item in violations
    )
    assert any(
        ":6: shared code imports sequence-family module "
        "number_compiler.sequences.antihydra.mahler" in item
        for item in violations
    )
    assert ownership_policy_violations(root, parsed_sources=parsed) == violations


def test_python_policy_allows_shared_and_external_imports(tmp_path: Path) -> None:
    root = tmp_path
    source = root / "src/number_compiler/resources/ledger.py"
    source.parent.mkdir(parents=True)
    source.write_text(
        "import math\nfrom . import stores\nfrom typing import TYPE_CHECKING\n",
        encoding="utf-8",
    )
    assert python_ownership_violations(root) == ()


def test_python_policy_checks_aliases_dynamic_routes_and_lazy_exports(
    tmp_path: Path,
) -> None:
    root = tmp_path
    source_root = root / "src/number_compiler/arithmetic"
    source_root.mkdir(parents=True)
    source = source_root / "router.py"
    text = (
        "import number_compiler.sequences.collatz.actions as collatz_actions\n"
        "from importlib import import_module as load_module\n"
        "load_module('..sequences.antihydra.mahler')\n"
        "_EXPORT_MODULES = {'family': 'number_compiler.sequences.reverse_add'}\n"
    )
    source.write_text(text, encoding="utf-8")

    violations = python_ownership_violations(root)

    assert len(violations) == 3
    assert any(
        "number_compiler.sequences.collatz.actions" in item for item in violations
    )
    assert any(
        "number_compiler.sequences.antihydra.mahler" in item for item in violations
    )
    assert any("number_compiler.sequences.reverse_add" in item for item in violations)


def test_python_policy_rejects_unresolvable_dynamic_router(tmp_path: Path) -> None:
    source = tmp_path / "src/number_compiler/resources/router.py"
    source.parent.mkdir(parents=True)
    source.write_text(
        "from importlib import import_module as load_module\n"
        "load_module(resolve_target())\n",
        encoding="utf-8",
    )

    violations = python_ownership_violations(tmp_path)

    assert len(violations) == 1
    assert "unresolvable dynamic import router" in violations[0]


@pytest.mark.parametrize(
    "argument", ["'number_compiler.sequences'", "package='number_compiler.sequences'"]
)
def test_relative_dynamic_import_uses_explicit_package(
    tmp_path: Path, argument: str
) -> None:
    source = tmp_path / "src/number_compiler/resources/router.py"
    source.parent.mkdir(parents=True)
    source.write_text(
        f"from importlib import import_module as load\nload('.collatz', {argument})\n",
        encoding="utf-8",
    )
    assert python_ownership_violations(tmp_path) == (
        (
            "src/number_compiler/resources/router.py: shared code routes to "
            "sequence-family module number_compiler.sequences.collatz"
        ),
    )


def _write_isabelle_session(
    proof_root: Path,
    area: str,
    namespace: str,
    session: str,
    theory_imports: str,
    *,
    parent: str = "HOL",
    sessions: str = "",
) -> None:
    registration = proof_root / area / namespace / "ROOT"
    registration.parent.mkdir(parents=True, exist_ok=True)
    (registration.parent / "ROOT").write_text(
        f'session {session} in "Session" = {parent} +\n'
        + (f"  sessions {sessions}\n" if sessions else "")
        + f"  theories\n    {session}\n",
        encoding="utf-8",
    )
    session_dir = registration.parent / "Session"
    session_dir.mkdir(parents=True, exist_ok=True)
    (session_dir / f"{session}.thy").write_text(
        f"theory {session} imports {theory_imports} begin\nend\n",
        encoding="utf-8",
    )


def _canonical_isabelle_fixture(root: Path) -> Path:
    proof_root = root / "proofs/isabelle"
    proof_root.mkdir(parents=True)
    (proof_root / "ROOTS").write_text("shared\nfamilies\nintegration\n")
    for area, children in (
        ("shared", "arithmetic"),
        ("families", "collatz\nreverse"),
        ("integration", "contracts"),
    ):
        parent = proof_root / area
        parent.mkdir()
        (parent / "ROOTS").write_text(children + "\n", encoding="utf-8")

    _write_isabelle_session(
        proof_root,
        "shared",
        "arithmetic",
        "Shared_Base",
        "Main Shared_Helper",
    )
    _write_isabelle_session(
        proof_root,
        "families",
        "collatz",
        "Collatz_Core",
        "Main Shared_Base Reverse_Core.Reverse_Core "
        "Integration_Contract.Integration_Contract",
        parent="Shared_Base",
        sessions="Integration_Contract",
    )
    _write_isabelle_session(
        proof_root,
        "families",
        "reverse",
        "Reverse_Core",
        "Main Shared_Base",
        parent="Shared_Base",
    )
    _write_isabelle_session(
        proof_root,
        "integration",
        "contracts",
        "Integration_Contract",
        "Main Reverse_Core",
        parent="Shared_Base",
        sessions="Reverse_Core",
    )
    helper = proof_root / "shared/arithmetic/Session/Shared_Helper.thy"
    helper.write_text(
        "theory Shared_Helper imports Collatz_Core.Collatz_Core "
        "../families/collatz/Session/Collatz_Core begin\nend\n",
        encoding="utf-8",
    )
    return proof_root


def test_isabelle_policy_checks_sessions_and_theory_imports(tmp_path: Path) -> None:
    _canonical_isabelle_fixture(tmp_path)

    violations = isabelle_ownership_violations(tmp_path)

    assert len(violations) == 4
    assert any(
        "shared theory Shared_Helper imports family theory Collatz_Core" in item
        for item in violations
    )
    assert any(
        "family theory Collatz_Core imports family theory Reverse_Core" in item
        for item in violations
    )
    assert any(
        "family theory Collatz_Core imports integration theory Integration_Contract"
        in item
        for item in violations
    )
    assert any(
        "family session Collatz_Core depends on integration session Integration_Contract"
        in item
        for item in violations
    )


def test_isabelle_policy_rejects_legacy_ownership_layout(tmp_path: Path) -> None:
    assert isabelle_ownership_violations(tmp_path) == ()

    proof_root = tmp_path / "proofs/isabelle"
    proof_root.mkdir(parents=True)
    (proof_root / "ROOT").write_text(
        "session Legacy = HOL +\n  theories\n    Legacy\n", encoding="utf-8"
    )
    (proof_root / "Legacy.thy").write_text(
        "theory Legacy imports Main begin\nend\n", encoding="utf-8"
    )
    assert isabelle_ownership_violations(tmp_path) == (
        "proofs/isabelle: session Legacy has noncanonical ownership path .",
    )


def test_isabelle_policy_reuses_supplied_inventory(tmp_path: Path) -> None:
    proof_root = _canonical_isabelle_fixture(tmp_path)
    sessions = (
        Session(
            "Shared_Base",
            Path("shared/arithmetic/Session"),
            "HOL",
            (),
            ("Shared_Base",),
        ),
        Session(
            "Collatz_Core",
            Path("families/collatz/Session"),
            "Shared_Base",
            (),
            ("Collatz_Core",),
        ),
    )
    headers = {
        proof_root / "shared/arithmetic/Session/Shared_Base.thy": (
            "Shared_Base",
            ("Collatz_Core",),
        ),
        proof_root / "families/collatz/Session/Collatz_Core.thy": (
            "Collatz_Core",
            ("Main",),
        ),
    }

    violations = isabelle_ownership_violations(
        tmp_path, sessions=sessions, theory_headers=headers
    )

    assert len(violations) == 1
    assert (
        "shared theory Shared_Base imports family theory Collatz_Core" in violations[0]
    )
