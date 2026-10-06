"""Registration ownership must not bypass dependency or execution policy checks."""

from pathlib import Path

import pytest

from devtools.checks.isabelle_registry import discover_sessions, root_files
from devtools.checks.isabelle_syntax import (
    named_type_and_locale_declarations,
    parse_sessions,
    session_dependency_closure,
)
from devtools.checks.repository_policy import isabelle_session_option_violations


def test_relocation_inventory_ignores_quoted_and_commented_carrier_names() -> None:
    text = """
datatype 'a Actual = Item 'a
type_synonym ('a, 'b) Pair = "'a × 'b"
record Payload = value :: nat
locale Contract = fixes value :: nat
(* datatype Commented = Wrong *)
text ‹datatype Documented = Wrong›
definition sample where "sample = ''datatype Quoted = Wrong''"
"""
    assert named_type_and_locale_declarations(text) == {
        "Actual",
        "Pair",
        "Payload",
        "Contract",
    }


def _registered_tree(root: Path) -> Path:
    theory_root = root / "proofs" / "isabelle"
    shared = theory_root / "shared"
    family = theory_root / "families" / "example"
    shared.mkdir(parents=True)
    family.mkdir(parents=True)
    (theory_root / "ROOTS").write_text("# Canonical owners\nshared\nfamilies/example\n")
    (shared / "ROOT").write_text("session Core in core = HOL +\n  theories Base\n")
    (family / "ROOT").write_text(
        "session Example in main = Core +\n  theories Family\n"
    )
    return theory_root


def test_registration_discovery_rebases_paths_and_checks_every_policy_owner(
    tmp_path: Path,
) -> None:
    root = _registered_tree(tmp_path)
    sessions = discover_sessions(root)
    assert [(s.name, s.directory) for s in sessions] == [
        ("Core", Path("shared/core")),
        ("Example", Path("families/example/main")),
    ]
    assert sessions[1].parent == "Core"
    family_root = root / "families/example/ROOT"
    family_root.write_text(family_root.read_text() + "  options [threads = 1]\n")
    assert isabelle_session_option_violations(tmp_path) == (
        (
            "proofs/isabelle/families/example/ROOT:3: session option "
            "threads=1 overrides shared policy"
        ),
    )


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        ("duplicate", "duplicate Isabelle session declaration"),
        ("cycle", "cyclic Isabelle session dependency"),
        ("hidden", "unregistered ROOT files"),
        ("escape", "escapes theory root"),
        ("repeat", "repeated ROOTS directory"),
        ("missing", "missing ROOT or ROOTS"),
        ("symlink", "escapes theory root"),
    ],
)
def test_invalid_registration_graph_is_rejected(
    tmp_path: Path, mutation: str, message: str
) -> None:
    root = _registered_tree(tmp_path)
    if mutation == "duplicate":
        (root / "families/example/ROOT").write_text("session Core = HOL +\n")
    elif mutation == "cycle":
        (root / "shared/ROOT").write_text("session Core = Example +\n")
    elif mutation == "hidden":
        (root / "unregistered").mkdir()
        (root / "unregistered/ROOT").write_text("session Hidden = HOL +\n")
    elif mutation == "escape":
        (root / "ROOTS").write_text("../outside\n")
    elif mutation == "repeat":
        (root / "ROOTS").write_text("shared\nshared\n")
    elif mutation == "missing":
        (root / "ROOTS").write_text("absent\n")
    else:
        (root / "escape").symlink_to(tmp_path, target_is_directory=True)
        (root / "ROOTS").write_text("escape\n")
    with pytest.raises(ValueError, match=message):
        discover_sessions(root)


def test_legacy_single_registration_uses_same_discovery(tmp_path: Path) -> None:
    registration = tmp_path / "ROOT"
    registration.write_text("session Example = HOL +\n")
    assert root_files(tmp_path) == (registration,)
    assert discover_sessions(tmp_path)[0].directory == Path(".")


def test_nested_session_path_requires_native_isabelle_quotes(tmp_path: Path) -> None:
    registration = tmp_path / "ROOT"
    registration.write_text("session Example in arithmetic/carry = HOL +\n")
    with pytest.raises(ValueError, match="path requires quotes"):
        discover_sessions(tmp_path)
    registration.write_text('session Example in "arithmetic/carry" = HOL +\n')
    assert discover_sessions(tmp_path)[0].directory == Path("arithmetic/carry")


def test_multiline_dependencies_and_inline_theories_are_not_dropped() -> None:
    sessions = parse_sessions(
        "session First in first = HOL +\n"
        "  theories First_Theory\n"
        "session Second in second = HOL +\n"
        "session Consumer in consumer = HOL +\n"
        '  sessions First\n    Second "HOL-Number_Theory"\n'
        "  theories\n    Consumer_Theory\n"
    )
    assert sessions[0].theories == ("First_Theory",)
    assert sessions[-1].dependencies == ("First", "Second", "HOL-Number_Theory")
    assert session_dependency_closure(sessions, ("Consumer",)) == (
        "First",
        "Second",
        "Consumer",
    )
