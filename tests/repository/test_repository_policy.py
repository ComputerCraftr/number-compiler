from pathlib import Path

import pytest

from devtools.checks.repository_policy import (
    MAX_SOURCE_LINES,
    physical_line_count,
    recursion_cycles,
    repository_policy_report,
    source_line_violations,
)
from devtools.paths import repository_root

ROOT = repository_root()


def test_all_source_files_stay_at_or_below_the_single_global_line_cap() -> None:
    assert MAX_SOURCE_LINES == 1000
    assert source_line_violations(ROOT) == ()


def test_repository_python_call_graph_has_no_direct_or_mutual_recursion() -> None:
    assert recursion_cycles(ROOT) == ()


def test_recursion_cycle_checker_detects_direct_and_cross_module_mutual_cycles(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "from b import g\n"
        "def f():\n"
        "    return g()\n"
        "def direct():\n"
        "    return direct()\n"
    )
    (tmp_path / "b.py").write_text("from a import f\ndef g():\n    return f()\n")
    cycles = recursion_cycles(tmp_path)
    assert ("a:direct",) in cycles
    assert ("a:f", "b:g") in cycles


@pytest.mark.parametrize("line_count", [1000, 1001])
@pytest.mark.parametrize("final_newline", [False, True])
@pytest.mark.parametrize(
    "directory", ["src", "tests", "devtools", "devtools/checks", "devtools/proofs"]
)
def test_source_line_cap_applies_to_all_authored_source(
    tmp_path: Path,
    line_count: int,
    final_newline: bool,
    directory: str,
) -> None:
    (tmp_path / "src").mkdir()
    path = tmp_path / directory / "sample.py"
    path.parent.mkdir(parents=True, exist_ok=True)
    text = "# source\n" * line_count
    if not final_newline:
        text = text[:-1]
    path.write_text(text)
    assert physical_line_count(path) == line_count
    expected = ((f"{directory}/sample.py", 1001),) if line_count == 1001 else ()
    assert source_line_violations(tmp_path) == expected


def test_source_line_cap_rejects_an_oversized_isabelle_theory(
    tmp_path: Path,
) -> None:
    path = tmp_path / "devtools" / "proofs" / "isabelle" / "Oversized.thy"
    path.parent.mkdir(parents=True)
    path.write_text("lemma placeholder: True by simp\n" * (MAX_SOURCE_LINES + 1))
    assert source_line_violations(tmp_path) == (
        ("devtools/proofs/isabelle/Oversized.thy", MAX_SOURCE_LINES + 1),
    )
    # Theory text is line-counted but never parsed as a Python call graph.
    assert recursion_cycles(tmp_path) == ()


@pytest.mark.parametrize("ending", ["\n", "\r\n", "\r"])
def test_physical_line_count_handles_line_endings_without_extra_lines(
    tmp_path: Path, ending: str
) -> None:
    path = tmp_path / "src" / "sample.py"
    path.parent.mkdir()
    path.write_bytes(("# source" + ending).encode() * 1000)
    assert physical_line_count(path) == 1000
    assert source_line_violations(tmp_path) == ()
    path.write_text("# one\fphysical\vline\u2028still one\n")
    assert physical_line_count(path) == 1
    path.write_text("")
    assert physical_line_count(path) == 0


@pytest.mark.parametrize(
    "name", ["report.md", "generated.json", "notes.txt", "data.csv"]
)
def test_non_source_files_have_no_line_count_limit(tmp_path: Path, name: str) -> None:
    (tmp_path / "src").mkdir()
    (tmp_path / name).write_text("x\n" * 2000)
    assert source_line_violations(tmp_path) == ()
    report = repository_policy_report(tmp_path)
    assert report["max_source_lines"] == 1000
    assert report["source_line_violations"] == ()
    assert report["recursion_cycles"] == ()
    assert "max_text_lines" not in report


def test_local_import_shadows_same_named_method_without_false_recursion(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "class Owner:\n def operation(self):\n  from b import operation\n  return operation(self)\n"
    )
    (tmp_path / "b.py").write_text("def operation(owner):\n return 1\n")
    assert recursion_cycles(tmp_path) == ()
    (tmp_path / "b.py").write_text(
        "def operation(owner):\n from c import cycle\n return cycle(owner)\n"
    )
    (tmp_path / "c.py").write_text(
        "def cycle(owner):\n from b import operation\n return operation(owner)\n"
    )
    assert ("b:operation", "c:cycle") in recursion_cycles(tmp_path)


def test_call_catalog_keeps_nested_functions_and_lambdas_separate(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "def outer():\n"
        "    def inner():\n"
        "        return inner()\n"
        "    deferred = lambda: outer()\n"
        "    return inner, deferred\n"
    )
    assert recursion_cycles(tmp_path) == (("a:outer.inner",),)
