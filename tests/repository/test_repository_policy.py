import ast
import os
from collections.abc import Callable, Iterator
from pathlib import Path

import pytest

from devtools.checks import repository_policy as policy_checker
from devtools.checks.repository_policy import (
    MAX_SOURCE_LINES,
    isabelle_session_option_violations,
    physical_line_count,
    recursion_cycles,
    repository_policy_report,
    source_line_violations,
    validation_entrypoint_violations,
)
from devtools.paths import repository_root

ROOT = repository_root()


@pytest.fixture(scope="module")
def policy_report() -> dict[str, object]:
    return repository_policy_report(ROOT)


# Release quality runs the same whole-tree report once; keep its individual
# conformance assertions in the explicit validation selection, not default unit.
@pytest.mark.validation
def test_all_source_files_stay_at_or_below_the_single_global_line_cap(
    policy_report: dict[str, object],
) -> None:
    assert MAX_SOURCE_LINES == 1000
    assert policy_report["source_line_violations"] == ()


def test_aggregate_policy_report_uses_one_authored_source_walk(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    package = tmp_path / "src" / "number_compiler"
    package.mkdir(parents=True)
    (package / "__init__.py").write_text('"""test package"""\n')
    tests = tmp_path / "tests"
    tests.mkdir()
    (tests / "__init__.py").write_text('"""Temporary policy test package."""\n')
    (tests / "test_sample.py").write_text("def sample() -> int:\n    return 1\n")
    original_walk = policy_checker._iter_authored_files
    walk_calls = 0

    def count_walks(root: Path) -> tuple[Path, ...]:
        nonlocal walk_calls
        walk_calls += 1
        return original_walk(root)

    monkeypatch.setattr(policy_checker, "_iter_authored_files", count_walks)
    report = repository_policy_report(tmp_path)
    assert walk_calls == 1
    assert report["source_line_violations"] == ()
    assert report["package_violations"] == ()


def test_optional_policy_profile_reports_existing_snapshot_without_changing_report(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    package = tmp_path / "src" / "number_compiler"
    package.mkdir(parents=True)
    (package / "__init__.py").write_text('"""test package"""\n')
    sample = package / "sample.py"
    sample.write_text("def sample(value):\n    return value + 1\n")

    monkeypatch.delenv("NUMBER_COMPILER_POLICY_PROFILE", raising=False)
    ordinary_report = repository_policy_report(tmp_path)
    assert capsys.readouterr().err == ""

    monkeypatch.setenv("NUMBER_COMPILER_POLICY_PROFILE", "1")
    profiled_report = repository_policy_report(tmp_path)
    profile_output = capsys.readouterr()

    assert profiled_report == ordinary_report
    assert profile_output.out == ""
    assert "policy-profile: snapshot:complete seconds=" in profile_output.err
    assert "policy-profile: ownership:complete seconds=" in profile_output.err
    assert "policy-profile: entrypoints:complete seconds=" in profile_output.err
    assert "policy-profile: recursion:complete seconds=" in profile_output.err
    assert "policy-profile: clones:complete seconds=" in profile_output.err
    assert "policy-profile: package:complete seconds=" in profile_output.err
    expected_ast_nodes = sum(
        sum(1 for _node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))))
        for path in package.glob("*.py")
    )
    assert (
        f"policy-profile: clone-progress modules=2 ast_nodes={expected_ast_nodes} "
        in profile_output.err
    )


@pytest.mark.validation
def test_repository_root_has_no_session_level_execution_overrides(
    policy_report: dict[str, object],
) -> None:
    assert policy_report["isabelle_session_option_violations"] == ()


@pytest.mark.validation
def test_shared_and_family_ownership_dependencies_are_respected(
    policy_report: dict[str, object],
) -> None:
    assert policy_report["ownership_violations"] == ()


@pytest.mark.validation
def test_repository_python_call_graph_has_no_direct_or_mutual_recursion(
    policy_report: dict[str, object],
) -> None:
    assert policy_report["recursion_cycles"] == ()


@pytest.mark.validation
def test_repository_has_no_substantial_alpha_equivalent_logic(
    policy_report: dict[str, object],
) -> None:
    assert policy_report["duplicate_bodies"] == (), (
        "Duplicate logic: run python -m devtools.checks.repository_policy for exact locations"
    )


def test_isabelle_session_execution_options_are_centralized(tmp_path: Path) -> None:
    root = tmp_path / "proofs" / "isabelle" / "ROOT"
    root.parent.mkdir(parents=True)
    root.write_text(
        "(* options [threads=1] is only a comment *)\n"
        "session Base = HOL +\n"
        "  options [document = false, quick_and_dirty = false]\n"
        "  theories Base_Theory\n"
    )
    assert isabelle_session_option_violations(tmp_path) == ()

    root.write_text(
        "session Base = HOL +\n"
        "  options [document = false, threads = 1, timeout = 900]\n"
        "  theories Base_Theory\n"
    )
    assert isabelle_session_option_violations(tmp_path) == (
        "proofs/isabelle/ROOT:2: session option threads=1 overrides shared policy",
        "proofs/isabelle/ROOT:2: session option timeout=900 overrides shared policy",
    )


def test_isabelle_execution_policy_finds_inline_and_multiline_options(
    tmp_path: Path,
) -> None:
    root = tmp_path / "proofs" / "isabelle" / "ROOT"
    root.parent.mkdir(parents=True)
    root.write_text(
        'session Inline = HOL + options [document=false, label="threads=1"]\n'
        "  theories Inline_Theory\n"
        "session Multiline = HOL +\n"
        "  options [document = false,\n"
        '    note = "parallel_proofs=9,timeout=900",\n'
        "    parallel_proofs = 2,\n"
        "    timeout_scale = 3]\n"
        "  theories Multiline_Theory\n"
        "(* session Hidden = HOL + options [threads=1] *)\n"
    )
    assert isabelle_session_option_violations(tmp_path) == (
        "proofs/isabelle/ROOT:6: session option parallel_proofs=2 overrides shared policy",
        "proofs/isabelle/ROOT:7: session option timeout_scale=3 overrides shared policy",
    )


def test_validation_entrypoints_require_the_runner_and_block_direct_pytest(
    tmp_path: Path,
) -> None:
    checks = tmp_path / "devtools" / "checks"
    checks.mkdir(parents=True)
    (checks / "unguarded.py").write_text(
        "def main():\n    return 0\n\n"
        'if __name__ == "__main__":\n'
        "    def unused():\n"
        "        from devtools.runs import run_reported\n"
        "        return run_reported(main)\n"
        "    raise SystemExit(main())\n"
    )
    (checks / "direct.py").write_text(
        "import subprocess\nimport sys\n\n"
        "def main():\n"
        '    subprocess.run([sys.executable, "-m", "pytest"])\n'
        "    return \"subprocess.run([sys.executable, '-m', 'pytest'])\"\n\n"
        'if __name__ == "__main__":\n'
        "    from devtools.runs import run_reported\n"
        "    raise SystemExit(run_reported(main))\n"
    )
    (checks / "reversed.py").write_text(
        "def main():\n    return 0\n\n"
        'if "__main__" == __name__:\n'
        "    from ..runs import run_reported\n"
        "    raise SystemExit(run_reported(main))\n"
    )
    (checks / "unreachable.py").write_text(
        "def main():\n    return 0\n\n"
        'if __name__ == "__main__":\n'
        "    if False:\n"
        "        from devtools.runs import run_reported\n"
        "        run_reported(main)\n"
        "    raise SystemExit(main())\n"
    )
    (checks / "aliased_launchers.py").write_text(
        "import subprocess as sp\n"
        "import pytest as pt\n"
        "from subprocess import run as launch\n"
        "from pytest import main as pytest_main\n"
        "import sys as runtime\n\n"
        "def main():\n"
        '    sp.run([runtime.executable, "-m", "pytest"])\n'
        '    launch(["pytest", "tests/sample.py"])\n'
        '    pt.main(["tests/sample.py"])\n'
        '    pytest_main(["tests/sample.py"])\n\n'
        'if __name__ == "__main__":\n'
        "    from devtools.runs import run_reported as report\n"
        "    raise SystemExit(report(main))\n"
    )
    assert validation_entrypoint_violations(tmp_path) == (
        "devtools/checks/aliased_launchers.py:10: pytest must be launched by the shared release runner",
        "devtools/checks/aliased_launchers.py:11: pytest must be launched by the shared release runner",
        "devtools/checks/aliased_launchers.py:8: pytest must be launched by the shared release runner",
        "devtools/checks/aliased_launchers.py:9: pytest must be launched by the shared release runner",
        "devtools/checks/direct.py:5: pytest must be launched by the shared release runner",
        "devtools/checks/unguarded.py:4: standalone validation entry point must call run_reported",
        "devtools/checks/unreachable.py:4: standalone validation entry point must call run_reported",
    )


def test_isabelle_review_uses_the_shared_source_analysis(tmp_path: Path) -> None:
    from devtools.checks.isabelle_source_analysis import analysis_report

    proofs = tmp_path / "proofs" / "isabelle"
    proofs.mkdir(parents=True)
    (proofs / "Example.thy").write_text(
        'definition first where "first x = x * 2 + 1"\n'
        'definition second where "second y = y * 2 + 1"\n'
    )
    review = analysis_report(proofs)
    assert review["duplicates"]


def test_proof_inventory_uses_shared_declaration_owner() -> None:
    from devtools.checks.isabelle_proof_index import _declarations

    declarations = _declarations(
        '  lemma real: "True" by simp\n'
        '  text \\<open>lemma fake: "False" by simp\\<close>\n'
        '  ML_prf \\<open>val x = "lemma also_fake: False"\\<close>\n'
    )
    assert [entry["name"] for entry in declarations] == ["real"]
    assert declarations[0]["line"] == 1
    assert declarations[0]["statement_and_assumptions"] == ': "True"'


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
    "directory",
    ["src", "tests", "devtools", "devtools/checks", "devtools/verification"],
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


@pytest.mark.parametrize("suffix", [".thy", ".ML", ".sml", ".pyi"])
def test_source_line_cap_rejects_an_oversized_isabelle_theory(
    tmp_path: Path,
    suffix: str,
) -> None:
    path = tmp_path / "proofs" / "isabelle" / f"Oversized{suffix}"
    path.parent.mkdir(parents=True)
    path.write_text("lemma placeholder: True by simp\n" * (MAX_SOURCE_LINES + 1))
    assert source_line_violations(tmp_path) == (
        (f"proofs/isabelle/Oversized{suffix}", MAX_SOURCE_LINES + 1),
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


def test_policy_report_exposes_single_statement_clone_threshold(
    tmp_path: Path,
) -> None:
    report = repository_policy_report(tmp_path)
    assert report["clone_minimum_single_statement_operations"] == 3


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
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "a.py").write_text(
        "def outer():\n"
        "    def inner():\n"
        "        return inner()\n"
        "    deferred = lambda: outer()\n"
        "    return inner, deferred\n"
    )

    def unexpected_ast_walk(_node: ast.AST) -> Iterator[ast.AST]:
        raise AssertionError("catalog should use its existing explicit traversal")

    monkeypatch.setattr(ast, "walk", unexpected_ast_walk)
    assert recursion_cycles(tmp_path) == (("a:outer.inner",),)


def test_generated_run_sources_are_not_authored_policy_inputs(tmp_path: Path) -> None:
    generated = tmp_path / "results/runs/example/old.py"
    generated.parent.mkdir(parents=True)
    generated.write_text(
        "def obsolete():\n    return obsolete()\n" + "# raw evidence\n" * 1001
    )
    assert source_line_violations(tmp_path) == ()
    assert recursion_cycles(tmp_path) == ()
    # Only the repository's generated root is exempt, not an authored subpackage.
    authored = tmp_path / "src/results/bad.py"
    authored.parent.mkdir(parents=True)
    authored.write_text(generated.read_text())
    assert source_line_violations(tmp_path)
    assert recursion_cycles(tmp_path)


def test_policy_walk_prunes_generated_roots_before_descending(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    for relative in (
        "results/runs/large/ignored.py",
        ".venv/lib/python/site-packages/ignored.py",
    ):
        generated = tmp_path / relative
        generated.parent.mkdir(parents=True, exist_ok=True)
        generated.write_text(
            "def obsolete():\n    return obsolete()\n" + "# raw\n" * 1001
        )

    authored = tmp_path / "src/results/authored.py"
    authored.parent.mkdir(parents=True)
    authored.write_text("def cycle():\n    return cycle()\n" + "# authored\n" * 999)

    visited: list[Path] = []
    original_walk = os.walk

    def recording_walk(
        root: Path,
        topdown: bool = True,
        onerror: Callable[[OSError], None] | None = None,
        followlinks: bool = False,
    ) -> Iterator[tuple[str, list[str], list[str]]]:
        for current, dirnames, filenames in original_walk(
            root,
            topdown=topdown,
            onerror=onerror,
            followlinks=followlinks,
        ):
            visited.append(Path(current).relative_to(tmp_path))
            yield current, dirnames, filenames

    monkeypatch.setattr(os, "walk", recording_walk)
    assert source_line_violations(tmp_path) == (("src/results/authored.py", 1001),)
    assert recursion_cycles(tmp_path) == (("results.authored:cycle",),)
    assert Path("src/results") in visited
    assert not any(
        relative.parts and relative.parts[0] in {"results", ".venv"}
        for relative in visited
    )


def test_recursive_local_aliases_and_lambdas_are_not_escape_hatches(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "def direct():\n    again = direct\n    return again()\n"
        "loop = lambda: loop()\n"
        "def outer():\n    next_call = lambda: outer()\n    return next_call()\n"
    )
    cycles = recursion_cycles(tmp_path)
    assert ("a:direct",) in cycles
    assert ("a:loop",) in cycles
    assert ("a:outer", "a:outer.next_call") in cycles


def test_parameter_shadowing_is_not_global_recursion(tmp_path: Path) -> None:
    (tmp_path / "a.py").write_text(
        "def operation(operation):\n    return operation()\n"
    )
    assert recursion_cycles(tmp_path) == ()


def test_method_receiver_renaming_and_async_calls_cannot_hide_recursion(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "class Owner:\n    def cycle(receiver):\n        again = receiver.cycle\n        return again()\n"
        "async def asynchronous():\n    return await asynchronous()\n"
        "class Other:\n    @staticmethod\n    def operation(value):\n        return value.operation()\n"
    )
    assert recursion_cycles(tmp_path) == (("a:Owner.cycle",), ("a:asynchronous",))


def test_function_scope_module_aliases_are_checked_as_method_receivers(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "def f():\n    import b as peer\n    return peer.g()\n"
    )
    (tmp_path / "b.py").write_text("from a import f\ndef g():\n    return f()\n")
    assert ("a:f", "b:g") in recursion_cycles(tmp_path)


def test_receiver_and_destructured_aliases_cannot_hide_recursion(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "class Owner:\n"
        "    def cycle(self):\n"
        "        receiver = self\n"
        "        return receiver.cycle()\n"
        "def direct():\n"
        "    again, = (direct,)\n"
        "    return again()\n"
    )
    cycles = recursion_cycles(tmp_path)
    assert ("a:Owner.cycle",) in cycles
    assert ("a:direct",) in cycles


def test_assignment_expression_aliases_inside_comprehensions_are_checked(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "def loop():\n    return [(again := loop)() for _ in (0,)]\n"
    )
    assert ("a:loop",) in recursion_cycles(tmp_path)


def test_conditional_callable_aliases_keep_both_reachable_targets(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "def loop(callback, enabled):\n"
        "    alias = loop if enabled else callback\n"
        "    return alias()\n"
    )
    assert ("a:loop",) in recursion_cycles(tmp_path)


def test_same_module_static_class_calls_form_cross_class_cycles(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "class A:\n"
        "    @staticmethod\n"
        "    def f():\n"
        "        return B.g()\n"
        "class B:\n"
        "    @staticmethod\n"
        "    def g():\n"
        "        return A.f()\n"
    )
    assert recursion_cycles(tmp_path) == (("a:A.f", "a:B.g"),)


def test_comprehension_targets_do_not_shadow_enclosing_function_names(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "def loop():\n    [loop for loop in (0,)]\n    return loop()\n"
    )
    assert recursion_cycles(tmp_path) == (("a:loop",),)


def test_comprehension_target_shadowing_does_not_create_false_recursion(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "def loop(callbacks):\n    return [loop() for loop in callbacks]\n"
    )
    assert recursion_cycles(tmp_path) == ()


def test_global_and_nonlocal_bindings_remain_resolvable(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "def global_target():\n"
        "    return global_wrapper()\n"
        "def global_wrapper():\n"
        "    global global_target\n"
        "    global_target = global_target\n"
        "    return global_target()\n"
        "def outer():\n"
        "    def nonlocal_target():\n"
        "        return nonlocal_wrapper()\n"
        "    def nonlocal_wrapper():\n"
        "        nonlocal nonlocal_target\n"
        "        nonlocal_target = nonlocal_target\n"
        "        return nonlocal_target()\n"
        "    return nonlocal_target()\n"
    )
    cycles = recursion_cycles(tmp_path)
    assert ("a:global_target", "a:global_wrapper") in cycles
    assert ("a:outer.nonlocal_target", "a:outer.nonlocal_wrapper") in cycles


def test_nested_scope_bindings_do_not_create_false_recursion(
    tmp_path: Path,
) -> None:
    (tmp_path / "m.py").write_text(
        "def f():\n"
        "    return outer(lambda: 0)\n"
        "def outer(f):\n"
        "    def inner():\n"
        "        return f()\n"
        "    return inner()\n"
        "class C:\n"
        "    def method(self, callback):\n"
        "        def inner(self):\n"
        "            return self.method()\n"
        "        return inner(callback)\n"
        "    @staticmethod\n"
        "    def static(self):\n"
        "        return self.static()\n"
        "    def named(self, C):\n"
        "        return C.named()\n"
    )
    (tmp_path / "api.py").write_text("def f():\n    return 1\n")
    (tmp_path / "m2.py").write_text("import api\ndef f(api):\n    return api.f()\n")
    assert recursion_cycles(tmp_path) == ()


def test_rebound_and_closure_aliases_are_resolved_without_scope_leaks(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "def f():\n"
        "    alias = f\n"
        "    def inner():\n"
        "        return alias()\n"
        "    return inner()\n"
        "alias = f\n"
        "class C:\n"
        "    def method(self, callback):\n"
        "        self = callback\n"
        "        return self.method()\n"
        "def comp(callbacks):\n"
        "    alias = comp\n"
        "    return [alias() for alias in callbacks]\n"
    )
    (tmp_path / "api.py").write_text("def method():\n    return 1\n")
    cycles = recursion_cycles(tmp_path)
    assert ("a:f", "a:f.inner") in cycles
    assert ("a:C.method",) not in cycles
    assert ("a:comp",) not in cycles


def test_exception_and_match_bindings_do_not_leak_global_function_names(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "def loop():\n"
        "    try:\n"
        "        raise RuntimeError\n"
        "    except RuntimeError as loop:\n"
        "        return loop()\n"
        "    return loop()\n"
        "def matched():\n"
        "    value = {}\n"
        "    match value:\n"
        "        case {**matched}:\n"
        "            return matched()\n"
        "    return matched()\n"
    )
    assert recursion_cycles(tmp_path) == ()


def test_nested_definition_defaults_and_decorators_belong_to_enclosing_function(
    tmp_path: Path,
) -> None:
    (tmp_path / "a.py").write_text(
        "def outer_default():\n"
        "    def inner(value=outer_default()):\n"
        "        return value\n"
        "    return inner()\n"
        "def factory(value):\n"
        "    return outer_decorator()\n"
        "def outer_decorator():\n"
        "    @factory(outer_decorator)\n"
        "    def decorated():\n"
        "        return 1\n"
        "    return inner()\n"
    )
    cycles = recursion_cycles(tmp_path)
    assert ("a:outer_default",) in cycles
    assert ("a:factory", "a:outer_decorator") in cycles


@pytest.mark.parametrize("name", ["ROOT", "ROOTS"])
def test_isabelle_session_sources_share_the_line_cap(tmp_path: Path, name: str) -> None:
    path = tmp_path / name
    path.write_text("(* session source *)\n" * 1000)
    assert source_line_violations(tmp_path) == ()
    path.write_text(path.read_text() + "(* another line *)\n")
    assert source_line_violations(tmp_path) == ((name, 1001),)


@pytest.mark.parametrize("name", ("build", "dist", "venv"))
def test_authored_nested_directory_names_cannot_hide_policy_violations(
    tmp_path: Path,
    name: str,
) -> None:
    folder = tmp_path / "src" / "package" / name
    folder.mkdir(parents=True)
    source = "def cycle():\n    return cycle()\n" + "# authored\n" * 999
    (folder / "logic.py").write_text(source)
    generated = tmp_path / name
    generated.mkdir()
    (generated / "ignored.py").write_text(source)
    report = repository_policy_report(tmp_path)
    assert report["source_line_violations"] == ((f"src/package/{name}/logic.py", 1001),)
    assert report["recursion_cycles"] == ((f"package.{name}.logic:cycle",),)
