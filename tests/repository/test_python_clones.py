"""Adversarial contracts for the shared binding-aware clone checker."""

from __future__ import annotations

import ast
import hashlib
from pathlib import Path

import pytest

from devtools.checks import python_clones
from devtools.checks.python_clones import duplicate_bodies

SOURCE = '''
def calculate(values, scale):
    """A description, not an executable difference."""
    output = []
    for value in values:
        shifted = value * scale + 3
        if shifted > 0:
            output.append(shifted - 1)
    return tuple(output)
'''


def clones(tmp_path: Path, left: str, right: str) -> int:
    paths = (tmp_path / "left.py", tmp_path / "right.py")
    trees = {}
    for path, content in zip(paths, (left, right), strict=True):
        path.write_text(content)
        trees[path] = ast.parse(content)
    return len(duplicate_bodies(tmp_path, trees))


def test_duplicate_body_sizes_are_computed_in_one_module_walk(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = tmp_path / "nested.py"
    path.write_text(SOURCE)
    tree = ast.parse(SOURCE)
    original_walk = ast.walk
    walked: list[ast.AST] = []

    def count_walk(node: ast.AST) -> list[ast.AST]:
        walked.append(node)
        return list(original_walk(node))

    monkeypatch.setattr(ast, "walk", count_walk)
    duplicate_bodies(tmp_path, {path: tree})
    assert walked == [tree]


def test_binding_resolution_is_cached_per_ast_node_and_analysis() -> None:
    tree = ast.parse(
        "def outer(value):\n"
        " state = value\n"
        " def inner(argument):\n"
        "  return state + argument\n"
        " return inner\n"
    )
    bindings = python_clones._Bindings(tree)
    outer = next(
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.FunctionDef) and node.name == "outer"
    )
    reference = next(
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.Name)
        and node.id == "state"
        and isinstance(node.ctx, ast.Load)
    )

    first = bindings.resolve(reference, "state")
    cached_entry_count = len(bindings._resolved)
    assert first == (bindings.inner[outer], "state")
    assert bindings.resolve(reference, "state") is first
    assert len(bindings._resolved) == cached_entry_count

    other_analysis = python_clones._Bindings(tree)
    other = other_analysis.resolve(reference, "state")
    assert other[0] is other_analysis.inner[outer]
    assert other[0] is not first[0]
    assert other[1] == first[1]


def renamed(source: str) -> str:
    for old, new in (
        ("calculate", "other"),
        ("values", "entries"),
        ("value", "item"),
        ("scale", "multiplier"),
        ("output", "answer"),
        ("shifted", "adjusted"),
    ):
        source = source.replace(old, new)
    return source


def test_renaming_comments_and_docstrings_do_not_hide_duplicates(
    tmp_path: Path,
) -> None:
    right = renamed(SOURCE).replace(
        "A description, not an executable difference.", "Different documentation."
    )
    assert clones(tmp_path, SOURCE, "# different formatting\n" + right) >= 1


@pytest.mark.parametrize(
    "old,new",
    [
        ("+ 3", "+ 4"),
        ("> 0", "< 0"),
        (".append(", ".extend("),
        ("tuple(output)", "list(output)"),
    ],
)
def test_literals_operators_attributes_and_free_names_remain_exact(
    tmp_path: Path, old: str, new: str
) -> None:
    assert clones(tmp_path, SOURCE, renamed(SOURCE.replace(old, new))) == 0


def test_parameter_positions_and_alias_relationships_are_preserved(
    tmp_path: Path,
) -> None:
    assert clones(tmp_path, SOURCE, SOURCE.replace("in values:", "in scale:")) == 0
    assert (
        clones(tmp_path, SOURCE, SOURCE.replace("value * scale", "value * value")) == 0
    )


def test_copied_logic_inside_different_functions_is_reported(tmp_path: Path) -> None:
    left = SOURCE.replace("    output = []", "    print('left')\n    output = []")
    right = renamed(SOURCE).replace(
        "    answer = []", "    print('right')\n    answer = []"
    )
    assert clones(tmp_path, left, right) >= 1


def test_simple_forwarders_and_stubs_are_not_substantial_logic(tmp_path: Path) -> None:
    assert (
        clones(
            tmp_path,
            "def one(x):\n return helper(x)\n",
            "def two(y):\n return helper(y)\n",
        )
        == 0
    )


def test_shadowed_comprehension_names_are_not_outer_parameters(tmp_path: Path) -> None:
    body = SOURCE.replace(
        "shifted = value * scale + 3",
        "shifted = sum(scale for scale in range(value)) + scale + 3",
    )
    assert clones(tmp_path, body, renamed(body)) >= 1
    changed = body.replace("+ scale + 3", "+ value + 3")
    assert clones(tmp_path, body, renamed(changed)) == 0


def test_global_declaration_cannot_be_normalized_into_a_local(tmp_path: Path) -> None:
    right = SOURCE.replace(
        '    """A description, not an executable difference."""', "    global output"
    )
    assert clones(tmp_path, SOURCE, right) == 0


def test_closures_nonlocals_and_comprehension_walrus_bindings(tmp_path: Path) -> None:
    body = """
def calculate(values, scale):
    output = 0
    def collect(value):
        nonlocal output
        shifted = value * scale + 3
        output += shifted
        return output
    collected = [collect(value) for value in values if (shifted := value + scale)]
    return collected, output, shifted
"""
    assert clones(tmp_path, body, renamed(body)) >= 1
    # Renaming values to an already-bound entries variable is capture, not
    # alpha equivalence; retain that changed binding relationship.
    captured = body.replace("collected", "entries")
    assert clones(tmp_path, captured, renamed(captured)) == 0


def test_digest_collisions_are_not_clone_evidence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    class Collision:
        def digest(self) -> bytes:
            return b"same"

    monkeypatch.setattr(hashlib, "sha256", lambda _: Collision())
    assert clones(tmp_path, SOURCE, renamed(SOURCE.replace("+ 3", "+ 4"))) == 0


def test_policy_command_fails_on_duplicates_without_allowlists(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    import json

    from devtools import paths
    from devtools.checks.repository_policy import main

    assert clones(tmp_path, SOURCE, renamed(SOURCE)) > 0
    monkeypatch.setattr(paths, "repository_root", lambda: tmp_path)
    assert main() == 1
    report = json.loads(capsys.readouterr().out)
    assert report["duplicate_bodies"]
    assert report["clone_minimum_expression_statement_nodes"] == 24
    assert report["clone_minimum_statements"] == 3


def test_semicolon_windows_retain_distinct_column_spans(tmp_path: Path) -> None:
    body = """def calculate(x, y):
 print('left'); z=(x*3+y*4)+(x-y)*(x+y); w=(z+x)*(z-y)+(x*y); return w+z+x+y
"""
    right = body.replace("calculate", "other").replace("'left'", "'right'")
    assert clones(tmp_path, body, right) > 0
    trees = {
        tmp_path / "left.py": ast.parse(body),
        tmp_path / "right.py": ast.parse(right),
    }
    reports = duplicate_bodies(tmp_path, trees)
    assert any(site.column > 1 for group in reports for site in group)


def test_substantial_single_expression_arithmetic_is_a_clone(tmp_path: Path) -> None:
    left = """def calculate(x,y):
 return (x*3+y*4)+(x-y)*(x+y)+(x*y)-(y*5)+(x+6)*(y-7)
"""
    right = left.replace("calculate", "other").replace("x", "p").replace("y", "q")
    assert clones(tmp_path, left, right) > 0
    assert clones(tmp_path, left, right.replace("*5", "*8")) == 0


def test_large_literal_data_and_thin_calls_are_not_computational_clones(
    tmp_path: Path,
) -> None:
    fields = ", ".join(f"'field_{i}': x" for i in range(40))
    left = f"def calculate(x):\n return helper({{{fields}}})\n"
    right = (
        left.replace("calculate", "other").replace(": x", ": y").replace("(x)", "(y)")
    )
    assert clones(tmp_path, left, right) == 0


def test_local_class_binding_is_renamable_but_attributes_remain_exact(
    tmp_path: Path,
) -> None:
    left = """def calculate(values,scale):
 class Temporary:
  payload=tuple(values)
  transformed=tuple((x+3)*scale for x in values)
  total=sum(transformed)
 return Temporary.total,Temporary.payload
"""
    right = left.replace("calculate", "other").replace("Temporary", "Accumulator")
    assert clones(tmp_path, left, right) > 0
    assert clones(tmp_path, left, right.replace("total", "result")) == 0


def closure_source(parameter: str, *, signature: str, tag: str) -> str:
    return f"""def outer({signature}):
 print({tag!r})
 def inner(items):
  output=[]
  for item in items:
   shifted=item*{parameter}+3
   if shifted>0: output.append(shifted-1)
  return tuple(output)
 return inner,{tag!r}
"""


def test_closure_captures_are_normalized_by_enclosing_parameter_position(
    tmp_path: Path,
) -> None:
    left = closure_source("scale", signature="values,scale", tag="left")
    renamed_capture = closure_source("factor", signature="entries,factor", tag="right")
    assert clones(tmp_path, left, renamed_capture) > 0
    moved_capture = closure_source("scale", signature="scale,values", tag="right")
    assert clones(tmp_path, left, moved_capture) == 0


def test_nested_defaults_and_decorators_keep_the_enclosing_binding_owner(
    tmp_path: Path,
) -> None:
    left = """def calculate(first,second):
 @decorator(first)
 def inner(value=second):
  return value+first
 result=inner(first)+inner(second)+first*second
 return result+first+second
"""
    right = (
        left.replace("calculate", "other")
        .replace("first", "left")
        .replace("second", "right")
    )
    assert clones(tmp_path, left, right) > 0
    assert clones(tmp_path, left, right.replace("value=right", "value=left")) == 0
    assert (
        clones(tmp_path, left, right.replace("decorator(left)", "decorator(right)"))
        == 0
    )
    assert clones(tmp_path, left, right.replace("@decorator", "@other_decorator")) == 0


def test_class_method_does_not_capture_the_class_namespace(tmp_path: Path) -> None:
    left = """def calculate(values,scale):
 class Local:
  scale=5
  def inner(self,items):
   output=[]
   for item in items:
    shifted=item*scale+3
    if shifted>0: output.append(shifted-1)
   return tuple(output)
 return Local,'left'
"""
    right = (
        left.replace("calculate", "other")
        .replace("Local", "Renamed")
        .replace("'left'", "'right'")
    )
    # The class attribute named scale cannot shadow the outer closure cell.
    right = right.replace("  scale=5", "  multiplier=5")
    assert clones(tmp_path, left, right) > 0


def test_nested_comprehension_and_lambda_shadowing_preserves_capture(
    tmp_path: Path,
) -> None:
    left = """def calculate(values,scale):
 result=[(lambda item: item*scale+3)(value) for value in values if value>0]
 adjusted=[value*scale-1 for value in result if value+scale>3]
 return sum(adjusted)+len(result)+scale
"""
    assert clones(tmp_path, left, renamed(left)) > 0
    captured = left.replace("lambda item: item*scale+3", "lambda scale: scale*scale+3")
    assert clones(tmp_path, left, renamed(captured)) == 0


def test_closure_captured_local_keeps_owner_declaration_position(
    tmp_path: Path,
) -> None:
    left = closure_source("scale", signature="values", tag="left").replace(
        " print('left')", " scale=3\n factor=4\n print('left')"
    )
    right = closure_source("multiplier", signature="entries", tag="right").replace(
        " print('right')", " multiplier=3\n adjustment=4\n print('right')"
    )
    assert clones(tmp_path, left, right) > 0
    assert (
        clones(tmp_path, left, right.replace("item*multiplier", "item*adjustment")) == 0
    )


def test_substantial_lambda_is_an_implicit_return_clone(tmp_path: Path) -> None:
    expression = "(x*3+y*4)+(x-y)*(x+y)+(x*y)-(y*5)+(x+6)*(y-7)"
    left = f"calculate = lambda x,y: {expression}\n"
    renamed_expression = expression.replace("x", "p").replace("y", "q")
    right = f"other = lambda p,q: {renamed_expression}\n"
    assert clones(tmp_path, left, right) > 0
    assert clones(tmp_path, f"def calculate(x,y):\n return {expression}\n", right) > 0
    assert clones(tmp_path, left, right.replace("*5", "*8")) == 0


def test_substantial_lambda_retains_capture_position(tmp_path: Path) -> None:
    expression = "(x*3+scale*4)+(x-scale)*(x+scale)+(x*scale)-(scale*5)+(x+6)*(scale-7)"
    left = f"def outer(first,scale):\n return lambda x: {expression}\n"
    right_expression = expression.replace("scale", "factor").replace("x", "p")
    right = f"def outer_other(other,factor):\n return lambda p: {right_expression}\n"
    assert clones(tmp_path, left, right) > 0
    moved = right.replace("outer_other(other,factor)", "outer_other(factor,other)")
    assert clones(tmp_path, left, moved) == 0


def test_thin_lambda_is_not_substantial(tmp_path: Path) -> None:
    assert (
        clones(tmp_path, "one=lambda x: helper(x)\n", "two=lambda y: helper(y)\n") == 0
    )
