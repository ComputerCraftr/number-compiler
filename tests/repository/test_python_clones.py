"""Adversarial contracts for the shared binding-aware clone checker."""

from __future__ import annotations

import ast
import hashlib
from collections.abc import Sized
from pathlib import Path
from typing import cast

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
    trees: dict[Path, ast.Module] = {}
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
    original_inventory = python_clones.module_ast_inventory
    inventoried: list[ast.AST] = []

    def count_inventory(
        node: ast.Module,
    ) -> tuple[
        list[ast.AST],
        dict[ast.AST, tuple[ast.AST, ...]],
        dict[ast.AST, tuple[ast.AST, ...]],
        dict[ast.AST, tuple[list[ast.stmt], ...]],
        dict[ast.stmt, tuple[ast.stmt, ...]],
    ]:
        inventoried.append(node)
        return original_inventory(node)

    monkeypatch.setattr(python_clones, "module_ast_inventory", count_inventory)
    duplicate_bodies(tmp_path, {path: tree})
    assert inventoried == [tree]


def test_small_complete_suite_does_not_generate_substantial_windows(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = tmp_path / "small.py"
    source = "def small():\n a=1\n b=2\n c=3\n d=4\n"
    path.write_text(source)

    def unexpected_windows(_body: object) -> object:
        raise AssertionError("small suite should be rejected before windows")

    monkeypatch.setattr(python_clones, "_window_bodies", unexpected_windows)
    assert duplicate_bodies(tmp_path, {path: ast.parse(source)}) == ()


def test_plain_token_events_skip_identifier_rendering(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def unexpected_render(
        _event: python_clones.IdentifierToken,
        _names: dict[python_clones.TokenBinding, int],
    ) -> str:
        raise AssertionError("plain string tokens need no identifier rendering")

    monkeypatch.setattr(python_clones, "_render_token_event", unexpected_render)
    tokens: list[str] = []
    names: dict[python_clones.TokenBinding, int] = {}
    binding = (None, "sample")

    python_clones.consume_token_events(
        (
            "Constant:int:3:None",
            python_clones.IdentifierReservation(binding),
            "BinOp",
        ),
        names,
        tokens,
    )

    assert tokens == ["Constant:int:3:None", "BinOp"]
    assert names == {binding: 0}


def test_statement_projection_preserves_binding_tokens() -> None:
    sources = (
        """
def outer(values, scale):
    global shared_value
    state = 0
    class Local:
        label = "local"
        def transform(self, item):
            if item > 0:
                return item * scale + 3
            return 0
    def inner(value=scale):
        nonlocal state
        import math as arithmetic
        try:
            output = []
            for index, item in enumerate(values):
                shifted = item * value + scale + index + 1
                if shifted > 0:
                    output.append(arithmetic.floor(shifted))
            pieces = [
                (lambda element: element * scale + 3)(item)
                for item in values if (last := item) > 0
            ]
            payload = {"first": pieces[0], "rest": tuple(pieces[1:])}
            match payload:
                case {"first": first, **remaining}:
                    state += first + len(remaining)
                case [first, *rest]:
                    state += first + len(rest)
                case _:
                    state += 1
        except Exception as error:
            state += len(str(error))
        mapper = lambda item: (item * 3 + scale * 4) + (item - scale) * (item + scale) + (item * scale) - (scale * 5) + (item + 6) * (scale - 7)
        return tuple(output), tuple(pieces), mapper, state
    return inner, Local
""",
        """def windows(x,y):
    print('left'); a=(x*3+y*4)+(x-y)*(x+y); b=(a+x)*(a-y)+(x*y); return b+x+y
""",
    )

    reference_digest = hashlib.sha256()
    for source in sources:
        tree = ast.parse(source)
        (
            nodes,
            _all_children,
            lexical_children,
            statement_suites,
            statement_children,
        ) = python_clones.module_ast_inventory(tree)
        assert nodes == list(ast.walk(tree))
        subtree_sizes: dict[ast.AST, tuple[int, int, int]] = {}
        for node in reversed(nodes):
            children = [subtree_sizes[child] for child in ast.iter_child_nodes(node)]
            subtree_sizes[node] = (
                int(isinstance(node, (ast.stmt, ast.expr)))
                + sum(size for size, _, _ in children),
                int(isinstance(node, ast.stmt))
                + sum(count for _, count, _ in children),
                int(isinstance(node, python_clones.OPERATIONS))
                + sum(count for _, _, count in children),
            )
        bindings = python_clones.Bindings(tree, lexical_children=lexical_children)
        for function in nodes:
            if not isinstance(function, python_clones.FUNCTIONS):
                continue
            projection = python_clones.FunctionTokenProjection(
                bindings, function, statement_children
            )
            for body in python_clones.substantial_bodies(
                function,
                subtree_sizes,
                lexical_children=lexical_children,
                statement_suites=statement_suites,
            ):
                expected = python_clones.function_tokens(body, bindings, function)
                assert projection.tokenize(body) == expected
                canonical = python_clones.canonical_tokens(expected[0])
                reference_digest.update(len(canonical).to_bytes(8, "big"))
                reference_digest.update(canonical)
                reference_digest.update(
                    f"{expected[1]},{expected[2]},{expected[3]};".encode("ascii")
                )
    # The production projection has cached nested statements rather than
    # rebuilding each nested suite for every containing candidate.
    nested_tree = ast.parse("def nested():\n if flag:\n  first = 1\n  second = 2\n")
    nested_nodes, _, _, _, statement_children = python_clones.module_ast_inventory(
        nested_tree
    )
    function = next(node for node in nested_nodes if isinstance(node, ast.FunctionDef))
    branch = next(node for node in nested_nodes if isinstance(node, ast.If))
    assert statement_children[function] == (branch,)
    assert tuple(statement_children[branch]) == tuple(branch.body)
    assert (
        reference_digest.hexdigest()
        == "af11a9c55aa525d4417cf6738190db19afc4859e1f6b582ce0cdcf45e01a18a0"
    )


def test_reviewer_binding_forms_keep_frozen_tokens() -> None:
    source = """
def sample(factor):
    total = factor
    class Local:
        async def convert(self, values):
            nonlocal total
            transform = lambda item: item * factor + 3
            try:
                match values[0]:
                    case {"value": matched, **remainder}:
                        total = matched + len(remainder)
                    case _:
                        total = 0
            except Exception as problem:
                total = len(str(problem))
            return transform(values[0]), total
    return Local
"""

    def token_digest(text: str) -> str:
        tree = ast.parse(text)
        function = tree.body[0]
        assert isinstance(function, ast.FunctionDef)
        tokens = python_clones.function_tokens(
            function.body, python_clones.Bindings(tree), function
        )[0]
        return hashlib.sha256(python_clones.canonical_tokens(tokens)).hexdigest()

    alpha_renamed = (
        source.replace("sample", "process")
        .replace("factor", "scale")
        .replace("total", "result")
        .replace("Local", "Container")
        .replace("values", "entries")
        .replace("transform", "mapper")
        .replace("item", "element")
        .replace("matched", "captured")
        .replace("remainder", "extras")
        .replace("problem", "error")
    )
    changed_capture = source.replace("item * factor", "item * matched")

    expected = "ead3e18a56aa65f56e04c839cb4dd3daa908d4aff165b1c61fe66a50c065f7cf"
    assert token_digest(source) == expected
    assert token_digest(alpha_renamed) == expected
    assert token_digest(changed_capture) != expected


def test_binding_resolution_is_cached_per_ast_node_and_analysis() -> None:
    tree = ast.parse(
        "def outer(value):\n"
        " state = value\n"
        " def inner(argument):\n"
        "  return state + argument\n"
        " return inner\n"
    )
    bindings = python_clones.Bindings(tree)
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
    cached_entry_count = len(
        cast(Sized, object.__getattribute__(bindings, "_resolved"))
    )
    assert first == (bindings.inner[outer], "state")
    assert bindings.resolve(reference, "state") is first
    assert (
        len(cast(Sized, object.__getattribute__(bindings, "_resolved")))
        == cached_entry_count
    )

    other_analysis = python_clones.Bindings(tree)
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

    def digest(_data: object) -> Collision:
        return Collision()

    monkeypatch.setattr(hashlib, "sha256", digest)
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
