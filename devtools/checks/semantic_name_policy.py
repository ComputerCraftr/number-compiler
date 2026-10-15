"""Check typed dispatch, named counter keys, and centralized CLI options."""

from __future__ import annotations

import ast
import re
from collections.abc import Mapping
from pathlib import Path

_API_DECLARATION_MODULES = frozenset(
    {
        "observation_types.py",
        "family_registry.py",
        "cli_requests.py",
    }
)
_SEMANTIC_ARGUMENT_NAMES = frozenset(
    {"family", "information", "observation", "selector"}
)
_SEMANTIC_ENUMS = frozenset({"FamilyId", "ObservationId", "SelectorId"})
_VERSION_TAG = re.compile(r"[-_]v[0-9]+(?:[-_]|$)")


def _string_constants(node: ast.AST) -> tuple[ast.Constant, ...]:
    return tuple(
        child
        for child in ast.walk(node)
        if isinstance(child, ast.Constant) and type(child.value) is str
    )


def _is_semantic_attribute(node: ast.AST) -> bool:
    return isinstance(node, ast.Attribute) and node.attr in {
        "family",
        "info",
        "selector",
    }


def _constant_string(node: ast.AST) -> tuple[ast.Constant, ...]:
    return (node,) if isinstance(node, ast.Constant) and type(node.value) is str else ()


def _dispatch_string_literals(
    node: ast.Compare, semantic_values: Mapping[str, frozenset[str]]
) -> tuple[ast.Constant, ...]:
    operands = (node.left, *node.comparators)
    if any(_is_semantic_attribute(operand) for operand in operands) or any(
        isinstance(operand, ast.Name) and operand.id in _SEMANTIC_ARGUMENT_NAMES
        for operand in operands
    ):
        return _string_constants(node)
    if any(
        isinstance(operand, ast.Name) and operand.id == "name" for operand in operands
    ):
        return tuple(
            literal
            for literal in _string_constants(node)
            if literal.value in semantic_values["ObservationId"]
        )
    return ()


def _semantic_id_values(
    api_root: Path, parsed_sources: Mapping[Path, ast.Module]
) -> dict[str, frozenset[str]]:
    """Read canonical family, selector and observation spellings from AST enums."""
    values: dict[str, set[str]] = {name: set() for name in _SEMANTIC_ENUMS}
    for path, tree in parsed_sources.items():
        resolved_path = Path(path).resolve()
        if (
            resolved_path.parent != api_root
            or resolved_path.name not in _API_DECLARATION_MODULES
        ):
            continue
        for node in tree.body:
            if not isinstance(node, ast.ClassDef) or node.name not in _SEMANTIC_ENUMS:
                continue
            for member in node.body:
                value = (
                    member.value
                    if isinstance(member, (ast.Assign, ast.AnnAssign))
                    else None
                )
                if isinstance(value, ast.Constant) and type(value.value) is str:
                    values[node.name].add(value.value)
    return {name: frozenset(items) for name, items in values.items()}


def _counter_string_literals(node: ast.AST) -> tuple[ast.Constant, ...]:
    """Return literal keys read or written through an owned counter mapping."""
    if isinstance(node, ast.Subscript) and _is_counter_mapping(node.value):
        return _constant_string(node.slice)
    if (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "get"
        and _is_counter_mapping(node.func.value)
        and node.args
    ):
        return _constant_string(node.args[0])
    return ()


def _is_counter_mapping(node: ast.AST) -> bool:
    return isinstance(node, ast.Attribute) and node.attr == "counters"


def _identity_domain_literals(node: ast.Call) -> tuple[ast.Constant, ...]:
    domain: ast.AST | None
    if node.args:
        domain = node.args[0]
    else:
        domain = next(
            (keyword.value for keyword in node.keywords if keyword.arg == "digest"),
            None,
        )
    return (
        (domain,)
        if isinstance(domain, ast.Constant) and type(domain.value) is str
        else ()
    )


def _duplicate_cli_flag_violations(
    root: Path, api_root: Path, parsed_sources: Mapping[Path, ast.Module]
) -> tuple[str, ...]:
    declarations: dict[str, list[tuple[Path, int]]] = {}
    for original_path, tree in parsed_sources.items():
        path = Path(original_path).resolve()
        if path.parent != api_root:
            continue
        for node in ast.walk(tree):
            if not (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "add_argument"
            ):
                continue
            for argument in node.args:
                if (
                    isinstance(argument, ast.Constant)
                    and type(argument.value) is str
                    and argument.value.startswith("-")
                ):
                    declarations.setdefault(argument.value, []).append(
                        (path, node.lineno)
                    )
    violations: list[str] = []
    for flag, sites in declarations.items():
        ordered_sites = sorted(sites, key=lambda site: (site[0].as_posix(), site[1]))
        for path, line in ordered_sites[1:]:
            relative = path.relative_to(root).as_posix()
            violations.append(
                f"{relative}:{line}: CLI flag {flag} is declared more than once"
            )
    return tuple(violations)


def _is_final_str_annotation(annotation: ast.AST) -> bool:
    return (
        isinstance(annotation, ast.Subscript)
        and isinstance(annotation.value, ast.Name)
        and annotation.value.id == "Final"
        and isinstance(annotation.slice, ast.Name)
        and annotation.slice.id == "str"
    )


def _enum_member_assignment(
    node: ast.Constant, parents: Mapping[ast.AST, ast.AST]
) -> bool:
    assignment = parents.get(node)
    if not isinstance(assignment, (ast.Assign, ast.AnnAssign)):
        return False
    owner = parents.get(assignment)
    if not isinstance(owner, ast.ClassDef):
        return False
    return any(
        isinstance(base, ast.Name) and base.id in {"Enum", "StrEnum"}
        for base in owner.bases
    )


def _version_tag_violations(
    root: Path, parsed_sources: Mapping[Path, ast.Module]
) -> tuple[str, ...]:
    """Require named, immutable owners for serialized version tags."""
    violations: list[str] = []
    for original_path, tree in parsed_sources.items():
        path = Path(original_path).resolve()
        source_root = (root / "src" / "number_compiler").resolve()
        if not path.is_relative_to(source_root):
            continue
        relative = path.relative_to(root).as_posix()
        parents = {
            child: parent
            for parent in ast.walk(tree)
            for child in ast.iter_child_nodes(parent)
        }
        for node in ast.walk(tree):
            if (
                not isinstance(node, ast.Constant)
                or type(node.value) is not str
                or _VERSION_TAG.search(node.value) is None
                or _enum_member_assignment(node, parents)
            ):
                continue
            assignment = parents.get(node)
            if isinstance(assignment, ast.AnnAssign) and _is_final_str_annotation(
                assignment.annotation
            ):
                continue
            violations.append(
                f"{relative}:{node.lineno}: versioned semantic tags must use named Final[str] constants"
            )
    return tuple(violations)


def semantic_name_violations(
    root: Path,
    parsed_sources: Mapping[Path, ast.Module],
) -> tuple[str, ...]:
    """Reject direct metric/domain literals and duplicated API observation logic.

    The observation declarations and parser boundary are the only places where
    serialized CLI spellings may be introduced. Consumers compare typed IDs.
    Resource counter keys and semantic identity domains likewise come from
    named owners instead of being repeated as call-site literals.
    """
    root = Path(root).resolve()
    source_root = (root / "src" / "number_compiler").resolve()
    api_root = source_root / "api"
    violations: list[str] = []
    semantic_id_values = _semantic_id_values(api_root, parsed_sources)

    for original_path, tree in sorted(
        parsed_sources.items(), key=lambda item: Path(item[0]).as_posix()
    ):
        path = Path(original_path).resolve()
        if not path.is_relative_to(source_root):
            continue
        relative = path.relative_to(root).as_posix()
        in_api = path.parent == api_root
        canonical_api_module = in_api and path.name in _API_DECLARATION_MODULES

        for node in ast.walk(tree):
            if isinstance(node, ast.Call):
                if (
                    isinstance(node.func, ast.Attribute)
                    and node.func.attr == "bump"
                    and node.args
                    and isinstance(node.args[0], ast.Constant)
                    and type(node.args[0].value) is str
                ):
                    violations.append(
                        f"{relative}:{node.lineno}: metric keys must use named constants"
                    )
                if (
                    isinstance(node.func, ast.Name)
                    and node.func.id == "SemanticIdentity"
                    and _identity_domain_literals(node)
                ):
                    violations.append(
                        f"{relative}:{node.lineno}: semantic identity domains must use SemanticIdentityDomain"
                    )
                if (
                    in_api
                    and not canonical_api_module
                    and isinstance(node.func, ast.Attribute)
                    and node.func.attr == "add_argument"
                ):
                    violations.append(
                        f"{relative}:{node.lineno}: API options must be declared by the family registry"
                    )
                for literal in _counter_string_literals(node):
                    violations.append(
                        f"{relative}:{literal.lineno}: metric keys must use named constants"
                    )
            elif isinstance(node, (ast.Subscript, ast.Call)):
                for literal in _counter_string_literals(node):
                    violations.append(
                        f"{relative}:{literal.lineno}: metric keys must use named constants"
                    )
            elif in_api and isinstance(node, ast.Compare):
                for literal in _dispatch_string_literals(node, semantic_id_values):
                    violations.append(
                        f"{relative}:{literal.lineno}: semantic dispatch must use typed identifiers"
                    )

    violations.extend(_duplicate_cli_flag_violations(root, api_root, parsed_sources))
    violations.extend(_version_tag_violations(root, parsed_sources))
    return tuple(sorted(set(violations)))


__all__ = ["semantic_name_violations"]
