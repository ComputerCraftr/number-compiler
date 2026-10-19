"""Source-derived checks for typed macro and registry declarations.

The checker is intentionally boundary-focused. It permits ordinary strings in
diagnostics and wire formats, and it permits a new, uniquely named typed
registry option in an extension module. It rejects raw strings where execution
expects typed identities, and duplicate option declarations that bypass the
canonical registry declarations.
"""

from __future__ import annotations

import ast
from collections import defaultdict
from collections.abc import Mapping
from pathlib import Path


def _call_name(call: ast.Call) -> str | None:
    if isinstance(call.func, ast.Name):
        return call.func.id
    if isinstance(call.func, ast.Attribute):
        return call.func.attr
    return None


def _argument(call: ast.Call, index: int, keyword: str) -> ast.expr | None:
    named = next(
        (item.value for item in call.keywords if item.arg == keyword),
        None,
    )
    if named is not None:
        return named
    return call.args[index] if len(call.args) > index else None


def _is_raw_string(node: ast.AST | None) -> bool:
    return isinstance(node, ast.Constant) and type(node.value) is str


def _assignment_value_targets(
    node: ast.stmt,
) -> tuple[ast.expr | None, tuple[ast.expr, ...]]:
    if isinstance(node, ast.Assign):
        return node.value, tuple(node.targets)
    if isinstance(node, ast.AnnAssign):
        return node.value, (node.target,)
    return None, ()


def _capability_table(tree: ast.Module) -> ast.Dict | None:
    """Find a direct or MappingProxyType-backed capability literal."""
    backing_name: str | None = None
    for node in tree.body:
        value, targets = _assignment_value_targets(node)
        if value is None:
            continue
        if not any(
            isinstance(target, ast.Name) and target.id == "CAPABILITIES"
            for target in targets
        ):
            continue
        if isinstance(value, ast.Dict):
            return value
        if isinstance(value, ast.Call) and _call_name(value) == "MappingProxyType":
            backing = _argument(value, 0, "mapping")
            if isinstance(backing, ast.Name):
                backing_name = backing.id
            break
    if backing_name is None:
        return None
    for node in tree.body:
        value, targets = _assignment_value_targets(node)
        if isinstance(value, ast.Dict) and any(
            isinstance(target, ast.Name) and target.id == backing_name
            for target in targets
        ):
            return value
    return None


def _parents(tree: ast.AST) -> dict[ast.AST, ast.AST]:
    return {
        child: parent
        for parent in ast.walk(tree)
        for child in ast.iter_child_nodes(parent)
    }


def _literal_option_name(
    call: ast.Call, parents: Mapping[ast.AST, ast.AST]
) -> str | None:
    named = next(
        (item.value for item in call.keywords if item.arg == "name"),
        call.args[3] if len(call.args) > 3 else None,
    )
    if _is_raw_string(named):
        if not isinstance(named, ast.Constant) or not isinstance(named.value, str):
            return None
        return named.value

    parent = parents.get(call)
    if isinstance(parent, ast.Tuple) and len(parent.elts) == 2:
        key, value = parent.elts
        if value is call and _is_raw_string(key):
            if not isinstance(key, ast.Constant) or not isinstance(key.value, str):
                return None
            return key.value
    if isinstance(parent, ast.Dict):
        for dict_key, dict_value in zip(parent.keys, parent.values, strict=True):
            if dict_value is call and _is_raw_string(dict_key):
                if not isinstance(dict_key, ast.Constant) or not isinstance(
                    dict_key.value, str
                ):
                    return None
                return dict_key.value
    return None


def _is_canonical_option_owner(tree: ast.Module) -> bool:
    """Recognize declaration owners from their current syntax, not file lists."""
    capability_table = _capability_table(tree)
    if capability_table is not None and any(
        isinstance(child, ast.Call) and _call_name(child) == "FamilySpec"
        for child in ast.walk(capability_table)
    ):
        return True

    return any(
        isinstance(node, ast.ClassDef)
        and node.name == "MatrixCapability"
        and any(
            isinstance(method, (ast.FunctionDef, ast.AsyncFunctionDef))
            and method.name == "options"
            and any(
                isinstance(child, ast.Call) and _call_name(child) == "OptionSpec"
                for child in ast.walk(method)
            )
            for method in node.body
        )
        for node in tree.body
    )


def _enum_class_names(
    root: Path, parsed_sources: Mapping[Path, ast.Module]
) -> frozenset[str]:
    """Discover enum constructors from source rather than an owner inventory."""
    names: set[str] = set()
    source_root = root / "src" / "number_compiler"
    for original_path, tree in parsed_sources.items():
        path = Path(original_path).resolve()
        if not path.is_relative_to(source_root):
            continue
        for node in tree.body:
            if not isinstance(node, ast.ClassDef):
                continue
            if any(
                isinstance(base, ast.Name) and base.id in {"Enum", "StrEnum"}
                for base in node.bases
            ):
                names.add(node.name)
    return frozenset(names)


def _capability_mapping_violations(relative: str, tree: ast.Module) -> list[str]:
    violations: list[str] = []
    value = _capability_table(tree)
    if value is None:
        return violations
    seen: dict[str, ast.expr] = {}
    for key in value.keys:
        if key is None:
            continue
        if _is_raw_string(key):
            assert isinstance(key, ast.Constant)
            violations.append(
                f"{relative}:{key.lineno}: CAPABILITIES keys must use FamilyId"
            )
        fingerprint = ast.dump(key, include_attributes=False)
        previous = seen.get(fingerprint)
        if previous is not None:
            violations.append(
                f"{relative}:{key.lineno}: duplicate family registry declaration"
            )
        else:
            seen[fingerprint] = key
    return violations


def _capability_lookup_violations(relative: str, tree: ast.Module) -> list[str]:
    violations: list[str] = []
    for node in ast.walk(tree):
        if (
            isinstance(node, ast.Subscript)
            and isinstance(node.value, ast.Name)
            and node.value.id == "CAPABILITIES"
            and _is_raw_string(node.slice)
        ):
            violations.append(
                f"{relative}:{node.lineno}: family dispatch must index by FamilyId"
            )
    return violations


def border_registry_violations(
    root: Path, parsed_sources: Mapping[Path, ast.Module]
) -> tuple[str, ...]:
    """Find raw typed-identity inputs and duplicated option declarations.

    New registry options are allowed when their names are new. Existing names
    declared again outside the source-discovered capability/matrix owners are
    rejected, while strings elsewhere in source remain outside this policy.
    """
    root = Path(root).resolve()
    source_root = (root / "src" / "number_compiler").resolve()
    violations: list[str] = []
    option_sites: dict[str, list[tuple[str, int, bool]]] = defaultdict(list)
    enum_names = _enum_class_names(root, parsed_sources)

    for original_path, tree in sorted(
        parsed_sources.items(), key=lambda item: Path(item[0]).as_posix()
    ):
        path = Path(original_path).resolve()
        if not path.is_relative_to(source_root):
            continue
        relative = path.relative_to(root).as_posix()
        canonical_options = _is_canonical_option_owner(tree)
        parents = _parents(tree)
        violations.extend(_capability_mapping_violations(relative, tree))
        violations.extend(_capability_lookup_violations(relative, tree))

        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            name = _call_name(node)
            if name == "OptionSpec":
                option_name = _literal_option_name(node, parents)
                if option_name:
                    option_sites[option_name].append(
                        (relative, node.lineno, canonical_options)
                    )
            if name == "BorderMacroIdentity":
                for field_name, position in (("family", 0), ("kind", 1)):
                    if _is_raw_string(_argument(node, position, field_name)):
                        violations.append(
                            f"{relative}:{node.lineno}: BorderMacroIdentity {field_name} must use a typed identifier"
                        )
            if name in enum_names and node.args and _is_raw_string(node.args[0]):
                violations.append(
                    f"{relative}:{node.lineno}: {name} construction must use a typed member or an external parsed value"
                )

    for option_name, sites in option_sites.items():
        canonical_sites = [site for site in sites if site[2]]
        external_sites = [site for site in sites if not site[2]]
        if canonical_sites and external_sites:
            for relative, line, _ in external_sites:
                violations.append(
                    f"{relative}:{line}: option {option_name!r} duplicates a canonical registry declaration"
                )
        elif len(external_sites) > 1:
            for relative, line, _ in external_sites:
                violations.append(
                    f"{relative}:{line}: option {option_name!r} is duplicated outside canonical owners"
                )

    return tuple(sorted(set(violations)))


__all__ = ["border_registry_violations"]
