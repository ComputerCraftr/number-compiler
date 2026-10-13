"""Architecture ownership rules for shared Python and Isabelle sources."""

from __future__ import annotations

import ast
import re
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path

from devtools.checks.dependency_graph import (
    module_package,
    source_syntax,
)
from devtools.checks.isabelle_registry import discover_sessions
from devtools.checks.isabelle_syntax import Session, parse_theory_header
from devtools.checks.source_discovery import authored_files

_SHARED_PYTHON_PACKAGES = frozenset({"arithmetic", "hashlife", "resources"})
_ISABELLE_ROOTS = frozenset({"shared", "families", "integration"})
_KNOWN_FAMILY_ML_STRUCTURES = frozenset(
    {
        "Comma_Entry_Arithmetic",
        "Comma_Proof_Dependency_Audit",
        "Comma_Proof_Profile",
    }
)


def _is_sequence_module(name: str) -> bool:
    return name == "number_compiler.sequences" or name.startswith(
        "number_compiler.sequences."
    )


def _resolve_package_module(
    name: str,
    path: Path,
    source_root: Path,
    package_override: str | None = None,
) -> str:
    """Resolve absolute and relative strings using the importing module's package."""
    if not name.startswith("."):
        return name
    package = (
        tuple(package_override.split("."))
        if package_override is not None
        else module_package(path, source_root)
    )
    level = len(name) - len(name.lstrip("."))
    keep = max(0, len(package) - level + 1)
    return ".".join((*package[:keep], name[level:]))


def python_ownership_violations(
    root: Path,
    *,
    parsed_sources: Mapping[Path, ast.Module] | None = None,
) -> tuple[str, ...]:
    """Reject imports from shared arithmetic/runtime/resource code into families.

    The parsed snapshot may be supplied by ``repository_policy`` so its
    aggregate report can reuse the ASTs it already parsed. Walking every AST
    node intentionally includes function-local and ``TYPE_CHECKING`` imports.
    """
    root = Path(root).resolve()
    source_root = (root / "src" / "number_compiler").resolve()
    if parsed_sources is None:
        trees = (
            {
                path.resolve(): ast.parse(
                    path.read_text(encoding="utf-8"), filename=str(path)
                )
                for path in authored_files(source_root)
                if path.suffix == ".py"
            }
            if source_root.is_dir()
            else {}
        )
    else:
        trees = {
            Path(path).resolve(): tree
            for path, tree in parsed_sources.items()
            if Path(path).resolve().is_relative_to(source_root)
        }

    violations: list[str] = []
    for path, tree in sorted(trees.items(), key=lambda item: item[0].as_posix()):
        if not path.is_relative_to(source_root):
            continue
        relative = path.relative_to(root).as_posix()
        parts = path.relative_to(source_root).parts
        if not parts or parts[0] not in _SHARED_PYTHON_PACKAGES:
            continue
        syntax = source_syntax(path, tree=tree, source_root=source_root)
        references = {
            (line, imported)
            for line, imported in syntax.import_references
            if _is_sequence_module(imported)
        }
        family_references = tuple(
            (line, imported)
            for line, imported in sorted(references)
            if not any(
                other_line == line and imported.startswith(other + ".")
                for other_line, other in references
            )
        )
        for line, imported in family_references:
            violations.append(
                f"{relative}:{line}: shared code imports sequence-family module {imported}"
            )
        dynamic_routes = {
            _resolve_package_module(imported, path, source_root, package)
            for imported, package in syntax.dynamic_import_routes
        }
        export_routes = {
            _resolve_package_module(imported, path, source_root)
            for imported in syntax.export_modules
        }
        for resolved in sorted(dynamic_routes | export_routes):
            if _is_sequence_module(resolved):
                violations.append(
                    f"{relative}: shared code routes to sequence-family module {resolved}"
                )
        if syntax.unknown_dynamic_import:
            violations.append(
                f"{relative}: shared code has an unresolvable dynamic import router"
            )
    return tuple(sorted(set(violations)))


@dataclass(frozen=True, slots=True)
class _IsabelleOwner:
    layer: str
    name: str


def _isabelle_owner(parts: tuple[str, ...]) -> _IsabelleOwner | None:
    if len(parts) < 3 or parts[0] not in _ISABELLE_ROOTS or not parts[1]:
        return None
    if parts[0] == "shared":
        return _IsabelleOwner("shared", parts[1])
    if parts[0] == "families":
        return _IsabelleOwner("family", parts[1])
    return _IsabelleOwner("integration", parts[1])


def _owner_violation(source: _IsabelleOwner, target: _IsabelleOwner) -> bool:
    if source.layer == "integration":
        return False
    if source.layer == "shared":
        return target.layer != "shared"
    return target.layer == "integration" or (
        target.layer == "family" and source.name != target.name
    )


def _theory_name(reference: str) -> str:
    """Normalize a ROOT/import-qualified theory reference to its local basename."""
    return (
        reference.removesuffix(".thy")
        .rsplit("/", maxsplit=1)[-1]
        .rsplit(".", maxsplit=1)[-1]
    )


def _audit_dependency(source: Path, target: Path) -> bool:
    """Audit-only implementation cannot supply release authority."""
    return "audit" not in source.parts and "audit" in target.parts


def _mask_ml_comments_and_strings(text: str) -> str:
    """Mask Standard ML comments and strings while preserving line positions."""
    output = list(text)
    comment_depth = 0
    in_string = False
    index = 0

    def blank(start: int, end: int) -> None:
        for position in range(start, end):
            if output[position] != "\n":
                output[position] = " "

    while index < len(text):
        pair = text[index : index + 2]
        if comment_depth:
            if pair == "(*":
                blank(index, index + 2)
                comment_depth += 1
                index += 2
            elif pair == "*)":
                blank(index, index + 2)
                comment_depth -= 1
                index += 2
            else:
                blank(index, index + 1)
                index += 1
        elif in_string:
            if text[index] == "\\":
                blank(index, min(index + 2, len(text)))
                index += 2
            elif text[index] == '"':
                blank(index, index + 1)
                in_string = False
                index += 1
            else:
                blank(index, index + 1)
                index += 1
        elif pair == "(*":
            blank(index, index + 2)
            comment_depth = 1
            index += 2
        elif text[index] == '"':
            blank(index, index + 1)
            in_string = True
            index += 1
        else:
            index += 1
    if comment_depth:
        raise ValueError("unterminated Standard ML comment")
    if in_string:
        raise ValueError("unterminated Standard ML string")
    return "".join(output)


def _shared_ml_family_reference_violations(
    proof_root: Path, authored_sources: tuple[Path, ...]
) -> tuple[str, ...]:
    """Catch references to the currently known Comma-owned ML structures.

    This is deliberately a narrow lexical audit for registered structure names,
    not a claim that arbitrary Standard ML references are fully resolved.
    Comments and strings are removed before checking qualified identifiers.
    """
    shared_root = proof_root / "shared"
    if not shared_root.is_dir():
        return ()
    violations: list[str] = []
    for path in sorted(
        source
        for source in authored_sources
        if source.suffix.lower() == ".ml"
        and source.resolve().is_relative_to(shared_root.resolve())
    ):
        code = _mask_ml_comments_and_strings(path.read_text(encoding="utf-8"))
        relative = path.relative_to(proof_root.parent.parent).as_posix()
        for structure in sorted(_KNOWN_FAMILY_ML_STRUCTURES):
            reference = re.compile(rf"(?<![A-Za-z0-9_']){re.escape(structure)}\s*\.")
            for match in reference.finditer(code):
                line = code.count("\n", 0, match.start()) + 1
                violations.append(
                    f"{relative}:{line}: shared ML references family-owned "
                    f"structure {structure}"
                )
    return tuple(violations)


def check_isabelle_resource_owner(root: Path, source: Path, target: Path) -> None:
    """Apply the same dependency direction to executable ML resources."""
    source_owner = _isabelle_owner(source.relative_to(root).parts[:-1])
    target_owner = _isabelle_owner(target.relative_to(root).parts[:-1])
    if (
        source_owner is not None
        and target_owner is not None
        and _owner_violation(source_owner, target_owner)
    ):
        raise ValueError(f"invalid ML resource ownership: {source} loads {target}")
    if _audit_dependency(source.relative_to(root), target.relative_to(root)):
        raise ValueError(f"release ML resource depends on audit owner: {target}")


def isabelle_ownership_violations(
    root: Path,
    *,
    sessions: tuple[Session, ...] | None = None,
    theory_headers: Mapping[Path, tuple[str, tuple[str, ...]]] | None = None,
    authored_sources: tuple[Path, ...] | None = None,
) -> tuple[str, ...]:
    """Audit session and theory edges under canonical Isabelle ownership roots.

    Every registered local session must have the
    ``shared/<domain>/<session>``, ``families/<family>/<session>``, or
    ``integration/<contract>/<session>`` shape.
    """
    root = Path(root).resolve()
    proof_root = root / "proofs" / "isabelle"
    if not proof_root.is_dir():
        return ()
    source_inventory = (
        authored_files(proof_root) if authored_sources is None else authored_sources
    )
    sessions = (
        sessions
        if sessions is not None
        else discover_sessions(proof_root, authored_sources=source_inventory)
    )
    violations: list[str] = []
    owners: dict[str, _IsabelleOwner] = {}
    for session in sessions:
        if not isinstance(session, Session):
            raise TypeError("Isabelle registry returned a foreign session record")
        owner = _isabelle_owner(session.directory.parts)
        parts = session.directory.parts
        canonical_depth = len(parts) == 3 or (len(parts) == 4 and parts[2] == "audit")
        if owner is None or not canonical_depth:
            violations.append(
                "proofs/isabelle: session "
                f"{session.name} has noncanonical ownership path "
                f"{session.directory.as_posix()}"
            )
        else:
            owners[session.name] = owner

    directories = {session.name: session.directory for session in sessions}
    for session in sessions:
        source_owner = owners.get(session.name)
        if source_owner is None:
            continue
        for target_name in (session.parent, *session.dependencies):
            target_directory = directories.get(target_name)
            if target_directory is not None and _audit_dependency(
                session.directory, target_directory
            ):
                violations.append(
                    f"release session {session.name} depends on audit session {target_name}"
                )
            target_owner = owners.get(target_name)
            if target_owner is None or not _owner_violation(source_owner, target_owner):
                continue
            violations.append(
                "proofs/isabelle/"
                f"{session.directory.as_posix()}: {source_owner.layer} session "
                f"{session.name} depends on {target_owner.layer} session {target_name}"
            )

    if theory_headers is None:
        headers = {}
        for path in sorted(source_inventory):
            resolved = path.resolve()
            if path.suffix == ".thy" and resolved.is_relative_to(proof_root):
                headers[resolved] = parse_theory_header(
                    path.read_text(encoding="utf-8"), path
                )
    else:
        headers = {
            (path if path.is_absolute() else proof_root / path).resolve(): value
            for path, value in theory_headers.items()
        }
    theories: dict[str, tuple[Path, _IsabelleOwner | None, tuple[str, ...]]] = {}
    theory_session_owners: dict[str, _IsabelleOwner] = {}
    for session in sessions:
        source_owner = owners.get(session.name)
        for reference in session.theories:
            target = (proof_root / session.directory / f"{reference}.thy").resolve()
            if not target.is_relative_to(proof_root):
                continue
            header = headers.get(target)
            if header is None:
                continue
            name, imports = header
            theories[name] = (target, source_owner, imports)
            if source_owner is not None:
                theory_session_owners[name] = source_owner

    for path, (name, imports) in sorted(
        headers.items(), key=lambda item: item[0].as_posix()
    ):
        if not path.is_relative_to(proof_root):
            continue
        if name not in theories:
            relative = path.relative_to(proof_root).parts
            theories[name] = (
                path.resolve(),
                _isabelle_owner(relative[:-1]),
                imports,
            )

    for name, (path, path_owner, imports) in sorted(theories.items()):
        source_owner = theory_session_owners.get(name, path_owner)
        if source_owner is None:
            continue
        for imported in imports:
            target_name = _theory_name(imported)
            target_record = theories.get(target_name)
            if target_record is None:
                continue
            if _audit_dependency(
                path.relative_to(proof_root), target_record[0].relative_to(proof_root)
            ):
                violations.append(
                    f"release theory {name} imports audit theory {target_name}"
                )
            target_owner = theory_session_owners.get(target_name, target_record[1])
            if target_owner is None or not _owner_violation(source_owner, target_owner):
                continue
            relative_path = path.relative_to(root).as_posix()
            violations.append(
                f"{relative_path}: {source_owner.layer} theory {name} imports "
                f"{target_owner.layer} theory {target_name}"
            )
    violations.extend(
        _shared_ml_family_reference_violations(proof_root, source_inventory)
    )
    return tuple(sorted(set(violations)))


def ownership_policy_violations(
    root: Path,
    *,
    parsed_sources: Mapping[Path, ast.Module] | None = None,
    sessions: tuple[Session, ...] | None = None,
    theory_headers: Mapping[Path, tuple[str, tuple[str, ...]]] | None = None,
    authored_sources: tuple[Path, ...] | None = None,
) -> tuple[str, ...]:
    """Return all Python and Isabelle ownership dependency violations."""
    return tuple(
        sorted(
            (
                *python_ownership_violations(root, parsed_sources=parsed_sources),
                *isabelle_ownership_violations(
                    root,
                    sessions=sessions,
                    theory_headers=theory_headers,
                    authored_sources=authored_sources,
                ),
            )
        )
    )


__all__ = [
    "isabelle_ownership_violations",
    "ownership_policy_violations",
    "python_ownership_violations",
]
