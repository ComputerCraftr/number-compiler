"""Build and validate the Isabelle proof inventory from authored sources."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import TypeGuard

from devtools.checks.isabelle_oracle_audit import (
    audited_theorems,
    declared_oracle_audit_bundles,
    validate_bundle_members,
)
from devtools.checks.isabelle_registry import discover_sessions, root_files
from devtools.checks.isabelle_source_analysis import (
    IsabelleAnalysis,
    IsabelleDeclaration,
    analysis_report,
    analyze_isabelle_source,
    extract_isabelle_declarations,
)
from devtools.checks.isabelle_syntax import (
    Session,
    executable_text,
    first_documentation_scope,
    global_simp_registrations,
    mask_comments,
    navigation_text,
    parse_theory_header,
    session_dependency_closure,
    unquoted_matches,
    unquoted_numeric_case_facts,
)
from devtools.checks.ownership_policy import (
    check_isabelle_resource_owner,
    isabelle_ownership_violations,
)
from devtools.checks.source_discovery import authored_files
from devtools.paths import isabelle_root, repository_root
from number_compiler.arithmetic.contracts.input_validation import string_keyed_mapping

ROOT = repository_root()
ISABELLE = isabelle_root(ROOT)

_ML_FILE_COMMAND = re.compile(r"(?m)^[ \t]*ML_file\b")
_ML_FILE_ARGUMENT = re.compile(
    r"""^[ \t]*(?:"((?:\\.|[^"\\])*)"|([^ \t\r\n]+))[ \t]*$"""
)

# These are active release contracts, not a repository-wide list of retired
# theories. Audit-only sessions may keep the old compiler as a differential
# oracle; only resources reachable from these production roots are gated.
_COMMA_RELEASE_SESSION_ROOTS = (
    "Comma_Semantic_B1_Instance",
    "Comma_Semantic_Future_Instance",
)

# This intentionally bounded source check describes the expensive ownership
# shape, not particular resource filenames. It is not an ML parser or a proof
# of reachability inside ML control flow; the theory/session closure below
# supplies the reachability boundary.
_RECURSIVE_ENVIRONMENT_COMPILER = (
    re.compile(
        r"(?m)^\s*(?:fun|and)\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s+frame\s+memo\s+active\s+env\b"
    ),
    re.compile(r"\bval\s+cache_key\s*=\s*\(\s*key\s*,\s*canonical_env\s*\)"),
    re.compile(r"\bCompiler_Table\.lookup\s+\(!memo\)\s+cache_key\b"),
    re.compile(r"(?<!\w)#certify\s+certify_state\s+context\s+child_states\b"),
)


def _environment_compiler_findings(source: str) -> tuple[str, ...]:
    """Recognize the current recursive environment-certification operation.

    The check is deliberately structural and bounded. Resource names are not
    used as evidence, so renaming an ML file does not bypass it. Isabelle
    kernel builds remain the authority for theorem validity.
    """
    code = mask_comments(source)
    code = re.sub(r'"(?:\\.|[^"\\])*"', lambda match: " " * len(match.group()), code)
    for recursive_declaration in _RECURSIVE_ENVIRONMENT_COMPILER[0].finditer(code):
        function_name = recursive_declaration.group("name")
        recursive_call = re.search(
            rf"\b{re.escape(function_name)}\s+frame\s+memo\s+active\s+child_env\b",
            code,
        )
        if recursive_call is not None and all(
            pattern.search(code) is not None
            for pattern in _RECURSIVE_ENVIRONMENT_COMPILER[1:]
        ):
            return (
                "recursive environment-keyed action states are certified after child construction "
                "(bounded ML source signature)",
            )
    return ()


def comma_release_owner_audit(
    *,
    sessions: tuple[Session, ...],
    registered: dict[str, str],
    imports_by_theory: dict[str, tuple[str, ...]],
    ml_references: dict[Path, list[str]],
    ml_sources: dict[Path, str],
    repository: Path,
) -> dict[str, object]:
    """Report environment-compiler operations in production Comma closures.

    The graph is derived from current ROOT session edges, theory imports, and
    ML_file references. Audit-only sessions that are not dependencies of a
    release root are outside scope and may retain independent proof engines.
    A checkout with no Comma sessions (for example, an isolated unit fixture)
    receives a not-configured result rather than a false failure. All ML_file
    targets attached to reached theories are followed; nested or dynamic ML
    ``use`` paths are outside this bounded source audit.
    """
    by_name = {session.name: session for session in sessions}
    comma_sessions = tuple(
        session for session in sessions if "comma" in session.directory.parts
    )
    if not comma_sessions:
        return {
            "status": "NOT_CONFIGURED",
            "scope": "bounded source-derived session/theory/ML resource audit",
            "limitations": "follows theory ML_file targets; does not resolve nested or dynamic ML use paths",
            "roots": [],
            "violations": [],
        }

    violations: list[str] = []
    root_reports: list[dict[str, object]] = []
    missing_roots = [
        name for name in _COMMA_RELEASE_SESSION_ROOTS if name not in by_name
    ]
    if missing_roots:
        violations.extend(
            f"required production session is not registered: {name}"
            for name in missing_roots
        )

    for root_name in _COMMA_RELEASE_SESSION_ROOTS:
        if root_name not in by_name:
            continue
        reached_sessions = session_dependency_closure(sessions, (root_name,))
        session_theories = {
            theory for theory, owner in registered.items() if owner in reached_sessions
        }
        reached_theories: set[str] = set()
        for theory in session_theories:
            reached_theories.update(_theory_import_closure(theory, imports_by_theory))
        reached_resources = sorted(
            {
                resource
                for resource, theories in ml_references.items()
                if reached_theories.intersection(theories)
            }
        )
        root_findings: list[dict[str, str]] = []
        for resource in reached_resources:
            source = ml_sources.get(resource)
            findings: tuple[str, ...]
            if source is None:
                findings = (
                    "referenced ML_file resource is absent from the source snapshot",
                )
            else:
                findings = _environment_compiler_findings(source)
            for finding in findings:
                relative_resource = resource.relative_to(
                    repository.resolve()
                ).as_posix()
                rendered = f"{root_name}: {relative_resource}: {finding}"
                violations.append(rendered)
                root_findings.append(
                    {"resource": relative_resource, "finding": finding}
                )
        root_reports.append(
            {
                "root": root_name,
                "sessions": reached_sessions,
                "theories": tuple(sorted(reached_theories)),
                "ml_resources": tuple(
                    resource.relative_to(repository.resolve()).as_posix()
                    for resource in reached_resources
                ),
                "status": "FAIL" if root_findings or missing_roots else "PASS",
                "findings": root_findings,
            }
        )
    return {
        "status": "FAIL" if violations else "PASS",
        "scope": "bounded source-derived session/theory/ML resource audit; not ML semantic proof",
        "limitations": "follows theory ML_file targets; does not resolve nested or dynamic ML use paths",
        "roots": root_reports,
        "violations": tuple(violations),
    }


def _declaration_records(
    declarations: tuple[IsabelleDeclaration, ...],
) -> tuple[dict[str, object], ...]:
    """Render an already parsed lexical inventory for navigation output."""
    rows: list[dict[str, object]] = []
    for declaration in declarations:
        if declaration.command not in {"lemma", "theorem", "corollary"}:
            continue
        body = declaration.body.lstrip().removeprefix(declaration.name)
        proofs = unquoted_matches(re.compile(r"(?m)(?:^|\s)(?:by|proof)\s"), body)
        proof = proofs[0] if proofs else None
        statement = (
            body[: proof.start()] if proof is not None else body.split("\n\n", 1)[0]
        )
        rows.append(
            {
                "name": declaration.name,
                "line": declaration.line,
                "statement_and_assumptions": statement.strip(),
            }
        )
    return tuple(rows)


def declarations(text: str) -> tuple[dict[str, object], ...]:
    """Return lexical navigation declarations; Isabelle checks their meaning."""
    return _declaration_records(extract_isabelle_declarations(text))


def _object_list(value: object) -> TypeGuard[list[object]]:
    return type(value) is list


def ml_file_references(text: str, path: Path) -> tuple[str, ...]:
    """Read authored ``ML_file`` paths while ignoring quoted fake commands."""
    clean = navigation_text(text)
    references: list[str] = []
    for command in unquoted_matches(_ML_FILE_COMMAND, clean):
        line_end = clean.find("\n", command.start())
        if line_end < 0:
            line_end = len(clean)
        argument = _ML_FILE_ARGUMENT.fullmatch(clean[command.end() : line_end])
        if argument is None:
            raise ValueError(f"{path}: unsupported ML_file target")
        reference = argument.group(1) or argument.group(2)
        if not reference or "\\" in reference:
            raise ValueError(f"{path}: unsupported ML_file target")
        references.append(reference)
    return tuple(references)


def _theory_import_closure(
    theory: str, imports_by_theory: dict[str, tuple[str, ...]]
) -> set[str]:
    reached = {theory}
    pending = [theory]
    while pending:
        source = pending.pop()
        for imported in imports_by_theory[source]:
            target = Path(imported.split(".")[-1]).name
            if target in imports_by_theory and target not in reached:
                reached.add(target)
                pending.append(target)
    return reached


def build_index() -> dict[str, object]:
    authored_sources = authored_files(ISABELLE)
    sessions = discover_sessions(ISABELLE, authored_sources=authored_sources)
    source_texts: dict[str, str] = {}
    source_texts_by_path: dict[Path, str] = {}
    source_analyses: dict[Path, IsabelleAnalysis] = {}
    declared: dict[
        str, tuple[Path, tuple[str, ...], str, tuple[str, ...], tuple[str, ...]]
    ] = {}
    theory_paths = sorted(path for path in authored_sources if path.suffix == ".thy")
    for path in theory_paths:
        text = path.read_text()
        invalid_case_facts = unquoted_numeric_case_facts(text)
        if invalid_case_facts:
            raise ValueError(
                f"{path}: quote numeric case fact names at lines {invalid_case_facts}"
            )
        # One immutable analysis object serves the per-theory inventory and
        # whole-tree duplicate/unused analysis below. Keeping it local to this
        # build preserves freshness when an authored source changes.
        source_analysis = analyze_isabelle_source(text, path, include_duplicates=False)
        name, imports = parse_theory_header(text, path)
        dangerous = global_simp_registrations(text, "gcd_nat.simps")
        if dangerous:
            raise ValueError(
                f"{path}: recursive gcd rule globally registered as simp at "
                f"lines {dangerous}; use closed ground equations"
            )
        if name in declared:
            raise ValueError(f"duplicate theory declaration: {name}")
        source_texts[name] = text
        source_texts_by_path[path] = text
        source_analyses[path] = source_analysis
        declared[name] = (
            path,
            imports,
            first_documentation_scope(text),
            (),
            ml_file_references(text, path),
        )

    bundle_definitions: dict[str, tuple[str, tuple[str, ...]]] = {}
    theorem_owners: dict[str, list[str]] = {}
    for theory, (path, _, _, _, _) in declared.items():
        for declaration in source_analyses[path].declarations:
            if declaration.command in {"lemma", "theorem", "corollary", "proposition"}:
                theorem_owners.setdefault(declaration.name, []).append(theory)
        for bundle_name, members in declared_oracle_audit_bundles(source_texts[theory]):
            if bundle_name in bundle_definitions:
                raise ValueError(
                    f"duplicate oracle audit bundle declaration: {bundle_name}"
                )
            bundle_definitions[bundle_name] = (theory, members)
    bundle_members = validate_bundle_members(
        bundle_definitions,
        {name: tuple(owners) for name, owners in theorem_owners.items()},
    )
    executed_bundle_refs: dict[str, set[str]] = {}
    for theory, (path, imports, scope, _, references) in tuple(declared.items()):
        bundle_refs: set[str] = set()
        try:
            audit = audited_theorems(
                source_texts[theory],
                bundle_members=bundle_members,
                executed_bundles=bundle_refs,
            )
        except ValueError as error:
            raise ValueError(f"{path}: {error}") from error
        declared[theory] = (path, imports, scope, audit, references)
        if bundle_refs:
            executed_bundle_refs[theory] = bundle_refs

    ownership_errors = isabelle_ownership_violations(
        ROOT,
        sessions=sessions,
        authored_sources=authored_sources,
        theory_headers={
            path: (name, imports) for name, (path, imports, _, _, _) in declared.items()
        },
    )
    if ownership_errors:
        raise ValueError("invalid proof ownership: " + "; ".join(ownership_errors))
    isabelle_path = ISABELLE.resolve()
    ml_references: dict[Path, list[str]] = {}
    for theory, (path, _, _, _, references) in declared.items():
        for reference in references:
            ml_target = (path.parent / reference).resolve()
            if not ml_target.is_relative_to(isabelle_path):
                raise ValueError(
                    f"{path}: ML_file target escapes theory root: {reference}"
                )
            if not ml_target.is_file():
                raise ValueError(f"{path}: missing ML_file target {ml_target}")
            check_isabelle_resource_owner(isabelle_path, path.resolve(), ml_target)
            ml_references.setdefault(ml_target, []).append(theory)

    authored_ml: set[Path] = set()
    ml_sources: dict[Path, str] = {}
    for path in authored_sources:
        if path.suffix.lower() not in {".ml", ".sml"}:
            continue
        ml_target = path.resolve()
        if not ml_target.is_relative_to(isabelle_path):
            raise ValueError(f"authored ML path escapes theory root: {path}")
        authored_ml.add(ml_target)
        ml_source = path.read_text()
        ml_sources[ml_target] = ml_source
        # Reuse this exact source snapshot for the whole-tree parser below.
        source_texts_by_path[ml_target] = ml_source
    ml_paths = sorted(authored_ml | set(ml_references))
    ml_entries = [
        {
            "path": path.relative_to(ROOT).as_posix(),
            "referenced_by": tuple(sorted(ml_references.get(path, []))),
        }
        for path in ml_paths
    ]

    canonical_session_dirs: dict[Path, str] = {}
    for session in sessions:
        session_path = (isabelle_path / session.directory).resolve()
        if not session_path.is_relative_to(isabelle_path):
            raise ValueError(
                f"{session.name}: session directory escapes theory root: "
                f"{session.directory}"
            )
        previous = canonical_session_dirs.get(session_path)
        if previous is not None:
            raise ValueError(
                f"duplicate canonical Isabelle session directory {session_path}: "
                f"{previous} and {session.name}"
            )
        canonical_session_dirs[session_path] = session.name

    registered: dict[str, str] = {}
    declared_paths = {row[0].resolve(): name for name, row in declared.items()}
    for session in sessions:
        for reference in session.theories:
            path = (ISABELLE / session.directory / f"{reference}.thy").resolve()
            if not path.is_relative_to(ISABELLE.resolve()):
                raise ValueError(
                    f"{session.name}: theory path escapes theory root: {reference}"
                )
            if not path.is_file():
                raise ValueError(f"{session.name}: missing registered theory {path}")
            registered_name = declared_paths.get(path)
            if registered_name is None or registered_name != path.stem:
                raise ValueError(
                    f"{session.name}: theory declaration differs from file {path}"
                )
            if registered_name in registered:
                raise ValueError(
                    f"theory {registered_name} registered in {registered[registered_name]} and {session.name}"
                )
            registered[registered_name] = session.name

    reverse: dict[str, list[str]] = {name: [] for name in declared}
    for source, (_, imports, _, _, _) in declared.items():
        for imported in imports:
            target = Path(imported.split(".")[-1]).name
            if target in reverse:
                reverse[target].append(source)

    imports_by_theory = {name: row[1] for name, row in declared.items()}
    closure_roots = set(registered) | set(executed_bundle_refs)
    import_closures = {
        theory: _theory_import_closure(theory, imports_by_theory)
        for theory in closure_roots
    }
    reachable: set[str] = set()
    for root_theory in registered:
        reachable.update(import_closures[root_theory])

    unreachable = sorted(set(declared) - reachable)
    if unreachable:
        raise ValueError(f"unregistered and unreachable theories: {unreachable}")

    consumers_by_bundle: dict[str, set[str]] = {
        name: set() for name in bundle_definitions
    }
    for consumer, bundle_refs in executed_bundle_refs.items():
        for bundle_name in bundle_refs:
            owner = bundle_definitions[bundle_name][0]
            if owner not in import_closures[consumer]:
                raise ValueError(
                    f"oracle audit bundle {bundle_name} executed by {consumer}, "
                    f"which does not import its owner {owner}"
                )
            if consumer in registered:
                consumers_by_bundle[bundle_name].add(consumer)
    required_sessions_by_bundle: dict[str, set[str]] = {}
    for bundle_name, (owner, _) in bundle_definitions.items():
        owner_session = registered.get(owner)
        if owner_session is not None:
            required_sessions = {owner_session}
        else:
            owner_path = declared[owner][0].resolve()
            containing_sessions = tuple(
                (len(directory.parts), session_name)
                for directory, session_name in canonical_session_dirs.items()
                if owner_path.is_relative_to(directory)
            )
            if containing_sessions:
                deepest = max(depth for depth, _ in containing_sessions)
                required_sessions = {
                    session_name
                    for depth, session_name in containing_sessions
                    if depth == deepest
                }
            else:
                required_sessions = {
                    registered[root]
                    for root in registered
                    if owner in import_closures[root]
                }
        if not required_sessions:
            raise ValueError(
                f"oracle audit bundle {bundle_name} has no registered owning session"
            )
        required_sessions_by_bundle[bundle_name] = required_sessions
        missing_sessions = sorted(
            session
            for session in required_sessions
            if not any(
                registered.get(consumer) == session
                and owner in import_closures[consumer]
                for consumer in consumers_by_bundle[bundle_name]
            )
        )
        if missing_sessions:
            raise ValueError(
                f"oracle audit bundle {bundle_name} is not executed in its owning "
                f"registered session(s): {missing_sessions}"
            )

    valid_consumers_by_bundle = {
        bundle_name: {
            consumer
            for consumer in consumers
            if registered.get(consumer) in required_sessions_by_bundle[bundle_name]
        }
        for bundle_name, consumers in consumers_by_bundle.items()
    }

    delegated_theories = {
        bundle_definitions[bundle_name][0]
        for bundle_name, consumers in valid_consumers_by_bundle.items()
        if any(consumer != bundle_definitions[bundle_name][0] for consumer in consumers)
    }
    missing_audits = sorted(
        name
        for name in reachable
        if not declared[name][3] and name not in delegated_theories
    )
    if missing_audits:
        raise ValueError(
            f"reachable theories without an oracle audit: {missing_audits}"
        )
    comma_release_owner = comma_release_owner_audit(
        sessions=sessions,
        registered=registered,
        imports_by_theory=imports_by_theory,
        ml_references=ml_references,
        ml_sources=ml_sources,
        repository=ROOT,
    )
    entries: list[dict[str, object]] = []
    token_uses: dict[str, set[str]] = {}
    for theory, contents in source_texts.items():
        contents = executable_text(contents)
        for token in set(re.findall(r"[A-Za-z][A-Za-z0-9_']*", contents)):
            token_uses.setdefault(token, set()).add(theory)
    for name in sorted(declared):
        path, imports, scope, audit, _ = declared[name]
        text = source_texts[name]
        declarations = _declaration_records(source_analyses[path].declarations)
        uses: dict[str, tuple[str, ...]] = {}
        for row in declarations:
            theorem = str(row["name"])
            uses[theorem] = tuple(sorted(token_uses.get(theorem, set()) - {name}))
        entries.append(
            {
                "theory": name,
                "path": path.relative_to(ROOT).as_posix(),
                "session": registered.get(name),
                "imports": imports,
                "imported_by": sorted(reverse[name]),
                "oracle_audit_theorems": audit,
                "delegated_oracle_audit_bundles": tuple(
                    sorted(
                        bundle_name
                        for bundle_name, (owner, _) in bundle_definitions.items()
                        if owner == name
                    )
                ),
                "scope": scope,
                "declarations": declarations,
                "lexical_uses_including_ML_and_attributes": uses,
                "verification_command": (
                    ".venv/bin/python -m devtools.checks.release --suite proofs "
                    f"--session {registered[name]}"
                    if name in registered
                    else "build an importing session"
                ),
            }
        )
    return {
        "schema_version": 2,
        "root": "proofs/isabelle",
        "registrations": [
            path.relative_to(ROOT).as_posix()
            for path in root_files(ISABELLE, authored_sources=authored_sources)
        ],
        "ml_files": ml_entries,
        "source_analysis": analysis_report(
            ISABELLE,
            source_texts_by_path,
            source_analyses,
            authored_sources,
        ),
        "sessions": [
            {
                "session": session.name,
                "directory": session.directory.as_posix(),
                "audit_only": "audit" in session.directory.parts,
                "parent": session.parent,
                "dependencies": session.dependencies,
                "theories": session.theories,
            }
            for session in sessions
        ],
        "comma_release_owner": comma_release_owner,
        "theories": entries,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json",
        type=Path,
        help="write the complete generated index; validation always runs",
    )
    parser.add_argument(
        "--require-comma-release-owner",
        action="store_true",
        help="fail unless B1 and future production closures avoid environment-compiled actions",
    )
    options = parser.parse_args()
    index = build_index()
    if options.json is not None:
        options.json.write_text(json.dumps(index, indent=2) + "\n")
    sessions = index["sessions"]
    theories = index["theories"]
    if not _object_list(sessions) or not _object_list(theories):
        raise TypeError("proof index collections have invalid types")
    comma_owner = string_keyed_mapping(index["comma_release_owner"])
    if comma_owner is None:
        raise TypeError("Comma release-owner audit has an invalid type")
    comma_status = comma_owner.get("status")
    required_gate_failed = (
        options.require_comma_release_owner and comma_status != "PASS"
    )
    print(
        json.dumps(
            {
                "status": "FAIL" if required_gate_failed else "PASS",
                "comma_release_owner": comma_status,
                "sessions": len(sessions),
                "theories": len(theories),
                "output": None if options.json is None else str(options.json),
            },
            sort_keys=True,
        )
    )
    if required_gate_failed:
        return 1
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
