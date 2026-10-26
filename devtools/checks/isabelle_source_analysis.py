"""Conservative Isabelle/HOL and embedded-ML source analysis.

This module deliberately does not pretend to parse Isabelle's full grammar.  It
extracts only declarations that are unambiguous at command boundaries and
reports evidence (duplicates, possible unused declarations, and unknown
regions) rather than making a completeness claim.  Proofs with dynamic ML are
kept reviewable instead of being declared dead by a lexical scan.
"""

from __future__ import annotations

import hashlib
import re
from bisect import bisect_right
from collections import defaultdict
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from devtools.checks.isabelle_references import (
    ReferenceEvidence,
    analyze_references,
    combine_reference_evidence,
    has_unsupported_antiquotation,
    mask_ml_strings,
)
from devtools.checks.isabelle_syntax import (
    executable_text,
    mask_comments,
    ml_cartouche_spans,
    navigation_text,
    unquoted_matches,
)
from devtools.checks.source_discovery import authored_files

_COMMANDS = (
    "definition",
    "fun",
    "function",
    "primrec",
    "abbreviation",
    "lemma",
    "theorem",
    "corollary",
    "proposition",
    "schematic_goal",
)
_COMMAND_RE = re.compile(
    rf"(?m)^(?P<indent>[ \t]*)(?P<command>{'|'.join(_COMMANDS)})\b"
)
_BOUNDARY_RE = re.compile(
    r"(?m)^(?P<indent>[ \t]*)(?:declare|lemmas|ML(?:_val|_prf)?|"
    r"ML_file|local_setup|setup|end|context|locale|interpretation|"
    r"instantiation|datatype|inductive|record|class|section|subsection|"
    r"text|theory|bundle|hide|unbundle|definition|fun|function|primrec|"
    r"abbreviation|lemma|theorem|corollary|proposition|schematic_goal)\b"
)
_NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
_ATTR_RE = re.compile(r"\[([^\]]*)\]")
_QUOTED_RE = re.compile(r'"(?:\\.|[^"\\])*"')
_ML_FUN_RE = re.compile(
    r"(?m)^[ \t]*(?P<keyword>fun|and)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*(?P<args>[^=]*)="
)
_ML_BOUNDARY_RE = re.compile(
    r"(?m)^[ \t]*(?:fun|and|val|structure|signature|datatype|end|local|in)\b"
)
_ML_DYNAMIC_RE = re.compile(
    r"(?m)^\s*(?:ML(?:_val|_prf)?|ML_file|local_setup|setup|declaration|syntax)\b"
)
_TOKEN_RE = re.compile(
    r"\\<[A-Za-z_][A-Za-z0-9_]*>|"
    r'"(?:\\.|[^"\\])*"|'
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*|"
    r"\d+(?:\.\d+)?|"
    r"=>|<=|>=|~=|:=|::|==>|<=>|[^\s]"
)
_BINDER_TOKENS = {
    "\\<lambda>",
    "\\<forall>",
    "\\<exists>",
    "\\<And>",
}
_UNSUPPORTED_TERM_TOKENS = {"let", "case", "of", "if", "then", "else"}
_RESERVED = {
    "where",
    "if",
    "then",
    "else",
    "let",
    "in",
    "case",
    "of",
    "and",
    "for",
    "True",
    "False",
}


@dataclass(frozen=True)
class IsabelleDeclaration:
    path: str
    line: int
    command: str
    name: str
    body: str
    attributes: tuple[str, ...]
    exported: bool
    dynamic: bool
    ml: bool = False


@dataclass(frozen=True)
class IsabelleDuplicate:
    digest: str
    declarations: tuple[IsabelleDeclaration, ...]
    normalized_body: str


@dataclass(frozen=True)
class IsabelleUnusedCandidate:
    declaration: IsabelleDeclaration
    reason: str
    confidence: str


@dataclass(frozen=True)
class IsabelleUnknown:
    path: str
    line: int
    reason: str


@dataclass(frozen=True)
class IsabelleAnalysis:
    declarations: tuple[IsabelleDeclaration, ...]
    duplicates: tuple[IsabelleDuplicate, ...]
    unused_candidates: tuple[IsabelleUnusedCandidate, ...]
    unknown_references: tuple[IsabelleUnknown, ...]
    unsupported_constructs: tuple[IsabelleUnknown, ...]
    reference_evidence: ReferenceEvidence

    def as_dict(self) -> dict[str, Any]:
        return {
            "declarations": tuple(asdict(item) for item in self.declarations),
            "duplicates": tuple(asdict(item) for item in self.duplicates),
            "unused_candidates": tuple(asdict(item) for item in self.unused_candidates),
            "unknown_references": tuple(
                asdict(item) for item in self.unknown_references
            ),
            "unsupported_constructs": tuple(
                asdict(item) for item in self.unsupported_constructs
            ),
        }


def _line(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _quoted_terms(body: str) -> tuple[str, ...]:
    return tuple(match.group(0)[1:-1] for match in _QUOTED_RE.finditer(body))


def _tokens(term: str) -> list[str]:
    return [match.group(0) for match in _TOKEN_RE.finditer(term)]


def _is_local_name(token: str) -> bool:
    return (
        bool(_NAME_RE.fullmatch(token))
        and token not in _RESERVED
        and not token[0].isupper()
        and "." not in token
        and "'" not in token
    )


def _normalize_term(term: str, self_name: str) -> tuple[str, ...] | None:
    """Alpha-normalize a small term while preserving constants and literals.

    Isabelle terms with unusual syntax are skipped rather than guessed.  This
    is intentionally a structural comparison, not a theorem prover.
    """
    tokens = _tokens(term)
    if not tokens or "=" not in tokens:
        return None
    equals = tokens.index("=")
    lhs = tokens[:equals]
    if not lhs:
        return None
    if lhs[0] != self_name:
        # Qualified names or parenthesized equations are not safely classified.
        return None
    pattern = lhs[1:]
    simple = all(_is_local_name(token) for token in pattern)
    suc_pattern = (
        len(pattern) == 4
        and pattern[0] == "("
        and pattern[1] == "Suc"
        and _is_local_name(pattern[2])
        and pattern[3] == ")"
    )
    if (
        pattern
        and not simple
        and not suc_pattern
        and not all(token.isdigit() or token in {"(", ")", "Suc"} for token in pattern)
    ):
        return None
    parameter_names = [
        token for token in pattern if _is_local_name(token) and token not in _RESERVED
    ]
    parameter_names = list(dict.fromkeys(parameter_names))
    parameter_map = {name: f"$p{index}" for index, name in enumerate(parameter_names)}
    result: list[str] = ["<self>"]
    # Keep patterns and binders in the body; only names proven to be parameters
    # or lexically-bound variables are renamed.
    for token in lhs[1:]:
        result.append(parameter_map.get(token, token))

    active: list[tuple[str, str, int]] = []
    next_binder = 0
    depth = 0
    index = equals + 1
    while index < len(tokens):
        token = tokens[index]
        if token == "(":
            depth += 1
        elif token == ")":
            depth -= 1
            active = [item for item in active if item[2] <= depth]
        if token in _BINDER_TOKENS:
            result.append(token)
            cursor = index + 1
            while cursor < len(tokens) and tokens[cursor] in {"(", ","}:
                cursor += 1
            if (
                cursor >= len(tokens)
                or not _is_local_name(tokens[cursor])
                or cursor + 1 >= len(tokens)
                or tokens[cursor + 1] != "."
            ):
                return None
            binder = tokens[cursor]
            replacement = f"$b{next_binder}"
            next_binder += 1
            active.append((binder, replacement, depth))
            # Emit the declaration immediately; skip it in the normal branch.
            result.append(replacement)
            index = cursor + 1
            continue
        replacement = next(
            (mapped for name, mapped, _ in reversed(active) if name == token),
            parameter_map.get(token, "<self>" if token == self_name else token),
        )
        result.append(replacement)
        index += 1
    if depth != 0:
        return None
    return tuple(result)


def _nontrivial(normalized: tuple[str, ...], minimum: int = 8) -> bool:
    if len(normalized) < minimum:
        return False
    operators = sum(
        token in {"+", "-", "*", "/", "<", ">", "=", "and", "or", "@", "#"}
        for token in normalized
    )
    return operators >= 2 and normalized[-2:] != ("by", "simp")


def _declaration_name(block: str) -> str | None:
    formal = re.match(
        r"\s*\(\s*in\s+[A-Za-z_][A-Za-z0-9_'.]*\s*\)\s*"
        r"([A-Za-z_][A-Za-z0-9_'.]*)",
        block,
    )
    if formal is not None:
        return formal.group(1)
    match = re.match(r"\s*([A-Za-z_][A-Za-z0-9_'.]*)", block)
    return match.group(1) if match is not None else None


def _definition_declarations(text: str, path: Path) -> tuple[IsabelleDeclaration, ...]:
    if path.suffix.lower() in {".ml", ".sml"}:
        return ()
    clean = navigation_text(text)
    matches = unquoted_matches(_COMMAND_RE, clean)
    boundaries = tuple(match.start() for match in unquoted_matches(_BOUNDARY_RE, clean))
    declarations: list[IsabelleDeclaration] = []
    for match in matches:
        start = match.start()
        position = bisect_right(boundaries, start)
        end = boundaries[position] if position < len(boundaries) else len(clean)
        block = clean[match.end() : end]
        name = _declaration_name(block)
        if name is None:
            continue
        header = block[: block.find("where") if "where" in block else len(block)]
        attributes = tuple(
            item.strip()
            for group in _ATTR_RE.findall(header)
            for item in group.split(",")
        )
        command = match.group("command")
        exported = command in {"lemma", "theorem", "corollary", "proposition"} or bool(
            attributes
        )
        declarations.append(
            IsabelleDeclaration(
                path=str(path),
                line=_line(text, start),
                command=command,
                name=name,
                body=block,
                attributes=attributes,
                exported=exported,
                dynamic=False,
            )
        )
    return tuple(declarations)


def _line_indent(text: str, offset: int) -> int:
    line_start = text.rfind("\n", 0, offset) + 1
    line_end = line_start
    text_length = len(text)
    while line_end < text_length and text[line_end] in " \t":
        line_end += 1
    return line_end - line_start


def _ml_code(body: str) -> tuple[str, str]:
    comments = mask_comments(body)
    return comments, mask_ml_strings(comments)


def _ml_declarations(text: str, path: Path) -> tuple[IsabelleDeclaration, ...]:
    declarations: list[IsabelleDeclaration] = []
    cartouches = ml_cartouche_spans(executable_text(text))
    blocks = cartouches
    if not blocks and path.suffix.lower() in {".ml", ".sml"}:
        blocks = ((0, len(text), text),)
    for start, _end, body in blocks:
        code, locator = _ml_code(body)
        all_matches = tuple(
            match
            for match in _ML_FUN_RE.finditer(locator)
            if match.group("keyword") == "fun" or match.group("args").strip()
        )
        if not all_matches:
            continue
        base_indent = min(_line_indent(locator, match.start()) for match in all_matches)
        matches = tuple(
            match
            for match in all_matches
            if _line_indent(locator, match.start()) == base_indent
        )
        boundaries = tuple(
            match
            for match in _ML_BOUNDARY_RE.finditer(locator)
            if _line_indent(locator, match.start()) == base_indent
        )
        boundary_positions = tuple(boundary.start() for boundary in boundaries)
        for index, match in enumerate(matches):
            boundary_index = bisect_right(boundary_positions, match.start())
            body_end = (
                boundary_positions[boundary_index]
                if boundary_index < len(boundary_positions)
                else len(code)
            )
            block = code[match.end() : body_end]
            mutual_group = match.group("keyword") == "and" or (
                match.group("keyword") == "fun"
                and index + 1 < len(matches)
                and matches[index + 1].group("keyword") == "and"
            )
            declarations.append(
                IsabelleDeclaration(
                    path=str(path),
                    line=_line(text, start + match.start()),
                    command="ML mutual fun" if mutual_group else "ML fun",
                    name=match.group("name"),
                    body=match.group("args") + "=" + block,
                    attributes=(),
                    exported=False,
                    dynamic=True,
                    ml=True,
                )
            )
    return tuple(declarations)


def extract_isabelle_declarations(
    text: str, path: Path | str = "<memory>"
) -> tuple[IsabelleDeclaration, ...]:
    """Return the declarations in the supported lexical subset.

    Callers that need the canonical declaration inventory should use this
    function rather than maintaining another command regex.  The returned
    objects carry a ``dynamic`` flag when ML/setup may hide references.
    """
    source_path = Path(path)
    return (
        *_definition_declarations(text, source_path),
        *_ml_declarations(text, source_path),
    )


def _definition_equations(
    declaration: IsabelleDeclaration,
) -> tuple[tuple[str, ...], tuple[str, ...]] | None:
    where = unquoted_matches(re.compile(r"\bwhere\b"), declaration.body)
    if not where:
        return None
    return (
        _quoted_terms(declaration.body[: where[0].start()]),
        _quoted_terms(declaration.body[where[0].end() :]),
    )


def _normalized_body(declaration: IsabelleDeclaration) -> tuple[str, ...] | None:
    if declaration.ml:
        if declaration.command != "ML fun":
            return None
        # ML functions use the same token alpha-normalizer after making a
        # synthetic equation.  The function name is the self symbol.
        term = f"{declaration.name} {declaration.body}"
        if any(token in _UNSUPPORTED_TERM_TOKENS for token in _tokens(term)):
            return None
        normalized_ml = _normalize_term(term, declaration.name)
        return (
            normalized_ml
            if normalized_ml is not None and _nontrivial(normalized_ml, minimum=7)
            else None
        )
    if declaration.command not in {
        "definition",
        "fun",
        "function",
        "primrec",
        "abbreviation",
    }:
        return None
    equations = _definition_equations(declaration)
    if equations is None:
        return None
    signature, terms = equations
    if any(
        token in _UNSUPPORTED_TERM_TOKENS for term in terms for token in _tokens(term)
    ):
        return None
    normalized: list[str] = ["HOL", *signature]
    for term in terms:
        value = _normalize_term(term, declaration.name)
        if value is None:
            return None
        normalized.extend(("<equation>", *value))
    result = tuple(normalized)
    return result if _nontrivial(result) else None


def _unknowns(
    text: str,
    path: Path,
    reference_evidence: ReferenceEvidence,
) -> tuple[IsabelleUnknown, ...]:
    unknowns: list[IsabelleUnknown] = []
    clean = executable_text(text)
    for match in unquoted_matches(_ML_DYNAMIC_RE, clean):
        unknowns.append(
            IsabelleUnknown(
                path=str(path),
                line=_line(text, match.start()),
                reason="dynamic Isabelle/ML command; lexical references are incomplete",
            )
        )
    unknowns.extend(
        IsabelleUnknown(
            path=lookup.path,
            line=lookup.line,
            reason=(
                f"dynamic theorem lookup may reference {lookup.name!r}"
                if lookup.name is not None
                else "dynamic theorem lookup has a nonliteral name"
            ),
        )
        for lookup in reference_evidence.dynamic_lookups
    )
    if has_unsupported_antiquotation(clean):
        unknowns.append(
            IsabelleUnknown(
                path=str(path),
                line=1,
                reason="unsupported ML antiquotation shape",
            )
        )
    return tuple(unknowns)


def _unsupported(
    text: str, path: Path, declarations: tuple[IsabelleDeclaration, ...]
) -> tuple[IsabelleUnknown, ...]:
    findings: list[IsabelleUnknown] = []
    clean = executable_text(text)
    for match in unquoted_matches(
        re.compile(
            r"(?m)^\s*(?:ML_file|method_setup|parse_translation|"
            r"print_translation)\b"
        ),
        clean,
    ):
        findings.append(
            IsabelleUnknown(
                path=str(path),
                line=_line(text, match.start()),
                reason="dynamic or external Isabelle extension is outside lexical scope",
            )
        )
    for match in unquoted_matches(_COMMAND_RE, navigation_text(text)):
        if match.group("indent"):
            findings.append(
                IsabelleUnknown(
                    path=str(path),
                    line=_line(text, match.start()),
                    reason="indented/proof-local command scope is not modeled",
                )
            )
    for start, _end, body in ml_cartouche_spans(text):
        _code, locator = _ml_code(body)
        matches = tuple(_ML_FUN_RE.finditer(locator))
        if matches:
            base_indent = min(_line_indent(locator, match.start()) for match in matches)
            if any(
                _line_indent(locator, match.start()) != base_indent for match in matches
            ):
                findings.append(
                    IsabelleUnknown(
                        path=str(path),
                        line=_line(text, start),
                        reason="nested ML function scope is not modeled",
                    )
                )
        elif "fun " in body:
            findings.append(
                IsabelleUnknown(
                    path=str(path),
                    line=_line(text, start),
                    reason="ML function layout is not safely recognized",
                )
            )
    for declaration in declarations:
        if not declaration.ml:
            continue
        if declaration.command == "ML mutual fun":
            findings.append(
                IsabelleUnknown(
                    path=str(path),
                    line=declaration.line,
                    reason=(
                        "mutually recursive ML function group is inventoried, "
                        "but group-level equivalence is not modeled"
                    ),
                )
            )
            continue
        if (
            any(
                token in _UNSUPPORTED_TERM_TOKENS for token in _tokens(declaration.body)
            )
            or _normalize_term(
                f"{declaration.name} {declaration.body}", declaration.name
            )
            is None
        ):
            findings.append(
                IsabelleUnknown(
                    path=str(path),
                    line=declaration.line,
                    reason="ML binding or expression is outside the supported subset",
                )
            )
    for declaration in declarations:
        if declaration.ml:
            continue
        if declaration.command not in {
            "definition",
            "fun",
            "function",
            "primrec",
            "abbreviation",
        }:
            continue
        equations = _definition_equations(declaration)
        terms = equations[1] if equations is not None else ()
        if (
            equations is None
            or any(
                token in _UNSUPPORTED_TERM_TOKENS
                for term in terms
                for token in _tokens(term)
            )
            or any(_normalize_term(term, declaration.name) is None for term in terms)
        ):
            findings.append(
                IsabelleUnknown(
                    path=str(path),
                    line=declaration.line,
                    reason="HOL binding or equation is outside the supported subset",
                )
            )
    return tuple(findings)


def duplicate_groups(
    declarations: Iterable[IsabelleDeclaration],
) -> tuple[IsabelleDuplicate, ...]:
    groups: dict[tuple[str, ...], list[IsabelleDeclaration]] = defaultdict(list)
    for declaration in declarations:
        normalized = _normalized_body(declaration)
        if normalized is not None:
            groups[("ML" if declaration.ml else "HOL", *normalized)].append(declaration)
    result: list[IsabelleDuplicate] = []
    for normalized, members in groups.items():
        if len(members) < 2:
            continue
        rendered = " ".join(normalized)
        digest = hashlib.sha256(rendered.encode()).hexdigest()
        result.append(
            IsabelleDuplicate(
                digest=digest,
                declarations=tuple(members),
                normalized_body=rendered,
            )
        )
    return tuple(result)


def _unused_candidate_review(
    declaration: IsabelleDeclaration,
    dynamic_names: frozenset[str],
    unresolved_dynamic_name: bool,
    uncertain_context: bool,
) -> tuple[str, str]:
    theorem = declaration.command in {
        "lemma",
        "theorem",
        "corollary",
        "proposition",
    }
    if declaration.name in dynamic_names or (unresolved_dynamic_name and theorem):
        return "dynamic theorem lookup may reference this declaration", "dynamic-review"
    if declaration.exported:
        return "exported theorem has no lexical incoming reference", "exported-review"
    if declaration.ml or uncertain_context:
        return (
            "dynamic or unknown context; no lexical incoming reference",
            "dynamic-review",
        )
    return "no lexical reference outside its declaration", "review"


def _unused_candidate(
    declaration: IsabelleDeclaration,
    dynamic_names: frozenset[str],
    unresolved_dynamic_name: bool,
    uncertain_context: bool,
) -> IsabelleUnusedCandidate:
    reason, confidence = _unused_candidate_review(
        declaration, dynamic_names, unresolved_dynamic_name, uncertain_context
    )
    return IsabelleUnusedCandidate(declaration, reason, confidence)


def analyze_isabelle_source(
    text: str, path: Path | str = "<memory>", *, include_duplicates: bool = True
) -> IsabelleAnalysis:
    source_path = Path(path)
    declarations = extract_isabelle_declarations(text, source_path)
    reference_evidence = analyze_references(text, source_path, declarations)
    refs = reference_evidence.referenced_names(
        declaration.name for declaration in declarations
    )
    unknowns = _unknowns(text, source_path, reference_evidence)
    unsupported = _unsupported(text, source_path, declarations)
    dynamic_names = reference_evidence.dynamic_lookup_names
    unresolved_dynamic_name = reference_evidence.unresolved_dynamic_lookup
    candidates = tuple(
        _unused_candidate(
            declaration,
            dynamic_names,
            unresolved_dynamic_name,
            bool(unknowns),
        )
        for declaration in declarations
        if declaration.name not in refs
        and (
            not declaration.exported
            or (
                declaration.command in {"lemma", "theorem", "corollary", "proposition"}
                and not declaration.attributes
            )
        )
    )
    return IsabelleAnalysis(
        declarations=tuple(declarations),
        duplicates=duplicate_groups(declarations) if include_duplicates else (),
        unused_candidates=candidates,
        unknown_references=unknowns,
        unsupported_constructs=unsupported,
        reference_evidence=reference_evidence,
    )


def analyze_isabelle_tree(
    root: Path,
    source_texts: Mapping[Path, str] | None = None,
    source_analyses: Mapping[Path, IsabelleAnalysis] | None = None,
    source_paths: Sequence[Path] | None = None,
) -> IsabelleAnalysis:
    """Analyze one tree, reusing caller-owned parses from the same snapshot.

    The optional mappings are deliberately scoped to one caller invocation.
    They avoid reparsing a source that was already read and analyzed while
    assembling a larger inventory; no analysis survives this call.
    """
    declarations: list[IsabelleDeclaration] = []
    source_analyses_for_tree: list[IsabelleAnalysis] = []
    root = root.resolve()
    paths = authored_files(root) if source_paths is None else source_paths
    for path in sorted(
        path
        for path in paths
        if path.suffix.lower() in {".thy", ".ml", ".sml"}
        and path.resolve().is_relative_to(root)
    ):
        path = path.resolve()
        if any(part in {"results", ".git", "__pycache__"} for part in path.parts):
            continue
        cached = (
            source_analyses.get(path)
            if source_texts is not None
            and path in source_texts
            and source_analyses is not None
            else None
        )
        text = (
            source_texts[path]
            if source_texts is not None and path in source_texts
            else path.read_text()
        )
        analysis = (
            cached
            if cached is not None
            else analyze_isabelle_source(text, path, include_duplicates=False)
        )
        source_analyses_for_tree.append(analysis)
        declarations.extend(analysis.declarations)
    all_duplicates = duplicate_groups(declarations)
    names: dict[str, list[IsabelleDeclaration]] = defaultdict(list)
    for declaration in declarations:
        names[declaration.name].append(declaration)
    reference_evidence = combine_reference_evidence(
        analysis.reference_evidence for analysis in source_analyses_for_tree
    )
    references = reference_evidence.referenced_names(names)
    unknowns = [
        unknown
        for analysis in source_analyses_for_tree
        for unknown in analysis.unknown_references
    ]
    unsupported = [
        unknown
        for analysis in source_analyses_for_tree
        for unknown in analysis.unsupported_constructs
    ]
    unknown_paths = {item.path for item in (*unknowns, *unsupported)}
    dynamic_names = reference_evidence.dynamic_lookup_names
    unresolved_dynamic_name = reference_evidence.unresolved_dynamic_lookup
    candidates = tuple(
        _unused_candidate(
            declaration,
            dynamic_names,
            unresolved_dynamic_name,
            str(declaration.path) in unknown_paths,
        )
        for declaration in declarations
        if declaration.name not in references
        and len(names[declaration.name]) == 1
        and (
            not declaration.exported
            or (
                declaration.command in {"lemma", "theorem", "corollary", "proposition"}
                and not declaration.attributes
            )
        )
    )
    return IsabelleAnalysis(
        declarations=tuple(declarations),
        duplicates=all_duplicates,
        unused_candidates=candidates,
        unknown_references=tuple(unknowns),
        unsupported_constructs=tuple(unsupported),
        reference_evidence=reference_evidence,
    )


def analysis_report(
    root: Path,
    source_texts: Mapping[Path, str] | None = None,
    source_analyses: Mapping[Path, IsabelleAnalysis] | None = None,
    source_paths: Sequence[Path] | None = None,
) -> dict[str, Any]:
    """Return a compact JSON-ready report for policy and proof inventories."""
    analysis = analyze_isabelle_tree(root, source_texts, source_analyses, source_paths)
    return {
        "scope": {
            "flat_hol_equations": True,
            "flat_ml_functions": True,
            "alpha_normalization": "bound identifiers only",
            "semantic_equivalence": False,
            "dynamic_ml": "reported as unknown",
        },
        "declaration_count": len(analysis.declarations),
        "duplicate_count": len(analysis.duplicates),
        "duplicates": [
            {
                "digest": duplicate.digest,
                "declarations": [
                    {
                        "path": item.path,
                        "line": item.line,
                        "command": item.command,
                        "name": item.name,
                    }
                    for item in duplicate.declarations
                ],
            }
            for duplicate in analysis.duplicates
        ],
        "unused_candidate_count": len(analysis.unused_candidates),
        "unused_candidates": [
            {
                "path": item.declaration.path,
                "line": item.declaration.line,
                "command": item.declaration.command,
                "name": item.declaration.name,
                "reason": item.reason,
                "confidence": item.confidence,
            }
            for item in analysis.unused_candidates
        ],
        "unknown_count": len(analysis.unknown_references),
        "unknown_references": [asdict(item) for item in analysis.unknown_references],
        "unsupported_count": len(analysis.unsupported_constructs),
        "unsupported_constructs": [
            asdict(item) for item in analysis.unsupported_constructs
        ],
    }
