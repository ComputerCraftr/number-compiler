"""Conservative reference evidence for Isabelle and embedded Standard ML.

The analyzer records lexical references and uncertain theorem lookups without
claiming that a name is semantically unused. This module owns the lexical
rules so per-source and tree reports consume the same evidence.
"""

from __future__ import annotations

import re
from collections import Counter
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import Protocol

from devtools.checks.isabelle_syntax import (
    dynamic_cartouche_spans,
    executable_text,
    mask_comments,
)

_IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
_ANTIQUOTE_RE = re.compile(
    r"@\{\s*(?:thm|lemma|term|const|prop|attribute|fact)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
_ML_FACT_LOOKUP_RE = re.compile(
    r"\b(?:Proof_Context|Global_Theory)\."
    r"(?:get_thm|get_thms|get_fact|get_fact_single)\b"
)
_ML_FACT_LOOKUP_LITERAL_RE = re.compile(
    r"^\s+[A-Za-z_][A-Za-z0-9_'.]*\s+"
    r'"(?P<name>[A-Za-z_][A-Za-z0-9_\'.]*)"'
)


class DeclarationReference(Protocol):
    @property
    def name(self) -> str: ...

    @property
    def body(self) -> str: ...

    @property
    def ml(self) -> bool: ...


@dataclass(frozen=True)
class DynamicFactLookup:
    """A possibly indirect theorem lookup in executable ML."""

    path: str
    line: int
    name: str | None


@dataclass(frozen=True)
class SourceReferenceEvidence:
    """Lexical reference counts from one already-read authored source."""

    path: str
    mentioned_counts: tuple[tuple[str, int], ...]
    declaration_counts: tuple[tuple[str, int], ...]
    explicit_references: frozenset[str]
    dynamic_lookups: tuple[DynamicFactLookup, ...]


@dataclass(frozen=True)
class ReferenceEvidence:
    """Reference evidence from one source or a combined authored tree."""

    sources: tuple[SourceReferenceEvidence, ...]

    @property
    def dynamic_lookup_names(self) -> frozenset[str]:
        return frozenset(
            lookup.name
            for source in self.sources
            for lookup in source.dynamic_lookups
            if lookup.name is not None
        )

    @property
    def unresolved_dynamic_lookup(self) -> bool:
        return any(
            lookup.name is None
            for source in self.sources
            for lookup in source.dynamic_lookups
        )

    @property
    def dynamic_lookups(self) -> tuple[DynamicFactLookup, ...]:
        return tuple(
            lookup for source in self.sources for lookup in source.dynamic_lookups
        )

    def referenced_names(self, declarations: Iterable[str]) -> frozenset[str]:
        candidates = set(declarations)
        references: set[str] = set()
        for source in self.sources:
            mentions = dict(source.mentioned_counts)
            owned = dict(source.declaration_counts)
            references.update(
                name
                for name in mentions.keys() & candidates
                if mentions[name] > owned.get(name, 0)
            )
            references.update(source.explicit_references & candidates)
        return frozenset(references)


def combine_reference_evidence(
    evidence_items: Iterable[ReferenceEvidence],
) -> ReferenceEvidence:
    items = tuple(evidence_items)
    return ReferenceEvidence(tuple(source for item in items for source in item.sources))


def mask_ml_strings(text: str) -> str:
    """Mask Standard ML string contents while preserving offsets and quotes."""
    output = list(text)
    quoted = False
    escaped = False
    for index, char in enumerate(text):
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
            elif char != "\n":
                output[index] = " "
        elif char == '"':
            quoted = True
    if quoted:
        raise ValueError("unterminated ML string")
    return "".join(output)


def has_unsupported_antiquotation(text: str) -> bool:
    return bool(re.search(r"@\{\s*thms\b", text)) or (
        "@{" in text and not _ANTIQUOTE_RE.search(text)
    )


def _reference_counts(text: str) -> Counter[str]:
    counts: Counter[str] = Counter()
    for token in _IDENTIFIER_RE.findall(text):
        counts[token] += 1
        if "." in token:
            counts[token.rsplit(".", 1)[-1]] += 1
    return counts


def _declaration_reference_text(declaration: DeclarationReference) -> str:
    if declaration.ml:
        return mask_ml_strings(mask_comments(declaration.body))
    return declaration.body


def _dynamic_lookups_in_block(
    code: str,
    source_offset: int,
    text: str,
    path: Path,
) -> tuple[DynamicFactLookup, ...]:
    lookups: list[DynamicFactLookup] = []
    locator = mask_ml_strings(code)
    for match in _ML_FACT_LOOKUP_RE.finditer(locator):
        literal = _ML_FACT_LOOKUP_LITERAL_RE.match(code[match.end() :])
        name = None
        if literal is not None:
            name = literal.group("name").rsplit(".", 1)[-1]
        lookups.append(
            DynamicFactLookup(
                path=str(path),
                line=text.count("\n", 0, source_offset + match.start()) + 1,
                name=name,
            )
        )
    return tuple(lookups)


def analyze_references(
    text: str, path: Path, declarations: Iterable[DeclarationReference]
) -> ReferenceEvidence:
    """Collect lexical refs and typed uncertainty without rescanning callers."""
    clean = executable_text(text)
    lookups: list[DynamicFactLookup] = []
    if path.suffix.lower() in {".ml", ".sml"}:
        code = mask_comments(clean)
        reference_source = mask_ml_strings(code)
        lookups.extend(_dynamic_lookups_in_block(code, 0, text, path))
    else:
        output = list(clean)
        for start, end, body in dynamic_cartouche_spans(clean):
            body_start = clean.find(body, start, end)
            if body_start < 0:
                continue
            code = mask_comments(body)
            masked = mask_ml_strings(code)
            output[start:end] = [
                "\n" if char == "\n" else " " for char in clean[start:end]
            ]
            output[body_start : body_start + len(masked)] = masked
            lookups.extend(_dynamic_lookups_in_block(code, body_start, text, path))
        reference_source = "".join(output)
    counts = _reference_counts(reference_source)
    own_counts: Counter[str] = Counter()
    declaration_list = tuple(declarations)
    for declaration in declaration_list:
        own_counts[declaration.name] += max(
            1,
            _reference_counts(_declaration_reference_text(declaration)).get(
                declaration.name, 0
            ),
        )
    explicit_references = {
        match.group(1) for match in _ANTIQUOTE_RE.finditer(reference_source)
    }
    for match in re.finditer(
        r"(?m)^\s*(?:declare|lemmas|export_code|code_thms)\b([^\n]*)",
        reference_source,
    ):
        explicit_references.update(_IDENTIFIER_RE.findall(match.group(1)))

    return ReferenceEvidence(
        (
            SourceReferenceEvidence(
                path=str(path),
                mentioned_counts=tuple(counts.items()),
                declaration_counts=tuple(own_counts.items()),
                explicit_references=frozenset(explicit_references),
                dynamic_lookups=tuple(lookups),
            ),
        )
    )
