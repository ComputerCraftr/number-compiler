"""Parse executed theorem-oracle audits and delegated theorem bundles."""

from __future__ import annotations

import re

from devtools.checks.isabelle_syntax import (
    executable_text,
    ml_cartouches,
    navigation_text,
    unquoted_matches,
)

_BUNDLE_NAME = re.compile(r"[A-Za-z][A-Za-z0-9_'.]*_oracle_audit_bundle\Z")
_COMMAND_START = re.compile(
    r"(?m)^[ \t]*(?:theory|imports|begin|end|lemma|theorem|corollary|"
    r"proposition|schematic_goal|definition|fun|function|primrec|"
    r"abbreviation|lemmas|ML(?:_val|_prf|_file)?|local_setup|setup|"
    r"declare|context|locale|interpretation|instantiation|datatype|"
    r"inductive|record|section|subsection|text(?:_raw)?)\b"
)
_LEMMAS_START = re.compile(r"(?m)^[ \t]*lemmas\b")


def _executed_ml_structure(
    source: str,
) -> tuple[tuple[tuple[int, int], ...], frozenset[int]]:
    """Return ML source segments separated by executed top-level semicolons.

    Delimiter and ML block tracking keeps separators inside lists, calls, and
    ``let``/``local``/``struct``/``sig`` bodies from looking like top-level
    evaluation. This intentionally recognizes only the small structural
    subset needed to distinguish unit calls from delayed expressions.
    """
    segments: list[tuple[int, int]] = []
    bindings: set[int] = set()
    start = 0
    delimiters: list[str] = []
    blocks: list[str] = []
    matching = {")": "(", "]": "[", "}": "{"}
    offset = 0
    while offset < len(source):
        char = source[offset]
        if char.isalpha() or char == "_":
            end = offset + 1
            while end < len(source) and (source[end].isalnum() or source[end] in "_.'"):
                end += 1
            word = source[offset:end]
            if not delimiters:
                if word == "val" and not blocks:
                    bindings.add(offset)
                if word in {"let", "local", "struct", "sig"}:
                    blocks.append(word)
                elif word == "end" and blocks:
                    blocks.pop()
            offset = end
            continue
        if char in "([{":
            delimiters.append(char)
        elif char in matching:
            if delimiters and delimiters[-1] == matching[char]:
                delimiters.pop()
        elif char == ";" and not delimiters and not blocks:
            segments.append((start, offset))
            start = offset + 1
        offset += 1
    segments.append((start, len(source)))
    return tuple(segments), frozenset(bindings)


def audited_theorems(
    text: str,
    *,
    bundle_members: dict[str, tuple[str, ...]] | None = None,
    executed_bundles: set[str] | None = None,
) -> tuple[str, ...]:
    names: list[str] = []
    clean = executable_text(text)
    for block in ml_cartouches(clean):
        block = re.sub(r'"(?:\\.|[^"\\])*"', '""', block)

        def names_from_body(body: str) -> tuple[str, ...]:
            body = body.strip()
            if (
                not body
                or re.fullmatch(
                    r"[A-Za-z][A-Za-z0-9_'.]*(?:\s+[A-Za-z][A-Za-z0-9_'.]*)*",
                    body,
                )
                is None
            ):
                raise ValueError(
                    "require_native_clean antiquotation is not a closed "
                    "theorem-name list"
                )
            return tuple(body.split())

        def names_from_antiquotation(expression: str) -> tuple[str, ...] | None:
            match = re.fullmatch(r"@\{thms?\s+(.*?)\}", expression, re.DOTALL)
            if match is None:
                return None
            return names_from_body(match.group(1))

        def resolve_native_argument(
            expression: str, bound_theorems: dict[str, str]
        ) -> tuple[str, ...]:
            expression = expression.strip()
            direct = names_from_antiquotation(expression)
            if direct is not None:
                if not direct:
                    raise ValueError("require_native_clean theorem list is empty")
                return direct
            if re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*", expression):
                bound = bound_theorems.get(expression)
                resolved = None if bound is None else names_from_body(bound)
                if resolved:
                    return resolved
                raise ValueError(
                    "require_native_clean theorem variable is not a closed "
                    "thm/thms antiquotation"
                )
            if expression.startswith("[") and expression.endswith("]"):
                contents = expression[1:-1]
                token_pattern = re.compile(
                    r"@\{thms?\s+.*?\}|[A-Za-z][A-Za-z0-9_']*", re.DOTALL
                )
                tokens = tuple(token_pattern.finditer(contents))
                remainder = token_pattern.sub("", contents)
                if not re.fullmatch(r"[\s,]*", remainder):
                    raise ValueError("require_native_clean list has unsupported syntax")
                if any(
                    not token.group(0).startswith("@{")
                    and token.group(0) not in bound_theorems
                    for token in tokens
                ):
                    raise ValueError(
                        "require_native_clean list contains an unresolved "
                        "theorem variable"
                    )
                resolved_names: list[str] = []
                for token in tokens:
                    item = token.group(0)
                    if item.startswith("@{"):
                        item_names = names_from_antiquotation(item)
                        if item_names is None:
                            raise ValueError(
                                "require_native_clean list has invalid "
                                "theorem antiquotation"
                            )
                    else:
                        item_names = names_from_body(bound_theorems[item])
                    resolved_names.extend(item_names)
                if resolved_names:
                    return tuple(resolved_names)
            raise ValueError("unsupported require_native_clean theorem argument")

        top_level_segments, executed_bindings = _executed_ml_structure(block)
        binding_assignment = re.compile(r"\bval\s+([A-Za-z_][A-Za-z0-9_']*|_)\s*=")
        binding_assignments = tuple(
            match
            for match in binding_assignment.finditer(block)
            if match.start() in executed_bindings
        )

        def theorem_bindings_before(
            offset: int,
            assignments: tuple[re.Match[str], ...] = binding_assignments,
            source: str = block,
        ) -> dict[str, str]:
            bound_theorems: dict[str, str] = {}
            for assignment in assignments:
                if assignment.start() >= offset:
                    break
                binding = assignment.group(1)
                if binding == "_":
                    continue
                # A later value shadows an earlier theorem list even when its
                # right-hand side is not a closed antiquotation.
                bound_theorems.pop(binding, None)
                antiquotation = re.match(
                    r"\s*@\{thms?\s+(.*?)\}",
                    source[assignment.end() :],
                    re.DOTALL,
                )
                if antiquotation is None:
                    continue
                trailing = source[assignment.end() + antiquotation.end() :]
                if re.match(r"\s*(?:;|(?=val\b)|$)", trailing):
                    bound_theorems[binding] = antiquotation.group(1)
            return bound_theorems

        pattern = (
            r"\bval\s+_\s*=\s*if\s+null\s*\(\s*Thm_Deps\.all_oracles\s+"
            r"(@\{thms?\s+.*?\}|[A-Za-z]\w*)\s*\)\s*then\s*\(\s*\)\s*else\s+error\b"
        )
        for audit in re.finditer(pattern, block, re.DOTALL):
            if audit.start() not in executed_bindings:
                continue
            argument = audit.group(1)
            direct = re.fullmatch(r"@\{thms?\s+(.*?)\}", argument, re.DOTALL)
            if direct is not None:
                names.extend(names_from_body(direct.group(1)))
            else:
                names.extend(
                    resolve_native_argument(
                        argument, theorem_bindings_before(audit.start())
                    )
                )

        authority_methods = {
            "require_expected_paths",
            "require_closed_expected_paths",
            "require_native_closed_expected_paths",
            "require_paths",
        }
        query_methods = {"names", "checked_names"}
        audit_methods = {
            *query_methods,
            "require_native_clean",
            "audit_fuel_free_global",
            *authority_methods,
        }
        audit_references = tuple(
            re.finditer(
                r"\bComma_Proof_Dependency_Audit\s*\.\s*"
                r"([A-Za-z][A-Za-z0-9_']*)\b",
                block,
            )
        )
        unknown_methods = sorted(
            {reference.group(1) for reference in audit_references} - audit_methods
        )
        if unknown_methods:
            raise ValueError(
                "unsupported Comma_Proof_Dependency_Audit methods: "
                + ", ".join(unknown_methods)
            )

        direct_call = re.compile(
            r"\bval\s+([A-Za-z_][A-Za-z0-9_']*|_)\s*=\s*"
            r"Comma_Proof_Dependency_Audit\s*\.\s*"
            r"([A-Za-z][A-Za-z0-9_']*)\b"
        )
        direct_calls = tuple(
            match
            for match in direct_call.finditer(block)
            if match.start() in executed_bindings
        )
        bare_call = re.compile(
            r"^\s*Comma_Proof_Dependency_Audit\s*\.\s*"
            r"([A-Za-z][A-Za-z0-9_']*)\b"
        )

        def executed_argument(
            method: str,
            rest: str,
            offset: int,
            *,
            bare: bool,
            path_methods: frozenset[str] = frozenset(authority_methods),
        ) -> tuple[str, ...] | None:
            context_and_label = re.match(r'\s+@\{context\}\s+""\s+', rest)
            tail = r"\s*\Z" if bare else r"\s*(?:;\s*)?(?=val\b|$)"
            if context_and_label is None:
                # Merely retaining a function reference executes no audit.
                if re.match(tail, rest):
                    return None
                raise ValueError(f"unsupported {method} invocation syntax or arguments")
            argument_text = rest[context_and_label.end() :]
            if method in path_methods:
                authorities = re.match(r'\[\s*""(?:\s*,\s*"")*\s*\]\s+', argument_text)
                if authorities is None:
                    raise ValueError(f"unsupported {method} authority list")
                argument_text = argument_text[authorities.end() :]
            argument = re.match(
                r"(?:@\{thms?\s+.*?\}|\[[^\]]*\]|"
                r"[A-Za-z][A-Za-z0-9_']*)",
                argument_text,
                re.DOTALL,
            )
            if argument is None:
                raise ValueError(f"unsupported {method} theorem argument")
            if re.match(tail, argument_text[argument.end() :]) is None:
                raise ValueError(f"unsupported trailing arguments to {method}")
            return resolve_native_argument(
                argument.group(0), theorem_bindings_before(offset)
            )

        bare_call_offsets: set[int] = set()
        for start, end in top_level_segments:
            segment = block[start:end]
            call = bare_call.match(segment)
            if call is None:
                continue
            method = call.group(1)
            reference_offset = (
                start
                + call.start()
                + call.group(0).find("Comma_Proof_Dependency_Audit")
            )
            bare_call_offsets.add(reference_offset)
            if method in query_methods:
                continue
            resolved = executed_argument(
                method, segment[call.end() :], start + call.start(), bare=True
            )
            if resolved is not None:
                names.extend(resolved)

        captured_call = re.compile(
            r"Exn\.capture\s*\(\s*fn\s*\(\s*\)\s*=>\s*"
            r"Comma_Proof_Dependency_Audit\.(?:require_native_clean|"
            r"audit_fuel_free_global|require_expected_paths|"
            r"require_closed_expected_paths|require_native_closed_expected_paths|"
            r"require_paths)\b",
            re.DOTALL,
        )
        captured_spans = tuple(match.span() for match in captured_call.finditer(block))
        direct_reference_offsets = {
            match.start(0) + match.group(0).find("Comma_Proof_Dependency_Audit")
            for match in direct_calls
        }
        direct_reference_offsets.update(bare_call_offsets)
        for reference in audit_references:
            if reference.start() in direct_reference_offsets:
                continue
            if any(start <= reference.start() < end for start, end in captured_spans):
                continue
            raise ValueError("unsupported Comma_Proof_Dependency_Audit invocation form")

        for call in direct_calls:
            binding, method = call.groups()
            if method in query_methods:
                continue
            resolved = executed_argument(
                method, block[call.end() :], call.start(), bare=False
            )
            if resolved is None:
                continue
            if binding != "_":
                raise ValueError(
                    f"executed {method} call is not a release audit binding"
                )
            names.extend(resolved)
    expanded: list[str] = []
    bundles = bundle_members or {}
    for name in names:
        members = bundles.get(name)
        if members is None:
            if name.endswith("_oracle_audit_bundle"):
                raise ValueError(
                    f"executed reference to undeclared oracle audit bundle: {name}"
                )
            expanded.append(name)
        else:
            if executed_bundles is not None:
                executed_bundles.add(name)
            expanded.extend(members)
    return tuple(dict.fromkeys(expanded))


def declared_oracle_audit_bundles(text: str) -> tuple[tuple[str, tuple[str, ...]], ...]:
    """Read strict top-level ``lemmas *_oracle_audit_bundle = ...`` declarations."""
    clean = navigation_text(text)
    command_starts = unquoted_matches(_COMMAND_START, clean)
    lemmas_starts = unquoted_matches(_LEMMAS_START, clean)
    bundles: list[tuple[str, tuple[str, ...]]] = []
    for command in lemmas_starts:
        next_boundary = next(
            (item.start() for item in command_starts if item.start() > command.start()),
            len(clean),
        )
        body = clean[command.start() : next_boundary]
        header = re.match(
            r"(?m)^[ \t]*lemmas[ \t]+(?P<name>[A-Za-z][A-Za-z0-9_'.]*)(?P<rest>.*)",
            body,
            re.DOTALL,
        )
        if header is None:
            malformed_name = re.search(
                r"[A-Za-z][A-Za-z0-9_'.]*_oracle_audit_bundle\b", body
            )
            if malformed_name is not None:
                raise ValueError(
                    "malformed oracle audit bundle declaration: "
                    + malformed_name.group(0)
                )
            continue
        name = header.group("name")
        if not name.endswith("_oracle_audit_bundle"):
            malformed_name = re.search(
                r"[A-Za-z][A-Za-z0-9_'.]*_oracle_audit_bundle\b", body
            )
            if malformed_name is not None:
                raise ValueError(
                    "malformed oracle audit bundle declaration: "
                    + malformed_name.group(0)
                )
            continue
        declaration = header.group("rest")
        match = re.fullmatch(r"[ \t]*=[ \t]*(.*?)[ \t\r\n]*", declaration, re.DOTALL)
        if match is None:
            raise ValueError(f"malformed oracle audit bundle declaration: {name}")
        raw_members = match.group(1).strip()
        if (
            not raw_members
            or re.fullmatch(
                r"[A-Za-z][A-Za-z0-9_'.]*(?:\s+[A-Za-z][A-Za-z0-9_'.]*)*",
                raw_members,
            )
            is None
        ):
            raise ValueError(f"malformed oracle audit bundle member list: {name}")
        members = tuple(raw_members.split())
        if len(set(members)) != len(members):
            raise ValueError(f"duplicate theorem in oracle audit bundle: {name}")
        bundles.append((name, members))
    return tuple(bundles)


def validate_bundle_members(
    bundles: dict[str, tuple[str, tuple[str, ...]]],
    theorem_owners: dict[str, tuple[str, ...]],
) -> dict[str, tuple[str, ...]]:
    """Reject missing, ambiguous, cross-owner, and cyclic bundle claims."""
    members_by_name: dict[str, tuple[str, ...]] = {}
    for name, (owner, members) in bundles.items():
        if _BUNDLE_NAME.fullmatch(name) is None or not members:
            raise ValueError(f"invalid oracle audit bundle declaration: {name}")
        if name in theorem_owners:
            raise ValueError(f"ambiguous oracle audit bundle name: {name}")
        for member in members:
            if member in bundles:
                raise ValueError(
                    f"cyclic oracle audit bundle reference: {name} -> {member}"
                )
            owners = theorem_owners.get(member, ())
            if len(owners) != 1:
                issue = "ambiguous" if owners else "missing"
                raise ValueError(
                    f"{issue} theorem in oracle audit bundle {name}: {member}"
                )
            if owners[0] != owner:
                raise ValueError(
                    f"foreign theorem in oracle audit bundle {name}: {member}"
                )
        members_by_name[name] = members
    return members_by_name
