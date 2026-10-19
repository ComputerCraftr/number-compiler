"""Injection tests for typed border and registry source contracts."""

from __future__ import annotations

import ast
from pathlib import Path

from devtools.checks.border_registry_policy import border_registry_violations


def _parsed_sources(root: Path, files: dict[str, str]) -> dict[Path, ast.Module]:
    parsed: dict[Path, ast.Module] = {}
    for relative, source in files.items():
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        parsed[path] = ast.parse(source, filename=str(path))
    return parsed


def test_raw_strings_at_typed_macro_and_enum_boundaries_are_rejected(
    tmp_path: Path,
) -> None:
    sources = _parsed_sources(
        tmp_path,
        {
            "src/number_compiler/arithmetic/contracts/family_identity.py": (
                "from enum import StrEnum\n"
                "class FamilyId(StrEnum):\n    REVERSE_ADD = 'reverse-add'\n"
            ),
            "src/number_compiler/hashlife/interfaces/border_macros.py": (
                "from enum import Enum\n"
                "from number_compiler.arithmetic.contracts.family_identity import FamilyId\n"
                "class BorderMacroKind(Enum):\n    CYCLE = 'cycle'\n"
            ),
            "src/number_compiler/sequences/reverse_add/bad_catalogue.py": (
                "def bad():\n"
                "    family = FamilyId('reverse-add')\n"
                "    kind = BorderMacroKind('cycle')\n"
                "    return BorderMacroIdentity('reverse-add', kind, Signature())\n"
                "def ordinary_text():\n"
                "    return 'cycle'\n"
            ),
        },
    )

    assert border_registry_violations(tmp_path, sources) == (
        "src/number_compiler/sequences/reverse_add/bad_catalogue.py:2: FamilyId construction must use a typed member or an external parsed value",
        "src/number_compiler/sequences/reverse_add/bad_catalogue.py:3: BorderMacroKind construction must use a typed member or an external parsed value",
        "src/number_compiler/sequences/reverse_add/bad_catalogue.py:4: BorderMacroIdentity family must use a typed identifier",
    )


def test_duplicate_option_declarations_are_rejected_but_new_typed_options_are_allowed(
    tmp_path: Path,
) -> None:
    sources = _parsed_sources(
        tmp_path,
        {
            "src/number_compiler/api/family_registry.py": (
                "class FamilyId(StrEnum):\n    COLLATZ = 'collatz'\n"
                "_CAPABILITY_ENTRIES = {FamilyId.COLLATZ: FamilySpec()}\n"
                "CAPABILITIES = MappingProxyType(_CAPABILITY_ENTRIES)\n"
                "del _CAPABILITY_ENTRIES\n"
                "COMMON_OPTIONS = {'depth': OptionSpec(0, (), name='depth')}\n"
            ),
            "src/number_compiler/sequences/collatz/extra_options.py": (
                "options = (\n"
                "    ('depth', OptionSpec(1, (), name='depth')),\n"
                "    ('new_depth', OptionSpec(2, (), name='new_depth')),\n"
                "    ('new_depth', OptionSpec(3, (), name='new_depth')),\n"
                ")\n"
                "diagnostic = 'ordinary option discussion'\n"
            ),
        },
    )

    assert border_registry_violations(tmp_path, sources) == (
        "src/number_compiler/sequences/collatz/extra_options.py:2: option 'depth' duplicates a canonical registry declaration",
        "src/number_compiler/sequences/collatz/extra_options.py:3: option 'new_depth' is duplicated outside canonical owners",
        "src/number_compiler/sequences/collatz/extra_options.py:4: option 'new_depth' is duplicated outside canonical owners",
    )


def test_raw_and_aliased_family_dispatch_keys_are_rejected(
    tmp_path: Path,
) -> None:
    sources = _parsed_sources(
        tmp_path,
        {
            "src/number_compiler/api/family_registry.py": (
                "_CAPABILITY_ENTRIES = {\n"
                "    'collatz': FamilySpec(),\n"
                "    'collatz': FamilySpec(),\n"
                "}\n"
                "CAPABILITIES = MappingProxyType(_CAPABILITY_ENTRIES)\n"
                "del _CAPABILITY_ENTRIES\n"
            ),
            "src/number_compiler/api/dispatch.py": (
                "def dispatch(family):\n    return CAPABILITIES['collatz']\n"
            ),
        },
    )

    assert border_registry_violations(tmp_path, sources) == (
        "src/number_compiler/api/dispatch.py:2: family dispatch must index by FamilyId",
        "src/number_compiler/api/family_registry.py:2: CAPABILITIES keys must use FamilyId",
        "src/number_compiler/api/family_registry.py:3: CAPABILITIES keys must use FamilyId",
        "src/number_compiler/api/family_registry.py:3: duplicate family registry declaration",
    )
