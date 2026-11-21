"""CLI renderers derived from the canonical family capability registry."""

from __future__ import annotations

from dataclasses import fields

from number_compiler.api.cli_types import PresentationOptions, QueryRequest
from number_compiler.api.family_registry import CAPABILITIES
from number_compiler.api.observation_types import (
    OptionSpec,
    OptionValueKind,
    OutputFormat,
    SelectorId,
    option_default,
)
from number_compiler.arithmetic.contracts.input_validation import is_exact_integer_tuple


def family_listing() -> tuple[str, ...]:
    """Return the canonical `--list-families` lines from registered metadata."""
    lines: list[str] = []
    for family, spec in CAPABILITIES.items():
        lines.append(
            f"{family}: --nth N ({spec.unit}); info: {', '.join(spec.nth_info)}"
        )
        for option in spec.view_options().values():
            lines.append(f"  {option.flag} {'|'.join(option.choices)}")
        lines.append("  --nth-power10 K (exact index 10^K, K >= 0)")
        if spec.event_query_type is not None:
            lines.append(
                "  --events E (accelerated_odd_events); info: "
                + ", ".join(spec.event_info)
            )
        if spec.palindrome_search:
            lines.append(
                f"  --{SelectorId.FIRST_PALINDROME.value} N (positive physical generations through N)"
            )
        if spec.verify_flag is not None:
            lines.append(f"  --{spec.verify_flag.replace('_', '-')} PATH")
    return tuple(lines)


def presentation_options() -> dict[str, OptionSpec]:
    """Derive shared CLI presentation flags from their typed-record defaults."""
    result: dict[str, OptionSpec] = {}
    for field in fields(PresentationOptions):
        if field.name == "index":
            continue
        default = option_default(field.default)
        kind = (
            OptionValueKind.BOOLEAN
            if type(default) is bool
            else OptionValueKind.INTEGER
        )
        choices: tuple[str, ...] = ()
        if field.name == "format":
            kind = OptionValueKind.CHOICE
            choices = tuple(value.value for value in OutputFormat)
        result[field.name] = OptionSpec(
            default,
            (),
            name=field.name,
            value_kind=kind,
            choices=choices,
        )
    max_index_bits = next(
        field for field in fields(QueryRequest) if field.name == "max_index_bits"
    )
    result["max_index_bits"] = OptionSpec(
        option_default(max_index_bits.default),
        (),
        name="max_index_bits",
    )
    return result


def option_argv(name: str, value: object) -> list[str]:
    """Render one canonical family/observer option for reproducible probes."""
    flag = name if name.startswith("--") else "--" + name.replace("_", "-")
    if isinstance(value, bool):
        return [flag] if value else []
    if is_exact_integer_tuple(value):
        return [flag + "=" + ",".join(str(item) for item in value)]
    return [flag, str(value)]


__all__ = ["family_listing", "option_argv", "presentation_options"]
