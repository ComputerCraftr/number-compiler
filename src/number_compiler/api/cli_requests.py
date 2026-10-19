"""Family-first CLI parsing into typed execution and observation requests."""

from __future__ import annotations

import argparse
from collections.abc import Mapping

from number_compiler.api.cli_types import (
    IndexPresentation,
    ObservationOptions,
    PresentationOptions,
    QueryRequest,
)
from number_compiler.api.family_registry import (
    CAPABILITIES as _CAPABILITIES,
)
from number_compiler.api.family_registry import (
    FamilySpec,
)
from number_compiler.api.observation_types import (
    IndexEncoding,
    ObservationId,
    OptionValueKind,
    SelectorId,
    observation_id,
)
from number_compiler.api.observation_types import (
    OutputFormat as OutputFormatId,
)
from number_compiler.api.query_types import (
    ExecutionQuery,
    QueryOptionError,
)
from number_compiler.api.registry_cli import presentation_options
from number_compiler.arithmetic.contracts.family_identity import (
    FamilyId,
    family_id,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer


def cli_index_token(text: str) -> str:
    """Validate decimal syntax while deferring integer construction to admission."""
    digits = text[1:] if text and text[0] in "+-" else text
    if not digits or any(char < "0" or char > "9" for char in digits):
        raise argparse.ArgumentTypeError("expected an ASCII integer")
    digits = digits.lstrip("0") or "0"
    return "-" + digits if text.startswith("-") and digits != "0" else digits


def _index_product(left: int, right: int, max_bits: int) -> int:
    if left and right and left.bit_length() + right.bit_length() - 1 > max_bits:
        raise ValueError("index exceeds --max-index-bits")
    value = left * right
    if value.bit_length() > max_bits:
        raise ValueError("index exceeds --max-index-bits")
    return value


def bounded_index(token: str, max_bits: int) -> int:
    """Parse an explicit decimal index with bounded integer intermediates."""
    negative = token.startswith("-")
    digits = token[1:] if negative else token
    if 3 * (len(digits) - 1) >= max_bits:
        raise ValueError("index exceeds --max-index-bits")
    value = 0
    for start in range(0, len(digits), 9):
        chunk = digits[start : start + 9]
        value = _index_product(value, 10 ** len(chunk), max_bits) + int(chunk)
        if value.bit_length() > max_bits:
            raise ValueError("index exceeds --max-index-bits")
    return -value if negative else value


def power10_index(exponent: int, max_bits: int) -> int:
    """Construct 10**K by capped exponentiation, without decimal expansion."""
    require_integer(exponent, "--nth-power10", 0)
    if 3 * exponent >= max_bits:
        raise ValueError("index exceeds --max-index-bits")
    value, factor, remaining = 1, 10, exponent
    while remaining:
        if remaining & 1:
            value = _index_product(value, factor, max_bits)
        remaining >>= 1
        if remaining:
            factor = _index_product(factor, factor, max_bits)
    return value


def cli_integer(text: str) -> int:
    digits = text[1:] if text and text[0] in "+-" else text
    if not digits or any(char < "0" or char > "9" for char in digits):
        raise argparse.ArgumentTypeError("expected an ASCII integer")
    try:
        return int(text, 10)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("integer token exceeds parser budget") from exc


class UniqueValue(argparse.Action):
    def __call__(
        self,
        parser: argparse.ArgumentParser,
        namespace: argparse.Namespace,
        values: object,
        option_string: str | None = None,
    ) -> None:
        if self.nargs == 0:
            values = self.const
        specified: dict[str, object] = getattr(namespace, "_specified", {})
        if self.dest in specified and specified[self.dest] != values:
            parser.error(f"conflicting values for {option_string}")
        specified[self.dest] = values
        namespace._specified = specified
        setattr(namespace, self.dest, values)


def parser(
    *,
    demanded_family: FamilyId | None = None,
    registry: Mapping[FamilyId, FamilySpec] | None = None,
) -> argparse.ArgumentParser:
    """Register all names while constructing only the demanded family's actions."""
    capabilities = _CAPABILITIES if registry is None else registry
    if any(
        type(family) is not FamilyId or type(spec) is not FamilySpec
        for family, spec in capabilities.items()
    ):
        raise TypeError("family registry keys and values must use typed declarations")
    if demanded_family is not None and demanded_family not in capabilities:
        unknown_family = demanded_family.value
        raise ValueError(f"unknown demanded CLI family: {unknown_family}")
    selected_family = None if demanded_family is None else demanded_family.value
    command = argparse.ArgumentParser(
        prog="number-compiler",
        description="Exact family terms: number-compiler FAMILY --nth N [--info NAME].",
    )
    command.add_argument("--list-families", action="store_true")
    families = command.add_subparsers(dest="family")
    for family, spec in capabilities.items():
        family_name = family.value
        family_parser = families.add_parser(
            family_name,
            help=f"index unit: {spec.unit}",
            description=(
                spec.description
                or f"{family}: --nth uses {spec.unit}; term zero is the seed where applicable."
            )
            + (
                f" --events uses {spec.event_unit}."
                if spec.event_query_type is not None and spec.event_unit is not None
                else ""
            ),
        )
        if selected_family is not None and family_name != selected_family:
            continue
        _add_family_options(family_parser, spec)
    return command


def _add_family_options(command: argparse.ArgumentParser, spec: FamilySpec) -> None:
    selectors = command.add_mutually_exclusive_group(required=True)
    selectors.add_argument("--nth", type=cli_index_token, action=UniqueValue)
    selectors.add_argument(
        "--nth-power10",
        type=cli_index_token,
        action=UniqueValue,
        metavar="K",
        help="exact term index 10^K, with K >= 0",
    )
    if spec.event_query_type is not None:
        selectors.add_argument(
            "--events",
            type=cli_index_token,
            action=UniqueValue,
            help="accelerated odd events; information-only query",
        )
    if spec.verify_flag is not None:
        selectors.add_argument(
            "--" + spec.verify_flag.replace("_", "-"),
            action=UniqueValue,
            metavar="PATH",
        )
    _add_information_option(command, spec)
    _add_presentation_options(command)
    for name, option in spec.parser_options().items():
        if not option.name:
            raise ValueError(f"registry option {name!r} has no canonical name")
        if option.value_kind is not OptionValueKind.INTEGER:
            if option.value_kind is OptionValueKind.BOOLEAN:
                command.add_argument(
                    option.flag,
                    dest=option.name,
                    action=UniqueValue,
                    nargs=0,
                    const=True,
                    default=option.default,
                    help=option.help,
                )
                continue
            if option.value_kind is OptionValueKind.CHOICE:
                command.add_argument(
                    option.flag,
                    dest=option.name,
                    choices=option.choices,
                    default=option.default,
                    action=UniqueValue,
                    help=option.help,
                )
                continue
            raise ValueError(f"unsupported parser value kind {option.value_kind!r}")
        command.add_argument(
            option.flag,
            dest=option.name,
            type=cli_integer,
            default=option.default,
            action=UniqueValue,
            help=option.help,
        )


def _add_information_option(command: argparse.ArgumentParser, spec: FamilySpec) -> None:
    supported = tuple(dict.fromkeys(item.identifier for item in spec.observation_specs))
    help_text = "requested information; repeat for multiple observations"
    if spec.event_info:
        help_text += (
            f"; --nth: {', '.join(spec.nth_info)}"
            f"; --events: {', '.join(spec.event_info)}"
        )
    command.add_argument(
        "--info", action="append", choices=supported, default=[], help=help_text
    )


def _add_presentation_options(command: argparse.ArgumentParser) -> None:
    for option in presentation_options().values():
        if option.value_kind is OptionValueKind.BOOLEAN:
            command.add_argument(
                option.flag,
                dest=option.name,
                action=UniqueValue,
                nargs=0,
                const=True,
                default=option.default,
                help=option.help,
            )
        elif option.value_kind is OptionValueKind.CHOICE:
            command.add_argument(
                option.flag,
                dest=option.name,
                choices=option.choices,
                default=option.default,
                action=UniqueValue,
                help=option.help,
            )
        elif option.value_kind is OptionValueKind.INTEGER:
            command.add_argument(
                option.flag,
                dest=option.name,
                type=cli_integer,
                default=option.default,
                action=UniqueValue,
                help=option.help,
            )
        else:
            raise ValueError(f"unsupported presentation option {option.value_kind!r}")


def parse_request(
    argv: list[str],
    *,
    registry: Mapping[FamilyId, FamilySpec] | None = None,
) -> QueryRequest | None:
    capabilities = _CAPABILITIES if registry is None else registry
    demanded_family: FamilyId | None = None
    if argv:
        try:
            candidate = family_id(argv[0])
        except ValueError:
            candidate = None
        if candidate in capabilities:
            demanded_family = candidate
    command = parser(demanded_family=demanded_family, registry=capabilities)
    args = command.parse_args(argv)
    if args.list_families:
        if args.family is not None:
            command.error("--list-families cannot be combined with a family query")
        return None
    if args.family is None:
        command.error(
            "choose a family and --nth N; use --list-families for available families"
        )
    return _request_from_args(args, capabilities)


def _request_from_args(
    args: argparse.Namespace,
    capabilities: Mapping[FamilyId, FamilySpec],
) -> QueryRequest:
    selected_family = family_id(args.family)
    spec = capabilities.get(selected_family)
    if spec is None:
        raise ValueError(f"unknown family: {args.family}")
    certificate = (
        None
        if spec.verify_flag is None
        else getattr(args, spec.verify_flag.replace("-", "_"), None)
    )
    max_index_bits = require_integer(args.max_index_bits, "--max-index-bits", 1)
    event_token = getattr(args, "events", None)
    event_count = (
        None if event_token is None else bounded_index(event_token, max_index_bits)
    )
    power10_token = getattr(args, "nth_power10", None)
    exponent = (
        None
        if power10_token is None
        else bounded_index(power10_token, max_index_bits.bit_length())
    )
    selector = (
        SelectorId.VERIFY
        if certificate is not None
        else SelectorId.EVENTS
        if event_count is not None
        else SelectorId.NTH
    )
    if selector is SelectorId.VERIFY:
        index = 0
    elif selector is SelectorId.EVENTS:
        if event_count is None:
            raise AssertionError("events selector lost its event count")
        index = event_count
    elif exponent is not None:
        index = power10_index(exponent, max_index_bits)
    else:
        index = bounded_index(args.nth, max_index_bits)
    execution = _execution_query(args, selector, index, certificate, spec)
    observations = _observation_query(args, selector, spec)
    presentation = PresentationOptions(
        index=IndexPresentation(IndexEncoding.POWER10, exponent)
        if exponent is not None
        else IndexPresentation(),
        format=OutputFormatId(args.format),
        output_base=args.output_base,
        max_output_bits=args.max_output_bits,
        no_value=args.no_value,
    )
    try:
        matrix = (
            spec.matrix.build(
                vars(args),
                trace=ObservationId.TEMPORAL_MATRIX_TRACE in observations.info,
            )
            if {
                ObservationId.TEMPORAL_MATRIX,
                ObservationId.TEMPORAL_MATRIX_TRACE,
            }.intersection(observations.info)
            and spec.matrix is not None
            else None
        )
        request = QueryRequest(
            execution, presentation, observations, max_index_bits, matrix
        )
    except QueryOptionError as exc:
        flag = spec.option_flag(
            exc.field, selector, frozenset(getattr(args, "_specified", {}))
        )
        if flag is None or str(exc).startswith(flag):
            raise
        raise ValueError(f"{flag}: {exc}") from exc
    _validate_request(request, frozenset(getattr(args, "_specified", {})), spec)
    return request


def _execution_query(
    args: argparse.Namespace,
    selector: SelectorId,
    index: int,
    certificate: str | None,
    spec: FamilySpec,
) -> ExecutionQuery:
    try:
        if selector is SelectorId.VERIFY:
            if certificate is None:
                raise AssertionError("verify selector lost its certificate path")
            return spec.build_verify_query(certificate)
        if selector is SelectorId.EVENTS:
            return spec.build_event_query(index, vars(args))
        return spec.build_term_query(index, vars(args))
    except QueryOptionError as exc:
        flag = spec.option_flag(
            exc.field, selector, frozenset(getattr(args, "_specified", {}))
        )
        if flag is None:
            raise
        if str(exc).startswith(flag):
            raise
        raise ValueError(f"{flag}: {exc}") from exc


def _observation_query(
    args: argparse.Namespace,
    selector: SelectorId,
    spec: FamilySpec,
) -> ObservationOptions:
    return spec.build_observations(
        selector,
        tuple(dict.fromkeys(observation_id(name) for name in args.info)),
        vars(args),
    )


def _validate_request(
    request: QueryRequest, specified: frozenset[str], spec: FamilySpec
) -> None:
    try:
        spec.validate_request(request, specified)
    except QueryOptionError as exc:
        flag = spec.option_flag(exc.field, request.selector, specified)
        if flag is None or str(exc).startswith(flag):
            raise
        raise ValueError(f"{flag}: {exc}") from exc


__all__ = [
    "bounded_index",
    "cli_index_token",
    "cli_integer",
    "parse_request",
    "parser",
    "power10_index",
]
