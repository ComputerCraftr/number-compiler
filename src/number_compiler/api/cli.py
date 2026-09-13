"""Command-line interface for the canonical number compiler."""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Iterable
from dataclasses import asdict
from typing import Any

from number_compiler.api.number_api import (
    FermatTermPayload,
    FormulaTermPayload,
    MersenneTermPayload,
    NumberCompiler,
    PoweredCollatzTermPayload,
    PoweredReverseAddTermPayload,
    ProjectedNumberTerm,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import (
    require_integer as _integer,
)
from number_compiler.arithmetic.fields.symbolic_extent import (
    DyadicExtent,
    Extent,
    ReverseAddExtent,
    extent_json_value,
)

_DIGITS = "0123456789abcdefghijklmnopqrstuvwxyz"


def _cli_integer(text: str) -> int:
    """Parse one explicit ASCII integer token without Python-literal aliases."""
    if type(text) is not str or not text:
        raise argparse.ArgumentTypeError("expected an ASCII integer")
    digits = text[1:] if text[0] in "+-" else text
    if not digits or any(character < "0" or character > "9" for character in digits):
        raise argparse.ArgumentTypeError("expected an ASCII integer")
    return int(text, 10)


class _UniqueValue(argparse.Action):
    """Reject conflicting repetitions instead of silently using the last value."""

    def __call__(
        self,
        parser: argparse.ArgumentParser,
        namespace: argparse.Namespace,
        values: Any,
        option_string: str | None = None,
    ) -> None:
        seen: dict[str, object] = getattr(namespace, "_specified_options", {})
        if self.dest in seen and seen[self.dest] != values:
            parser.error(f"conflicting values for {option_string}")
        seen[self.dest] = values
        namespace._specified_options = seen
        setattr(namespace, self.dest, values)


def _validate_arguments(args: argparse.Namespace) -> None:
    """Admit domains and reject irrelevant explicit options before compilation."""
    _integer(args.index, "index", 1 if args.family == "mersenne" else 0)
    _integer(args.output_base, "--output-base", 2, 36)
    _integer(args.max_output_bits, "--max-output-bits", 1)
    permitted = {
        "reverse-add": {"seed", "base"},
        "196": {"seed", "base"},
        "collatz": {"seed", "radix"},
        "prime": {"start"},
        "fermat": set(),
        "mersenne": set(),
    }
    specified: dict[str, object] = getattr(args, "_specified_options", {})
    for option in specified.keys() & {"seed", "base", "radix", "start"}:
        if option not in permitted[args.family]:
            raise ValueError(f"--{option} does not apply to family {args.family}")
    if args.family in {"reverse-add", "196", "collatz"}:
        if args.seed is None and args.family != "196":
            raise ValueError(f"{args.family} requires seed")
        if args.seed is not None:
            _integer(args.seed, "--seed", 1 if args.family == "collatz" else 0)
    if args.family in {"reverse-add", "196"}:
        _integer(args.base, "--base", 2)
    elif args.family == "collatz":
        radix = _integer(args.radix, "--radix", 2)
        if not (radix in (2, 3) or radix % 6 == 0):
            raise ValueError("--radix must be 2, 3, or a multiple of 6 for Collatz")
    elif args.family == "prime":
        _integer(args.start, "--start", 0)

    if args.format == "symbolic":
        return
    cap = args.max_output_bits
    # These bounds require no sequence execution or large represented integer.
    over_cap = False
    if args.family == "fermat":
        over_cap = DyadicExtent(args.index, 1) > cap
    elif args.family == "mersenne":
        over_cap = args.index > cap
    elif args.family in {"reverse-add", "196"}:
        seed = 196 if args.seed is None else args.seed
        over_cap = max(1, seed.bit_length()) > cap  # Reverse/add cannot decrease.
    elif args.family == "collatz":
        # Preserve the renderer's existing conservative bit-extent policy.
        over_cap = args.seed.bit_length() + 2 * args.index + 2 > cap
    elif args.family == "prime":
        over_cap = (max(2, args.start) + args.index).bit_length() > cap
    if over_cap:
        raise ValueError(f"output exceeds --max-output-bits ({cap})")


def _metrics_json(term: ProjectedNumberTerm) -> dict[str, object]:
    """Separate immutable construction descriptors from observed runtime work."""
    payload = asdict(term.metrics)
    payload["width"] = extent_json_value(term.metrics.width)
    payload["metrics_scope"] = "construction_and_projection_descriptors"
    if isinstance(
        term.payload, (PoweredReverseAddTermPayload, PoweredCollatzTermPayload)
    ):
        payload["execution_metrics"] = asdict(term.payload.power_metrics())
        payload["execution_metrics_scope"] = "current_powered_term_ledger_snapshot"
    else:
        payload["execution_metrics"] = None
        payload["execution_metrics_scope"] = "unavailable_for_this_family"
    return payload


def _radix_string_from_lsd(digits: Iterable[int], base: int) -> str:
    base = _integer(base, "text output base", 2, len(_DIGITS))
    encoded = [_DIGITS[_integer(d, "output digit", 0, base - 1)] for d in digits]
    return "".join(reversed(encoded)) or "0"


def _power_of_two_radix_string(
    digits: Iterable[int],
    source_base: int,
    output_base: int,
) -> str:
    """Regroup a digit stream using a bounded carry, without an endpoint int."""
    source_base = _integer(source_base, "source radix", 2)
    output_base = _integer(output_base, "text output base", 2, len(_DIGITS))
    if source_base & (source_base - 1) or output_base & (output_base - 1):
        raise ValueError("digit regrouping requires power-of-two radices")
    source_bits, target_bits = (
        source_base.bit_length() - 1,
        output_base.bit_length() - 1,
    )
    accumulator = available = 0
    encoded: list[str] = []
    for digit in digits:
        accumulator |= _integer(digit, "output digit", 0, source_base - 1) << available
        available += source_bits
        while available >= target_bits:
            encoded.append(_DIGITS[accumulator & (output_base - 1)])
            accumulator >>= target_bits
            available -= target_bits
    if available:
        encoded.append(_DIGITS[accumulator])
    while len(encoded) > 1 and encoded[-1] == "0":
        encoded.pop()
    return "".join(reversed(encoded)) or "0"


def _radix_string(value: int, base: int) -> str:
    value = _integer(value, "output value", 0)
    base = _integer(base, "text output base", 2, len(_DIGITS))
    if value == 0:
        return "0"
    if base in (2, 8, 16):
        return format(value, {2: "b", 8: "o", 16: "x"}[base])
    if base == 10:
        previous_limit = sys.get_int_max_str_digits()
        try:
            sys.set_int_max_str_digits(0)
            return str(value)
        finally:
            sys.set_int_max_str_digits(previous_limit)
    out: list[str] = []
    while value:
        value, digit = divmod(value, base)
        out.append(_DIGITS[digit])
    return "".join(reversed(out))


def _render_value(term: ProjectedNumberTerm, *, output_base: int, max_bits: int) -> str:
    output_base = _integer(output_base, "--output-base", 2, len(_DIGITS))
    max_bits = _integer(max_bits, "--max-output-bits", 1)
    bit_extent: Extent
    if isinstance(term.payload, PoweredReverseAddTermPayload):
        powered = term.payload.term
        upper_bound = powered.maximum_width * (powered.base - 1).bit_length()
        # An admitted symbolic upper bound needs no separate exact-width
        # query before the explicit endpoint lowering. Tight caps retain the
        # existing exact-width decision.
        bit_extent = (
            upper_bound if upper_bound <= max_bits else powered.estimated_bit_length
        )
    else:
        bit_extent = term.estimated_bit_length
    if isinstance(bit_extent, ReverseAddExtent):
        bit_extent = bit_extent.materialize()
    if bit_extent > max_bits:
        raise ValueError(f"output exceeds --max-output-bits ({max_bits})")

    if (
        isinstance(term.payload, (FormulaTermPayload, PoweredReverseAddTermPayload))
        and term.source_radix == output_base
    ):
        if not 2 <= output_base <= len(_DIGITS):
            raise ValueError("text output base must be between 2 and 36")
        if isinstance(term.payload, PoweredReverseAddTermPayload):
            return _radix_string_from_lsd(term.payload.iter_digits(), output_base)
        return (
            "".join(_DIGITS[d] for d in term.payload.iter_digits(reverse=True)) or "0"
        )

    if not output_base & (output_base - 1):
        chunk_bits = output_base.bit_length() - 1
        if isinstance(term.payload, FermatTermPayload):
            exponent = term.payload.spec.exponent_extent.materialize(
                max_power=max_bits.bit_length(),
            )
            whole, remainder = divmod(exponent, chunk_bits)
            if not whole:
                return _DIGITS[(1 << remainder) + 1]
            return _DIGITS[1 << remainder] + "0" * (whole - 1) + "1"
        if isinstance(term.payload, MersenneTermPayload):
            whole, remainder = divmod(term.payload.spec.exponent, chunk_bits)
            prefix = _DIGITS[(1 << remainder) - 1] if remainder else ""
            return prefix + _DIGITS[output_base - 1] * whole
        if isinstance(term.payload, PoweredCollatzTermPayload):
            # The physical term's native image is binary, independently of
            # the user's requested Collatz digit-view radix.
            return _power_of_two_radix_string(
                term.payload.term.iter_digits(), 2, output_base
            )
        source_base = term.source_radix
        if (
            isinstance(term.payload, (FormulaTermPayload, PoweredReverseAddTermPayload))
            and source_base is not None
            and not source_base & (source_base - 1)
        ):
            return _power_of_two_radix_string(
                term.payload.iter_digits(), source_base, output_base
            )

    return _radix_string(term.materialize(max_bits=max_bits), output_base)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="number-compiler",
        description="Compile/project and emit exact terms from the canonical number-sequence families.",
    )
    sub = parser.add_subparsers(dest="command", required=True)
    nth = sub.add_parser("nth", help="project and output one exact sequence term")
    nth.add_argument(
        "family",
        choices=("reverse-add", "196", "collatz", "prime", "fermat", "mersenne"),
    )
    nth.add_argument(
        "index",
        type=_cli_integer,
        help="zero-based orbit/prime index; Fermat index; Mersenne exponent",
    )
    nth.add_argument(
        "--seed",
        type=_cli_integer,
        action=_UniqueValue,
        help="required for reverse-add/collatz; defaults to 196 for family '196'",
    )
    nth.add_argument(
        "--base",
        type=_cli_integer,
        action=_UniqueValue,
        default=10,
        help="reverse-add radix (default: 10)",
    )
    nth.add_argument(
        "--radix",
        type=_cli_integer,
        action=_UniqueValue,
        default=2,
        help="Collatz compiler radix: 2, 3, or a multiple of 6",
    )
    nth.add_argument(
        "--start",
        type=_cli_integer,
        action=_UniqueValue,
        default=2,
        help="prime sequence lower bound (default: 2)",
    )
    nth.add_argument(
        "--output-base",
        type=_cli_integer,
        action=_UniqueValue,
        default=10,
        help="text output radix, 2..36 (default: 10)",
    )
    nth.add_argument(
        "--max-output-bits",
        type=_cli_integer,
        action=_UniqueValue,
        default=1_000_000,
        help="refuse value expansion above this bound",
    )
    nth.add_argument(
        "--format",
        action=_UniqueValue,
        choices=("value", "symbolic", "json"),
        default="value",
    )
    nth.add_argument(
        "--metrics",
        action="store_true",
        help="include construction descriptors and available runtime ledger metrics on stderr",
    )

    classify = sub.add_parser(
        "classify", help="demand a Fermat/Mersenne primality certificate"
    )
    classify.add_argument("family", choices=("fermat", "mersenne"))
    classify.add_argument("index", type=_cli_integer)
    classify.add_argument("--format", choices=("value", "json"), default="value")
    classify.add_argument(
        "--factor",
        action="store_true",
        help="print an available factor; permit a separately counted etale witness query",
    )
    classify.add_argument("--max-factor-products", type=_cli_integer, default=4096)
    classify.add_argument("--max-candidate-bits", type=_cli_integer, default=1_000_000)
    observe = sub.add_parser("observe", help="demand a bounded cylinder observation")
    observe.add_argument("family", choices=("collatz", "196", "fermat", "mersenne"))
    observe.add_argument(
        "index",
        type=_cli_integer,
        help="accelerated events (physical ticks for physical-clock), generation, or special parameter",
    )
    observe.add_argument(
        "--kind",
        choices=(
            "clock",
            "physical-clock",
            "modular",
            "twisted",
            "hasse",
            "hensel",
            "tropical",
            "factor",
            "mirror",
            "root",
        ),
    )
    observe.add_argument("--seed", type=_cli_integer)
    observe.add_argument(
        "--defect",
        type=_cli_integer,
        help="supplied quadratic root, checked before observation",
    )
    observe.add_argument("--modulus", type=_cli_integer, default=257)
    observe.add_argument("--width", type=_cli_integer, default=2)
    observe.add_argument("--sign", type=_cli_integer, choices=(-1, 1), default=-1)
    observe.add_argument("--precision", type=_cli_integer, default=8)
    observe.add_argument("--target", type=_cli_integer, default=0)
    observe.add_argument("--s-weight", type=_cli_integer, default=1)
    observe.add_argument("--z-weight", type=_cli_integer, default=1)
    observe.add_argument(
        "--max-events",
        type=_cli_integer,
        default=4096,
        help="cap accelerated events, or physical ticks for physical-clock",
    )
    observe.add_argument("--max-digits", type=_cli_integer, default=4096)
    sub.add_parser("families", help="list canonical sequence/index semantics")
    return parser


def _classify(args: argparse.Namespace) -> int:
    """Resolve the demanded terminal bit without a hidden recurrence fallback."""
    index = _integer(args.index, "index", 2 if args.family == "mersenne" else 0)
    cap = _integer(args.max_candidate_bits, "--max-candidate-bits", 1)
    from number_compiler.sequences.power_numbers.admission import (
        require_special_candidate_budget,
    )

    try:
        require_special_candidate_budget(args.family, index, cap)
    except ValueError:
        raise ValueError(f"candidate exceeds --max-candidate-bits ({cap})") from None
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler

    factor_budget = _integer(args.max_factor_products, "--max-factor-products", 0)
    resolution = CanonicalSequenceCompiler().resolve_special_theorem(
        args.family,
        index,
        collect_etale_factor=args.factor,
        max_factor_products=factor_budget,
        max_candidate_bits=cap,
    )
    failure = resolution.source_guard.failure_bit
    status = "unknown" if failure is None else "composite" if failure else "prime"
    factor_expression = (
        None
        if resolution.composite_exponent_factor is None
        else f"2^{resolution.composite_exponent_factor.exponent}-1"
    )
    if args.format == "json":
        print(
            json.dumps(
                {
                    "family": args.family,
                    "index": index,
                    "status": status,
                    "decided": resolution.decided,
                    "method": resolution.projection_method,
                    "factor_query_status": resolution.factor_query_status,
                    "certificate": (
                        None
                        if resolution.primality is None
                        else asdict(resolution.primality)
                    ),
                    "factor_witness": resolution.factor_witness,
                    "factor_proof": (
                        "proper-coefficient-gcd"
                        if resolution.factor_witness is not None
                        else None
                    ),
                    "factor_expression": factor_expression,
                    "etale_ring_multiplications": resolution.etale_ring_multiplications,
                },
                sort_keys=True,
            )
        )
    else:
        print(status)
        if args.factor and resolution.factor_witness is not None:
            print(f"factor: {resolution.factor_witness}")
        elif args.factor and factor_expression is not None:
            print(f"factor: {factor_expression}")
    return 0 if resolution.decided else 3


def _family_text() -> str:
    return "\n".join(
        (
            "reverse-add INDEX --seed N [--base B]   (term 0 is the seed)",
            "196 INDEX                               (reverse-add; defaults seed 196 base 10)",
            "collatz INDEX --seed N [--radix R]      (ordinary Collatz term 0 is the seed)",
            "prime INDEX [--start N]                 (zero-based prime at or above start)",
            "fermat INDEX                            (F_INDEX = 2^(2^INDEX)+1)",
            "mersenne EXPONENT                       (M_EXPONENT = 2^EXPONENT-1)",
        )
    )


def main(argv: list[str] | None = None) -> int:
    if argv is not None and (
        type(argv) is not list or any(type(value) is not str for value in argv)
    ):
        print("number-compiler: argv must be a list of strings", file=sys.stderr)
        return 2
    args = _parser().parse_args(argv)
    if args.command == "families":
        print(_family_text())
        return 0

    try:
        if args.command == "observe":
            from number_compiler.api.cylinder_observation import execute_observation

            print(json.dumps(execute_observation(args), sort_keys=True))
            return 0
        if args.command == "classify":
            return _classify(args)
        _validate_arguments(args)
        compiler = NumberCompiler()
        term = compiler.project_nth(
            args.family,
            args.index,
            seed=args.seed,
            base=args.base,
            radix=args.radix,
            start=args.start,
        )
        if args.format == "symbolic":
            rendered = term.symbolic
        else:
            value_text = _render_value(
                term,
                output_base=args.output_base,
                max_bits=args.max_output_bits,
            )
            if args.format == "json":
                metric_payload = _metrics_json(term)
                execution_metrics = metric_payload.pop("execution_metrics")
                execution_scope = metric_payload.pop("execution_metrics_scope")
                rendered = json.dumps(
                    {
                        "family": term.family,
                        "index": term.index,
                        "parameter": term.parameter,
                        "source_radix": term.source_radix,
                        "output_base": args.output_base,
                        "value": value_text,
                        "symbolic": term.symbolic,
                        "estimated_bit_length": extent_json_value(
                            term.estimated_bit_length
                        ),
                        "projection_metrics": metric_payload,
                        "execution_metrics": execution_metrics,
                        "execution_metrics_scope": execution_scope,
                    },
                    sort_keys=True,
                )
            else:
                rendered = value_text
        print(rendered)
        if args.metrics and args.format != "json":
            print(json.dumps(_metrics_json(term), sort_keys=True), file=sys.stderr)
        return 0
    except (
        ValueError,
        TypeError,
        IndexError,
        OverflowError,
        BlockContextBudgetExceeded,
    ) as exc:
        print(f"number-compiler: {exc}", file=sys.stderr)
        return 2


__all__ = ["main"]
