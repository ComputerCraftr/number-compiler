"""Family capabilities and typed, fully admitted command-line requests."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from typing import Any, Literal

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent


@dataclass(frozen=True)
class FamilyCapability:
    unit: str
    parameters: tuple[str, ...]
    nth_info: tuple[str, ...]
    event_info: tuple[str, ...] = ()


CAPABILITIES = {
    "reverse-add": FamilyCapability(
        "iterations", ("seed", "base"), ("metrics", "mirror")
    ),
    "196": FamilyCapability("iterations", ("seed", "base"), ("metrics", "mirror")),
    "collatz": FamilyCapability(
        "iterations",
        ("seed", "radix"),
        ("metrics", "clock"),
        ("clock", "modular", "twisted", "hasse", "hensel", "tropical", "factor"),
    ),
    "prime": FamilyCapability("prime_index", ("start",), ("metrics",)),
    "fermat": FamilyCapability(
        "fermat_index", (), ("metrics", "primality", "factor", "root")
    ),
    "mersenne": FamilyCapability(
        "mersenne_exponent", (), ("metrics", "primality", "factor", "root")
    ),
    "antihydra": FamilyCapability(
        "iterations",
        (),
        (
            "metrics",
            "ledger",
            "clock",
            "modular",
            "tape",
            "twisted",
            "spacetime",
            "hasse",
            "hensel",
            "mahler",
            "tropical",
            "factor",
        ),
    ),
}


@dataclass(frozen=True)
class QueryRequest:
    family: str
    selector: Literal["nth", "events", "verify"]
    index: int
    info: tuple[str, ...] = ()
    no_value: bool = False
    format: str = "value"
    output_base: int = 10
    seed: int | None = None
    base: int = 10
    radix: int = 2
    start: int = 2
    certificate: str | None = None
    max_output_bits: int = 1_000_000
    max_steps: int = 4096
    max_state_bits: int = 4096
    max_events: int = 4096
    max_digits: int = 4096
    max_observer_terms: int = 1_000_000
    max_candidate_bits: int = 1_000_000
    max_factor_products: int = 4096
    max_prime_states: int = 131_072
    max_prime_work: int = 1_000_000
    max_prime_stages: int = 4096
    defect: int | None = None
    modulus: int = 257
    width: int = 2
    sign: int = -1
    precision: int = 8
    target: int = 0
    s_weight: int = 1
    z_weight: int = 1
    time_width: int = 2
    time_sign: int = 1

    @property
    def index_unit(self) -> str:
        return (
            "accelerated_odd_events"
            if self.selector == "events"
            else CAPABILITIES[self.family].unit
        )


def cli_integer(text: str) -> int:
    digits = text[1:] if text and text[0] in "+-" else text
    if not digits or any(c < "0" or c > "9" for c in digits):
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
        values: Any,
        option_string: str | None = None,
    ) -> None:
        seen: dict[str, object] = getattr(namespace, "_specified", {})
        if self.dest in seen and seen[self.dest] != values:
            parser.error(f"conflicting values for {option_string}")
        seen[self.dest] = values
        namespace._specified = seen
        setattr(namespace, self.dest, values)


# Options are exposed only by families with the matching observation capability.
OBSERVER_OPTIONS: dict[str, tuple[int | None, tuple[str, ...]]] = {
    "defect": (None, ("root",)),
    "modulus": (257, ("modular", "twisted", "tape", "spacetime", "hasse", "factor")),
    "width": (2, ("mirror", "twisted", "tape", "spacetime", "hasse", "factor")),
    "sign": (-1, ("twisted", "tape", "spacetime", "factor")),
    "precision": (8, ("hensel", "mahler")),
    "target": (0, ("hensel",)),
    "s_weight": (1, ("tropical",)),
    "z_weight": (1, ("tropical",)),
    "time_width": (2, ("spacetime",)),
    "time_sign": (1, ("spacetime",)),
}


def observation_options(family: str) -> dict[str, tuple[int | None, tuple[str, ...]]]:
    """Narrow shared names to parameters actually consumed by a family."""
    capability = CAPABILITIES[family]
    infos = set(capability.nth_info + capability.event_info)
    selected = {
        name: (default, tuple(info for info in supported if info in infos))
        for name, (default, supported) in OBSERVER_OPTIONS.items()
        if infos.intersection(supported)
    }
    if family in {"fermat", "mersenne"}:
        return {name: value for name, value in selected.items() if name == "defect"}
    if family == "antihydra":
        return {
            name: value
            for name, value in selected.items()
            if name not in {"target", "s_weight", "z_weight"}
        }
    if family == "collatz":
        for name in ("width", "sign"):
            default, supported = selected[name]
            selected[name] = (
                default,
                tuple(info for info in supported if info != "factor"),
            )
    return selected


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        prog="number-compiler",
        description="Exact family terms: number-compiler FAMILY --nth N [--info NAME].",
    )
    result.add_argument("--list-families", action="store_true")
    families = result.add_subparsers(dest="family")
    for name, capability in CAPABILITIES.items():
        command = families.add_parser(
            name,
            help=f"index unit: {capability.unit}",
            description=f"{name}: --nth uses {capability.unit}; term zero is the seed where applicable.",
        )
        selectors = command.add_mutually_exclusive_group(required=True)
        selectors.add_argument("--nth", type=cli_integer, action=UniqueValue)
        if capability.event_info:
            selectors.add_argument(
                "--events",
                type=cli_integer,
                action=UniqueValue,
                help="accelerated odd events; information-only query",
            )
        if name == "antihydra":
            selectors.add_argument(
                "--verify-nonhalting", action=UniqueValue, metavar="PATH"
            )
        command.add_argument(
            "--info",
            action="append",
            choices=tuple(dict.fromkeys(capability.nth_info + capability.event_info)),
            default=[],
            help="requested information; repeat for multiple observations",
        )
        command.add_argument("--no-value", action="store_true")
        command.add_argument(
            "--format",
            choices=("value", "symbolic", "json"),
            default="value",
            action=UniqueValue,
        )
        command.add_argument(
            "--output-base", type=cli_integer, default=10, action=UniqueValue
        )
        command.add_argument(
            "--max-output-bits", type=cli_integer, default=1_000_000, action=UniqueValue
        )
        defaults = {"seed": None, "base": 10, "radix": 2, "start": 2}
        for parameter in capability.parameters:
            command.add_argument(
                "--" + parameter,
                type=cli_integer,
                default=defaults[parameter],
                action=UniqueValue,
            )
        for option, (default, _) in observation_options(name).items():
            command.add_argument(
                "--" + option.replace("_", "-"),
                type=cli_integer,
                default=default,
                action=UniqueValue,
            )
        budgets: dict[str, int] = {}
        if name == "antihydra":
            budgets.update(
                max_steps=4096, max_state_bits=4096, max_observer_terms=1_000_000
            )
        elif name == "prime":
            budgets.update(
                max_prime_states=131_072,
                max_prime_work=1_000_000,
                max_prime_stages=4096,
            )
        else:
            budgets["max_digits"] = 4096
        if name == "collatz":
            budgets["max_events"] = 4096
        if name in {"fermat", "mersenne"}:
            budgets.update(max_candidate_bits=1_000_000, max_factor_products=4096)
        for option, default in budgets.items():
            command.add_argument(
                "--" + option.replace("_", "-"),
                type=cli_integer,
                default=default,
                action=UniqueValue,
            )
    return result


def parse_request(argv: list[str]) -> QueryRequest | None:
    command = parser()
    if argv and argv[0] in {
        "nth",
        "observe",
        "classify",
        "verify-nonhalting",
        "families",
    }:
        command.error(
            "old command form removed; use FAMILY --nth N [--info NAME], "
            "antihydra --verify-nonhalting PATH, or --list-families"
        )
    args = command.parse_args(argv)
    if args.list_families:
        if args.family is not None:
            command.error("--list-families cannot be combined with a family query")
        return None
    if args.family is None:
        command.error(
            "choose a family and --nth N; use --list-families for available families"
        )
    certificate = getattr(args, "verify_nonhalting", None)
    events = getattr(args, "events", None)
    selector: Literal["nth", "events", "verify"] = (
        "verify"
        if certificate is not None
        else "events"
        if events is not None
        else "nth"
    )
    fields = {
        key: value
        for key, value in vars(args).items()
        if key in QueryRequest.__dataclass_fields__ and key not in {"info", "index"}
    }
    fields.update(
        selector=selector,
        index=0
        if selector == "verify"
        else events
        if selector == "events"
        else args.nth,
        certificate=certificate,
        info=tuple(dict.fromkeys(args.info)),
    )
    request = QueryRequest(**fields)
    validate(request, frozenset(getattr(args, "_specified", {})))
    return request


def validate(q: QueryRequest, specified: frozenset[str]) -> None:
    capability = CAPABILITIES[q.family]
    if q.selector == "verify":
        if q.info or q.no_value or specified - {"verify_nonhalting", "format"}:
            raise ValueError(
                "certificate verification cannot be combined with term options"
            )
        if q.format == "symbolic":
            raise ValueError("certificate verification has no symbolic value")
        return
    require_integer(
        q.index,
        "--nth" if q.selector == "nth" else "--events",
        1 if q.family == "mersenne" else 0,
    )
    allowed = capability.event_info if q.selector == "events" else capability.nth_info
    if set(q.info) - set(allowed):
        raise ValueError("requested information is unavailable for this selector")
    if (q.no_value or q.selector == "events") and not q.info:
        raise ValueError("information-only queries require --info")
    if q.format == "symbolic" and (q.no_value or q.selector == "events"):
        raise ValueError("symbolic output requires a term value")
    for option, (_, supported) in observation_options(q.family).items():
        if option in specified and not set(q.info).intersection(supported):
            raise ValueError(
                f"--{option.replace('_', '-')} requires its matching --info"
            )
    if "root" in q.info and q.defect is None:
        raise ValueError("--info root requires --defect")
    if q.family in {"reverse-add", "collatz"} and q.seed is None:
        raise ValueError(f"{q.family} requires --seed")
    if q.seed is not None:
        require_integer(q.seed, "--seed", 1 if q.family == "collatz" else 0)
    require_integer(q.base, "--base", 2)
    require_integer(q.radix, "--radix", 2)
    if q.family == "collatz" and not (q.radix in (2, 3) or q.radix % 6 == 0):
        raise ValueError("--radix must be 2, 3, or a multiple of 6 for Collatz")
    if q.selector == "events" and q.seed is not None and not q.seed & 1:
        raise ValueError("accelerated event observations require an odd seed")
    require_integer(q.start, "--start", 0)
    require_integer(q.output_base, "--output-base", 2, 36)
    for name in (
        "max_output_bits",
        "max_state_bits",
        "max_digits",
        "max_candidate_bits",
    ):
        require_integer(getattr(q, name), "--" + name.replace("_", "-"), 1)
    for name in (
        "max_steps",
        "max_events",
        "max_factor_products",
        "max_observer_terms",
    ):
        require_integer(getattr(q, name), "--" + name.replace("_", "-"), 0)
    for name in ("max_prime_states", "max_prime_work", "max_prime_stages"):
        require_integer(getattr(q, name), "--" + name.replace("_", "-"), 1)
    if q.selector == "events" and q.index > q.max_events:
        raise ValueError("source observation budget exceeded")
    if q.family == "collatz" and q.selector == "nth" and "clock" in q.info:
        assert q.seed is not None
        if q.index > q.max_events or q.seed.bit_length() > q.max_digits:
            raise ValueError("physical clock observation budget exceeded")
    require_integer(q.modulus, "--modulus", 2)
    if q.modulus.bit_length() > 4096:
        raise ValueError("coefficient modulus exceeds bit budget")
    if "mirror" in q.info:
        require_integer(q.width, "--width", 1)
        if q.width > q.max_digits:
            raise ValueError("mirror sheet exceeds digit budget")
    else:
        require_integer(q.width, "--width", 1, 256)
    require_integer(q.time_width, "--time-width", 1, 256)
    require_integer(q.precision, "--precision", 0, 4096)
    if q.sign not in (-1, 1) or q.time_sign not in (-1, 1):
        raise ValueError("cylinder signs must be -1 or +1")
    if q.family == "antihydra":
        require_integer(q.max_state_bits, "--max-state-bits", 4)
        if "hasse" in q.info:
            require_integer(q.width, "Hasse order", 1, 8)
        if {"hensel", "mahler"}.intersection(q.info):
            require_integer(q.precision, "--precision", 1, 4096)
        if "factor" in q.info and pow(2, q.width, q.modulus) != q.sign % q.modulus:
            raise ValueError("factor target is incompatible with the tape cylinder")
        if "spacetime" in q.info:
            require_integer(q.width, "spatial width", 1, 64)
            require_integer(q.time_width, "temporal width", 1, 64)
            require_integer(q.max_observer_terms, "projection work budget", 1)
    if q.family in {"fermat", "mersenne"} and {"primality", "factor"}.intersection(
        q.info
    ):
        require_integer(
            q.index, "special theorem parameter", 2 if q.family == "mersenne" else 0
        )
        from number_compiler.sequences.power_numbers.admission import (
            require_special_candidate_budget,
        )

        require_special_candidate_budget(q.family, q.index, q.max_candidate_bits)
    if q.no_value or q.selector != "nth" or q.format == "symbolic":
        return
    cap = q.max_output_bits
    over_cap = False
    if q.family == "fermat":
        over_cap = DyadicExtent(q.index, 1) > cap
    elif q.family == "mersenne":
        over_cap = q.index > cap
    elif q.family in {"reverse-add", "196"}:
        over_cap = (196 if q.seed is None else q.seed).bit_length() > cap
    elif q.family == "collatz":
        assert q.seed is not None
        over_cap = q.seed.bit_length() + 2 * q.index + 2 > cap
    elif q.family == "prime":
        over_cap = (max(2, q.start) + q.index).bit_length() > cap
    if over_cap:
        raise ValueError(f"output exceeds --max-output-bits ({cap})")
