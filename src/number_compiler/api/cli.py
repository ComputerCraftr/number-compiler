"""Family-first CLI; parsing, execution owners and rendering have separate roles."""

from __future__ import annotations

import json
import sys

from number_compiler.api import cli_render as _rendering
from number_compiler.api.cli_requests import CAPABILITIES, QueryRequest, parse_request
from number_compiler.api.number_api import NumberCompiler
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.unresolved_term import UnresolvedSequenceTerm

# Retain the established Python helper exports with their canonical owner.
_metrics_json = _rendering._metrics_json
_power_of_two_radix_string = _rendering._power_of_two_radix_string
_radix_string = _rendering._radix_string
_radix_string_from_lsd = _rendering._radix_string_from_lsd
_render_value = _rendering._render_value


def _verify(request: QueryRequest) -> int:
    from number_compiler.api.json_output import json_integers
    from number_compiler.sequences.antihydra.certificate import verify_file

    assert request.certificate is not None
    try:
        verdict = verify_file(request.certificate)
    except (ValueError, TypeError, OverflowError) as exc:
        verdict = {
            "nonhalting_certified": False,
            "status": "rejected",
            "reason": str(exc),
        }
    if request.format == "json":
        print(json.dumps(json_integers(verdict), sort_keys=True))
    else:
        print(
            "nonhalting certified"
            if verdict["nonhalting_certified"]
            else "certificate rejected"
        )
        if not verdict["nonhalting_certified"]:
            print(json.dumps(json_integers(verdict), sort_keys=True), file=sys.stderr)
    return 0 if verdict["nonhalting_certified"] else 1


def main(argv: list[str] | None = None) -> int:
    if argv is not None and (
        type(argv) is not list or any(type(v) is not str for v in argv)
    ):
        print("number-compiler: argv must be a list of strings", file=sys.stderr)
        return 2
    try:
        request = parse_request(list(sys.argv[1:]) if argv is None else argv)
        if request is None:
            for family, capability in CAPABILITIES.items():
                print(
                    f"{family}: --nth N ({capability.unit}); info: {', '.join(capability.nth_info)}"
                )
                print("  --nth-power10 K (exact index 10^K, K >= 0)")
                if capability.event_info:
                    print(
                        f"  --events E (accelerated_odd_events); info: {', '.join(capability.event_info)}"
                    )
                if family == "antihydra":
                    print("  --verify-nonhalting PATH")
            return 0
        if request.selector == "verify":
            return _verify(request)
        from number_compiler.api.cli_context import QueryContext, information_unresolved
        from number_compiler.api.json_output import json_integers

        bounded_observer = "mirror" in request.info or (
            request.family == "collatz"
            and request.selector == "nth"
            and "clock" in request.info
        )
        compiler = (
            NumberCompiler(max_context_nodes=10000, max_cache_entries=20000)
            if bounded_observer
            else NumberCompiler()
        )
        context = QueryContext(request, compiler)
        context.admit_observation_extents()
        value = None
        if request.selector == "nth" and not request.no_value:
            from number_compiler.api.symbolic_terms import render_symbolic

            value = (
                (
                    context.term.symbolic
                    if request.nth_power10 is None
                    else render_symbolic(context.term, f"10^{request.nth_power10}")
                )
                if request.format == "symbolic"
                else _render_value(
                    context.term,
                    output_base=request.output_base,
                    max_bits=request.max_output_bits,
                )
            )
        info = context.information()
        if request.format == "json":
            print(
                json.dumps(
                    json_integers(
                        {
                            "family": request.family,
                            "index": request.presentation_index,
                            "index_unit": request.index_unit,
                            "output_base": request.output_base,
                            "value": value,
                            "info": info,
                            **(
                                {}
                                if context.unresolved_boundary is None
                                else {
                                    "error": request.present_indices(
                                        context.unresolved_boundary.diagnostic()
                                    )
                                }
                            ),
                        }
                    ),
                    sort_keys=True,
                )
            )
        else:
            if value is not None:
                print(value)
            if info:
                print(json.dumps(json_integers(info), sort_keys=True), file=sys.stderr)
        if context.unresolved_boundary is not None:
            if request.format != "json":
                print(
                    f"number-compiler: {context.unresolved_boundary}", file=sys.stderr
                )
            return 3
        return 3 if information_unresolved(info) else 0
    except UnresolvedSequenceTerm as exc:
        # No endpoint or symbolic value is published across an unproved boundary.
        if request is not None and request.format == "json":
            from number_compiler.api.json_output import json_integers

            print(
                json.dumps(
                    json_integers(
                        {
                            "family": request.family,
                            "index": request.presentation_index,
                            "index_unit": request.index_unit,
                            "output_base": request.output_base,
                            "value": None,
                            "info": {},
                            "error": request.present_indices(exc.diagnostic()),
                        }
                    ),
                    sort_keys=True,
                )
            )
        else:
            print(
                f"number-compiler: {exc}; certified through index "
                f"{exc.certified_max_index}",
                file=sys.stderr,
            )
        return 3
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
