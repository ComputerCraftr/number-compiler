"""Family-first CLI; parsing, execution owners and rendering have separate roles."""

from __future__ import annotations

import json
import sys

from number_compiler.api import cli_render as _rendering
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.cli_types import QueryRequest
from number_compiler.api.family_registry import (
    family_listing,
    resolve_verification_adapter,
)
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.observation_types import OutputFormat, SelectorId
from number_compiler.api.output_schema import UnresolvedErrorPacket, query_result
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.unresolved_term import UnresolvedSequenceTerm


def _verify(request: QueryRequest) -> int:
    from number_compiler.api.json_output import json_integers

    result = resolve_verification_adapter(request.execution)(request.execution)
    if request.presentation.format is OutputFormat.JSON:
        print(json.dumps(json_integers(result.packet), sort_keys=True))
    else:
        print(result.success_message if result.accepted else "certificate rejected")
        if not result.accepted:
            print(
                json.dumps(json_integers(result.packet), sort_keys=True),
                file=sys.stderr,
            )
    return 0 if result.accepted else 1


def _unresolved_packet(
    request: QueryRequest, error: UnresolvedSequenceTerm
) -> UnresolvedErrorPacket:
    return {
        "code": "unresolved_sequence_boundary",
        "requested_index": request.presentation_index,
        "certified_max_index": error.certified_max_index,
        "certificate_id": error.certificate_id,
        "reason": error.reason,
    }


def main(argv: list[str] | None = None) -> int:
    if argv is not None and (
        type(argv) is not list or any(type(v) is not str for v in argv)
    ):
        print("number-compiler: argv must be a list of strings", file=sys.stderr)
        return 2
    request: QueryRequest | None = None
    try:
        request = parse_request(list(sys.argv[1:]) if argv is None else argv)
        if request is None:
            print("\n".join(family_listing()))
            return 0
        if request.selector is SelectorId.VERIFY:
            return _verify(request)
        from number_compiler.api.cli_context import QueryContext, information_unresolved
        from number_compiler.api.json_output import json_integers

        compiler = (
            NumberCompiler(max_context_nodes=10000, max_cache_entries=20000)
            if request.requires_bounded_observer
            else NumberCompiler()
        )
        context = QueryContext(request, compiler)
        context.admit_observation_extents()
        value = None
        if request.selector is SelectorId.NTH and not request.presentation.no_value:
            from number_compiler.api.symbolic_terms import render_symbolic

            value = (
                (
                    context.term.symbolic
                    if request.presentation.index.exponent is None
                    else render_symbolic(
                        context.term, f"10^{request.presentation.index.exponent}"
                    )
                )
                if request.presentation.format is OutputFormat.SYMBOLIC
                else _rendering._render_value(
                    context.term,
                    output_base=request.presentation.output_base,
                    max_bits=request.presentation.max_output_bits,
                )
            )
        info = context.information()
        if request.presentation.format is OutputFormat.JSON:
            print(
                json.dumps(
                    json_integers(
                        query_result(
                            family=request.family.value,
                            index=request.presentation_index,
                            index_unit=request.index_unit.value,
                            output_base=request.presentation.output_base,
                            value=value,
                            info=info,
                            error=None
                            if context.unresolved_boundary is None
                            else _unresolved_packet(
                                request, context.unresolved_boundary
                            ),
                        )
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
            if request.presentation.format is not OutputFormat.JSON:
                print(
                    f"number-compiler: {context.unresolved_boundary}", file=sys.stderr
                )
            return 3
        return 3 if information_unresolved(info) else 0
    except UnresolvedSequenceTerm as exc:
        # No endpoint or symbolic value is published across an unproved boundary.
        if request is not None and request.presentation.format is OutputFormat.JSON:
            from number_compiler.api.json_output import json_integers

            print(
                json.dumps(
                    json_integers(
                        query_result(
                            family=request.family.value,
                            index=request.presentation_index,
                            index_unit=request.index_unit.value,
                            output_base=request.presentation.output_base,
                            value=None,
                            info={},
                            error=_unresolved_packet(request, exc),
                        )
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
