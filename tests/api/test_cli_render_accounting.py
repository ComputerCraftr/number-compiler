"""CLI rendering is measured even when it bypasses the native digit iterator."""

from typing import Never

import pytest

from number_compiler.api import cli_render
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.query_types import (
    AntihydraTermQuery,
    CollatzTermQuery,
    ReverseAddTermQuery,
    TermQuery,
)


@pytest.mark.parametrize("family", ("collatz", "antihydra", "reverse-add"))
@pytest.mark.parametrize("base", (2, 10))
def test_render_accounting_matches_actual_output_without_reporting_work(
    family: str,
    base: int,
) -> None:
    queries: dict[str, TermQuery] = {
        "collatz": CollatzTermQuery(4, seed=27),
        "reverse-add": ReverseAddTermQuery(4, seed=196),
        "antihydra": AntihydraTermQuery(4),
    }
    query = queries[family]
    term = NumberCompiler().project(query)
    before = cli_render._metrics_json(term)["execution_metrics"]
    assert isinstance(before, dict)
    assert before["rendering"]["requests"] is None
    result = cli_render._render_value(term, output_base=base, max_bits=1000)
    first = cli_render._metrics_json(term)
    assert cli_render._metrics_json(term) == first
    metrics = first["execution_metrics"]
    assert isinstance(metrics, dict)
    rendering = metrics["rendering"]
    assert rendering["requests"] == 1
    assert rendering["emitted_digits"] == len(result)
    assert rendering["failures"] == 0
    if family == "antihydra" or (family == "collatz" and base == 10):
        assert (
            rendering["integer_conversion_operand_bits"]
            == int(result, base).bit_length()
        )


def test_failed_conversion_is_visible_without_claimed_emission(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = NumberCompiler().project(CollatzTermQuery(10, seed=27))

    def fail_conversion(value: int, base: int) -> Never:
        assert value == 214 and base == 10
        raise RuntimeError("conversion failed")

    monkeypatch.setattr(cli_render, "_radix_string", fail_conversion)
    with pytest.raises(RuntimeError, match="conversion failed"):
        cli_render._render_value(term, output_base=10, max_bits=1000)
    metrics = cli_render._metrics_json(term)["execution_metrics"]
    assert isinstance(metrics, dict)
    assert metrics["rendering"] == {
        "requests": 1,
        "emitted_digits": 0,
        "failures": 1,
        "integer_conversion_operand_bits": 8,
    }


@pytest.mark.parametrize("regroup", (False, True))
def test_bad_native_digit_closes_consumer_stream_immediately(regroup: bool) -> None:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.resources.output_stream_metrics import (
        initialize_output_stream_metrics,
        measured_output_stream,
    )

    ledger = ResourceLedger()
    initialize_output_stream_metrics(ledger, "test_output_stream")
    stream = measured_output_stream(ledger, "test_output_stream", lambda: iter((1, 99)))
    with pytest.raises(ValueError, match="output digit"):
        if regroup:
            cli_render._power_of_two_radix_string(stream, 2, 16)
        else:
            cli_render._radix_string_from_lsd(stream, 10)
    assert ledger.counters["test_output_stream_emitted_digits"] == 2
    assert ledger.counters["test_output_stream_cancellations"] == 1
    assert ledger.counters["test_output_stream_failures"] == 0
    assert list(stream) == []
