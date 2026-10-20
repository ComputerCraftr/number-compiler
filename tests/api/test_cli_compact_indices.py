"""Compact CLI coordinates retain exact integer execution and bounded admission."""

from __future__ import annotations

import json
import sys
from typing import Never

import pytest

from number_compiler.api import cli, cli_context, cli_render, cli_requests
from number_compiler.api.family_registry import CAPABILITIES
from number_compiler.api.json_output import is_string_object_mapping
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.query_types import FermatTermQuery, TermQuery
from number_compiler.arithmetic.contracts.family_identity import FamilyId
from number_compiler.arithmetic.contracts.unresolved_term import UnresolvedSequenceTerm


def forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("unrequested execution was entered")


def _json_object(text: str) -> dict[str, object]:
    decoded: object = json.loads(text)
    if not is_string_object_mapping(decoded):
        raise AssertionError("CLI output must be a JSON object")
    return dict(decoded)


def family_options(family: FamilyId) -> list[str]:
    return ["--seed", "27"] if family in {"reverse-add", "2rev10", "collatz"} else []


@pytest.mark.parametrize("family", CAPABILITIES)
@pytest.mark.parametrize("exponent", (0, 1, 4))
def test_compact_selector_is_an_exact_family_integer(
    family: FamilyId, exponent: int
) -> None:
    request = cli_requests.parse_request(
        [
            family.value,
            "--nth-power10",
            str(exponent),
            *family_options(family),
            "--format",
            "symbolic",
        ]
    )
    assert request is not None
    assert request.selector == "nth" and type(request.index) is int
    assert request.index == 10**exponent
    assert request.index_unit == CAPABILITIES[family].unit
    assert request.presentation_index == {"encoding": "power10", "exponent": exponent}
    assert request.max_index_bits == 1_000_000


@pytest.mark.parametrize("family", CAPABILITIES)
def test_compact_value_and_info_match_explicit_index(
    family: FamilyId,
    capsys: pytest.CaptureFixture[str],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    common = [*family_options(family), "--info", "metrics", "--format", "json"]
    if family == FamilyId.A367620:
        from number_compiler.resources.process_cache import (
            ProcessCache,
            temporary_process_cache,
        )
        from tests.support.comma_certificate_cache import (
            count_forest_certificate_verifications,
            forbid_certificate_asset_access,
        )

        with temporary_process_cache(ProcessCache()):
            verification_calls = count_forest_certificate_verifications(monkeypatch)
            # The cold path still hashes the shipped asset and accepts the
            # verifier's result; the standalone cache test exercises the full
            # forest walk. The warm path must avoid all package access.
            assert cli.main([family.value, "--nth", "1", *common]) == 0
            ordinary = json.loads(capsys.readouterr().out)
            assert len(verification_calls) == 1
            forbid_certificate_asset_access(monkeypatch)
            assert cli.main([family.value, "--nth-power10", "0", *common]) == 0
            compact = json.loads(capsys.readouterr().out)
            assert len(verification_calls) == 1
    else:
        assert cli.main([family.value, "--nth", "1", *common]) == 0
        ordinary = json.loads(capsys.readouterr().out)
        assert cli.main([family.value, "--nth-power10", "0", *common]) == 0
        compact = json.loads(capsys.readouterr().out)
    encoded = {"encoding": "power10", "exponent": 0}
    assert compact["index"] == compact["info"]["metrics"]["index"] == encoded
    assert ordinary["index"] == ordinary["info"]["metrics"]["index"] == 1
    assert compact["value"] == ordinary["value"]
    assert compact["index_unit"] == ordinary["index_unit"]


@pytest.mark.parametrize("seed,entry_ticks", ((5, 5), (13, 9), (1 << 1000, 1000)))
@pytest.mark.parametrize("exponent", (6, 12))
def test_collatz_compact_index_uses_exact_terminal_cycle(
    seed: int,
    entry_ticks: int,
    exponent: int,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "collatz",
                "--seed",
                str(seed),
                "--nth-power10",
                str(exponent),
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = _json_object(capsys.readouterr().out)
    terminal_values: tuple[int, ...] = (1, 4, 2)
    terminal_index: int = (10**exponent - entry_ticks) % len(terminal_values)
    terminal_value: int = terminal_values[terminal_index]
    assert packet["value"] == str(terminal_value)
    assert packet["index"] == {"encoding": "power10", "exponent": exponent}


@pytest.mark.parametrize(
    "family,conflict",
    (
        ("prime", ["--nth", "10"]),
        ("collatz", ["--events", "10"]),
        ("antihydra", ["--verify-nonhalting", "certificate.json"]),
        ("prime", ["--nth-power10", "2"]),
    ),
)
def test_compact_selector_conflicts(family: FamilyId, conflict: list[str]) -> None:
    with pytest.raises(SystemExit) as stopped:
        cli_requests.parse_request([family, "--nth-power10", "1", *conflict])
    assert stopped.value.code == 2


def test_repeated_equivalent_index_options_remain_accepted() -> None:
    explicit = cli_requests.parse_request(["prime", "--nth", "+01", "--nth", "1"])
    compact = cli_requests.parse_request(
        ["prime", "--nth-power10", "+01", "--nth-power10", "1"]
    )
    assert explicit is not None and explicit.index == 1
    assert compact is not None and compact.index == 10


@pytest.mark.parametrize("token", ("1.0", "1e3", "0x10", "1_000", "١", ""))
def test_compact_exponents_require_ascii_integers(token: str) -> None:
    with pytest.raises(SystemExit) as stopped:
        cli_requests.parse_request(["prime", "--nth-power10", token])
    assert stopped.value.code == 2


@pytest.mark.parametrize(
    "options",
    (
        ["--nth-power10", "-1"],
        ["--nth-power10", "1", "--max-index-bits", "3"],
        ["--nth-power10", "3", "--max-index-bits", "9"],
        ["--nth", "1000", "--max-index-bits", "9"],
        ["--nth-power10", "0", "--max-index-bits", "0"],
        ["--nth-power10", "0", "--max-index-bits", "-1"],
        ["--nth-power10", "9" * 4000],
        ["--nth-power10", "9" * 100000],
        ["--nth", "9" * 10000, "--max-index-bits", "32"],
    ),
)
def test_invalid_or_over_budget_indices_refuse_before_execution(
    options: list[str],
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(cli, "NumberCompiler", forbidden)
    assert cli.main(["prime", *options]) == 2
    captured = capsys.readouterr()
    assert captured.out == ""
    assert "--nth-power10" in captured.err or "--max-index-bits" in captured.err


@pytest.mark.parametrize("exponent", (0, 1, 2, 3, 8, 17, 100, 1000))
def test_exact_index_bit_budget_boundary(exponent: int) -> None:
    expected = 10**exponent
    bits = expected.bit_length()
    request = cli_requests.parse_request(
        [
            "prime",
            "--nth-power10",
            str(exponent),
            "--max-index-bits",
            str(bits),
            "--format",
            "symbolic",
        ]
    )
    assert request is not None and request.index == expected
    if bits > 1:
        with pytest.raises(ValueError, match="--max-index-bits"):
            cli_requests.parse_request(
                [
                    "prime",
                    "--nth-power10",
                    str(exponent),
                    "--max-index-bits",
                    str(bits - 1),
                    "--format",
                    "symbolic",
                ]
            )


def test_large_explicit_index_uses_local_bounded_conversion() -> None:
    previous = sys.get_int_max_str_digits()
    request = cli_requests.parse_request(
        ["prime", "--nth", "1" + "0" * 5000, "--format", "symbolic"]
    )
    assert request is not None and request.index == 10**5000
    assert request.presentation_index == request.index
    assert sys.get_int_max_str_digits() == previous


def test_huge_exponent_refuses_before_power_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(cli_requests, "power10_index", forbidden)
    with pytest.raises(ValueError, match="--max-index-bits"):
        cli_requests.parse_request(["prime", "--nth-power10", "9" * 100000])


def test_huge_event_index_refuses_without_decimal_integer_conversion(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(cli, "NumberCompiler", forbidden)
    original = cli_requests.cli_integer

    def guarded(text: str) -> int:
        assert len(text) < 1000, "event index entered unbounded decimal conversion"
        return original(text)

    monkeypatch.setattr(cli_requests, "cli_integer", guarded)
    previous = sys.get_int_max_str_digits()
    try:
        sys.set_int_max_str_digits(0)
        assert (
            cli.main(
                [
                    "collatz",
                    "--events",
                    "9" * 100000,
                    "--seed",
                    "27",
                    "--info",
                    "temporal.clock",
                    "--max-index-bits",
                    "32",
                ]
            )
            == 2
        )
    finally:
        sys.set_int_max_str_digits(previous)
    assert "--max-index-bits" in capsys.readouterr().err


@pytest.mark.parametrize(
    "family",
    (FamilyId.FERMAT, FamilyId.MERSENNE, FamilyId.ANTIHYDRA, FamilyId.A367620),
)
def test_real_large_compact_metadata_never_formats_index_text(
    family: FamilyId,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.api import symbolic_terms

    monkeypatch.setattr(symbolic_terms, "integer_text", forbidden)
    monkeypatch.setattr(cli_render, "render_value", forbidden)
    expected = 3 if family == "a367620" else 2 if family == "antihydra" else 0
    assert (
        cli.main(
            [
                family.value,
                "--nth-power10",
                "5000",
                "--no-value",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == expected
    )
    captured = capsys.readouterr()
    if family == "antihydra":
        assert captured.out == "" and "source execution budget" in captured.err
        return
    packet = json.loads(captured.out)
    assert (
        packet["index"]
        == packet["info"]["metrics"]["index"]
        == {
            "encoding": "power10",
            "exponent": 5000,
        }
    )
    assert packet["value"] is None
    if family == "fermat":
        extent = packet["info"]["metrics"]["width"]
        assert extent["power"] == packet["index"]
        assert extent["expression"] == "2**(10**5000)+1"
    elif family == "mersenne":
        assert packet["info"]["metrics"]["width"] == packet["index"]


@pytest.mark.parametrize(
    "family", (FamilyId.FERMAT, FamilyId.MERSENNE, FamilyId.ANTIHYDRA)
)
def test_compact_symbolic_value_keeps_power10_selector(
    family: FamilyId,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.api import symbolic_terms

    monkeypatch.setattr(symbolic_terms, "integer_text", forbidden)
    exponent = "2" if family == "antihydra" else "5000"
    assert (
        cli.main([family.value, "--nth-power10", exponent, "--format", "symbolic"]) == 0
    )
    text = capsys.readouterr().out
    assert f"10^{exponent}" in text and len(text) < 100


def test_projected_symbolic_constructor_keyword_remains_supported() -> None:
    from number_compiler.api.number_api import ProjectedNumberTerm

    term = NumberCompiler().project(FermatTermQuery(1))
    copied = ProjectedNumberTerm(
        family=term.family,
        index=term.index,
        parameter=term.parameter,
        source_radix=term.source_radix,
        symbolic="explicit description",
        payload=term.payload,
        metrics=term.metrics,
    )
    assert copied.symbolic == "explicit description"
    assert copied.index == 1 and copied.materialize() == 5


@pytest.mark.parametrize(
    "family,expected",
    (
        ("a367620", "A367620[1]"),
        ("reverse-add", "reverse_add(seed=27,base=10)[1]"),
        ("collatz", "collatz(seed=27)[1]"),
        ("prime", "prime_at_or_after(start=2)[1]"),
        ("fermat", "2^(2^1)+1"),
        ("mersenne", "2^1-1"),
        ("antihydra", "antihydra_arithmetic(source=blank)[1]"),
    ),
)
def test_ordinary_symbolic_text_remains_unchanged(
    family: FamilyId,
    expected: str,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [family, "--nth", "1", *family_options(family), "--format", "symbolic"]
        )
        == 0
    )
    assert capsys.readouterr().out == expected + "\n"


def test_index_budget_covers_explicit_event_coordinates() -> None:
    with pytest.raises(ValueError, match="--max-index-bits"):
        cli_requests.parse_request(
            [
                "collatz",
                "--events",
                "4",
                "--seed",
                "27",
                "--info",
                "temporal.clock",
                "--max-index-bits",
                "2",
            ]
        )


def test_verification_rejects_index_budget_as_a_term_option() -> None:
    with pytest.raises(ValueError, match="term options"):
        cli_requests.parse_request(
            [
                "antihydra",
                "--verify-nonhalting",
                "certificate.json",
                "--max-index-bits",
                "32",
            ]
        )


@pytest.mark.parametrize("family", CAPABILITIES)
def test_compact_information_only_never_renders(
    family: FamilyId,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(cli_render, "render_value", forbidden)
    assert (
        cli.main(
            [
                family.value,
                "--nth-power10",
                "0",
                *family_options(family),
                "--no-value",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    assert packet["info"]["metrics"]["index"] == {"encoding": "power10", "exponent": 0}


def test_large_compact_unresolved_diagnostics_keep_index_encoded(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    def unresolved(self: NumberCompiler, query: TermQuery) -> Never:
        assert type(query.index) is int and query.index == 10**5000
        raise UnresolvedSequenceTerm(
            query.index, 1, "test-certificate", "outside prefix"
        )

    monkeypatch.setattr(NumberCompiler, "project", unresolved)
    monkeypatch.setattr(cli_render, "render_value", forbidden)
    assert cli.main(["a367620", "--nth-power10", "5000", "--format", "json"]) == 3
    captured = capsys.readouterr()
    packet = json.loads(captured.out)
    encoded = {"encoding": "power10", "exponent": 5000}
    assert packet["index"] == packet["error"]["requested_index"] == encoded
    assert len(captured.out) < 500 and captured.err == ""


def test_compact_metadata_only_preserves_unresolved_comma_boundary(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(cli_render, "render_value", forbidden)
    assert (
        cli.main(
            [
                "a367620",
                "--nth-power10",
                "9",
                "--no-value",
                "--info",
                "safety.certificate",
                "--format",
                "json",
            ]
        )
        == 3
    )
    packet = json.loads(capsys.readouterr().out)
    encoded = {"encoding": "power10", "exponent": 9}
    assert packet["index"] == packet["error"]["requested_index"] == encoded
    assert packet["info"]["safety.certificate"]["requested_index"] == encoded


def test_compact_presentation_does_not_rewrite_equal_arithmetic_values() -> None:
    from number_compiler.api.json_output import json_integers

    request = cli_requests.parse_request(
        ["antihydra", "--nth-power10", "2", "--format", "symbolic"]
    )
    assert request is not None
    packet = json_integers(
        {"index": request.presentation_index, "value": {"h": 100, "parameter": 100}}
    )
    assert packet == {
        "index": {"encoding": "power10", "exponent": 2},
        "value": {"h": 100, "parameter": 100},
    }


@pytest.mark.parametrize(
    "argv,message",
    (
        (
            [
                "collatz",
                "--nth-power10",
                "1",
                "--seed",
                "27",
                "--info",
                "temporal.clock",
                "--temporal-clock-max-events",
                "1",
            ],
            "physical clock observation budget",
        ),
        (
            [
                "fermat",
                "--nth-power10",
                "1",
                "--no-value",
                "--info",
                "number-theory.primality",
                "--max-candidate-bits",
                "16",
            ],
            "max_candidate_bits",
        ),
        (
            [
                "mersenne",
                "--nth-power10",
                "0",
                "--no-value",
                "--info",
                "number-theory.primality",
            ],
            "special theorem parameter",
        ),
        (["reverse-add", "--nth-power10", "0"], "requires --seed"),
        (["antihydra", "--nth-power10", "0", "--no-value"], "require --info"),
    ),
)
def test_compact_queries_preserve_family_admission(
    argv: list[str],
    message: str,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(cli, "NumberCompiler", forbidden)
    assert cli.main(argv) == 2
    assert message in capsys.readouterr().err


def test_compact_info_metadata_is_centralized_in_query_context(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    request = cli_requests.parse_request(
        ["antihydra", "--nth-power10", "1", "--no-value", "--info", "safety.ledger"]
    )
    assert request is not None

    def observation(self: cli_context.QueryContext, name: str) -> dict[str, object]:
        return {"requested_returns": 10, "value": 10}

    monkeypatch.setattr(cli_context.QueryContext, "_observe", observation)
    packet = cli_context.QueryContext(request, NumberCompiler()).information()[
        "safety.ledger"
    ]
    encoded = {"encoding": "power10", "exponent": 1}
    assert packet["index"] == encoded
    assert packet["requested_returns"] == 10
    assert packet["value"] == 10
