"""Bounded palindrome events through the public parser and execution owners."""

import json

import pytest

from number_compiler.api import (
    FirstPalindromeQuery,
    NumberCompiler,
    ReverseAddTermQuery,
)
from number_compiler.api.cli import main


@pytest.mark.parametrize(
    ("family", "seed", "horizon", "arrival"),
    (
        ("reverse-add", 92, 1, 1),
        ("reverse-add", 98, 1, None),
        ("reverse-add", 196, 0, None),
        ("2rev10", 0, 1, 1),
        ("2rev10", 22, 0, None),
        ("2rev10", 903939, 64, None),
    ),
)
def test_positive_generation_interval(
    capsys: pytest.CaptureFixture[str],
    family: str,
    seed: int,
    horizon: int,
    arrival: int | None,
) -> None:
    assert (
        main(
            [
                family,
                "--seed",
                str(seed),
                "--first-palindrome-within",
                str(horizon),
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["info"]["first-palindrome-within"] == {
        "first_generation": arrival,
        "searched_through": horizon if arrival is None else arrival,
    }
    assert packet.get("error") is None


def test_source_budget_refusal_and_decimal_admission() -> None:
    assert (
        main(
            [
                "2rev10",
                "--seed",
                "7",
                "--first-palindrome-within",
                "10",
                "--max-steps",
                "0",
            ]
        )
        == 2
    )
    assert (
        main(
            [
                "reverse-add",
                "--seed",
                "7",
                "--first-palindrome-within",
                "0",
                "--base",
                "2",
            ]
        )
        == 2
    )
    query = FirstPalindromeQuery(ReverseAddTermQuery(0, seed=29), 1)
    assert NumberCompiler().first_palindrome(query) == 1


def test_long_search_can_finish_before_prefix_budget(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(["reverse-add", "--seed", "92", "--first-palindrome-within", "1000000"])
        == 0
    )
    assert capsys.readouterr().out.strip() == "1"


def test_partial_interval_stays_unresolved(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.sequences.reverse_add import q19_event_spans

    monkeypatch.setattr(q19_event_spans, "DEFAULT_EVENT_STEP_BUDGET", 4)
    assert (
        main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--first-palindrome-within",
                "5",
                "--format",
                "json",
            ]
        )
        == 3
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    assert packet["error"]["certified_max_index"] == 4
    assert not packet["info"]


def test_uncached_search_disposes_issuer_on_cancellation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.api import DoubleReverseTermQuery
    from number_compiler.sequences.double_reverse.power import DoubleReverseTerm

    terms: list[DoubleReverseTerm] = []

    def cancel(term: DoubleReverseTerm, horizon: int) -> int:
        terms.append(term)
        raise KeyboardInterrupt

    monkeypatch.setattr(DoubleReverseTerm, "first_palindrome_within", cancel)
    query = FirstPalindromeQuery(DoubleReverseTermQuery(0, seed=17), 6)
    with pytest.raises(KeyboardInterrupt):
        NumberCompiler(max_cached_terms=0).first_palindrome(query)
    assert len(terms) == 1
    with pytest.raises(ValueError, match="disposed|closed"):
        terms[0].check_open()
