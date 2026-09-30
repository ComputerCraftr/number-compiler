"""Public comparison evidence retains every route and never conceals disagreement."""

import pytest

from devtools.benchmarks.public_query_comparison import Sample, compare


def test_public_routes_agree_and_warm_priming_is_retained() -> None:
    rows = compare("collatz", [0, 2], 1, ["cold", "warm", "bypass"], seed=27)
    assert len(rows) == 24
    assert sum(row["phase"] == "priming" for row in rows) == 6
    assert {row["route"] for row in rows} == {"cli", "point"}
    for row in rows:
        expected = 27 if row["horizon"] == 0 else 41
        if row["route"] == "cli":
            assert int(row["value"], row["output_base"]) == expected
        else:
            assert int(row["value"]) == (expected >> 2) & 1


def test_mismatched_cli_sample_is_retained_before_rejection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.benchmarks import public_query_comparison as module

    def wrong(arguments: list[str], *, fresh: bool) -> tuple[float, dict[str, object]]:
        return 0.01, {"value": "0", "info": {"metrics": None}}

    monkeypatch.setattr(module, "cli_sample", wrong)
    retained: list[Sample] = []
    with pytest.raises(AssertionError, match="CLI output differs"):
        compare("collatz", [0], 1, ["bypass"], seed=27, on_sample=retained.append)
    assert len(retained) == 1
    assert retained[0]["value"] == "0"
