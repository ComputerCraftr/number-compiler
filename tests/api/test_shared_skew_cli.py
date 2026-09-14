"""Production connectivity of the shared source-bound execution owner."""

from collections.abc import Hashable
import json

import pytest

from number_compiler.api import cli
from number_compiler.api.number_api import NumberCompiler
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
    SourceBoundSchedulerCore,
    SourceImageID,
)
from number_compiler.sequences.prime.partial_successor_image import (
    PrimePartialSuccessorAdapter,
)
from number_compiler.sequences.prime.select import PrimePrefixRank


def test_prime_cli_consumes_shared_source_images(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str],
) -> None:
    original = SourceBoundSchedulerCore.apply
    families: list[str] = []
    filters: list[int] = []
    original_filter = PrimePartialSuccessorAdapter.apply_primitive

    def filtered(
        self: PrimePartialSuccessorAdapter, action: Hashable,
        source: object,
    ) -> object:
        from number_compiler.hashlife.execution.source_bound_images import SourceImageView

        assert isinstance(source, SourceImageView)
        result = original_filter(self, action, source)
        filters.append(self.ledger.counters.get("prime_partial_successor_filters", 0))
        return result

    def retired(*args: object, **kwargs: object) -> int:
        raise AssertionError("prime CLI delegated to retired rank wrapper")

    def traced(
        self: SourceBoundSchedulerCore, adapter: SourceBoundImageAdapter,
        source: Hashable, action: Hashable,
    ) -> SourceImageID:
        result = original(self, adapter, source, action)
        families.append(adapter.family)
        return result

    NumberCompiler().clear_shared_cache()
    monkeypatch.setattr(SourceBoundSchedulerCore, "apply", traced)
    monkeypatch.setattr(PrimePartialSuccessorAdapter, "apply_primitive", filtered)
    monkeypatch.setattr(PrimePrefixRank, "count_leq", retired)
    assert cli.main([
        "prime", "--nth", "100", "--info", "metrics", "--format", "json",
    ]) == 0
    captured = capsys.readouterr()
    packet = json.loads(captured.out)
    assert packet["value"] == "547"
    assert captured.err == ""
    assert families, "prime CLI bypassed the common source-image executor"
    assert all(family.startswith("prime") for family in families)
    assert filters and max(filters) > 0, "CLI never applied the fresh-prime filter"
    metrics = packet["info"]["metrics"]
    assert metrics["prime_scheduler_work"] > 0
    assert metrics["prime_scheduler_peak_entries"] > 0
    counters = metrics["prime_scheduler_counters"]
    assert counters["prime_partial_successor_filters"] == max(filters)
    assert counters["source_image_primitive_applications"] == max(filters)
    assert counters["source_image_seal_creation_visits"] > 0
    assert counters["source_image_seal_validation_visits"] > 0
    assert counters["source_image_workspace_peak"] > 0
    assert metrics["prime_scheduler_metrics_scope"] == "query_before_disposal"


def test_special_digits_leave_classification_unrequested(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("term-only query requested special classification")

    monkeypatch.setattr(
        CanonicalSequenceCompiler, "resolve_special_theorem", forbidden,
    )
    assert cli.main(["fermat", "--nth", "4"]) == 0
    assert capsys.readouterr().out.strip() == "65537"
    assert cli.main(["mersenne", "--nth", "13"]) == 0
    assert capsys.readouterr().out.strip() == "8191"
