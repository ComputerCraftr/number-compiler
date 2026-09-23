"""Production connectivity of the shared source-bound execution owner."""

import json
from collections.abc import Hashable

import pytest

from number_compiler.api import cli
from number_compiler.api.number_api import NumberCompiler
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageView,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicAggregateSummary,
)
from number_compiler.sequences.collatz.physical_images import (
    CollatzPhysicalImageWorkspace,
)
from number_compiler.sequences.prime.select import PrimePrefixRank
from number_compiler.sequences.prime.successor_action import (
    PrimeSuccessorImageAdapter,
)


@pytest.mark.parametrize(
    "steps,expected", ((999999, "1"), (1000000, "4"), (10**12, "4"))
)
def test_public_collatz_cycle_uses_safety_transformer_after_exact_entry(
    steps: int,
    expected: str,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    original = CollatzPhysicalImageWorkspace.saturated_summary
    counters: list[dict[str, int]] = []

    def observed(self: CollatzPhysicalImageWorkspace) -> DyadicAggregateSummary:
        result = original(self)
        counters.append(dict(self.ledger.counters))
        return result

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("public cycle query entered causal execution")

    monkeypatch.setattr(CollatzPhysicalImageWorkspace, "saturated_summary", observed)
    monkeypatch.setattr(CausalTileEngine, "__init__", forbidden)
    assert cli.main(["collatz", "--seed", "27", "--nth", str(steps)]) == 0
    output = capsys.readouterr()
    assert output.out.strip() == expected
    assert not output.err
    assert counters
    assert counters[-1]["collatz_physical_cycle_safety_transformer_applications"] > 0
    assert counters[-1]["collatz_physical_leaf_steps"] <= 128
    assert counters[-1].get("tile_causal_frames", 0) == 0


def test_prime_cli_consumes_shared_source_images(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    original = TileScheduler.source_image_demanded
    demands: list[tuple[str, SourceImageDemand]] = []
    filters: list[int] = []
    original_filter = PrimeSuccessorImageAdapter.apply_composite

    def filtered(
        self: PrimeSuccessorImageAdapter,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand,
    ) -> SourceImageCandidate | None:
        result = original_filter(self, action, source, demand)
        filters.append(self.ledger.counters.get("prime_partial_successor_filters", 0))
        return result

    def retired(*args: object, **kwargs: object) -> int:
        raise AssertionError("prime CLI delegated to retired rank wrapper")

    def traced(
        self: TileScheduler,
        adapter: SourceBoundImageAdapter,
        source: Hashable,
        action: Hashable,
        demand: SourceImageDemand,
    ) -> SourceImageID:
        result = original(self, adapter, source, action, demand)
        demands.append((adapter.family, demand))
        return result

    NumberCompiler().clear_shared_cache()
    monkeypatch.setattr(TileScheduler, "source_image_demanded", traced)
    monkeypatch.setattr(PrimeSuccessorImageAdapter, "apply_composite", filtered)
    monkeypatch.setattr(PrimePrefixRank, "count_leq", retired)
    assert (
        cli.main(
            [
                "prime",
                "--nth",
                "100",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    captured = capsys.readouterr()
    packet = json.loads(captured.out)
    assert packet["value"] == "547"
    assert captured.err == ""
    assert demands, "prime CLI bypassed the common source-image executor"
    assert all(family.startswith("prime") for family, _demand in demands)
    assert all(demand.name == "rank-before" for _family, demand in demands)
    assert filters and max(filters) > 0, "CLI never applied the fresh-prime filter"
    metrics = packet["info"]["metrics"]
    assert metrics["prime_scheduler_work"] > 0
    assert metrics["prime_scheduler_peak_entries"] > 0
    counters = metrics["prime_scheduler_counters"]
    assert counters["prime_partial_successor_filters"] == max(filters)
    assert counters["source_image_demanded_composite_applications"] == max(filters)
    assert counters["source_image_seal_creation_visits"] > 0
    assert counters["source_image_seal_validation_visits"] > 0
    assert counters["source_image_workspace_peak"] > 0
    assert metrics["prime_scheduler_metrics_scope"] == "query_before_disposal"


def test_special_digits_leave_classification_unrequested(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("term-only query requested special classification")

    monkeypatch.setattr(
        CanonicalSequenceCompiler,
        "resolve_special_theorem",
        forbidden,
    )
    assert cli.main(["fermat", "--nth", "4"]) == 0
    assert capsys.readouterr().out.strip() == "65537"
    assert cli.main(["mersenne", "--nth", "13"]) == 0
    assert capsys.readouterr().out.strip() == "8191"
