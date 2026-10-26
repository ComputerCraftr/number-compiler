"""Differential checks for the root-balanced and generic Antihydra producers."""

from __future__ import annotations

from collections.abc import Hashable

import pytest

from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageCandidate,
    SourceImageView,
)
from number_compiler.sequences.antihydra.arithmetic_images import (
    AntihydraArithmeticImageWorkspace as Workspace,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm


def _certified_result(n: int) -> tuple[int, int, int, int | None]:
    result = AntihydraArithmeticTerm(n, shared_cache=False).result()
    result.require_source()
    return (result.h, result.balance, result.minimum, result.first_failure_index)


def test_root_balanced_producer_matches_generic_composite_issuer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Force the generic composite route as an independent oracle; do not
    # compare the root producer with itself through its public result wrapper.
    lengths = (17, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1023, 1024, 2047, 2048)
    fast = {n: _certified_result(n) for n in lengths}

    def use_generic_composite(
        self: Workspace,
        action: Hashable,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        return DyadicReturnImageWorkspace.complete_composite_candidate(
            self, action, source
        )

    def no_macro(_self: Workspace, _action: Hashable, _source: SourceImageView) -> None:
        return None

    monkeypatch.setattr(Workspace, "_try_odd_macro_candidate", no_macro)
    monkeypatch.setattr(Workspace, "_balanced_root_candidate", use_generic_composite)
    for n in lengths:
        assert fast[n] == _certified_result(n), n


def test_large_exact_roots_publish_shared_balanced_effect_directly(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(
        self: Workspace, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        raise AssertionError("main nth scheduler opened the generic composite path")

    monkeypatch.setattr(Workspace, "complete_composite_candidate", forbidden)
    term = AntihydraArithmeticTerm(3072, shared_cache=False)
    result = term.result()
    result.require_source()
    assert result.h > 0
    counters = term.ledger.counters
    assert (
        counters.get("antihydra_arithmetic_balanced_effect_requests", 0) > 0
        or counters.get("antihydra_arithmetic_temporal_odd_macro_repetitions", 0) > 0
    )
    assert (
        term.ledger.counters.get("antihydra_arithmetic_composite_cutover_chunks", 0)
        == 0
    )
