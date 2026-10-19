"""Differential proof checks for finite exact-run producer dispatch."""

from __future__ import annotations

from collections.abc import Hashable

import pytest

from number_compiler.hashlife.execution.dyadic_return_images import DyadicReturnActionID
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageCandidate,
    SourceImageView,
)
from number_compiler.sequences.antihydra.arithmetic_images import (
    AntihydraArithmeticImageWorkspace as Workspace,
)
from number_compiler.sequences.antihydra.mahler_odd_source_transfer import (
    MahlerOddMacroSelection,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm


def _certified_result(n: int) -> tuple[int, int, int, int | None]:
    result = AntihydraArithmeticTerm(n, shared_cache=False).result()
    result.require_source()
    return (result.h, result.balance, result.minimum, result.first_failure_index)


def test_exact_run_cold_producer_matches_balanced_issuer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # The reference is the prior certified balanced-residue producer, not a
    # second copy of the new digit recurrence implementation.
    lengths = (17, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1023, 1024, 2047, 2048)
    fast = {n: _certified_result(n) for n in lengths}
    original = Workspace._run_candidate

    def balanced_on_moderate_exact_root(
        self: Workspace,
        action: DyadicReturnActionID,
        source: SourceImageView,
        *,
        macro_selection: MahlerOddMacroSelection | None = None,
        scratch: RunArithmeticWorkspace | None = None,
        source_h: int | None = None,
    ) -> SourceImageCandidate:
        width = self.action_node(action).width
        if width > self.MAX_LEAF_STEPS:
            return self.complete_composite_candidate(action, source)
        return original(
            self,
            action,
            source,
            macro_selection=macro_selection,
            scratch=scratch,
            source_h=source_h,
        )

    monkeypatch.setattr(Workspace, "_run_candidate", balanced_on_moderate_exact_root)
    for n in lengths:
        assert fast[n] == _certified_result(n), n


def test_large_exact_roots_retain_old_balanced_limit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = Workspace.complete_composite_candidate
    # 3072 is inside the source budget but outside the new 2048-step bypass.
    seen: list[int] = []

    def observed(
        self: Workspace, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        assert isinstance(action, DyadicReturnActionID)
        seen.append(self.action_node(action).width)
        return original(self, action, source)

    monkeypatch.setattr(Workspace, "complete_composite_candidate", observed)
    result = _certified_result(3072)
    assert result[0] > 0
    assert 3072 in seen
