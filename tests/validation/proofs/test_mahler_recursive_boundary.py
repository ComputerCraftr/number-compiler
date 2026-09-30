"""Bounded independent checks of the recursive Mahler interval boundary.

These exercise live source cylinders, not the downloaded recursive compiler,
and establish neither its construction cost nor an all-width crossing theorem.
"""

from fractions import Fraction

from devtools.experiments.antihydra.source_safety import SourceSafetyWorkspace
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational as Q
from number_compiler.resources.ledger import ResourceLedger


def test_source_cap_cancellation_and_nested_zero_tail_boundaries() -> None:
    workspace = SourceSafetyWorkspace(
        ResourceLedger(max_nodes=50_000, max_cache_entries=50_000), max_width=32
    )
    survivors: dict[int, list[int]] = {8: [], 16: [], 32: []}
    try:
        for source in range(1, 256):
            target = source
            cap: Fraction | None = None
            previous: tuple[Q, Q] | None = None
            for width in range(1, 33):
                epsilon = target % 2
                local_cap = Fraction(9 if epsilon == 0 else 3, 4)
                cap = (
                    local_cap
                    if cap is None
                    else min(local_cap, Fraction(3, 2) * (cap - epsilon))
                )
                target = (3 * target + 1) // 2
                if width not in survivors:
                    continue
                block = workspace.view(workspace.cylinder(width, source))
                scale = Q(3**width, 1 << width)
                assert block.endpoint == target
                assert block.predicate_action.scale == scale
                assert block.predicate_action.offset == (
                    Q(3) * scale * Q(source) - Q(3 * target)
                )
                assert block.predicate_action.cap == Q(cap.numerator, cap.denominator)
                lower = Q(3 * target) / scale
                upper = (Q(cap.numerator, cap.denominator) + Q(3 * target)) / scale
                assert (lower < upper) == (not block.predicate_state.forbidden)
                if previous is not None:
                    assert previous[0] <= lower
                    assert upper <= previous[1]
                previous = lower, upper
                if lower < upper:
                    survivors[width].append(source)
        assert len(survivors[8]) == 39
        assert survivors[16] == [53, 80, 120, 149, 180, 224]
        assert survivors[32] == []
    finally:
        workspace.close()
