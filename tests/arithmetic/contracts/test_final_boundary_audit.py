import tracemalloc
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
    ExactSource,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.lazy_compiler import (
    LazyCompiler,
    ProgramComposition,
)
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger


def test_source_tile_rejects_oversized_level_without_expanding_its_power() -> None:
    ledger = ResourceLedger()
    geometry = SourceGeometry(ledger, ExactSource((1,), 2, "collatz", 2, 1))
    geometry.span((1,), 2, 1)
    assert geometry.tile_at(0, 0) is not None
    before = ledger.snapshot()
    tracemalloc.start()
    try:
        assert geometry.tile_at(0, 1_000_000) is None
        _, peak = tracemalloc.get_traced_memory()
    finally:
        tracemalloc.stop()
    assert peak < 64_000
    assert ledger.snapshot() == before


@pytest.mark.parametrize("start,level", [(True, 0), (0, True), (0.0, 0), (0, "1")])
def test_source_tile_rejects_noninteger_geometry_before_lookup(
    start: bool | float | int, level: bool | int | str
) -> None:
    ledger = ResourceLedger()
    geometry = SourceGeometry(ledger, ExactSource((1,), 2, "collatz", 2, 1))
    geometry.span((1,), 2, 1)
    before = ledger.snapshot()
    with pytest.raises(TypeError, match="integers"):
        geometry.tile_at(cast("int", start), cast("int", level))
    assert ledger.snapshot() == before


def test_source_tile_preserves_aligned_subtrees_and_exterior_queries() -> None:
    ledger = ResourceLedger()
    geometry = SourceGeometry(ledger, ExactSource((1, 0, 1, 0), 2, "collatz", 2, 8))
    geometry.span((1, 0, 1, 0), 2, 8)
    assert geometry.tile_at(0, 1) is geometry.tile_at(2, 1)
    assert geometry.read(0) == 1
    assert geometry.read(5) == 2
    before = ledger.snapshot()
    for start, level in ((-1, 0), (0, -1), (1, 1), (8, 0), (0, 4)):
        assert geometry.tile_at(start, level) is None
    assert ledger.snapshot() == before


@pytest.mark.parametrize("warm", [False, True])
def test_mixed_alphabet_program_rejected_before_retaining_any_runtime(
    warm: bool,
) -> None:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    if warm:
        valid = compiler.compose(BaseBlockEffect(10), DigitNormalizeBlockEffect(10))
        HashLifeBlockIndex(
            valid, (2, 2), logical_length=8, ledger=ledger, compiler=compiler
        )
    handle = ActionProgramID(ArenaToken(), "action-program", 0)
    malformed = ProgramComposition(
        BaseBlockEffect(10), DigitNormalizeBlockEffect(2), handle
    )
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="mixed alphabets"):
        compiler.import_effect(malformed)
    assert ledger.snapshot() == before
