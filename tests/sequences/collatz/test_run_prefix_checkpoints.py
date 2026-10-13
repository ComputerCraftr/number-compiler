from number_compiler.sequences.collatz.run_prefix_checkpoints import (
    _checkpoint_widths,
    _crosses_root_checkpoint,
)


def test_checkpoint_widths_start_at_the_next_root_power() -> None:
    assert _checkpoint_widths(0, 64, 32) == (8, 16, 32)
    assert _checkpoint_widths(7, 1, 8) == (8,)
    assert _checkpoint_widths(8, 8, 16) == (16,)
    assert _checkpoint_widths(16, 8, 16) == ()


def test_checkpoint_predicate_respects_block_and_source_bounds() -> None:
    assert _crosses_root_checkpoint(8, 8, 16)
    assert not _crosses_root_checkpoint(8, 0, 16)
    assert not _crosses_root_checkpoint(16, 64, 16)
    assert not _crosses_root_checkpoint(8, 8, 8)


def test_huge_start_skips_checkpoint_search_without_linear_doubling() -> None:
    huge_start = 1 << 100_000

    assert _checkpoint_widths(huge_start, huge_start, 128) == ()
    assert not _crosses_root_checkpoint(huge_start, huge_start, 128)
