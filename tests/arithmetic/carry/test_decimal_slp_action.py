"""Independent digit-wise checks for compressed decimal carry actions."""

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.carry.decimal_slp_action import multiply_decimal_slp
from number_compiler.resources.ledger import ResourceLedger


@pytest.mark.parametrize("multiplier", (2, 5))
@pytest.mark.parametrize("copies", (0, 1, 2, 7, 18))
def test_all_inlet_compressed_block_matches_scalar(
    multiplier: int, copies: int
) -> None:
    ledger = ResourceLedger()
    scratch = ledger.register("decimal-action-scratch", "workspace")
    arena = LedgerSLPArena(ledger, "decimal-action", "arithmetic")
    head, tile, tail = (9, 0), (1, 8, 3), (9, 9)
    try:
        root = arena.concat_many(
            (arena.word(head), arena.repeat(arena.word(tile), copies), arena.word(tail))
        )
        action = multiply_decimal_slp(arena, root, multiplier, ledger, scratch)
        for inlet in range(multiplier):
            carry = inlet
            expected: list[int] = []
            for digit in head + tile * copies + tail:
                carry, emitted = divmod(multiplier * digit + carry, 10)
                expected.append(emitted)
            output, exit_carry = action.resolve(arena, inlet)
            assert exit_carry == carry
            assert arena.materialize(output) == tuple(expected)
        assert ledger.account_usage(scratch) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(scratch)
    assert ledger.nodes == ledger.entries == 0


def test_decimal_action_refuses_large_repeat_and_releases_scratch() -> None:
    ledger = ResourceLedger()
    scratch = ledger.register("decimal-limit-scratch", "workspace")
    arena = LedgerSLPArena(ledger, "decimal-limit", "arithmetic")
    try:
        root = arena.repeat(arena.word((1, 2, 3)), 2**20)
        previous = len(arena.nodes), ledger.entries, ledger.nodes
        with pytest.raises(ValueError, match="power budget"):
            multiply_decimal_slp(arena, root, 2, ledger, scratch, max_power_bits=8)
        assert (len(arena.nodes), ledger.entries, ledger.nodes) == previous
        assert ledger.account_usage(scratch) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(scratch)
    assert ledger.nodes == ledger.entries == 0


def test_decimal_action_rejects_foreign_and_stale_arena() -> None:
    ledger = ResourceLedger()
    scratch = ledger.register("decimal-authority-scratch", "workspace")
    arena = LedgerSLPArena(ledger, "decimal-authority", "arithmetic")
    foreign = LedgerSLPArena(ledger, "decimal-foreign", "arithmetic")
    try:
        root = arena.word((9, 8, 3))
        checkpoint = len(arena.nodes)
        action = multiply_decimal_slp(arena, root, 2, ledger, scratch)
        output, carry = action.resolve(arena, 0)
        assert output >= 0 and carry in (0, 1)
        with pytest.raises(ValueError, match="another arena"):
            action.resolve(foreign, 0)
        arena.rollback_unpublished_suffix(checkpoint)
        with pytest.raises(ValueError, match="stale"):
            action.resolve(arena, 0)
    finally:
        arena.dispose()
        foreign.dispose()
        ledger.mark_disposed(scratch)


def test_decimal_action_survives_unrelated_rollback_but_rejects_reused_source_id() -> (
    None
):
    ledger = ResourceLedger()
    scratch = ledger.register("decimal-rollback-scratch", "workspace")
    arena = LedgerSLPArena(ledger, "decimal-rollback", "arithmetic")
    try:
        root = arena.word((1, 2, 3))
        action = multiply_decimal_slp(arena, root, 2, ledger, scratch)
        expected = tuple(action.resolve(arena, inlet) for inlet in range(2))
        checkpoint = len(arena.nodes)
        arena.terminal(97)

        def fail_removal(_node: int) -> None:
            raise RuntimeError("injected removal failure")

        with pytest.raises(RuntimeError, match="injected removal failure"):
            arena.rollback_unpublished_suffix(checkpoint, before_remove=fail_removal)
        assert tuple(action.resolve(arena, inlet) for inlet in range(2)) == expected
        arena.rollback_unpublished_suffix(checkpoint)
        assert tuple(action.resolve(arena, inlet) for inlet in range(2)) == expected

        checkpoint = len(arena.nodes)
        temporary_source = arena.word((8, 8, 8, 8, 8))
        temporary_action = multiply_decimal_slp(
            arena, temporary_source, 5, ledger, scratch
        )
        arena.rollback_unpublished_suffix(checkpoint)
        replacement = arena.word((8, 8, 8, 8, 8))
        assert replacement == temporary_source
        with pytest.raises(ValueError, match="stale after source reclamation"):
            temporary_action.resolve(arena, 0)
        assert tuple(action.resolve(arena, inlet) for inlet in range(2)) == expected
        assert ledger.account_usage(scratch) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(scratch)
