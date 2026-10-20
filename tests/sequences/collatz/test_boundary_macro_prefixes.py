"""Algebraic source-cylinder publication from guarded Collatz boundary words."""

from number_compiler.hashlife.execution.dyadic_return_runs import (
    RunArithmeticWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_identity import ENTRY_421
from number_compiler.sequences.collatz.boundary_macro_prefixes import (
    publish_boundary_macro_prefixes,
    root_prefix_widths,
)
from number_compiler.sequences.collatz.boundary_macros import select_boundary_macro
from number_compiler.sequences.collatz.source_cylinder_cache import (
    CollatzDyadicMacros,
)


def _normalized_step(value: int) -> int:
    return (3 * value + 1) // 2 if value & 1 else value // 2


def _normalized_endpoint(source: int, width: int) -> tuple[int, int]:
    odd_symbols = 0
    for _ in range(width):
        odd_symbols += source & 1
        source = _normalized_step(source)
    return source, odd_symbols


def _macro_sources() -> tuple[tuple[int, int], ...]:
    # Each source has enough exact 2-adic guard for at least D16.
    quiet = 4 + 40 * (1 << 40)
    inverse_five = pow(5, -1, 1 << 40)
    growth = 40 * ((-2 * inverse_five) % (1 << 40)) + 14
    forced_zero = 20 * ((1 << 20) - 1) // 3 + 6
    odd_run = 5 * (1 << 40) - 1
    return ((quiet, 31), (growth, 41), (forced_zero, 23), (odd_run, 40))


def test_each_boundary_family_publishes_exact_dyadic_prefixes() -> None:
    for source, ticks in _macro_sources():
        ledger = ResourceLedger()
        scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
        macros = CollatzDyadicMacros(ledger, shared_cache=False)
        try:
            with scratch.scope():
                macro = select_boundary_macro(source, ticks)
                assert macro is not None
                count = publish_boundary_macro_prefixes(
                    macro,
                    macros,
                    scratch,
                    anchor=source,
                    normalized_offset=0,
                    odd_offset=0,
                )
            assert count >= 2
            width = 8
            while width <= macro.normalized_symbols:
                expected, odd_symbols = _normalized_endpoint(source, width)
                cell = macros.lookup(source, width)
                assert cell is not None
                assert cell.odd_symbols == odd_symbols
                assert cell.apply(source) == expected
                width *= 2
            assert (
                macro.endpoint
                == _normalized_endpoint(source, macro.normalized_symbols)[0]
            )
        finally:
            macros.__exit__(None, None, None)


def test_boundary_macro_chunks_join_a_prior_root_prefix() -> None:
    # Seven zero steps and one odd step end exactly at a long 421 source.
    macro_source = 4 + 40 * (1 << 130)
    odd_predecessor = (2 * macro_source - 1) // 3
    assert odd_predecessor & 1
    anchor = odd_predecessor << 7
    ticks = 3 * 65 + 1
    macro = select_boundary_macro(macro_source, ticks)
    assert macro is not None and macro.identity == ENTRY_421
    assert macro.normalized_symbols >= 128

    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    macros = CollatzDyadicMacros(ledger, shared_cache=False)
    try:
        macros.observe(anchor, 8, 1, macro_source, anchor=anchor)
        with scratch.scope():
            count = publish_boundary_macro_prefixes(
                macro,
                macros,
                scratch,
                anchor=anchor,
                normalized_offset=8,
                odd_offset=1,
            )
        assert count >= 1  # Crossed global root powers are retained directly.
        cell = macros.lookup(anchor, 128)
        assert cell is not None
        expected, odd_symbols = _normalized_endpoint(anchor, 128)
        assert cell.odd_symbols == odd_symbols
        assert cell.apply(anchor) == expected
    finally:
        macros.__exit__(None, None, None)


def test_short_unobserved_macro_prefix_breaks_frontier_adjacency() -> None:
    macro_source = 4 + 40 * (1 << 40)
    anchor = macro_source << 11
    macro = select_boundary_macro(macro_source, 31)
    assert macro is not None and macro.identity == ENTRY_421

    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    macros = CollatzDyadicMacros(ledger, shared_cache=False)
    try:
        macros.observe(anchor, 8, 0, anchor >> 8, anchor=anchor)
        joins_before = ledger.counters.get(
            "collatz_hashlife_occurrence_frontier_joins", 0
        )
        with scratch.scope():
            publish_boundary_macro_prefixes(
                macro,
                macros,
                scratch,
                anchor=anchor,
                normalized_offset=11,
                odd_offset=0,
            )
        cell = macros.lookup(anchor, 16)
        assert cell is not None
        expected, ones = _normalized_endpoint(anchor, 16)
        assert cell.odd_symbols == ones
        assert cell.apply(anchor) == expected
        assert (
            ledger.counters.get("collatz_hashlife_occurrence_frontier_joins", 0)
            == joins_before
        )
    finally:
        macros.__exit__(None, None, None)


def test_global_checkpoint_includes_width_eight_after_short_prefix() -> None:
    macro_source = 4 + 40 * (1 << 40)
    anchor = macro_source << 1
    macro = select_boundary_macro(macro_source, 31)
    assert macro is not None and macro.identity == ENTRY_421

    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    macros = CollatzDyadicMacros(ledger, shared_cache=False)
    try:
        assert _normalized_endpoint(anchor, 1)[0] == macro_source
        with scratch.scope():
            count = publish_boundary_macro_prefixes(
                macro,
                macros,
                scratch,
                anchor=anchor,
                normalized_offset=1,
                odd_offset=0,
            )
        assert count >= 1
        expected, odd_symbols = _normalized_endpoint(anchor, 8)
        cell = macros.lookup(anchor, 8)
        assert cell is not None
        assert cell.odd_symbols == odd_symbols
        assert cell.apply(anchor) == expected
    finally:
        macros.__exit__(None, None, None)


def testroot_prefix_widths_never_exceed_the_anchor_bit_cap() -> None:
    huge_macro_width = 1 << 100_000

    assert root_prefix_widths(huge_macro_width, 65) == (8, 16, 32, 64)
    assert root_prefix_widths(huge_macro_width, 7) == ()
