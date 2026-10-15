"""Source-authorized 6305 return/exit regression cases in Number Compiler 11."""

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_identity import (
    BorderEntryPort,
    BorderExitPort,
    BoundaryPathKind,
    GuardedBorderPath,
)
from number_compiler.sequences.collatz.border_return_grammar import (
    BorderReturnMacro,
    select_border_return_macro,
    validate_border_return_macro,
)
from number_compiler.sequences.collatz.innovation_carry_cocycle import (
    exact_source_symbol,
)
from number_compiler.sequences.collatz.innovation_port_moore import SIGNED_SYMBOLS
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)
from tests.support.collatz_finite_trace import physical_values


def _physical(source: int, ticks: int) -> tuple[int, list[int]]:
    values = physical_values(source, ticks)
    return values[-1], [value.bit_length() for value in values]


def _large_3adic_source(exponent: int) -> int:
    quotient = (-pow(3, -1, 1 << exponent)) % (1 << exponent)
    return 10 * (quotient + (1 << 120)) + 3


@pytest.mark.parametrize(
    "source,ticks,tails,exit_port,endpoint",
    (
        (6, 6, (0,), BorderExitPort.EIGHT_TO_FOUR, 4),
        (13, 7, (2,), BorderExitPort.EIGHT_TO_FOUR, 4),
        (23, 13, (0, 4), BorderExitPort.EIGHT_TO_FOUR, 4),
        (26, 8, (2,), BorderExitPort.EIGHT_TO_FOUR, 4),
        (43, 7, (0,), BorderExitPort.EIGHT_TO_NINE_TO_EIGHT, 74),
        (35, 11, (4,), BorderExitPort.EIGHT_TO_FOUR, 4),
    ),
)
def test_return_grammar_preserves_upper_border_and_full_action(
    source: int,
    ticks: int,
    tails: tuple[int, ...],
    exit_port: BorderExitPort,
    endpoint: int,
) -> None:
    macro = select_border_return_macro(source, ticks)
    assert macro is not None
    assert macro.identity.kind is BoundaryPathKind.THREE_BORDER_RETURN
    assert macro.zero_tails == tails
    assert macro.exit_port == exit_port
    assert macro.endpoint == endpoint
    assert macro.physical_ticks == ticks
    validate_border_return_macro(macro)
    assert _physical(source, ticks)[0] == endpoint
    assert sum(length for bit, length in macro.parts if bit) == macro.odd_symbols
    with pytest.raises(TypeError):
        BorderReturnMacro()


def test_upper_borrow_returns_until_it_exits_at_8() -> None:
    macro = select_border_return_macro(23, 13)
    assert macro is not None
    assert macro.returns == 1 and macro.zero_tails == (0, 4)
    # 23 -> 70 -> 35 -> 106 -> 53 is a border return.
    q = (23 - 3) // 10
    u = (3 * q + 1) >> macro.zero_tails[0]
    assert (3 * u - 1) // 4 == (53 - 3) // 10
    assert macro.exit_port is BorderExitPort.EIGHT_TO_FOUR


def test_return_uses_j_plus_four_physical_ticks_not_j_plus_two() -> None:
    # x=13 has q=1, 3*q+1=4=2**2*1.  T**(j+2) reaches 5*u=5;
    # two more physical steps reach (15*u+1)//2=8.
    source = 13
    j = 2
    macro = select_border_return_macro(source, j + 4)
    assert macro is not None
    assert macro.zero_tails == (j,)
    assert macro.normalized_symbols == j + 2
    assert macro.odd_symbols == 2
    assert macro.physical_ticks == j + 4
    assert macro.endpoint == (15 * 1 + 1) // 2
    assert _physical(source, j + 2)[0] == 5
    assert _physical(source, j + 4)[0] == macro.endpoint


@pytest.mark.parametrize(
    "source,j,endpoint",
    ((23, 0, 53), (33, 1, 38), (13, 2, 8), (133, 3, 38), (53, 4, 8)),
)
def test_each_completed_return_reports_both_clocks(
    source: int, j: int, endpoint: int
) -> None:
    macro = select_border_return_macro(source, j + 4)
    assert macro is not None
    assert macro.zero_tails == (j,)
    assert macro.endpoint == endpoint
    assert macro.return_physical_ticks == (j + 4,)
    assert macro.return_normalized_steps == (j + 2,)
    packet = macro.observation()
    assert packet["return_physical_ticks"] == (j + 4,)
    assert packet["return_normalized_steps"] == (j + 2,)
    assert _physical(source, j + 4)[0] == endpoint
    validate_border_return_macro(macro)


def test_composite_return_clock_excludes_entry_and_exit_steps() -> None:
    for source, physical, tails, return_ticks, return_steps, normalized in (
        (13, 7, (2,), (6,), (4,), 5),
        (23, 13, (0, 4), (4, 8), (2, 6), 9),
        (26, 8, (2,), (6,), (4,), 6),
        (43, 7, (0,), (4,), (2,), 4),
    ):
        macro = select_border_return_macro(source, physical)
        assert macro is not None
        assert macro.zero_tails == tails
        assert macro.physical_ticks == physical
        assert macro.normalized_symbols == normalized
        assert macro.return_physical_ticks == return_ticks
        assert macro.return_normalized_steps == return_steps
        assert physical >= sum(return_ticks)
        assert normalized >= sum(return_steps)


def test_demanded_boundary_observation_exposes_both_return_clocks() -> None:
    from number_compiler.sequences.collatz.boundary_observation import (
        observe_guarded_boundary,
    )

    macro = select_border_return_macro(23, 13)
    assert macro is not None
    packet = observe_guarded_boundary(23, (0, macro), None, ResourceLedger())
    observed = packet["first_executed_macro"]
    assert isinstance(observed, dict)
    assert observed["physical_ticks"] == 13
    assert observed["normalized_symbols"] == 9
    assert observed["return_physical_ticks"] == (4, 8)
    assert observed["return_normalized_steps"] == (2, 6)


def test_9_can_only_be_emitted_by_authenticated_8_entry() -> None:
    for source in (43, 123, 183, 243):
        macro = select_border_return_macro(source, 60)
        if macro is not None and macro.exit_port in (
            BorderExitPort.EIGHT_TO_NINE,
            BorderExitPort.EIGHT_TO_NINE_TO_EIGHT,
            BorderExitPort.EIGHT_TO_NINE_OPEN,
            BorderExitPort.EIGHT_TO_NINE_PENDING,
        ):
            # The final zero symbol is the actual 8->9 division, not
            # an independent 9-action assumed from the quotient.
            assert any(bit == 0 for bit, _ in macro.parts)
            assert type(macro.entry_port) is BorderEntryPort


def test_initial_nine_remains_a_valid_independent_source() -> None:
    # A source ending in 9 needs no invented predecessor.  The composite
    # 6305 return selector declines it; the existing exact 989 source guard
    # continues to own the standalone seed case.
    assert select_border_return_macro(19, 4) is None


def test_prefix_budget_does_not_guess_an_incomplete_305_word() -> None:
    for ticks in range(4, 13):
        macro = select_border_return_macro(23, ticks)
        if macro is None:
            continue
        assert macro.physical_ticks <= ticks
        assert macro.fields.endpoint(23) == _physical(23, macro.physical_ticks)[0]


def test_minimum_useful_extent_is_inclusive_and_accounts_for_ties() -> None:
    equal = select_border_return_macro(23, 13, minimum_useful_physical_ticks=13)
    assert equal is not None and equal.physical_ticks == 13

    shorter = select_border_return_macro(23, 13, minimum_useful_physical_ticks=14)
    assert shorter is None


@pytest.mark.parametrize("minimum", (True, -1, 1.5))
def test_minimum_useful_extent_requires_a_nonnegative_exact_integer(
    minimum: object,
) -> None:
    with pytest.raises(ValueError, match="minimum useful physical ticks"):
        select_border_return_macro(
            23,
            13,
            minimum_useful_physical_ticks=minimum,  # type: ignore[arg-type]
        )


def test_rejected_8_to_9_suffix_skips_power_preflight_and_action_publication() -> None:
    ledger = ResourceLedger()
    preflight_calls: list[int] = []
    macro = select_border_return_macro(
        43,
        60,
        minimum_useful_physical_ticks=8,
        preflight=preflight_calls.append,
        ledger=ledger,
    )
    assert macro is None
    assert preflight_calls == []
    assert (
        ledger.counters["collatz_physical_border_return_candidate_threshold_refusals"]
        == 1
    )
    assert (
        ledger.counters.get(
            "collatz_physical_border_return_candidate_extent_bound_refusals", 0
        )
        == 0
    )


def test_rejected_entry_candidate_skips_zero_exponent_preflight() -> None:
    preflight_calls: list[int] = []
    macro = select_border_return_macro(
        30,
        60,
        minimum_useful_physical_ticks=60,
        preflight=preflight_calls.append,
    )
    assert macro is None
    assert preflight_calls == []


def test_assembled_return_is_one_hashlife_action_and_exact_observer() -> None:
    for source, ticks in ((13, 7), (23, 13), (43, 7), (26, 8)):
        ledger = ResourceLedger()
        result = compile_collatz_temporal_run_quotient(
            source,
            ticks,
            ledger=ledger,
            include_f5=True,
            include_width_spine=True,
            include_joint_cocycle=True,
            include_innovation_tape=True,
            innovation_modulus=49,
        )
        endpoint, widths = _physical(source, ticks)
        assert result.endpoint == endpoint and result.run_actions == 1
        assert result.first_boundary_macro is not None
        assert isinstance(result.first_boundary_macro.identity, GuardedBorderPath)
        assert (
            result.first_boundary_macro.identity.kind
            is BoundaryPathKind.THREE_BORDER_RETURN
        )
        assert result.physical_f5 is not None
        assert result.physical_f5.apply(source) == endpoint % 5
        assert result.joint_action is not None
        assert result.joint_action.endpoint == endpoint
        assert result.tape_width_summary is not None
        blank = result.tape_width_summary.blank
        assert source.bit_length() + blank.minimum == min(widths)
        assert source.bit_length() + blank.maximum == max(widths)
        assert ledger.counters["collatz_physical_boundary_6305R_macro_actions"] == 1
        tape = result.innovation_observation
        assert tape is not None
        normalized_sources = []
        value = source
        for _ in range(result.normalized_symbols):
            normalized_sources.append(value)
            value = (3 * value + 1) // 2 if value & 1 else value // 2
        expected = tuple(exact_source_symbol(x, 49) for x in normalized_sources)
        assert tuple(tape.symbol_counts) == tuple(
            expected.count(sym) for sym in SIGNED_SYMBOLS
        )
        assert tuple(tape.sample) == expected[: len(tape.sample)]


def test_d32_cells_are_published_from_composed_return_without_replay() -> None:
    exponent = 40
    source = _large_3adic_source(exponent)
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source,
        exponent + 4,
        ledger=ledger,
        shared_cache=True,
        include_joint_cocycle=True,
        include_width_spine=True,
        include_innovation_tape=True,
        innovation_modulus=49,
    )
    assert result.run_actions == 1
    assert result.first_boundary_macro is not None
    assert isinstance(result.first_boundary_macro.identity, GuardedBorderPath)
    assert type(result.first_boundary_macro) is BorderReturnMacro
    assert (
        result.first_boundary_macro.identity.kind
        is BoundaryPathKind.THREE_BORDER_RETURN
    )
    assert result.first_boundary_macro.zero_tails[0] == 40
    assert ledger.counters.get("collatz_boundary_prefix_root_publications", 0) >= 3
    assert ledger.counters.get("collatz_hashlife_max_level", 0) >= 5


def test_same_guarded_parity_word_transports_high_fibers() -> None:
    exponent = 40
    base = _large_3adic_source(exponent)
    fibers = (base, base + 5 * (1 << 160))
    for source in fibers:
        macro = select_border_return_macro(source, exponent + 4)
        assert macro is not None
        assert macro.physical_ticks == exponent + 4
        assert macro.fields.endpoint(source) == _physical(source, exponent + 4)[0]
        assert macro.zero_tails == (40,)


def test_composite_source_image_publishes_structural_macro() -> None:
    from number_compiler.sequences.collatz.physical_images import (
        CollatzPhysicalImageWorkspace,
    )

    workspace = CollatzPhysicalImageWorkspace(
        ResourceLedger(),
        23,
        13,
        retain_chronology=False,
        include_innovation_tape=True,
        innovation_modulus=49,
    )
    try:
        witness = workspace.first_boundary_macro
        assert witness is not None
        start, macro = witness
        assert type(macro) is BorderReturnMacro
        assert start == 0
        assert macro.identity.kind is BoundaryPathKind.THREE_BORDER_RETURN
        assert macro.exit_port is BorderExitPort.EIGHT_TO_FOUR
        observation = workspace.innovation_observation
        assert observation is not None
        assert sum(observation.symbol_counts) == observation.normalized_steps
    finally:
        workspace.dispose()


def test_d8_frame_after_return_does_not_join_a_stale_joint_cache_frontier() -> None:
    """Regression: NC11 6305R followed by D8 must not join disconnected cells.

    This high fiber was accepted by the untouched NC11 joint producer but
    initially failed after the border-route insertion, when a later D8 batch
    skipped frontier publication and left a stale dyadic block to be joined.
    """
    source = 8960806254037478453122773870951197237439506
    ticks = 118
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source,
        ticks,
        ledger=ledger,
        shared_cache=False,
        include_joint_cocycle=True,
        include_width_spine=True,
        include_f5=True,
        include_innovation_tape=True,
        innovation_modulus=49,
    )
    assert result.first_boundary_macro is not None
    assert isinstance(result.first_boundary_macro.identity, GuardedBorderPath)
    assert (
        result.first_boundary_macro.identity.kind
        is BoundaryPathKind.THREE_BORDER_RETURN
    )
    assert result.endpoint == _physical(source, ticks)[0]
    assert result.joint_action is not None
    assert result.joint_action.endpoint == result.endpoint
    assert ledger.counters.get("collatz_physical_temporal_d8_discovery_symbols", 0) > 0


def test_border_entry_does_not_split_a_maximal_homogeneous_power() -> None:
    """A last digit 5 is not a reason to shorten a certified 256-odd run."""
    source = (1 << 256) - 1
    result = compile_collatz_temporal_run_quotient(
        source,
        512,
        ledger=ResourceLedger(),
    )
    assert result.run_actions == 1
    assert result.endpoint == 3**256 - 1
