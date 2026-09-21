"""Challenge future-pattern claims with exact original-source witnesses."""

import json
from fractions import Fraction

import pytest

from devtools.experiments.antihydra.barrier_search import grammar_refinement, main
from devtools.experiments.antihydra.future_grammar import ReachableFutureGrammar
from devtools.experiments.antihydra.source_safety import SourceSafetyWorkspace
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational as Q,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    SaturatingAffineAction,
)
from number_compiler.resources.ledger import ResourceLedger


def _grammar(width: int = 128) -> ReachableFutureGrammar:
    return ReachableFutureGrammar(
        SourceSafetyWorkspace(ResourceLedger(), max_width=width)
    )


def _literal(source: int, width: int) -> tuple[int, tuple[int, ...]]:
    parities = []
    for _ in range(width):
        parities.append(source % 2)
        source = (3 * source + 1) // 2
    return source, tuple(parities)


def _fraction(value: Q) -> Fraction:
    return Fraction(value.numerator, value.denominator)


def _literal_first_failure(
    source: int, fraction: Fraction, width: int
) -> tuple[int | None, int, Fraction]:
    if not Fraction(0) <= fraction < Fraction(1, 2):
        return 0, source, fraction
    for step in range(1, width + 1):
        old = source
        source = (3 * source + 1) // 2
        fraction = Fraction(3, 2) * (old + fraction) - source
        if not Fraction(0) <= fraction < Fraction(1, 2):
            return step, source, fraction
    return None, source, fraction


@pytest.mark.parametrize("events", ((1,), (2,), (3, 3), (4, 3), (2, 4), (3, 4, 3)))
def test_reachable_edges_select_events_from_one_fixed_witness(
    events: tuple[int, ...],
) -> None:
    grammar = _grammar()
    handle = grammar.root
    for exponent in events:
        handle = grammar.extend(handle, exponent)
    block = grammar.workspace.view(handle)
    if block.guard.empty:
        # A negative constructor answer must agree with an independent guard intersection.
        source, scale, lo, hi = block.residue, Fraction(1), Fraction(0), Fraction(1, 2)
        for _ in range(block.width):
            source = (3 * source + 1) // 2
            scale *= Fraction(3, 2)
            lo = max(lo, source / scale - block.residue)
            hi = min(hi, (source + Fraction(1, 2)) / scale - block.residue)
        assert lo >= hi
        return
    source, t = grammar.witness(handle)
    value = Fraction(source) + _fraction(t)
    current = source
    for exponent in events:
        assert (current & -current).bit_length() == exponent
        for _ in range(exponent):
            assert value - value.numerator // value.denominator < Fraction(1, 2)
            value *= Fraction(3, 2)
            current = (3 * current + 1) // 2
    assert 0 <= value - current < Fraction(1, 2)
    assert current == block.endpoint + 3**block.width * (source >> block.width)
    action = grammar.telescoping(handle)
    assert action.denominator * current == action.gain * source + action.innovation
    assert not grammar.admits(handle, source, block.guard.upper)
    assert grammar.admits(handle, source + (1 << block.width), t)
    assert not grammar.admits(handle, source + 1, t)


@pytest.mark.parametrize("events", ((3,), (2, 4), (3, 4, 3)))
def test_edges_retain_exact_high_fiber_parameter_transport(
    events: tuple[int, ...],
) -> None:
    grammar = _grammar()
    parent = grammar.root
    for exponent in events:
        edge = grammar.edge(parent, exponent)
        before = grammar.workspace.view(parent)
        child = grammar.workspace.view(edge.child)
        event = grammar.workspace.view(
            grammar.workspace.cylinder(exponent, 1 << (exponent - 1))
        )
        transport = edge.transport
        assert 0 <= transport.gain_inverse < transport.input_stride
        assert (
            transport.output_stride * transport.gain_inverse % transport.input_stride
            == 1 % transport.input_stride
        )
        assert (
            transport.input_offset
            == (
                (
                    event.residue
                    + transport.input_stride
                    - before.endpoint % transport.input_stride
                )
                * transport.gain_inverse
            )
            % transport.input_stride
        )
        for parameter in (0, 1, 17, 2**80 + 39):
            parent_high = transport.input_offset + transport.input_stride * parameter
            source = before.residue + (parent_high << before.width)
            event_source = before.endpoint + 3**before.width * parent_high
            event_high = transport.output_offset + transport.output_stride * parameter
            assert event_source == event.residue + (event_high << exponent)
            endpoint, word = _literal(source, child.width)
            assert word == _literal(child.residue, child.width)[1]
            assert endpoint == child.endpoint + 3**child.width * parameter
        parent = edge.child


@pytest.mark.parametrize("transitions", (0, 1, 2, 7, 31))
def test_finite_clause_transport_preserves_source_and_guard_for_every_fiber(
    transitions: int,
) -> None:
    grammar = _grammar(256)
    clause = grammar.extend(grammar.root, 3)
    block = grammar.workspace.view(clause)
    transport = grammar.finite_repeated_clause_transport(clause, transitions)
    admitted = grammar.workspace.view(transport.admitted)
    assert admitted.width == block.width * (transitions + 1)
    assert transport.guard == admitted.guard
    assert not transport.guard.contains(transport.guard.upper)
    if transport.guard.empty:
        return
    _, fraction = grammar.witness(transport.admitted)
    prefix_width = block.width * transitions
    for parameter in (0, 1, 19, 2**70 + 5):
        input_high = transport.input_offset + transport.input_stride * parameter
        source = block.residue + (input_high << block.width)
        assert source == admitted.residue + (parameter << admitted.width)
        current, word = _literal(source, prefix_width)
        output_high = transport.output_offset + transport.output_stride * parameter
        assert current == block.residue + (output_high << block.width)
        assert word == _literal(admitted.residue, prefix_width)[1]
        assert transport.guard.contains(fraction)
        value = Q(source) + fraction
        for _ in range(prefix_width):
            value = Q(3, 2) * value
        residual = value - Q(current)
        assert block.guard.contains(residual)


def test_finite_clause_transport_uses_logarithmic_composition() -> None:
    grammar = _grammar(4096)
    clause = grammar.extend(grammar.root, 3)
    before = grammar.workspace.ledger.counters["safety_composition_attempts"]
    retained_before = grammar.workspace.ledger.counters["safety_retained_integer_bits"]
    transport = grammar.finite_repeated_clause_transport(clause, 1023)
    used = grammar.workspace.ledger.counters["safety_composition_attempts"] - before
    assert used <= 2 * (1023).bit_length()
    assert grammar.workspace.view(transport.admitted).width == 3 * 1024
    # Binary composition saves calls, but the exact source/guard certificate is
    # still linear-size.  Do not report this finite constructor as cheap power.
    assert (
        grammar.workspace.ledger.counters["safety_retained_integer_bits"]
        - retained_before
        >= 3 * 1024
    )
    assert grammar.workspace.ledger.counters.get("mahler_carry_columns", 0) == 0


def test_finite_clause_transports_do_not_pose_as_one_invariant_pump() -> None:
    grammar = _grammar()
    clause = grammar.extend(grammar.root, 3)
    transports = tuple(
        grammar.finite_repeated_clause_transport(clause, n) for n in range(3)
    )
    assert tuple(
        grammar.workspace.view(transport.admitted).residue for transport in transports
    ) == (4, 20, 404)
    assert tuple(
        (transport.input_offset, transport.input_stride) for transport in transports
    ) == ((0, 1), (2, 8), (50, 64))
    assert {
        grammar.workspace.view(transport.admitted).residue for transport in transports
    } == {4, 20, 404}


@pytest.mark.parametrize("width", (1, 2, 3, 7, 16, 31))
def test_total_safe_fail_consumer_descends_exact_composed_guard(width: int) -> None:
    grammar = _grammar(64)
    fractions = (Q(-1, 8), Q(0), Q(1, 64), Q(1, 4), Q(31, 64), Q(1, 2))
    for residue in (0, 1, (1 << width) // 3, (1 << width) - 1):
        handle = grammar.workspace.cylinder(width, residue)
        source = residue + (17 << width)
        for fraction in fractions:
            expected = _literal_first_failure(source, _fraction(fraction), width)
            actual = grammar.first_failure(handle, source, fraction)
            assert (
                actual.step,
                actual.endpoint_source,
                _fraction(actual.residual),
            ) == expected


def test_safe_fail_consumer_skips_a_complete_safe_action() -> None:
    grammar = _grammar(2048)
    clause = grammar.extend(grammar.root, 3)
    repeated = grammar.repeat(clause, 512)
    source, fraction = grammar.witness(repeated)
    before = grammar.workspace.ledger.counters.get("grammar_failure_descent_nodes", 0)
    result = grammar.first_failure(repeated, source, fraction)
    assert result.step is None
    assert (
        grammar.workspace.ledger.counters.get("grammar_failure_descent_nodes", 0)
        == before
    )
    block = grammar.workspace.view(repeated)
    assert result.endpoint_source == block.endpoint + 3**block.width * (
        source >> block.width
    )


@pytest.mark.parametrize("width", (1, 2, 3, 4, 5))
def test_periodic_source_limit_matches_independent_parity_replay(width: int) -> None:
    grammar = _grammar()
    for residue in range(1 << width):
        handle = grammar.workspace.cylinder(width, residue)
        _, word = _literal(residue, width)
        for high in range(4):
            source = residue + (high << width)
            if source == 0:
                continue
            result = grammar.periodic_obstruction(handle, source)
            current = source
            for _ in range(result.source_repetition_limit):
                current, actual = _literal(current, width)
                assert actual == word
            assert _literal(current, width)[1] != word
            assert result.source_obstruction > 0
            assert (
                result.source_obstruction
                % (1 << (width * result.source_repetition_limit))
                == 0
            )


def test_fractional_cycle_does_not_authorize_an_infinite_positive_source() -> None:
    grammar = _grammar()
    clause = grammar.extend(grammar.root, 3)
    obstruction = grammar.periodic_obstruction(clause, 4)
    assert obstruction.fractional_fixed_point == Q(4, 19)
    assert obstruction.fractional_cycle_admitted
    assert obstruction.source_obstruction == 80
    assert obstruction.source_repetition_limit == 1
    for n in range(1, 9):
        repeated = grammar.repeat(clause, n)
        block = grammar.workspace.view(repeated)
        assert block.guard.contains(Q(4, 19))
        if n > 1:
            assert not grammar.admits(repeated, 4, Q(4, 19))
        direct = grammar.root
        for _ in range(n):
            direct = grammar.extend(direct, 3)
        assert repeated == direct
    lanes = grammar.cyclotomic(clause)
    assert next(row for row in lanes if row.prime == 19).fractional_cycle_lane is None
    exceptional = next(row for row in lanes if row.prime == 19)
    assert exceptional.multiplier_order == 1 and exceptional.affine_order == 19
    for row in lanes:
        for u in range(row.prime):
            v = u
            for _ in range(row.affine_order):
                v = (row.multiplier * v + row.offset) % row.prime
            assert v == u
        assert pow(row.multiplier, row.multiplier_order, row.prime) == 1
        assert all(
            pow(row.multiplier, k, row.prime) != 1
            for k in range(1, row.multiplier_order)
        )
        if row.fractional_cycle_lane is not None:
            u = row.fractional_cycle_lane
            assert (row.multiplier * u + row.offset) % row.prime == u


def test_joint_readout_keeps_deck_event_carry_prime_and_telescoping_bound() -> None:
    grammar = _grammar()
    parent = grammar.extend(grammar.root, 3)
    result = grammar.observe_edge(parent, 3)
    assert result.source == result.deck + 64 * result.high_fiber
    middle, _ = _literal(result.source, 3)
    assert result.event.source == middle
    assert result.event.exponent == 3
    assert result.readouts.source == middle
    assert result.readouts.exponent == 3
    assert (
        Q(result.readouts.raw_numerator, 1 << result.readouts.denominator_exponent)
        == Q(4) * result.event.next_fraction
    )
    final, _ = _literal(result.source, 6)
    action = result.telescoping
    assert action.denominator * final == action.gain * result.source + action.innovation


def test_foreign_authority_limits_and_lazy_readouts() -> None:
    grammar, other = _grammar(), _grammar()
    with pytest.raises(ValueError, match="different arena"):
        grammar.extend(other.root, 3)
    handle = grammar.extend(grammar.root, 3)
    before = dict(grammar.workspace.ledger.counters)
    assert grammar.extend(grammar.root, 3) == handle
    assert (
        grammar.workspace.ledger.counters["grammar_edges_constructed"]
        == before["grammar_edges_constructed"]
    )
    assert grammar.workspace.ledger.counters.get("mahler_carry_columns", 0) == 0
    with pytest.raises(ValueError, match="positive source"):
        grammar.periodic_obstruction(handle, 0)
    with pytest.raises(ValueError, match="positive source"):
        grammar.periodic_obstruction(handle, 5)
    with pytest.raises(ValueError, match="exploration bound"):
        grammar.extend(handle, 9)
    with pytest.raises(BlockContextBudgetExceeded, match="width budget"):
        grammar.repeat(handle, 10**9)
    with pytest.raises(BlockContextBudgetExceeded, match="column budget"):
        grammar.observe_edge(grammar.root, 3, max_columns=1)
    assert grammar.workspace.ledger.counters.get("mahler_carry_columns", 0) == 0


def test_bounded_grammar_reports_unexplored_events_and_no_infinite_certificate() -> (
    None
):
    result = grammar_refinement(2, 4, 1000)
    assert result["status"] == "FINITE_REACHABLE_GRAMMAR"
    assert result["larger_event_branches"] == "UNEXPLORED"
    assert result["all_time_quotient_certified"] is False
    assert result["global_safety_decided"] is False
    assert result["nonhalting_certified"] is False
    assert result["sample_periodic_obligations"]
    assert result["joint_finite_witness_observations"]
    refused = grammar_refinement(2, 4, 1)
    assert refused["status"] == "BUDGET_EXHAUSTED"
    assert refused["all_time_quotient_certified"] is False


def test_supplied_clause_binary_power_does_not_rediscover_events(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    grammar = _grammar(2048)
    clause = grammar.extend(grammar.root, 3)

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("binary repetition rediscovered source leaves")

    monkeypatch.setattr(grammar.workspace, "cylinder", forbidden)
    before = grammar.workspace.ledger.counters["safety_composition_attempts"]
    powered = grammar.repeat(clause, 512)
    block = grammar.workspace.view(powered)
    assert block.width == 1536
    assert (
        grammar.workspace.ledger.counters["safety_composition_attempts"] - before == 10
    )
    assert block.guard.contains(Q(4, 19))
    source, _ = grammar.witness(powered)
    assert _literal(source, 1536)[1] == (0, 0, 1) * 512
    assert grammar.periodic_obstruction(clause, source).source_repetition_limit >= 512
    assert grammar.workspace.ledger.counters.get("mahler_carry_columns", 0) == 0


def test_rejected_edge_publication_keeps_only_charged_complete_source_blocks() -> None:
    ledger = ResourceLedger(max_nodes=10, max_cache_entries=4)
    workspace = SourceSafetyWorkspace(ledger)
    grammar = ReachableFutureGrammar(workspace)
    for _ in range(2):
        with pytest.raises(BlockContextBudgetExceeded):
            grammar.extend(grammar.root, 1)
        assert ledger.nodes == 2
        assert ledger.entries == 4
        assert ledger.counters.get("grammar_edges_constructed", 0) == 0
        assert ledger.counters.get("grammar_edge_hits", 0) == 0
        assert workspace.view(grammar.root).width == 0


def test_research_command_serializes_joint_carry_domains(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(
        "sys.argv",
        ["barrier_search", "--mode", "grammar", "--rounds", "2", "--max-event", "4"],
    )
    main()
    report = json.loads(capsys.readouterr().out)
    assert report["status"] == "FINITE_REACHABLE_GRAMMAR"
    for row in report["joint_finite_witness_observations"]:
        assert set(row["readouts"]["subtraction"]) <= {"0", "id", "1"}


def test_research_grammar_and_workspace_release_all_retained_owners() -> None:
    ledger = ResourceLedger()
    workspace = SourceSafetyWorkspace(ledger, max_width=64)
    grammar = ReachableFutureGrammar(workspace)
    handle = grammar.extend(grammar.extend(grammar.root, 3), 4)
    grammar.first_failure(handle, *grammar.witness(handle))
    assert ledger.entries > 0 and ledger.nodes > 0

    grammar.close()
    grammar.close()
    with pytest.raises(ValueError, match="closed Mahler reachable-future grammar"):
        grammar.extend(grammar.root, 3)
    assert any(
        row.disposed and row.name.startswith("mahler-grammar-")
        for row in ledger.snapshot().inventory
    )

    workspace.close()
    workspace.close()
    assert ledger.entries == 0 and ledger.nodes == 0
    with pytest.raises(ValueError, match="closed Mahler source-safety workspace"):
        workspace.view(handle)
    safety_rows = tuple(
        row
        for row in ledger.snapshot().inventory
        if row.name.startswith("mahler-safety-")
    )
    assert safety_rows and all(row.disposed for row in safety_rows)


def test_closed_workspace_refuses_grammar_before_registering_edge_owner() -> None:
    ledger = ResourceLedger()
    workspace = SourceSafetyWorkspace(ledger)
    workspace.close()
    owner_count = ledger.owner_count
    with pytest.raises(ValueError, match="closed Mahler source-safety workspace"):
        ReachableFutureGrammar(workspace)
    assert ledger.owner_count == owner_count


@pytest.mark.parametrize(
    "width,expected_occurrences,expected_kernels",
    ((6, 18, 12), (8, 40, 18), (10, 90, 26)),
)
def test_normalized_safe_kernel_sharing_retains_occurrence_authority(
    width: int, expected_occurrences: int, expected_kernels: int
) -> None:
    grammar = _grammar(max(8, width))
    rows = []
    for residue in range(1 << width):
        handle = grammar.workspace.cylinder(width, residue)
        if grammar.workspace.view(handle).guard.empty:
            continue
        rows.append(grammar.normalized_safe_effect(handle))
    assert len(rows) == expected_occurrences
    assert len({kernel for kernel, _ in rows}) == expected_kernels
    assert len({chart for _, chart in rows}) == expected_occurrences


def test_shared_safe_kernel_does_not_merge_distinct_failure_paths() -> None:
    grammar = _grammar(8)
    first = grammar.workspace.cylinder(4, 5)
    second = grammar.workspace.cylinder(4, 14)
    first_kernel, first_chart = grammar.normalized_safe_effect(first)
    second_kernel, second_chart = grammar.normalized_safe_effect(second)
    assert first_kernel == second_kernel
    assert first_chart != second_chart
    assert grammar.first_failure(first, 5, Q(0)).step == 1
    assert grammar.first_failure(second, 14, Q(0)).step == 2


def test_safe_skip_consumes_normalized_kernel_without_original_affine_apply(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    grammar = _grammar()
    handle = grammar.extend(grammar.root, 3)
    source, fraction = grammar.witness(handle)
    kernel, chart = grammar.normalized_safe_effect(handle)

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("safe skip returned to the occurrence affine evaluator")

    monkeypatch.setattr(SaturatingAffineAction, "apply", forbidden)
    result = grammar.first_failure(handle, source, fraction)
    assert result.step is None
    normalized = fraction - chart.input_origin
    assert result.residual == kernel.scale * normalized + kernel.output_origin
