"""NC17 source-punctured successor power and hot-path regression checks."""

from __future__ import annotations

from dataclasses import replace
from typing import cast

import pytest

from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
    WeightedPairMatrix,
    certify_pointed_low_border,
)
from number_compiler.sequences.collatz.boundary_macros import select_boundary_macro
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.guarded_port_join import (
    GuardedPortJoin,
    PortPuncture,
    certify_pointed_port_join,
)
from number_compiler.sequences.collatz.guarded_radix6_bridge import (
    certify_guarded_radix6_bridge,
)
from number_compiler.sequences.collatz.named_border_carry_matrix import (
    MAX_NAMED_MATRIX_TRACE_PREFIX,
    certify_named_border_carry_matrix,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    SourceClosedPortAction,
    SourceCongruence,
)


def test_weighted_deterministic_fast_product_matches_exact_semiring() -> None:
    a = WeightedPairMatrix.odd_half(0)
    b = WeightedPairMatrix.odd_half(1)
    c = WeightedPairMatrix.even(0)
    for before, after in ((a, a), (a, b), (a, c), (c, a), (c, c)):
        out = before.then(after)
        for i in range(100):
            reference = tuple(
                sorted(
                    {
                        (z, x + u, y + v)
                        for mid, x, y in before.successors(i)
                        for z, u, v in after.successors(mid)
                    }
                )
            )
            assert out.successors(i) == reference
    # A genuinely branching source cannot use the one-arrow fast path.
    rows = list(WeightedPairMatrix.identity().rows)
    rows[63] = ((18, 2, 0), (82, 1, 3))
    branch = WeightedPairMatrix(tuple(rows))
    product = branch.then(a)
    expected = tuple(
        sorted(
            {
                (z, c1 + d1, c2 + d2)
                for j, c1, c2 in branch.successors(63)
                for z, d1, d2 in a.successors(j)
            }
        )
    )
    assert product.successors(63) == expected
    assert product == branch.then(a)


def test_cached_weighted_factories_validate_before_cache_lookup() -> None:
    WeightedPairMatrix.even(1)
    WeightedPairMatrix.odd_half(0, inlet=1)
    with pytest.raises(ValueError, match="parity bit"):
        WeightedPairMatrix.even(True)
    with pytest.raises(ValueError, match="parity bit"):
        WeightedPairMatrix.odd_half(False)
    with pytest.raises(ValueError, match="inlet"):
        WeightedPairMatrix.odd_half(0, inlet=True)


def test_restricted_radix6_bridge_keeps_every_published_five_sound() -> None:
    word = DyadicTerminalFieldAction.one_run(2)
    cylinder = CollatzTwoSidedCylinder(63, 67, 3, 4)
    bridge = certify_guarded_radix6_bridge(cylinder, word, 2)
    for x in (63, 67):
        narrower = CollatzTwoSidedCylinder(x, x, 0, 1)
        subset = bridge.restrict_to(narrower)
        full = certify_guarded_radix6_bridge(narrower, word, 2)
        assert subset.target == full.target
        assert subset.action == word
        assert subset.centered_defect_range == full.centered_defect_range
        for band in subset.source_fives:
            for pos in range(band.lower, band.upper):
                assert (x // 6**pos) % 6 == 5
        y = word.endpoint(x)
        for band in subset.target_fives:
            for pos in range(band.lower, band.upper):
                assert (y // 6**pos) % 6 == 5
    try:
        bridge.restrict_to(CollatzTwoSidedCylinder(71, 71, 0, 1))
    except ValueError:
        pass
    else:
        raise AssertionError("foreign source must not reuse a radix6 proof")


def test_pointed_join_consumes_the_already_certified_decimal_pair(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = 7
    action = DyadicTerminalFieldAction.one_run(2)
    endpoint = action.endpoint(source)
    low_pair = certify_pointed_low_border(source, endpoint, action, 2)

    def reject_duplicate_point_puncture(
        _joined: GuardedPortJoin, _source: int, *, check_last: bool = True
    ) -> object:
        raise AssertionError("join rebuilt an already certified pointed pair")

    monkeypatch.setattr(
        GuardedPortJoin, "require_pointed", reject_duplicate_point_puncture
    )
    joined = certify_pointed_port_join(
        source,
        action,
        2,
        pointed_pair=low_pair.pair,
    )
    assert joined.port.endpoint(source) == endpoint
    assert joined.bridge.target.contains(endpoint)


def test_pointed_join_rejects_a_pair_from_another_endpoint() -> None:
    source = 7
    action = DyadicTerminalFieldAction.one_run(2)
    foreign_action = DyadicTerminalFieldAction.one_run(1)
    foreign_endpoint = foreign_action.endpoint(source)
    foreign = certify_pointed_low_border(source, foreign_endpoint, foreign_action, 1)
    with pytest.raises((ArithmeticError, ValueError)):
        certify_pointed_port_join(
            source,
            action,
            2,
            pointed_pair=foreign.pair,
        )


def test_pointed_join_rejects_pair_from_foreign_source() -> None:
    action = DyadicTerminalFieldAction.one_run(2)
    source = 7
    foreign_source = 15
    foreign = certify_pointed_low_border(
        foreign_source,
        action.endpoint(foreign_source),
        action,
        2,
    )
    with pytest.raises((ArithmeticError, ValueError)):
        certify_pointed_port_join(
            source,
            action,
            2,
            pointed_pair=foreign.pair,
        )


def test_pointed_join_rejects_forged_public_pair_fields() -> None:
    source = 7
    action = DyadicTerminalFieldAction.one_run(2)
    endpoint = action.endpoint(source)
    pair = certify_pointed_low_border(source, endpoint, action, 2).pair
    forged_rows = (
        replace(pair, output_pair=(pair.output_pair + 1) % 100),
        replace(pair, guard=SourceCongruence(0, 1)),
        replace(
            pair,
            inlet=CollatzTwoSidedCylinder(source + 1, source + 1, 0, 1),
        ),
        replace(
            pair,
            target=CollatzTwoSidedCylinder(endpoint + 1, endpoint + 1, 0, 1),
        ),
    )
    for forged in forged_rows:
        with pytest.raises((ArithmeticError, ValueError)):
            certify_pointed_port_join(
                source,
                action,
                2,
                pointed_pair=forged,
            )


def test_pointed_join_rejects_boolean_pair_indices() -> None:
    cases = (
        (1, DyadicTerminalFieldAction.one_run(1), 1, True),
        (2, DyadicTerminalFieldAction.zero_run(1), 0, False),
    )
    for source, action, odd_events, input_alias in cases:
        pair = certify_pointed_low_border(
            source, action.endpoint(source), action, odd_events
        ).pair
        # bool compares equal to 0 or 1, but is not an admitted pair index.
        if input_alias:
            forged = replace(pair, input_pair=True)
        else:
            forged = replace(pair, output_pair=True)
        with pytest.raises((ArithmeticError, ValueError)):
            certify_pointed_port_join(
                source,
                action,
                odd_events,
                pointed_pair=forged,
            )


def test_modular_clock_and_future_family_punctures_retain_root_branches() -> None:
    a, b = 63, 263
    root = CollatzTwoSidedCylinder(a, b, a % (b - a), b - a)
    port = SourceClosedPortAction.identity()
    joined = GuardedPortJoin(
        root, port, certify_guarded_radix6_bridge(root, port.action, 0)
    )
    for x in (a, b):
        cut = joined.puncture(
            0,
            PortPuncture(
                clock_residues=(
                    (99, x % 99),
                    (198, x % 198),
                    (25, x % 25),
                )
            ),
            pointed_source=x,
        )
        assert cut.pointed(x) is not None
        assert cut.admitted_count == 1
    alternatives = joined.future_family_partition()
    assert sum(part.count for _, part in alternatives) == 2
    assert all(any(part.contains(x) for _, part in alternatives) for x in (a, b))


def test_named_matrix_trace_reads_only_a_bounded_retained_tape_prefix() -> None:
    macro = select_boundary_macro(159, 300, minimum_repetitions=1)
    assert macro is not None
    matrix = certify_named_border_carry_matrix(macro)
    length = min(12, macro.normalized_symbols)
    packet = matrix.trace_packet(normalized_steps=length)
    trace = cast(dict[str, object], packet["trace"])
    parity = cast(tuple[int, ...], trace["parity"])
    clocks = cast(dict[str, object], packet["clocks"])

    assert len(parity) == length
    assert set(parity) <= {0, 1}
    assert trace["odd_events"] == sum(parity)
    physical = cast(dict[str, object], trace["physical_ticks"])
    assert physical == {
        "value": length + sum(parity),
        "unit": "physical-ticks",
    }
    normalized = cast(dict[str, object], clocks["normalized_steps"])
    odd = cast(dict[str, object], clocks["odd_events"])
    assert normalized["unit"] == "normalized-halving-events"
    assert odd["unit"] == "odd-events"
    assert (
        trace["endpoint_mod5"]
        == matrix.joined.prefix_units(length).apply(macro.source % 5)[0]
    )
    with pytest.raises(ValueError, match="64"):
        matrix.trace_packet(normalized_steps=MAX_NAMED_MATRIX_TRACE_PREFIX + 1)
