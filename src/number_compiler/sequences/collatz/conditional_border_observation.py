"""Demand-only low-border matrix projections for conditional Collatz paths."""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
        GuardedDecimalPairTransfer,
        UpperNumeratorF5Matrix,
    )
    from number_compiler.sequences.collatz.collatz_two_sided_ring import (
        CollatzTwoSidedCylinder,
    )
    from number_compiler.sequences.collatz.conditional_border_moore import (
        ConditionalBorderMoore,
        ConditionalReturnPower,
        PointedBorderPath,
    )


def demanded_conditional_pointed_ports(
    graph: ConditionalBorderMoore,
    pointed_source: int,
    *,
    binary_bits: int = 32,
    radix_places: dict[int, int] | None = None,
    walsh64: bool = False,
    include_width_coverage: bool = False,
) -> dict[str, object]:
    """Build the demanded output packet without adding work to graph admission."""
    from number_compiler.sequences.collatz.conditional_border_moore import (
        ConditionalBorderMoore,
    )

    if type(graph) is not ConditionalBorderMoore:
        raise TypeError("conditional port demand needs a compiled border graph")
    pointed = graph.select(pointed_source)
    if pointed is None:
        raise ValueError("unresolved conditional inlet has no certified ports")
    packet = pointed.action.demanded_outer_inner_future(
        pointed_source,
        binary_bits=binary_bits,
        leading_bits=min(8, pointed_source.bit_length()),
        radix_places=radix_places,
        walsh64=walsh64,
        include_width_coverage=include_width_coverage,
    )
    pair_packet = demanded_pointed_path_pair_packet(
        graph.source, pointed_source, pointed
    )
    return {
        **packet,
        **pair_packet,
        "conditional_moore_class": graph.classes[pointed.state_path[-1]],
        "quadratic_clock": (
            pointed.skew_clock.value,
            pointed.skew_clock.linear,
            pointed.skew_clock.quadratic,
        ),
        "source_bound_skew_verified": True,
        "conditional_root_source_guard": (
            pointed.action.guard.residue,
            pointed.action.guard.modulus,
        ),
        "conditional_proved_tails": pointed.tails,
        "all_alternatives_retained": True,
    }


def demanded_pointed_path_pair_packet(
    source: CollatzTwoSidedCylinder,
    pointed_source: int,
    pointed: PointedBorderPath,
) -> dict[str, object]:
    """Project the pointed pair/F5 and source-correlated radix-6 inlet ports."""
    from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
        GuardedDecimalPairTransfer,
        UpperNumeratorF5Matrix,
        WeightedPairMatrix,
        upper_numerator_f5,
    )
    from number_compiler.sequences.collatz.cross_family_port_power import (
        MacroTraceGrammar,
    )
    from number_compiler.sequences.collatz.guarded_port_join import GuardedPortJoin
    from number_compiler.sequences.collatz.guarded_radix6_bridge import (
        certify_guarded_radix6_bridge,
        certify_return_trace_radix6_bridge,
    )

    endpoint = pointed.action.endpoint(pointed_source)
    pair = GuardedDecimalPairTransfer(pointed.action).pointed_entry(pointed_source)
    first_odd = WeightedPairMatrix.odd_half((pointed_source // 100) & 1).successors(
        pointed_source % 100
    )
    if len(first_odd) != 1 or first_odd[0][0] != ((3 * pointed_source + 1) // 2) % 100:
        raise ArithmeticError(
            "guarded first odd pair/carry operator disagrees with source"
        )
    packet: dict[str, object] = {
        "low_pair_transition": (pair.input_pair, pair.output_pair),
        "low_pair_root_guard": (pair.guard.residue, pair.guard.modulus),
        "low_pair_first_odd_carries": first_odd[0][1:],
    }
    inlet = source.intersect_congruence(
        pointed.action.guard.residue, pointed.action.guard.modulus
    )
    if inlet is not None and inlet.first < pointed.action.guard.minimum_source:
        inlet = inlet.intersect_interval(
            pointed.action.guard.minimum_source, inlet.upper
        )
    if inlet is None or not inlet.contains(pointed_source):
        raise ArithmeticError("conditional matrix guard has no original source fiber")
    full_returns = (
        inlet.forced_residue(10) == 3
        and pointed_source % 10 == 3
        and endpoint % 10 == 3
        and pointed.action.odd_events == 2 * len(pointed.tails)
        and pointed.action.action.steps == sum(tail + 2 for tail in pointed.tails)
    )
    trace = (
        MacroTraceGrammar.leaf(pointed.tails)
        if full_returns
        else MacroTraceGrammar.leaf(())
    )
    bridge = (
        certify_return_trace_radix6_bridge(inlet, trace, pointed.action.action)
        if full_returns
        else certify_guarded_radix6_bridge(
            inlet, pointed.action.action, pointed.action.odd_events
        )
    )
    joined = GuardedPortJoin(inlet, pointed.action, bridge)
    first, last = joined.require_pointed(pointed_source)
    if last is None or last.output_pair != endpoint % 100:
        raise ArithmeticError("conditional punctured matrix lost its endpoint pair")
    packet["joint_punctured_source_guard"] = (
        inlet.residue,
        inlet.modulus,
        inlet.count,
    )
    packet["joint_punctured_pair_endpoints"] = (
        first.output_pair,
        last.output_pair,
    )
    packet["joint_punctured_radix6"] = bridge.observation()
    if (
        pointed_source % 10 == 3
        and endpoint % 10 == 3
        and pointed.action.odd_events == 2 * len(pointed.tails)
        and pointed.action.action.steps == sum(j + 2 for j in pointed.tails)
    ):
        phase = UpperNumeratorF5Matrix.from_trace(MacroTraceGrammar.leaf(pointed.tails))
        if phase.apply(upper_numerator_f5(pointed_source)) != upper_numerator_f5(
            endpoint
        ):
            raise ArithmeticError("conditional low-border phase lost its endpoint")
        packet["low_border_f5_phase_matrix"] = phase.entries
        packet["low_border_f5_phase_returns"] = phase.returns
    return packet


def demanded_powered_pair_transfer(
    powered: ConditionalReturnPower, pointed_source: int
) -> GuardedDecimalPairTransfer | None:
    """Return a lazy guarded transfer for one selected powered inlet branch."""
    from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
        GuardedDecimalPairTransfer,
    )
    from number_compiler.sequences.collatz.conditional_border_moore import (
        ConditionalReturnPower,
    )

    if type(powered) is not ConditionalReturnPower:
        raise TypeError("conditional pair transfer needs a powered return relation")
    branch = powered.select(pointed_source)
    if branch.port is None:
        return None
    return GuardedDecimalPairTransfer(branch.port)


def demanded_powered_upper_phase(
    powered: ConditionalReturnPower, pointed_source: int
) -> UpperNumeratorF5Matrix | None:
    """Return F5 matrix only for a selected, uninterrupted 3-to-3 trace."""
    from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
        UpperNumeratorF5Matrix,
        upper_numerator_f5,
    )
    from number_compiler.sequences.collatz.conditional_border_moore import (
        ConditionalReturnPower,
    )

    if type(powered) is not ConditionalReturnPower:
        raise TypeError("conditional phase needs a powered return relation")
    branch = powered.select(pointed_source)
    if (
        branch.port is None
        or branch.target is None
        or pointed_source % 10 != 3
        or branch.target.forced_residue(10) != 3
        or branch.tails.length == 0
    ):
        return None
    matrix = UpperNumeratorF5Matrix.from_trace(branch.tails)
    if matrix.returns != powered.return_count:
        raise ArithmeticError("powered F5 phase lost the return count")
    if matrix.apply(upper_numerator_f5(pointed_source)) != upper_numerator_f5(
        branch.port.endpoint(pointed_source)
    ):
        raise ArithmeticError("powered F5 upper phase disagrees with endpoint")
    return matrix
