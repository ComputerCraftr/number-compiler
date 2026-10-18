"""Exact finite source closure for already-issued cross-family actions."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as collatz_keys
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_0563,
    ENTRY_89_AT_NINE,
    ENTRY_421,
    ENTRY_4721,
    ENTRY_26847_PHASES,
    PATH_305,
    PATH_630,
    BoundaryActionIdentity,
)
from number_compiler.sequences.collatz.boundary_macros import BoundaryActionTemplateMemo
from number_compiler.sequences.collatz.cross_family_port_power import (
    CrossFamilyPortAction,
    MacroTraceGrammar,
    SourceCongruence,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.joint_radix_border import (
    JointRadix6Source,
    candidate_family_guard,
)
from number_compiler.sequences.collatz.unified_skew_chain import (
    select_unified_skew_chain,
)
from number_compiler.sequences.collatz.unified_skew_clock import SkewQuadraticClock


def _normalized(source: int, steps: int) -> tuple[int, tuple[int, ...]]:
    word: list[int] = []
    for _ in range(steps):
        bit = source & 1
        word.append(bit)
        source = (3 * source + 1) // 2 if bit else source // 2
    return source, tuple(word)


def test_general_affine_preimage_handles_nonunit_radix_three_and_six() -> None:
    odd_step = DyadicTerminalFieldAction.one_run(1)
    target = SourceCongruence(2, 6)
    pulled = target.pullback(odd_step)
    assert pulled == SourceCongruence(1, 4)
    impossible = SourceCongruence(0, 3).pullback(odd_step)
    assert impossible is None
    for modulus in (3, 6, 9, 36, 64, 160):
        for residue in range(modulus):
            preimage = SourceCongruence(residue, modulus).pullback(odd_step)
            for source in range(1, 160):
                admitted = odd_step.certifies(source)
                matches = admitted and odd_step.endpoint(source) % modulus == residue
                assert (preimage.admits(source) if preimage else False) == matches


def test_candidate_quotient_keeps_selector_lower_bound_and_typed_phase() -> None:
    identities: tuple[BoundaryActionIdentity, ...] = (
        ENTRY_421,
        ENTRY_4721,
        ENTRY_0563,
        *ENTRY_26847_PHASES,
        PATH_630,
        PATH_305,
        ENTRY_89_AT_NINE,
    )
    guards: dict[BoundaryActionIdentity, SourceCongruence] = {}
    for identity in identities:
        residue, modulus, minimum = candidate_family_guard(identity)
        guards[identity] = SourceCongruence(residue, modulus, minimum)

    # Exhaust every finite source label and several lifts of each radix-160
    # class. The quotient preserves the typed output, not an arbitrary word.
    for source in range(1, 1_601):
        candidate = JointRadix6Source.from_source(source).candidate_family
        for identity, guard in guards.items():
            _, _, minimum = candidate_family_guard(identity)
            assert guard.admits(source) == (candidate == identity and source >= minimum)

    entry_421_guard = guards[ENTRY_421]
    assert JointRadix6Source.from_source(4).candidate_family == ENTRY_421
    assert not entry_421_guard.admits(4)
    assert entry_421_guard.admits(44)

    phase_three = ENTRY_26847_PHASES[3]
    phase_three_guard = guards[phase_three]
    assert JointRadix6Source.from_source(14).candidate_family == ENTRY_4721
    assert not phase_three_guard.admits(14)
    assert phase_three_guard.admits(34)


def test_affine_preimage_transports_minimum_source_bound() -> None:
    action = DyadicTerminalFieldAction.one_run(1)
    target = SourceCongruence(2, 6, minimum_source=5)
    pulled = target.pullback(action)
    assert pulled is not None
    assert pulled == SourceCongruence(1, 4, minimum_source=3)
    assert not pulled.admits(1)
    assert pulled.admits(5)


def test_poisoned_guard_cannot_strip_the_parity_source_authority() -> None:
    action = DyadicTerminalFieldAction.one_run(1)
    with pytest.raises(ValueError, match="imply"):
        CrossFamilyPortAction(action, SourceCongruence(), 1, None)
    issued = CrossFamilyPortAction(action, SourceCongruence(1, 2), 1, None, (19,))
    with pytest.raises(ValueError, match="imply"):
        replace(issued, guard=SourceCongruence(0, 2))
    with pytest.raises(ValueError, match="outside"):
        issued.endpoint(20)


def test_external_event_count_and_clock_cannot_forge_growth_moments() -> None:
    action = DyadicTerminalFieldAction.one_run(1)
    guard = SourceCongruence(1, 2)
    with pytest.raises(ValueError, match="event count.*gain"):
        CrossFamilyPortAction(action, guard, 0, None)

    authentic = SkewQuadraticClock.atom(1, precision=8)
    forged_moments = replace(authentic, linear=1, quadratic=3)
    assert forged_moments.value == action.offset % (1 << forged_moments.precision)
    with pytest.raises(TypeError, match="checked internal producer"):
        CrossFamilyPortAction(action, guard, 1, forged_moments)


def test_issued_clock_seal_rejects_replace_and_mutation_before_readout() -> None:
    with BoundaryActionTemplateMemo(ResourceLedger()) as templates:
        chain = select_unified_skew_chain(19, 128, templates=templates)
    assert chain is not None
    joined = chain.source_closed_port_action()
    clock = joined.clock
    assert clock is not None
    with pytest.raises(TypeError, match="checked internal producer"):
        replace(joined, _clock=clock)

    object.__setattr__(clock, "linear", (clock.linear + 1) % (1 << clock.precision))
    with pytest.raises(ValueError, match="issuance seal"):
        joined.endpoint(chain.source)
    with pytest.raises(ValueError, match="issuance seal"):
        _ = joined.clock


def test_chain_source_guard_and_power_preserve_exact_normalized_word() -> None:
    with BoundaryActionTemplateMemo(ResourceLedger()) as templates:
        chain = select_unified_skew_chain(19, 128, templates=templates)
    assert chain is not None
    joined = chain.source_closed_port_action()
    assert joined.admits(chain.source)
    assert joined.endpoint(chain.source) == chain.endpoint
    assert joined.action == chain.fields
    assert joined.clock == chain.clock
    assert joined.source_trace == tuple(seam.source % 160 for seam in chain.seams)

    for multiplier in (1, 2):
        other = chain.source + multiplier * joined.guard.modulus
        assert joined.admits(other)
        foreign_endpoint, foreign_word = _normalized(other, chain.normalized_symbols)
        assert foreign_word == _normalized(chain.source, chain.normalized_symbols)[1]
        assert joined.endpoint(other) == foreign_endpoint
        current = other
        for seam in chain.seams:
            try:
                candidate_family_guard(seam.identity)
            except ValueError:
                assert current % 160 == seam.source % 160
            else:
                assert (
                    JointRadix6Source.from_source(current).candidate_family
                    == seam.identity
                )
            assert seam.action.certifies(current)
            current = seam.action.endpoint(current)
        assert current == foreign_endpoint
    assert chain.source_closed_temporal_power(1) == joined

    observation = chain.observation(difference_places=4, include_walsh64=True)
    family_ports = observation["source_closed_cross_family_ports"]
    assert isinstance(family_ports, dict)
    ports = family_ports["root_difference_ports"]
    assert isinstance(ports, dict)
    assert ports["endpoint"] == chain.endpoint
    assert ports["endpoint_f5"] == chain.endpoint % 5
    differences = ports["difference_fields"]
    assert isinstance(differences, dict)
    assert set(differences) == {"3", "6", "10", "64"}
    radix64 = differences["64"]
    assert isinstance(radix64, dict)
    walsh = radix64["walsh64_mod5"]
    assert isinstance(walsh, tuple)
    assert len(walsh) == 64
    scope = family_ports["scope"]
    assert isinstance(scope, str)
    assert "maximal named-family authority" in scope


def test_temporal_power_is_bounded_and_does_not_expand_trace() -> None:
    action = DyadicTerminalFieldAction.one_run(1).then(
        DyadicTerminalFieldAction.zero_run(1)
    )
    guarded = CrossFamilyPortAction(action, SourceCongruence(1, 20), 1, None, (1, 2))
    ledger = ResourceLedger()
    powered = guarded.power(64, max_coefficient_bits=2_048, ledger=ledger)
    assert powered is not None
    assert (
        ledger.counters[collatz_keys.COLLATZ_CROSS_FAMILY_ACTION_COMPOSITION_ATTEMPTS]
        > 0
    )
    assert (
        ledger.counters[
            collatz_keys.COLLATZ_CROSS_FAMILY_ACTION_COMPOSITION_OPERAND_BITS
        ]
        > 0
    )
    assert (
        ledger.counters.get(
            collatz_keys.COLLATZ_CROSS_FAMILY_ACTION_COMPOSITION_REFUSALS, 0
        )
        == 0
    )
    trace = powered.trace
    assert isinstance(trace, MacroTraceGrammar)
    assert trace.length == 128
    assert trace.left is not None and trace.right is not None
    limited_ledger = ResourceLedger()
    with pytest.raises(BlockContextBudgetExceeded):
        guarded.power(64, max_coefficient_bits=8, ledger=limited_ledger)
    assert (
        limited_ledger.counters[collatz_keys.COLLATZ_CROSS_FAMILY_ACTION_POWER_REFUSALS]
        == 1
    )
    with pytest.raises(BlockContextBudgetExceeded):
        trace.materialize(max_labels=64)
