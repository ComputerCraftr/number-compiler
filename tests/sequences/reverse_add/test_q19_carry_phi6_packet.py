"""Literal checks for the demanded source-issued Q19 carry/Phi6 packet."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace
from itertools import product
from random import Random

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import SLPNode
from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.decimal_pair_partition import (
    DECIMAL_PAIR_BANDS,
    decimal_pair_partition,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add import q19_output_publication
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.q19_word_summary import (
    Q19CarryPhi6Summary,
    Q19CarryPhi6WordSummary,
    Q19Summary,
)
from number_compiler.sequences.reverse_add.temporal_matrix7_port import (
    Mod7CarryPortAction,
)


def _fold(pairs: tuple[int, ...]) -> Q19CarryPhi6Summary:
    result = Q19CarryPhi6Summary.identity()
    for pair in pairs:
        result = result.then(Q19CarryPhi6Summary.atom(pair))
    return result


def _literal_carries(pairs: tuple[int, ...], incoming: int) -> tuple[int, ...]:
    carry = incoming
    result: list[int] = []
    for pair in pairs:
        carry = int(pair + carry >= 10)
        result.append(carry)
    return tuple(result)


def _word7(bits: tuple[int, ...], root: int) -> int:
    return sum(bit * pow(root, index, 7) for index, bit in enumerate(bits)) % 7


def _phi6(bits: tuple[int, ...]) -> tuple[int, int]:
    at3, at5 = _word7(bits, 3), _word7(bits, 5)
    high = 4 * (at5 - at3) % 7
    return ((at3 - 3 * high) % 7, high)


def _pairs(seed: int) -> tuple[int, ...]:
    digits = digits_lsd(seed, 10)
    return tuple(a + b for a, b in zip(digits, reversed(digits), strict=True))


def _spatial_key(pairs: tuple[int, ...]) -> tuple[object, ...]:
    q19 = Q19Summary.identity()
    for pair in pairs:
        q19 = q19.then(Q19Summary.atom(pair))
    phi6 = _fold(pairs)
    return (
        q19.domain,
        q19.f9,
        phi6.length % 6,
        phi6.bands3,
        phi6.carry3,
        phi6.carry5,
    )


def test_both_forward_carry_responses_match_literal_words() -> None:
    for length in range(1, 5):
        for pairs in product((0, 8, 9, 10, 18), repeat=length):
            summary = _fold(pairs)
            for incoming in (0, 1):
                carries = _literal_carries(pairs, incoming)
                assert summary.carry3[incoming] == _word7(carries, 3)
                assert summary.carry5[incoming] == _word7(carries, 5)
                assert summary.carry_phi6(incoming) == _phi6(carries)
                assert summary.carry_exit(incoming) == carries[-1]
            assert summary.bands3 == tuple(
                _word7(tuple(decimal_pair_partition(s).masks[i] for s in pairs), 3)
                for i in range(5)
            )
    with pytest.raises(ValueError, match="carry"):
        Q19CarryPhi6Summary.atom(9).carry_phi6(2)


def test_composition_repetition_and_spatial_copy_return() -> None:
    random = Random(196)
    for _ in range(100):
        pairs = tuple(random.randrange(19) for _ in range(random.randrange(1, 30)))
        cut = random.randrange(len(pairs) + 1)
        assert _fold(pairs) == _fold(pairs[:cut]).then(_fold(pairs[cut:]))
        block = _fold(pairs)
        copies = random.randrange(1, 9)
        assert block.repeat(copies) == _fold(pairs * copies)
        assert _spatial_key(pairs * copies) == _spatial_key(pairs * (copies + 126))
    long_wire = Q19CarryPhi6Summary.atom(9).repeat(10**12)
    assert long_wire.length == 10**12
    assert long_wire.carry_exit(0) == 0
    assert long_wire.carry_exit(1) == 1


@pytest.mark.parametrize("seed", (196, 168, 99, 999, 123456789))
def test_issued_packet_matches_independent_decimal_masks(seed: int) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        pairs = _pairs(seed)
        before_resources = ledger.entries, ledger.nodes
        packet = owner.issued_carry_phi6_packet(owner.initial)
        assert (ledger.entries, ledger.nodes) == before_resources
        carries = _literal_carries(pairs, 0)
        assert carries
        final_carry = carries[-1]
        assert packet["source_pair_width"] == len(pairs)
        assert packet["occurrence_temporal_steps"] == 1
        assert packet["spatial_orientation"] == "lsd_to_msd"
        assert packet["scope"] == "whole symmetric Q19 occurrence; spatial carry only"
        assert packet["complete_temporal_successor_certified"] is False
        assert packet["forward_carry_at3"] == (
            _word7(_literal_carries(pairs, 0), 3),
            _word7(_literal_carries(pairs, 1), 3),
        )
        assert packet["forward_carry_at5"] == (
            _word7(_literal_carries(pairs, 0), 5),
            _word7(_literal_carries(pairs, 1), 5),
        )
        assert (
            packet["propagated_carry_mod70"]
            == sum(bit * 10**index for index, bit in enumerate(carries)) % 70
        )
        assert packet["propagated_carry_phi6_mod7"] == _phi6(carries)
        gt = tuple(int(pair > 9) for pair in pairs)
        eq = tuple(int(pair == 9) for pair in pairs)
        assert (
            packet["raw_gt_mask_mod70"]
            == sum(bit * 10**index for index, bit in enumerate(gt)) % 70
        )
        assert (
            packet["raw_eq_mask_mod70"]
            == sum(bit * 10**index for index, bit in enumerate(eq)) % 70
        )
        band_mod70 = packet["five_band_mod70"]
        band_phi6 = packet["five_band_phi6_mod7"]
        assert isinstance(band_mod70, dict)
        assert isinstance(band_phi6, dict)
        for index, band in enumerate(DECIMAL_PAIR_BANDS):
            bits = tuple(decimal_pair_partition(pair).masks[index] for pair in pairs)
            assert (
                band_mod70[band.value]
                == sum(bit * 10**position for position, bit in enumerate(bits)) % 70
            )
            assert band_phi6[band.value] == _phi6(bits)
        assert packet["raw_gt_phi6_mod7"] == _phi6(gt)
        assert packet["raw_eq_phi6_mod7"] == _phi6(eq)
        internal = int("".join(map(str, carries[:-1]))) if len(carries) > 1 else 0
        difference = (internal + 3 * final_carry) % 7
        port = Mod7CarryPortAction.from_port(
            difference_mod7=difference, growth=final_carry
        )
        assert packet["aligned_difference_mod7"] == difference
        assert packet["source_mod7_affine_action"] == (
            port.multiplier,
            port.correction,
        )
        normalized = seed + int(str(seed)[::-1])
        successor = normalized + int(str(normalized)[::-1])
        assert port.apply(normalized % 7) == successor % 7
        assert packet["mod7_affine_source_step"] == 1
        assert packet["mod7_affine_target_step"] == 2
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_demand_fold_budget_refusal_releases_scratch() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    try:
        before = ledger.entries, ledger.nodes
        ledger.max_nodes = ledger.nodes + 1
        with pytest.raises(BlockContextBudgetExceeded):
            owner.issued_carry_phi6_packet(owner.initial)
        assert (ledger.entries, ledger.nodes) == before
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_reentrant_disposal_during_projection_preserves_original_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    fold = fold_slp_dag
    cancelled = False

    def interrupted_fold(
        arena: LedgerSLPArena,
        root: int,
        *,
        empty_value: Q19CarryPhi6WordSummary,
        terminal_value: Callable[[int], Q19CarryPhi6WordSummary],
        concatenate: Callable[
            [Q19CarryPhi6WordSummary, Q19CarryPhi6WordSummary],
            Q19CarryPhi6WordSummary,
        ],
        repeat: Callable[[Q19CarryPhi6WordSummary, int], Q19CarryPhi6WordSummary],
        on_pending: Callable[[SLPNode], None],
    ) -> dict[int, Q19CarryPhi6WordSummary]:
        def cancel(node: SLPNode) -> None:
            nonlocal cancelled
            if not cancelled:
                cancelled = True
                owner.dispose()
                raise RuntimeError("injected projection cancellation")
            on_pending(node)

        return fold(
            arena,
            root,
            empty_value=empty_value,
            terminal_value=terminal_value,
            concatenate=concatenate,
            repeat=repeat,
            on_pending=cancel,
        )

    monkeypatch.setattr(q19_output_publication, "fold_slp_dag", interrupted_fold)
    try:
        with pytest.raises(RuntimeError, match="injected projection cancellation"):
            owner.issued_carry_phi6_packet(owner.initial)
        assert cancelled
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_packet_is_demand_only_and_does_not_render_or_refold(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    try:

        def forbidden(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("unrequested projection, digit render, or base refold")

        with monkeypatch.context() as patch:
            patch.setattr(owner, "_demanded_carry_phi6_summary", forbidden)
            owner.validate(owner.initial)
            assert tuple(owner.iter_digits(owner.initial))
        with monkeypatch.context() as patch:
            patch.setattr(owner, "_build_word_summary", forbidden)
            patch.setattr(owner, "_stream_pair_values", forbidden)
            assert (
                owner.issued_carry_phi6_packet(owner.initial)["source_pair_width"] == 3
            )
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_packet_rejects_foreign_stale_and_deeply_mutated_source() -> None:
    ledger = ResourceLedger()
    other_ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    foreign = ReversePairQ19OutputOwner(other_ledger, digits_lsd(196, 10), base=10)
    occurrence = owner.initial
    try:
        with pytest.raises(ValueError):
            foreign.issued_carry_phi6_packet(occurrence)
        with pytest.raises(ValueError):
            owner.issued_carry_phi6_packet(replace(occurrence))
        terminal = owner.arena.existing_terminal(7)
        assert terminal is not None
        node = owner.arena.nodes[terminal]
        object.__setattr__(node, "symbol", 8)
        try:
            with pytest.raises(ValueError, match="terminal binding"):
                owner.issued_carry_phi6_packet(occurrence)
        finally:
            object.__setattr__(node, "symbol", 7)
        summary = owner.published_word_summary(occurrence.root)
        original_first = summary.first_symbol
        object.__setattr__(summary, "first_symbol", 8)
        try:
            with pytest.raises(ValueError, match="first pair metadata"):
                owner.issued_carry_phi6_packet(occurrence)
        finally:
            object.__setattr__(summary, "first_symbol", original_first)
        assert owner.issued_carry_phi6_packet(occurrence)["source_pair_width"] == 3
    finally:
        foreign.dispose()
        owner.dispose()
    with pytest.raises(ValueError):
        owner.issued_carry_phi6_packet(occurrence)
    assert ledger.entries == ledger.nodes == 0
    assert other_ledger.entries == other_ledger.nodes == 0


def test_spatial_phi6_key_does_not_merge_temporal_successors() -> None:
    assert _spatial_key(_pairs(101)) == _spatial_key(_pairs(112))
    assert 101 + 101 == 202
    assert 112 + 211 == 323
    assert _spatial_key(_pairs(202)) != _spatial_key(_pairs(323))
