"""Independent finite-source / CRT / binary-pivot Mahler safety regressions."""

from __future__ import annotations

from collections.abc import Callable
from fractions import Fraction
from random import Random
from typing import cast
from unittest.mock import patch

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.boolean_counter import BinaryBooleanCarryAction
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational as Q
from number_compiler.sequences.antihydra import payload_audit
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.mahler_joint_future import (
    MahlerJointFutureAction as M,
)
from number_compiler.sequences.antihydra.mahler_joint_future import (
    MahlerJointInteriorWindow,
)
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MahlerSourceBoundSafetyAction as S,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm


def _fraction(x: Q) -> Fraction:
    return Fraction(x.numerator, x.denominator)


def _record(value: object) -> dict[str, object]:
    if not isinstance(value, dict):
        raise TypeError("expected an object packet")
    return cast(dict[str, object], value)


def _integer(record: dict[str, object], name: str) -> int:
    value = record[name]
    if type(value) is not int:
        raise AssertionError(f"{name} is not an integer packet field")
    return value


def _boolean(record: dict[str, object], name: str) -> bool:
    value = record[name]
    if type(value) is not bool:
        raise AssertionError(f"{name} is not a Boolean packet field")
    return value


def _literal(source: int, fraction: Fraction, width: int) -> tuple[int, Fraction, bool]:
    safe = Fraction(0) <= fraction < Fraction(1, 2)
    for _ in range(width):
        e = source & 1
        source = (3 * source + e) // 2
        fraction = (3 * fraction - e) / 2
        safe = safe and Fraction(0) <= fraction < Fraction(1, 2)
    return source, fraction, safe


def test_all_source_cylinders_exact_against_literal_fractional_oracle() -> None:
    for width in range(8):
        for residue in range(1 << width):
            action = M.from_source_prefix(residue, width)
            assert action.residue == residue
            for fiber in (0, 1, 19, 1001):
                source = residue + (1 << width) * fiber
                assert action.integer_admits(source)
                for numerator in range(24):
                    fraction = Fraction(numerator, 48)
                    endpoint, end_fraction, safe = _literal(source, fraction, width)
                    rational = Q(fraction.numerator, fraction.denominator)
                    assert action.admits(source, rational) == safe
                    assert action.endpoint(source) == endpoint
                    if safe:
                        actual = action.fraction_endpoint(rational)
                        assert _fraction(actual) == end_fraction
                        assert action.apply(source, rational) == (endpoint, actual)


def test_source_cylinder_concat_associative_not_only_minplus() -> None:
    for a in range(8):
        for b in range(8):
            for c in range(4):
                u, v, w = (M.from_source_prefix(x, 3) for x in (a, b, c))
                assert u.then(v).then(w) == u.then(v.then(w))
                assert u.then(v).then(w).safety == u.safety.then(v.safety).then(
                    w.safety
                )


def test_symbolic_successors_are_selected_by_high_fiber_parity() -> None:
    for source in range(65):
        for width in range(7):
            old = M.from_source_prefix(source, width)
            selected = old.endpoint(source) & 1
            for option in old.successor_branches():
                assert option.high_fiber_parity == (
                    option.epsilon ^ (old.endpoint_residue & 1)
                )
                assert option.action.residue == (
                    old.residue + old.source_modulus * option.high_fiber_parity
                )
                if option.epsilon == selected:
                    assert option.action.integer_admits(source)
                else:
                    assert not option.action.integer_admits(source)
                assert not option.action.guard.empty
            for e in (0, 1):
                child = old.then(M.bit(e))
                for f in (Q(0), Q(1, 4), Q(1, 3), Q(2, 5)):
                    next_source, _, ok = _literal(source, _fraction(f), width + 1)
                    assert child.admits(source, f) == (ok and e == selected), (
                        source,
                        width,
                        e,
                        f,
                        next_source,
                    )


def test_pumped_event_grammar_no_fixed_max_event() -> None:
    for exponent in (1, 2, 3, 7, 13, 64, 512):
        event = M.event(exponent)
        assert event.extent == exponent
        assert event.residue == 1 << (exponent - 1)
        assert event.innovation == 1 << (exponent - 1)
        assert event.safety.offset_hat == -12 * (1 << (exponent - 1))
        assert event.guard.lower == Q(1 << (exponent - 1), 3**exponent)
        assert event.guard.upper == (
            Q(1, 2) if exponent == 1 else Q(1 << (exponent - 2), 3 ** (exponent - 1))
        )
    with pytest.raises(BlockContextBudgetExceeded):
        M.event(9000)


def test_zero_run_closed_form_matches_binary_composition_and_source_prefixes() -> None:
    for length in (0, 1, 2, 3, 7, 16, 64, 128):
        direct = M.zero_run(length)
        composed = M.bit(0).power(length)
        assert direct == composed
        if length:
            assert direct.guard.lower == Q(0)
            assert direct.guard.upper == Q(1 << (length - 1), 3**length)
            assert direct.safety.cap_hat == 9 * (1 << length)

    # The accelerated source builder is compared to a separately assembled
    # one-bit action for every physical parity, including a clipped final run.
    for source in range(64):
        for length in range(17):
            accelerated = M.from_source_prefix(source, length)
            literal = M()
            current = source
            for _ in range(length):
                bit = current & 1
                literal = literal.then(M.bit(bit))
                current = (3 * current + bit) // 2
            assert accelerated == literal
            assert accelerated.endpoint(source) == current

    with pytest.raises(ValueError):
        M.zero_run(True)
    with pytest.raises(ValueError):
        M.zero_run(1, max_extent=0)
    with pytest.raises(ValueError):
        M.from_source_prefix(0, True)


def test_source_prefix_uses_one_composition_for_a_maximal_zero_run(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    compositions = 0
    original = M.then

    def counted(self: M, after: M) -> M:
        nonlocal compositions
        compositions += 1
        return original(self, after)

    monkeypatch.setattr(M, "then", counted)
    action = M.from_source_prefix(0, 128)
    assert action.endpoint(0) == 0
    assert action.extent == 128
    assert compositions == 1


def test_repeat_source_obstruction_and_fractional_guard() -> None:
    word = M.bit(0).then(M.bit(0)).then(M.bit(1))
    assert word.residue == 4
    assert word.innovation == 4
    assert word.max_fixed_word_repetitions(4) == 1
    assert word.max_fixed_word_repetitions(20) == 2
    assert word.power(2).residue == 20
    for n in (0, 1, 2, 3, 6, 11):
        powered = word.power(n)
        repeated = M()
        for _ in range(n):
            repeated = repeated.then(word)
        assert powered == repeated
    with pytest.raises(ValueError):
        word.max_fixed_word_repetitions(0)
    with pytest.raises(ValueError):
        word.max_fixed_word_repetitions(5)
    with pytest.raises(BlockContextBudgetExceeded):
        word.power(10000)


def test_binary_counter_five_adic_crt_and_difference_borrow_oracles() -> None:
    random = Random(152607)
    for _ in range(170):
        source = random.randrange(1, 1 << 64)
        extent = random.randrange(0, 10)
        action = M.from_source_prefix(source, extent)
        bits = random.randrange(4, 32)
        places = random.randrange(1, min(bits, 8) + 1)
        win = action.source_window(source, bits=bits, decimal_places=places)
        expected = (3 * win.source_endpoint + (win.source_endpoint & 1)) // 2
        assert win.next_source == expected
        assert win.epsilon == win.source_endpoint % 2
        assert win.next_binary == expected % (1 << bits)
        assert win.next_five == expected % 5**places
        assert win.next_decimal == expected % 10**places
        assert win.counter.apply(0)[0] == (win.source_binary + win.addend_binary) >> (
            bits + 1
        )
        assert win.counter.next_carries[0] in (0, 1)
        assert win.counter.next_carries[1] in (0, 1)
        assert win.counter.harmonics[0].length_mod6 == (bits + 1) % 6
        a, b, modulus = action.five_adic_affine(places)
        assert (a * source + b) % modulus == win.source_endpoint % modulus
        # Independent digitwise borrows, not the Boolean counter calculation.
        borrow = observed = 0
        for i in range(bits):
            borrow = int(
                ((win.next_source >> i) & 1)
                < (((win.source_endpoint >> i) & 1) + borrow)
            )
            observed |= borrow << i
        assert observed == win.binary_difference_borrows
        borrow = observed = 0
        for i in range(places):
            old = win.source_decimal // (10**i) % 10
            new = win.next_decimal // (10**i) % 10
            borrow = int(new < old + borrow)
            observed |= borrow << i
        assert observed == win.decimal_difference_borrows


def test_interior_window_is_a_proven_high_fiber_crt_class() -> None:
    random = Random(264625)
    for _ in range(90):
        level = random.randrange(0, 17)
        root = M.from_source_prefix(random.randrange(0, 1 << level), level)
        k = random.randrange(0, 10**8)
        bits = random.randrange(3, 24)
        places = random.randrange(1, bits + 1)
        fine = root.interior_fiber_window(k, bits=bits, decimal_places=places)
        assert fine.fiber_residue == k % fine.fiber_modulus
        for multiple in (0, 1, 19, 101):
            source = root.residue + root.source_modulus * (
                fine.fiber_residue + multiple * fine.fiber_modulus
            )
            concrete = root.source_window(source, bits=bits, decimal_places=places)
            assert concrete.epsilon == fine.window.epsilon
            assert concrete.next_binary == fine.window.next_binary
            assert concrete.next_five == fine.window.next_five
            assert concrete.next_decimal == fine.window.next_decimal
            assert concrete.xor_mask == fine.window.xor_mask
            assert (
                concrete.binary_difference_borrows
                == fine.window.binary_difference_borrows
            )
            assert (
                concrete.decimal_difference_borrows
                == fine.window.decimal_difference_borrows
            )
            assert concrete.counter.semantic_id == fine.window.counter.semantic_id


def test_joint_source_not_substitutable_and_fractional_selector_is_strict() -> None:
    block = M.bit(0)
    good = block.source_window(2, bits=8, decimal_places=3, fraction=Q(1, 4))
    assert good.fraction_authenticated
    assert good.next_fraction == Q(3, 8)
    assert good.next_branch_safe
    unsafe = block.source_window(2, bits=8, decimal_places=3, fraction=Q(1, 6))
    assert unsafe.next_fraction == Q(1, 4)
    assert not unsafe.next_branch_safe
    with pytest.raises(ValueError):
        block.source_window(3)
    with pytest.raises(ValueError):
        block.source_window(2, fraction=Q(1, 3))
    with pytest.raises(ValueError):
        block.source_window(2, bits=2, decimal_places=3)
    with pytest.raises(ValueError):
        M(1, 1, 0)
    with pytest.raises(ValueError):
        M(1, 1, 1, safety=S.one_bit(0))


def test_production_source_8_demand_switches_off_unowned_observer() -> None:
    for n in (1, 2, 3, 8, 16):
        term = AntihydraArithmeticTerm(n, shared_cache=False)
        result = term.result()
        ordinary = associated_action(result)
        assert "source_bound_joint_successor" not in ordinary
        packet = associated_action(result, include_radix_ports=True)
        joint = _record(packet["source_bound_joint_successor"])
        radix = _record(packet["source_bound_radix6_difference"])
        assert "joint_source_successor" not in radix
        assert _integer(joint, "source_residue") == 7 % (1 << n)
        assert _integer(joint, "source_modulus") == 1 << n
        assert _integer(joint, "source_endpoint") == result.h - 1
        next_bit = _integer(joint, "selected_next_bit")
        assert next_bit == ((result.h - 1) & 1)
        expected_next = (3 * (result.h - 1) + next_bit) // 2
        assert _integer(joint, "selected_next_source") == expected_next
        assert _integer(joint, "decimal_next_low") == expected_next % 10000
        assert _boolean(joint, "interior_fiber_exact")
        fiber_residue = _integer(joint, "interior_fiber_residue")
        fiber_modulus = _integer(joint, "interior_fiber_modulus")
        assert 0 <= fiber_residue < fiber_modulus
        affine = cast(tuple[int, int, int], joint["five_adic_affine"])
        period = _integer(joint, "five_primary_multiplier_period")
        assert pow(affine[0], period, affine[2]) == 1
        assert _boolean(joint, "guard_empty") == (n >= 2)
        assert not _boolean(joint, "all_time_claim")


def test_production_joint_packet_reads_one_concrete_source_window() -> None:
    term = AntihydraArithmeticTerm(8, shared_cache=False)
    result = term.result()
    original = M.source_window
    calls = 0

    def counted(
        self: M,
        source: int,
        *,
        bits: int = 16,
        decimal_places: int = 4,
        fraction: Q | None = None,
    ) -> MahlerJointInteriorWindow:
        nonlocal calls
        calls += 1
        return original(
            self,
            source,
            bits=bits,
            decimal_places=decimal_places,
            fraction=fraction,
        )

    with patch.object(M, "source_window", counted):
        packet = associated_action(result, include_radix_ports=True)
        repeated = associated_action(result, include_radix_ports=True)
    assert calls == 1
    joint = _record(packet["source_bound_joint_successor"])
    assert _record(repeated["source_bound_joint_successor"]) == joint
    assert _boolean(joint, "interior_fiber_exact")


def test_warm_joint_packet_does_not_rebuild_window_semantics() -> None:
    term = AntihydraArithmeticTerm(8, shared_cache=False)
    result = term.result()
    associated_action(result, include_radix_ports=True)
    with (
        patch.object(
            BinaryBooleanCarryAction,
            "from_words",
            side_effect=AssertionError("warm window rebuilt its Boolean action"),
        ),
    ):
        associated_action(result, include_radix_ports=True)


@pytest.mark.parametrize("upgrade_existing", [False, True])
def test_window_contract_failure_restores_authority_and_allows_retry(
    monkeypatch: pytest.MonkeyPatch, upgrade_existing: bool
) -> None:
    term = AntihydraArithmeticTerm(8, shared_cache=False)
    result = term.result()
    if upgrade_existing:
        associated_action(result)
    workspace = term.mahler_workspace
    if upgrade_existing:
        assert workspace is not None and workspace.window_memo_container is None
    else:
        assert workspace is None
    active_before = frozenset(
        item.owner for item in term.ledger.inventory() if not item.disposed
    )
    query_before = frozenset(
        item.owner
        for item in term.ledger.inventory()
        if not item.disposed and item.role == "query_memo"
    )

    def fail_registration(*_args: object, **_kwargs: object) -> None:
        raise RuntimeError("injected Antihydra contract failure")

    with monkeypatch.context() as local:
        local.setattr(
            payload_audit,
            "register_antihydra_payload_contract",
            fail_registration,
        )
        with pytest.raises(RuntimeError, match="injected Antihydra contract failure"):
            associated_action(result, include_radix_ports=True)

    assert term.mahler_workspace is workspace
    if workspace is not None:
        assert workspace.window_memo_container is None
        assert workspace.window_memo_owner is None
        assert not workspace.window_contract_registered
    assert (
        frozenset(item.owner for item in term.ledger.inventory() if not item.disposed)
        == active_before
    )
    assert (
        frozenset(
            item.owner
            for item in term.ledger.inventory()
            if not item.disposed and item.role == "query_memo"
        )
        == query_before
    )
    assert term.ledger.audit_payload_contracts().owns_root(
        "antihydra", term, ledger=term.ledger
    )
    assert term.ledger.audit_payload_contracts().owns_root(
        "antihydra", term, ledger=term.ledger
    )
    associated_action(result, include_radix_ports=True)
    assert term.mahler_workspace is not None
    assert term.mahler_workspace.window_memo_container is not None
    if workspace is not None:
        assert term.mahler_workspace is workspace
    assert term.ledger.audit_payload_contracts().invalid == frozenset()


def test_root_transfer_canonical_source_guard_equals_exact_discovery() -> None:
    for n in range(25):
        result = AntihydraArithmeticTerm(n, shared_cache=False).result()
        from_literal = M.from_source_prefix(7, n)
        via_transfer = M.from_root_seven_transfer(n, result.h, from_literal.safety)
        assert via_transfer == from_literal


def test_root_transfer_rejects_endpoint_with_another_source_prefix() -> None:
    forged_safety = S(2, -12, 42)
    with pytest.raises(ValueError):
        M.from_root_seven_transfer(2, 17, forged_safety)
    with pytest.raises(ValueError):
        M.from_root_seven_transfer(2, 1 << 10_000, forged_safety)

    with pytest.raises(ValueError, match="workspace-issued"):
        forged_safety.demanded_tripling_ports(
            base=6,
            places=4,
            source=7,
            endpoint_h=17,
        )


def test_root_transfer_rejects_endpoint_and_public_gain_poison() -> None:
    result = AntihydraArithmeticTerm(8, shared_cache=False).result()
    action = M.from_source_prefix(7, 8)
    with pytest.raises(ValueError):
        M.from_root_seven_transfer(8, result.h + 1, action.safety)
    gain_constructor = cast(Callable[..., object], M.from_root_seven_transfer)
    with pytest.raises(TypeError):
        gain_constructor(8, result.h, action.safety, gain=3**8 + 2)


def test_joint_future_hard_extent_ceiling_cannot_be_raised_by_callers() -> None:
    with pytest.raises(BlockContextBudgetExceeded):
        M.event(5000, max_extent=10_000)
    with pytest.raises(BlockContextBudgetExceeded):
        M.bit(0).power(5000, max_extent=10_000)
    with pytest.raises(BlockContextBudgetExceeded):
        M(extent=5000)


def test_interior_window_publication_seal_detects_mutated_payload() -> None:
    window = M.from_source_prefix(2, 1).source_window(2, bits=8, decimal_places=3)
    with pytest.raises(TypeError):
        MahlerJointInteriorWindow()
    object.__setattr__(window, "next_binary", window.next_binary ^ 1)
    with pytest.raises(ValueError, match="publication seal"):
        window.verify_issued()


def test_interior_window_seal_snapshots_nested_harmonic_coordinates() -> None:
    window = M.from_source_prefix(2, 1).source_window(2, bits=8, decimal_places=3)
    harmonic = window.counter.harmonics[0]
    object.__setattr__(harmonic, "phi2", (harmonic.phi2 + 1) % 5)
    with pytest.raises(ValueError, match="publication seal"):
        window.verify_issued()


def test_production_precision_memo_audits_its_window_payload() -> None:
    term = AntihydraArithmeticTerm(8, shared_cache=False)
    result = term.result()
    associated_action(result, include_radix_ports=True)
    workspace = term.mahler_workspace
    assert workspace is not None
    entries = workspace.window_memo_entries()
    assert len(entries) == 1
    window = entries[0][1]
    object.__setattr__(window, "next_binary", window.next_binary ^ 1)
    with pytest.raises(ValueError, match="publication seal"):
        workspace.validate(result)
