"""A finite forcing return must preserve its exact source window."""

import pytest

from number_compiler.arithmetic.fields.ordered_matrix import Matrix2
from number_compiler.sequences.reverse_add.mixed_adic_period import CheckedFiniteForcing
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def test_issued_mixed_forcing_consumes_only_the_verified_repetitions() -> None:
    term = ReverseAddPoweredTerm(196, 7)
    checked = term.certify_finite_period(period=1, repeats=2, precision=1)
    assert checked.consume(0) == 8  # 187088
    assert checked.consume(1) == 9  # 1067869
    assert checked.consume(2) == 0  # 10755470
    with pytest.raises(ValueError, match="source-verified"):
        checked.consume(3)
    with pytest.raises(ValueError, match="does not repeat"):
        term.certify_finite_period(period=1, repeats=3, precision=1)
    object.__setattr__(checked, "verified_repeats", 3)
    with pytest.raises(ValueError, match="coordinates were altered"):
        checked.consume(3)


def test_finite_forcing_requires_a_source_check() -> None:
    with pytest.raises(TypeError, match="source verification"):
        CheckedFiniteForcing(7, 8, 0, 1, 1, 2, Matrix2.identity(10), object())


@pytest.mark.parametrize("generation", (7, 8, 9))
@pytest.mark.parametrize("places", (1, 4, 12))
def test_forcing_period_matches_literal_borders_without_scalar_replay(
    generation: int, places: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    literal = 196
    previous = literal
    for _ in range(generation):
        previous = literal
        literal += int(str(literal)[::-1])
    reflected = int(str(literal)[::-1])
    modulus = 10**places
    expected_initial = literal % modulus
    expected_target = (literal + reflected) % modulus
    multiplier = 11 if len(str(literal)) > len(str(previous)) else 2
    expected_action = Matrix2(
        (multiplier, expected_target - multiplier * expected_initial, 0, 1), modulus
    )

    term = ReverseAddPoweredTerm(196, generation)
    workspace = term.source_workspace()
    try:
        term.completed_q19_occurrence()

        def reject_scalar(*_args: object, **_kwargs: object) -> int:
            raise AssertionError("forcing reconstructed scalar source digits")

        monkeypatch.setattr(ReversePairQ19OutputOwner, "digit", reject_scalar)
        for _ in range(2):
            checked = term.certify_finite_period(period=1, repeats=1, precision=places)
            assert checked.initial_residue == expected_initial
            assert checked.final_residue == expected_target
            assert checked.period_action == expected_action
            assert checked.consume(1) == expected_target
    finally:
        workspace.dispose()


def test_forcing_period_consumes_batched_source_borders(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.metric_keys.reverse_add import (
        REVERSE_Q19_BATCHED_DIGIT_REQUESTS,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    term = ReverseAddPoweredTerm(196, 7)
    workspace = term.source_workspace()
    try:
        term.completed_q19_occurrence()
        before = term.resource_ledger.counters.get(
            REVERSE_Q19_BATCHED_DIGIT_REQUESTS, 0
        )

        def reject_scalar(*_args: object, **_kwargs: object) -> int:
            raise AssertionError("forcing reconstructed scalar source digits")

        monkeypatch.setattr(ReversePairQ19OutputOwner, "digit", reject_scalar)
        checked = term.certify_finite_period(period=1, repeats=2, precision=1)
        assert checked.consume(2) == 0
        assert (
            term.resource_ledger.counters[REVERSE_Q19_BATCHED_DIGIT_REQUESTS] - before
            == 3
        )
    finally:
        workspace.dispose()


@pytest.mark.parametrize("after_release", (False, True))
def test_forcing_scratch_release_failure_is_reconciled(
    after_release: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    term = ReverseAddPoweredTerm(196, 7)
    workspace = term.source_workspace()
    try:
        term.completed_q19_occurrence()
        ledger = term.resource_ledger
        scratch = ledger.owner_count
        original_release = ledger.release
        failed = False

        def fail_once(owner: int, entries: int = 0, nodes: int = 0) -> None:
            nonlocal failed
            if owner == scratch and nodes and not failed:
                failed = True
                if after_release:
                    original_release(owner, entries=entries, nodes=nodes)
                raise RuntimeError("injected forcing scratch release failure")
            original_release(owner, entries=entries, nodes=nodes)

        with monkeypatch.context() as patch:
            patch.setattr(ledger, "release", fail_once)
            with pytest.raises(RuntimeError, match="forcing scratch release failure"):
                term.certify_finite_period(period=1, repeats=1, precision=1)

        assert failed
        assert ledger.account_usage(scratch) == (0, 0)
        assert ledger.account_status(scratch).disposed
    finally:
        workspace.dispose()


def test_forcing_failed_cleanup_keeps_original_error_and_retryable_charge(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = ReverseAddPoweredTerm(196, 7)
    workspace = term.source_workspace()
    try:
        term.completed_q19_occurrence()
        ledger = term.resource_ledger
        scratch = ledger.owner_count
        original_release = ledger.release

        def fail_release(owner: int, entries: int = 0, nodes: int = 0) -> None:
            if owner == scratch and nodes:
                raise RuntimeError("persistent forcing scratch release failure")
            original_release(owner, entries=entries, nodes=nodes)

        with monkeypatch.context() as patch:
            patch.setattr(ledger, "release", fail_release)
            with pytest.raises(
                RuntimeError, match="persistent forcing scratch release failure"
            ) as failure:
                term.certify_finite_period(period=1, repeats=1, precision=1)

        assert failure.value.__cause__ is not None
        entries, nodes = ledger.account_usage(scratch)
        assert entries == 0 and nodes > 0
        assert not ledger.account_status(scratch).disposed
        original_release(scratch, entries=entries, nodes=nodes)
        ledger.mark_disposed(scratch)
        assert ledger.account_status(scratch).disposed
    finally:
        workspace.dispose()
