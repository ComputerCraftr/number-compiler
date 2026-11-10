"""Single physical traversal, exact mirror sheets, and failed-work cleanup."""

from collections.abc import Callable
from dataclasses import replace
from decimal import Decimal

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.polynomials.twisted_observer import (
    TwistedCylinderProjection,
    mirror_obstruction_from_buffer,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as reverse_add_keys
from number_compiler.sequences.reverse_add import temporal_mirrored_diagonal as diagonal
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.q19_occurrence import (
    ReversePairOutputOccurrence,
)
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.temporal_center11 import Center11Action
from number_compiler.sequences.reverse_add.temporal_port_quotient import (
    SymmetricCoefficientPort,
    native_decimal_string_transport,
)
from tests.support.ledger_failures import assert_empty_ledger_account
from tests.support.reference_arithmetic import literal_reverse_add


def _center11_scratch_owner(term: ReverseAddPoweredTerm) -> int:
    return assert_empty_ledger_account(
        term.resource_ledger, "reverse-center11-term-scratch"
    ).owner


def _forbidden(*_args: object, **_kwargs: object) -> None:
    raise AssertionError("unexpected source replay")


def test_center_native_stream_has_no_second_q19_successor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(SymmetricCoefficientPort, "successor_with_carry", _forbidden)
    ticks: list[int] = []
    visits: list[int] = []
    packet = diagonal.center11_interval_packet(
        196, 256, on_tick_start=ticks.append, on_coefficient_visits=visits.append
    )
    assert len(ticks) == len(visits) == 256
    assert visits == [width // 2 + 1 for width in ticks]
    assert packet["duration"] == 256
    assert packet["target_width"] == len(digits_lsd(literal_reverse_add(196, 256), 10))


def test_center_rebinding_leaves_reusable_scratch_empty_before_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = ReverseAddPoweredTerm(196, 8, max_context_nodes=100_000)
    original = native_decimal_string_transport
    failures_before = term.resource_ledger.snapshot().counters.get(
        reverse_add_keys.REVERSE_CENTER11_FAILED_WORK, 0
    )

    def rebound(
        source_text: str,
        steps: int,
        *,
        max_width: int,
        on_tick_start: Callable[[int], None] | None,
        on_tick_complete: Callable[[str, Decimal, Decimal], None] | None,
    ) -> tuple[str, int]:
        result = original(
            source_text,
            steps,
            max_width=max_width,
            on_tick_start=on_tick_start,
            on_tick_complete=on_tick_complete,
        )
        term.generation += 1
        return result

    monkeypatch.setattr(diagonal, "native_decimal_string_transport", rebound)
    before = term.resource_ledger.nodes
    with pytest.raises(ValueError, match="changed during"):
        term.temporal_mirrored_diagonal()
    failures_after = term.resource_ledger.snapshot().counters.get(
        reverse_add_keys.REVERSE_CENTER11_FAILED_WORK, 0
    )
    assert failures_after - failures_before == 1
    assert term.resource_ledger.nodes == before
    scratch_owner = _center11_scratch_owner(term)
    owner_count = term.resource_ledger.owner_count

    term.generation = 8
    monkeypatch.setattr(diagonal, "native_decimal_string_transport", original)
    packet = term.temporal_mirrored_diagonal()
    assert packet["duration"] == 8
    assert _center11_scratch_owner(term) == scratch_owner
    assert term.resource_ledger.owner_count == owner_count


def test_center_midstream_failure_scrubs_decimal_buffers_before_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = ReverseAddPoweredTerm(196, 8, max_context_nodes=100_000)
    original = Center11Action.from_physical_ports
    failed = False

    def fail_once(
        *,
        source_width: int,
        growth: int,
        center_coefficient: int,
        carry_in: int,
        carry_out: int,
    ) -> Center11Action:
        nonlocal failed
        if not failed:
            failed = True
            raise RuntimeError("injected Center11 midstream failure")
        return original(
            source_width=source_width,
            growth=growth,
            center_coefficient=center_coefficient,
            carry_in=carry_in,
            carry_out=carry_out,
        )

    monkeypatch.setattr(Center11Action, "from_physical_ports", fail_once)
    with pytest.raises(
        RuntimeError, match="injected Center11 midstream failure"
    ) as caught:
        term.temporal_mirrored_diagonal()
    assert caught.value.__cause__ is None
    assert caught.value.__context__ is None

    frames: dict[str, dict[str, object]] = {}
    frame = caught.value.__traceback__
    while frame is not None:
        name = frame.tb_frame.f_code.co_name
        if name in (
            "completed",
            "native_decimal_string_transport",
            "_center11_interval_packet_source",
        ):
            frames[name] = frame.tb_frame.f_locals
        frame = frame.tb_next
    completed_frame = frames["completed"]
    transport_frame = frames["native_decimal_string_transport"]
    source_frame = frames["_center11_interval_packet_source"]
    assert completed_frame.get("text") is None
    assert completed_frame.get("_value") is None
    assert completed_frame.get("_reverse") is None
    assert transport_frame["source_text"] == ""
    assert transport_frame["value"] is None
    assert transport_frame["reverse"] is None
    assert source_frame["initial_text"] == ""
    assert source_frame["source_text"] == ""
    assert source_frame["final_text"] == ""

    scratch_owner = _center11_scratch_owner(term)
    owner_count = term.resource_ledger.owner_count

    monkeypatch.setattr(Center11Action, "from_physical_ports", original)
    packet = term.temporal_mirrored_diagonal()
    assert packet["duration"] == 8
    assert _center11_scratch_owner(term) == scratch_owner
    assert term.resource_ledger.owner_count == owner_count


def test_center_refuses_before_native_source_decode(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = ReverseAddPoweredTerm(196, 8, max_context_nodes=1)
    monkeypatch.setattr(diagonal, "native_decimal_string_transport", _forbidden)
    with pytest.raises(BlockContextBudgetExceeded):
        term.temporal_mirrored_diagonal()
    assert term.resource_ledger.nodes == 0


def test_output_entrypoints_authenticate_once_and_reject_forged_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    original = ReversePairQ19OutputOwner.validate
    calls = 0

    def counted(
        self: ReversePairQ19OutputOwner, source: ReversePairOutputOccurrence
    ) -> None:
        nonlocal calls
        calls += 1
        original(self, source)

    monkeypatch.setattr(ReversePairQ19OutputOwner, "validate", counted)
    try:
        assert tuple(owner.iter_digits(owner.initial)) == (7, 8, 8)
        assert calls == 1
        tuple(owner.iter_pair_values(owner.initial))
        assert calls == 2
        with pytest.raises(ValueError, match="not issued"):
            tuple(owner.iter_digits(replace(owner.initial)))
    finally:
        owner.dispose()
    assert ledger.nodes == ledger.entries == 0


def test_finite_cochain_avoids_full_grammar_summary_and_dag_fold(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add import radix19_cochain

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    monkeypatch.setattr(ReversePairQ19OutputOwner, "validate", _forbidden)
    monkeypatch.setattr(radix19_cochain, "fold_slp_dag", _forbidden)
    try:
        before = ledger.nodes, ledger.entries
        result = owner.radix19_cochain(owner.initial, z=10, modulus=1000)
        assert result.normalized_polynomial() == 887
        assert (ledger.nodes, ledger.entries) == before
    finally:
        owner.dispose()
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize("sheet", (1, 2, 3, 5, 100))
def test_buffered_sheets_equal_independent_full_defect_fold(sheet: int) -> None:
    digits = (1, 3, 8, 2, 0, 9, 4, 3, 1)
    defect = tuple(digit - digits[-1 - i] for i, digit in enumerate(digits))
    width, sign = sheet, 1
    while True:
        expected = TwistedCylinderProjection.observe(defect, width=width, sign=sign)
        if expected.nonzero or width >= len(digits):
            break
        if sign == 1:
            sign = -1
        else:
            width *= 2
    assert mirror_obstruction_from_buffer(digits, first_width=sheet) == (
        expected if expected.nonzero else None
    )
