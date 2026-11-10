"""Independent exact checks for Mahler carry/innovation recovery and issued ports."""

from __future__ import annotations

from random import Random

import pytest

from number_compiler.sequences.collatz.diagonal_source_window import (
    CollatzDiagonalWindow,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalEndpointAction,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction as Field,
)
from number_compiler.sequences.collatz.mahler_joint_carry import (
    MahlerCarryProgram,
    MahlerFutureCarryPort,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    SourceClosedPortAction,
    SourceCongruence,
)


def _digits(x: int) -> list[int]:
    out: list[int] = []
    while x:
        x, digit = divmod(x, 10)
        out.append(digit)
    return out


def _add(dst: list[int], src: list[int], shift: int = 0, scale: int = 1) -> None:
    needed = shift + len(src)
    if len(dst) < needed:
        dst.extend([0] * (needed - len(dst)))
    for i, value in enumerate(src):
        dst[shift + i] += scale * value


def _trim(x: list[int]) -> tuple[int, ...]:
    while x and x[-1] == 0:
        x.pop()
    return tuple(x)


def _direct_oracle(
    source: int, steps: int
) -> tuple[Field, int, tuple[int, ...], tuple[int, ...]]:
    value = source
    word = Field.identity()
    innovation: list[int] = []
    carried: list[int] = []
    for i in range(steps):
        p = value & 1
        op = Field.one_run(1) if p else Field.zero_run(1)
        word = word.then(op)
        digits = _digits(value)
        m = 5 + 10 * p
        e = [(m - 15) * t for t in digits]
        if p:
            _add(e, [5])
        c: list[int] = []
        incoming = 0
        for j in range(len(digits) + 3):
            digit = digits[j] if j < len(digits) else 0
            raw = m * digit + (5 * p if j == 0 else 0) + incoming
            incoming, _ = divmod(raw, 10)
            c.append(incoming)
        assert incoming == 0
        innovation = [15 * v for v in innovation]
        carried = [15 * v for v in carried]
        _add(innovation, e, i)
        _add(carried, c, i)
        value = (m * value + 5 * p) // 10
    return word, value, _trim(innovation), _trim(carried)


def _twisted_join(
    a: tuple[int, ...], b: tuple[int, ...], da: int, db: int
) -> tuple[int, ...]:
    out: list[int] = []
    _add(out, list(a), scale=15**db)
    _add(out, list(b), shift=da)
    return _trim(out)


def _source_window(
    source: int, physical_budget: int, max_normalized: int
) -> CollatzDiagonalWindow:
    return CollatzDiagonalWindow.from_source_window(
        source,
        physical_budget,
        max_normalized=max_normalized,
        retain_field_action=False,
        record_step=lambda: None,
        reserve_bits=lambda _bits: None,
        record_work=lambda _bits: None,
    )


def test_randomized_chronological_recovery_and_twisted_composition() -> None:
    rng = Random(202611061)
    for _ in range(300):
        x = rng.randrange(1, 10**11)
        d1, d2 = rng.randrange(0, 25), rng.randrange(0, 25)
        action, mid, i1, c1 = _direct_oracle(x, d1)
        following, out, i2, c2 = _direct_oracle(mid, d2)
        composed = action.then(following)
        row = composed.mahler_chronological_cocycle(x, max_columns=180)
        assert row.source == x and row.endpoint == out
        assert row.innovation == _twisted_join(i1, i2, d1, d2)
        assert row.chronological_carries == _twisted_join(c1, c2, d1, d2)
        assert row == MahlerCarryProgram.issued(composed).chronological_cocycle(
            x, max_columns=180
        )
        assert _trim(list(row.total_defect)) == row.total_defect


def test_known_carry_difference_and_future_6305_program() -> None:
    word = Field.one_run(2)
    result = word.mahler_chronological_cocycle(23)
    assert result.endpoint == 53
    assert result.innovation == (75, 5)
    assert result.chronological_carries == (75, 53, 5)
    assert result.total_defect == (-675, -450, 3, 5)
    port = _source_window(23, 4, 2).mahler_future_carry_port()
    assert (port.target, port.parity, port.border_upper, port.border_zero_tail) == (
        53,
        1,
        16,
        4,
    )
    assert port.nested_band(53, 1) == (3, 1, 1)
    with pytest.raises(ValueError):
        port.nested_band(23, 1)


def test_powered_word_without_parity_expansion_and_external_guard() -> None:
    word = Field.one_run(1)
    power = MahlerCarryProgram.issued(word).power(2048)
    assert power.action.steps == 2048
    source = (1 << 2100) - 1
    assert power.endpoint(source) == 3**2048 * ((source + 1) >> 2048) - 1
    with pytest.raises(ValueError, match="step budget"):
        power.chronological_cocycle(source, max_steps=32)
    short = MahlerCarryProgram.issued(word).power(8)
    oracle, out, expected_innov, expected_carry = _direct_oracle(1023, 8)
    result = short.chronological_cocycle(1023, max_columns=128)
    assert result.endpoint == out
    assert (result.innovation, result.chronological_carries) == (
        expected_innov,
        expected_carry,
    )
    assert short.action.coefficient_snapshot() == oracle.coefficient_snapshot()
    odd_guard = SourceCongruence(23 % 20, 20)
    guarded = SourceClosedPortAction.create_checked(
        Field.one_run(2), odd_guard, 2, None
    )
    assert guarded.endpoint(23) == 53
    assert guarded.mahler_chronological_cocycle(23).chronological_carries == (75, 53, 5)
    with pytest.raises(ValueError, match="authenticated"):
        guarded.mahler_chronological_cocycle(7)
    with pytest.raises(ValueError, match="source-closed parity cylinder"):
        guarded.endpoint(7)


def test_issued_source_guard_and_scratch_preflight() -> None:
    action = Field.one_run(2)
    assert not action.certifies(22)
    with pytest.raises(ValueError):
        action.mahler_chronological_cocycle(22)
    reserve: list[int] = []
    result = action.mahler_chronological_cocycle(23, reserve_bits=reserve.append)
    assert result.endpoint == 53 and reserve and reserve[0] > 0

    def refuse(_bits: int) -> None:
        raise MemoryError("preflight refused")

    with pytest.raises(MemoryError, match="preflight"):
        action.mahler_chronological_cocycle(23, reserve_bits=refuse)
    with pytest.raises(ValueError, match="column budget"):
        action.mahler_chronological_cocycle(23, max_columns=2)
    with pytest.raises(ValueError, match="step budget"):
        action.mahler_chronological_cocycle(23, max_steps=1)
    zero_port = _source_window(46, 1, 1).mahler_future_carry_port()
    assert zero_port.target == 23
    assert zero_port.border_zero_tail == 0
    endpoint = DyadicTerminalEndpointAction
    assert Field.zero_run(1).producer_issued
    # The endpoint-only action is used by the cold scalar diagonal compiler.
    from number_compiler.sequences.collatz.diagonal_source_window import (
        CollatzDiagonalWindow,
    )

    w = CollatzDiagonalWindow.from_source_window(
        46,
        1,
        max_normalized=1,
        retain_field_action=False,
        record_step=lambda: None,
        reserve_bits=lambda bits: None,
        record_work=lambda bits: None,
    )
    assert type(w.action) is endpoint
    assert w.mahler_future_carry_port().target == 23


def test_scratch_refusal_precedes_endpoint_materialization(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    action = Field.one_run(2)

    def forbidden_endpoint(_self: Field, _source: int) -> int:
        raise AssertionError("endpoint was materialized before scratch admission")

    def refuse(_bits: int) -> None:
        raise MemoryError("preflight refused")

    monkeypatch.setattr(Field, "endpoint", forbidden_endpoint)
    with pytest.raises(MemoryError, match="preflight"):
        action.mahler_chronological_cocycle(23, reserve_bits=refuse)


def test_border_selector_accepts_source_window_carry_view() -> None:
    from number_compiler.sequences.collatz import border_return_grammar as br

    window = _source_window(23, 4, 2)
    port = window.mahler_future_carry_port()
    expected = br.select_border_return_macro(53, 16, max_returns=1)
    assert expected is not None
    actual = br.select_border_return_macro(
        53,
        16,
        max_returns=1,
        future_carry_port=port,
    )
    assert actual is not None
    assert actual.endpoint == expected.endpoint
    assert actual.fields.coefficient_snapshot() == (
        expected.fields.coefficient_snapshot()
    )
    assert actual.zero_tails == expected.zero_tails
    # The action already owned by the source window remains the sole issuer.
    object.__setattr__(window.action, "gain", window.action.gain + 2)
    with pytest.raises(ValueError, match="source window"):
        br.select_border_return_macro(53, 16, max_returns=1, future_carry_port=port)


def test_window_carry_view_uses_issued_endpoint_without_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The carry view delegates to the window and does not replay its action."""
    window = _source_window(23, 4, 2)
    action_type = type(window.action)

    def forbid_endpoint_replay(_action: object, _source: int) -> int:
        raise AssertionError("carry view replayed the issued endpoint")

    monkeypatch.setattr(action_type, "endpoint", forbid_endpoint_replay)
    port = window.mahler_future_carry_port()
    assert type(port) is MahlerFutureCarryPort
    assert port.target == 53
    assert port.first_6305_carry(53) == (16, 4)
