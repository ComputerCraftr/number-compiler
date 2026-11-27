"""Source-bound branch-chart guards and the physical cylinder consumer."""

from dataclasses import replace
from fractions import Fraction
from random import Random
from struct import Struct

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra import (
    mahler_cf_fractional_path as fractional,
)
from number_compiler.sequences.antihydra import (
    mahler_continued_fraction_cylinder as cf,
)


def _literal_endpoint(value: Fraction, ticks: int) -> Fraction:
    for _ in range(ticks):
        assert 0 <= value <= Fraction(1, 2)
        bit = int(3 * value >= 1)
        value = (3 * value - bit) / 2
    assert 0 <= value <= Fraction(1, 2)
    return value


def _checked_extent(
    action: fractional.FractionalPath, low: Fraction, high: Fraction, ticks: int
) -> int:
    scalar = fractional.FractionalPath()
    scalar.extend(low, high, ticks)
    action.extend(low, high, ticks)
    assert replace(action, chart=None, packed_chart=None) == scalar
    return action.extent


def test_compiled_responses_match_all_physical_intermediate_guards() -> None:
    keys, raw = fractional.branch_chart()
    actions = [(i, k // 2, u) for k, i, u in Struct("=III").iter_unpack(raw)]
    assert len(actions) == 40
    assert keys == tuple(sorted(keys))
    gain = fractional.BRANCH_BLOCK_GAIN
    for key, (innovation, lower, upper) in zip(keys, actions, strict=True):
        assert key == 2 * lower and 2 * lower < upper
        value = Fraction(2 * lower + upper, 4 * gain)
        assert (
            _literal_endpoint(value, fractional.BRANCH_BLOCK_TICKS)
            == (gain * value - innovation) / fractional.BRANCH_BLOCK_MODULUS
        )


def test_chart_and_scalar_have_same_guards_including_boundary_ties() -> None:
    chart = fractional.branch_chart()
    random = Random(812)
    intervals = [(Fraction(0), Fraction(1, 3)), (Fraction(1, 3), Fraction(1, 2))]
    gain = fractional.BRANCH_BLOCK_GAIN
    epsilon = Fraction(1, 4 * gain * 1000)
    for key, _, upper in Struct("=III").iter_unpack(chart[1]):
        lower = key // 2
        low = Fraction(lower, gain)
        high = Fraction(upper, 2 * gain)
        intervals.append((low, high))
        if low > 0:
            intervals.append((low - epsilon, high))
        if high < Fraction(1, 2):
            intervals.append((low, high + epsilon))
    for _ in range(2000):
        denominator = random.randrange(2, 10000)
        lower = random.randrange(denominator // 2 + 1)
        upper = random.randrange(lower, denominator // 2 + 1)
        if lower < upper:
            intervals.append(
                (Fraction(lower, denominator), Fraction(upper, denominator))
            )
    for low, high in intervals:
        _checked_extent(fractional.FractionalPath(chart=chart), low, high, 128)


def test_live_cylinder_skips_scalar_branch_search_and_preserves_packet(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = fractional.max_zero_run
    calls = 0

    def counted(numerator: int, denominator: int, remaining: int) -> int:
        nonlocal calls
        calls += 1
        return original(numerator, denominator, remaining)

    monkeypatch.setattr(fractional, "max_zero_run", counted)
    chart = fractional.packed_branch_chart
    monkeypatch.setattr(fractional, "packed_branch_chart", lambda: b"")
    scalar_ledger = ResourceLedger(max_nodes=10000)
    expected = cf.continued_fraction_cylinder(4096, 20000, ledger=scalar_ledger)
    scalar_calls = calls
    calls = 0
    monkeypatch.setattr(fractional, "packed_branch_chart", chart)
    ledger = ResourceLedger(max_nodes=10000)
    actual = cf.continued_fraction_cylinder(4096, 20000, ledger=ledger)
    assert actual == expected
    assert actual["coefficient_count"] == 540
    assert calls < scalar_calls // 4
    assert ledger.nodes == ledger.entries == 0
    assert scalar_ledger.nodes == scalar_ledger.entries == 0


def test_chart_is_built_once_after_admission_and_small_cap_stays_lazy(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fractional.packed_branch_chart.cache_clear()
    with monkeypatch.context() as scoped:
        original = fractional.packed_branch_chart
        calls = 0

        def counted() -> bytes:
            nonlocal calls
            calls += 1
            return original()

        scoped.setattr(fractional, "packed_branch_chart", counted)
        for budget in (1, 7, 32):
            cf.continued_fraction_cylinder(4096, budget, ledger=ResourceLedger())
        assert calls == 0
        cf.continued_fraction_cylinder(4096, 20000, ledger=ResourceLedger())
        assert calls > 1
        assert original.cache_info().misses == 1
        cf.continued_fraction_cylinder(4096, 20000, ledger=ResourceLedger())
        assert original.cache_info().misses == 1


def test_optional_chart_capacity_refusal_restores_scalar_path(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = RunArithmeticWorkspace.require_bits
    calls = 0

    def refuse_chart(self: RunArithmeticWorkspace, bits: int) -> None:
        nonlocal calls
        if self.prefix == "mahler-cf-branch-chart":
            calls += 1
            raise BlockContextBudgetExceeded("test refusal before chart construction")
        original(self, bits)

    reference_ledger = ResourceLedger(max_nodes=10000)
    expected = cf.continued_fraction_cylinder(4096, 20000, ledger=reference_ledger)
    monkeypatch.setattr(RunArithmeticWorkspace, "require_bits", refuse_chart)
    ledger = ResourceLedger(max_nodes=10000)
    assert cf.continued_fraction_cylinder(4096, 20000, ledger=ledger) == expected
    assert calls == 2
    assert ledger.nodes == ledger.entries == 0


def test_public_cli_reports_exact_first_exclusion(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    import json

    from number_compiler.api.cli import main

    args = [
        "antihydra",
        "--nth",
        "0",
        "--no-value",
        "--info",
        "arithmetic.continued-fraction",
        "--safety-horizon",
        "4096",
        "--continued-fraction-max-coefficients",
        "539",
        "--format",
        "json",
    ]
    original = fractional.packed_branch_chart
    monkeypatch.setattr(fractional, "packed_branch_chart", lambda: b"")
    scalar_status = main(args)
    scalar_packet = json.loads(capsys.readouterr().out)
    monkeypatch.setattr(fractional, "packed_branch_chart", original)
    assert main(args) == scalar_status
    assert json.loads(capsys.readouterr().out) == scalar_packet
    assert scalar_status == 3
    assert scalar_packet["info"]["arithmetic.continued-fraction"]["status"] == "unknown"


def test_chart_interruption_releases_all_query_reservations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def interrupted() -> bytes:
        raise KeyboardInterrupt

    monkeypatch.setattr(fractional, "packed_branch_chart", interrupted)
    ledger = ResourceLedger(max_nodes=10000)
    with pytest.raises(KeyboardInterrupt):
        cf.continued_fraction_cylinder(4096, 20000, ledger=ledger)
    assert ledger.nodes == ledger.entries == 0


def test_packed_chart_matches_all_physical_words_and_ordered_boundaries() -> None:
    record = Struct("=III")
    raw = fractional.packed_branch_chart()
    assert len(raw) == 12 * (40 + 1018)
    rows = list(record.iter_unpack(raw))
    assert raw[: 40 * record.size] == fractional.branch_chart()[1]
    wide = rows[40:]
    gain = 3**16
    assert wide[0][0] == 0 and wide[-1][2] == gain
    assert all(a[2] == b[0] for a, b in zip(wide[:-1], wide[1:], strict=True))
    for key, innovation, upper in wide:
        value = Fraction(key + upper, 4 * gain)
        assert _literal_endpoint(value, 16) == (gain * value - innovation) / 2**16
        low = Fraction(key, 2 * gain)
        high = Fraction(upper, 2 * gain)
        packed = fractional.FractionalPath(packed_chart=raw)
        assert _checked_extent(packed, low, high, 16) == 16


def test_packed_chart_rejects_intervals_crossing_each_wide_boundary() -> None:
    raw = fractional.packed_branch_chart()
    rows = list(Struct("=III").iter_unpack(raw))[40:]
    gain = 3**16
    for key, _, _ in rows[1:]:
        low, high = Fraction(key - 1, 2 * gain), Fraction(key + 1, 2 * gain)
        packed = fractional.FractionalPath(packed_chart=raw)
        assert _checked_extent(packed, low, high, 16) < 16


def test_packed_refusal_uses_short_chart_before_scalar(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = RunArithmeticWorkspace.require_bits
    wide_refusals = 0
    short_admissions = 0

    def refuse_wide(self: RunArithmeticWorkspace, bits: int) -> None:
        nonlocal wide_refusals, short_admissions
        if self.prefix == "mahler-cf-branch-chart":
            if bits == fractional.PACKED_CHART_SCRATCH_BITS:
                wide_refusals += 1
                raise BlockContextBudgetExceeded("wide action cannot fit")
            short_admissions += 1
        original(self, bits)

    expected = cf.continued_fraction_cylinder(4096, 20000, ledger=ResourceLedger())
    monkeypatch.setattr(RunArithmeticWorkspace, "require_bits", refuse_wide)
    ledger = ResourceLedger(max_nodes=10000)
    assert cf.continued_fraction_cylinder(4096, 20000, ledger=ledger) == expected
    assert wide_refusals == 1 and short_admissions > 0
    assert ledger.nodes == ledger.entries == 0
