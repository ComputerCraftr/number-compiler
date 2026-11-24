"""Independent decimal and rational checks for bounded Mahler projections."""

from collections.abc import Callable
from random import Random

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.ordered_matrix import Matrix2
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.process_cache import (
    ProcessCache,
    temporary_process_cache,
)
from number_compiler.sequences.antihydra.mahler_continued_fraction import (
    continued_fraction_band,
)


def literal_matrix(digits: list[int]) -> tuple[tuple[int, int], tuple[int, int]]:
    a, b, c, d = 1, 0, 0, 1
    for digit in digits:
        x = digit + 1
        a, b, c, d = a * x + b, a, c * x + d, c
    return ((a, b), (c, d))


def literal_band_matrix(
    exponent: int, cut: int, width: int, rows: int
) -> tuple[tuple[int, int], tuple[int, int]]:
    digits: list[int] = []
    for offset in range(rows):
        value = int.__pow__(5, exponent + offset) // 10 ** (cut + offset - width)
        value %= 10**width
        digits.extend(int(digit) for digit in f"{value:0{width}d}")
    return literal_matrix(digits)


def test_lifted_band_known_source_and_repeat(monkeypatch: pytest.MonkeyPatch) -> None:
    powers: list[int] = []
    original = Matrix2.power

    def checked(matrix: Matrix2, count: int) -> Matrix2:
        powers.append(count)
        return original(matrix, count)

    monkeypatch.setattr(Matrix2, "power", checked)
    ledger = ResourceLedger()
    result = continued_fraction_band(1530, 33, 1, 6, ledger=ledger)
    assert result["lifted_source"] == 106
    assert result["matrix"] == ((26041, 6293), (3596, 869))
    assert powers == [3]
    assert ledger.nodes == 0


def test_live_band_consumes_the_shared_ordered_compiler(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields import ordered_matrix

    original = ordered_matrix.compile_dyadic_ordered_band
    calls: list[tuple[int, int, int, bool]] = []

    def observe(
        quotient: int,
        rows: int,
        width: int,
        reserve: Callable[[int, int, int], None],
        *,
        use_memo: bool,
    ) -> Matrix2:
        assert callable(reserve)
        calls.append((quotient, rows, width, use_memo))
        return original(quotient, rows, width, reserve, use_memo=use_memo)

    monkeypatch.setattr(
        "number_compiler.sequences.antihydra.mahler_continued_fraction.compile_dyadic_ordered_band",
        observe,
    )
    for shared in (True, False):
        ledger = ResourceLedger()
        result = continued_fraction_band(
            1530, 33, 1, 6, ledger=ledger, shared_cache=shared
        )
        assert result["matrix"] == literal_band_matrix(1530, 33, 1, 6)
        assert ledger.nodes == ledger.entries == 0
    assert calls == [(106, 6, 1, True), (106, 6, 1, False)]


def test_bands_match_independent_decimal_powers() -> None:
    rng = Random(98712)
    for _ in range(90):
        exponent = rng.randrange(12, 110)
        rows = rng.randrange(1, 7)
        width = rng.randrange(1, 4)
        source = int.__pow__(5, exponent)
        decimal_width = len(str(source))
        cut = rng.randrange(width, decimal_width + 1)
        last = int.__pow__(5, exponent + rows - 1)
        if len(str(last)) < cut + rows - 1:
            result = continued_fraction_band(
                exponent, cut, width, rows, ledger=ResourceLedger()
            )
            assert result["status"] == "unavailable"
            continue
        expected = literal_band_matrix(exponent, cut, width, rows)
        for shared in (False, True):
            result = continued_fraction_band(
                exponent, cut, width, rows, ledger=ResourceLedger(), shared_cache=shared
            )
            assert result["matrix"] == expected


def test_short_and_multicolumn_bands_use_exact_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(_matrix: Matrix2, _count: int) -> Matrix2:
        raise AssertionError("formal power used on a non-admitted performance band")

    monkeypatch.setattr(Matrix2, "power", forbidden)
    for exponent, cut, width, rows in ((200, 24, 5, 32), (1023, 10, 1, 6)):
        packet = continued_fraction_band(
            exponent, cut, width, rows, ledger=ResourceLedger()
        )
        assert packet["matrix"] == literal_band_matrix(exponent, cut, width, rows)


def test_powered_band_matches_literal_rows_on_larger_sources() -> None:
    rng = Random(1677)
    for _ in range(24):
        exponent = rng.randrange(1024, 1400)
        cut = rng.randrange(1, 300)
        rows = rng.randrange(6, 25)
        expected = literal_matrix(
            [
                int.__pow__(5, exponent + time) // 10 ** (cut + time - 1) % 10
                for time in range(rows)
            ]
        )
        for shared in (False, True):
            packet = continued_fraction_band(
                exponent, cut, 1, rows, ledger=ResourceLedger(), shared_cache=shared
            )
            assert packet["matrix"] == expected


@pytest.mark.parametrize(
    ("exponent", "cut", "width", "rows"),
    [
        (1024, 16, 16, 64),
        (1530, 32, 32, 32),
        (2048, 128, 64, 32),
        (3072, 128, 128, 32),
    ],
)
def test_wide_balanced_rows_preserve_the_physical_digit_order(
    exponent: int, cut: int, width: int, rows: int
) -> None:
    expected = literal_band_matrix(exponent, cut, width, rows)
    for shared in (False, True):
        ledger = ResourceLedger()
        result = continued_fraction_band(
            exponent, cut, width, rows, ledger=ledger, shared_cache=shared
        )
        assert result["matrix"] == expected
        assert ledger.nodes == ledger.entries == 0


def test_rotated_period_uses_its_receiving_phase(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    powers: list[int] = []
    original = Matrix2.power

    def checked(matrix: Matrix2, count: int) -> Matrix2:
        powers.append(count)
        return original(matrix, count)

    monkeypatch.setattr(Matrix2, "power", checked)
    first = continued_fraction_band(1530, 33, 1, 6, ledger=ResourceLedger())
    shifted = continued_fraction_band(1531, 34, 1, 6, ledger=ResourceLedger())
    assert first["matrix"] == literal_band_matrix(1530, 33, 1, 6)
    assert shifted["matrix"] == literal_band_matrix(1531, 34, 1, 6)
    assert first["matrix"] != shifted["matrix"]
    assert powers == [3, 3]


@pytest.mark.parametrize("cap", [5_500, 10_000])
def test_wide_split_preserves_direct_admission(
    cap: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    original = RunArithmeticWorkspace.require_bits
    attempts: list[int] = []

    def checked(workspace: RunArithmeticWorkspace, bits: int) -> None:
        attempts.append(bits)
        original(workspace, bits)

    monkeypatch.setattr(RunArithmeticWorkspace, "require_bits", checked)
    ledger = ResourceLedger(max_nodes=cap)
    cache = ProcessCache()
    with temporary_process_cache(cache):
        if cap == 5_500:
            with pytest.raises(BlockContextBudgetExceeded):
                continued_fraction_band(1530, 32, 16, 64, ledger=ledger)
            assert len(attempts) == 2 and attempts[1] > attempts[0]
        else:
            result = continued_fraction_band(1530, 32, 16, 64, ledger=ledger)
            assert result["matrix"] == literal_band_matrix(1530, 32, 16, 64)
            assert len(attempts) > 3
    cache.reset()
    assert ledger.nodes == ledger.entries == 0


def test_interrupted_balanced_fold_releases_scratch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = Matrix2.multiply
    calls = 0

    def fail(matrix: Matrix2, right: Matrix2) -> Matrix2:
        nonlocal calls
        calls += 1
        if calls == 20:
            raise RuntimeError("interrupted ordered fold")
        return original(matrix, right)

    monkeypatch.setattr(Matrix2, "multiply", fail)
    ledger = ResourceLedger()
    cache = ProcessCache()
    with temporary_process_cache(cache):
        with pytest.raises(RuntimeError, match="interrupted ordered fold"):
            continued_fraction_band(1530, 32, 16, 64, ledger=ledger)
    assert cache.stats().entries == 0
    assert ledger.nodes == ledger.entries == 0


def test_rejects_band_limits_and_insufficient_scratch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.antihydra.mahler_continued_fraction as cf

    assert (
        continued_fraction_band(5, 5, 1, 3, ledger=ResourceLedger())["status"]
        == "unavailable"
    )
    with pytest.raises(ValueError, match="budget"):
        continued_fraction_band(1000, 128, 128, 40, ledger=ResourceLedger())
    ledger = ResourceLedger(max_nodes=1)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("source width exponent was evaluated before reservation")

    monkeypatch.setattr(cf, "pow", forbidden, raising=False)
    with pytest.raises(BlockContextBudgetExceeded):
        continued_fraction_band(4096, 1, 1, 1, ledger=ledger)
    assert ledger.nodes == 0


@pytest.mark.parametrize(
    ("original", "shifted"),
    [
        ((1530, 32, 16, 65), (1531, 33, 16, 64)),
        ((1531, 33, 16, 64), (1530, 32, 16, 65)),
        ((2049, 129, 64, 31), (2048, 128, 64, 32)),
        ((3001, 129, 1, 1024), (3000, 128, 1, 1025)),
    ],
)
def test_issued_band_hits_and_transports_one_row_at_the_same_endpoint(
    original: tuple[int, int, int, int],
    shifted: tuple[int, int, int, int],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.antihydra.mahler_continued_fraction as cf

    expected = continued_fraction_band(
        *shifted, ledger=ResourceLedger(), shared_cache=False
    )
    ledger = ResourceLedger()
    cache = ProcessCache()
    joined = Matrix2.multiply
    joins = 0

    def observe(left: Matrix2, right: Matrix2) -> Matrix2:
        nonlocal joins
        joins += 1
        return joined(left, right)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("an issued band reached cold lift or recursive compilation")

    with temporary_process_cache(cache):
        first = continued_fraction_band(*original, ledger=ledger)
        monkeypatch.setattr(cf, "pow", forbidden, raising=False)
        monkeypatch.setattr(cf, "compile_dyadic_ordered_band", forbidden)
        monkeypatch.setattr(Matrix2, "multiply", observe)
        assert continued_fraction_band(*original, ledger=ledger) == first
        assert joins == 0
        assert continued_fraction_band(*shifted, ledger=ledger) == expected
        assert joins == 1
        assert continued_fraction_band(*shifted, ledger=ledger) == expected
        assert joins == 1
        assert cache.stats().entries == 2
    cache.reset()
    assert ledger.nodes == ledger.entries == 0
    assert cache.ledger.nodes == cache.ledger.entries == 0


@pytest.mark.parametrize("issued", [(1530, 32, 16, 65), (1531, 33, 16, 64)])
@pytest.mark.parametrize(
    "different", [(1531, 32, 16, 65), (1530, 32, 16, 66), (1530, 32, 17, 65)]
)
def test_issued_band_rechecks_source_extent_and_precision(
    issued: tuple[int, int, int, int],
    different: tuple[int, int, int, int],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.antihydra.mahler_continued_fraction as cf

    inspected = 0

    def examine(base: int, exponent: int) -> int:
        nonlocal inspected
        inspected += 1
        value = base**exponent
        assert type(value) is int
        return value

    cache = ProcessCache()
    with temporary_process_cache(cache):
        continued_fraction_band(*issued, ledger=ResourceLedger())
        monkeypatch.setattr(cf, "pow", examine, raising=False)
        answer = continued_fraction_band(*different, ledger=ResourceLedger())
        assert inspected == 1
        assert answer["matrix"] == literal_band_matrix(*different)
    cache.reset()


def test_cached_band_refuses_under_reduced_query_budget() -> None:
    cache = ProcessCache()
    with temporary_process_cache(cache):
        args = (1530, 32, 16, 65)
        continued_fraction_band(*args, ledger=ResourceLedger())
        tight = ResourceLedger(max_nodes=1)
        with pytest.raises(BlockContextBudgetExceeded):
            continued_fraction_band(*args, ledger=tight)
        assert tight.nodes == tight.entries == 0
    cache.reset()


def test_preceding_cut_rejects_foreign_neighbor_and_tight_ledger() -> None:
    from number_compiler.resources.process_cache import CacheRecordIssuerMismatch

    args = (1530, 32, 16, 65)
    exponent, cut, width, rows = args
    cache = ProcessCache()
    with temporary_process_cache(cache):
        partition = (exponent - cut, width, cut + rows - 1)
        with cache.acquire("mahler-cf-diagonal", "1", partition) as lease:
            assert lease.put_issued((cut + 1,), (0, (1, 0, 0, 1)), object())
        with pytest.raises(CacheRecordIssuerMismatch):
            continued_fraction_band(*args, ledger=ResourceLedger())
    cache.reset()
    with temporary_process_cache(cache):
        continued_fraction_band(
            exponent + 1, cut + 1, width, rows - 1, ledger=ResourceLedger()
        )
        tight = ResourceLedger(max_nodes=1)
        with pytest.raises(BlockContextBudgetExceeded):
            continued_fraction_band(*args, ledger=tight)
        assert tight.nodes == tight.entries == 0
    cache.reset()
    assert cache.ledger.nodes == cache.ledger.entries == 0


@pytest.mark.parametrize("stage", ["cancel", "publication"])
def test_preceding_cut_failure_keeps_only_the_issued_successor(
    stage: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    import number_compiler.sequences.antihydra.mahler_continued_fraction as cf
    from number_compiler.resources.process_cache import CacheLease

    args = (1530, 32, 16, 65)
    ledger = ResourceLedger()
    cache = ProcessCache()

    def fail(*_args: object, **_kwargs: object) -> None:
        raise RuntimeError("interrupted preceding-cut construction")

    with temporary_process_cache(cache):
        successor = continued_fraction_band(1531, 33, 16, 64, ledger=ledger)
        assert cache.stats().entries == 1
        with monkeypatch.context() as patched:
            if stage == "cancel":
                patched.setattr(cf, "fold_fixed_decimal_row", fail)
            else:
                patched.setattr(CacheLease, "put_issued", fail)
            with pytest.raises(RuntimeError, match="interrupted preceding-cut"):
                continued_fraction_band(*args, ledger=ledger)
        assert ledger.nodes == ledger.entries == 0
        assert cache.stats().entries == 1
        assert cache.stats().active_leases == 0
        assert continued_fraction_band(1531, 33, 16, 64, ledger=ledger) == successor
    cache.reset()
    assert cache.ledger.nodes == cache.ledger.entries == 0


def test_equal_low_phases_do_not_authorize_different_source_widths() -> None:
    assert pow(5, 40, 32) == pow(5, 48, 32) == 1
    earlier = continued_fraction_band(40, 32, 1, 1, ledger=ResourceLedger())
    later = continued_fraction_band(48, 32, 1, 1, ledger=ResourceLedger())
    assert earlier["status"] == "unavailable"
    assert later["status"] == "available"
    assert later["matrix"] == literal_band_matrix(48, 32, 1, 1)
