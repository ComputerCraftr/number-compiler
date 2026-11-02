"""Run-level reflection and pairing for decimal digit words."""

from __future__ import annotations

from collections.abc import Sequence


def append_run(runs: list[tuple[int, int]], symbol: int, count: int) -> None:
    """Append a counted symbol, coalescing its adjacent equal run."""
    if count <= 0:
        return
    if runs and runs[-1][0] == symbol:
        previous, length = runs[-1]
        runs[-1] = previous, length + count
    else:
        runs.append((symbol, count))


def pair_normalized_mirror_digit_runs(
    digit_runs: Sequence[tuple[int, int]],
    *,
    width: int,
    half_only: bool,
) -> tuple[tuple[tuple[int, int], ...], bool, int]:
    """Pair one already canonical normalized run tape from both boundaries.

    The caller owns normalization and supplies its authenticated extent. This
    kernel performs no second validation or coalescing scan, so source-issued
    run ports can share the same pointer walk as the validating public entry.
    """
    if not digit_runs or type(width) is not int or width < 1:
        raise ValueError("normalized mirror pairing needs a positive run tape")
    remaining_pairs = (width + 1) // 2 if half_only else width
    left, right = 0, len(digit_runs) - 1
    left_remaining = digit_runs[left][1]
    right_remaining = digit_runs[right][1]
    paired: list[tuple[int, int]] = []
    visits = 0
    while remaining_pairs:
        visits += 1
        amount = min(left_remaining, right_remaining, remaining_pairs)
        append_run(
            paired,
            digit_runs[left][0] + digit_runs[right][0],
            amount,
        )
        remaining_pairs -= amount
        left_remaining -= amount
        right_remaining -= amount
        if left_remaining == 0:
            left += 1
            if left < len(digit_runs):
                left_remaining = digit_runs[left][1]
        if right_remaining == 0:
            right -= 1
            if right >= 0:
                right_remaining = digit_runs[right][1]
    return tuple(paired), bool(width & 1), visits


def pair_mirror_digit_runs(
    digit_runs: Sequence[tuple[int, int]], *, half_only: bool
) -> tuple[tuple[tuple[int, int], ...], bool, int]:
    """Pair each decimal position with its reflected position.

    ``half_only`` returns the first ``ceil(width / 2)`` pair sums, the form
    stored by reverse/add's symmetric half-field. Otherwise it returns all
    pair sums in order. The final integer reports run-boundary iterations for
    accounting without expanding represented digits.
    """
    if not digit_runs:
        raise ValueError("normalization produced an empty decimal word")
    runs: list[tuple[int, int]] = []
    for symbol, count in digit_runs:
        if type(symbol) is not int or not 0 <= symbol <= 9:
            raise ValueError("normalized output digit is outside decimal range")
        if type(count) is not int or count <= 0:
            raise ValueError("normalized output run length must be positive")
        if runs and runs[-1][0] == symbol:
            runs[-1] = (symbol, runs[-1][1] + count)
        else:
            runs.append((symbol, count))

    width = sum(count for _, count in runs)
    return pair_normalized_mirror_digit_runs(
        runs,
        width=width,
        half_only=half_only,
    )
