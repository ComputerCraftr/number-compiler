"""The source-issued repeat power preserves the physical and safety action."""

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.dyadic_return_actions import append_source
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnSourceRecord,
)
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm
from tests.support.mahler_harmonic_reference import literal_antihydra_summary
from tests.support.source_image_assertions import dyadic_image_summary


def repeated_source(low: int, bits: int) -> int:
    current = low
    for _ in range(8):
        current = 3 * current // 2
    correction = 3**8 * low - (current << 8)
    return correction * pow(3**8 - 2**8, -1, 1 << bits) % (1 << bits)


@pytest.mark.parametrize("low", (2, 39, 74, 127, 198, 255))
@pytest.mark.parametrize("width", (24, 64, 128, 129))
def test_source_admitted_repeat_matches_endpoint_and_safety(
    low: int, width: int
) -> None:
    source = repeated_source(low, 128)
    term = AntihydraArithmeticTerm(0)
    workspace = term.arithmetic_image()
    record = DyadicReturnSourceRecord(
        source % (1 << width), width, source >> width, None, None, None, 0, True
    )
    source_id = append_source(workspace, record)
    image = workspace.scheduler.source_image(
        workspace, source_id, workspace.action_for_extent(width)
    )
    view = workspace.scheduler.source_image_core().view(image)
    summary = dyadic_image_summary(workspace, view)
    expected_h, delta, minimum, odd_steps, failure = literal_antihydra_summary(
        source, width
    )
    transfer = summary.transfer
    assert (transfer.upper * source + transfer.offset) // transfer.lower == expected_h
    assert (summary.delta, summary.minimum, summary.odd_steps) == (
        delta,
        minimum,
        odd_steps,
    )
    assert workspace.first_failure(view) == failure


def test_repeat_consumes_one_action_and_releases_failed_reservation() -> None:
    source = repeated_source(39, 128)
    term = AntihydraArithmeticTerm(0)
    workspace = term.arithmetic_image()
    scratch = RunArithmeticWorkspace.for_ledger(term.ledger, workspace.counter_prefix)
    with scratch.scope():
        values = tuple(workspace.punctured_steps(source, 128, scratch))
    assert len(values) == 1
    expected_h, delta, minimum, odd_steps, _ = literal_antihydra_summary(source, 128)
    assert values[0] == (128, delta, minimum, odd_steps, expected_h - 1)

    before = term.ledger.entries, term.ledger.nodes
    # The second limit admits the bounded prefix and full-width difference,
    # then refuses the larger geometric coefficient.
    prefix_capacity = 16 + (8 * (source.bit_length() + 40) + 63) // 64
    for capacity in (1, prefix_capacity):
        term.ledger.max_nodes = before[1] + capacity
        with pytest.raises(BlockContextBudgetExceeded), scratch.scope():
            tuple(workspace.punctured_steps(source, 128, scratch))
        assert (term.ledger.entries, term.ledger.nodes) == before
        assert scratch.nodes == 0 and not scratch.active


def test_two_copy_cylinder_is_not_admitted_as_three() -> None:
    source = repeated_source(39, 16)
    first = source
    for _ in range(8):
        first = 3 * first // 2
    if (first - source) % (1 << 16) == 0:
        source += 1 << 16
    first = source
    for _ in range(8):
        first = 3 * first // 2
    assert (first - source) % (1 << 8) == 0
    assert (first - source) % (1 << 16) != 0

    term = AntihydraArithmeticTerm(0)
    workspace = term.arithmetic_image()
    scratch = RunArithmeticWorkspace.for_ledger(term.ledger, workspace.counter_prefix)
    with scratch.scope():
        parts = tuple(workspace.punctured_steps(source, 24, scratch))
    assert len(parts) > 1
    expected_h, _, _, _, _ = literal_antihydra_summary(source, 24)
    assert parts[-1][-1] == expected_h - 1


@pytest.mark.parametrize("source", (7058, 7058 + 2**12, 7058 + 2**16, 1))
@pytest.mark.parametrize("width", (11, 12, 13, 15, 16, 17, 24, 31, 128))
def test_four_step_source_phase_matches_ordered_literal_action(
    source: int, width: int
) -> None:
    term = AntihydraArithmeticTerm(0)
    workspace = term.arithmetic_image()
    scratch = RunArithmeticWorkspace.for_ledger(term.ledger, workspace.counter_prefix)
    with scratch.scope():
        parts = tuple(workspace.punctured_steps(source, width, scratch))
    result, balance, minimum, odd = source, 0, 0, 0
    for length, delta, part_minimum, part_odd, endpoint in parts:
        part_result, expected_delta, expected_minimum, expected_odd, _ = (
            literal_antihydra_summary(result, length)
        )
        assert (endpoint, delta, part_minimum, part_odd) == (
            part_result - 1,
            expected_delta,
            expected_minimum,
            expected_odd,
        )
        minimum = min(minimum, balance + part_minimum)
        balance += delta
        odd += part_odd
        result = endpoint + 1
    expected, expected_delta, expected_minimum, expected_odd, _ = (
        literal_antihydra_summary(source, width)
    )
    assert (result, balance, minimum, odd) == (
        expected,
        expected_delta,
        expected_minimum,
        expected_odd,
    )
    if source == 7058 and width >= 12:
        assert parts[0][0] >= 12


def test_all_four_step_phases_preserve_original_source_and_safety() -> None:
    term = AntihydraArithmeticTerm(0)
    workspace = term.arithmetic_image()
    scratch = RunArithmeticWorkspace.for_ledger(term.ledger, workspace.counter_prefix)
    modulus = 1 << 16
    inverse = pow(3**4 - 2**4, -1, modulus)
    for phase_bits in range(16):
        correction = 0
        word: list[int] = []
        for position in range(4):
            parity = (phase_bits >> position) & 1
            word.append(parity)
            correction = 3 * correction + (1 << position) * parity
        source = correction * inverse % modulus or modulus
        prefix_correction = 0
        endpoint = source
        for cut in range(1, 4):
            parity = word[cut - 1]
            prefix_correction = 3 * prefix_correction + (1 << (cut - 1)) * parity
            endpoint = 3 * endpoint // 2
            rotated = word[cut:] + word[:cut]
            rotated_correction = 0
            for position, bit in enumerate(rotated):
                rotated_correction = 3 * rotated_correction + (1 << position) * bit
            endpoint_guard = rotated_correction * pow(3, -4, 16) % 16
            guard_modulus = 1 << (4 + cut)
            source_guard = (
                (prefix_correction + (1 << cut) * endpoint_guard)
                * pow(3, -cut, guard_modulus)
                % guard_modulus
            )
            assert endpoint % 16 == endpoint_guard
            assert source % guard_modulus == source_guard
        with scratch.scope():
            parts = tuple(workspace.punctured_steps(source, 28, scratch))
        value = source
        for length, delta, minimum, odd_steps, endpoint in parts:
            expected, expected_delta, expected_minimum, expected_odd, _ = (
                literal_antihydra_summary(value, length)
            )
            assert (endpoint, delta, minimum, odd_steps) == (
                expected - 1,
                expected_delta,
                expected_minimum,
                expected_odd,
            )
            value = endpoint + 1
        assert value == literal_antihydra_summary(source, 28)[0]
