"""Physical and local checks for the period-three mixed-EQ carry action."""

from __future__ import annotations

import json
from collections.abc import Callable
from itertools import product
from typing import cast

import pytest

from number_compiler.api import cli
from number_compiler.sequences.reverse_add import mixed_periodic_bank
from number_compiler.sequences.reverse_add.mixed_periodic_bank import MixedPeriodicCore
from tests.support.private_attributes import private_test_attribute
from tests.support.reverse_add_source_data import reverse_add_step
from tests.support.reverse_add_sources import periodic_reverse_add_source


def _word(index: int, digit: int, high: int) -> tuple[int, int, int]:
    result = [0, 0, 0]
    x = digit + 10 * high
    result[index] = 9
    result[(index - 1) % 3] = x
    result[(index + 1) % 3] = 18 - x
    return result[0], result[1], result[2]


def _literal_ports(word: tuple[int, ...]) -> tuple[tuple[int, int], ...]:
    result: list[tuple[int, int]] = []
    for i in range(len(word)):
        inlets: list[int] = []
        for direction in (-1, 1):
            for offset in range(1, len(word) + 1):
                neighbour = word[(i + direction * offset) % len(word)]
                if neighbour != 9:
                    inlets.append(int(neighbour > 9))
                    break
        result.append((inlets[0], inlets[1]))
    return tuple(result)


def test_all_54_mixed_eq_phases_and_both_physical_choices() -> None:
    for index, digit, high in product(range(3), range(9), range(2)):
        word = _word(index, digit, high)
        source = MixedPeriodicCore(word)
        ports = _literal_ports(word)
        assert source.ingresses() == ports
        for birth in (0, 1):
            target, frame = source.advance(birth)
            if birth:
                expected = _word((index - 1) % 3, 8 - digit, high)
            else:
                x = 2 * (digit + 1 - high)
                expected = _word(index, x % 10, x // 10)
            assert target.coefficients == expected
            assert frame.incoming == ports
            expected_low = tuple(
                (s + p[0]) % 10 for s, p in zip(word, ports, strict=True)
            )
            expected_high = tuple(
                ((word[(i - 1) % 3] + int(word[i] + ports[i][1] >= 10)) % 10)
                if birth
                else (word[i] + ports[i][1]) % 10
                for i in range(3)
            )
            assert frame.digits_low == expected_low
            assert frame.digits_reflected == expected_high
            assert expected == tuple(
                a + b for a, b in zip(expected_low, expected_high, strict=True)
            )


def test_mixed_eq_spatial_cli_consumes_the_source_guard(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.sequences.reverse_add import q19_border_control

    seed = periodic_reverse_add_source((5, 9, 13), seed=9)
    current = seed
    physical_births: list[int] = []
    after_three = 0
    for tick in range(6):
        following = reverse_add_step(current)
        physical_births.append(int(len(str(following)) > len(str(current))))
        current = following
        if tick == 2:
            after_three = current
    assert physical_births[:3] == [1, 0, 1]
    assert physical_births != [1, 0, 1, 1, 0, 1]
    original = cast(
        Callable[[tuple[int, int], int], tuple[int, int, int]],
        private_test_attribute(mixed_periodic_bank, "_mixed_eq_target"),
    )
    seen: list[tuple[int, int, int]] = []

    def observe(phase: tuple[int, int], growth: int) -> tuple[int, int, int]:
        result = original(phase, growth)
        seen.append(result)
        return result

    monkeypatch.setattr(mixed_periodic_bank, "_mixed_eq_target", observe)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("source-certified 101 opened the border frontier")

    monkeypatch.setattr(q19_border_control, "_certify_reserved", forbidden)
    status = cli.main(
        [
            "reverse-add",
            "--seed",
            str(seed),
            "--nth",
            "3",
            "--no-value",
            "--info",
            "spatial.bank-morphism",
            "--spatial-pair-bank-position",
            "200",
            "--spatial-bank-morphism-count",
            "32",
            "--temporal-grammar-period",
            "3",
            "--format",
            "json",
        ]
    )
    out = capsys.readouterr()
    assert status == 0, out.err
    packet = json.loads(out.out)["info"]["spatial.bank-morphism"]
    assert packet["status"] == "available" and packet["control_certified"]
    assert seen
    digits = str(after_three)
    pairs = [int(digits[-1 - i]) + int(digits[i]) for i in range(200, 216)]
    assert packet["first_pair_coefficients"] == pairs


def test_noncomplementary_period_retains_exact_carries() -> None:
    for word in ((9, 4, 9), (9, 5, 12), (4, 9, 13), (4, 9, 9)):
        assert MixedPeriodicCore(word).ingresses() == _literal_ports(word)


def test_shared_periodic_cone_inlets_preserve_all_eq_refusal() -> None:
    from number_compiler.sequences.reverse_add import q19_periodic_cone
    from number_compiler.sequences.reverse_add.q19_uniform_cone import (
        UniformConeNotAuthorized,
    )

    ingress = cast(
        Callable[[tuple[int, ...]], tuple[tuple[int, int], ...]],
        private_test_attribute(q19_periodic_cone, "_periodic_ingresses"),
    )
    for word in ((5, 9, 13), (0, 11), (4, 9, 9, 14)):
        assert ingress(word) == _literal_ports(word)
    for bad_word in ((), (9,), (9, 9, 9)):
        with pytest.raises(UniformConeNotAuthorized, match="all-EQ core"):
            ingress(bad_word)


@pytest.mark.parametrize("compact_first", (False, True))
def test_cli_growth_receipt_does_not_weaken_python_border(
    compact_first: bool,
) -> None:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    seed = periodic_reverse_add_source((5, 9, 13), seed=9)
    term = ReverseAddPoweredTerm(seed, 3)
    workspace = term.source_workspace()
    try:
        results = {
            compact: term.temporal_spatial_bank_morphism(
                200, 32, period=3, _growth_only=compact
            )
            for compact in ((True, False) if compact_first else (False, True))
        }
        wide = results[False].action.border_certificate
        narrow = results[True].action.border_certificate
        assert wide is not None and narrow is not None
        assert wide.window_digits == 6 and narrow.window_digits == 1
        assert wide.growth_word == narrow.growth_word == (1, 0, 1)
        wide_constraints = wide.inward_temporal_constraints(max_modular_digits=0)
        narrow_constraints = narrow.inward_temporal_constraints(max_modular_digits=0)
        assert wide_constraints.digit_domain(0, 1) == (int(str(seed)[1]),)
        assert narrow_constraints.digit_domain(0, 1) == tuple(range(10))
        assert results[False].output_word("coefficient") == results[True].output_word(
            "coefficient"
        )
    finally:
        workspace.dispose()


def test_equal_mod_five_inputs_keep_the_next_exact_reset_separate() -> None:
    # The first quiet response has equal residues but opposite reset carries.
    source = MixedPeriodicCore((14, 4, 14, 9, 14))
    target, frame = source.advance(0)
    assert frame.incoming[1] == frame.incoming[3] == (1, 1)
    assert target.coefficients[1] == 10
    assert target.coefficients[3] == 0
    assert target.coefficients[1] % 5 == target.coefficients[3] % 5
    assert target.ingresses()[2][0] != target.ingresses()[4][0]


def test_quiet_initial_phase_is_not_replaced_by_101() -> None:
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(11461, 10), base=10)
    try:
        border = owner.certify_border_growth(owner.initial, steps=1, window_digits=1)
        assert border.growth_word == (0,)
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0
