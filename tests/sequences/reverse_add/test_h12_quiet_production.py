"""H12's authenticated zero and carry-free actions reach physical publication."""

from itertools import product
from random import Random
from typing import Never

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as keys
from number_compiler.sequences.reverse_add.q19_broadword_publisher import (
    PackedQ19,
)
from number_compiler.sequences.reverse_add.q19_carry_window import physical_carry_image
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner


def test_h12_groups_carry_free_prefix(monkeypatch: pytest.MonkeyPatch) -> None:
    source = PackedQ19.from_digits((0,) * 128 + (1,))
    expected = source
    for _ in range(12):
        expected, _ = expected.advance(emit_digits=True)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("quiet prefix opened a physical transition")

    with monkeypatch.context() as patch:
        patch.setattr(PackedQ19, "_advance_with_masks", forbidden)
        quiet = source.advance_repeated(4)
    literal = source
    for _ in range(4):
        literal, _ = literal.advance(emit_digits=True)
    assert quiet == literal
    assert physical_carry_image(source) == expected


def test_arbitrary_quiet_prefix_does_not_change_endpoint() -> None:
    rng = Random(95)
    for _ in range(300):
        digits = tuple(rng.randrange(10) for _ in range(rng.randrange(0, 30))) + (
            rng.randrange(1, 10),
        )
        initial = PackedQ19.from_digits(digits)
        n = rng.randrange(1, 30)
        state = initial
        for _ in range(n):
            state, _ = state.advance(emit_digits=True)
        assert initial.advance_repeated(n) == state


def test_zero_owner_publishes_huge_horizon_without_physical_steps(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("zero fixed point opened a physical continuation")

    monkeypatch.setattr(PackedQ19, "advance_repeated", forbidden)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, (0,), base=10)
    try:
        result = owner.publish_carry_window_continuation(10**12)
        assert tuple(owner.iter_digits(result)) == (0,)
        assert ledger.counters.get(keys.REVERSE_Q19_BROADWORD_SEMANTIC_STEPS, 0) == 0
        assert ledger.peak_nodes < 512
    finally:
        owner.dispose()
    assert ledger.nodes == ledger.entries == 0


def test_pair_four_keeps_bilinear_successor_carry() -> None:
    for a, b in product((False, True), repeat=2):
        pairs = (1, 10 if a else 1, 4, 10 if b else 1)
        source = PackedQ19(
            sum(value << (6 * i) for i, value in enumerate(pairs)), 4, None
        )
        target, _, ports = source.advance_with_ports()
        assert bool((ports.carry_in_lsd >> 2) & 1) is a
        assert bool((ports.carry_in_lsd >> 5) & 1) is b
        assert (target.pairs >> 12) & 63 == 8 + int(a) + int(b)
        _, _, next_ports = target.advance_with_ports()
        assert bool((next_ports.carry_in_lsd >> 3) & 1) is (a and b)

    # With mixed inlets the successor is 9, which propagates a true inlet.
    # The false-inlet bilinear observation alone cannot authorize this row.
    pairs = (1, 8, 4, 10)
    source = PackedQ19(sum(value << (6 * i) for i, value in enumerate(pairs)), 4, None)
    target, _, ports = source.advance_with_ports()
    assert not ((ports.carry_in_lsd >> 2) & 1)
    assert (ports.carry_in_lsd >> 5) & 1
    assert (target.pairs >> 12) & 63 == 9
    _, _, next_ports = target.advance_with_ports()
    assert (next_ports.carry_in_lsd >> 3) & 1
