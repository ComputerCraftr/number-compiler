"""Reproduce the seven harmonic output conflicts, without claiming closure."""

from collections import Counter, defaultdict
from collections.abc import Hashable, Iterator

import pytest

from devtools.verification import exact_oracle
from devtools.verification.collatz_harmonic_ports import (
    binary_output_response,
    radix64_phi5,
)
from number_compiler.arithmetic.fields.radix import digits_lsd, value_from_lsd_digits
from number_compiler.arithmetic.fields.two_adic import v2_positive
from tests.validation.research.collatz.test_carry_domain_hensel_quotient import (
    crop_source,
    observe_source,
)

PAIRS = (
    (477, 797),
    (481, 801),
    (485, 805),
    (557, 877),
    (1853, 2173),
    (1929, 2249),
    (3209, 3529),
)


@pytest.fixture(autouse=True)
def reference_scope() -> Iterator[None]:
    with exact_oracle():
        yield


def response_key(n: int) -> Hashable:
    digits, _q = crop_source(digits_lsd(n, 64))
    m = value_from_lsd_digits(digits, 64)
    return observe_source(n).key(True), binary_output_response(m)


def pointwise_phi(n: int) -> tuple[int, ...]:
    digits, _q = crop_source(digits_lsd(n, 64))
    return tuple(radix64_phi5(d) for d in digits)


def test_output_response_has_exactly_seven_remaining_conflicts() -> None:
    sources = tuple(n for n in range(1, 4096, 2) if n % 64 != 21)
    fibers: dict[Hashable, list[int]] = defaultdict(list)
    for n in sources:
        fibers[response_key(n)].append(n)
    conflicts = sorted(
        tuple(group)
        for group in fibers.values()
        if len({response_key(observe_source(n).target) for n in group}) > 1
    )
    assert len(sources) == 1984 and len(fibers) == 1977
    assert conflicts == list(PAIRS)
    assert sum(map(len, conflicts)) == 14
    # This is an explicit pointwise Phi5 control, not a reconstruction of the
    # missing long-tail relational decimation implementation.
    strengthened = {(response_key(n), pointwise_phi(n)) for n in sources}
    assert len(strengthened) == len(sources)  # Zero conflicts would be vacuous.


def test_phi5_fibers_and_seven_pair_separation() -> None:
    fibers = Counter(radix64_phi5(d) for d in range(64))
    assert tuple(fibers[i] for i in range(5)) == (28, 16, 4, 7, 9)
    for left, right in PAIRS:
        assert right - left == 5 * 64
        assert response_key(left) == response_key(right)
        assert response_key(observe_source(left).target) != response_key(
            observe_source(right).target
        )
        assert pointwise_phi(left) != pointwise_phi(right)


def test_output_and_phi_preserve_consumed_frame_gauge() -> None:
    for e in range(6):
        m = next(m for m in range(64) if m != 21 and v2_positive(3 * m + 1) == e)
        keys: list[tuple[Hashable, tuple[int, ...]]] = []
        for q in (1, 193, 385):
            n = 64**q * m + (64**q - 1) // 3
            keys.append((response_key(n), pointwise_phi(n)))
        assert len(set(keys)) == 1
