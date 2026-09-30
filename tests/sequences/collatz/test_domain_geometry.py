"""Exact bounded Collatz carry ports derived from shared domain geometry."""

from __future__ import annotations

import pytest

from devtools.verification.collatz_domain_geometry import CollatzDomainGeometry
from devtools.verification.threshold_expressions import ThresholdExpressions
from number_compiler.arithmetic.automata import program_word as words
from number_compiler.arithmetic.carry.collatz_output_quotient import radix64_domain


def _wire(carry: int) -> tuple[int, int]:
    return int(carry >= 1), int(carry == 2)


def test_all_radix64_digits_and_prefix_ports_match_raw_carry() -> None:
    for digit in range(64):
        expression = ThresholdExpressions()
        adapter = CollatzDomainGeometry(expression)
        one = adapter.from_digits((digit,))
        two = adapter.from_digits((digit, digit))
        assert one.width == 1
        assert two.width == 2
        assert radix64_domain(digit) in range(5)
        for incoming in range(3):
            assert adapter.evaluate_carry(one, 0, incoming) == incoming
            assert (
                adapter.evaluate_carry(one, 1, incoming) == (3 * digit + incoming) // 64
            )
            carry = incoming
            for stop in range(3):
                assert adapter.evaluate_carry(two, stop, incoming) == carry
                if stop < 2:
                    carry = (3 * digit + carry) // 64


def test_five_way_domain_expression_derives_both_wire_geometries() -> None:
    expressions = ThresholdExpressions()
    adapter = CollatzDomainGeometry(expressions)
    domain = expressions.variable(5, 0)
    geometry = adapter.from_domains((domain,))
    for action, outputs in enumerate(
        ((0, 0, 0), (0, 1, 1), (1, 1, 1), (1, 1, 2), (2, 2, 2))
    ):
        for incoming in range(3):
            ports = adapter.carry_at(geometry, 1, incoming)
            assert adapter.evaluate(ports, (action,)) == _wire(outputs[incoming])
    assert any(
        node.kind == "variable" and node.data == (0,) for node in expressions.nodes
    )


def test_composed_prefix_actions_use_native_carry_monoid() -> None:
    expressions = ThresholdExpressions()
    adapter = CollatzDomainGeometry(expressions)
    geometry = adapter.from_action_indices((0, 1, 3, 4))
    left = adapter.from_action_indices((0, 1))
    right = adapter.from_action_indices((3, 4))
    prefix = adapter.prefix_action(right, 2)
    direct = adapter.prefix_action(left, 2)
    combined = adapter.compose_actions(
        prefix,
        direct,
    )
    for incoming in range(3):
        # A prefix action is a sort-three function on the incoming carry;
        # composing two such actions is the same native monoid operation as
        # querying the complete geometry at its right boundary.
        assert adapter.evaluate(
            adapter.apply_action(combined, incoming), ()
        ) == adapter.evaluate(adapter.carry_at(geometry, 4, incoming), ())
    assert direct.lower != combined.lower or direct.upper != combined.upper


def test_counted_uniform_geometry_never_materializes_cells(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    expressions = ThresholdExpressions()
    adapter = CollatzDomainGeometry(expressions)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("uniform carry geometry materialized its cells")

    monkeypatch.setattr(adapter, "from_domains", forbidden)
    monkeypatch.setattr(adapter.geometry, "coordinates", forbidden)
    monkeypatch.setattr(words, "iter_runs", forbidden)
    huge = adapter.from_uniform_action(4, 10**100)
    for position in (0, 1, 10**50, 10**100):
        for incoming in range(3):
            expected = incoming if position == 0 else 2
            assert adapter.evaluate_carry(huge, position, incoming) == expected
    assert huge.lower.word.run_count == huge.upper.word.run_count == 1
    assert huge.width == 10**100


def test_same_current_domain_geometry_does_not_claim_next_value_quotient() -> None:
    first = CollatzDomainGeometry(ThresholdExpressions())
    second = CollatzDomainGeometry(ThresholdExpressions())
    left = first.from_digits((4,))
    same_domain = first.from_digits((8,))
    assert left == same_domain
    assert first.evaluate_carry(left, 1, 0) == 0
    # The carry geometry is intentionally only the control quotient.  The
    # exact radix-64 output value distinguishes the next domain immediately.
    assert radix64_domain(4) == radix64_domain(8)
    assert radix64_domain(3 * 4 + 1) != radix64_domain(3 * 8 + 1)
    with pytest.raises(ValueError, match="foreign"):
        second.prefix_action(left, 1)
