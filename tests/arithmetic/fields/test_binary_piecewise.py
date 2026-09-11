from collections.abc import Callable

from number_compiler.arithmetic.fields.binary_piecewise import (
    BinaryBranchDecision,
    BinaryPiecewiseHandler,
)


def test_binary_piecewise_dispatch_executes_exactly_one_selected_branch() -> None:
    handler = BinaryPiecewiseHandler("test")
    calls: list[str] = []

    def branch(name: str) -> Callable[[BinaryBranchDecision], tuple[str, str]]:
        def run(decision: BinaryBranchDecision) -> tuple[str, str]:
            calls.append(name)
            return name, decision.kind

        return run

    for decision, expected in (
        (BinaryBranchDecision.zero("z"), "zero"),
        (BinaryBranchDecision.one("o"), "one"),
        (BinaryBranchDecision.split("s", 7), "split"),
        (BinaryBranchDecision.unknown("u"), "unknown"),
    ):
        calls.clear()
        out = handler.dispatch(
            decision,
            zero_branch=branch("zero"),
            one_branch=branch("one"),
            split_branch=branch("split"),
            unknown_branch=branch("unknown"),
        )
        assert out == (expected, decision.kind)
        assert calls == [expected]


def test_binary_decision_rejects_fake_split_packets_and_branch_payloads() -> None:
    try:
        BinaryBranchDecision("SPLIT", "bad", 1)
    except ValueError:
        pass
    else:
        raise AssertionError("split gcd=1 must be rejected")

    try:
        BinaryBranchDecision("ZERO", "bad", 7)
    except ValueError:
        pass
    else:
        raise AssertionError("ordinary branch must not carry a gcd packet")
