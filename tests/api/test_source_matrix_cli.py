"""Independent endpoint fixtures for the unified family matrix consumers."""

import json

import pytest

from number_compiler.api.cli import main


def test_reverse_source_matrix_uses_emitted_growth_guard(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.sequences.reverse_add.q19_conditional_stencil import (
        GuardedPairStencil,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    calls: list[int] = []
    original = GuardedPairStencil.next_carry_domain_at

    def tracked(
        self: GuardedPairStencil, owner: ReversePairQ19OutputOwner, coordinate: int
    ) -> int | None:
        calls.append(coordinate)
        return original(self, owner, coordinate)

    monkeypatch.setattr(GuardedPairStencil, "next_carry_domain_at", tracked)
    assert (
        main(
            [
                "reverse-add",
                "--seed",
                "9999",
                "--nth",
                "2",
                "--no-value",
                "--info",
                "temporal.matrix",
                "--temporal-matrix-kind",
                "source-transfer",
                "--temporal-matrix-steps",
                "1",
                "--temporal-matrix-pair-depth",
                "1",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert "temporal.matrix" in packet["info"]
    assert calls


@pytest.mark.parametrize(
    ("seed", "index", "source", "endpoint"), [(7, 0, 7, 11), (11, 2, 17, 26)]
)
def test_collatz_matrix_starts_at_main_query_endpoint(
    seed: int,
    index: int,
    source: int,
    endpoint: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    if seed == 7:
        from number_compiler.api.cli_context import QueryContext

        def reject_unused_parity_owner(*_args: object, **_kwargs: object) -> object:
            raise AssertionError(
                "complete single-macro summary allocated a parity action owner"
            )

        monkeypatch.setattr(
            QueryContext,
            "collatz_parity_actions",
            reject_unused_parity_owner,
        )
    assert (
        main(
            [
                "collatz",
                "--seed",
                str(seed),
                "--nth",
                str(index),
                "--info",
                "temporal.matrix",
                "--temporal-matrix-steps",
                "2",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    matrix = packet["info"]["temporal.matrix"]
    assert int(packet["value"]) == source
    assert matrix["status"] == "available"
    assert (matrix["source"], matrix["endpoint"]) == (source, endpoint)
    assert matrix["physical_ticks"] == 2
    assert matrix["normalized_steps"] == 1
    assert matrix["execution_authority"] is False


def test_fermat_source_matrix_keeps_ordered_carry_without_primality_claim(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "fermat",
                "--nth",
                "2",
                "--info",
                "temporal.matrix.trace",
                "--temporal-matrix-steps",
                "3",
                "--temporal-matrix-digit-position",
                "1",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    matrix = packet["info"]["temporal.matrix.trace"]
    assert packet["value"] == "17"
    assert matrix["source_level"] == 3
    assert matrix["trace"]["digits"] == [6, 8, 4, 4]
    assert matrix["trace"]["carry_in"] == [0, 0, 2]
    assert matrix["trace"]["carry_out"] == [1, 2, 1]
    assert matrix["primality_authority"] is False
    assert matrix["complete_signed_fold_certified"] is False


def test_collatz_matrix_trace_uses_admitted_parity_prefix(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "collatz",
                "--seed",
                "7",
                "--nth",
                "0",
                "--no-value",
                "--info",
                "temporal.matrix.trace",
                "--temporal-matrix-steps",
                "2",
                "--format",
                "json",
            ]
        )
        == 0
    )
    matrix = json.loads(capsys.readouterr().out)["info"]["temporal.matrix.trace"]
    assert matrix["trace"]["parity"] == [1]
    assert matrix["trace"]["physical_ticks"] == {"value": 2, "unit": "physical-ticks"}
    assert matrix["trace"]["endpoint_mod5"] == 11 % 5
    assert matrix["clocks"]["odd_events"]["value"] == 1


def test_collatz_cli_matrix_joins_adjacent_macros_without_refolding(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.sequences.collatz import boundary_macros
    from number_compiler.sequences.collatz.guarded_parity_binding import (
        ParityTapeActionBinding,
    )

    def reject_full_fold(_cls: type[ParityTapeActionBinding], *_args: object) -> None:
        raise AssertionError("production matrix join refolded a retained parity tape")

    monkeypatch.setattr(
        ParityTapeActionBinding,
        "issue_from_fold",
        classmethod(reject_full_fold),
    )

    def reject_uncached_template(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("production matrix bypassed the ledgered template memo")

    monkeypatch.setattr(
        boundary_macros, "build_boundary_action_template", reject_uncached_template
    )
    assert (
        main(
            [
                "collatz",
                "--seed",
                "44",
                "--nth",
                "0",
                "--info",
                "temporal.matrix",
                "--temporal-matrix-steps",
                "6",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    matrix = packet["info"]["temporal.matrix"]
    assert matrix["status"] == "available"
    assert (matrix["source"], matrix["endpoint"]) == (44, 26)
    assert matrix["physical_ticks"] == 6
    assert matrix["normalized_steps"] == 4
    assert matrix["odd_events"] == 2


def test_collatz_cli_matrix_refuses_unsupported_guarded_tail(
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    # The source has an exact four-tick endpoint, but after 7→11 there is no
    # admitted named macro at 11. Endpoint equality cannot supply that guard.
    assert PoweredCollatzTerm(7, 4).materialize(max_bits=16) == 17
    assert (
        main(
            [
                "collatz",
                "--seed",
                "7",
                "--nth",
                "0",
                "--no-value",
                "--info",
                "temporal.matrix",
                "--temporal-matrix-steps",
                "4",
                "--format",
                "json",
            ]
        )
        == 3
    )
    matrix = json.loads(capsys.readouterr().out)["info"]["temporal.matrix"]
    assert matrix["status"] == "unavailable"
    assert matrix["reason"] == (
        "no admitted border macro covers the requested endpoint horizon"
    )
