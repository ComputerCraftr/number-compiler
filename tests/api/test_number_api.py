from __future__ import annotations

import json
from typing import Never

import pytest

import number_compiler.sequences.reverse_add.digits as reverse_digits
from number_compiler.api.cli import main as cli_main
from number_compiler.api.number_api import NumberCompiler
from tests.support.power_assertions import assert_collatz_radices


def test_nth_terms_are_exact_across_all_canonical_families() -> None:
    c = NumberCompiler()
    assert c.nth("196", 0) == 196
    assert c.nth("196", 5) == 52514
    assert c.nth("reverse-add", 5, seed=196, base=10) == 52514
    assert_collatz_radices(c)
    assert c.nth("prime", 10, start=2) == 31
    assert c.nth("prime", 0, start=100) == 101
    assert c.nth("prime", 3, start=100) == 109
    assert c.nth("fermat", 0) == 3
    assert c.nth("fermat", 4) == 65537
    assert c.nth("mersenne", 13) == 8191


def test_projection_phase_does_not_materialize_formula_terms(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("materialization entered projection phase")

    monkeypatch.setattr(
        "number_compiler.hashlife.execution.evaluator.materialize_values", forbidden
    )
    c = NumberCompiler()
    r = c.project_nth("reverse-add", 16, seed=196, base=10)
    z = c.project_nth("collatz", 32, seed=27, radix=2)
    # Both iterative families now construct source-independent binary-powered
    # operators.  Endpoint execution is deferred until a digit/value is asked
    # for; no orbit is replayed during projection construction.
    assert r.metrics.projection_work == 0
    assert z.metrics.projection_work == 0
    assert z.metrics.construction_steps <= 2 * (32).bit_length()
    assert r.metrics.raw_squarings == 0
    assert z.metrics.raw_squarings == 0


def test_special_term_projection_is_direct_and_has_no_raw_squaring() -> None:
    c = NumberCompiler()
    f = c.project_nth("fermat", 20)
    m = c.project_nth("mersenne", 100_000)
    assert f.metrics.projection_work == 0
    assert m.metrics.projection_work == 0
    assert f.metrics.raw_squarings == m.metrics.raw_squarings == 0
    assert f.metrics.descriptor_bits <= 8
    assert m.metrics.descriptor_bits <= 17
    assert f.symbolic == "2^(2^20)+1"
    assert m.symbolic == "2^100000-1"


def test_output_cap_applies_only_when_materializing() -> None:
    term = NumberCompiler().project_nth("fermat", 20)
    assert term.estimated_bit_length == (1 << 20) + 1
    with pytest.raises(ValueError):
        term.materialize(max_bits=1024)


def test_cli_value_symbolic_json_and_family_alias(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert cli_main(["196", "--nth", "5"]) == 0
    assert capsys.readouterr().out.strip() == "52514"

    assert cli_main(["fermat", "--nth", "20", "--format", "symbolic"]) == 0
    assert capsys.readouterr().out.strip() == "2^(2^20)+1"

    assert (
        cli_main(["prime", "--nth", "10", "--format", "json", "--info", "metrics"]) == 0
    )
    obj = json.loads(capsys.readouterr().out)
    assert obj["value"] == "31"
    assert obj["info"]["metrics"]["projection_work"] > 0


def test_cli_rejects_missing_seed(capsys: pytest.CaptureFixture[str]) -> None:
    assert cli_main(["collatz", "--nth", "4"]) == 2
    assert "requires --seed" in capsys.readouterr().err


def test_reverse_add_growth_projection_uses_boundary_phase_only(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("orbit/carry construction entered growth-only projection")

    monkeypatch.setattr(reverse_digits, "reverse_add_nth_formula", forbidden)
    c = NumberCompiler()
    state = c.project_reverse_add_growth_state(196, base=10)
    assert (state.boundary_offset, state.relation, state.growth) == (0, -1, 0)
    assert c.project_reverse_add_boundary_phase(196, base=10) == -1
    assert c.project_reverse_add_growth(196, base=10) == 0
    assert c.project_reverse_add_growth_state(99, base=10).growth == 1
    assert c.project_reverse_add_boundary_phase(10989, base=10) in (-1, 0, 1)


def test_single_digit_projection_never_materializes_the_full_word(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError(
            "full digit materialization entered single-digit projection"
        )

    monkeypatch.setattr(
        "number_compiler.hashlife.execution.evaluator.materialize_values", forbidden
    )
    c = NumberCompiler()

    # Sparse special sources answer arbitrary positions directly from their
    # source descriptors, including enormous Fermat endpoints.
    assert c.project_digit("fermat", 20, 0) == 1
    assert c.project_digit("fermat", 20, 123456) == 0
    assert c.project_digit("fermat", 20, 1 << 20) == 1
    assert c.project_digit("mersenne", 100_000, 99_999) == 1

    # Formula families evaluate only the requested position rather than calling
    # materialize_values on the complete term.
    term = c.project_nth("reverse-add", 5, seed=196, base=10)
    assert term.digit(0) == 4
    assert c.project_digit("reverse-add", 5, 0, seed=196, base=10) == 4


def test_large_fermat_projection_keeps_public_width_symbolic(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("dyadic extent materialized during projection")

    monkeypatch.setattr(DyadicExtent, "materialize", forbidden)
    term = NumberCompiler().project_nth("fermat", 1_000_000)
    assert term.estimated_bit_length == DyadicExtent(1_000_000, 1)
    assert term.metrics.width == DyadicExtent(1_000_000, 1)
    assert term.digit(0) == 1
    assert term.digit(1) == 0


def test_native_binary_special_output_skips_integer_materialization(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.api.cli import _render_value
    from number_compiler.sequences.power_numbers.numbers import (
        FermatNumberSpec,
        MersenneNumberSpec,
    )

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("special integer materialized for native binary output")

    monkeypatch.setattr(FermatNumberSpec, "materialize", forbidden)
    monkeypatch.setattr(MersenneNumberSpec, "materialize", forbidden)
    compiler = NumberCompiler()
    assert (
        _render_value(compiler.project_nth("fermat", 4), output_base=2, max_bits=32)
        == bin(65537)[2:]
    )
    assert (
        _render_value(compiler.project_nth("mersenne", 13), output_base=2, max_bits=32)
        == "1" * 13
    )
