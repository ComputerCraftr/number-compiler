from __future__ import annotations

import number_compiler
from devtools.paths import repository_root
from number_compiler.api.number_api import NumberCompiler, PoweredCollatzTermPayload
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def test_public_reverse_add_and_collatz_use_only_powered_block_backends() -> None:
    root = repository_root() / "src" / "number_compiler"
    reverse_text = (root / "sequences/reverse_add/power.py").read_text()
    api_text = (root / "api/number_api.py").read_text()
    collatz_text = (root / "sequences/collatz/block_power.py").read_text()

    assert "ReverseAddCausalSpacetimeEngine" not in reverse_text
    assert "collatz_orbit_formulas(" not in api_text
    assert "collatz_orbit_formulas_ternary" not in api_text
    assert "collatz_orbit_formulas_local_composite_radix" not in api_text
    assert "CollatzCausalSpacetimeEngine" not in collatz_text
    for retired in (
        "ReverseAddCausalSpacetimeEngine",
        "CollatzCausalSpacetimeEngine",
        "BlockPointIndex",
        "CollatzGermTransitionCache",
        "collatz_affine_suffix_event_power_word",
        "collatz_affine_suffix_event_power_value",
    ):
        assert not hasattr(number_compiler, retired), retired


def test_collatz_huge_nth_construction_is_logarithmic_and_does_not_execute_endpoint() -> (
    None
):
    steps = 10**18
    term = PoweredCollatzTerm(27, steps)
    metrics = term.metrics()
    assert metrics.point_queries == 0
    assert metrics.direct_powered_point_queries == 0
    assert metrics.operator_nodes <= 2 * steps.bit_length()
    assert metrics.compose_operations <= 2 * steps.bit_length()
    assert metrics.syntax_depth_bound <= steps.bit_length() + 2


def test_number_api_collatz_projection_is_lazy_binary_powered() -> None:
    term = NumberCompiler().project_nth("collatz", 10**12, seed=27, radix=2)
    assert term.metrics.projection_work == 0
    assert term.metrics.construction_steps < 2 * (10**12).bit_length()
    assert isinstance(term.payload, PoweredCollatzTermPayload)
    payload_metrics = term.payload.power_metrics()
    assert payload_metrics.point_queries == 0
    assert payload_metrics.direct_powered_point_queries == 0


def test_fast_paths_remain_exact_on_representative_terms() -> None:
    assert (
        ReverseAddPoweredTerm(196, 16, base=10).materialize(max_bits=10_000)
        == 897100798
    )
    assert PoweredCollatzTerm(27, 10).materialize(max_bits=10_000) == 214
    compiler = NumberCompiler()
    assert compiler.nth("collatz", 10, seed=27, radix=2) == 214
    assert compiler.nth("collatz", 10, seed=27, radix=3) == 214
    assert compiler.nth("collatz", 10, seed=27, radix=6) == 214
