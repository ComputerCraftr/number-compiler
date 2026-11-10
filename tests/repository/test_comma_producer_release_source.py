"""Guard the concrete comma writer bridge and its Isabelle symbol syntax."""

from collections.abc import Mapping

from devtools.checks.isabelle_source_analysis import extract_isabelle_declarations
from devtools.checks.isabelle_syntax import Session
from devtools.paths import isabelle_root
from number_compiler.sequences.comma.future_authority import (
    GLOBAL_RELEASE_CLAIMS,
    GLOBAL_RELEASE_CONTRACT_ID,
    GLOBAL_RELEASE_SESSION_ID,
    GLOBAL_RELEASE_THEOREM_ID,
)

ISABELLE = isabelle_root()


def test_concrete_decade_summary_producer_bridge_is_registered(
    repository_sessions: Mapping[str, Session],
) -> None:
    future = repository_sessions["Comma_Semantic_Future_Instance"]
    assert "Comma_Semantic_Release" in future.theories
    assert GLOBAL_RELEASE_SESSION_ID == future.name
    assert GLOBAL_RELEASE_THEOREM_ID == (
        "Comma_Semantic_Release.comma_semantic_producer_global_release_contract"
    )
    assert GLOBAL_RELEASE_CONTRACT_ID == "comma-semantic-producer-global-release-v2"
    assert "producer-writer-point-and-prefix-refinement" in GLOBAL_RELEASE_CLAIMS
    assert "boundary-grouped-chart-termination" in GLOBAL_RELEASE_CLAIMS
    assert (
        "boundary-scalar-chart-to-published-macro-refinement" in GLOBAL_RELEASE_CLAIMS
    )

    release = (
        ISABELLE
        / "families/comma/comma_semantic_future_instance/Comma_Semantic_Release.thy"
    ).read_text()
    summary = (
        ISABELLE
        / "families/comma/comma_semantic_graph_instance/Comma_Semantic_Summary_Instance.thy"
    ).read_text()

    assert "comma_semantic_graph_action_power 5 r (comma_offset_orbit x)" in summary
    assert "comma_semantic_graph_action_power_refines" in summary
    summary_declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            summary,
            ISABELLE
            / "families/comma/comma_semantic_graph_instance/Comma_Semantic_Summary_Instance.thy",
        )
    }
    stop_bridge = summary_declarations["comma_semantic_b1_action_power_b32_stop242"]
    assert "comma_semantic_b1_action_b32_stop242_checked" in stop_bridge.body

    assert "comma_semantic_decade_summary_writer_release" in release
    summary_result_start = release.index(
        "definition comma_semantic_decade_writer_release_result"
    )
    summary_result_end = release.index(
        "definition comma_semantic_decade_partial_selection_result"
    )
    summary_contract = release[summary_result_start:summary_result_end]
    for contract_field in (
        "comma_semantic_decade_summary",
        "comma_decade_exact_summary",
        "comma_python_writer_run",
        "comma_python_published_weights",
        "comma_python_published_displacements",
        "length (comma_python_published_weights",
        "length (comma_python_published_displacements",
        "foldl comma_python_affine_add comma_python_affine_zero",
    ):
        assert contract_field in summary_contract
    assert (
        "comma_semantic_decade_writer_release_result p x h terminal events"
        in release[
            release.index(
                "theorem comma_semantic_decade_summary_writer_release_closed"
            ) :
        ]
    )
    assert "theorem comma_semantic_producer_global_release_contract:" in release
    release_declarations = {
        item.name
        for item in extract_isabelle_declarations(
            release,
            ISABELLE
            / "families/comma/comma_semantic_future_instance/Comma_Semantic_Release.thy",
        )
    }
    assert GLOBAL_RELEASE_THEOREM_ID.partition(".")[2] in release_declarations
    aggregate_start = release.index(
        "theorem comma_semantic_producer_global_release_contract:"
    )
    aggregate_end = release.index("ML \\<open>", aggregate_start)
    aggregate_contract = release[aggregate_start:aggregate_end]
    for release_field in (
        "comma_semantic_b32_boundary_chart_publisher_contract",
        "comma_python_grouped_chart_walk",
        "comma_semantic_b32_grouped_chart_terminates",
        "comma_semantic_decade_writer_release_result",
        "comma_semantic_decade_partial_selection_result",
        "comma_semantic_global_release_safety",
        "comma_decade_admitted",
        "path 412987859=19999999999",
        "comma_child",
    ):
        assert release_field in aggregate_contract

    boundary_start = release.index(
        "theorem comma_semantic_b32_boundary_chart_publisher_closed"
    )
    boundary_end = release.index(
        "theorem comma_semantic_b32_grouped_chart_terminates", boundary_start
    )
    boundary_bridge = release[boundary_start:boundary_end]
    for bridge_field in (
        "comma_python_scalar_chart_walk_to_first_terminal_walk",
        "comma_python_boundary_indexed_macro_fields",
        "comma_semantic_decade_summary_provider_exact",
        "comma_python_first_terminal_walk_result_unique",
        "comma_python_make_indexed_macro_output",
    ):
        assert bridge_field in boundary_bridge

    selection_start = release.index(
        "definition comma_semantic_decade_partial_selection_result"
    )
    selection_end = release.index(
        "theorem comma_semantic_decade_summary_writer_release:"
    )
    selection_contract = release[selection_start:selection_end]
    assert "comma_semantic_decade_writer_release_result" in selection_contract
    for contract_field in (
        "comma_prefix_lower_bound",
        "comma_python_cut_boundaries",
        "weights = comma_python_published_weights",
        "prefixes = map",
        "length weights = Suc (length fragments)",
        "length prefixes = Suc (length fragments)",
        "comma_python_fragment_scale_guard",
        "comma_python_fragment_event_cut",
        "comma_python_fragment_event_count",
        "comma_python_event_prefix_endpoint",
        "comma_chart_value",
        "comma_python_affine_evaluate",
        "comma_python_affine_denominator",
        "comma_python_affine_divides",
        "comma_python_published_displacements",
        "comma_python_fragment_weight_at_scale",
        "i < length fragments",
        "prefixes ! i < target",
        r"target \<le> prefixes ! Suc i",
        "comma_python_event_weight_prefix",
    ):
        assert contract_field in selection_contract
    selection_proof = release[
        release.index(
            "theorem comma_semantic_decade_writer_partial_selection:"
        ) : release.index(
            "theorem comma_semantic_decade_writer_partial_selection_closed"
        )
    ]
    assert (
        "comma_python_actual_writer_published_displacement_prefixes" in selection_proof
    )
    closed_selection = release[
        release.index(
            "theorem comma_semantic_decade_writer_partial_selection_closed"
        ) : release.index("ML \\<open>")
    ]
    assert "comma_semantic_decade_partial_selection_result" in closed_selection
    assert "\\<forall>p x target." in closed_selection
    assert "5 \\<le> p" in closed_selection
    assert "boundaries weights prefixes i" in closed_selection

    audit_start = release.index("val endpoints =")
    audit_end = release.index("\\<close>", audit_start)
    expected_audit = release[audit_start:audit_end]
    for global_authority in (
        "comma_semantic_global_release_safety",
        "comma_semantic_future_candidate_provider_check_checked",
        "comma_semantic_concrete_future_rank_check",
        "comma_semantic_concrete_boundary_strong_occurrence_bridge",
        "comma_semantic_graph_valid_checked",
        "comma_semantic_graph_root_binding_exact",
        "comma_semantic_graph_root_action_exact",
        "comma_semantic_graph_action_power_refines",
        "comma_semantic_b1_action_power_refines_orbit",
        "comma_semantic_phase_continue24_image_certificate_native",
        "comma_semantic_phase_continue24_image_checked",
        "comma_semantic_phase_class_B32_exact_output_checked",
        "comma_semantic_phase_class_B32_exact_output",
        "comma_crt_rank_relations_sound",
        "comma_semantic_decade_summary_provider_exact",
        "comma_semantic_graph_b32_stop242_checked",
        "comma_semantic_p5_entry_future_open_checked",
        "comma_semantic_p5_entry_infinite_imp_open",
        "comma_semantic_unique_infinite_decimal_root",
        "comma_semantic_concrete_source20_infinite_path",
        "comma_semantic_concrete_source20_z_no_infinite_path",
        "comma_semantic_concrete_future_paths_agree",
        "comma_every_positive_has_decimal_root",
        "comma_source20_to_fork_unique",
    ):
        assert global_authority in expected_audit


def test_b32_bridge_covers_the_concrete_ungrouped_boundary_chart_loop() -> None:
    release = (
        ISABELLE
        / "families/comma/comma_semantic_future_instance/Comma_Semantic_Release.thy"
    ).read_text()
    theorem_name = "comma_semantic_b32_boundary_chart_loop_structurally_terminates"
    assert theorem_name in release
    start = release.index(f"theorem {theorem_name}:")
    end = release.index("\nlemma comma_python_writer_run_fragments_unique", start)
    bridge = release[start:end]
    for exact_bridge_step in (
        "5 \\<le> p",
        "2 \\<le> a",
        "a \\<le> 9",
        "comma_semantic_decade_summary_provider_exact",
        "comma_python_boundary_indexed_trace",
        "comma_indexed_trace_to_python_first_terminal_walk",
        "comma_indexed_trace_is_refined",
        "comma_refined_indexed_trace",
    ):
        assert exact_bridge_step in bridge

    coefficients = (
        ISABELLE
        / "families/comma/comma_semantic_future_instance/Comma_Semantic_Producer_Coefficients.thy"
    ).read_text()
    producer_bridge_start = coefficients.index(
        "theorem comma_python_boundary_indexed_trace:"
    )
    producer_bridge_end = coefficients.index(
        "\ntheorem comma_python_boundary_indexed_macro_fields", producer_bridge_start
    )
    producer_bridge = coefficients[producer_bridge_start:producer_bridge_end]
    for crossing_step in (
        "comma_round_close_crossing_phase",
        "comma_round_weighted_prefix_indexed_trace_continue",
        "comma_indexed_trace_shift_position",
    ):
        assert crossing_step in producer_bridge

    chart_source = (
        ISABELLE.parent.parent / "src/number_compiler/sequences/comma/boundary_chart.py"
    ).read_text()
    initial_start = chart_source.index("def initial_chart(")
    initial_end = chart_source.index("\n\ndef validate_chart", initial_start)
    initial = chart_source[initial_start:initial_end]
    assert 'BoundaryChart("near", a - 1, 0, 1)' in initial
    assert 'BoundaryChart("entry", a, 0, 0)' in initial

    loop_start = chart_source.index("def chart_moves(")
    loop = chart_source[loop_start:]
    assert "grouped_near: bool = False" in loop
    assert "move = chart_step(residue, chart, charge_bits=charge_bits)" in loop


def test_producer_near_increment_uses_one_isabelle_exists_symbol() -> None:
    producer = (
        ISABELLE
        / "families/comma/comma_semantic_future_instance/Comma_Semantic_Producer_Record_Refinement.thy"
    ).read_text()
    marker = "definition comma_python_fragment_record_matches"
    start = producer.index(marker)
    end = producer.index("\n\ntext", start)
    declaration = producer[start:end]

    assert r"(\<exists>increment." in declaration
    assert r"(\\<exists>increment." not in declaration


def test_grouped_chart_termination_uses_the_checked_scalar_continuation(
    repository_sessions: Mapping[str, Session],
) -> None:
    future = repository_sessions["Comma_Semantic_Future_Instance"]
    assert future.theories.index(
        "Comma_Python_Grouped_Near_Refinement"
    ) < future.theories.index("Comma_Python_Grouped_Chart_Refinement")
    assert future.theories.index(
        "Comma_Python_Grouped_Chart_Refinement"
    ) < future.theories.index("Comma_Semantic_Release")
    owner = ISABELLE / "families/comma/comma_semantic_future_instance"
    grouped = (owner / "Comma_Python_Grouped_Chart_Refinement.thy").read_text()
    for contract in (
        "comma_python_grouped_chart_walk_of_scalar",
        "comma_python_scalar_chart_walk_cut_near_prefix",
        "length suffix_moves < length scalar_moves",
        "comma_round_weighted_prefix p (p mod 924)",
        "comma_python_chart_literal_increment macro = h - ?t",
        "Thm_Deps.all_oracles",
    ):
        assert contract in grouped
    release = (owner / "Comma_Semantic_Release.thy").read_text()
    start = release.index("theorem comma_semantic_b32_grouped_chart_terminates:")
    end = release.index("\nlemma comma_python_writer_run_fragments_unique", start)
    bridge = release[start:end]
    assert "comma_semantic_b32_scalar_chart_terminates" in bridge
    assert (
        "comma_python_grouped_chart_walk_of_scalar[OF scalar exponent admitted]"
        in bridge
    )
    assert "= Some outcome" in bridge
