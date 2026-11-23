"""Keep semantic source/future proofs independent of eager concrete publishers."""

from devtools.checks.isabelle_registry import discover_sessions
from devtools.checks.isabelle_source_analysis import (
    extract_isabelle_declarations,
)
from devtools.checks.isabelle_syntax import (
    executable_text,
    ml_cartouches,
    parse_theory_header,
    session_dependency_closure,
)
from devtools.paths import isabelle_root, repository_root

THEORY_PATH = (
    isabelle_root(repository_root())
    / "families/comma/comma_semantic_future"
    / "Comma_Semantic_Future.thy"
)


def test_semantic_future_owner_uses_only_foundational_imports() -> None:
    theory_name, imports = parse_theory_header(
        THEORY_PATH.read_text(encoding="utf-8"), THEORY_PATH
    )

    assert theory_name == "Comma_Semantic_Future"
    assert imports == (
        "Comma_Cylinder.Comma_Finite_Transition",
        "Comma_Arithmetic.Comma_Boundary_Primitives",
    )
    assert not any(
        "Sparse" in imported or "Rank_Data" in imported or "Native_Boundary" in imported
        for imported in imports
    )


def test_semantic_future_owner_exposes_the_shared_proof_chain() -> None:
    declarations = extract_isabelle_declarations(
        THEORY_PATH.read_text(encoding="utf-8"), THEORY_PATH
    )
    names = {declaration.name for declaration in declarations}

    assert {
        "comma_semantic_occurrence_bridge",
        "comma_semantic_rank_check",
        "comma_semantic_ranked_state_no_infinite_path",
        "comma_semantic_unranked_state_has_infinite_path",
        "comma_semantic_infinite_path_forces_unique_unranked_child",
        "comma_semantic_rank_check_lifts_through_class_map",
    } <= names


def test_root_routes_share_literal_arithmetic_without_sharing_future_authority() -> (
    None
):
    root = isabelle_root(repository_root())
    shared = root / "families/comma/comma_entry" / "Comma_Global_Root_Arithmetic.thy"
    legacy = (
        root / "families/comma/comma_future_global" / "Comma_Global_Root_Safety.thy"
    )
    semantic = (
        root
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Global_Root_Bridge.thy"
    )
    helpers = {
        "comma_child_strict_growth",
        "comma_child_increment_bound",
        "comma_child_parent",
        "comma_infinite_root_first_p5_entry",
        "comma_p5_open_entries_have_root20",
    }
    shared_source = shared.read_text()
    shared_names = {
        declaration.name
        for declaration in extract_isabelle_declarations(shared_source, shared)
    }
    assert helpers <= shared_names
    shared_text = executable_text(shared_source)
    assert "comma_decimal_root_of.simps[simp del]" in shared_text
    for consumer in (legacy, semantic):
        text = consumer.read_text()
        _, imports = parse_theory_header(text, consumer)
        assert "Comma_Source_Entry.Comma_Global_Root_Arithmetic" in imports
        local_names = {
            declaration.name
            for declaration in extract_isabelle_declarations(text, consumer)
        }
        assert helpers.isdisjoint(local_names)
    # This helper theory imports only arithmetic/source foundations. Its local
    # all_oracles block audits those helper lemmas; it is not future authority.
    _, shared_imports = parse_theory_header(shared_source, shared)
    assert shared_imports == (
        "Comma_Source_Entry",
        "Comma_C1_Occurrence.Comma_C1_First_Sector",
        "Comma_Arithmetic.Comma_Decimal_Parent",
        "Comma_Arithmetic.Comma_Child_Classification",
    )
    shared_audits = tuple(
        body for body in ml_cartouches(shared_source) if "Thm_Deps.all_oracles" in body
    )
    assert len(shared_audits) == 1
    assert helpers <= set(shared_audits[0].split())

    _, imports = parse_theory_header(semantic.read_text(), semantic)
    assert not any("Native" in name or "Forest" in name for name in imports)


def test_semantic_path_bridge_retains_unique_prefix_at_the_selected_weight() -> None:
    root = isabelle_root(repository_root())
    path = root / "families/comma/comma_semantic_future" / "Comma_Semantic_Path.thy"
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            path.read_text(encoding="utf-8"), path
        )
    }
    bridge = declarations["comma_semantic_strong_occurrence_bridge"].body
    assert "control_step q = Some control" in bridge
    assert "comma_unique_literal_path weight (value q p) endpoint" in bridge
    assert "comma_semantic_infinite_paths_agree" in declarations
    assert "comma_semantic_strong_occurrence_bridge_implies" in declarations
    native = (
        root
        / "families/comma/comma_native_boundary"
        / "Comma_Native_Path_Uniqueness.thy"
    ).read_text(encoding="utf-8")
    assert "comma_native_unique_path_prefix" not in native
    assert "comma_unique_literal_path_prefix" in native


def test_semantic_global_bridge_retains_every_infinite_path_not_one_witness() -> None:
    root = isabelle_root(repository_root())
    path = (
        root
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Global_Safety.thy"
    )
    source = path.read_text(encoding="utf-8")
    _, imports = parse_theory_header(source, path)
    assert "Comma_Semantic_Global_Root_Bridge" in imports
    assert not any("Native" in name or "Forest" in name for name in imports)
    declarations = {
        item.name: item for item in extract_isabelle_declarations(source, path)
    }
    assert {
        "comma_semantic_source20_global_infinite_literal_path",
        "comma_semantic_source20_global_first_choice_unique",
        "comma_semantic_source20_global_infinite_paths_agree",
        "comma_semantic_decimal_root_infinite_iff_20",
        "comma_semantic_global_release_safety",
    } <= declarations.keys()
    agreement = declarations["comma_semantic_source20_global_infinite_paths_agree"].body
    assert "comma_semantic_concrete_future_paths_agree" in agreement
    assert "comma_unique_literal_path_prefix" in agreement
    assert "left_initial" in agreement and "right_initial" in agreement


def test_semantic_stop_occurrence_bridge_has_no_concrete_sparse_authority() -> None:
    root = isabelle_root(repository_root())
    path = (
        root
        / "families/comma/comma_semantic_future"
        / "Comma_Semantic_B1_Future_Bridge.thy"
    )
    source = path.read_text(encoding="utf-8")
    name, imports = parse_theory_header(source, path)
    assert name == "Comma_Semantic_B1_Future_Bridge"
    assert imports == (
        "Comma_Semantic_B1.Comma_Semantic_Action_Power",
        "Comma_Decade_Occurrence_Lift.Comma_Decade_Occurrence_Lift",
    )
    sessions = discover_sessions(root)
    closure = session_dependency_closure(sessions, ("Comma_Semantic_Future",))
    assert "Comma_Semantic_B1" in closure
    assert not {
        "Comma_Sparse_Core",
        "Comma_Sparse_Base_Instance",
        "Comma_Sparse_Power_Instance",
        "Comma_Native_Future_Instance",
        "Comma_Native_Summary",
        "Comma_Native_Summary_Occurrence",
        "Comma_Future_Rank_Data",
    }.intersection(closure)
    assert "require_native_clean" in source


def test_semantic_graph_reuses_the_canonical_packet_recurrence() -> None:
    root = isabelle_root(repository_root())
    graph = root / "families/comma/comma_semantic_b1" / "Comma_Semantic_Graph.thy"
    packet = (
        root
        / "families/comma/comma_decisive_endpoint_quotient"
        / "Comma_Decisive_Endpoint_Quotient.thy"
    )
    graph_names = {
        item.name
        for item in extract_isabelle_declarations(
            graph.read_text(encoding="utf-8"), graph
        )
    }
    packet_names = {
        item.name
        for item in extract_isabelle_declarations(
            packet.read_text(encoding="utf-8"), packet
        )
    }
    assert "comma_decisive_endpoint_round_step_equation" not in graph_names
    assert "comma_decisive_endpoint_round_packet" in packet_names


def test_semantic_power_keeps_chronological_action_and_orbit_refinement() -> None:
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1"
        / "Comma_Semantic_Action_Power.thy"
    )
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            path.read_text(encoding="utf-8"), path
        )
    }
    power = declarations["comma_semantic_b1_action_power"].body
    assert "comma_semantic_word_then (2^k)" in power
    assert "comma_semantic_b1_action_power k" in power
    refinement = declarations["comma_semantic_b1_action_power_refines_orbit"].body
    assert "comma_orbit_word" in refinement
    assert "comma_semantic_b1_of_word" in refinement


def test_crt_lookup_reads_published_predicates_without_future_discovery() -> None:
    root = isabelle_root(repository_root())
    path = root / "families/comma/comma_semantic_b1" / "Comma_CRT_Power.thy"
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            path.read_text(encoding="utf-8"), path
        )
    }
    lookup = declarations["comma_crt_result_at"].body
    assert "List.find" in lookup
    assert "comma_crt_eval" in lookup
    for oracle in ("comma_orbit_word", "column_at", "comma_semantic_b1_output_binding"):
        assert oracle not in lookup
    stop_check = declarations["comma_crt_rows_stop242"].body
    assert "list_all" in stop_check
    assert "snd row" in stop_check
    assert "comma_crt_eval" not in stop_check
    assert "924" not in stop_check
    assert {
        "comma_crt_result_at_preserves_invalid",
        "comma_crt_result_at_rejects_malformed_width",
        "comma_crt_result_at_stop242",
    } <= declarations.keys()


def test_stop_occurrence_bridge_covers_offsets_and_preserves_exponent_weight() -> None:
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_future"
        / "Comma_Semantic_B1_Future_Bridge.thy"
    )
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            path.read_text(encoding="utf-8"), path
        )
    }
    bridge = declarations["comma_semantic_b32_stop_exact_occurrence_for_offset"].body
    assert "comma_offset_orbit x" in bridge
    assert "comma_orbit_word_refines" in bridge
    assert "comma_chart_value (p+h)" in bridge
    assert "comma_summary_ordered_children terminal (p+h)" in bridge
    assert "comma_chart_value (p+D)" not in bridge
    assert "comma_offset_representatives" not in bridge
    projection = declarations[
        "comma_semantic_b32_entry_infinite_path_projects_summary_child"
    ].body
    assert "comma_semantic_b32_stop_exact_occurrence_for_offset" in projection
    assert "comma_unique_literal_path_endpoint" in projection
    assert "stream weight=endpoint" in projection
    assert "successor=stream (Suc weight)" in projection
    assert "comma_summary_ordered_children terminal (p+h)" in projection


def test_concrete_summary_consumes_checked_weight_and_instantiates_boundary_bridge() -> (
    None
):
    root = isabelle_root(repository_root())
    path = (
        root
        / "families/comma/comma_semantic_b1_instance"
        / "Comma_Semantic_Summary_Instance.thy"
    )
    source_text = path.read_text(encoding="utf-8")
    source = executable_text(source_text)
    declarations = {
        item.name: item for item in extract_isabelle_declarations(source_text, path)
    }
    boundary_path = (
        root
        / "families/comma/comma_semantic_future"
        / "Comma_Semantic_B1_Future_Bridge.thy"
    )
    boundary_text = boundary_path.read_text(encoding="utf-8")
    boundary_declarations = {
        item.name: item
        for item in extract_isabelle_declarations(boundary_text, boundary_path)
    }
    provider = boundary_declarations["comma_semantic_decade_summary"].body
    assert "comma_semantic_b1_action_power 5 r (comma_offset_orbit x)" in provider
    assert "comma_offset_orbit x" in provider
    assert "comma_terminal_weight_decode D" in provider
    exact = declarations["comma_semantic_decade_summary_total_exact"].body
    assert "comma_semantic_b1_action_power_b32_stop242" in exact
    bound = declarations["comma_semantic_b1_action_power_b32_stop242"].body
    assert "comma_semantic_b1_action_b32_stop242_checked" in bound
    assert "D\\<le>242" in bound
    code = declarations["comma_semantic_decade_summary_code"].body
    assert "comma_frontier_m204_weight r (comma_offset_orbit x)" in code
    assert "comma_terminal_weight_decode" in code
    assert "comma_decade_admitted s" in code
    assert "comma_frontier_m204_exact_weight_from_checked_bellman" in code
    assert "comma_frontier_m204_bellman_native" in code
    assert "comma_semantic_decade_summary_code[code]" in source
    assert "comma_semantic_decade_summary_total_exact_for_bound" in executable_text(
        source
    )
    assert "comma_semantic_concrete_boundary_occurrence_bridge" in source
    assert "[OF comma_semantic_decade_summary_provider_exact]" in source
    sessions = discover_sessions(root)
    closure = session_dependency_closure(sessions, ("Comma_Semantic_B1_Instance",))
    assert "Comma_Semantic_B1" in closure
    assert not any(session.endswith("_Smoke") for session in closure)
    assert not {
        "Comma_Sparse_Core",
        "Comma_Sparse_Base_Instance",
        "Comma_Sparse_Power_Instance",
        "Comma_Future_Rank_Data",
    }.intersection(closure)


def test_b32_instance_uses_checked_bellman_exact_output() -> None:
    rank_path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1_instance"
        / "Comma_Continue_Image_Instance.thy"
    )
    rank_text = rank_path.read_text(encoding="utf-8")
    rank_source = executable_text(rank_text)
    rank_declarations = {
        item.name: item for item in extract_isabelle_declarations(rank_text, rank_path)
    }
    exact_bound = rank_declarations[
        "comma_semantic_phase_class_B32_exact_output_checked"
    ].body
    for condition in (
        "phase<924",
        "cid<46",
        "height\\<le>26",
        "comma_decade_exact_summary",
        "comma_semantic_b1_action_power 5 phase cid",
        "comma_terminal_weight_encode height terminal\\<le>242",
    ):
        assert condition in exact_bound
    assert "Comma_Continue_Frontier24_Source_Bridge" in rank_source
    assert "comma_frontier_m204_exact_stop_from_checked_bellman" in exact_bound
    assert "comma_frontier_m204_bellman_native" in exact_bound
    semantic_path = rank_path.parent / "Comma_Semantic_B1_Instance.thy"
    semantic_declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            semantic_path.read_text(), semantic_path
        )
    }
    semantic_bound = semantic_declarations[
        "comma_semantic_b1_action_b32_stop242_checked"
    ].body
    assert "comma_semantic_phase_class_B32_exact_output_checked" in semantic_bound
    assert "comma_semantic_graph_action_power" not in semantic_bound


def test_future_source_bridge_preserves_physical_outputs_and_child_order() -> None:
    path = THEORY_PATH.parent / "Comma_Future_M204_Source_Bridge.thy"
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(path.read_text(), path)
    }
    bridge = declarations["comma_future_m204_source_output_exact"].body
    assert "comma_frontier_m204_bellman D" in bridge
    assert "comma_boundary_valid q" in bridge
    assert "J<9" in bridge
    assert "comma_semantic_boundary_control_step" in bridge
    assert "comma_semantic_boundary_children" in bridge
    assert "(snd (snd q)+delta) mod 924" in bridge
    assert bridge.index("(Comma_N,J+2,") < bridge.index("(Comma_Z,J+2,")


def test_future_rank_publication_consumes_checked_family_transports() -> None:
    owner = THEORY_PATH.parent.parent / "comma_semantic_future_instance"
    source = (owner / "semantic_future_m204_final_publication.ML").read_text()
    assert "length family_facts=16" in source
    assert "comma_future_m204_boundary_cases" in source
    assert "comma_future_m204_source_rank_lift" in source
    assert "[bellman,rows_checked,bound_fact,join_fact]" in source
    assert "require_native_clean" in source
    instance = (owner / "Comma_Semantic_Future_Instance.thy").read_text()
    assert "Comma_Future_M204_Component_Loader.prepare" in instance
    assert "comma_semantic_concrete_future_rank_check" in instance
    assert "comma_semantic_concrete_source20_unranked" in instance
    assert "comma_semantic_concrete_source20_z_ranked_value" in instance


def test_decimal_root_gate_uses_authenticated_points_and_exact_fixture() -> None:
    owner = THEORY_PATH.parent.parent / "comma_semantic_future_instance"
    source = (owner / "semantic_future_m204_entry_open.ML").read_text()
    assert "Comma_CRT_MDD_Point_Eval.prove" in source
    assert "Store.action_index" in source
    assert "exact_prop" in source
    assert "require_native_clean" in source
    assert '"[0..<91::nat]"' in source
    assert '"[3,34,75::nat]"' in source
    assert "comma_semantic_decade_summary_code" in source
    assert "comma_future_m204_rank_def" in source
