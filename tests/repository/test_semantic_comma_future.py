"""Keep semantic source/future proofs independent of eager concrete publishers."""

from devtools.checks.isabelle_registry import discover_sessions
from devtools.checks.isabelle_source_analysis import (
    IsabelleDeclaration,
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


def _future_theory(name: str) -> tuple[str, dict[str, IsabelleDeclaration]]:
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_future_instance"
        / f"{name}.thy"
    )
    source = path.read_text(encoding="utf-8")
    return source, {
        item.name: item for item in extract_isabelle_declarations(source, path)
    }


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


def test_semantic_boundary_bridge_consumes_direct_round_refinement() -> None:
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Instance.thy"
    )
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(path.read_text(), path)
    }
    bridge = declarations["comma_semantic_boundary_step_decisive_round"].body
    assert "comma_decisive_endpoint_round_refines[" in bridge
    assert "comma_round_control_germ_refines" in bridge
    assert "comma_round_close" in bridge


def test_semantic_future_checker_context_is_private_and_entry_open_scoped() -> None:
    root = isabelle_root(repository_root())
    instance_path = (
        root
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Instance.thy"
    )
    source = instance_path.read_text(encoding="utf-8")
    checker = next(
        body
        for body in ml_cartouches(source)
        if "structure Comma_Semantic_Future_Candidate_Check" in body
    )
    private = checker.split("\nlocal\n", 1)[1].split("\nin\n", 1)[0]
    assert "val checker_cache" in private
    assert "fun access_checker operation" in private
    assert "val entry_open_theory_name =" in private
    assert "Long_Name.qualify (Resources.theory_qualifier owner_theory_name)" in private
    assert '"Comma_Semantic_Entry_Open"' in private

    context_tac = checker.split("fun context_tac ctxt operation i state =", 1)[1].split(
        "fun class_table_tac", 1
    )[0]
    assert "Context.subthy_id (owner_theory_id, requested_theory_id)" in context_tac
    assert (
        "Context.theory_long_name requested_theory = entry_open_theory_name"
        in context_tac
    )
    assert "Seq.list_of (operation (#proof_context checker) i state)" in context_tac
    assert "Seq.of_list results" in context_tac

    # Provider admission now comes from the checked 16-source normal-form
    # action, rather than a second theorem-construction cache in this checker.
    # Keep the cache private-context contract above, and assert the new
    # source-to-provider proof path at its theorem owner.
    _source_bridge, source_bridge_declarations = _future_theory(
        "Comma_Semantic_Future_Source_NF_Bridge"
    )
    boundary_action = source_bridge_declarations[
        "comma_semantic_future_initial_nf_direct_boundary_exact"
    ].body
    assert "comma_boundary_valid q" in boundary_action
    assert "comma_semantic_graph_initial_nf_actions" in boundary_action
    assert "comma_semantic_future_initial_source_index q" in boundary_action
    assert "delta\\<le>27" in boundary_action
    assert "(snd (snd q)+delta) mod 924" in boundary_action
    assert "Comma_Semantic_B1_CRT_Stop J delta" in boundary_action
    assert "actual_delta=1+H" in boundary_action
    assert "comma_semantic_boundary_children" in boundary_action
    assert boundary_action.index("(Comma_N,a,") < boundary_action.index("(Comma_Z,a,")
    assert "comma_semantic_future_candidate_" not in boundary_action
    assert "comma_semantic_future_projected_key_apply" not in boundary_action

    _candidate_bridge, candidate_declarations = _future_theory(
        "Comma_Semantic_Future_Candidate_Bridge"
    )
    candidate_action = candidate_declarations[
        "comma_semantic_future_initial_nf_action_boundary_exact"
    ].body
    assert "comma_semantic_future_initial_nf_direct_boundary_exact[OF valid]" in (
        candidate_action
    )
    assert "comma_semantic_future_candidate_child_ids_at" in candidate_action
    assert "comma_semantic_future_candidate_class_ids" in candidate_action
    assert "comma_semantic_future_projected_key_apply" in candidate_action
    assert "comma_semantic_future_candidate_child_receiver" not in candidate_action
    assert "J<9" in candidate_action and "delta\\<le>27" in candidate_action
    assert "(snd (snd q)+delta) mod 924" in candidate_action
    assert "ordered_children" in candidate_action
    assert candidate_action.index("(Comma_N,a,") < candidate_action.index("(Comma_Z,a,")
    assert "comma_semantic_future_initial_nf_source_key_action_result" in (
        candidate_action
    )
    assert "source_J=J" in candidate_action and "source_delta=delta" in candidate_action

    closure, closure_declarations = _future_theory(
        "Comma_Semantic_Future_Candidate_Provider_Closure"
    )
    row_proof = closure_declarations[
        "comma_semantic_future_candidate_provider_row_of_initial_nf_boundary"
    ].body
    assert "comma_semantic_future_initial_nf_action_boundary_exact" in row_proof
    assert "boundary_control" in row_proof and "boundary_children" in row_proof
    assert "comma_semantic_future_candidate_provider_check_checked" in closure
    assert "comma_semantic_future_provider_check_lifts_rank" in closure
    assert "comma_semantic_concrete_future_rank_check" in closure

    compare_path = (
        root
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Action_Compare.thy"
    )
    weighted_transport_path = (
        root
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Weighted_Transport.thy"
    )
    compare_source = compare_path.read_text(encoding="utf-8")
    weighted_transport = weighted_transport_path.read_text(encoding="utf-8")
    projected_declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            weighted_transport, weighted_transport_path
        )
    }
    projected_apply = projected_declarations[
        "comma_semantic_future_projected_key_apply"
    ].body
    assert "Comma_Future_Fork target" in projected_apply
    assert "north_weight" in projected_apply and "south_weight" in projected_apply
    assert "Comma_Future_Landmine" in projected_apply
    assert "comma_semantic_future_action_children_shape Comma_Future_Landmine []" in (
        projected_apply
    )
    compare_declarations = {
        item.name: item
        for item in extract_isabelle_declarations(compare_source, compare_path)
    }
    north_receiver = compare_declarations[
        "comma_semantic_future_candidate_child_receiver_north"
    ].body
    south_receiver = compare_declarations[
        "comma_semantic_future_candidate_child_receiver_south"
    ].body
    for receiver in (north_receiver, south_receiver):
        assert "Comma_Future_Fork target_family_digit" in receiver
        assert r"_ \<Rightarrow> Comma_Weighted_CRT_Leaf 0" in receiver
    provider_nf_path = (
        root
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Candidate_Provider_NF.thy"
    )
    provider_nf = provider_nf_path.read_text(encoding="utf-8")
    assert "comma_semantic_future_candidate_parent_key_action_apply" in (compare_source)
    assert 'assumes table: "comma_semantic_future_candidate_class_table_check"' in (
        compare_source
    )
    assert "comma_semantic_future_candidate_parent_source_key_nf" in provider_nf
    assert "comma_semantic_future_projected_key_apply" in provider_nf


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


def test_concrete_summary_consumes_graph_power_and_instantiates_boundary_bridge() -> (
    None
):
    root = isabelle_root(repository_root())
    path = (
        root
        / "families/comma/comma_semantic_graph_instance"
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
    assert "comma_semantic_graph_action_power_refines" in source
    code = declarations["comma_semantic_decade_summary_code"].body
    assert "comma_semantic_graph_action_power 5 r (comma_offset_orbit x)" in code
    assert "Comma_Semantic_B1_Stop D" in code
    assert "comma_terminal_weight_decode D" in code
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


def test_b32_instance_uses_the_demand_driven_graph_action_certificate() -> None:
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_graph_instance"
        / "Comma_Semantic_Graph_B32_Instance.thy"
    )
    text = path.read_text(encoding="utf-8")
    declarations = {
        item.name: item for item in extract_isabelle_declarations(text, path)
    }
    stop = declarations["comma_semantic_graph_b32_stop242_checked"].body
    for condition in (
        "root<46",
        "phase<924",
        "comma_semantic_graph_action_power 5 phase root",
        "D\\<le>242",
    ):
        assert condition in stop
    assert 'ML_file "semantic_graph_action_certificate.ML"' in text
    assert "Comma_Semantic_Graph_Action_Certificate.make" in text
    assert "comma_semantic_graph_action_power_refines" in text
    graph_power_path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_graph_instance"
        / "Comma_Semantic_Graph_Action_Power.thy"
    )
    graph_power = executable_text(graph_power_path.read_text(encoding="utf-8"))
    assert "comma_semantic_graph_valid_checked" in graph_power
    assert "comma_semantic_graph_root_binding_exact" in graph_power
    assert "comma_semantic_graph_action_power_refines" in graph_power

    # The Continue image supplies exact output and its physical Stop bound.
    # The graph projector consumes that theorem after its own refinement.
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
    assert "comma_continue24_image_implies_direct_certificate" in rank_source
    assert "comma_continue_frontier_empty_implies_image" in rank_source
    assert "comma_semantic_phase_continue24_image_checked" in exact_bound
    semantic_path = (
        path.parent.parent / "comma_semantic_b1_instance/Comma_Semantic_B1_Instance.thy"
    )
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
    assert "comma_semantic_b1_action_b32_stop242_checked" in stop


def test_release_consumers_project_the_graph_power_refinement() -> None:
    root = isabelle_root(repository_root())
    summary_path = (
        root
        / "families/comma/comma_semantic_graph_instance/Comma_Semantic_Summary_Instance.thy"
    )
    future_path = (
        root
        / "families/comma/comma_semantic_future_instance/Comma_Semantic_Future_Instance.thy"
    )
    entry_path = (
        root
        / "families/comma/comma_semantic_future_instance/Comma_Semantic_Entry_Open.thy"
    )
    global_path = (
        root
        / "families/comma/comma_semantic_future_instance/Comma_Semantic_Global_Safety.thy"
    )
    release_path = (
        root
        / "families/comma/comma_semantic_future_instance/Comma_Semantic_Release.thy"
    )

    summary_text = summary_path.read_text(encoding="utf-8")
    summary_declarations = {
        item.name: item
        for item in extract_isabelle_declarations(summary_text, summary_path)
    }
    assert "comma_semantic_graph_action_power 5 r (comma_offset_orbit x)" in (
        summary_declarations["comma_semantic_decade_summary_code"].body
    )
    assert "comma_semantic_graph_action_power_refines" in summary_text

    future_text = future_path.read_text(encoding="utf-8")
    assert "Comma_Semantic_Future_Source_NF_Bridge" in future_text
    assert "comma_semantic_future_candidate_class_table_checked" in future_text

    closure_text, closure_declarations = _future_theory(
        "Comma_Semantic_Future_Candidate_Provider_Closure"
    )
    provider_row = closure_declarations[
        "comma_semantic_future_candidate_provider_row_of_initial_nf_boundary"
    ].body
    assert "comma_semantic_future_initial_nf_action_boundary_exact" in provider_row
    assert "boundary_control" in provider_row and "boundary_children" in provider_row
    assert "comma_semantic_future_candidate_provider_check_checked" in closure_text

    # The entry-open slice remains a separate, bounded projection request. Its
    # checked list still uses the graph-action projector; the all-family future
    # provider is certified through Source_NF_Bridge above.
    entry_consumer = executable_text(entry_path.read_text(encoding="utf-8"))
    assert "Comma_Semantic_Graph_Action_Certificate.make" in entry_consumer
    assert "comma_semantic_b1_action_power 5 phase root" in entry_consumer
    assert "Comma_Selected_List_Conversion.schematize" in entry_consumer

    # Source admission and class-row validity remain separate prerequisites.
    _source_nf_text, source_nf_declarations = _future_theory(
        "Comma_Semantic_Future_Source_NF_Bridge"
    )
    initial_action = source_nf_declarations[
        "comma_semantic_future_initial_nf_direct_boundary_exact"
    ].body
    assert "comma_semantic_graph_initial_nf_actions" in initial_action
    assert "J<9" in initial_action and "delta\\<le>27" in initial_action
    assert "(snd (snd q)+delta) mod 924" in initial_action
    assert "comma_semantic_boundary_children" in initial_action
    assert "comma_semantic_future_candidate_" not in initial_action
    _, source_imports = parse_theory_header(
        _source_nf_text,
        root
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Source_NF_Bridge.thy",
    )
    assert source_imports == ("Comma_Semantic_Future_Source_Action",)
    assert "Comma_Semantic_Future_Candidate_Bridge" in closure_text

    provider_nf_path = (
        root
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Candidate_Provider_NF.thy"
    )
    provider_nf = provider_nf_path.read_text(encoding="utf-8")
    provider_nf_ml = (
        provider_nf_path.parent / "semantic_future_candidate_provider_nf.ML"
    ).read_text(encoding="utf-8")
    assert "comma_semantic_graph_initial_nf_actions_length" in provider_nf
    assert "comma_semantic_future_candidate_provider_nf_actions_equal" in provider_nf
    assert "comma_semantic_future_candidate_source_key_nf_all_phases" in provider_nf
    assert "comma_semantic_graph_initial_nf_actions_def" in provider_nf_ml
    assert "length source_nf_terms = 16" in provider_nf_ml
    assert "comma_semantic_future_projected_key_apply" in provider_nf_ml
    assert "key_dagT" not in provider_nf_ml
    assert "temporary" not in provider_nf_ml
    assert "val child_serializer = Data.make_serializer arena natT" in provider_nf_ml
    assert "Data.erase_weights arena" in provider_nf_ml
    assert "terminal = 8 then Data.leaf arena (payload_of (nat 0))" in provider_nf_ml
    provider_functions = {
        declaration.name: declaration.body
        for declaration in extract_isabelle_declarations(
            provider_nf_ml,
            provider_nf_path.parent / "semantic_future_candidate_provider_nf.ML",
        )
    }
    # The checked combined output owns both children. Admission retains their
    # order and rejects malformed terminal shapes before either projection.
    components = provider_functions["parse_candidate_output_components"]
    assert "[north, south] => (north, south)" in components
    assert "Provider_Landmine =>" in components
    assert "if null children then (0, 0)" in components
    assert "payload ctxt class_count (nat north_id)" in components
    assert "payload ctxt class_count (nat south_id)" in components
    lookup = provider_functions["candidate_output"]
    assert "exact_closed ctxt theorem" in lookup
    assert "Context.subthy" in lookup
    publisher = provider_functions["publish"]
    assert publisher.count("candidate_output ctxt") == 1
    assert "comma_semantic_future_candidate_class_output_key" in publisher
    assert publisher.index("candidate_output ctxt") < publisher.index(
        "parse_candidate_output_components"
    )
    assert "candidate_child_projection true id_action" in publisher
    assert "candidate_child_projection false id_action" in publisher

    global_text = executable_text(global_path.read_text(encoding="utf-8"))
    assert "comma_semantic_concrete_boundary_strong_occurrence_bridge" in global_text
    assert "comma_semantic_global_release_safety" in global_text
    assert "comma_semantic_future_candidate_provider_check_checked" in global_text
    assert "comma_semantic_concrete_future_rank_check" in global_text
    release_text = executable_text(release_path.read_text(encoding="utf-8"))
    assert "comma_semantic_graph_action_power_refines" in release_text
    assert "comma_semantic_graph_b32_stop242_checked" in release_text
