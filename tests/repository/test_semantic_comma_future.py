"""Keep semantic source/future proofs independent of eager concrete publishers."""

from devtools.checks.isabelle_source_analysis import extract_isabelle_declarations
from devtools.checks.isabelle_syntax import (
    dynamic_cartouche_spans,
    executable_text,
    ml_cartouches,
    navigation_text,
    parse_sessions,
    parse_theory_header,
    session_dependency_closure,
)
from devtools.paths import isabelle_root, repository_root

THEORY_PATH = (
    isabelle_root(repository_root())
    / "comma_semantic_future"
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
    shared = root / "comma_entry" / "Comma_Global_Root_Arithmetic.thy"
    legacy = root / "comma_future_global" / "Comma_Global_Root_Safety.thy"
    semantic = (
        root
        / "comma_semantic_future_instance"
        / "Comma_Semantic_Global_Root_Bridge.thy"
    )
    helpers = {
        "comma_child_strict_growth",
        "comma_child_increment_bound",
        "comma_child_parent",
        "comma_infinite_root_first_p5_entry",
        "comma_p5_open_entries_have_root20",
    }
    shared_names = {
        declaration.name
        for declaration in extract_isabelle_declarations(shared.read_text(), shared)
    }
    assert helpers <= shared_names
    shared_text = executable_text(shared.read_text())
    assert "comma_decimal_root_of.simps[simp del]" in shared_text
    assert "Thm_Deps.all_oracles" not in shared_text
    for consumer in (legacy, semantic):
        text = consumer.read_text()
        _, imports = parse_theory_header(text, consumer)
        assert "Comma_Source_Entry.Comma_Global_Root_Arithmetic" in imports
        local_names = {
            declaration.name
            for declaration in extract_isabelle_declarations(text, consumer)
        }
        assert helpers.isdisjoint(local_names)
    _, imports = parse_theory_header(semantic.read_text(), semantic)
    assert not any("Native" in name or "Forest" in name for name in imports)


def test_semantic_path_bridge_retains_unique_prefix_at_the_selected_weight() -> None:
    root = isabelle_root(repository_root())
    path = root / "comma_semantic_future" / "Comma_Semantic_Path.thy"
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
        root / "comma_native_boundary" / "Comma_Native_Path_Uniqueness.thy"
    ).read_text(encoding="utf-8")
    assert "comma_native_unique_path_prefix" not in native
    assert "comma_unique_literal_path_prefix" in native


def test_semantic_global_bridge_retains_every_infinite_path_not_one_witness() -> None:
    root = isabelle_root(repository_root())
    path = root / "comma_semantic_future_instance" / "Comma_Semantic_Global_Safety.thy"
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
    path = root / "comma_semantic_future" / "Comma_Semantic_B1_Future_Bridge.thy"
    source = path.read_text(encoding="utf-8")
    name, imports = parse_theory_header(source, path)
    assert name == "Comma_Semantic_B1_Future_Bridge"
    assert imports == (
        "Comma_Semantic_B1.Comma_Semantic_B1_Power",
        "Comma_Native_Summary_Occurrence.Comma_Native_Summary_Occurrence",
    )
    sessions = parse_sessions((root / "ROOT").read_text(encoding="utf-8"))
    closure = session_dependency_closure(sessions, ("Comma_Semantic_Future",))
    assert "Comma_Semantic_B1" in closure
    assert not {
        "Comma_Sparse_Base_Instance",
        "Comma_Sparse_Power_Instance",
        "Comma_Native_Future_Instance",
        "Comma_Future_Rank_Data",
    }.intersection(closure)
    assert "require_native_clean" in source


def test_semantic_source_slot_does_not_materialize_an_action_row() -> None:
    path = (
        isabelle_root(repository_root())
        / "comma_semantic_b1"
        / "Comma_Semantic_B1_Table_Transform.thy"
    )
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            path.read_text(encoding="utf-8"), path
        )
    }
    body = declarations["comma_semantic_b1_source_slot_action"].body
    assert "comma_decisive_endpoint_packet" in body
    assert "comma_source_continuation_id" not in body
    assert "comma_source_continuation_action_at" not in body
    assert "comma_semantic_b1_source_slot_action_refines" in declarations


def test_semantic_b1_does_not_build_the_physical_row_audit() -> None:
    root = isabelle_root(repository_root())
    sessions = parse_sessions((root / "ROOT").read_text(encoding="utf-8"))
    closure = session_dependency_closure(sessions, ("Comma_Semantic_B1",))
    assert "Comma_Semantic_Graph_Instance" not in closure
    for name in (
        "Comma_Semantic_B1_Columns",
        "Comma_Semantic_B1_Publication",
        "Comma_Semantic_B1_Table_Transform",
        "Comma_Semantic_B1_CRT_Source_Binding",
        "Comma_CRT_Columns",
        "Comma_CRT_Apply",
        "Comma_CRT_Power",
    ):
        text = (root / "comma_semantic_b1" / f"{name}.thy").read_text(encoding="utf-8")
        assert "Thm.consolidate" not in text
        assert "require_native_clean" in text


def test_semantic_graph_reuses_the_canonical_packet_recurrence() -> None:
    root = isabelle_root(repository_root())
    graph = root / "comma_semantic_b1" / "Comma_Semantic_Graph.thy"
    packet = (
        root
        / "comma_decisive_endpoint_quotient"
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


def test_candidate_publication_does_not_require_physical_row_certificates() -> None:
    root = isabelle_root(repository_root())
    candidate = (
        root / "comma_semantic_b1_instance" / "semantic_b1_template_constructor.ML"
    ).read_text(encoding="utf-8")
    foundation = (
        root / "comma_semantic_b1" / "Comma_Semantic_B1_Table_Transform.thy"
    ).read_text(encoding="utf-8")
    assert 'ML_file "semantic_b1_template_constructor.ML"' not in foundation
    assert all(
        "Comma_Semantic_B1_Template_Constructor.make" not in body
        for body in ml_cartouches(foundation)
    )
    for retired in (
        "graph_engine",
        "source_row_equation",
        "source_action_rows",
        "source_order_valid_goal",
        "graph_valid_goal",
        "table_goal",
        "partition_rebase_goal",
        "reconstruction_goal",
        "Code_Evaluation.dynamic_value_strict",
    ):
        assert retired not in candidate
    assert "comma_semantic_b1_source_slot_actions" in candidate
    assert "val columnT = @{typ comma_crt_column}" in candidate
    publisher = (
        root / "comma_semantic_b1_instance" / "semantic_b1_occurrence_publication.ML"
    ).read_text(encoding="utf-8")
    # HOL serialization moved out of discovery so shared nodes survive until
    # publication; constructor identity and kernel checking remain unchanged.
    assert "@{term Comma_CRT_Node}" in publisher
    assert "#template_keys artifact" in publisher
    assert "HOLogic.mk_Collect" not in candidate
    assert not (root / "comma_semantic_b1" / "semantic_b1_publication.ML").exists()


def test_root_instance_consumes_certified_occurrences_without_source_replay() -> None:
    root = isabelle_root(repository_root())
    path = root / "comma_semantic_b1_instance" / "Comma_Semantic_B1_Instance.thy"
    source = path.read_text(encoding="utf-8")
    declarations = {
        item.name: item for item in extract_isabelle_declarations(source, path)
    }
    root_action = declarations["comma_semantic_b1_crt_root_split_action"].body
    assert "comma_semantic_b1_crt_root_occurrence" in root_action
    assert "comma_crt_occurrence_split_action" in root_action
    assert "None" in root_action and "comma_crt_occurrence_split_initial" in root_action
    assert "comma_crt_source_recursive_rows" not in executable_text(source)
    assert "comma_semantic_b1_crt_root_split_action_exact" in declarations
    assert "comma_semantic_b1_crt_root_occurrence_exact" in source
    assert "comma_semantic_b1_crt_power_result_outside_domain" in declarations
    assert "discover_sources" not in source
    assert "Template_Constructor.make" not in source
    assert "source_order" not in source
    assert not (path.parent / "semantic_b1_source_order_instance.ML").exists()


def test_power_definition_keeps_control_and_weight_separate() -> None:
    path = (
        isabelle_root(repository_root())
        / "comma_semantic_b1_instance"
        / "Comma_Semantic_B1_Instance.thy"
    )
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            path.read_text(encoding="utf-8"), path
        )
    }
    power = declarations["comma_semantic_b1_crt_power_split_action"].body
    assert "comma_crt_split_compose_from" in power
    assert "comma_crt_split_control" in power
    assert "comma_crt_split_weight" in power
    assert "comma_semantic_b1_crt_power_split_action_consistent" in declarations
    assert "comma_semantic_b1_crt_power_split_action_exact" in declarations
    query = declarations["comma_semantic_b1_crt_power_result"].body
    assert "comma_semantic_b1_crt_power_split_action" in query
    assert "comma_crt_split_mdd_result_at" in query
    assert "comma_semantic_b1_crt_power_rows" not in declarations


def test_online_publication_checks_shape_and_all_goto_children() -> None:
    root = isabelle_root(repository_root()) / "comma_semantic_b1_instance"
    path = root / "Comma_Semantic_B1_Occurrence_Publication.thy"
    source = path.read_text(encoding="utf-8")
    declarations = {
        item.name: item for item in extract_isabelle_declarations(source, path)
    }
    shape = next(
        item.body
        for item in extract_isabelle_declarations(source, path)
        if item.name == "comma_semantic_b1_crt_occurrence_data_checked"
        and item.command == "definition"
    )
    assert "length comma_semantic_b1_crt_root_occurrence_indices = 46" in shape
    assert "list_all comma_semantic_b1_crt_occurrence_entry_checked" in shape
    assert "list_all comma_semantic_b1_crt_source_order_step" in shape
    assert "distinct comma_semantic_b1_crt_sources" not in shape
    uniqueness = declarations["comma_semantic_b1_crt_source_order_distinct"].body
    assert 'shows "distinct comma_semantic_b1_crt_sources"' in uniqueness
    assert "comma_semantic_b1_crt_source_order_steps_sorted" in uniqueness
    assert (
        "comma_semantic_b1_crt_source_order_rejects_equal_adjacent_keys" in declarations
    )
    assert (
        "comma_semantic_b1_crt_source_order_distinct"
        in declarations["comma_semantic_b1_crt_published_resolves_index"].body
    )
    assert "comma_semantic_b1_crt_source_index" not in shape
    assert "List.find" not in shape
    indexed_entry = declarations["comma_semantic_b1_crt_occurrence_entry_checked"].body
    assert "comma_semantic_b1_crt_lift_local_cover_witness" in indexed_entry
    assert "comma_semantic_b1_crt_lift_refs ! index" in indexed_entry
    assert "comma_semantic_b1_crt_published" not in indexed_entry
    assert "List.find" not in indexed_entry
    entry = declarations["comma_semantic_b1_crt_root_entry_checked"].body
    assert "distinct" not in entry
    binding = declarations[
        "comma_semantic_b1_crt_root_occurrence_distinct_binding"
    ].body
    assert "comma_semantic_b1_crt_occurrence_entry_checked_at" in binding
    assert "comma_semantic_b1_crt_lift_local_cover_witness" in binding
    assert (
        'shows "distinct (comma_semantic_b1_crt_occurrence_beta occurrence)"' in binding
    )
    exact = declarations["comma_semantic_b1_crt_published_exact"].body
    assert "comma_semantic_b1_crt_occurrence_map_exact" in exact
    assert (
        "comma_semantic_b1_crt_lift_local_cover_candidate_matches"
        in executable_text(source)
    )
    assert "published child=Some child_occurrence" in exact
    lookup = declarations["comma_semantic_b1_crt_root_occurrence"].body
    assert "comma_semantic_b1_crt_root_occurrence_indices ! root" in lookup
    assert "else None" in lookup
    for obsolete in (
        "comma_crt_source_recursive_rows",
        "comma_response_data_rows",
        "comma_semantic_b1_crt_slot_child_indices",
        "comma_semantic_b1_crt_occurrence_indexed_local_check",
        "comma_semantic_b1_crt_occurrence_goto_rows_check",
        "comma_semantic_b1_crt_occurrence_terminal_rows_check",
        "comma_semantic_b1_crt_online_fold_refs",
        "comma_semantic_b1_crt_occurrence_online_fold_witness",
        "[0..<924]",
    ):
        assert obsolete not in executable_text(source)


def test_candidate_fold_retains_child_occurrences_instead_of_physical_returns() -> None:
    path = (
        isabelle_root(repository_root())
        / "comma_semantic_b1_instance"
        / "semantic_b1_template_constructor.ML"
    )
    source = path.read_text(encoding="utf-8")
    declarations = {
        item.name: item for item in extract_isabelle_declarations(source, path)
    }
    # The shared ML analyzer deliberately does not model nested let bindings.
    # These are lexical ownership checks; executable sign/binding tests live
    # in the ML owner and are run by the concrete publication theory below.
    constructor = executable_text(source)
    assert "make" in declarations
    assert "occurrence_for child" in constructor
    assert "#return_shift occurrence" in constructor
    assert "#binding occurrence" in constructor
    assert "cached_slot_lift" in constructor
    assert "mdd_partition Termtab.table" not in source
    assert "fold_source_mdds" not in declarations
    assert "binding_rows_term" not in constructor
    assert "pairwise_disjoint" not in constructor
    assert "Pending_Child" not in constructor


def test_candidate_occurrence_examples_are_executed_without_graph_discovery() -> None:
    path = (
        isabelle_root(repository_root())
        / "comma_semantic_b1_instance"
        / "semantic_b1_template_constructor.ML"
    )
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            path.read_text(encoding="utf-8"), path
        )
    }
    assert "lift_template_slot_with" in declarations
    publisher_path = path.parent / "semantic_b1_occurrence_publication.ML"
    publisher = publisher_path.read_text(encoding="utf-8")
    assert "check_candidate_examples" in {
        item.name for item in extract_isabelle_declarations(publisher, publisher_path)
    }
    examples = executable_text(publisher)
    for behavior in (
        "shifted",
        "swapped_binding",
        "complementary",
        "overlap",
        "missing",
    ):
        assert behavior in examples
    publication = (
        path.parent / "Comma_Semantic_B1_Occurrence_Publication.thy"
    ).read_text(encoding="utf-8")
    bodies = ml_cartouches(publication)
    assert any("Publication.check_candidate_examples ()" in body for body in bodies)
    assert all("Template_Constructor.make" not in body for body in bodies)
    assert publication.index(
        "Publication.check_candidate_examples ()"
    ) < publication.index("local_setup")


def test_occurrence_fold_does_not_assume_a_child_physical_return_table() -> None:
    root = isabelle_root(repository_root()) / "comma_semantic_b1"
    path = root / "Comma_Semantic_B1_CRT_Occurrence_Fold.thy"
    source = path.read_text(encoding="utf-8")
    declarations = {
        item.name: item for item in extract_isabelle_declarations(source, path)
    }
    local_step = declarations["comma_semantic_b1_crt_occurrence_local_step"].body
    assert "children child" in local_step
    assert "comma_semantic_b1_crt_occurrence_lookup" in local_step
    for retired in ("source_recursive_rows", "source_rows_from", "rows_exact"):
        assert retired not in executable_text(source)
    resolver = declarations["comma_semantic_b1_crt_resolve_descriptor"].body
    assert "cid < length templates" in resolver
    assert "else None" in resolver
    assert "templates!cid" in resolver
    assert "comma_semantic_b1_crt_resolve_descriptor_rejects_foreign" in declarations
    shape_check = declarations["comma_semantic_b1_crt_occurrence_wellformed_check"].body
    assert "comma_semantic_b1_crt_occurrence_geometry_check" in shape_check
    geometry = declarations["comma_semantic_b1_crt_occurrence_geometry_check"].body
    assert "comma_crt_equiv_check" in geometry
    assert "comma_crt_supported" in geometry
    assert "comma_semantic_b1_crt_geometry_fold" in geometry
    assert "occurrence_rebase" not in geometry
    assert "occurrence_beta" not in geometry
    assert "comma_semantic_b1_crt_occurrence_geometry_check_sound" in declarations
    for rejection in ("empty", "overlap", "missing_coverage", "bad_column"):
        assert (
            f"comma_semantic_b1_crt_occurrence_geometry_check_rejects_{rejection}"
            in declarations
        )
    assert "occurrence_covered" not in shape_check
    assert "occurrence_disjoint" not in shape_check
    assert "forall" not in shape_check
    contract = declarations["comma_semantic_b1_crt_occurrence_candidate_exact"].body
    for obligation in ("child_present", "child_exact", "candidate", "wellformed"):
        assert obligation in contract
    foundation = (root / "Comma_Semantic_B1_Table_Transform.thy").read_text(
        encoding="utf-8"
    )
    owners = {
        item.name
        for item in extract_isabelle_declarations(
            foundation, root / "Comma_Semantic_B1_Table_Transform.thy"
        )
    }
    assert {
        "comma_semantic_b1_terminal_action_result_present",
        "comma_semantic_b1_terminal_action_output",
    } <= owners
    lift_path = root / "Comma_Semantic_B1_CRT_Local_Cover.thy"
    lift = {
        item.name: item.body
        for item in extract_isabelle_declarations(lift_path.read_text(), lift_path)
    }
    witness = lift["comma_semantic_b1_crt_lift_local_cover_witness"]
    assert "children" not in witness
    for suffix in ("local_slot_valid", "local_cover_witness"):
        body = lift[f"comma_semantic_b1_crt_lift_{suffix}"]
        assert "comma_crt_set" not in body
        assert "goto_rows_check" not in body
        assert "terminal_rows_check" not in body
    assert "comma_semantic_b1_crt_lift_local_slot_valid" in witness
    assert "comma_crt_occurrence_split_action" not in witness
    assert "comma_semantic_b1_crt_lift_source_split_action" not in witness


def test_occurrence_checker_keeps_clock_quantifiers_out_of_execution() -> None:
    path = (
        isabelle_root(repository_root())
        / "comma_semantic_b1"
        / "Comma_Semantic_B1_CRT_Local_Cover.thy"
    )
    source = path.read_text(encoding="utf-8")
    declarations = {
        item.name: item for item in extract_isabelle_declarations(source, path)
    }
    for name in (
        "comma_semantic_b1_crt_lift_local_cover_witness",
        "comma_semantic_b1_crt_lift_local_slot_valid",
    ):
        body = declarations[name].body
        assert "occurrence_wellformed" not in body
        assert "candidate_matches" not in body
        assert "[0..<924]" not in body
    assert "comma_semantic_b1_crt_lift_local_cover_candidate_matches" in declarations
    cover = declarations["comma_semantic_b1_crt_local_piece_covered"].body
    assert "comma_crt_supported" in cover
    assert "comma_crt_negate parent_column" in cover
    assert "comma_crt_occurrence_split_from_bindings" not in executable_text(source)
    for retired in (
        "source_recursive_rows",
        "source_rows_from",
        "comma_response_data_rows",
    ):
        assert retired not in executable_text(source)


def test_occurrence_induction_uses_actual_goto_decrease_and_required_children() -> None:
    root = isabelle_root(repository_root()) / "comma_semantic_b1"
    source = (root / "Comma_Semantic_B1_CRT_Occurrence_Fold.thy").read_text(
        encoding="utf-8"
    )
    assert "comma_source_continuation_goto_decreases" in source
    assert "comma_semantic_b1_crt_occurrence_map_exact" in source
    assert "child_present" in source
    assert "child_exact" in source
    assert "less_induct" in source
    for retired in (
        "source_action_rows_equation",
        "local_packet_equations",
        "comma_semantic_b1_source_order_valid",
    ):
        assert retired not in source
    for retired_file in (
        "Comma_Semantic_B1_Source_Order_Certificate.thy",
        "semantic_b1_source_order_publisher.ML",
        "Comma_Semantic_B1_Source_Fold_Refinement.thy",
        "Comma_Semantic_B1_Source_Binding_Refinement.thy",
        "Comma_Semantic_B1_CRT_Provider_Fold.thy",
        "Comma_Semantic_B1_CRT_Recursive_Provider.thy",
        "Comma_Semantic_B1_CRT_Occurrence_Check.thy",
        "Comma_Semantic_B1_CRT_Occurrence_Grouped_Refinement.thy",
        "Comma_Semantic_B1_CRT_Occurrence_Online_Fold.thy",
        "Comma_Semantic_B1_CRT_Occurrence_Online_Fold_Refinement.thy",
    ):
        assert not (root / retired_file).exists()


def test_crt_lookup_reads_published_predicates_without_future_discovery() -> None:
    root = isabelle_root(repository_root())
    path = root / "comma_semantic_b1" / "Comma_CRT_Power.thy"
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
        / "comma_semantic_future"
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
    assert "comma_semantic_b32_stop_exact_occurrence" not in declarations
    projection = declarations[
        "comma_semantic_b32_entry_infinite_path_projects_summary_child"
    ].body
    assert "comma_semantic_b32_stop_exact_occurrence_for_offset" in projection
    assert "comma_unique_literal_path_endpoint" in projection
    assert "stream weight=endpoint" in projection
    assert "successor=stream (Suc weight)" in projection
    assert "comma_summary_ordered_children terminal (p+h)" in projection


def test_concrete_summary_consumes_checked_b32_and_instantiates_boundary_bridge() -> (
    None
):
    root = isabelle_root(repository_root())
    path = root / "comma_semantic_b1_instance" / "Comma_Semantic_Summary_Instance.thy"
    source = path.read_text(encoding="utf-8")
    declarations = {
        item.name: item for item in extract_isabelle_declarations(source, path)
    }
    provider = declarations["comma_semantic_decade_summary"].body
    assert "comma_semantic_b1_crt_power_result 5" in provider
    assert "comma_offset_orbit x" in provider
    assert "comma_terminal_weight_decode D" in provider
    exact = declarations["comma_semantic_decade_summary_total_exact"].body
    assert "comma_semantic_b1_crt_b32_stop242_checked" in exact
    assert "comma_semantic_b1_crt_b32_result_exact" in exact
    assert "comma_semantic_b32_stop_exact_occurrence_for_offset" in exact
    assert "[OF comma_semantic_decade_summary_provider_exact]" in source
    for retired in ("comma_checked_sparse_B32_rows", "comma_native_rank_measure"):
        assert retired not in executable_text(source)
    sessions = parse_sessions((root / "ROOT").read_text(encoding="utf-8"))
    closure = session_dependency_closure(sessions, ("Comma_Semantic_B1_Instance",))
    assert "Comma_Semantic_Future" in closure
    assert not {
        "Comma_Sparse_Base_Instance",
        "Comma_Sparse_Power_Instance",
        "Comma_Future_Rank_Data",
    }.intersection(closure)


def test_b32_instance_publishes_the_aggregate_range_certificate() -> None:
    path = (
        isabelle_root(repository_root())
        / "comma_semantic_b1_instance"
        / "Comma_Semantic_B1_Instance.thy"
    )
    text = path.read_text(encoding="utf-8")
    publication = next(
        body
        for _, _, body in dynamic_cartouche_spans(text)
        if "Local_Theory.note" in body
    )
    assert "#b32_stop242_all engine ()" in publication
    assert "comma_semantic_b1_crt_b32_roots_stop242_checked" in publication
    assert "require_native_clean" in publication
    exported = navigation_text(text)
    assert "lemmas comma_semantic_b1_crt_b32_stop242_checked =" in exported
    assert "[OF comma_semantic_b1_crt_b32_roots_stop242_checked]" in exported


def test_b32_weight_certificate_does_not_reopen_column_evaluation() -> None:
    source = (
        isabelle_root(repository_root())
        / "comma_semantic_b1_instance"
        / "semantic_b1_crt_conversion.ML"
    ).read_text(encoding="utf-8")
    assert "comma_crt_mdd_stop_weights_bounded242" in source
    assert "comma_crt_split_weight" in source
    assert "comma_crt_eval" not in executable_text(source)
    projection = (
        isabelle_root(repository_root())
        / "comma_semantic_b1_instance"
        / "semantic_b1_b32_projection.ML"
    ).read_text(encoding="utf-8")
    assert "stop_weights: thm" in projection
    assert "stop_weights_claim action" in projection
    assert "standalone stop_weights" in projection
    assert "standalone equation" in projection
    assert "equation_request root" in projection
    assert "comma_semantic_b1_crt_power_split_action_exact" in projection
    assert "comma_crt_split_mdd_result_at" in projection
    for retired in (
        "comma_crt_source_recursive_rows",
        "comma_crt_source_raw_rows",
        "comma_crt_compose_raw_rows",
        "comma_crt_power_table",
        "comma_semantic_b1_crt_root_rows_total",
        "comma_semantic_b1_crt_power_rows",
    ):
        assert retired not in executable_text(source)


def test_occurrence_certificate_waits_for_proof_and_preserves_memo_authority() -> None:
    root = isabelle_root(repository_root()) / "comma_semantic_b1_instance"
    publication = (root / "Comma_Semantic_B1_Occurrence_Publication.thy").read_text(
        encoding="utf-8"
    )
    checker = (root / "semantic_b1_occurrence_check_cache.ML").read_text(
        encoding="utf-8"
    )
    selector = (root.parent / "shared" / "selected_list_conversion.ML").read_text(
        encoding="utf-8"
    )
    shared = (root / "semantic_b1_crt_operation_conversion.ML").read_text(
        encoding="utf-8"
    )
    assert publication.index(
        "definition comma_semantic_b1_crt_occurrence_data_checked"
    ) < publication.index('ML_file "semantic_b1_occurrence_check_cache.ML"')
    assert "by comma_semantic_b1_occurrence_check" in publication
    assert publication.index("Thm.consolidate") < publication.index(
        "stage=after-concrete-check"
    )
    for authority_check in (
        "lhs aconv request",
        "closed rhs",
        "Thm.nprems_of theorem = 0",
        "null (Thm.hyps_of theorem)",
        "null (Thm.tpairs_of theorem)",
    ):
        assert authority_check in selector
    assert "Comma_Selected_List_Conversion.validate_equation" in checker
    assert "Simplifier.Congproc false" in checker
    assert "Code_Simp.static_conv" in checker
    assert "Simplifier.simpset_of evaluation_context" in checker
    operation_setup = checker.split("val operation_context =", 1)[1].split(
        "fun prove cterm =", 1
    )[0]
    initialize_operation_context = "operation_context_ref := SOME operation_context"
    assert initialize_operation_context in operation_setup
    assert operation_setup.index(initialize_operation_context) < operation_setup.index(
        "val _ = code_conversion := SOME"
    )
    assert operation_setup.index(initialize_operation_context) < operation_setup.index(
        "val _ = smoke"
    )
    assert "Termtab.delete request" in checker
    assert "memo_capacity" in checker
    # A kernel-valid equality can still have an unevaluated RHS. A plain
    # congruence procedure must not advertise it as completed normalization.
    publication_gate = checker.split("fun publish_completed", 1)[1].split(
        "fun convert", 1
    )[0]
    assert "check_equation request theorem" in publication_gate
    assert "status = {complete, nodes}" in publication_gate
    assert "status = {complete, nodes}, reused_rhs, reused_closed}" in publication_gate
    assert "value_nodes := !value_nodes + nodes" in publication_gate
    assert (
        "rhs_reuse_hits := !rhs_reuse_hits + 1" in publication_gate
        and "closed_reuse_hits := !closed_reuse_hits + 1" in publication_gate
    )
    assert "make_equation_checker ctxt" in checker
    assert "incomplete := Termtab.update" in publication_gate
    assert "rejected_partial = publish_completed" in checker
    assert "returned_by_congproc = memo_proc evaluation_context partial_key" in checker
    assert "incomplete := Termtab.delete partial_request" in checker
    assert "comma_semantic_b1_crt_geometry_fold accumulated entries" in checker
    assert "fold_hits_before_projections" in checker
    assert "fold_projections_are_exact" in checker
    assert "fold accumulator smoke was not cold" not in checker
    assert "crt_operation_base_patterns" in checker
    assert "crt_operation_base_heads" in checker
    assert "Comma_Entry_Arithmetic.natural_context ctxt" in checker
    assert "selector_context_ref" in checker
    assert "Let_def[abs_def]" in "".join(checker.split())
    assert "Thm.beta_conversion true" in checker
    assert "comma_crt_admitted lower column" in checker
    # Fold and primitive CRT requests use the same operand-first converter;
    # local copies previously drifted in HOL/meta-equation handling.
    assert "fun geometry_fold_conversion" not in checker
    assert "make_staged_operation_converter" in checker
    assert "reflect_boundaries boundaries" in shared
    assert "comma_crt_supported_node_short_circuit" in shared
    assert "rule RS @{thm eq_reflection}" in shared
    selected_check = checker.split("fun selected_geometry_rewrite", 1)[1].split(
        "fun publish_completed", 1
    )[0]
    assert "selected_was_active = Termtab.defined (!active) selected_request" in (
        selected_check
    )
    assert (
        selected_check.index("val simplify_attempt = Exn.capture")
        < (selected_check.index("Termtab.delete selected_request"))
        < selected_check.index("Exn.release simplify_attempt")
    )
    assert "if selected_was_active then ()" in selected_check
    assert "Termtab.update (selected_request, theorem)" not in selected_check


def test_static_code_preparation_excludes_generated_catalogue_constants() -> None:
    path = (
        isabelle_root(repository_root())
        / "comma_semantic_b1_instance"
        / "semantic_b1_occurrence_check_cache.ML"
    )
    checker = path.read_text(encoding="utf-8")
    primitive_roots = checker.split("val generic_constants =", 1)[1].split("val ", 1)[0]
    assert (
        "consts = filter_out (member (op =) operation_roots) generic_constants"
        in checker
    )
    for generated in (
        "comma_semantic_b1_crt_templates",
        "comma_semantic_b1_crt_descriptors",
        "comma_semantic_b1_crt_sources",
        "comma_semantic_b1_crt_source_index",
        "comma_semantic_b1_crt_root_occurrence_indices",
        "comma_semantic_b1_crt_published",
        "comma_semantic_b1_crt_occurrence_at_index",
    ):
        assert generated not in primitive_roots


def test_occurrence_certificate_assembles_indexed_facts_without_catalogue_rewrite() -> (
    None
):
    root = isabelle_root(repository_root()) / "comma_semantic_b1_instance"
    checker = (root / "semantic_b1_occurrence_check_cache.ML").read_text(
        encoding="utf-8"
    )
    indexed = checker.split("fun prove_list_all predicate range =", 1)[1].split(
        "fun prove_expression", 1
    )[0]
    assert "prove_true (predicate $ numeral index)" in indexed
    assert "Comma_Selected_List_Conversion.prove_indexed_list_all" in indexed
    shared = (root.parent / "shared" / "selected_list_conversion.ML").read_text(
        encoding="utf-8"
    )
    recurrence = shared.split("fun prove_indexed_list_all", 1)[1].split("fun make", 1)[
        0
    ]
    assert "comma_indexed_all_Suc" in indexed
    assert "comma_indexed_all_zero" in indexed
    for caller_path in (
        root / "Comma_Semantic_B1_Occurrence_Publication.thy",
        root.parent
        / "comma_semantic_future_instance"
        / "Comma_Semantic_Future_Instance.thy",
    ):
        caller = executable_text(caller_path.read_text(encoding="utf-8"))
        assert "Comma_Selected_List_Conversion.prove_indexed_list_all" in caller
        assert (
            "Comma_Semantic_B1_Occurrence_Check_Cache.prove_indexed_list_all"
            not in caller
        )
        assert "zero_fact = @{thm comma_indexed_all_zero}" in caller
        assert "step_fact = @{thm comma_indexed_all_Suc}" in caller
    assert "Thm.prop_of head_proof aconv expected_head" in recurrence
    assert "Thm.nprems_of head_proof = 0" in recurrence
    assert "null (Thm.hyps_of head_proof)" in recurrence
    assert "null (Thm.tpairs_of head_proof)" in recurrence
    assert "HOLogic.dest_list" not in recurrence
    assert "upt_rec" not in recurrence
    assert "HOLogic.dest_list" not in indexed
    assert "upt_rec" not in indexed
    assert "Simplifier.full_rewrite" not in checker
    assert "comma_semantic_b1_crt_source_index_for" not in checker
    assert "comma_semantic_b1_crt_published" not in checker
    dispatch = checker.split("fun prove_expression expression =", 1)[1].split(
        "val definition", 1
    )[0]
    assert "HOLogic.dest_bin" in dispatch
    assert "HOLogic.dest_conj" not in dispatch
    assert "then prove_list_all predicate range" in dispatch
    selector = (root.parent / "shared" / "selected_list_conversion.ML").read_text(
        encoding="utf-8"
    )
    assert "suffix_memo" in selector
    assert "_spine_node_visits=" in selector
    assert "_selected_cells=" in selector
    assert "_list_node_visits=" not in selector


def test_selected_list_checks_each_nested_extent_before_cache_access() -> None:
    path = isabelle_root(repository_root()) / "shared" / "selected_list_conversion.ML"
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            path.read_text(encoding="utf-8"), path
        )
        if item.ml
    }
    assert "make" in declarations
    # Nested ML let declarations are outside the shared declaration subset.
    body = executable_text(path.read_text(encoding="utf-8"))
    lookup = body.split("fun lookup cterm =", 1)[1].split("and nth cterm =", 1)[0]
    assert lookup.index("if not (in_extent cterm)") < lookup.index(
        "Termtab.lookup (!memo) key"
    )
    assert "Conv.arg_conv lookup" in lookup
    assert "extent_at extents depth" in body
    conversion = body.split("fun convert cterm =", 1)[1].split("val pattern", 1)[0]
    assert "else if owned_selector cterm then" in conversion
    assert "else if in_extent cterm then" not in conversion
    length_lookup = body.split("fun lookup_length cterm =", 1)[1].split(
        "fun convert cterm =", 1
    )[0]
    assert "list_size_spine (Thm.rhs_of selected)" in length_lookup
    assert "Simplifier.rewrite" not in length_lookup
    publication = (
        path.parent.parent
        / "comma_semantic_b1_instance"
        / "Comma_Semantic_B1_Occurrence_Publication.thy"
    ).read_text(encoding="utf-8")
    assert "nested_extent_regression" in publication
    assert 'slot"} [2, 3]' in publication
    assert "Exn.capture nested_select" in publication
    assert "selected_suffix_index_two" in publication
    assert "selected_suffix_index_three" in publication


def test_occurrence_evaluator_is_created_only_for_a_validated_subgoal() -> None:
    path = (
        isabelle_root(repository_root())
        / "comma_semantic_b1_instance"
        / "semantic_b1_occurrence_check_cache.ML"
    )
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            path.read_text(encoding="utf-8"), path
        )
        if item.ml
    }
    assert "tactic" in declarations
    tactic = executable_text(path.read_text(encoding="utf-8")).split(
        "fun tactic ctxt i =", 1
    )[1]
    assert tactic.index("fun solve") < tactic.index("val evaluator = make ctxt")
    assert tactic.index("if request aconv expected") < tactic.index(
        "val evaluator = make ctxt"
    )


def test_b1_terminal_projection_consumes_the_selected_endpoint_once() -> None:
    root = isabelle_root(repository_root())
    path = root / "comma_semantic_b1" / "Comma_Semantic_B1_Table_Transform.thy"
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            path.read_text(encoding="utf-8"), path
        )
    }
    assert "comma_semantic_b1_source_slot_action_width_refines" in declarations
    text = executable_text(path.read_text(encoding="utf-8"))
    action = text.split("definition comma_semantic_b1_source_slot_action_width", 1)[
        1
    ].split("definition comma_semantic_b1_source_slot_actions", 1)[0]
    assert action.count("comma_decisive_sector_target") == 1
    assert "comma_near_terminal_width_j f h" in action
    assert "Comma_Continuation_Landmine delta" in action
    assert "Comma_Continuation_Fork (j + 2) delta" in action
    assert "comma_decisive_endpoint_packet" not in action
    actions = text.split("definition comma_semantic_b1_source_slot_actions", 1)[
        1
    ].split("lemma", 1)[0]
    assert "map (comma_semantic_b1_source_slot_action_width source)" in actions
    assert "comma_semantic_b1_source_slot_action_def[code del]" in text
    assert "comma_semantic_b1_source_slot_action_code[code]" in text
    equation = text.split("lemma comma_semantic_b1_source_slot_action_code", 1)[
        1
    ].split("proof", 1)[0]
    assert "if comma_round_admitted source" in equation
    assert "else comma_source_continuation_action_of_packet" in equation
