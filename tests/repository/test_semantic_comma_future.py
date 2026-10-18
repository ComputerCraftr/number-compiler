"""Keep semantic source/future proofs independent of eager concrete publishers."""

from devtools.checks.isabelle_registry import discover_sessions
from devtools.checks.isabelle_source_analysis import extract_isabelle_declarations
from devtools.checks.isabelle_syntax import (
    dynamic_cartouche_spans,
    executable_text,
    ml_cartouches,
    navigation_text,
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
        "Comma_Semantic_B1.Comma_Semantic_B1_Power",
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


def test_semantic_source_slot_does_not_materialize_an_action_row() -> None:
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1"
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
    for retired in (
        "comma_decisive_endpoint_round_refines_fast",
        "comma_fast_round_aux",
        "comma_fast_boundary_run",
    ):
        assert retired not in bridge


def test_semantic_future_checker_context_is_private_and_entry_open_scoped() -> None:
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Instance.thy"
    )
    source = path.read_text(encoding="utf-8")
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

    provider_cache = checker.split("val provider_check_theorem_cache =", 1)[1].split(
        "in {prove_table", 1
    )[0]
    assert "case !provider_check_theorem_cache" in provider_cache
    assert "SOME theorem => theorem" in provider_cache
    assert "construct_provider_check ()" in provider_cache


def test_semantic_b1_does_not_build_the_physical_row_audit() -> None:
    root = isabelle_root(repository_root())
    sessions = discover_sessions(root)
    closure = session_dependency_closure(sessions, ("Comma_Semantic_B1",))
    assert "Comma_Semantic_Graph_Instance" not in closure
    assert "Comma_Sparse_Core" not in closure
    for name in (
        "Comma_Semantic_B1_Columns",
        "Comma_Semantic_B1_Publication",
        "Comma_Semantic_B1_Table_Transform",
        "Comma_Semantic_B1_CRT_Source_Binding",
        "Comma_CRT_Columns",
        "Comma_CRT_Apply",
        "Comma_CRT_Power",
    ):
        text = (root / "families/comma/comma_semantic_b1" / f"{name}.thy").read_text(
            encoding="utf-8"
        )
        # Consolidating a generic refinement theorem is a proof checkpoint,
        # not construction of the retired physical-source certificate. Keep
        # the prohibition on the old physical-table inputs. Small constant
        # arithmetic checks do not construct physical-source row tables.
        executable = executable_text(text)
        assert "comma_semantic_graph_candidate" not in executable
        assert "comma_response_data_rows" not in executable
        assert "require_native_clean" in text


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


def test_candidate_publication_does_not_require_physical_row_certificates() -> None:
    root = isabelle_root(repository_root())
    candidate = (
        root
        / "families/comma/comma_semantic_b1_instance"
        / "semantic_b1_template_constructor.ML"
    ).read_text(encoding="utf-8")
    foundation = (
        root
        / "families/comma/comma_semantic_b1"
        / "Comma_Semantic_B1_Table_Transform.thy"
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
        root
        / "families/comma/comma_semantic_b1_instance"
        / "semantic_b1_occurrence_publication.ML"
    ).read_text(encoding="utf-8")
    # HOL serialization moved out of discovery so shared nodes survive until
    # publication; constructor identity and kernel checking remain unchanged.
    assert "@{const_name Comma_B1_CRT_Column_Block_Node}" in publisher
    assert "@{const_name Comma_B1_CRT_Column_DAG_Block}" in publisher
    assert "@{const_name Comma_B1_CRT_Column_DAG_Branch}" in publisher
    assert "Local_Theory.define" in publisher
    assert 'Binding.name "comma_semantic_b1_crt_column_definitions"' not in publisher
    assert "Local_Theory.background_theory_result" in publisher
    catalog = (
        root
        / "families/comma/comma_semantic_b1_instance"
        / "semantic_b1_column_catalog.ML"
    ).read_text(encoding="utf-8")
    assert "fun get_definitions ctxt" in publisher
    assert "define_global_definitions" in publisher
    assert "child < #cid parent" in catalog
    assert "#template_keys artifact" in publisher
    assert "HOLogic.mk_Collect" not in candidate
    assert not (
        root / "families/comma/comma_semantic_b1" / "semantic_b1_publication.ML"
    ).exists()


def test_root_instance_consumes_certified_occurrences_without_source_replay() -> None:
    root = isabelle_root(repository_root())
    path = (
        root
        / "families/comma/comma_semantic_b1_instance"
        / "Comma_Semantic_B1_Instance.thy"
    )
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
        / "families/comma/comma_semantic_b1_instance"
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
    root = (
        isabelle_root(repository_root()) / "families/comma/comma_semantic_b1_instance"
    )
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
    assert "list_all comma_semantic_b1_crt_construction_check" in shape
    assert "comma_semantic_b1_crt_occurrence_entry_checked" not in shape
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
    construction = declarations["comma_semantic_b1_crt_construction_check"].body
    assert "comma_semantic_b1_crt_compact_occurrence_check" in construction
    construction_at = declarations["comma_semantic_b1_crt_construction_check_at"].body
    assert "list_all comma_semantic_b1_crt_construction_check" in construction_at
    assert 'shows "comma_semantic_b1_crt_construction_check index"' in construction_at
    indexed_total = declarations["comma_semantic_b1_crt_occurrence_at_index_total"].body
    assert "comma_semantic_b1_crt_construction_check_at" in indexed_total
    assert "comma_semantic_b1_crt_compact_occurrence_check_total" in indexed_total
    assert "comma_semantic_b1_crt_constructed_occurrence_bound_def" not in indexed_total
    entry = declarations["comma_semantic_b1_crt_root_entry_checked"].body
    assert "distinct" not in entry
    binding = declarations[
        "comma_semantic_b1_crt_root_occurrence_distinct_binding"
    ].body
    assert "comma_semantic_b1_crt_root_entry_resolves_checked" in binding
    root_bridge = declarations["comma_semantic_b1_crt_root_entry_resolves_checked"].body
    assert 'checked: "comma_semantic_b1_crt_occurrence_data_checked"' in root_bridge
    assert "comma_semantic_b1_crt_construction_check_at" in root_bridge
    assert "comma_semantic_b1_crt_construction_check" not in entry
    assert "comma_semantic_b1_crt_compact_occurrence_check_exposes" in binding
    assert "comma_semantic_b1_crt_lift_local_cover_witness_def" in binding
    assert (
        'shows "distinct (comma_semantic_b1_crt_occurrence_beta occurrence)"' in binding
    )
    candidate_bridge = declarations[
        "comma_semantic_b1_crt_published_constructed_candidate_matches"
    ].body
    assert (
        "comma_semantic_b1_crt_compact_occurrences_candidate_matches"
        in candidate_bridge
    )
    exact = declarations["comma_semantic_b1_crt_published_exact"].body
    assert "comma_semantic_b1_crt_occurrence_map_exact" in exact
    assert (
        "comma_semantic_b1_crt_published_constructed_candidate_matches"
        in declarations["comma_semantic_b1_crt_published_lift_candidate"].body
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
        / "families/comma/comma_semantic_b1_instance"
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
        / "families/comma/comma_semantic_b1_instance"
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
    fixture_path = path.parent / "semantic_b1_publication_fixtures.ML"
    fixture = executable_text(fixture_path.read_text(encoding="utf-8"))
    assert "Publication.check_candidate_examples ()" in fixture
    fixture_call = "Comma_Semantic_B1_Publication_Fixtures.check_candidate"
    assert any(fixture_call in body for body in bodies)
    assert all("Template_Constructor.make" not in body for body in bodies)
    assert "Template_Constructor.make" not in fixture
    assert publication.index(fixture_call) < publication.index("local_setup")


def test_occurrence_fold_does_not_assume_a_child_physical_return_table() -> None:
    root = isabelle_root(repository_root()) / "families/comma/comma_semantic_b1"
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
    wellformed = declarations["comma_semantic_b1_crt_occurrence_wellformed"].body
    for contract in (
        "occurrence_rebase",
        "comma_crt_admitted",
        "comma_crt_supported",
        "comma_semantic_b1_crt_occurrence_disjoint",
        "comma_semantic_b1_crt_occurrence_covered",
    ):
        assert contract in wellformed
    for rejection in ("empty", "overlap", "missing_coverage", "bad_column"):
        assert (
            f"comma_semantic_b1_crt_occurrence_wellformed_rejects_{rejection}"
            in declarations
        )
    retired_checks = (
        "comma_semantic_b1_crt_occurrence_wellformed_check",
        "comma_semantic_b1_crt_occurrence_geometry_check",
        "comma_semantic_b1_crt_geometry_fold",
    )
    assert all(name not in declarations for name in retired_checks)
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
        / "families/comma/comma_semantic_b1"
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
    candidate_path = path.with_name("Comma_Semantic_B1_CRT_Local_Cover_Candidate.thy")
    candidate_declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            candidate_path.read_text(encoding="utf-8"), candidate_path
        )
    }
    assert (
        "comma_semantic_b1_crt_lift_local_cover_candidate_matches"
        in candidate_declarations
    )
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
    root = isabelle_root(repository_root()) / "families/comma/comma_semantic_b1"
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
    path = (
        root
        / "families/comma/comma_semantic_b1_instance"
        / "Comma_Semantic_Summary_Instance.thy"
    )
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
    sessions = discover_sessions(root)
    closure = session_dependency_closure(sessions, ("Comma_Semantic_B1_Instance",))
    assert "Comma_Semantic_Future" in closure
    assert not {
        "Comma_Sparse_Core",
        "Comma_Sparse_Base_Instance",
        "Comma_Sparse_Power_Instance",
        "Comma_Future_Rank_Data",
    }.intersection(closure)


def test_b32_instance_publishes_the_aggregate_range_certificate() -> None:
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1_instance"
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
        / "families/comma/comma_semantic_b1_instance"
        / "semantic_b1_crt_conversion.ML"
    ).read_text(encoding="utf-8")
    assert "comma_crt_mdd_stop_weights_bounded242" in source
    assert "comma_crt_split_weight" in source
    assert "comma_crt_eval" not in executable_text(source)
    projection = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1_instance"
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
