"""Semantic Comma certificate publication and memo authority invariants."""

import re

from devtools.checks.isabelle_source_analysis import extract_isabelle_declarations
from devtools.checks.isabelle_syntax import executable_text
from devtools.paths import isabelle_root, repository_root


def test_occurrence_certificate_waits_for_proof_and_preserves_memo_authority() -> None:
    """Keep exact cache authority independent of the retired geometry stage.

    This test retains theorem-shape, closed-RHS, partial-equation, and active
    request lifecycle checks. The constructed-induction and result/destination
    obligations replacing geometry staging are mapped in the next test; direct
    semantic wellformed-contract rejection lemmas remain in
    ``test_semantic_comma_future.py``.
    """
    root = (
        isabelle_root(repository_root()) / "families/comma/comma_semantic_b1_instance"
    )
    publication = (root / "Comma_Semantic_B1_Occurrence_Publication.thy").read_text(
        encoding="utf-8"
    )
    checker = (root / "semantic_b1_occurrence_check_cache.ML").read_text(
        encoding="utf-8"
    )
    selector = (
        isabelle_root(repository_root())
        / "families/comma/comma_entry_arithmetic/selected_list_conversion.ML"
    ).read_text(encoding="utf-8")
    shared = (root / "semantic_b1_crt_operation_conversion.ML").read_text(
        encoding="utf-8"
    )
    fixtures = (root / "semantic_b1_certificate_store_fixtures.ML").read_text(
        encoding="utf-8"
    )
    construction = (root / "semantic_b1_construction_check.ML").read_text(
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
        "val _ = Comma_Semantic_B1_Construction_Check.check_evaluator_smoke"
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
    assert "make_equation_checker_with_columns" in checker
    assert "ctxt (#known_column columns)" in checker
    assert "Term_LRU.remember_partial memo request" in publication_gate
    # The executable negative fixture moved to its canonical fixture owner;
    # require it to exercise the live publication and dispatch callbacks.
    assert "Certificate_Store_Fixtures.check_partial_equation_gate" in checker
    assert "publish_completed ctxt request theorem" in checker
    assert "dispatch = (fn cterm => memo_proc evaluation_context cterm)" in checker
    partial_fixture = fixtures.split("fun check_partial_equation_gate", 1)[1].split(
        "fun check_cofactor_state_warm_memo", 1
    )[0]
    assert "publish request (Thm.reflexive cterm)" in partial_fixture
    assert "publication_count () = before_publications" in partial_fixture
    assert "memo_size () = before_retained" in partial_fixture
    assert "val returned = dispatch cterm" in partial_fixture
    assert "not (memo_has request)" in partial_fixture
    assert "val _ = clear_incomplete request" in partial_fixture
    assert "Term_LRU.clear_partial memo request" in checker
    assert "crt_operation_base_patterns" in checker
    assert "crt_operation_base_heads" in checker
    assert "Comma_Entry_Arithmetic.natural_context ctxt" in checker
    assert "local_cover_context_ref" not in checker
    assert "comma_semantic_b1_crt_occurrence_entry_checked" not in checker
    assert "Construction_Check.prove_indexed_list_all" in checker
    assert "Comma_Selected_List_Conversion.prove_indexed_list_all" in construction
    assert "Thm.prop_of head_proof aconv expected_head" in selector
    assert "Thm.nprems_of head_proof = 0" in selector
    assert "null (Thm.hyps_of head_proof)" in selector
    assert "null (Thm.tpairs_of head_proof)" in selector
    assert "comma_crt_admitted lower column" in construction
    assert "Construction_Check.occurrence_cache_patterns" in checker
    # Constructed bounds and primitive CRT requests use the shared staged
    # converter; local copies previously drifted in HOL/meta-equation handling.
    assert "fun geometry_fold_conversion" not in checker
    assert "make_staged_operation_converter" in checker
    assert "reflect_boundaries boundaries" in shared
    assert "comma_crt_supported_node_short_circuit" in shared
    assert "rule RS @{thm eq_reflection}" in shared
    conversion = checker.split("fun convert context cterm =", 1)[1].split(
        "fun memo_proc context ct =", 1
    )[0]
    assert "Termtab.defined (!active) request" in conversion
    assert conversion.index("active := Termtab.update (request") < conversion.index(
        "val attempt = #capture_conversion template_partition_profile"
    )
    assert "active := Termtab.delete request (!active)" in conversion
    memo_proc = checker.split("fun memo_proc context ct =", 1)[1].split(
        "val proc =", 1
    )[0]
    assert "else if Termtab.defined (!active) request then" in memo_proc
    assert "recursive := !recursive + 1; NONE" in memo_proc


def test_compact_occurrence_gate_binds_source_lifts_and_induction() -> None:
    """Check the live compact occurrence contract and its exact proof bridge."""
    root = isabelle_root(repository_root())
    instance = root / "families/comma/comma_semantic_b1_instance"
    family = root / "families/comma/comma_semantic_b1"
    publication_path = instance / "Comma_Semantic_B1_Occurrence_Publication.thy"
    publication_source = publication_path.read_text(encoding="utf-8")
    publication = {
        item.name: item
        for item in extract_isabelle_declarations(publication_source, publication_path)
    }
    compact_path = family / "Comma_Semantic_B1_CRT_Compact_Refinement.thy"
    compact_source = compact_path.read_text(encoding="utf-8")
    compact = {
        item.name: item
        for item in extract_isabelle_declarations(compact_source, compact_path)
    }
    local_path = family / "Comma_Semantic_B1_CRT_Local_Cover.thy"
    local_source = local_path.read_text(encoding="utf-8")
    local = {
        item.name: item
        for item in extract_isabelle_declarations(local_source, local_path)
    }

    construction = publication["comma_semantic_b1_crt_construction_check"].body
    for required in (
        "comma_semantic_b1_crt_templates",
        "comma_semantic_b1_crt_sources",
        "comma_semantic_b1_crt_occurrence_at_index",
        "comma_semantic_b1_crt_descriptors",
        "comma_semantic_b1_crt_lift_refs",
        "comma_semantic_b1_crt_lift_descriptors",
    ):
        assert required in construction
    assert "comma_semantic_b1_crt_compact_occurrence_check" in construction
    checked = next(
        item.body
        for item in extract_isabelle_declarations(publication_source, publication_path)
        if item.name == "comma_semantic_b1_crt_occurrence_data_checked"
        and item.command == "definition"
    )
    assert "length comma_semantic_b1_crt_lift_refs =" in checked
    assert "list_all comma_semantic_b1_crt_construction_check" in checked
    assert "list_all (comma_semantic_b1_crt_template_mass_certified" in checked
    assert "comma_semantic_b1_crt_used_lift_bindings_checked" in checked
    geometry_bridge = publication[
        "comma_semantic_b1_crt_checked_bounds_and_geometry"
    ].body
    assert (
        "comma_semantic_b1_crt_compact_occurrences_wellformed_from_mass"
        in geometry_bridge
    )
    assert (
        "comma_semantic_b1_crt_template_geometry_from_resolved_wellformed_occurrence"
        in geometry_bridge
    )

    compact_check = compact["comma_semantic_b1_crt_compact_occurrence_check"].body
    for authority in (
        "comma_source_continuation_base source",
        "comma_round_admitted source",
        "comma_semantic_b1_crt_occurrence_rebase parent",
        "comma_semantic_b1_crt_occurrence_beta parent",
        "comma_semantic_b1_crt_occurrence_columns parent",
        "comma_semantic_b1_crt_lift_local_cover_witness",
        "child_index < index",
    ):
        assert authority in compact_check

    local_witness = local["comma_semantic_b1_crt_lift_local_cover_witness"].body
    local_slot = local["comma_semantic_b1_crt_lift_local_slot_valid"].body
    assert "map comma_semantic_b1_crt_lift_ref_slot refs = [0..<length refs]" in (
        local_witness
    )
    assert "list_all" in local_witness
    assert "zip lifted_columns child_beta" in local_slot
    assert "comma_semantic_b1_crt_local_piece_covered parent" in local_slot
    assert "comma_semantic_b1_crt_find_result_index_sound" in local
    assert "comma_semantic_b1_crt_lift_local_cover_rejects_truncated_refs" in local

    generic_bridge = compact[
        "comma_semantic_b1_crt_compact_occurrences_candidate_matches"
    ].body
    assert "comma_semantic_b1_crt_lift_local_cover_candidate_matches" in generic_bridge
    assert "referenced_children_wellformed" in generic_bridge
    assert "children_resolve" in generic_bridge
    concrete_bridge = publication[
        "comma_semantic_b1_crt_published_constructed_candidate_matches"
    ].body
    assert "comma_semantic_b1_crt_compact_occurrences_candidate_matches" in (
        concrete_bridge
    )
    assert "comma_semantic_b1_crt_published_children_resolve_index" in concrete_bridge
    assert "comma_semantic_b1_crt_checked_bounds_and_geometry" in concrete_bridge
    assert (
        "comma_semantic_b1_crt_root_occurrence_exact"
        in (publication_source.split("Thm_Deps.all_oracles", 1)[1])
    )

    root_binding = publication[
        "comma_semantic_b1_crt_root_occurrence_distinct_binding"
    ].body
    assert "comma_semantic_b1_crt_root_entry_resolves_checked" in root_binding
    root_bridge = publication["comma_semantic_b1_crt_root_entry_resolves_checked"].body
    assert 'checked: "comma_semantic_b1_crt_occurrence_data_checked"' in root_bridge
    assert "comma_semantic_b1_crt_construction_check_at" in root_bridge
    assert "comma_semantic_b1_crt_compact_occurrence_check_exposes" in root_binding
    assert "distinct (comma_semantic_b1_crt_occurrence_beta value)" in root_binding


def test_constructed_occurrence_regressions_are_kernel_audited() -> None:
    """Retain exact DAG fixtures and the generic compact coverage negatives."""
    root = isabelle_root(repository_root())
    instance = root / "families/comma/comma_semantic_b1_instance"
    publication = (instance / "Comma_Semantic_B1_Occurrence_Publication.thy").read_text(
        encoding="utf-8"
    )
    dag = (instance / "semantic_b1_crt_apply_dag.ML").read_text(encoding="utf-8")
    local_path = (
        root / "families/comma/comma_semantic_b1/Comma_Semantic_B1_CRT_Local_Cover.thy"
    )
    candidate_path = local_path.with_name(
        "Comma_Semantic_B1_CRT_Local_Cover_Candidate.thy"
    )
    local = {
        item.name: item
        for source_path in (local_path, candidate_path)
        for item in extract_isabelle_declarations(
            source_path.read_text(encoding="utf-8"), source_path
        )
    }

    assert (
        "#check_fixtures (Comma_Semantic_B1_CRT_Apply_DAG.make @{context} "
        "fixture_authority) ()" in " ".join(publication.split())
    )
    assert "known_column = K false" in publication
    fixture_dispatch = dag.split("fun check_fixtures () =", 1)[1].split(
        "in\n      {convert = convert", 1
    )[0]
    production_fixture = (
        instance / "semantic_b1_crt_apply_dag_production_fixture.ML"
    ).read_text(encoding="utf-8")
    assert (
        "Comma_Semantic_B1_CRT_Apply_DAG_Production_Fixture.check_owner_fixtures"
        in fixture_dispatch
    )
    fixture_body = production_fixture.split("fun check_owner_fixtures", 1)[1]
    for negative_or_authority_case in (
        "valid_theorem exact forged",
        "not (Option.isSome malformed)",
        "wrong_result_binding",
        "changed_shift",
        "changed_column",
        "wrong_parent_rebase",
        "wrong_child_net_shift",
    ):
        assert negative_or_authority_case in fixture_body
    assert "null (Thm_Deps.all_oracles [theorem])" in fixture_body
    assert "Comma_Semantic_B1_CRT_Apply_DAG_Production_Fixture.check" in dag
    for checked_case in (
        "warm_no_recursion = after_warm_recursive = after_recursive",
        "warm_hit = after_warm_hits > before_hits",
        "first_no_fallback = after_fallbacks = before_fallbacks",
        "first_no_rejection = after_rejections = before_rejections",
        "null (Thm_Deps.all_oracles [first])",
        "if all_checks",
    ):
        assert checked_case in production_fixture
    for name in (
        "comma_semantic_b1_crt_lift_local_cover_rejects_truncated_refs",
        "comma_semantic_b1_crt_lift_local_cover_candidate_matches",
    ):
        assert name in local
        assert (
            name
            in candidate_path.read_text(encoding="utf-8").split(
                "Thm_Deps.all_oracles @{thms", 1
            )[1]
        )


def test_static_code_preparation_excludes_generated_catalogue_constants() -> None:
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1_instance"
        / "semantic_b1_occurrence_check_cache.ML"
    )
    checker = path.read_text(encoding="utf-8")
    construction = path.with_name("semantic_b1_construction_check.ML").read_text()
    primitive_roots = construction.split("val occurrence_cache_generic_constants =", 1)[
        1
    ].split("val ", 1)[0]
    assert (
        "consts = filter_out (member (op =) operation_roots) "
        "Comma_Semantic_B1_Construction_Check.occurrence_cache_generic_constants"
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


def test_certificate_source_reset_clears_source_bindings_and_retains_lift_proofs() -> (
    None
):
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1_instance"
        / "semantic_b1_certificate_store.ML"
    )
    source = executable_text(path.read_text(encoding="utf-8"))
    reset = source.split("fun reset_current_source", 1)[1].split(
        "fun remember_equation", 1
    )[0]
    for table in (
        "slots",
        "slot_validity",
        "bindings",
    ):
        assert f"{table} := Termtab.empty" in reset
    for table in ("templates", "lifts", "lift_bindings"):
        assert f"{table} := Inttab.empty" not in reset


def test_b1_certificate_store_scopes_cid_proofs_and_consumes_action_rows() -> None:
    root = isabelle_root(repository_root()) / "families/comma"
    instance = root / "comma_semantic_b1_instance"
    store = executable_text((instance / "semantic_b1_certificate_store.ML").read_text())
    checker = executable_text(
        (instance / "semantic_b1_occurrence_check_cache.ML").read_text()
    )
    fixtures = executable_text(
        (instance / "semantic_b1_certificate_store_fixtures.ML").read_text()
    )
    slot_source = (
        root / "comma_semantic_b1/Comma_Semantic_B1_CRT_Slot_Certificates.thy"
    ).read_text(encoding="utf-8")
    construction = (
        root / "comma_semantic_b1/Comma_Semantic_B1_CRT_Occurrence_Bounds.thy"
    ).read_text(encoding="utf-8")
    publication = (
        root / "comma_semantic_b1_instance/Comma_Semantic_B1_Occurrence_Publication.thy"
    ).read_text(encoding="utf-8")
    assert "structure Comma_Semantic_B1_Certificate_Store" in store
    assert "store_generation = serial ()" in store
    assert "Context.eq_thy (Proof_Context.theory_of context, store_theory)" in store
    assert "Context.subthy (Thm.theory_of_thm theorem, store_theory)" in store
    assert "B1 certificate theorem comes from a non-ancestor theory" in store
    assert (
        "Isabelle_Thread.equal (store_owner_thread, Isabelle_Thread.self ())" in store
    )
    assert "B1 certificate store used outside its owning ML thread" in store
    assert "val template_capacity = 1024" in store
    assert "val lift_capacity = 1024 * 28" in store
    assert "val selected_equation_capacity = 8192" in store
    assert "selected_equations_reused=" in store
    assert "fun rewrite_lift_geometry ctxt context request cterm =" in store
    assert "make_lift_geometry_from_binding ctxt request" in store
    assert "fun selected_catalogue_equation context rules request =" in store
    assert "Simplifier.rewrite (context addsimps rules)" in store
    assert (
        "comma_semantic_b1_crt_lift_geometry_from_binding_and_template_geometry"
        in store
    )
    assert (
        "#rewrite_lift_binding certificate_store ctxt\n"
        "                          (require_operation_context ()) request cterm"
        in checker
    )
    assert "(memo_proc (require_operation_context ()))" in checker
    assert "List.all Comma_Selected_List_Conversion.closed catalog_terms" in store
    assert (
        "val templates = Unsynchronized.ref (Inttab.empty: thm Inttab.table)" in store
    )
    assert "val lifts = Unsynchronized.ref (Inttab.empty: thm Inttab.table)" in store
    assert (
        "val bindings = Unsynchronized.ref (Termtab.empty: thm Termtab.table)" in store
    )
    assert "if not (exact_prefix args authority) then NONE" in store
    assert "Thm.term_of (Thm.lhs_of theorem) aconv request" in store
    assert "standalone theorem andalso" in store
    assert "certify_equations false [theorem]" in store
    assert "Comma_Entry_Arithmetic.make_certifier ctxt" in store
    assert "List.app (ignore o certify_equation) theorems" in store
    assert "Thm_Deps.all_oracles theorems" not in store
    assert "val result = Exn.capture" in store
    assert "Exn.release result" in store
    assert "selected_equation_oracle_elapsed_ms=" in store
    assert "captured_equation_oracle_elapsed_ms=" in store
    assert (
        'action_table = @{term "comma_semantic_b1_crt_slot_actions_table comma_semantic_b1_crt_sources"}'
        in store
    )
    for parameter, head in (
        ("action_row_head", "comma_semantic_b1_crt_source_slot_action_row_certified"),
        (
            "slot_valid_actions_head",
            "comma_semantic_b1_crt_lift_slot_valid_from_actions",
        ),
        (
            "binding_actions_head",
            "comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions",
        ),
    ):
        assert f"root_args {parameter} request" in store
        assert f"{parameter} = @{{const_name {head}}}" in store
    assert "lift_binding_proofs_reused=" in store
    assert "lift_binding_cold_evaluations=" in store
    assert "binding_counts_before_warm = (1, 0)" in fixtures
    assert "binding_counts_after_warm = (1, 1)" in fixtures
    assert "forged_columns" in fixtures and "forged_root_rejected" in fixtures
    assert "foreign_theorem_has_descendant_provenance" in fixtures
    assert "foreign_theorem_is_exact_kernel_equation" in fixtures
    assert "foreign_theorem_rejected" in fixtures
    assert "off_thread_rejected" in fixtures
    assert "ignored_generic_skips_oracle_scan" in fixtures
    assert "source_action_rhs aconv expected_source_action" in fixtures
    assert '("action_head_fixtures_pass", action_head_fixtures_pass)' in fixtures
    assert "filter (not o #2) fixture_checks" in fixtures
    assert "if null failed_fixture_checks then ()" in fixtures
    assert 'else error ("B1 exact certificate-store fixture failed: "' in fixtures
    action_fixtures = executable_text(
        (instance / "semantic_b1_certificate_store_action_fixtures.ML").read_text()
    )
    for check in (
        "canonical_row_warm",
        "canonical_slot_warm",
        "binding_warm",
        "changed_action_rejected",
        "changed_parent_rejected",
        "changed_catalog_rejected",
        "changed_source_rejected",
    ):
        assert check in action_fixtures
    assert 'ML_file "semantic_b1_certificate_store_action_fixtures.ML"' in publication
    assert (
        "Context.proper_subthy (thy, Thm.theory_of_thm foreign_template_eq)" in fixtures
    )
    assert (
        "comma_semantic_b1_crt_lift_columns_option"
        not in slot_source.split(
            "definition comma_semantic_b1_crt_constructed_goto_slot_certificate", 1
        )[1].split(
            "definition comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions",
            1,
        )[0]
    )
    bound = construction.split(
        "definition comma_semantic_b1_crt_constructed_occurrence_bound", 1
    )[1].split(
        "lemma comma_semantic_b1_crt_constructed_occurrence_bound_index_guards", 1
    )[0]
    assert "slot_actions" in bound
    assert "comma_semantic_b1_crt_lift_slot_valid_from_actions" in bound
    assert (
        "comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions" in bound
    )
    assert "comma_semantic_b1_crt_lift_geometry_certified" not in bound
    requests = executable_text(
        (instance / "semantic_b1_construction_check.ML").read_text()
    )
    assert r"length comma_semantic_b1_crt_sources \<le> 1024" in requests
    assert r"length comma_semantic_b1_crt_templates \<le> 1024" in requests
    assert "Construction_Check.occurrence_cache_catalogue_patterns" in checker
    assert "selected_period_value context selected_source" in store
    assert "slot < period" in store
    assert 'ML_file "semantic_b1_certificate_store.ML"' in publication
    assert (
        publication.index('ML_file "semantic_b1_construction_check.ML"')
        < publication.index('ML_file "semantic_b1_certificate_store.ML"')
        < publication.index('ML_file "semantic_b1_certificate_store_fixtures.ML"')
    )


def test_occurrence_certificate_assembles_indexed_facts_without_catalogue_rewrite() -> (
    None
):
    root = (
        isabelle_root(repository_root()) / "families/comma/comma_semantic_b1_instance"
    )
    checker = (root / "semantic_b1_occurrence_check_cache.ML").read_text(
        encoding="utf-8"
    )
    construction = (root / "semantic_b1_construction_check.ML").read_text()
    indexed = construction.split("fun prove_indexed_list_all", 1)[1].split(
        "fun check_helper_fixtures", 1
    )[0]
    assert "Construction_Check.prove_indexed_list_all" in checker
    assert "successor_equation = #equation indexed_successors" in checker
    assert (
        "prove_beta_item ctxt prove_selected "
        "(predicate $ Comma_Semantic_B1_CRT_Operation_Conversion.natural_numeral index)"
        in " ".join(indexed.split())
    )
    assert "Comma_Selected_List_Conversion.prove_indexed_list_all" in indexed
    assert "indexed_extent_contract predicate upper" in " ".join(indexed.split())
    assert "val _ = check_indexed_extent_regressions ()" in construction
    assert "not (indexed_extent_admitted 1025 unrelated_extent)" in construction
    assert "not (indexed_extent_admitted 1025 forged_extent)" in construction
    assert "maximum_lift_catalog_extent = 28 * maximum_source_extent" in construction
    shared = (
        isabelle_root(repository_root())
        / "families/comma/comma_entry_arithmetic/selected_list_conversion.ML"
    ).read_text(encoding="utf-8")
    recurrence = shared.split("fun prove_indexed_list_all", 1)[1].split(
        "fun literal_nested_extents", 1
    )[0]
    assert "comma_indexed_all_Suc" in indexed
    assert "comma_indexed_all_zero" in indexed
    arithmetic = (
        isabelle_root(repository_root())
        / "families/comma/comma_entry_arithmetic/Comma_Entry_Arithmetic.thy"
    )
    arithmetic_declarations = {
        item.name
        for item in extract_isabelle_declarations(
            arithmetic.read_text(encoding="utf-8"), arithmetic
        )
    }
    assert {
        "comma_indexed_all_zero",
        "comma_indexed_all_Suc",
        "comma_selected_length_nil",
        "comma_selected_length_cons",
    } <= arithmetic_declarations
    endpoint_path = (
        isabelle_root(repository_root())
        / "families/comma/comma_decade_orbit/Comma_Decade_Orbit_Quotient.thy"
    )
    endpoint = executable_text(endpoint_path.read_text(encoding="utf-8"))
    # Uniform orbit induction replaces 91 x 22 separately evaluated cells;
    # the public bounded proposition and oracle closure remain required.
    assert "[0..<22]) [0..<91]" in endpoint
    assert "comma_offset_endpoint_representative" in endpoint
    assert "lemma comma_offset_endpoint_checked" in endpoint
    assert "comma_offset_endpoint_check_def" in endpoint
    assert (
        "comma_offset_endpoint_checked" in endpoint.split("Thm_Deps.all_oracles", 1)[1]
    )
    assert not (endpoint_path.parent / "endpoint_check.ML").exists()
    assert 'ML_file "endpoint_check.ML"' not in endpoint
    for caller_path in (
        root / "Comma_Semantic_B1_Occurrence_Publication.thy",
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_future_instance"
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
    nested_extents = shared.split("fun literal_nested_extents", 1)[1].split(
        "fun make_with_extents", 1
    )[0]
    terminal_dimension = nested_extents.split("if remaining = 1 then", 1)[1].split(
        "else", 1
    )[0]
    assert "literal_list_length table" in terminal_dimension
    assert "map literal_list" not in terminal_dimension
    assert "maps I lists" in nested_extents
    assert "HOLogic.dest_list" not in indexed
    assert "upt_rec" not in indexed
    assert "Simplifier.full_rewrite" not in checker
    assert "comma_semantic_b1_crt_source_index_for" not in checker
    assert "comma_semantic_b1_crt_published" not in checker
    dispatch = checker.split("fun prove_expression small_upt context expression =", 1)[
        1
    ].split("val _ = construction_handler :=", 1)[0]
    assert "HOLogic.dest_bin" in dispatch
    assert "HOLogic.dest_conj" not in dispatch
    assert 'predicate aconv @{term "comma_crt_admitted (0::nat)"}' in dispatch
    assert "range aconv @{term comma_semantic_b1_crt_columns}" in dispatch
    assert "val prove_table_admission = #prove_all_columns_admitted columns" in checker
    assert "then prove_table_admission ()" in dispatch
    assert "head_name range = SOME @{const_name upt}" in dispatch
    assert "Construction_Check.prove_indexed_list_all" in dispatch
    assert "prove_selected = prove_expression small_upt context" in dispatch
    assert "else prove_true_using small_upt context expression" in dispatch
    selector = (
        isabelle_root(repository_root())
        / "families/comma/comma_entry_arithmetic/selected_list_conversion.ML"
    ).read_text(encoding="utf-8")
    assert "suffix_memo" in selector
    assert "_spine_node_visits=" in selector
    assert "_selected_cells=" in selector
    assert "_list_node_visits=" not in selector


def test_selected_list_checks_each_nested_extent_before_cache_access() -> None:
    """Keep foreign parent/slot indices outside the selector's memo extent."""
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_entry_arithmetic/selected_list_conversion.ML"
    )
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
    lookup = body.split("fun lookup index_context cterm =", 1)[1].split(
        "and nth index_context cterm index_conversion =", 1
    )[0]
    lookup = re.sub(r"\s+", " ", lookup)
    assert lookup.index("case in_extent index_context cterm") < lookup.index(
        "Termtab.lookup (!memo) key"
    )
    assert "Conv.arg_conv (lookup index_context)" in lookup
    assert "nth index_context (Thm.rhs_of prepared) index_conversion" in lookup
    assert "extent_at extents depth" in body
    assert "Simplifier.rewrite index_context (Thm.rhs_of overloaded)" in body
    assert "proc = fn _ => fn index_context => convert index_context" in body
    assert "fun make_nested" in body
    assert "literal_nested_extents depth root_body" in body
    conversion = body.split("fun convert index_context cterm =", 1)[1].split(
        "val pattern", 1
    )[0]
    assert re.search(
        r"if owned_selector cterm then\s+"
        r"SOME \(timed elapsed failures \(lookup index_context\) cterm\)",
        conversion,
    )
    assert "else if in_extent cterm then" not in conversion
    length_lookup = body.split("fun lookup_length definition cterm =", 1)[1].split(
        "fun lookup_concat definition cterm =", 1
    )[0]
    assert "list_size_spine (Thm.rhs_of selected)" in length_lookup
    assert "Simplifier.rewrite" not in length_lookup
    assert "make_named_children" in body
    assert "child_extent_table table" in body
    assert "index < extent" in body
    publication = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1_instance"
        / "Comma_Semantic_B1_Occurrence_Publication.thy"
    ).read_text(encoding="utf-8")
    fixtures = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1_instance"
        / "semantic_b1_publication_fixtures.ML"
    ).read_text(encoding="utf-8")
    assert 'ML_file "semantic_b1_publication_fixtures.ML"' in publication
    assert (
        "Comma_Semantic_B1_Publication_Fixtures.check_selected_list @{context}"
        in publication
    )
    assert "nested_extent_regression" in fixtures
    assert 'slot"} [2, 3]' in fixtures
    assert "Exn.capture nested_select" in fixtures
    assert "selected_suffix_index_two" in fixtures
    assert "selected_suffix_index_three" in fixtures


def test_occurrence_evaluator_is_created_only_for_a_validated_subgoal() -> None:
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1_instance"
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
    path = (
        root
        / "families/comma/comma_semantic_b1"
        / "Comma_Semantic_B1_Table_Transform.thy"
    )
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


def test_beta_item_fixture_is_in_the_kernel_path() -> None:
    root = (
        isabelle_root(repository_root()) / "families/comma/comma_semantic_b1_instance"
    )
    helper = executable_text((root / "semantic_b1_construction_check.ML").read_text())
    publication = executable_text(
        (root / "Comma_Semantic_B1_Occurrence_Publication.thy").read_text()
    )
    assert "Comma_Semantic_B1_Construction_Check.check_helper_fixtures" in publication
    assert "Thm.prop_of body_proof aconv expected" in helper
    assert "Thm.equal_elim (Thm.symmetric proposition_eq) body_proof" in helper
    assert "standalone body_proof" in helper
    assert "B1 beta item prover accepted a theorem for another item" in helper
    assert "val wrong_callback = Exn.capture" in helper
    assert "prove_beta_item_with_body" in helper
