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
    assert "Comma_Selected_List_Conversion.prove_indexed_list_all" in checker
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


def test_constructed_occurrence_gate_binds_induction_and_piece_authority() -> None:
    """Map the replacement gate to its generic construction and refinement laws.

    The publisher checks global CID admission and each constructed occurrence;
    the generic all-index theorem supplies the decreasing-child induction.
    Local-cover checks still bind branch refs, while group and piece laws bind
    shared CRT nodes, parent result rows, and each piece's destination. Semantic
    wellformed rejection fixtures remain asserted by
    ``test_semantic_comma_future.py``.
    """
    root = isabelle_root(repository_root())
    # The retired fused-fold implementation had no publication consumer.
    # It must not silently return to the critical release session.
    assert "Comma_CRT_Composition_Fold" not in (root / "families/comma/ROOT").read_text(
        encoding="utf-8"
    )
    assert not (
        root / "families/comma/comma_semantic_b1/Comma_CRT_Composition_Fold.thy"
    ).exists()
    instance = root / "families/comma/comma_semantic_b1_instance"
    publication_path = instance / "Comma_Semantic_B1_Occurrence_Publication.thy"
    publication_source = publication_path.read_text(encoding="utf-8")
    publication_declarations = extract_isabelle_declarations(
        publication_source, publication_path
    )
    publication = {item.name: item for item in publication_declarations}
    constructed_path = (
        root
        / "families/comma/comma_semantic_b1"
        / "Comma_Semantic_B1_CRT_Constructed_Occurrence.thy"
    )
    constructed_source = constructed_path.read_text(encoding="utf-8")
    constructed = {
        item.name: item
        for item in extract_isabelle_declarations(constructed_source, constructed_path)
    }
    bounds_path = constructed_path.with_name(
        "Comma_Semantic_B1_CRT_Occurrence_Bounds.thy"
    )
    bounds = {
        item.name: item
        for item in extract_isabelle_declarations(bounds_path.read_text(), bounds_path)
    }
    slot_path = constructed_path.with_name(
        "Comma_Semantic_B1_CRT_Slot_Certificates.thy"
    )
    slot_certificates = {
        item.name: item
        for item in extract_isabelle_declarations(slot_path.read_text(), slot_path)
    }
    binding_path = (
        root
        / "families/comma/comma_semantic_b1"
        / "Comma_Semantic_B1_CRT_Construction_Binding.thy"
    )
    binding_source = binding_path.read_text(encoding="utf-8")
    binding = {
        item.name: item
        for item in extract_isabelle_declarations(binding_source, binding_path)
    }

    certificate = next(
        item.body
        for item in publication_declarations
        if item.name == "comma_semantic_b1_crt_occurrence_data_checked"
        and item.command == "definition"
    )
    for malformed_case in ("out_of_range_index", "missing_occurrence"):
        assert (
            "comma_semantic_b1_crt_constructed_bound_rejects_" + malformed_case
            in publication
        )
    construction_check = publication["comma_semantic_b1_crt_construction_check"].body
    assert "Comma_Semantic_B1_CRT_Constructed_Occurrence" in publication_source
    assert (
        "list_all (comma_crt_admitted 0) comma_semantic_b1_crt_columns" in certificate
    )
    column_dag_path = (
        root
        / "families/comma/comma_semantic_b1"
        / "Comma_Semantic_B1_CRT_Column_DAG.thy"
    )
    column_dag = column_dag_path.read_text(encoding="utf-8")
    assert "comma_semantic_b1_crt_columns_for dag extent" in column_dag
    assert "map (comma_semantic_b1_crt_column_at dag) [0..<extent]" in column_dag
    assert "comma_semantic_b1_crt_columns_for_length" in column_dag
    assert "list_all comma_semantic_b1_crt_construction_check" in certificate
    assert "comma_semantic_b1_crt_constructed_occurrence_bound" in construction_check
    for published_input in (
        "comma_semantic_b1_crt_columns",
        "comma_semantic_b1_crt_templates",
        "comma_semantic_b1_crt_template_column_ids",
        "comma_semantic_b1_crt_lift_column_ids",
        "comma_semantic_b1_crt_sources",
        "comma_semantic_b1_crt_occurrence_at_index",
        "comma_semantic_b1_crt_descriptors",
        "comma_semantic_b1_crt_lift_refs",
        "comma_semantic_b1_crt_lift_descriptors",
        "comma_semantic_b1_crt_construction_piece_refs",
    ):
        assert published_input in construction_check
    assert "comma_semantic_b1_crt_grouped_union_start_ids" not in publication_source
    assert "comma_semantic_b1_crt_grouped_union_steps" not in publication_source
    assert "comma_semantic_b1_crt_template_geometry_at" not in publication_source
    constructed_bound = bounds[
        "comma_semantic_b1_crt_constructed_occurrence_bound"
    ].body
    all_index = constructed[
        "comma_semantic_b1_crt_constructed_occurrences_wellformed"
    ].body
    assert "comma_semantic_b1_crt_constructed_goto_slot_certificate" in (
        constructed_bound
    )
    assert (
        "child_index<index"
        in slot_certificates[
            "comma_semantic_b1_crt_constructed_goto_slot_certificate"
        ].body
    )
    assert "child_index<index" in all_index
    assert "comma_semantic_b1_crt_source_order_induction[OF step]" in all_index
    piece_bridge_statement = slot_certificates[
        "comma_semantic_b1_crt_constructed_piece_matches_from_certificates"
    ].body.split("proof", 1)[0]
    # Each premise must certify the piece's slot. An unrelated implicit slot
    # can certify a Terminal ref while the piece uses a different Goto ref.
    piece_slot = "(fst (comma_semantic_b1_crt_constructed_piece_origin piece))"
    assert piece_bridge_statement.count(piece_slot) == 2
    child_bounds = slot_certificates[
        "comma_semantic_b1_crt_goto_slot_certificate_child_bounds"
    ].body
    assert "refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid" in child_bounds
    assert "child_index<length occurrence_descriptors" in child_bounds
    assert "goto_at" not in constructed_source
    publication_wf = publication[
        "comma_semantic_b1_crt_published_occurrences_wellformed"
    ].body
    assert "comma_semantic_b1_crt_checked_bounds_and_geometry" in publication_wf
    geometry_bridge = publication[
        "comma_semantic_b1_crt_checked_bounds_and_geometry"
    ].body
    assert "all_occurrences_wellformed" in geometry_bridge
    assert (
        "comma_semantic_b1_crt_constructed_occurrences_catalog_geometry_from_mass"
        in geometry_bridge
    )

    # Constructed occurrence bounds and the child resolver now provide the
    # concrete all-index candidate bridge; lower-level local-cover lemmas stay
    # separately covered as semantic regression material.
    assert "comma_semantic_b1_crt_occurrence_entry_checked" not in publication
    assert "comma_semantic_b1_crt_published_local_cover_witness" not in publication
    occurrence_index = publication[
        "comma_semantic_b1_crt_published_occurrence_index"
    ].body
    assert "List.find" in occurrence_index
    assert "comma_semantic_b1_crt_sources!index=source" in occurrence_index
    candidate_bridge = publication[
        "comma_semantic_b1_crt_published_constructed_candidate_matches"
    ].body
    assert (
        "comma_semantic_b1_crt_constructed_occurrences_candidate_matches"
        in candidate_bridge
    )
    assert "comma_semantic_b1_crt_published_children_resolve_index" in candidate_bridge
    assert "comma_semantic_b1_crt_lift_local_cover_witness" not in candidate_bridge
    assert "comma_semantic_b1_crt_checked_bounds_and_geometry" in candidate_bridge
    assert (
        "[OF table_admitted bounds parent_template_geometries used_lift_geometries"
        in candidate_bridge
    )
    checked_geometry = publication[
        "comma_semantic_b1_crt_checked_bounds_and_geometry"
    ].body
    assert (
        "comma_semantic_b1_crt_constructed_occurrences_catalog_geometry_from_mass"
        in checked_geometry
    )
    assert (
        "[OF table_admitted bounds_fact parent_masses used_lift_bindings]"
        in checked_geometry
    )
    assert (
        "simp add: comma_semantic_b1_crt_occurrence_data_checked_def\n"
        "      comma_semantic_b1_crt_construction_check_def" not in candidate_bridge
    )
    indexed_total = publication["comma_semantic_b1_crt_occurrence_at_index_total"].body
    assert (
        "comma_semantic_b1_crt_constructed_occurrence_bound_parent_present"
        in indexed_total
    )
    assert "comma_semantic_b1_crt_constructed_occurrence_bound_def" not in indexed_total
    parent_present = bounds[
        "comma_semantic_b1_crt_constructed_occurrence_bound_parent_present"
    ].body
    assert "comma_semantic_b1_crt_constructed_occurrence_bound_index_guards" in (
        parent_present
    )
    index_guards = bounds[
        "comma_semantic_b1_crt_constructed_occurrence_bound_index_guards"
    ].body
    for guarded_table in (
        "sources",
        "occurrence_descriptors",
        "lift_refs",
        "piece_refs",
    ):
        assert f"index<length {guarded_table}" in index_guards
    root_binding = publication[
        "comma_semantic_b1_crt_root_occurrence_distinct_binding"
    ].body
    assert "comma_semantic_b1_crt_construction_check_at" in root_binding
    assert "comma_semantic_b1_crt_constructed_occurrence_bound" in root_binding
    assert "comma_semantic_b1_crt_constructed_occurrence_bound_beta_distinct" in (
        root_binding
    )
    assert "comma_semantic_b1_crt_occurrence_wellformed" not in root_binding
    local_path = (
        root
        / "families/comma/comma_semantic_b1"
        / "Comma_Semantic_B1_CRT_Local_Cover.thy"
    )
    local_source = local_path.read_text(encoding="utf-8")
    local_cover = {
        item.name: item
        for item in extract_isabelle_declarations(local_source, local_path)
    }
    slot_valid = local_cover["comma_semantic_b1_crt_lift_local_slot_valid"].body
    witness = local_cover["comma_semantic_b1_crt_lift_local_cover_witness"].body
    assert "length lifted_columns = length child_beta" in slot_valid
    assert "list_all" in slot_valid and "zip lifted_columns child_beta" in slot_valid
    assert "map comma_semantic_b1_crt_lift_ref_slot refs = [0..<length refs]" in witness
    assert "comma_semantic_b1_crt_find_result_index_sound" in local_cover

    # Local result-directed inclusion replaces parent OR reconstruction only
    # with an independently certified template partition. Neither refs alone
    # nor a different published parent may satisfy this gate.
    group_bound = binding["comma_semantic_b1_crt_group_construction_bound"].body
    assert "comma_crt_supported" in group_bound
    assert "comma_semantic_b1_crt_piece_parent_column piece=parent_index" in group_bound
    assert "pieces\\<noteq>[]" in group_bound
    assert "comma_semantic_b1_crt_group_piece_fold" not in group_bound
    assert "comma_crt_negate" in group_bound and "comma_crt_apply" in group_bound
    assert "comma_crt_shift rebase" in " ".join(group_bound.split())
    geometry = slot_certificates[
        "comma_semantic_b1_crt_template_geometry_certified"
    ].body
    assert "comma_semantic_b1_crt_columns_partition_certified" in geometry
    assert "comma_semantic_b1_crt_template_geometry_certified_partition" in (
        constructed_source
    )
    assert (
        "comma_crt_set (columns!parent_cid)"
        in binding["comma_semantic_b1_crt_group_construction_bound_sound"].body
    )
    assert "comma_semantic_b1_crt_or_chain_valid" not in group_bound
    assert "comma_semantic_b1_crt_or_chain_final" not in group_bound
    assert "comma_semantic_b1_crt_group_construction_bound_sound" in (
        constructed_source
    )
    assert "comma_semantic_b1_crt_constructed_bound_source_partition" in (
        constructed_source
    )
    assert "comma_semantic_b1_crt_constructed_bound_source_partition" in (
        slot_certificates
    )
    assert "comma_semantic_b1_crt_constructed_bound_source_partition" not in (
        constructed
    )
    piece_matches = slot_certificates[
        "comma_semantic_b1_crt_constructed_piece_matches"
    ].body
    assert (
        "sort (map comma_semantic_b1_crt_constructed_piece_origin" in constructed_bound
    )
    assert "distinct origins" not in constructed_bound
    source_origins_distinct = constructed[
        "comma_semantic_b1_crt_constructed_source_origins_distinct"
    ].body
    assert "comma_semantic_b1_crt_distinct_concat_tagged_rows" in (
        source_origins_distinct
    )
    legacy_wellformed = constructed[
        "comma_semantic_b1_crt_constructed_occurrence_wellformed"
    ].body
    assert "comma_semantic_b1_crt_constructed_occurrence_from_partition_or_mass" in (
        legacy_wellformed
    )
    # Both callers use one source-partition and result-coverage proof. The mass
    # alternative must still establish a parent partition; it is not refs-only.
    occurrence_wellformed = constructed[
        "comma_semantic_b1_crt_constructed_occurrence_from_partition_or_mass"
    ].body
    assert "parent_partition_or_mass" in occurrence_wellformed
    assert "comma_semantic_b1_crt_parent_columns_partition_from_grouped_cover" in (
        occurrence_wellformed
    )
    assert "comma_semantic_b1_crt_constructed_source_origins_distinct" in (
        occurrence_wellformed
    )
    assert "= origins" in constructed_bound
    assert "list_all (comma_semantic_b1_crt_constructed_piece_binding_matches" in (
        constructed_bound
    )
    assert "comma_semantic_b1_crt_constructed_piece_matches_list_from_certificates" in (
        occurrence_wellformed
    )
    binding_check = slot_certificates[
        "comma_semantic_b1_crt_constructed_piece_binding_matches"
    ].body
    assert "comma_semantic_b1_crt_constructed_piece_matches" not in binding_check
    assert "comma_semantic_b1_source_slot_action" not in binding_check
    terminal_binding = binding_check.split("| Comma_B1_Piece_Goto", 1)[0]
    assert "Comma_B1_Lift_Terminal_Ref slot destination" in terminal_binding
    assert "columns!cid=comma_crt_source_scope_column (period,slot)" in terminal_binding
    goto_binding = binding_check.split("| Comma_B1_Piece_Goto", 1)[1]
    assert "comma_semantic_b1_source_slot_action" not in goto_binding
    assert "comma_semantic_b1_crt_lift_columns_option" not in goto_binding
    assert "beta!destination=" in goto_binding
    assert "parent_column=destination" in piece_matches
    assert "beta!destination=result" in piece_matches
    assert "sources!child_index=comma_source_continuation_base child" in piece_matches
    assert "comma_semantic_b1_crt_occurrence_beta child_occurrence" in piece_matches
    mismatched_lift_shape = publication[
        "comma_semantic_b1_crt_piece_matches_rejects_mismatched_lift_shape"
    ].body
    assert "mismatched_shape" in mismatched_lift_shape
    assert "length (lift_column_ids!lift_cid)" in mismatched_lift_shape
    assert "comma_semantic_b1_crt_occurrence_beta child_occurrence" in (
        mismatched_lift_shape
    )


def test_constructed_occurrence_regressions_are_kernel_audited() -> None:
    """Keep concrete negative witnesses for row-fold and piece bindings.

    These small HOL fixtures reject a wrong parent column, rebase, destination,
    foreign CID, malformed column, missing/duplicated origin, wrong terminal
    result, and wrong Goto source. The companion generic theory proves the
    positive construction laws; these witnesses make the exact guards
    reviewable without asking an evaluation oracle to certify them.
    """
    theory_path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1"
        / "Comma_Semantic_B1_CRT_Construction_Regression.thy"
    )
    source = theory_path.read_text(encoding="utf-8")
    declarations = {
        item.name: item for item in extract_isabelle_declarations(source, theory_path)
    }
    assert "imports Comma_Semantic_B1_CRT_Constructed_Occurrence" in source
    fixtures = (
        "comma_semantic_b1_crt_fixture_swapped_parent_wellformed",
        "comma_semantic_b1_crt_fixture_swapped_parent_partition",
        "comma_semantic_b1_crt_fixture_swapped_parent_beta_distinct",
        "comma_semantic_b1_crt_fixture_swapped_parent_phase_one_lookup",
        "comma_semantic_b1_crt_fixture_rejects_swapped_parent_label",
        "comma_semantic_b1_crt_group_fold_fixture_valid",
        "comma_semantic_b1_crt_group_fold_rejects_wrong_parent",
        "comma_semantic_b1_crt_group_fold_rejects_wrong_rebase",
        "comma_semantic_b1_crt_group_fold_rejects_wrong_piece_destination",
        "comma_semantic_b1_crt_group_fold_rejects_foreign_cid",
        "comma_semantic_b1_crt_malformed_column_rejected_by_admission",
        "comma_semantic_b1_crt_constructed_occurrence_bound_rejects_piece_omission",
        "comma_semantic_b1_crt_constructed_occurrence_bound_rejects_piece_multiplicity",
        "comma_semantic_b1_crt_piece_matches_rejects_wrong_terminal_result",
        "comma_semantic_b1_crt_piece_matches_rejects_wrong_goto_source",
    )
    assert all(name in declarations for name in fixtures)
    for name in fixtures:
        assert declarations[name].command == "lemma"
    for name in fixtures[-4:-2]:
        assert "assumes" not in declarations[name].body
        assert "Comma_Near 9 0 19" in declarations[name].body
    assert "by eval" not in source
    assert "Thm_Deps.all_oracles @{thms" in source
    for name in fixtures:
        assert name in source.split("Thm_Deps.all_oracles @{thms", 1)[1]


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
    assert "comma_semantic_b1_crt_constructed_piece_matches" not in checker
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


def test_certificate_source_reset_clears_unconsumed_contexts() -> None:
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
        "pending_template_context",
    ):
        assert f"{table} := Termtab.empty" in reset


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
    assert "Simplifier.rewrite (context addsimps [theorem]) cterm" in store
    assert "fun lift_context" not in store
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
    assert "pending_template_context" in store
    assert (
        "template_context_lookups=" in store
        and "template_context_requests_completed=" in store
    )
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
    indexed = checker.split(
        "fun prove_list_all prove_selected context predicate range =", 1
    )[1].split("fun prove_expression", 1)[0]
    assert (
        "Comma_Semantic_B1_Construction_Check.prove_beta_item ctxt prove_selected "
        "(predicate $ Comma_Semantic_B1_CRT_Operation_Conversion.natural_numeral index)"
        in " ".join(indexed.split())
    )
    assert "Comma_Selected_List_Conversion.prove_indexed_list_all" in indexed
    assert "Construction_Check.indexed_extent_contract predicate upper" in " ".join(
        indexed.split()
    )
    construction = (root / "semantic_b1_construction_check.ML").read_text()
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
    ].split("val definition", 1)[0]
    assert "HOLogic.dest_bin" in dispatch
    assert "HOLogic.dest_conj" not in dispatch
    assert 'predicate aconv @{term "comma_crt_admitted (0::nat)"}' in dispatch
    assert "range aconv @{term comma_semantic_b1_crt_columns}" in dispatch
    assert "val prove_table_admission = #prove_all_columns_admitted columns" in checker
    assert "then prove_table_admission ()" in dispatch
    assert "head_name range = SOME @{const_name upt}" in dispatch
    assert "prove_list_all (prove_expression small_upt context)" in dispatch
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


def test_origin_sort_and_beta_item_fixtures_are_in_the_kernel_path() -> None:
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
    assert "B1 origin quicksort fixture lost order or multiplicity" in helper
    assert "B1 origin literal-spine admission failed" in helper
    assert "B1 origin quicksort eagerly accepted a symbolic list" in helper
    literal_guard = helper.split("fun literal_origins", 1)[1].split(
        "fun identity_key", 1
    )[0]
    assert "remaining > 0" in literal_guard
    assert "spine (remaining - 1) tail" in literal_guard
    assert "HOLogic.dest_list" not in literal_guard
    conversion = helper.split("fun make_origin_sort_proc", 1)[1].split(
        "fun check_helper_fixtures", 1
    )[0]
    assert "not (literal_origins values)" in conversion
    assert "Conv.rewr_conv quicksort_rule cterm" in conversion
    assert "validate_equation" in conversion
    assert "list.case_cong_weak" in conversion
    assert "old.prod.case_cong_weak" in conversion
    assert "delsimps @{thms case_prod_beta}" in conversion
    assert "Code_Simp.static_conv" not in conversion
