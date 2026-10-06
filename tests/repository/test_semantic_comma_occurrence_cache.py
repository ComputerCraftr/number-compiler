"""Semantic Comma certificate publication and memo authority invariants."""

from devtools.checks.isabelle_source_analysis import extract_isabelle_declarations
from devtools.checks.isabelle_syntax import executable_text
from devtools.paths import isabelle_root, repository_root


def test_occurrence_certificate_waits_for_proof_and_preserves_memo_authority() -> None:
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
        / "families/comma/comma_semantic_b1_instance"
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
    root = (
        isabelle_root(repository_root()) / "families/comma/comma_semantic_b1_instance"
    )
    checker = (root / "semantic_b1_occurrence_check_cache.ML").read_text(
        encoding="utf-8"
    )
    indexed = checker.split("fun prove_list_all predicate range =", 1)[1].split(
        "fun prove_expression", 1
    )[0]
    assert "prove_true (predicate $ numeral index)" in indexed
    assert "Comma_Selected_List_Conversion.prove_indexed_list_all" in indexed
    shared = (
        isabelle_root(repository_root())
        / "families/comma/comma_entry_arithmetic/selected_list_conversion.ML"
    ).read_text(encoding="utf-8")
    recurrence = shared.split("fun prove_indexed_list_all", 1)[1].split("fun make", 1)[
        0
    ]
    assert "comma_indexed_all_Suc" in indexed
    assert "comma_indexed_all_zero" in indexed
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
    selector = (
        isabelle_root(repository_root())
        / "families/comma/comma_entry_arithmetic/selected_list_conversion.ML"
    ).read_text(encoding="utf-8")
    assert "suffix_memo" in selector
    assert "_spine_node_visits=" in selector
    assert "_selected_cells=" in selector
    assert "_list_node_visits=" not in selector


def test_selected_list_checks_each_nested_extent_before_cache_access() -> None:
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
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1_instance"
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
