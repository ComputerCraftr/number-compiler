"""Source contracts for the semantic B1 mass publication route.

These checks inspect the authored Isabelle/ML boundary only.  Kernel builds
remain the authority for theorem validity; the tests catch accidental removal
of the registered bridge, multiplicity, guards, or lazy legacy setup.
"""

from collections.abc import Mapping
from pathlib import Path

from devtools.checks.isabelle_source_analysis import (
    IsabelleDeclaration,
    extract_isabelle_declarations,
)
from devtools.checks.isabelle_syntax import Session, parse_theory_header
from devtools.paths import isabelle_root, repository_root

ISABELLE = isabelle_root(repository_root())
GENERIC = ISABELLE / "families/comma/comma_semantic_b1"
INSTANCE = ISABELLE / "families/comma/comma_semantic_b1_instance"
ROOT = ISABELLE / "families/comma/ROOT"
CARDINALITY = GENERIC / "Comma_Semantic_B1_CRT_Cardinality.thy"
PARENT_PARTITION = GENERIC / "Comma_Semantic_B1_CRT_Parent_Partition.thy"
CONSTRUCTOR_MASS = GENERIC / "Comma_Semantic_B1_CRT_Constructor_Mass.thy"
CONSTRUCTED_OCCURRENCE = GENERIC / "Comma_Semantic_B1_CRT_Constructed_Occurrence.thy"
COMPLETENESS = GENERIC / "Comma_Semantic_B1_CRT_Partition_Completeness.thy"
COLUMN_MASS = INSTANCE / "semantic_b1_column_mass.ML"
TEMPLATE_MASS = INSTANCE / "semantic_b1_template_mass_check.ML"
OCCURRENCE_CACHE = INSTANCE / "semantic_b1_occurrence_check_cache.ML"
PUBLICATION = INSTANCE / "Comma_Semantic_B1_Occurrence_Publication.thy"


def _declarations(path: Path) -> dict[str, IsabelleDeclaration]:
    return {
        item.name: item
        for item in extract_isabelle_declarations(
            path.read_text(encoding="utf-8"), path
        )
    }


def test_mass_bridge_is_registered_in_dependency_order_and_audited(
    repository_sessions: Mapping[str, Session],
) -> None:
    generic = repository_sessions["Comma_Semantic_B1"]
    assert generic.theories.index(
        "Comma_Semantic_B1_CRT_Cardinality"
    ) < generic.theories.index("Comma_Semantic_B1_CRT_Constructor_Mass")
    assert "Comma_Semantic_B1_CRT_Constructor_Mass" in ROOT.read_text(encoding="utf-8")

    publication_name, publication_imports = parse_theory_header(
        PUBLICATION.read_text(encoding="utf-8"), PUBLICATION
    )
    assert publication_name == "Comma_Semantic_B1_Occurrence_Publication"
    assert (
        "Comma_Semantic_B1.Comma_Semantic_B1_CRT_Mass_Transport" in publication_imports
    )
    assert (
        "Comma_Semantic_B1.Comma_Semantic_B1_CRT_Constructor_Mass"
        in publication_imports
    )

    source = CONSTRUCTOR_MASS.read_text(encoding="utf-8")
    assert "imports Comma_Semantic_B1_CRT_Constructed_Occurrence" in source
    assert "Comma_Semantic_B1_CRT_Cardinality" in source
    assert "Thm_Deps.all_oracles bundle" in source
    assert (
        "comma_semantic_b1_crt_constructed_occurrences_catalog_geometry_from_mass"
        in source
    )


def test_ordered_mass_theorem_preserves_row_multiplicity() -> None:
    cardinality = _declarations(CARDINALITY)
    ordered = cardinality["comma_semantic_b1_crt_column_list_card_mass"].body
    assert "list_all (comma_crt_admitted 0) columns" in ordered
    assert "sum_list (map card (map comma_crt_set columns))" in ordered
    assert "sum_list (map comma_semantic_b1_crt_column_mass columns)" in ordered
    assert "distinct" not in ordered

    constructor = _declarations(CONSTRUCTOR_MASS)
    template_mass = constructor["comma_semantic_b1_crt_template_mass_certified"].body
    assert "templates!template_cid" in template_mass
    assert "sum_list (map comma_semantic_b1_crt_column_mass" in template_mass
    assert "=924" in template_mass


def test_parent_geometry_keeps_local_coverage_and_admission_contract() -> None:
    parent = _declarations(PARENT_PARTITION)
    grouped = parent[
        "comma_semantic_b1_crt_parent_columns_partition_from_grouped_cover"
    ].body
    for premise in (
        "source_width",
        "source_partition",
        "label_set",
        "results_distinct",
        "parent_width",
        "rebase",
        "parent_admitted",
        "local_coverage",
        "parent_cardinality",
    ):
        assert premise in grouped
    assert "comma_semantic_b1_crt_cells_partition {..<924}" in grouped
    assert "map comma_crt_set parent_columns" in grouped

    constructed = CONSTRUCTED_OCCURRENCE.read_text(encoding="utf-8")
    assert "have local_coverage:" in constructed
    assert (
        "comma_semantic_b1_crt_parent_columns_partition_from_grouped_cover"
        in constructed
    )

    constructor = CONSTRUCTOR_MASS.read_text(encoding="utf-8")
    assert (
        "comma_semantic_b1_crt_constructed_occurrence_from_partition_or_mass"
        in constructor
    )
    assert (
        "[OF table_admitted bound _ parent_at parent_template_resolution]"
        in constructor
    )
    assert "apply (rule earlier_wellformed; assumption)" in constructor
    assert "apply (rule disjI2[OF parent_mass])" in constructor
    assert "parent_mass" in constructor


def test_completeness_bridge_requires_admitted_columns_and_partition() -> None:
    completeness = _declarations(COMPLETENESS)
    complete = completeness[
        "comma_semantic_b1_crt_columns_partition_certified_complete"
    ].body
    assert 'admitted: "list_all (comma_crt_admitted 0) columns"' in complete
    assert "comma_semantic_b1_crt_cells_partition {..<924}" in complete
    assert "map comma_crt_set columns" in complete
    assert "comma_semantic_b1_crt_partition_witness_of_cells_partition" in complete
    assert "[OF level_bound admitted partition]" in complete

    constructor = CONSTRUCTOR_MASS.read_text(encoding="utf-8")
    assert "comma_semantic_b1_crt_columns_partition_certified_complete" in constructor
    assert "[OF template_admitted template_partition]" in constructor


def test_mass_cache_rejects_foreign_or_open_requests_and_bad_theorems() -> None:
    source = COLUMN_MASS.read_text(encoding="utf-8")
    for guard in (
        "cache_limit <= 8192",
        "require_cid cid",
        "require_depth depth",
        "closed term",
        "term aconv expected_column cid",
        "known_column term",
        "cid < parent",
        "clean theorem",
        "theorem_in_context theorem",
        "check_mass theorem request value",
        "check_card theorem request value",
    ):
        assert guard in source
    for fixture in (
        "foreign_dag",
        "malformed_step_cache",
        "malformed_admission_cache",
        "B1 mass foreign-DAG fixture was accepted",
        "B1 mass malformed-step fixture was accepted",
        "B1 mass malformed-admission fixture was accepted",
    ):
        assert fixture in source
    assert "comma_semantic_b1_crt_column_mass.simps" in source
    assert "certify_theorem theorem" in source


def test_live_publication_requests_mass_for_literal_distinct_cids() -> None:
    publication = PUBLICATION.read_text(encoding="utf-8")
    cache = OCCURRENCE_CACHE.read_text(encoding="utf-8")
    template_mass = TEMPLATE_MASS.read_text(encoding="utf-8")
    assert 'ML_file "semantic_b1_column_mass.ML"' in publication
    assert 'ML_file "semantic_b1_template_mass_check.ML"' in publication
    assert "Comma_Semantic_B1_CRT_Constructor_Mass" in publication
    assert "#check_fixtures column_mass ()" in cache
    assert "checked_mass_row ids_values (mass_row ids_values)" in template_mass
    assert "length ids = length values" in template_mass
    assert "val (mass_equation, mass_values)" in template_mass
    assert "val row_arithmetic = ordered_fact mass_values" in template_mass
    assert "template_mass_requests" in template_mass
    assert "column_mass_mass_proofs" in COLUMN_MASS.read_text(encoding="utf-8")
    assert "template_mass_handler := SOME (#prove template_mass_check)" in cache
    assert "#mass_row invariant_mass" in cache
    assert "ids_values" in template_mass
    assert "Thm.transitive row_map mass_equation" in template_mass


def test_template_mass_hoists_catalogue_extents_outside_requests() -> None:
    source = TEMPLATE_MASS.read_text(encoding="utf-8")
    prove_at = source.index("fun prove request")
    assert source.index("val template_extent = extent") < prove_at
    assert source.index("val ids_extent = extent") < prove_at
    request_body = source[prove_at : source.index("fun stats", prove_at)]
    assert "normalize size" not in request_body


def test_template_mass_transports_only_the_selected_cid() -> None:
    source = TEMPLATE_MASS.read_text(encoding="utf-8")
    assert "Conv.arg_conv (Conv.arg_conv (K cid_eq))" in source
    assert "normalize (HOLogic.mk_Trueprop request)" not in source
    assert "check_fact" in source
    assert "Thm.reflexive (Thm.cterm_of ctxt term), value" in source
    assert "checked_cid (number 0)" in source
    assert "checked_cid (number 1)" in source
    assert "val template_row_equation" in source
    assert "(Thm.reflexive map_column_at_ct) ids_equation" in source
    assert "Thm.transitive selected_literal_map" in source
    assert "(Thm.symmetric template_row_equation)" in source


def test_used_template_publication_preserves_source_transport() -> None:
    publication = PUBLICATION.read_text(encoding="utf-8")
    constructor = CONSTRUCTOR_MASS.read_text(encoding="utf-8")
    used = (INSTANCE / "semantic_b1_used_templates.ML").read_text(encoding="utf-8")
    assert "remdups (map fst comma_semantic_b1_crt_descriptors)" in publication
    assert "comma_semantic_b1_crt_used_template_masses_cover_sources" in publication
    assert "descriptor_extent" in constructor
    assert "column_ids_resolve" in constructor
    assert "range aconv expected_range" in used
    assert "predicate aconv expected_predicate" in used
    assert "Thm.prop_of head aconv HOLogic.mk_Trueprop request" in used
    assert "check_items unique_entries" in used
    assert "map lookup_item entries" not in used
    assert "fun fold_exact_list_all ctxt pred elements facts" in used
    assert "fold_rev add pairs" in used
    assert "list_all_Cons_iff} RS @{thm eq_reflection}" in used
    assert "Thm.symmetric (proposition_equation equation)" in used
    assert "Used_Templates.check_fold @{context}" in used
    assert "B1 used-template early list-fold fixture changed its result" in used
    assert "Termtab.lookup item_facts_by_id entry" in used
    assert "fold_exact_list_all ctxt predicate entries occurrence_facts" in used
    assert "B1 used-template occurrence has no distinct item proof" in used
    assert "B1 used-template occurrence changed its cached item theorem" in used
    assert "B1 used-template occurrence fold changed its theorem" in used
    assert "occurrence-list-transport-complete refs=" in used
    assert "comma_semantic_b1_crt_list_all_subset" not in used
    assert "auto_tac" not in used
    assert "comma_semantic_b1_crt_list_all_remdups" in used
    assert "remdups.simps" not in used
    assert "comma_semantic_b1_crt_descriptors_def" in used
    assert "Thm.dest_comb current" in used
    assert "Conv.rewr_conv fst_pair" in used
    assert "map_via_indices" not in used


def test_shared_arithmetic_does_not_replace_exact_column_authority() -> None:
    transport_path = GENERIC / "Comma_Semantic_B1_CRT_Mass_Transport.thy"
    _, imports = parse_theory_header(
        transport_path.read_text(encoding="utf-8"), transport_path
    )
    assert "Comma_Semantic_B1_CRT_Column_DAG" in imports
    source = COLUMN_MASS.read_text(encoding="utf-8")
    assert "comma_semantic_b1_crt_column_mass_step" in source
    assert "column_mass_arithmetic_schema" in source
    assert "checked_mass_map" in source
    row = TEMPLATE_MASS.read_text(encoding="utf-8")
    assert "Thm.term_of (Thm.lhs_of equation) aconv expected_left" in row
    assert "column_at_const $ expected_dag $ number cid" in row
    assert "sort int_ord values" in row
    assert "comma_semantic_b1_crt_sum_list_mset" in row
    assert "comma_semantic_b1_crt_template_mass_certified_intro" in row
    assert "OF [template_bound, ids_bound, resolved, row_mass]" in row
    assert "context delsimps" in row
    assert "@{thms sum_list.Cons sum_list.Nil}" in row
    assert "comma_semantic_b1_crt_column_ids_resolve_columns_for_from_map" in row
    assert 'component_fact "row resolution"' not in row


def test_sparse_mass_invariant_checks_source_shape_and_child_closure() -> None:
    path = GENERIC / "Comma_Semantic_B1_CRT_Mass_Annotations.thy"
    declarations = _declarations(path)
    row = declarations["comma_semantic_b1_crt_mass_tree_row_valid"].body
    child = declarations["comma_semantic_b1_crt_mass_tree_child_valid"].body
    sound = declarations["comma_semantic_b1_crt_column_mass_annotation_tree_sound"].body
    assert "comma_semantic_b1_crt_column_dag_lookup dag cid" in row
    assert "None \\<Rightarrow> False" in row
    assert "level=source_level" in row
    assert "level<4" in row
    assert "length children=comma_crt_period level" in row
    assert "map (comma_semantic_b1_crt_mass_tree_value tree) children" in row
    assert "child<parent" in child
    assert "comma_semantic_b1_crt_mass_tree_lookup tree child" in child
    assert "Suc parent_level\\<le>child_level" in child
    assert "less_induct" in sound

    fixtures = (
        GENERIC / "Comma_Semantic_B1_CRT_Mass_Annotation_Regression.thy"
    ).read_text(encoding="utf-8")
    for rejected in (
        "deduplicated_mass",
        "forward_child",
        "wrong_radix",
        "foreign_extent",
        "missing_nonterminal",
    ):
        assert f"comma_mass_annotation_rejects_{rejected}" in fixtures
    assert "comma_mass_annotation_checks_repeated_children" in fixtures


def test_mass_consumer_uses_checked_invariant_without_column_steps() -> None:
    cache = OCCURRENCE_CACHE.read_text(encoding="utf-8")
    construction = cache.split("val invariant_mass =", 1)[1].split(
        "val _ = #check_fixtures", 1
    )[0]
    assert "make_from_nodes ctxt" in construction
    assert "source_bindings = #source_bindings columns" in construction
    assert "lookup_node" not in construction
    assert "#step" not in construction
    assert "mass_row = #mass_row invariant_mass" in cache
    source = (INSTANCE / "semantic_b1_column_mass_invariant.ML").read_text(
        encoding="utf-8"
    )
    assert "column_mass_annotation_tree_valid" in source
    assert "column_mass_annotation_tree_sound" in source
    assert "column_mass_invariant_misses" in source
    assert "#step" not in source
    assert "Thm.prop_of interval aconv expected_interval" in source
    assert "source_bindings cids" in source
    assert "map lookup_node cids" not in source


def test_legacy_partition_fixture_remains_lazy() -> None:
    source = OCCURRENCE_CACHE.read_text(encoding="utf-8")
    zipper = source.split("fun get_labelled_zipper () =", 1)[1].split(
        "fun prove_partition_checker", 1
    )[0]
    assert "NONE =>" in zipper
    assert "check_partition_transition_dag" in zipper
    assert "labelled_zipper_ref := SOME prove_checker" in zipper
    assert "labelled_zipper=lazy-uninitialized" in source
    assert source.count("check_partition_transition_dag") == 1


def test_mass_layout_certifies_exact_subtrees_without_list_reconstruction() -> None:
    source = (INSTANCE / "semantic_b1_column_mass_invariant.ML").read_text(
        encoding="utf-8"
    )
    helper = (INSTANCE / "semantic_b1_mass_layout.ML").read_text(encoding="utf-8")
    theory = (GENERIC / "Comma_Semantic_B1_CRT_Mass_Layout.thy").read_text(
        encoding="utf-8"
    )
    assert "Mass_Layout.make" in source
    assert "fun height_equation" not in source
    assert "fun ordered_equation" not in source
    for lemma in ("summary_empty", "summary_node", "summary_ordered"):
        assert f"comma_semantic_b1_crt_mass_tree_{lemma}" in helper
        assert f"comma_semantic_b1_crt_mass_tree_{lemma}" in theory
    for obsolete in (
        "fun parse_rows",
        "fun sorted_fact",
        "fun bounds_fact",
        "fun builder_equation",
        "comma_semantic_b1_crt_mass_tree_from_rows",
    ):
        assert obsolete not in helper
        assert obsolete not in theory
    assert "Thm.prop_of result aconv expected" in helper
    assert "Thm.cprop_of theorem" in helper
    assert '("left", left_ct)' in helper
    assert '("right", right_ct)' in helper
    assert "normalize_height height_equation height_term fact" in helper
    assert "val scalar_height_capacity = 512" in helper
    assert "scalar_facts left_height_value right_height_value" in helper
    assert "Thm.instantiate (TVars.empty, Vars.make entries) theorem" in helper
    assert "Thm.implies_elim theorem premise" in helper
    assert "null type_vars" in helper
    assert "fun prepare_rule theorem" in helper
    assert "length entries = length vars" in helper
    for rejected in (
        "an unbalanced tree",
        "a duplicate CID",
        "a foreign CID",
        "out-of-order rows",
        "an open annotation",
        "a wrong annotation type",
        "an invalid extent",
    ):
        assert rejected in helper
    assert "make ctxt arithmetic_context 8 valid_skew" in helper
    assert "fastype_of annotation = treeT andalso closed annotation" in helper
    assert "closed (Thm.prop_of theorem)" in helper
    assert "Mass_Layout.fixture" in PUBLICATION.read_text(encoding="utf-8")


def test_source_block_transport_checks_exact_intervals_and_authority() -> None:
    source = (INSTANCE / "semantic_b1_column_mass_invariant.ML").read_text(
        encoding="utf-8"
    )
    for rejection in (
        "changed source-binding base",
        "changed source-binding extent",
        "foreign source block definition",
        "foreign source block interval",
    ):
        assert rejection in source
    assert "Thm.prop_of interval aconv expected_interval" in source
    assert "Context.subthy" in source
    assert "check_source_binding_authority" in PUBLICATION.read_text(encoding="utf-8")


def test_mass_specialization_reuses_certified_tree_and_selected_path() -> None:
    source = (INSTANCE / "semantic_b1_column_mass_invariant.ML").read_text(
        encoding="utf-8"
    )
    specialize = source.split("fun specialize cid level value =", 1)[1].split(
        "fun mass cid =", 1
    )[0]
    assert "SOME lookup_fact =>" in specialize
    assert "lookup_fact cid" in specialize
    assert "Mass_Rows.lookup_equation" in specialize  # direct-certificate fallback
    assert "Goal.prove" not in specialize
    assert "Thm.prop_of lookup_fact aconv expected_lookup_fact" in specialize
    helper = (INSTANCE / "semantic_b1_mass_rows.ML").read_text(encoding="utf-8")
    assert "Column_Conversion.choose_closed_if" in helper
    assert "Thm.apply (Thm.apply lookup_ct tree_ct) cid_ct" in helper
    assert "fun choose_if" not in helper


def test_production_mass_owner_reuses_frozen_named_root_lookup_facts() -> None:
    rows = (INSTANCE / "semantic_b1_mass_rows.ML").read_text(encoding="utf-8")
    invariant = (INSTANCE / "semantic_b1_column_mass_invariant.ML").read_text(
        encoding="utf-8"
    )
    assert "val frozen_lookup_cache = !lookup_cache" in rows
    assert "Inttab.lookup frozen_lookup_cache cid" in rows
    assert "B1 mass row cached lookup does not cover the requested CID" in rows
    assert "lookup_facts = Inttab.size frozen_lookup_cache" in rows
    assert "val rows_fact = #theorem rows_result" in invariant
    assert "#lookup_fact rows_result" in invariant
    assert "val (certificate, cached_lookup) = prove_valid annotation_body" in invariant
    assert "make_with_lookup_provider ctxt (SOME cached_lookup)" in invariant
    assert "local\n  fun make_with_lookup_provider" in invariant
    assert "comma_semantic_b1_crt_column_mass.simps if_True if_False" in invariant
    assert "column_mass_invariant_cached_lookup_reuses=" in invariant
    assert "B1 mass-row fixture did not retain its exact named-root lookup" in rows


def test_mass_rows_consume_exact_child_summaries_without_reopening_vectors() -> None:
    source = (INSTANCE / "semantic_b1_mass_rows.ML").read_text(encoding="utf-8")
    row_proof = source.split("fun small_row_fact", 1)[1].split("fun conjunction", 1)[0]
    assert "Goal.prove" not in row_proof
    assert "Simplifier.rewrite" not in row_proof
    assert "val summary = child_vector_summary children_ct" in row_proof
    assert "val fact = apply_premises rule facts" in row_proof
    assert "Thm.prop_of fact aconv HOLogic.mk_Trueprop request" in row_proof
    assert "structurally_closed fact" in row_proof
    assert "mass_tree_row_valid_of_child_vector_summary" in source
    assert "vector_capacity = 8192" in source
    assert "Termtab.lookup (!vector_cache) children" in source
    assert "Thm.term_of (Thm.lhs_of reduced) aconv expected" in source
    assert "structurally_closed reduced" in source
    assert "fun rows_fact (subtree, subtree_ct)" in source
    assert "cterm_arguments 5 subtree_ct" in source
    assert "Thm.apply rows_authority_ct subtree_ct" in source

    theory = _declarations(GENERIC / "Comma_Semantic_B1_CRT_Mass_Annotations.thy")
    summary = theory["comma_semantic_b1_crt_child_vector_summary_of"].body
    assert "None" in summary
    assert "mass_tree_lookup tree child" in summary
    assert "child_mass + vector_total" in summary
    assert "distinct" not in summary
    row = theory[
        "comma_semantic_b1_crt_mass_tree_row_valid_of_child_vector_summary"
    ].body
    for premise in (
        "source:",
        "cid_bound:",
        "level_bound:",
        "summary:",
        "width:",
        "max_bound:",
        "min_bound:",
        "mass:",
    ):
        assert premise in row


def test_mass_lookup_transport_preserves_named_authority_and_exact_bounds() -> None:
    theory = _declarations(GENERIC / "Comma_Semantic_B1_CRT_Mass_Layout.thy")
    prefix = "comma_semantic_b1_crt_mass_tree_lookup_transport"
    for suffix in ("left", "right", "node_key"):
        lemma = theory[f"{prefix}_{suffix}"].body
        assert "ordered:" in lemma
        assert "transport:" in lemma
    source = (INSTANCE / "semantic_b1_mass_rows.ML").read_text(encoding="utf-8")
    assert "Thm.prop_of ordered_fact aconv expected_ordered" in source
    assert "published_tree_ct" in source
    assert "fun collect_lookup_facts" in source
    assert "point lookup" in source
    assert "lookup $ published_tree $ HOLogic.mk_number natT cid_value" in source
    assert "lookup_path_fallbacks" in source
    invariant = (INSTANCE / "semantic_b1_column_mass_invariant.ML").read_text(
        encoding="utf-8"
    )
    assert "ordered_fact = ordered_body_fact" in invariant
    publication = PUBLICATION.read_text(encoding="utf-8")
    assert publication.index('ML_file "semantic_b1_mass_layout.ML"') < (
        publication.index('ML_file "semantic_b1_mass_rows.ML"')
    )


def test_mass_source_rows_compose_block_authority_before_point_selection() -> None:
    helper = (INSTANCE / "semantic_b1_mass_source_rows.ML").read_text(encoding="utf-8")
    for guard in (
        "Thm.prop_of definition aconv definition_expected",
        "Thm.prop_of interval aconv interval_expected",
        "Thm_Deps.all_oracles source_theorems",
        "source-row traversal found duplicate CIDs",
        "source-row CID has no exact authenticated block lookup",
    ):
        assert guard in helper
    assert "mass_source_lookup_transport_root" in helper
    assert "mass_source_lookup_transport_split" in helper
    assert "HOLogic.mk_eq (lhs, expected_row)" in helper
    rows = (INSTANCE / "semantic_b1_mass_rows.ML").read_text(encoding="utf-8")
    provider = rows.split("fun source_row_provider", 1)[1].split("fun make (", 1)[0]
    assert "Mass_Source_Rows.make" in provider
    assert "#lookup block_cache" not in provider
    assert "@{thm spec}" not in provider
    assert "Thm.rhs_of equation" in provider


def test_mass_alias_is_theory_owned_and_checks_exact_metadata() -> None:
    publisher = (INSTANCE / "semantic_b1_occurrence_publication.ML").read_text(
        encoding="utf-8"
    )
    authority = (INSTANCE / "semantic_b1_mass_alias.ML").read_text(encoding="utf-8")
    invariant = (INSTANCE / "semantic_b1_column_mass_invariant.ML").read_text(
        encoding="utf-8"
    )
    assert "structure Mass_Annotation_Data = Theory_Data" in publisher
    assert "body_cids = cids" in authority
    assert "right aconv body" in authority
    assert "alias_roots = roots" in invariant
    assert "Mass_Alias.check_fixtures" in invariant
    for rejection in (
        "wrong alias constant",
        "wrong alias body",
        "wrong alias definition",
        "missing alias CID",
        "duplicate alias CID",
        "foreign alias CID",
        "foreign alias root",
        "negative demanded root",
        "missing nonterminal annotation root",
        "duplicate demanded root",
        "undersized DAG extent",
    ):
        assert rejection in authority


def test_map_resolution_retains_bounds_and_exact_catalogue() -> None:
    path = GENERIC / "Comma_Semantic_B1_CRT_Construction_Binding.thy"
    bridge = _declarations(path)[
        "comma_semantic_b1_crt_column_ids_resolve_columns_for_from_map"
    ].body
    for premise in (
        "columns=comma_semantic_b1_crt_columns_for dag extent",
        r"list_all (\<lambda>cid. cid<extent) ids",
        "map (comma_semantic_b1_crt_column_at dag) ids=values",
    ):
        assert premise in bridge
    assert "comma_semantic_b1_crt_column_ids_resolve columns ids values" in bridge
    assert "distinct" not in bridge
    source = TEMPLATE_MASS.read_text(encoding="utf-8")
    bounds = source.split("val column_bound_predicate =", 1)[1].split(
        "fun component_fact", 1
    )[0]
    assert "Const (@{const_name less}, natT --> natT --> @{typ bool})" in bounds
    assert "HOLogic.mk_binrel" not in bounds
    transport = source.split("val selected_id_bounds_raw =", 1)[1].split(
        "val mapped_row =", 1
    )[0]
    assert "@{term Trueprop}" in transport
    assert (
        "Thm.equal_elim (Thm.symmetric selected_id_bounds) literal_id_bounds"
        in transport
    )


def test_piece_publication_uses_checked_blocks_and_bounded_source_projection() -> None:
    publisher = (INSTANCE / "semantic_b1_occurrence_publication.ML").read_text(
        encoding="utf-8"
    )
    projection = (INSTANCE / "semantic_b1_construction_piece_projection.ML").read_text(
        encoding="utf-8"
    )
    assert "construction_piece_source_block_size = 32" in publisher
    assert "serialize_construction_piece_source_definitions" not in publisher
    assert "serialize_construction_piece_source_blocks" in publisher
    assert "Construction_Piece_Projection.make ctxt" in OCCURRENCE_CACHE.read_text(
        encoding="utf-8"
    )
    for guard in (
        "blocks are foreign, missing, or reordered",
        "catalogue contains a noncanonical definition",
        "source index exceeds its extent",
        "row index exceeds its source extent",
        "actual_source_extents = child_row_extents",
    ):
        assert guard in projection
    assert "source_cache_capacity = 8192" in projection
    assert "Synchronized.change_result source_cache" in projection
    assert "source_operation_procedures" in projection
    assert "piece_block_locator_steps" in projection
    assert "block_visits = block_visits + block + 1" not in projection
    assert 'ML_file "semantic_b1_construction_piece_projection.ML"' in (
        PUBLICATION.read_text(encoding="utf-8")
    )
