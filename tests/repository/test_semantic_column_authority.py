"""The named B1 column blocks are closed, ordered proof data, not an oracle."""

import re

from devtools.checks.isabelle_syntax import executable_text
from devtools.paths import isabelle_root, repository_root


def _column_source(name: str) -> str:
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1_instance"
        / name
    )
    return executable_text(path.read_text(encoding="utf-8"))


def test_column_authority_is_closed_bounded_blocks_with_balanced_directory() -> None:
    source = _column_source("semantic_b1_column_conversion.ML")
    catalog = _column_source("semantic_b1_column_catalog.ML")
    make = source.split("fun make ctxt definitions", 1)[1].split(
        "val nodes = maps #nodes ordered_blocks", 1
    )[0]

    for check in (
        "dag_definitions = 1",
        "length block_definitions + 1 = length raw_definitions",
        "Thm.nprems_of equation = 0",
        "null (Thm.hyps_of equation)",
        "null (Thm.tpairs_of equation)",
        "null (Thm_Deps.all_oracles [equation])",
        "closed left andalso closed right",
        "fastype_of left = dagT",
        '"comma_semantic_b1_crt_column_node_dag"',
        '"B1 column DAG definition has invalid authority"',
    ):
        assert check in make

    parser = catalog.split("fun parse_block_tree base tree_term", 1)[1].split(
        "fun structure_key level children", 1
    )[0]
    assert "Comma_B1_CRT_Column_Block_Empty" in parser
    assert "Comma_B1_CRT_Column_Block_Node" in parser
    assert "cid >= base andalso cid < base + block_size" in parser
    assert "Int.abs (left_height - right_height) <= 1" in parser
    assert "level < Vector.length periods" in parser
    assert "length children = Vector.sub (periods, level)" in parser
    assert "B1 column DAG node has an invalid level" in parser
    assert "B1 column DAG node has an invalid radix shape" in parser

    validation = catalog.split("fun validate_nodes nodes", 1)[1].split(
        "fun parse_directory blocks term", 1
    )[0]
    assert "cids = expected" in validation
    assert "child < #cid parent" in validation
    assert "#level parent < #level child_node" in validation
    assert '"B1 column DAG has a foreign, forward, or shallow child CID"' in validation

    directory = catalog.split(
        "fun parse_directory (blocks: block Inttab.table) term", 1
    )[1].split("\nend", 1)[0]
    directory = re.sub(r"\s+", " ", directory)
    assert "case directory_shape value of" in directory
    assert "Directory_Block" in directory
    assert "Directory_Branch" in directory
    assert "extent = #extent block" in directory
    assert "#constant block aconv block_constant" in directory
    assert "Int.abs (left_height - right_height) <= 1" in directory
    assert "directory omits, repeats, or reorders a block" in directory


def test_column_interpreter_unfolds_one_kernel_node_and_keeps_children_named() -> None:
    source = _column_source("semantic_b1_column_conversion.ML")
    catalog = _column_source("semantic_b1_column_catalog.ML")
    directory_dispatch = catalog.split("fun directory_shape term", 1)[1].split(
        "fun dest_nat term", 1
    )[0]
    directory_dispatch = re.sub(r"\s+", " ", directory_dispatch)
    assert "Directory_Block" in directory_dispatch
    assert "Directory_Branch" in directory_dispatch
    assert "name = @{const_name Comma_B1_CRT_Column_DAG_Block}" in directory_dispatch
    assert "name = @{const_name Comma_B1_CRT_Column_DAG_Branch}" in directory_dispatch
    assert "case directory_shape value of" in catalog
    assert "fun dest_column_cid term" in source
    assert "fastype_of term = columnT" in source
    assert "fun known_column term = is_some (dest_column_cid term)" in source
    assert "val structure_index = fold" in catalog
    assert "Termtab.update (column_value cid, cid)" not in source
    assert "Conv.rewr_conv" in source
    assert "@{thm comma_semantic_b1_crt_column_at.simps}" in source
    evaluator = source.split("fun step_context cid", 1)[1].split(
        "fun prove_columns_admitted_conversion target_ct", 1
    )[0]
    assert "put_simpset HOL_basic_ss ctxt" not in evaluator
    admission_helper = source.split(
        "fun prove_columns_admitted_conversion target_ct", 1
    )[1].split("fun counters ()", 1)[0]
    assert "put_simpset HOL_basic_ss ctxt" in admission_helper
    assert "addsimps [columns_definition, count_definition]" in admission_helper
    assert "comma_semantic_b1_crt_columns_for_admitted" in admission_helper
    assert (
        "fun checked_definition expected_name expected_type theorem message"
        in admission_helper
    )
    assert "clean_equation equation left right" in admission_helper
    assert (
        "B1 published column list is not the DAG/count projection" in admission_helper
    )
    assert "expected_columns_body" in admission_helper
    assert "declared_count = count" in admission_helper
    assert (
        "published column count disagrees with the validated DAG extent"
        in admission_helper
    )
    assert "fold add_index" not in admission_helper
    assert "0 upto (count - 1)" not in admission_helper
    assert "comma_semantic_b1_crt_column_dag_lookup.simps" in source
    assert "comma_semantic_b1_crt_column_block_lookup.simps" in source
    assert "fun lookup_tree cid ct" not in source
    assert "fun lookup_value cid" in source
    assert "Comma_Entry_Arithmetic.natural_context ctxt" in source
    assert "fun controlled_lookup ctxt numeral_context lookup_rules visits" in source
    assert "fun choose_if ct" in source
    assert "fun open_selected_block ct" in source
    assert "Conv.rewrs_conv lookup_rules (Thm.rhs_of opened)" in source
    assert "val lookup_step = controlled_lookup ctxt numeral_context" in source
    assert "val expected = shallow_body cid" in source
    assert "lhs aconv request andalso rhs aconv expected" in source
    assert 'certify_derived_theorem "B1 one-node column unfolding" theorem' in source
    assert "null (Thm.tpairs_of theorem)" in source
    assert "certify_derived_fact theorem" in source
    assert "val child_terms = map column_value children" in source
    assert "case body_cid (Thm.term_of result) of" in source
    assert "Symtab.lookup structure_index" in source
    assert "Thm.symmetric (column_step cid)" in source
    evaluator_dispatch = source.split("fun evaluate context ct =", 1)[1].split(
        "val patterns =", 1
    )[0]
    header = source.split("fun admission_header_equation request =", 1)[1].split(
        "fun unfold_column ct =", 1
    )[0]
    assert evaluator_dispatch.index("admission_header_equation request") < (
        evaluator_dispatch.index("val expanded = operands ct")
    )
    assert "Simplifier.rewrite numeral_context" in header
    assert "argument_at 1" in header
    assert "Thm.transitive normalized header" in header
    assert "column_step_hits=" in source and "column_step_misses=" in source

    regression = _column_source("semantic_b1_column_regression.ML")
    assert "fun check_controlled_lookup ctxt" in regression
    assert "fun check_mixed_directory_shape ctxt" in regression
    assert "Comma_Semantic_B1_Column_Catalog.directory_shape" in regression
    assert "Comma_Semantic_B1_Column_Catalog.Directory_Branch" in regression
    assert "Comma_Semantic_B1_Column_Catalog.Directory_Block" in regression
    assert "fun check_generic_fixtures ctxt" in regression
    assert "Conversion.normalize_lookup_rules ctxt" in regression
    assert (
        '@{term "comma_semantic_b1_crt_template_column_ids ! index"}' not in regression
    )
    assert "!visits = 4" in regression
    assert "malformed_directory" in regression
    assert "forward_nodes" in regression
    assert "foreign_nodes" in regression
    assert "all_columns_target" in regression
    assert "computed_columns_target" in regression
    assert "nonliteral_column" in regression
    assert (
        "Comma_Semantic_B1_Column_Catalog.canonical_block_name thy 7 canonical_block_name"
        in regression
    )
    assert (
        "not (Comma_Semantic_B1_Column_Catalog.canonical_block_name thy 7 foreign_block_name)"
        in regression
    )

    publication_theory = _column_source("Comma_Semantic_B1_Occurrence_Publication.thy")
    assert publication_theory.index(
        'ML_file "semantic_b1_column_regression.ML"'
    ) < publication_theory.index("check_generic_fixtures")
    assert publication_theory.index(
        "check_generic_fixtures"
    ) < publication_theory.index("local_setup")
    assert publication_theory.count("check_generic_fixtures") == 1
    assert publication_theory.index(
        'ML_file "semantic_b1_template_projection.ML"'
    ) < publication_theory.index('ML_file "semantic_b1_column_conversion.ML"')
    assert publication_theory.index(
        'ML_file "semantic_b1_column_catalog.ML"'
    ) < publication_theory.index('ML_file "semantic_b1_column_conversion.ML"')
    assert publication_theory.index(
        'ML_file "semantic_b1_crt_operation_conversion.ML"'
    ) < publication_theory.index('ML_file "semantic_b1_column_conversion.ML"')
    assert "semantic_b1_ephemeral_or_fold.ML" not in publication_theory

    evaluate = source.split("fun evaluate context ct =", 1)[1].split(
        "val patterns =", 1
    )[0]
    publication = source.split("fun check_and_publish request theorem =", 1)[1].split(
        "fun unfold_column", 1
    )[0]
    assert evaluate.index("if not (closed request)") < evaluate.index(
        "val expanded = operands ct"
    )
    assert "Termtab.defined (!active) request" in evaluate
    assert "check_and_publish request" in evaluate
    assert "val result = #check equation_checker request theorem" in publication
    assert "#complete (#status result)" in publication
    assert "Termtab.size (!facts) < 8192" in publication
    assert publication.index(
        "#check equation_checker request theorem"
    ) < publication.index("facts := Termtab.update (request, checked)")
    assert "val _ = active := Termtab.delete request (!active)" in evaluate
    assert "comma_semantic_b1_crt_group_piece_fold" not in source
    assert "make_ephemeral_or_fold" not in source
    assert "group_piece_fold" not in regression
    partition_conversion = _column_source("semantic_b1_partition_conversion.ML")
    assert "rewrite_template_partition_certificate" in partition_conversion
    assert (
        "comma_semantic_b1_crt_columns_partition_certified_def" in partition_conversion
    )
    assert "! source ! row" in regression
    assert "production_request" in regression
    assert "outside_row_request" in regression
    assert "B1 Suc-level admission did not use the checked header" in regression


def test_template_partitions_use_shared_residuals_without_prefix_union() -> None:
    root = isabelle_root(repository_root()) / "families/comma/comma_semantic_b1"
    theory = executable_text(
        (root / "Comma_Semantic_B1_CRT_Partition_Coverage.thy").read_text(
            encoding="utf-8"
        )
    )
    cache = _column_source("semantic_b1_occurrence_check_cache.ML")
    converter = _column_source("semantic_b1_partition_conversion.ML")
    column_converter = _column_source("semantic_b1_column_conversion.ML")
    store_fixtures = _column_source("semantic_b1_certificate_store_fixtures.ML")
    checker = theory.split("fun comma_semantic_b1_crt_partition_cofactor_checked", 1)[
        1
    ].split("definition comma_semantic_b1_crt_columns_partition_certified", 1)[0]
    assert "comma_crt_cofactor_or_false" in checker
    assert "comma_semantic_b1_crt_partition_drop_false" in checker
    assert "remdups" not in checker
    assert "0..<924" not in checker
    assert "comma_crt_apply" not in checker
    assert "comma_semantic_b1_crt_partition_fold" not in theory
    assert "occurrence_cache_patterns" in cache
    assert "comma_semantic_b1_crt_partition_cofactor_checked" in _column_source(
        "semantic_b1_construction_check.ML"
    )
    assert "rewrite_partition_cofactor_checked" in converter
    assert "context delsimps recursive_rules" in converter
    assert "template_partition_cofactor_state_conversions" in converter
    assert "template_partition_cofactor_state_memo_hits" in converter
    assert "template_partition_fold_or" not in converter
    assert "template_partition_fold_and" not in converter
    assert "case_comma_crt_column" in column_converter
    assert "complementary_quarters_request" in store_fixtures
    assert "named_complement_request" in store_fixtures
    assert (
        "quarter_conversions_after > quarter_conversions_before + 1" in store_fixtures
    )
    assert "quarter_hits_after > quarter_hits_before" in store_fixtures
    for fixture in (
        "rejects_empty",
        "rejects_missing_coverage",
        "rejects_duplicate_true",
        "rejects_missing_quarter",
        "accepts_complementary_quarters",
    ):
        assert "comma_semantic_b1_crt_columns_partition_certified_" + fixture in theory


def test_publication_defines_bounded_blocks_and_canonical_cid_applications() -> None:
    source = _column_source("semantic_b1_occurrence_publication.ML")
    block_serializer = source.split("fun serialize_column_block rows", 1)[1].split(
        "fun define_column_blocks", 1
    )[0]
    blocks = source.split("fun define_column_blocks", 1)[1].split(
        "fun column_value", 1
    )[0]
    batch = source.split("fun define_global_definitions", 1)[1].split(
        "fun serialize_column_block", 1
    )[0]
    assert "column_block_size = 512" in source
    assert "Local_Theory.background_theory_result" in batch
    assert "Sign.declare_const_global" in batch
    assert "Global_Theory.add_def" in batch
    assert (
        'define_global_definitions\n        "column-block-batch-definitions"' in blocks
    )
    assert 'stage ^ "-complete definitions="' in batch
    assert '"comma_semantic_b1_crt_column_block_"' in blocks
    assert "Comma_B1_CRT_Column_DAG_Block" in blocks
    assert "Comma_B1_CRT_Column_DAG_Branch" in blocks
    assert "Comma_B1_CRT_Column_Block_Node" in block_serializer
    assert "Vector.sub (row_vector, middle)" in block_serializer
    assert "Vector.sub (block_vector, middle)" in blocks
    assert "build lower middle" in blocks
    assert "build middle upper" in blocks

    define = source.split("fun define_column_data", 1)[1].split(
        "fun template_projection", 1
    )[0]
    assert define.count("Local_Theory.define") == 3
    assert '"comma_semantic_b1_crt_column_node_dag"' in define
    assert '"comma_semantic_b1_crt_column_count"' in define
    assert '"comma_semantic_b1_crt_columns"' in define
    assert "comma_semantic_b1_crt_columns_for" in define
    assert '"comma_semantic_b1_crt_compact_definitions"' in define
    assert "column-block-theorem-bundle-skipped" in define
    assert "columns_for $ dag_constant $ count_constant" in define
    assert "Array.sub (constants" not in define
    assert "column_constant_name" not in source
    assert "compress_template_row" not in source
    assert "Term.size_of_term columns_term" not in source
    publisher = _column_source("semantic_b1_occurrence_publication.ML")
    catalogue = publisher.split("fun get_definitions ctxt =", 1)[1].split(
        "fun template_projection", 1
    )[0]
    catalogue = re.sub(r"\s+", " ", catalogue)
    assert '"comma_semantic_b1_crt_column_node_dag_def"' in catalogue
    assert (
        'Comma_Semantic_B1_Column_Catalog.block_prefix ^ Int.toString index ^ "_def"'
        in catalogue
    )
    assert "val (indices, _) = parse directory" in catalogue
    assert "canonical_block_name thy index block_long_name" in catalogue
    assert "0 upto (length indices - 1)" in catalogue
    assert '"comma_semantic_b1_crt_column_count_def"' not in catalogue

    artifact_batch = source.split("val artifact_definitions =", 1)[1].split(
        "val (_, next) = define_global_definitions", 1
    )[0]
    assert (
        'val template_ids_name = "comma_semantic_b1_crt_template_column_ids"' in source
    )
    assert (
        "data template_ids_name (fastype_of template_column_ids_term)" in artifact_batch
    )
    assert "val map_column_rows" in source
    assert "template_projection dag_constant" in artifact_batch
    assert (
        'lookup_global_constant "artifact batch" constants template_ids_name'
        in artifact_batch
    )
    assert "lift_column_id_block_definitions @" in artifact_batch
    assert (
        "[lift_column_id_blocks_root_definition, lift_column_ids_root_definition] @"
        in artifact_batch
    )
    lift_root = source.split("val lift_column_ids_definition", 1)[1].split(
        "fun define_global_definitions", 1
    )[0]
    assert '"comma_semantic_b1_crt_lift_column_ids"' in lift_root
    assert 'lookup_global_constant "lift-column root" constants' in lift_root
    assert "lift_column_id_blocks_name" in lift_root
    assert "concatenate $" in lift_root
    assert "get_lift_column_id_block_definitions" in source
    assert "length root_children = expected_block_count" in source
    assert "B1 lift-column block directory is foreign, missing, or reordered" in source
    assert "lift_column_id_block_size = 64" in source
    projection = _column_source("semantic_b1_lift_column_projection.ML")
    assert "[0, 1, 63, 64, 2443]" in projection
    assert "row_count = 2444" in projection
    assert "HOLogic.mk_number natT row_count" in projection
    assert "B1 lift-column index exceeds its authenticated extent" in projection
    assert "Named selected-list child has an inconsistent row extent" in projection
    assert "piece_source_definitions @" in artifact_batch
    assert "construction_piece_refs_definition piece_sources" in artifact_batch
    piece_root = source.split("fun construction_piece_refs_definition", 1)[1].split(
        "val column_block_size", 1
    )[0]
    assert '"comma_semantic_b1_crt_construction_piece_refs"' in piece_root
    assert "HOLogic.mk_list sourceT" in piece_root
    assert "map (lookup_global_constant" in piece_root
    assert "construction_piece_refs_term" not in source
    assert '"comma_semantic_b1_crt_grouped_union_steps"' not in artifact_batch
    assert '"comma_semantic_b1_crt_grouped_union_start_ids"' not in artifact_batch
    assert "serialize_grouped_union_steps" not in source
    assert "union_prefixes=ephemeral" not in source
    assert '"comma_semantic_b1_crt_templates"' in artifact_batch
    assert "Comma_Semantic_B1_Template_Constructor.make lthy" in source
    assert '"comma_semantic_b1_crt_sources"' in artifact_batch
    assert '"comma_semantic_b1_crt_descriptors"' in artifact_batch

    shared_fixture = source.split("fun check_shared_column_dag_example ()", 1)[1].split(
        "fun serialize_construction_piece", 1
    )[0]
    assert "shared_child parent andalso" in shared_fixture
    assert "shared_child sibling" in shared_fixture
    assert "#cid dag parent <> #cid dag swapped" in shared_fixture
    assert "length (distinct (op =) encoded_ids) = length encoded_ids" in shared_fixture
    assert "check_shared_column_dag_example ()" in source

    dag_theory = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1/Comma_Semantic_B1_CRT_Column_DAG.thy"
    ).read_text(encoding="utf-8")
    assert "comma_semantic_b1_crt_columns_for dag extent" in dag_theory
    assert "comma_semantic_b1_crt_columns_for_length" in dag_theory
    assert "comma_semantic_b1_crt_columns_for_nth" in dag_theory
    assert "index < extent" in dag_theory
    assert "comma_semantic_b1_crt_guarded_node_admitted" in dag_theory
    assert "comma_semantic_b1_crt_column_at_admitted" in dag_theory
    assert "comma_semantic_b1_crt_columns_for_admitted" in dag_theory
    assert "comma_semantic_b1_crt_column_templates_nth" in dag_theory
    cache = _column_source("semantic_b1_occurrence_check_cache.ML")
    certificate_store = _column_source("semantic_b1_certificate_store.ML")
    projection = _column_source("semantic_b1_template_projection.ML")
    assert 'select "templates"' not in cache
    assert "val base_context = fold Simplifier.add_proc procedures" in cache
    assert "make_template_projection ctxt" in cache
    assert "Comma_Semantic_B1_Certificate_Store.make_instance_store" in cache
    assert "columns = @{term comma_semantic_b1_crt_columns}" in certificate_store
    assert (
        "Context.eq_thy (Proof_Context.theory_of context, store_theory)"
        in certificate_store
    )
    assert (
        "Context.subthy (Thm.theory_of_thm theorem, store_theory)" in certificate_store
    )
    assert (
        "Isabelle_Thread.equal (store_owner_thread, Isabelle_Thread.self ())"
        in certificate_store
    )
    assert "fun same_selected context left right =" in certificate_store
    assert "selected_equation context left" in certificate_store
    assert "val selected_equation_capacity = 8192" in certificate_store
    assert "fun rewrite_lift_geometry ctxt context request cterm =" in certificate_store
    assert (
        "B1 admitted lift geometry is missing its captured TemplateCID certificate"
        in certificate_store
    )
    fixtures = _column_source("semantic_b1_certificate_store_fixtures.ML")
    assert '("missing_template_lift_rejected",' in fixtures
    assert '("missing_template_lift_not_published",' in fixtures
    assert "lookup_cid templates" in certificate_store
    assert "[columns, templates_table, template_ids]" in certificate_store
    assert (
        "Context.proper_subthy (thy, Thm.theory_of_thm foreign_template_eq)"
        in _column_source("semantic_b1_certificate_store_fixtures.ML")
    )
    assert "exact_prefix args authority" in certificate_store
    assert "Inttab.lookup (!table) cid" in certificate_store
    assert "Thm.term_of (Thm.lhs_of theorem) aconv request" in certificate_store
    assert "templates_table, template_ids" in certificate_store
    assert "lift_ids, lift_descriptors" in certificate_store
    assert '"semantic_b1_selected_template_projection"' in projection
    assert "val bridge_step = Conv.rewr_conv bridge" in projection
    assert "selected_row = Simplifier.rewrite selected_context" in projection
    assert "template_projection_row_cells" in projection
    assert "val projection_capacity = 8192" in projection
    assert 'Synchronized.var "semantic_b1_template_projection"' in projection
    assert "Synchronized.change_result projection_memo" in projection
    assert "Termtab.size (#facts state) < projection_capacity" in projection
    assert "#raced_reuses state + 1" in projection
    assert "template_projection_hits=" in projection
    assert "template_projection_race_reuses=" in projection
    assert "template_projection_publications=" in projection
    assert "template_projection_retained=" in projection
    template_factory = projection.split("fun make {", 1)[1]
    template_setup = template_factory.split("fun check_fixtures ()", 1)[0]
    assert "Simplifier.rewrite projection_context" not in template_setup
    assert '"comma_semantic_b1_crt_sources_def"' not in template_setup
    assert "check_fixtures = check_fixtures" in template_factory
    assert "@{const_name size}" in template_setup
    assert "@{const_name length}" not in template_setup
    regression = _column_source("semantic_b1_column_regression.ML")
    assert "fun check_template_projection ctxt" in regression
    assert (
        "val nested_ids_request = ids_nth $ ids_table $ descriptor_template_index"
        in regression
    )
    assert "malformed_nested_ids" in regression
    assert (
        "nested selected-list did not resolve a sibling descriptor index" in regression
    )
    assert "#check_fixtures projection ()" in regression
    assert "val _ = check_template_projection ctxt" in regression
    project = projection.split("fun project_template cterm", 1)[1].split(
        "val procedure = Simplifier.make_simproc", 1
    )[0]
    assert (
        project.index("normalize_template_index request cterm index")
        < project.index("lookup_projection canonical")
        < project.index("compute_template_row canonical canonical_cterm index'")
    )
    assert "compose_cached_projection request canonical" in project
    assert (
        "descriptor_alias_request = nth_const $ template_table $ descriptor_index"
        in projection
    )
    assert "rows_before_descriptor_alias" in projection
    assert "#hits (Synchronized.value projection_memo)" in projection
    assert (
        "replayed_zero = Simplifier.rewrite projection_context template_zero_cterm"
        in projection
    )
    assert "reuse its exact row theorem" in projection
    assert "template_zero_result" in projection
    assert "foreign-definition fixture" in projection
    assert "projection did not cancel on its selected row" in projection
    assert "out-of-range row" in projection
    assert "declare comma_semantic_b1_crt_column_at.simps [simp del]" in dag_theory


def test_dag_stale_foreign_and_swapped_child_fixtures_are_mapped() -> None:
    regression = _column_source("semantic_b1_column_regression.ML")
    assert "Publication.get_definitions ctxt" in regression
    assert "duplicate DAG authority" in regression
    assert "stale table value" in regression
    assert "foreign_column = column_value (#node_count converter)" in regression
    assert "stale_column = column_at $ empty_dag" in regression
    assert "val swapped_reified = #reify converter" in regression
    assert (
        "not (Thm.term_of (Thm.rhs_of swapped_reified) aconv node_constant)"
        in regression
    )
    assert "clean_theorem node_equation" in regression
    assert "B1 column DAG node has an invalid level" in regression
    assert "B1 column DAG node has an invalid radix shape" in regression
    assert "missing_decode_theorem" in regression
    assert "admitted_false_theorem" in regression
    assert "strict converter rejects missing CID" in regression
    assert "val expected_node_body" in regression
    assert "node_body aconv expected_node_body" in regression


def test_b1_construction_checker_keeps_action_row_component_in_bound_order() -> None:
    root = isabelle_root(repository_root()) / "families/comma"
    checker = executable_text(
        (
            root / "comma_semantic_b1_instance/semantic_b1_construction_check.ML"
        ).read_text(encoding="utf-8")
    )
    bounds_path = root / "comma_semantic_b1/Comma_Semantic_B1_CRT_Occurrence_Bounds.thy"
    bounds = bounds_path.read_text(encoding="utf-8")
    bound = bounds.split(
        "definition comma_semantic_b1_crt_constructed_occurrence_bound", 1
    )[1].split(
        "lemma comma_semantic_b1_crt_constructed_occurrence_bound_index_guards", 1
    )[0]
    labels_source = checker.split("val labels =", 1)[1].split("val components =", 1)[0]
    labels = re.findall(r'"([^"\\]*)"', labels_source)

    assert labels == [
        "source-normalization",
        "source-admission",
        "lift-reference-width",
        "lift-slot-order",
        "descriptor-width",
        "piece-row-width",
        "parent-descriptor-and-column-resolution",
        "parent-binding",
        "beta-nonempty",
        "beta-distinct",
        "source-action-row",
        "lift-slots",
        "goto-source-order",
        "origin-multiplicity",
        "group-geometry-and-piece-binding",
    ]
    assert len(labels) == 15
    action_row = (
        "comma_semantic_b1_crt_source_slot_action_row_certified source period actions"
    )
    action_slots = "list_all (comma_semantic_b1_crt_lift_slot_valid_from_actions"
    piece_bindings = (
        "comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions"
    )
    assert bound.count(action_row) == 1
    assert bound.index("distinct beta") < bound.index(action_row)
    assert bound.index(action_row) < bound.index(action_slots)
    assert bound.index(action_slots) < bound.index(piece_bindings)


def test_construction_counter_deltas_are_source_scoped() -> None:
    root = (
        isabelle_root(repository_root()) / "families/comma/comma_semantic_b1_instance"
    )
    checker = (root / "semantic_b1_occurrence_check_cache.ML").read_text(
        encoding="utf-8"
    )
    store = (root / "semantic_b1_certificate_store.ML").read_text(encoding="utf-8")
    construction = (root / "semantic_b1_construction_check.ML").read_text(
        encoding="utf-8"
    )
    fixtures = (root / "semantic_b1_certificate_store_fixtures.ML").read_text(
        encoding="utf-8"
    )
    partition = (root / "semantic_b1_partition_conversion.ML").read_text(
        encoding="utf-8"
    )
    conversion = checker.split("fun convert context cterm =", 1)[1].split(
        "fun memo_proc context ct =", 1
    )[0]
    memo_proc = checker.split("fun memo_proc context ct =", 1)[1].split(
        "val proc =", 1
    )[0]
    assert "binding_source_action_evaluations :=" in conversion
    assert "#note_source_action_reuse certificate_store ();" in checker
    hit_recorder = checker.split("fun record_completed_hit request =", 1)[1].split(
        "fun memo_proc", 1
    )[0]
    assert "note_source_action_reuse request" in hit_recorder
    assert "record_completed_hit request" in memo_proc
    assert "source_action_captured" in store and "source_action_reused" in store
    assert (
        "source_action_rows_captured=" in store
        and "source_action_rows_reused=" in store
    )
    assert "track_current_source_counter slot_valid_captured 2" in store
    assert "track_current_source_counter slot_valid_reused 3" in store
    reset = store.split("fun reset_current_source index =", 1)[1].split(
        "fun remember_equation", 1
    )[0]
    assert "source_construction_active := true" in reset
    assert "Array.modify (fn _ => 0) current_source_metrics" in reset
    assert "source_action_evaluations := 0" not in reset
    assert "slot_valid_captured := 0" not in reset
    assert "source_action_evaluations_delta=" in store
    assert "source_action_reuses_delta=" in store
    assert "source_slot_certificates_captured_delta=" in store
    assert "source_slot_certificates_reused_delta=" in store
    assert "source_construction_active := false" in store
    assert "source_action_proofs_new=" in store
    assert "source_action_proofs_reused=" in store
    assert "source_action_rows_captured=" in store
    assert "source_action_rows_reused=" in store
    assert "template_context_lookups=" in store
    assert "template_context_requests_completed=" in store
    assert "template_context_consumed=" not in store
    assert "Partition_Conversion.make_template_partition_session" in checker
    assert "val profile = make_template_partition_profile ()" in partition
    assert "val result = Exn.capture work ()" in partition
    assert "val _ = active := prior_depth" in partition
    assert "fun check_partition_profile_scope ()" in fixtures
    assert "val _ = check_partition_profile_scope ()" in fixtures
    assert "B1 partition exception fixture leaked active profiling scope" in fixtures
    assert "fun make_instance_store ctxt =" in store
    assert "lift_columns_option_evaluations=" in checker
    assert "lift_columns_option_memo_hits=" in checker
    assert "slot_context" not in checker
    assert "Comma_Semantic_B1_Certificate_Store.make_instance_store" in checker
    assert (
        "Comma_Semantic_B1_Construction_Check.make_certificate_store"
        not in construction
    )
    assert 'profile_certificate_source (stage ^ "-start") false' in construction
    assert 'profile_certificate_source (stage ^ "-complete") false' in construction
    assert 'then profile_certificate_source "proof-complete" true' in construction


def test_live_partition_proof_uses_certified_cid_transitions_before_recursion() -> None:
    construction = _column_source("semantic_b1_construction_check.ML")
    cache = _column_source("semantic_b1_occurrence_check_cache.ML")
    converter = _column_source("semantic_b1_partition_conversion.ML")
    fixtures = _column_source("semantic_b1_certificate_store_fixtures.ML")
    geometry = construction.split("fun prove_template_geometry_certificate", 1)[
        1
    ].split("val occurrence_cache_arithmetic_rules", 1)[0]
    assert "prove_partition_checker" in geometry
    assert "Simplifier.rewrite context checker_ct" not in geometry
    assert "prove_partition_checker = prove_partition_checker" in cache
    assert "make_template_partition_session ctxt" in cache
    assert "val profile = make_template_partition_profile ()" in converter
    vector = converter.split("fun vector_transition", 1)[1].split("fun prove_state", 1)[
        0
    ]
    assert vector.index("Symtab.lookup (!vector_transition_facts)") < vector.index(
        "cofactor_transition (level, digit, cid)"
    )
    assert "filter (fn (cid, _) => cid <> 0) edges" in vector
    assert "comma_semantic_b1_crt_partition_drop_false_idempotent" in vector
    assert "Thm.symmetric theorem" in vector
    assert "residual_transition_derivations" in vector
    assert "column_index_equation" not in converter
    assert "comma_semantic_b1_crt_column_ids_resolve_columns_for" in converter
    for regression in (
        "B1 warm CID edge repeated proof construction or DAG opening",
        "B1 warm vector transition rebuilt column proofs or reopened the DAG",
        "B1 warm partition state reconstructed its proof",
        "B1 CID partition vector contains a foreign CID",
    ):
        assert regression in fixtures
    assert "Certificate_Store_Fixtures.check_cid_transition_cache" in cache
    assert "Certificate_Store_Fixtures.check_partition_transition_dag" in cache
    column = _column_source("semantic_b1_column_conversion.ML")
    edge_audit = column.split("fun check_fresh_cofactor_transition", 1)[1].split(
        "fun build_cofactor_transition", 1
    )[0]
    assert "Comma_Entry_Arithmetic.make_certifier ctxt" in column
    assert "check_cofactor_transition_contract theorem request target_cid" in edge_audit
    assert (
        'certify_derived_theorem "B1 fresh cofactor transition" checked' in edge_audit
    )
    assert "Thm_Deps.all_oracles" not in edge_audit
    # Authority definitions and exported geometry keep independent builtin audits.
    assert "null (Thm_Deps.all_oracles [equation])" in column
    store = _column_source("semantic_b1_certificate_store.ML")
    assert "Thm_Deps.all_oracles" in store
