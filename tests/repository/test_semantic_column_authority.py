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

    assert catalog.count("fun parse_directory ") == 1
    validation = catalog.split("fun validate_nodes nodes", 1)[1].split(
        "fun parse_directory ", 1
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
    lookup_cache = _column_source("semantic_b1_column_lookup_cache.ML")
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
    evaluator = source.split("fun targeted_step_context", 1)[1].split(
        "val cofactor_or_false_const", 1
    )[0]
    assert "put_simpset HOL_basic_ss ctxt" not in evaluator
    assert "Simplifier.add_proc" not in evaluator
    assert "[root_lookup, raw_admission]" in evaluator
    assert "rhs aconv expected" in evaluator
    assert "make_column_at_admitted_header ctxt" in source
    assert source.index("val prove_admitted_header =") < source.index(
        "fun child_admission_fact"
    )
    assert "val admitted_equation = prove_admitted_header" in source
    assert "val header = prove_admitted_header" in source
    assert "Termtab.size (!child_admission_facts) < 8192" in source
    skipped = source.split("val theorem = if cid >= 2 andalso", 1)[1].split(
        "            else", 1
    )[0]
    assert "child_admission_fact (level + 1) cid" in skipped
    assert "comma_crt_cofactor_skip_from_admission" in skipped
    assert "column_step" not in skipped
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
    assert "comma_semantic_b1_crt_column_block_lookup_node_key" in lookup_cache
    assert "fun lookup_tree cid ct" not in source
    assert "fun lookup_value cid" in source
    assert "Comma_Entry_Arithmetic.natural_context ctxt" in source
    assert "fun controlled_lookup ctxt numeral_context lookup_rules visits" in source
    controlled_lookup = source.split("fun controlled_lookup", 1)[1].split(
        "fun make_template_projection", 1
    )[0]
    assert "Conv.rewrs_conv lookup_rules" in controlled_lookup
    assert "fun choose_if ct" in source
    assert "fun open_selected_block ct" in source
    assert "Conv.rewrs_conv lookup_rules (Thm.rhs_of opened)" in source
    assert "fun make_directory ctxt numeral_context capacity" in lookup_cache
    assert "#lookup directory_lookup_cache" in source
    assert "val lookup_step = #lookup interval_lookup_cache lookup_visits" in source
    assert "selected_block" in source
    assert "#base selected_block" in source and "#extent selected_block" in source
    assert "val expected = shallow_body cid" in source
    assert "val expected_value = Const" in source
    assert "selected column block returned another node payload" in source
    assert "lhs aconv request andalso rhs aconv expected" in source
    assert 'certify_derived_theorem "B1 one-node column unfolding" theorem' in source
    assert "null (Thm.tpairs_of theorem)" in source

    directory = lookup_cache.split("fun make_directory", 1)[1]
    assert "actual_block aconv block_constant" in directory
    assert (
        "actual_dag aconv dag_constant andalso actual_cid aconv cid_term" in directory
    )
    assert "pointer_eq (block_definition, #definition state)" in directory
    assert "column_dag_lookup_interval_left" in directory
    assert "column_dag_lookup_interval_right" in directory
    assert "column_dag_lookup_interval_block" in directory
    assert "selected block interval straddles a directory split" in directory
    assert directory.index("base <= cid andalso cid < upper") < directory.index(
        "val universal = interval_fact"
    )
    key = directory.split("fun interval_key", 1)[1].split("type directory_state", 1)[0]
    assert "dag_body" not in key and "block_body" not in key
    interval_lookup = lookup_cache.split("fun lookup visits block_constant", 1)[
        1
    ].split("fun counters ()", 1)[0]
    assert "extent > 0 andalso extent <= 512" in interval_lookup
    assert "base <= cid andalso cid < upper" in interval_lookup
    assert "actual_block aconv block_constant" in interval_lookup
    assert interval_lookup.index("base <= cid andalso cid < upper") < (
        interval_lookup.index("val block_state = state_for")
    )
    child_derivation = lookup_cache.split("fun derive_child state", 1)[1].split(
        "fun point_from_interval", 1
    )[0]
    assert 'if side = "left" then lower else key + 1' in child_derivation
    assert 'if side = "left" then key else upper' in child_derivation
    assert "interval_key child_lower child_upper" in child_derivation
    assert child_derivation.index("Termtab.lookup") < child_derivation.index(
        "val theorem = rule OF"
    )
    assert "clean theorem" in child_derivation
    walk = interval_lookup.split("fun walk lower upper", 1)[1].split(
        "val result = walk base upper", 1
    )[0]
    assert "else if cid < key" in walk
    assert 'left right "left"\n                      in walk lower key' in walk
    assert 'left right "right"\n                      in walk (key + 1)' in walk
    assert walk.index("else if cid < key") < walk.index(
        'left right "left"\n                      in walk lower key'
    )
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
    lookup_regression = _column_source("semantic_b1_column_lookup_regression.ML")
    for fixture in (
        "check_controlled_lookup",
        "check_mixed_directory_shape",
        "check_directory_interval_cache",
    ):
        assert f"fun {fixture} ctxt" in lookup_regression
        assert f"Comma_Semantic_B1_Column_Lookup_Regression.{fixture}" in regression
    assert "second_nodes = first_nodes" in lookup_regression
    assert "final_retained = 1" in lookup_regression
    assert '"foreign DAG directory cache authority"' in lookup_regression
    assert '"changed directory block authority"' in lookup_regression
    assert '"changed directory block interval"' in lookup_regression
    assert "Comma_Semantic_B1_Column_Catalog.directory_shape" in lookup_regression
    assert "Comma_Semantic_B1_Column_Catalog.Directory_Branch" in lookup_regression
    assert "Comma_Semantic_B1_Column_Catalog.Directory_Block" in lookup_regression
    assert "fun check_generic_fixtures ctxt" in regression
    assert "Conversion.normalize_lookup_rules ctxt" in lookup_regression
    assert (
        '@{term "comma_semantic_b1_crt_template_column_ids ! index"}' not in regression
    )
    assert "!visits = 4" in lookup_regression
    assert "malformed_directory" in lookup_regression
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
    assert (
        publication_theory.index('ML_file "semantic_b1_column_conversion.ML"')
        < publication_theory.index('ML_file "semantic_b1_column_lookup_regression.ML"')
        < publication_theory.index('ML_file "semantic_b1_column_regression.ML"')
    )
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
    assert "nth_row $ selected_source $ nat 0" in regression
    assert "Construction_Piece_Projection.make_with_catalogue" in regression
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
    assert "concatenate $" in piece_root
    assert 'lookup_global_constant "piece-source directory" constants' in piece_root
    assert "construction_piece_source_blocks_name" in piece_root
    assert "construction_piece_source_block_size = 32" in source
    piece_projection = _column_source("semantic_b1_construction_piece_projection.ML")
    assert "blocks are foreign, missing, or reordered" in piece_projection
    assert "actual_source_extents = child_row_extents" in piece_projection
    assert "catalogue contains a noncanonical definition" in piece_projection
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
    zipper = (root / "semantic_b1_labelled_zip.ML").read_text(encoding="utf-8")
    projection = (root / "semantic_b1_template_row_projection.ML").read_text(
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
    assert "Comma_Semantic_B1_Labelled_Zip.make ctxt" in checker
    assert "make_template_partition_profile ()" in checker
    assert "make_template_partition_checker_with_state" in partition
    assert "resolved_fact" in projection
    assert "comma_semantic_b1_crt_column_ids_resolve_columns_for" in projection
    assert "Thm_Deps.all_oracles" not in zipper
    assert "state_work_summary" in projection
    assert "val template_partition_profile =" in checker
    assert "make_template_partition_profile ()" in checker
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
    zipper = _column_source("semantic_b1_labelled_zip.ML")
    projection = _column_source("semantic_b1_template_row_projection.ML")
    fixtures = _column_source("semantic_b1_certificate_store_fixtures.ML")
    geometry = construction.split("fun prove_template_geometry_certificate", 1)[
        1
    ].split("val occurrence_cache_arithmetic_rules", 1)[0]
    assert "prove_partition_checker" in geometry
    assert "Simplifier.rewrite context checker_ct" not in geometry
    assert "prove_partition_checker = prove_partition_checker" in cache
    assert "Comma_Semantic_B1_Labelled_Zip.make ctxt" in cache
    assert "make_template_partition_checker_with_state" in converter
    assert "fun make ctxt" in projection
    assert "val template_partition_profile =" in cache
    assert "make_template_partition_profile ()" in cache
    vector = zipper.split("val (targets, vector_fact) =", 1)[1].split(
        "val child_fact = build (level + 1) targets", 1
    )[0]
    # Parent-state lookup stays first. Exact common suffixes now have a separate
    # proof owner; the retired whole-vector cache could never hit here.
    assert "Vector_Key" not in zipper
    assert "Comma_Semantic_B1_Vector_Suffix_Cache.make ctxt" in zipper
    assert "val vector_request" in vector
    assert "distinct (op =) inputs" in vector
    assert "prove_vector_map" in vector
    assert 'check_equation "vector cofactor"' in vector
    suffix = _column_source("semantic_b1_vector_suffix_cache.ML")
    assert "Simplifier.rewrite" not in suffix
    assert "scan (rev source_ids) n root" in suffix
    assert "Inttab.lookup (!children) cid" in suffix
    assert 'check_equation "column transition"' in suffix
    assert 'check_equation "cached vector suffix"' in suffix
    assert "owner aconv dag" in suffix
    assert "column aconv column_value cid" in suffix
    assert "!nodes < cache_limit" in suffix
    assert "Thm.dest_comb source" in suffix
    assert "Thm.transitive map_fact" in suffix
    assert "Thm.combination head_fact tail_fact" in suffix
    assert "target_cid :: tail_ids" in suffix
    insertion = suffix.split("fun put node theorem =", 1)[1].split("fun root_for", 1)[0]
    assert "check_equation" not in insertion
    assert "labelled_zip_vector_suffix_trie_nodes" in suffix
    assert "prefix_steps = swap_at + 2" in suffix
    assert "!cons_steps = warm_steps" in suffix
    assert "B1 permuted vector alias missed its exact shared suffix" in suffix
    assert "B1 warm vector alias rebuilt structural map work" in suffix
    assert "val result = Exn.capture run ()" in suffix
    assert "cache := saved_cache" in suffix
    assert "Exn.release result" in suffix
    state = zipper.split("and build_compact level ids =", 1)[1].split(
        "fun prove_root_checker ids =", 1
    )[0]
    assert "State_Key.lookup (!state_cache) state_key" in state
    assert state.index("State_Key.lookup (!state_cache)") < state.index(
        "val columns = literal_columns ids"
    )
    assert 'check_theorem "cached witness"' not in state
    assert "val state_key = (level, key_ids)" in state
    assert "(state_key, (ids, theorem))" in state
    assert state.index("requested_cache ()") < state.index("owner_cache ()")
    cold = state.split("val columns = literal_columns ids", 1)[1].split(
        "fun warm_child_permutation_fixture", 1
    )[0]
    assert "transport_state_witness" not in cold
    assert "(int list * thm) State_Key.table" in zipper
    assert "transport_state_witness level source_ids ids source_theorem" in state
    permutation = _column_source("semantic_b1_permutation_cache.ML")
    assert "comma_semantic_b1_crt_partition_witness_mset" in permutation
    assert "val key = (source_ids, target_ids)" in permutation
    assert "sort int_ord source_ids = sort int_ord target_ids" in permutation
    assert "B1 requested state changed occurrence multiplicity" in permutation
    assert "Comma_Entry_Arithmetic.make_certifier ctxt" in permutation
    assert "Thm_Deps.all_oracles" not in permutation
    assert (
        'check_theorem "numeric occurrence multiset" numeric_proposition' in permutation
    )
    assert 'check_theorem "exact mapped occurrence multiset"' in permutation
    assert 'check_theorem "multiset-rebased compact state witness"' in permutation
    assert "mset.simps add_mset_commute" in permutation
    assert "mset_map" in permutation
    assert "State_Key.lookup (!certificate_cache) key" in permutation
    assert "numeric_projection_rules" not in permutation
    assert "upt_rec" not in permutation
    assert "fun check_fixtures ctxt" in permutation
    assert "[2, 1, 2, 0]" in permutation
    assert "[0, 2, 2, 1]" in permutation
    assert "[0, 2, 1, 1]" in permutation
    assert "[1, 2, 0, 2]" in permutation
    assert "B1 multiset fixture conflated source-order cache keys" in permutation
    assert (
        "B1 identity fixture accepted a theorem with an open assumption" in permutation
    )
    assert "B1 identity fixture accepted a wrong-level or TrueI theorem" in permutation
    assert (
        "B1 multiset fixture accepted a malformed literal-column callback"
        in permutation
    )
    assert "permutation_certificate_builds ()" in zipper
    assert "permutation_transport_count ()" in zipper
    assert "fun canonical_key_ids level ids" in zipper
    assert "if level = 0 then ids" in zipper
    assert "B1 root warm-owner fixture unexpectedly used an order transport" in zipper
    assert "B1 warm child replay rebuilt its permutation certificate" in zipper
    assert "warm_owner_fixture ids witness" in zipper
    assert "!child_permutation_fixture_runs > 0" in zipper
    # The legacy checker is now a lazy fallback; if constructed, its complete
    # fixtures still run before publication of the checked occurrence data.
    assert "labelled_zipper_fixtures := SOME (#check_complete_fixtures zipper)" in cache
    assert "case !labelled_zipper_fixtures of" in cache
    assert "SOME check => check ()" in cache
    assert "B1 warm raw-owner fixture performed cold owner/compression work" in zipper
    assert "B1 warm raw-owner fixture did not hit compact owner state" in zipper
    assert "B1 warm raw-owner fixture missed its embedding cache" in zipper
    assert "B1 warm raw-owner fixture did not count its selector lift" in zipper
    raw = zipper.split("fun build level raw_ids =", 1)[1].split(
        "and build_compact level ids =", 1
    )[0]
    assert raw.index("compress_indexed_labels raw_ids") < raw.index(
        "build_compact level compact_ids"
    )
    assert "comma_semantic_b1_crt_partition_witness_lift" in raw
    assert 'check_theorem "lifted raw state witness"' in raw
    embedding_cache = _column_source("semantic_b1_indexed_labels.ML")
    assert "type key = int list" in embedding_cache
    assert "comma_semantic_b1_crt_indexed_mask_embedding" in embedding_cache
    assert "step 0" in embedding_cache
    assert "step cid" not in embedding_cache
    assert "indexed_nonfalse_from" not in embedding_cache
    assert "prove_nonfalse_from_step" not in embedding_cache
    lookup = embedding_cache.split("fun compress raw_ids =", 1)[1]
    assert lookup.index("Embedding_Key.lookup") < lookup.index(
        "compression_embedding_uncached raw_ids"
    )
    assert "Embedding_Key.size (!embedding_cache) < cache_limit" in lookup
    assert "comma_semantic_b1_crt_column_ids_resolve_columns_for" in projection
    assert "resolved_fact" in projection
    assert "comma_semantic_b1_crt_partition_witness_node" in zipper
    child_proof = zipper.split("fun child_branch_fact", 1)[1].split(
        "val child_list_fact", 1
    )[0]
    assert "Thm.beta_conversion false" in child_proof
    assert "child_predicate $ number digit" in child_proof
    assert "selector_context" not in child_proof
    assert "finite child existence witnesses" in zipper
    assert "thm State_Key.table" in zipper
    assert "selector_and_theorem" not in zipper
    assert "children $ Bound 0" not in zipper
    # The common publication check remains authoritative after removal of
    # duplicate branch-local full-selector comparisons.
    assert 'check_theorem "new witness" proposition' in zipper
    checker_bridge = zipper.split("val checker_true =", 1)[1].split("val levels =", 1)[
        0
    ]
    assert "comma_semantic_b1_crt_partition_witness_checker_true" in checker_bridge
    assert "RS @{thm eq_reflection}" in checker_bridge
    assert "fun reject_unless_interrupted failure" in zipper
    assert "Exn.is_interrupt failure" in zipper
    assert zipper.count("reject_unless_interrupted failure") == 3
    assert "column_index_equation" not in zipper
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
    assert "Comma_Entry_Arithmetic.make_certifier ctxt" in store


def test_projection_and_lookup_checks_preserve_exact_authority_without_goal_replay() -> (
    None
):
    projection = _column_source("semantic_b1_template_projection.ML")
    assert "Comma_Entry_Arithmetic.make_certifier ctxt" in projection
    validation = projection.split("fun validate_projection", 1)[1].split(
        "fun compose_cached_projection", 1
    )[0]
    assert "Thm.term_of (Thm.lhs_of theorem) aconv request" in validation
    assert "oracle_free theorem" in validation
    assert "forall canonical_column entries" in validation
    assert "Thm_Deps.all_oracles" not in validation
    lookup = _column_source("semantic_b1_column_lookup_cache.ML")
    bound = lookup.split("fun natural_bound ctxt", 1)[1].split("fun make ctxt", 1)[0]
    assert "Goal.prove" not in bound
    assert "closed proposition" in bound
    assert "Thm.term_of (Thm.lhs_of equation) aconv proposition" in bound
    assert "Thm.term_of (Thm.rhs_of equation) aconv @{term True}" in bound
    fixtures = _column_source("semantic_b1_column_lookup_regression.ML")
    assert '"false scalar interval bound"' in fixtures
