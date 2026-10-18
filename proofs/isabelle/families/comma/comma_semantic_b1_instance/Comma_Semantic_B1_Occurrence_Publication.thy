theory Comma_Semantic_B1_Occurrence_Publication
  imports "HOL-Library.Multiset" Comma_Semantic_B1_Occurrence_Arithmetic
    Comma_Semantic_B1.Comma_Semantic_B1_CRT_Construction_Binding
    Comma_Semantic_B1.Comma_Semantic_B1_CRT_Column_Lookup
    Comma_Semantic_B1.Comma_Semantic_B1_CRT_Mass_Transport
    Comma_Semantic_B1.Comma_Semantic_B1_CRT_Mass_Layout
    Comma_Semantic_B1.Comma_Semantic_B1_CRT_Constructor_Mass
    Comma_Semantic_B1.Comma_Semantic_B1_CRT_Compact_Mass
begin
ML_file "../comma_entry_arithmetic/selected_list_conversion.ML"
ML_file "semantic_b1_term_lru.ML"
ML_file "semantic_b1_column_lookup_cache.ML"
ML_file "semantic_b1_source_column_normalizer.ML"
ML \<open>Comma_Semantic_B1_Source_Column_Normalizer.check_digit_equation_cache @{context}\<close>
ML_file "semantic_b1_crt_apply_shortcut_fixture.ML"
ML_file "semantic_b1_crt_apply_dag_production_fixture.ML"
ML_file "semantic_b1_crt_apply_shortcuts.ML"
ML_file "semantic_b1_shift_quotient.ML"
ML_file "semantic_b1_right_shift_quotient.ML"
ML_file "semantic_b1_apply_clock_quotient.ML"
ML_file "semantic_b1_crt_apply_dag.ML"
ML_file "semantic_b1_apply_clock_dag_fixture.ML"
ML \<open>Comma_Semantic_B1_Apply_Clock_DAG_Fixture.check @{context}\<close>
ML_file "semantic_b1_crt_operation_conversion.ML"
ML \<open>
  val fixture_authority: Comma_Semantic_B1_CRT_Apply_DAG.column_authority =
    {known_column = K false,
     column_id = K NONE,
     column_value = (fn _ => error "literal apply fixture requested a column"),
     cofactor_node_level = K NONE,
     prove_admitted = (fn _ => error "literal apply fixture requested admission"),
     resolve_column = K NONE,
     cofactor_transition = (fn _ => error "literal apply fixture requested a cofactor"),
     reify_column = Thm.reflexive}
  val _ = #check_fixtures
    (Comma_Semantic_B1_CRT_Apply_DAG.make @{context} fixture_authority) ()
\<close>
ML_file "semantic_b1_template_projection.ML"
ML_file "semantic_b1_column_catalog.ML"
ML_file "semantic_b1_column_conversion.ML"
ML_file "semantic_b1_mass_layout.ML"
ML_file "semantic_b1_mass_source_rows.ML"
ML_file "semantic_b1_mass_rows.ML"
ML \<open>Comma_Semantic_B1_Mass_Layout.fixture @{context}\<close>
ML_file "semantic_b1_permutation_cache.ML"
ML \<open>Comma_Semantic_B1_Permutation_Cache.check_fixtures @{context}\<close>
text \<open>The candidate constructor and its bounded rebase/binding examples
belong to this concrete publisher. Generic theories do not load candidate code.
Admission still requires the checked occurrence certificate below.\<close>
ML_file "semantic_b1_mdd.ML"
ML_file "semantic_b1_template_constructor.ML"
ML_file "semantic_b1_mass_candidate.ML"
ML_file "semantic_b1_occurrence_publication.ML"
ML_file "semantic_b1_publication_fixtures.ML"
ML \<open>Comma_Semantic_B1_Publication_Fixtures.check_selected_list @{context}\<close>
ML_file "semantic_b1_lift_column_projection.ML"
ML_file "semantic_b1_column_lookup_regression.ML"
ML_file "semantic_b1_column_regression.ML"
ML \<open>Comma_Semantic_B1_Column_Regression.check_generic_fixtures @{context}\<close>
ML \<open>Comma_Semantic_B1_Publication_Fixtures.check_candidate @{context}\<close>

local_setup \<open>Comma_Semantic_B1_Occurrence_Publication.publish\<close>
ML_file "semantic_b1_mass_alias.ML"
ML_file "semantic_b1_column_mass_invariant.ML"
ML_file "semantic_b1_column_mass.ML"
ML \<open>let val columns = Comma_Semantic_B1_Column_Regression.check @{context} in Comma_Semantic_B1_Column_Mass_Invariant.check_source_binding_authority @{context} (#node_count columns) (#source_bindings columns) end\<close>
definition comma_semantic_b1_crt_occurrence_at_index ::
    "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option" where
  "comma_semantic_b1_crt_occurrence_at_index index =
    (if index < length comma_semantic_b1_crt_descriptors then
       comma_semantic_b1_crt_resolve_descriptor comma_semantic_b1_crt_templates
         (comma_semantic_b1_crt_descriptors ! index)
     else None)"

definition comma_semantic_b1_crt_construction_check :: "nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_construction_check index \<longleftrightarrow>
    comma_semantic_b1_crt_compact_occurrence_check
      comma_semantic_b1_crt_templates comma_semantic_b1_crt_sources
      comma_semantic_b1_crt_occurrence_at_index
      comma_semantic_b1_crt_descriptors comma_semantic_b1_crt_lift_refs
      comma_semantic_b1_crt_lift_descriptors index"

abbreviation comma_semantic_b1_crt_source_occurrence_bound :: "nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_source_occurrence_bound index \<equiv>
    comma_semantic_b1_crt_construction_check index"

definition comma_semantic_b1_crt_used_lift_bindings_checked :: bool where
  "comma_semantic_b1_crt_used_lift_bindings_checked \<longleftrightarrow>
    list_all (comma_semantic_b1_crt_lift_binding_certified
      comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
      comma_semantic_b1_crt_lift_column_ids comma_semantic_b1_crt_lift_descriptors)
      (comma_semantic_b1_crt_used_lift_cids comma_semantic_b1_crt_lift_refs)"

definition comma_semantic_b1_crt_source_index ::
    "(comma_finite_position \<times> nat) list" where
  "comma_semantic_b1_crt_source_index =
    zip comma_semantic_b1_crt_sources [0..<length comma_semantic_b1_crt_sources]"

definition comma_semantic_b1_crt_source_index_for ::
    "comma_finite_position \<Rightarrow> nat option" where
  "comma_semantic_b1_crt_source_index_for source =
    map_option snd (List.find (\<lambda>entry. fst entry = source)
      comma_semantic_b1_crt_source_index)"

definition comma_semantic_b1_crt_source_order_key ::
    "comma_finite_position \<Rightarrow> nat" where
  "comma_semantic_b1_crt_source_order_key source =
    (case source of
       Comma_Entry f delta offset \<Rightarrow> (9 - f) * 1024 + offset
     | Comma_Near f delta headroom \<Rightarrow>
         (9 - f) * 1024 + 100 + headroom)"

definition comma_semantic_b1_crt_source_order_step :: "nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_source_order_step index \<longleftrightarrow>
    Suc index < length comma_semantic_b1_crt_sources \<longrightarrow>
    comma_semantic_b1_crt_source_order_key
        (comma_semantic_b1_crt_sources ! index) <
      comma_semantic_b1_crt_source_order_key
        (comma_semantic_b1_crt_sources ! Suc index)"

definition comma_semantic_b1_crt_published ::
    "comma_finite_position \<Rightarrow> comma_semantic_b1_crt_occurrence option" where
  "comma_semantic_b1_crt_published source =
    (case comma_semantic_b1_crt_source_index_for source of
       None \<Rightarrow> None
     | Some index \<Rightarrow> comma_semantic_b1_crt_occurrence_at_index index)"

definition comma_semantic_b1_crt_root_occurrence ::
    "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option" where
  "comma_semantic_b1_crt_root_occurrence root =
    (if root < length comma_semantic_b1_crt_root_occurrence_indices then
       comma_semantic_b1_crt_occurrence_at_index
         (comma_semantic_b1_crt_root_occurrence_indices ! root)
     else None)"

definition comma_semantic_b1_crt_root_entry_checked :: "nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_root_entry_checked root =
    (if root < 46 \<and>
        root < length comma_semantic_b1_crt_root_occurrence_indices then
       let source = Comma_Entry 1 0 (comma_offset_representatives ! root);
           index = comma_semantic_b1_crt_root_occurrence_indices ! root
       in index < length comma_semantic_b1_crt_sources \<and>
          index < length comma_semantic_b1_crt_descriptors \<and>
          index < length comma_semantic_b1_crt_lift_refs \<and>
          comma_semantic_b1_crt_sources ! index = source \<and>
          (case comma_semantic_b1_crt_occurrence_at_index index of
             None \<Rightarrow> False
           | Some _ \<Rightarrow> True)
     else False)"

definition comma_semantic_b1_crt_occurrence_data_checked :: bool where
  "comma_semantic_b1_crt_occurrence_data_checked \<longleftrightarrow>
     length comma_semantic_b1_crt_sources =
       length comma_semantic_b1_crt_descriptors \<and>
     length comma_semantic_b1_crt_lift_refs =
       length comma_semantic_b1_crt_sources \<and>
     length comma_semantic_b1_crt_sources \<le> 1024 \<and>
     length comma_semantic_b1_crt_templates \<le> 1024 \<and>
     length comma_semantic_b1_crt_lift_descriptors \<le>
       28 * length comma_semantic_b1_crt_sources \<and>
     list_all comma_semantic_b1_crt_source_order_step
       [0..<length comma_semantic_b1_crt_sources - 1] \<and>
     list_all (comma_crt_admitted 0) comma_semantic_b1_crt_columns \<and>
     comma_semantic_b1_crt_used_lift_bindings_checked \<and>
     list_all (comma_semantic_b1_crt_template_mass_certified
         comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
         comma_semantic_b1_crt_template_column_ids)
       (remdups (map fst comma_semantic_b1_crt_descriptors)) \<and>
     list_all comma_semantic_b1_crt_construction_check
       [0..<length comma_semantic_b1_crt_sources] \<and>
     length comma_semantic_b1_crt_root_occurrence_indices = 46 \<and>
     list_all comma_semantic_b1_crt_root_entry_checked [0..<46]"

lemma comma_semantic_b1_crt_source_order_steps_sorted:
  assumes steps:
    "list_all comma_semantic_b1_crt_source_order_step
      [0..<length comma_semantic_b1_crt_sources - 1]"
  shows "sorted_wrt (<) (map comma_semantic_b1_crt_source_order_key
    comma_semantic_b1_crt_sources)"
proof -
  have adjacent:
    "\<forall>index. Suc index < length comma_semantic_b1_crt_sources \<longrightarrow>
      comma_semantic_b1_crt_source_order_key
        (comma_semantic_b1_crt_sources ! index) <
      comma_semantic_b1_crt_source_order_key
        (comma_semantic_b1_crt_sources ! Suc index)"
  proof (intro allI impI)
    fix index
    assume bound: "Suc index < length comma_semantic_b1_crt_sources"
    have member: "index \<in> set [0..<length comma_semantic_b1_crt_sources - 1]"
      using bound by auto
    have step: "comma_semantic_b1_crt_source_order_step index"
      using steps member by (auto simp: list_all_iff)
    show "comma_semantic_b1_crt_source_order_key
        (comma_semantic_b1_crt_sources ! index) <
      comma_semantic_b1_crt_source_order_key
        (comma_semantic_b1_crt_sources ! Suc index)"
      using step bound
      by (simp add: comma_semantic_b1_crt_source_order_step_def)
  qed
  have trans: "transp ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)"
    by (rule transpI) auto
  show ?thesis
    using adjacent trans
    by (simp add: sorted_wrt_iff_nth_Suc_transp)
qed

lemma comma_semantic_b1_crt_source_order_distinct:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
  shows "distinct comma_semantic_b1_crt_sources"
proof -
  have steps:
    "list_all comma_semantic_b1_crt_source_order_step
      [0..<length comma_semantic_b1_crt_sources - 1]"
    using checked
    unfolding comma_semantic_b1_crt_occurrence_data_checked_def
    by blast
  have sorted:
    "sorted_wrt (<) (map comma_semantic_b1_crt_source_order_key
      comma_semantic_b1_crt_sources)"
    by (rule comma_semantic_b1_crt_source_order_steps_sorted[OF steps])
  have key_distinct:
    "distinct (map comma_semantic_b1_crt_source_order_key
      comma_semantic_b1_crt_sources)"
    using sorted
    by (simp add: strict_sorted_iff)
  show ?thesis
    using key_distinct by (simp add: distinct_map)
qed

lemma comma_semantic_b1_crt_source_order_rejects_equal_adjacent_keys:
  assumes bound: "Suc index < length comma_semantic_b1_crt_sources"
    and equal:
      "comma_semantic_b1_crt_source_order_key
          (comma_semantic_b1_crt_sources ! index) =
        comma_semantic_b1_crt_source_order_key
          (comma_semantic_b1_crt_sources ! Suc index)"
  shows "\<not> comma_semantic_b1_crt_source_order_step index"
  using bound equal
  by (simp add: comma_semantic_b1_crt_source_order_step_def)

ML_file "semantic_b1_partition_support.ML"
ML_file "semantic_b1_template_row_projection.ML"
ML_file "semantic_b1_partition_conversion.ML"
ML_file "semantic_b1_indexed_labels.ML"
ML_file "semantic_b1_vector_suffix_cache.ML"
ML_file "semantic_b1_labelled_zip.ML"
ML_file "semantic_b1_construction_check.ML"
ML_file "semantic_b1_used_templates.ML"
ML_file "semantic_b1_certificate_store.ML"
ML_file "semantic_b1_template_mass_check.ML"
ML \<open>Comma_Semantic_B1_Construction_Check.check_helper_fixtures @{context}\<close>
ML_file "semantic_b1_certificate_store_action_fixtures.ML"
ML_file "semantic_b1_certificate_store_fixtures.ML"
ML_file "semantic_b1_occurrence_check_cache.ML"
(* Exercise the bounded list_all proof assembler before the concrete
   occurrence certificate.  The first call checks a nonempty range; the
   second supplies a valid proof at the wrong index and must be rejected by
   exact proposition matching. *)
ML \<open>
  local
    val ctxt = @{context}
    val natT = @{typ nat}
    val boolT = @{typ bool}
    val nat_listT = @{typ "nat list"}
    fun numeral n = HOLogic.mk_number natT n
    val successor_cache = Comma_Selected_List_Conversion.make_successor_cache ctxt 3
    val predicate = Const (@{const_name less_eq}, natT --> natT --> boolT) $
      numeral 0
    fun item_at index =
      Goal.prove ctxt [] [] (HOLogic.mk_Trueprop (predicate $ numeral index))
        (fn {context, ...} =>
          simp_tac (Comma_Entry_Arithmetic.natural_context context) 1)
    val positive =
      Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt = ctxt, predicate = predicate, bound = 3,
         prove_item = item_at,
         zero_fact = @{thm comma_indexed_all_zero},
         step_fact = @{thm comma_indexed_all_Suc},
         successor_equation = #equation successor_cache}
    val list_all = Const (@{const_name list_all},
      (natT --> boolT) --> nat_listT --> boolT)
    val upt = Const (@{const_name upt}, natT --> natT --> nat_listT)
    val expected = HOLogic.mk_Trueprop
      (list_all $ predicate $ (upt $ numeral 0 $ numeral 3))
    val _ = if Thm.prop_of positive aconv expected andalso
        Thm.nprems_of positive = 0 andalso null (Thm.hyps_of positive) andalso
        null (Thm.tpairs_of positive)
      then () else error "Indexed list_all positive fixture returned the wrong theorem"
    val _ = Thm.consolidate [positive]
    val wrong_index = Exn.capture (fn () =>
      Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt = ctxt, predicate = predicate, bound = 3,
         prove_item = fn index => item_at (index + 1),
         zero_fact = @{thm comma_indexed_all_zero},
         step_fact = @{thm comma_indexed_all_Suc},
         successor_equation = #equation successor_cache}) ()
    val _ = (case wrong_index of
        Exn.Exn (ERROR message) =>
          if message = "Indexed list_all item proof has the wrong proposition"
          then () else error message
      | Exn.Exn exn => Exn.reraise exn
      | Exn.Res _ => error "Indexed list_all accepted an item theorem for the wrong index")
  in
    val _ = ()
  end
\<close>
ML \<open>
  val comma_semantic_b1_occurrence_certificate_started = Time.now ()
  val _ = Comma_Proof_Profile.report
    "B1 occurrence certificate stage=before-concrete-check"
\<close>

lemma comma_semantic_b1_crt_occurrence_data_checked:
  "comma_semantic_b1_crt_occurrence_data_checked"
  by comma_semantic_b1_occurrence_check

ML \<open>
  val _ = Thm.consolidate [@{thm comma_semantic_b1_crt_occurrence_data_checked}]
  val _ = Comma_Proof_Profile.report
    ("B1 occurrence certificate stage=after-concrete-check elapsed_ms=" ^
      Comma_Proof_Profile.elapsed_ms comma_semantic_b1_occurrence_certificate_started)
\<close>

lemma comma_semantic_b1_crt_find_source_member:
  assumes found:
    "List.find (\<lambda>entry. fst entry = source)
       comma_semantic_b1_crt_source_index = Some entry"
  shows "entry \<in> set comma_semantic_b1_crt_source_index \<and>
    fst entry = source"
  using found
  by (auto simp: find_Some_iff dest: nth_mem)

lemma comma_semantic_b1_crt_construction_check_at:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and index: "index < length comma_semantic_b1_crt_sources"
  shows "comma_semantic_b1_crt_construction_check index"
proof -
  have constructions:
    "list_all comma_semantic_b1_crt_construction_check
      [0..<length comma_semantic_b1_crt_sources]"
    using checked
    unfolding comma_semantic_b1_crt_occurrence_data_checked_def
    by blast
  show ?thesis using constructions index by (auto simp: list_all_iff)
qed

lemma comma_semantic_b1_crt_checked_bounds_and_geometry:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
  shows bounds:
      "list_all comma_semantic_b1_crt_source_occurrence_bound
        [0..<length comma_semantic_b1_crt_sources]"
    and parent_template_geometries:
      "\<And>index. index<length comma_semantic_b1_crt_sources \<Longrightarrow>
        comma_semantic_b1_crt_template_geometry_certified
          comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
          comma_semantic_b1_crt_template_column_ids
          (fst (comma_semantic_b1_crt_descriptors!index))"
    and all_occurrences_wellformed:
      "\<forall>index<length comma_semantic_b1_crt_sources. \<forall>parent.
        comma_semantic_b1_crt_occurrence_at_index index=Some parent \<longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed parent"
proof -
  have checks: "list_all comma_semantic_b1_crt_construction_check
      [0..<length comma_semantic_b1_crt_sources]"
    using checked unfolding comma_semantic_b1_crt_occurrence_data_checked_def
    by blast
  have bounds_fact: "list_all comma_semantic_b1_crt_source_occurrence_bound
      [0..<length comma_semantic_b1_crt_sources]"
    using checks
    by (simp only: list_all_iff comma_semantic_b1_crt_construction_check_def)
  have occurrence_checks:
      "list_all (comma_semantic_b1_crt_compact_occurrence_check
        comma_semantic_b1_crt_templates comma_semantic_b1_crt_sources
        comma_semantic_b1_crt_occurrence_at_index comma_semantic_b1_crt_descriptors
        comma_semantic_b1_crt_lift_refs comma_semantic_b1_crt_lift_descriptors)
        [0..<length comma_semantic_b1_crt_sources]"
    using checks by (simp only: list_all_iff comma_semantic_b1_crt_construction_check_def)
  have template_masses:
      "list_all (comma_semantic_b1_crt_template_mass_certified
        comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
        comma_semantic_b1_crt_template_column_ids)
        (remdups (map fst comma_semantic_b1_crt_descriptors))"
    using checked unfolding comma_semantic_b1_crt_occurrence_data_checked_def by blast
  have table_admitted:
      "list_all (comma_crt_admitted 0) comma_semantic_b1_crt_columns"
    using checked unfolding comma_semantic_b1_crt_occurrence_data_checked_def by blast
  have descriptor_extent:
      "length comma_semantic_b1_crt_descriptors = length comma_semantic_b1_crt_sources"
    using checked unfolding comma_semantic_b1_crt_occurrence_data_checked_def by blast
  have parent_mass:
      "\<And>index. index<length comma_semantic_b1_crt_sources \<Longrightarrow>
        comma_semantic_b1_crt_template_mass_certified
          comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
          comma_semantic_b1_crt_template_column_ids
          (fst (comma_semantic_b1_crt_descriptors!index))"
    by (rule comma_semantic_b1_crt_used_template_masses_cover_sources
      [OF descriptor_extent template_masses])
  have parent_wellformed:
      "\<forall>index<length comma_semantic_b1_crt_sources. \<forall>parent.
        comma_semantic_b1_crt_occurrence_at_index index=Some parent \<longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed parent"
    by (rule comma_semantic_b1_crt_compact_occurrences_wellformed_from_mass
      [OF table_admitted descriptor_extent template_masses occurrence_checks])
  have parent_geometry:
      "\<And>index. index<length comma_semantic_b1_crt_sources \<Longrightarrow>
        comma_semantic_b1_crt_template_geometry_certified
          comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
          comma_semantic_b1_crt_template_column_ids
          (fst (comma_semantic_b1_crt_descriptors!index))"
  proof -
    fix index
    assume index: "index<length comma_semantic_b1_crt_sources"
    have check:
        "comma_semantic_b1_crt_compact_occurrence_check comma_semantic_b1_crt_templates
          comma_semantic_b1_crt_sources comma_semantic_b1_crt_occurrence_at_index
          comma_semantic_b1_crt_descriptors comma_semantic_b1_crt_lift_refs
          comma_semantic_b1_crt_lift_descriptors index"
      using occurrence_checks index by (auto simp: list_all_iff)
    obtain parent where occurrence:
        "comma_semantic_b1_crt_occurrence_at_index index=Some parent"
      using comma_semantic_b1_crt_compact_occurrence_check_total[OF check index]
      by blast
    have selected:
        "comma_semantic_b1_crt_occurrence_columns parent =
          comma_semantic_b1_crt_templates ! fst (comma_semantic_b1_crt_descriptors!index)"
      using comma_semantic_b1_crt_compact_occurrence_check_exposes[OF check occurrence]
      by blast
    have wf: "comma_semantic_b1_crt_occurrence_wellformed parent"
      using parent_wellformed index occurrence by blast
    have mass: "comma_semantic_b1_crt_template_mass_certified
        comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
        comma_semantic_b1_crt_template_column_ids
        (fst (comma_semantic_b1_crt_descriptors!index))"
      by (rule parent_mass[OF index])
    have template_bound:
        "fst (comma_semantic_b1_crt_descriptors!index) <
          length comma_semantic_b1_crt_templates"
      and ids_bound:
        "fst (comma_semantic_b1_crt_descriptors!index) <
          length comma_semantic_b1_crt_template_column_ids"
      and resolved:
        "comma_semantic_b1_crt_column_ids_resolve comma_semantic_b1_crt_columns
          (comma_semantic_b1_crt_template_column_ids !
            fst (comma_semantic_b1_crt_descriptors!index))
          (comma_semantic_b1_crt_templates !
            fst (comma_semantic_b1_crt_descriptors!index))"
      using mass unfolding comma_semantic_b1_crt_template_mass_certified_def by blast+
    show "comma_semantic_b1_crt_template_geometry_certified
        comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
        comma_semantic_b1_crt_template_column_ids
        (fst (comma_semantic_b1_crt_descriptors!index))"
      by (rule comma_semantic_b1_crt_template_geometry_from_resolved_wellformed_occurrence
        [OF template_bound ids_bound selected resolved wf])
  qed
  show "list_all comma_semantic_b1_crt_source_occurrence_bound
      [0..<length comma_semantic_b1_crt_sources]"
    by (rule bounds_fact)
  show "\<And>index. index<length comma_semantic_b1_crt_sources \<Longrightarrow>
      comma_semantic_b1_crt_template_geometry_certified
        comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
        comma_semantic_b1_crt_template_column_ids
        (fst (comma_semantic_b1_crt_descriptors!index))"
    by (rule parent_geometry)
  show "\<forall>index<length comma_semantic_b1_crt_sources. \<forall>parent.
      comma_semantic_b1_crt_occurrence_at_index index=Some parent \<longrightarrow>
      comma_semantic_b1_crt_occurrence_wellformed parent"
    by (rule parent_wellformed)
qed

lemma comma_semantic_b1_crt_root_entry_checked_at:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and root: "root<46"
  shows "comma_semantic_b1_crt_root_entry_checked root"
proof -
  have roots: "list_all comma_semantic_b1_crt_root_entry_checked [0..<46]"
    using checked unfolding comma_semantic_b1_crt_occurrence_data_checked_def
    by blast
  show ?thesis using roots root by (simp add: list_all_iff)
qed

lemma comma_semantic_b1_crt_root_entry_resolves_checked:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and root: "root<46"
  obtains index occurrence where
    "comma_semantic_b1_crt_root_occurrence_indices ! root=index"
    "root<length comma_semantic_b1_crt_root_occurrence_indices"
    "index<length comma_semantic_b1_crt_sources"
    "comma_semantic_b1_crt_sources ! index=
      Comma_Entry 1 0 (comma_offset_representatives ! root)"
    "comma_semantic_b1_crt_occurrence_at_index index=Some occurrence"
    "comma_semantic_b1_crt_construction_check index"
proof -
  have root_entry: "comma_semantic_b1_crt_root_entry_checked root"
    by (rule comma_semantic_b1_crt_root_entry_checked_at[OF checked root])
  obtain index occurrence where root_index:
      "comma_semantic_b1_crt_root_occurrence_indices ! root=index"
    and root_bound: "root<length comma_semantic_b1_crt_root_occurrence_indices"
    and index_bound: "index<length comma_semantic_b1_crt_sources"
    and source_at_index:
      "comma_semantic_b1_crt_sources ! index=
        Comma_Entry 1 0 (comma_offset_representatives ! root)"
    and occurrence_at_index:
      "comma_semantic_b1_crt_occurrence_at_index index=Some occurrence"
    using root_entry root
    by (auto simp: comma_semantic_b1_crt_root_entry_checked_def Let_def
      split: option.splits)
  have construction: "comma_semantic_b1_crt_construction_check index"
    by (rule comma_semantic_b1_crt_construction_check_at[OF checked index_bound])
  show thesis
    by (rule that[OF root_index root_bound index_bound source_at_index
      occurrence_at_index construction])
qed

lemma comma_semantic_b1_crt_published_resolves_index:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and index: "index < length comma_semantic_b1_crt_sources"
    and source: "comma_semantic_b1_crt_sources ! index = source"
    and occurrence:
      "comma_semantic_b1_crt_occurrence_at_index index = Some value"
  shows "comma_semantic_b1_crt_published source = Some value"
proof -
  have index_data:
      "comma_semantic_b1_crt_source_index =
        zip comma_semantic_b1_crt_sources [0..<length comma_semantic_b1_crt_sources]"
    by (simp add: comma_semantic_b1_crt_source_index_def)
  have sources_unique: "distinct comma_semantic_b1_crt_sources"
    by (rule comma_semantic_b1_crt_source_order_distinct[OF checked])
  have index_pair:
      "comma_semantic_b1_crt_source_index ! index = (source,index)"
    using source index_data index by simp
  have no_earlier:
      "\<forall>j<index. fst (comma_semantic_b1_crt_source_index ! j) \<noteq> source"
  proof (intro allI impI)
    fix j
    assume j: "j<index"
    have j_bound: "j<length comma_semantic_b1_crt_sources"
      using j index by simp
    assume equal: "fst (comma_semantic_b1_crt_source_index ! j) = source"
    have source_at_j: "comma_semantic_b1_crt_sources ! j=source"
      using equal index_data j_bound by simp
    have equal_positions: "j=index"
      using sources_unique index j_bound index source source_at_j
      by (auto simp: nth_eq_iff_index_eq)
    with j show False by simp
  qed
  have found:
      "List.find (\<lambda>entry. fst entry=source)
        comma_semantic_b1_crt_source_index = Some (source,index)"
    using index_pair no_earlier index_data index
    by (auto simp: find_Some_iff)
  show ?thesis using found occurrence
    by (simp add: comma_semantic_b1_crt_source_index_for_def
      comma_semantic_b1_crt_published_def)
qed

lemma comma_semantic_b1_crt_published_occurrences_wellformed:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
  shows "\<forall>index<length comma_semantic_b1_crt_sources.
    \<forall>parent. comma_semantic_b1_crt_occurrence_at_index index=Some parent
      \<longrightarrow> comma_semantic_b1_crt_occurrence_wellformed parent"
proof -
  have _bounds:
      "list_all comma_semantic_b1_crt_source_occurrence_bound
        [0..<length comma_semantic_b1_crt_sources]"
    and _parents:
      "\<And>index. index<length comma_semantic_b1_crt_sources \<Longrightarrow>
        comma_semantic_b1_crt_template_geometry_certified
          comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
          comma_semantic_b1_crt_template_column_ids
          (fst (comma_semantic_b1_crt_descriptors!index))"
    and all:
      "\<forall>index<length comma_semantic_b1_crt_sources. \<forall>parent.
        comma_semantic_b1_crt_occurrence_at_index index=Some parent \<longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed parent"
    by (rule comma_semantic_b1_crt_checked_bounds_and_geometry[OF checked])
  show ?thesis by (rule all)
qed

lemma comma_semantic_b1_crt_occurrence_at_index_wellformed:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and index: "index < length comma_semantic_b1_crt_sources"
    and occurrence:
      "comma_semantic_b1_crt_occurrence_at_index index = Some value"
  shows "comma_semantic_b1_crt_occurrence_wellformed value"
proof -
  have all:
      "\<forall>index<length comma_semantic_b1_crt_sources.
        \<forall>parent. comma_semantic_b1_crt_occurrence_at_index index=Some parent
          \<longrightarrow> comma_semantic_b1_crt_occurrence_wellformed parent"
    by (rule comma_semantic_b1_crt_published_occurrences_wellformed[OF checked])
  show ?thesis using all index occurrence by blast
qed

lemma comma_semantic_b1_crt_occurrence_at_index_total:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and index: "index < length comma_semantic_b1_crt_sources"
  obtains occ where
    "comma_semantic_b1_crt_occurrence_at_index index = Some occ"
proof -
  have construction: "comma_semantic_b1_crt_construction_check index"
    by (rule comma_semantic_b1_crt_construction_check_at[OF checked index])
  have compact:
      "comma_semantic_b1_crt_compact_occurrence_check comma_semantic_b1_crt_templates
        comma_semantic_b1_crt_sources comma_semantic_b1_crt_occurrence_at_index
        comma_semantic_b1_crt_descriptors comma_semantic_b1_crt_lift_refs
        comma_semantic_b1_crt_lift_descriptors index"
    using construction by (simp add: comma_semantic_b1_crt_construction_check_def)
  have present:
      "\<exists>occ. comma_semantic_b1_crt_occurrence_at_index index=Some occ"
    by (rule comma_semantic_b1_crt_compact_occurrence_check_total
      [OF compact index])
  show thesis
  proof (cases "comma_semantic_b1_crt_occurrence_at_index index")
    case None
    with present show thesis by simp
  next
    case (Some occ)
    then show thesis by (rule that)
  qed
qed

lemma comma_semantic_b1_crt_published_occurrence_index:
  assumes published: "comma_semantic_b1_crt_published source = Some occurrence"
  obtains index where
    "index < length comma_semantic_b1_crt_sources"
    "comma_semantic_b1_crt_sources ! index = source"
    "comma_semantic_b1_crt_occurrence_at_index index = Some occurrence"
proof -
  obtain index where source_index:
      "comma_semantic_b1_crt_source_index_for source = Some index"
    and occurrence_at_index:
      "comma_semantic_b1_crt_occurrence_at_index index = Some occurrence"
    using published
    by (cases "comma_semantic_b1_crt_source_index_for source")
      (auto simp: comma_semantic_b1_crt_published_def)
  obtain entry where found:
      "List.find (\<lambda>entry. fst entry=source)
        comma_semantic_b1_crt_source_index = Some entry"
    and index_entry: "snd entry=index"
    using source_index
    by (auto simp: comma_semantic_b1_crt_source_index_for_def
      split: option.splits prod.splits)
  have member: "entry \<in> set comma_semantic_b1_crt_source_index"
    and source_entry: "fst entry=source"
    using comma_semantic_b1_crt_find_source_member[OF found] by blast+
  have source_index_data:
      "comma_semantic_b1_crt_source_index =
        zip comma_semantic_b1_crt_sources [0..<length comma_semantic_b1_crt_sources]"
    by (simp add: comma_semantic_b1_crt_source_index_def)
  have indexed:
      "\<exists>j<length comma_semantic_b1_crt_sources.
        comma_semantic_b1_crt_sources!j=fst entry \<and>
        [0..<length comma_semantic_b1_crt_sources]!j=snd entry"
    using member source_index_data by (auto simp: in_set_zip)
  then obtain j where j_bound: "j<length comma_semantic_b1_crt_sources"
    and source_at_j: "comma_semantic_b1_crt_sources!j=source"
    and index_at_j: "[0..<length comma_semantic_b1_crt_sources]!j=snd entry"
    using source_entry by blast
  have j_index: "j=index" using index_entry index_at_j j_bound by simp
  have source_at_index: "comma_semantic_b1_crt_sources!index=source"
    using source_at_j j_index by simp
  have index_bound: "index<length comma_semantic_b1_crt_sources"
    using j_bound j_index by simp
  show thesis
    by (rule that[OF index_bound source_at_index occurrence_at_index])
qed

lemma comma_semantic_b1_crt_published_children_resolve_index:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and index: "index < length comma_semantic_b1_crt_sources"
  shows "comma_semantic_b1_crt_published (comma_semantic_b1_crt_sources ! index) =
    comma_semantic_b1_crt_occurrence_at_index index"
proof (cases "comma_semantic_b1_crt_occurrence_at_index index")
  case None
  have total:
      "\<exists>occ. comma_semantic_b1_crt_occurrence_at_index index = Some occ"
    by (rule comma_semantic_b1_crt_occurrence_at_index_total[OF checked index])
  then obtain occ where
      "comma_semantic_b1_crt_occurrence_at_index index = Some occ"
    by blast
  with None show ?thesis by contradiction
next
  case (Some occ)
  show ?thesis
    by (rule comma_semantic_b1_crt_published_resolves_index
      [OF checked index refl Some])
qed

lemma comma_semantic_b1_crt_published_constructed_candidate_matches:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
  shows "\<forall>index<length comma_semantic_b1_crt_sources. \<forall>parent.
    comma_semantic_b1_crt_occurrence_at_index index=Some parent \<longrightarrow>
    comma_semantic_b1_crt_occurrence_candidate_matches
      comma_semantic_b1_crt_published
      (comma_semantic_b1_crt_sources!index) parent"
proof -
  have bounds:
      "list_all comma_semantic_b1_crt_source_occurrence_bound
        [0..<length comma_semantic_b1_crt_sources]"
    and parent_template_geometries:
      "\<And>index. index<length comma_semantic_b1_crt_sources \<Longrightarrow>
        comma_semantic_b1_crt_template_geometry_certified
          comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
          comma_semantic_b1_crt_template_column_ids
          (fst (comma_semantic_b1_crt_descriptors!index))"
    by (rule comma_semantic_b1_crt_checked_bounds_and_geometry[OF checked])
  have children_resolve:
      "\<And>index. index<length comma_semantic_b1_crt_sources \<Longrightarrow>
        comma_semantic_b1_crt_published
          (comma_semantic_b1_crt_sources!index) =
        comma_semantic_b1_crt_occurrence_at_index index"
    by (rule comma_semantic_b1_crt_published_children_resolve_index[OF checked])
  have compact:
      "list_all (comma_semantic_b1_crt_compact_occurrence_check
        comma_semantic_b1_crt_templates comma_semantic_b1_crt_sources
        comma_semantic_b1_crt_occurrence_at_index comma_semantic_b1_crt_descriptors
        comma_semantic_b1_crt_lift_refs comma_semantic_b1_crt_lift_descriptors)
        [0..<length comma_semantic_b1_crt_sources]"
    using checked unfolding comma_semantic_b1_crt_occurrence_data_checked_def
      comma_semantic_b1_crt_construction_check_def by blast
  have descriptor_extent:
      "length comma_semantic_b1_crt_descriptors = length comma_semantic_b1_crt_sources"
    using checked unfolding comma_semantic_b1_crt_occurrence_data_checked_def by blast
  have template_geometries:
      "list_all (comma_semantic_b1_crt_template_geometry_certified
        comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
        comma_semantic_b1_crt_template_column_ids)
        (remdups (map fst comma_semantic_b1_crt_descriptors))"
    using parent_template_geometries descriptor_extent
    by (auto simp: list_all_iff in_set_conv_nth)
  show ?thesis
    by (rule comma_semantic_b1_crt_compact_occurrences_candidate_matches
      [OF descriptor_extent compact template_geometries children_resolve])
qed

lemma comma_semantic_b1_crt_published_lift_candidate:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and normalized: "source=comma_source_continuation_base source"
    and admitted: "comma_round_admitted source"
    and published: "comma_semantic_b1_crt_published source=Some occurrence"
  shows "comma_semantic_b1_crt_occurrence_wellformed occurrence \<and>
    comma_semantic_b1_crt_occurrence_candidate_matches
      comma_semantic_b1_crt_published source occurrence"
proof -
  obtain index where index: "index<length comma_semantic_b1_crt_sources"
    and source_at_index: "comma_semantic_b1_crt_sources!index=source"
    and occurrence_at_index:
      "comma_semantic_b1_crt_occurrence_at_index index=Some occurrence"
    by (rule comma_semantic_b1_crt_published_occurrence_index[OF published])
  have parent_wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    by (rule comma_semantic_b1_crt_occurrence_at_index_wellformed
      [OF checked index occurrence_at_index])
  have all_candidates:
      "\<forall>index<length comma_semantic_b1_crt_sources. \<forall>parent.
        comma_semantic_b1_crt_occurrence_at_index index=Some parent \<longrightarrow>
        comma_semantic_b1_crt_occurrence_candidate_matches
          comma_semantic_b1_crt_published
          (comma_semantic_b1_crt_sources!index) parent"
    by (rule comma_semantic_b1_crt_published_constructed_candidate_matches[OF checked])
  have candidate:
      "comma_semantic_b1_crt_occurrence_candidate_matches
        comma_semantic_b1_crt_published source occurrence"
    using all_candidates index source_at_index occurrence_at_index by blast
  show ?thesis using parent_wellformed candidate by blast
qed

lemma comma_semantic_b1_crt_published_candidate_child_present:
  assumes normalized: "source=comma_source_continuation_base source"
    and admitted: "comma_round_admitted source"
    and wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    and candidate:
      "comma_semantic_b1_crt_occurrence_candidate_matches
        comma_semantic_b1_crt_published source occurrence"
    and slot: "slot<comma_decisive_sector_period source"
    and action: "comma_semantic_b1_source_slot_action source slot=
      Comma_Continuation_Goto child shift"
  shows "\<exists>child_occurrence.
    comma_semantic_b1_crt_published child=Some child_occurrence"
proof -
  let ?period = "comma_decisive_sector_period source"
  have period_positive: "0<?period"
    by (rule comma_decisive_sector_period_admitted(1)[OF admitted])
  have period_divides: "?period dvd 924"
    by (rule comma_decisive_sector_period_admitted(2)[OF admitted])
  have period_le: "?period\<le>924"
    using period_divides by (rule dvd_imp_le) simp
  have clock: "slot<924" using slot period_le by arith
  have total: "\<exists>result. comma_semantic_b1_crt_occurrence_lookup occurrence slot =
      Some result"
    by (rule comma_semantic_b1_crt_occurrence_lookup_total[OF wellformed])
  then obtain result where lookup:
      "comma_semantic_b1_crt_occurrence_lookup occurrence slot=Some result"
    by blast
  have matches:
      "comma_semantic_b1_crt_occurrence_lookup occurrence slot=
        comma_semantic_b1_crt_occurrence_local_step
          comma_semantic_b1_crt_published source slot"
    using candidate clock
    by (auto simp: comma_semantic_b1_crt_occurrence_candidate_matches_def)
  have local_some:
      "comma_semantic_b1_crt_occurrence_local_step
        comma_semantic_b1_crt_published source slot=Some result"
    using lookup matches by simp
  show ?thesis
    using local_some action slot clock
    by (auto simp: comma_semantic_b1_crt_occurrence_local_step_def)
qed

lemma comma_semantic_b1_crt_published_exact:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and normalized: "source=comma_source_continuation_base source"
    and admitted: "comma_round_admitted source"
    and published: "comma_semantic_b1_crt_published source=Some occurrence"
  shows "comma_semantic_b1_crt_occurrence_exact source occurrence"
proof (rule comma_semantic_b1_crt_occurrence_map_exact
    [where published=comma_semantic_b1_crt_published,
      OF _ _ normalized admitted published])
  show "\<And>source occurrence.
      source=comma_source_continuation_base source \<Longrightarrow>
      comma_round_admitted source \<Longrightarrow>
      comma_semantic_b1_crt_published source=Some occurrence \<Longrightarrow>
      comma_semantic_b1_crt_occurrence_wellformed occurrence \<and>
      comma_semantic_b1_crt_occurrence_candidate_matches
        comma_semantic_b1_crt_published source occurrence"
  proof -
    fix source occurrence
    assume normalized_source: "source=comma_source_continuation_base source"
      and admitted_source: "comma_round_admitted source"
      and present: "comma_semantic_b1_crt_published source=Some occurrence"
    have candidate:
        "comma_semantic_b1_crt_occurrence_wellformed occurrence \<and>
         comma_semantic_b1_crt_occurrence_candidate_matches
           comma_semantic_b1_crt_published source occurrence"
      by (rule comma_semantic_b1_crt_published_lift_candidate
        [OF checked normalized_source admitted_source present])
    show "comma_semantic_b1_crt_occurrence_wellformed occurrence \<and>
      comma_semantic_b1_crt_occurrence_candidate_matches
        comma_semantic_b1_crt_published source occurrence"
      using candidate by blast
  qed
next
  fix source occurrence slot child shift
  assume normalized_source: "source=comma_source_continuation_base source"
    and admitted_source: "comma_round_admitted source"
    and present: "comma_semantic_b1_crt_published source=Some occurrence"
    and slot: "slot<comma_decisive_sector_period source"
    and action: "comma_semantic_b1_source_slot_action source slot=
      Comma_Continuation_Goto child shift"
  have candidate:
      "comma_semantic_b1_crt_occurrence_wellformed occurrence \<and>
       comma_semantic_b1_crt_occurrence_candidate_matches
         comma_semantic_b1_crt_published source occurrence"
    by (rule comma_semantic_b1_crt_published_lift_candidate
      [OF checked normalized_source admitted_source present])
  have wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    using candidate by blast
  show "\<exists>child_occurrence.
      comma_semantic_b1_crt_published child=Some child_occurrence"
    by (rule comma_semantic_b1_crt_published_candidate_child_present
      [OF normalized_source admitted_source wellformed candidate[THEN conjunct2]
        slot action])
qed

lemma comma_semantic_b1_crt_root_occurrence_exact:
  assumes root: "root<46"
  obtains occurrence where
    "comma_semantic_b1_crt_root_occurrence root=Some occurrence"
    "comma_semantic_b1_crt_occurrence_exact
      (Comma_Entry 1 0 (comma_offset_representatives ! root)) occurrence"
proof -
  have checked: "comma_semantic_b1_crt_occurrence_data_checked"
    by (rule comma_semantic_b1_crt_occurrence_data_checked)
  obtain index occurrence where root_index:
      "comma_semantic_b1_crt_root_occurrence_indices ! root=index"
    and root_bound: "root<length comma_semantic_b1_crt_root_occurrence_indices"
    and index_bound: "index<length comma_semantic_b1_crt_sources"
    and source_at_index:
      "comma_semantic_b1_crt_sources ! index=
        Comma_Entry 1 0 (comma_offset_representatives ! root)"
    and occurrence_at_index:
      "comma_semantic_b1_crt_occurrence_at_index index=Some occurrence"
    and construction: "comma_semantic_b1_crt_construction_check index"
    by (rule comma_semantic_b1_crt_root_entry_resolves_checked[OF checked root])
  have root_occurrence:
      "comma_semantic_b1_crt_root_occurrence root=Some occurrence"
    using root_bound root_index occurrence_at_index
    by (simp add: comma_semantic_b1_crt_root_occurrence_def)
  have published:
      "comma_semantic_b1_crt_published
        (Comma_Entry 1 0 (comma_offset_representatives ! root))=Some occurrence"
    by (rule comma_semantic_b1_crt_published_resolves_index
      [OF checked index_bound source_at_index occurrence_at_index])
  have normalized:
      "Comma_Entry 1 0 (comma_offset_representatives ! root) =
       comma_source_continuation_base
         (Comma_Entry 1 0 (comma_offset_representatives ! root))"
    by simp
  have bound: "comma_offset_representatives ! root \<le> 90"
    using comma_offset_representatives_checked root
    by (auto simp: list_all_iff)
  have admitted:
      "comma_round_admitted
        (Comma_Entry 1 0 (comma_offset_representatives ! root))"
    using bound by (simp; arith)
  have exact:
      "comma_semantic_b1_crt_occurrence_exact
        (Comma_Entry 1 0 (comma_offset_representatives ! root)) occurrence"
    by (rule comma_semantic_b1_crt_published_exact
      [OF checked normalized admitted published])
  show thesis by (rule that[OF root_occurrence exact])
qed

lemma comma_semantic_b1_crt_root_occurrence_distinct_binding:
  assumes root: "root<46"
    and lookup: "comma_semantic_b1_crt_root_occurrence root=Some occurrence"
  shows "distinct (comma_semantic_b1_crt_occurrence_beta occurrence)"
proof -
  have checked: "comma_semantic_b1_crt_occurrence_data_checked"
    by (rule comma_semantic_b1_crt_occurrence_data_checked)
  obtain index value where root_index:
      "comma_semantic_b1_crt_root_occurrence_indices ! root=index"
    and root_bound: "root<length comma_semantic_b1_crt_root_occurrence_indices"
    and index_bound: "index<length comma_semantic_b1_crt_sources"
    and source_at_index:
      "comma_semantic_b1_crt_sources ! index =
        Comma_Entry 1 0 (comma_offset_representatives ! root)"
    and indexed_occurrence:
      "comma_semantic_b1_crt_occurrence_at_index index=Some value"
    and construction: "comma_semantic_b1_crt_construction_check index"
    by (rule comma_semantic_b1_crt_root_entry_resolves_checked[OF checked root])
  have compact:
      "comma_semantic_b1_crt_compact_occurrence_check comma_semantic_b1_crt_templates
        comma_semantic_b1_crt_sources comma_semantic_b1_crt_occurrence_at_index
        comma_semantic_b1_crt_descriptors comma_semantic_b1_crt_lift_refs
        comma_semantic_b1_crt_lift_descriptors index"
    using construction by (simp add: comma_semantic_b1_crt_construction_check_def)
  have exposed:
      "comma_semantic_b1_crt_lift_local_cover_witness comma_semantic_b1_crt_sources
        comma_semantic_b1_crt_occurrence_at_index comma_semantic_b1_crt_descriptors
        comma_semantic_b1_crt_templates (comma_semantic_b1_crt_sources!index) value
        (comma_semantic_b1_crt_lift_refs!index)
        comma_semantic_b1_crt_lift_descriptors"
    using comma_semantic_b1_crt_compact_occurrence_check_exposes
      [OF compact indexed_occurrence] by blast
  have binding:
      "distinct (comma_semantic_b1_crt_occurrence_beta value)"
    using exposed
    by (auto simp: comma_semantic_b1_crt_lift_local_cover_witness_def)
  have selected:
      "comma_semantic_b1_crt_occurrence_at_index index=Some occurrence"
    using lookup root_index root_bound
    by (simp add: comma_semantic_b1_crt_root_occurrence_def)
  have "value=occurrence" using indexed_occurrence selected by simp
  with binding show ?thesis by simp
qed

ML \<open>
(* The named proof calls reach compact occurrence coverage, checked parent
   geometry, source ordering, index lookup, and exact child/lift bridges.
   all_oracles follows those proof bodies, so retain the independent local-cover
   fixture and root consumer as audit roots. *)
val _ =
  if null (Thm_Deps.all_oracles @{thms
    comma_indexed_all_zero
    comma_indexed_all_Suc
    comma_selected_length_nil
    comma_selected_length_cons
    comma_semantic_b1_crt_local_cover_fixtures
    comma_semantic_b1_crt_source_order_rejects_equal_adjacent_keys
    comma_semantic_b1_crt_root_occurrence_exact
    comma_semantic_b1_crt_root_occurrence_distinct_binding
  }) then ()
  else error "Comma_Semantic_B1_Occurrence_Publication local oracle audit failed"
\<close>
end
