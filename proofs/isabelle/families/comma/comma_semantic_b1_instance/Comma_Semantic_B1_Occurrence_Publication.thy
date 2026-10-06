theory Comma_Semantic_B1_Occurrence_Publication
  imports Comma_Semantic_B1_Occurrence_Arithmetic
begin
ML_file "../comma_entry_arithmetic/selected_list_conversion.ML"
ML_file "semantic_b1_crt_operation_conversion.ML"

ML \<open>
  local
    val ctxt = @{context}
    fun make_selector name table pattern extents =
      let
        val selector = Comma_Selected_List_Conversion.make
          {ctxt = ctxt, name = name,
           root_definition = Thm.reflexive (Thm.cterm_of ctxt table),
           table_pattern = pattern, extents = extents}
        val context = put_simpset HOL_basic_ss ctxt
          |> Simplifier.add_proc (#procedure selector)
      in fn term => Simplifier.rewrite context (Thm.cterm_of ctxt term) end
    val nested_table = @{term "[[0,1,2,3]::nat list, [1], [2]]"}
    val nested_select = make_selector "nested_extent_regression" nested_table
      @{term "([[0,1,2,3]::nat list, [1], [2]]) ! row ! slot"} [2, 3]
    val valid_nested = nested_select
      @{term "([[0,1,2,3]::nat list, [1], [2]]) ! 1 ! 0"}
    val _ = if Thm.term_of (Thm.rhs_of valid_nested) aconv @{term "1::nat"}
      then () else error "Selected-list nested selector failed on an admitted row"
    val rejected_parent = Exn.capture nested_select
      @{term "([[0,1,2,3]::nat list, [1], [2]]) ! 2 ! 0"}
    val rejected_slot = Exn.capture nested_select
      @{term "([[0,1,2,3]::nat list, [1], [2]]) ! 0 ! 3"}
    val three_table = @{term "[0::nat, 1, 2]"}
    val select_three = make_selector "selected_suffix_index_two" three_table
      @{term "[0::nat, 1, 2] ! index"} [3]
    val selected_two = select_three @{term "[0::nat, 1, 2] ! 2"}
    val _ = if Thm.term_of (Thm.rhs_of selected_two) aconv @{term "2::nat"}
      then () else error "Selected-list suffix regression failed at index 2"
    val unoverloaded_zero = Thm.term_of (Thm.rhs_of
      (Axclass.unoverload_conv ctxt
        (Thm.cterm_of ctxt @{term "0::nat"})))
    val unoverloaded_nth = Const (@{const_name nth},
      fastype_of three_table --> @{typ nat} --> @{typ nat}) $
        three_table $ unoverloaded_zero
    val selected_unoverloaded = select_three unoverloaded_nth
    val _ = if Thm.term_of (Thm.rhs_of selected_unoverloaded) aconv @{term "0::nat"}
      then () else error "Selected-list failed to normalize an unoverloaded index"
    val four_table = @{term "[0::nat, 1, 2, 3]"}
    val select_four = make_selector "selected_suffix_index_three" four_table
      @{term "[0::nat, 1, 2, 3] ! index"} [4]
    val selected_three = select_four @{term "[0::nat, 1, 2, 3] ! 3"}
    val _ = if Thm.term_of (Thm.rhs_of selected_three) aconv @{term "3::nat"}
      then () else error "Selected-list suffix regression failed at index 3"
    val length_table = @{term "[[0::nat,1,2], [3,4,5]]"}
    val length_select = make_selector "opaque_head_length" length_table
      @{term "[[0::nat,1,2], [3,4,5]] ! index"} [2]
    val selected_length = length_select @{term "length [[0::nat,1,2], [3,4,5]]"}
    val _ = if Thm.term_of (Thm.rhs_of selected_length) aconv @{term "2::nat"}
      then () else error "Selected-list outer-spine length regression failed"
  in
    fun check_rejected label result =
      (case result of
        Exn.Exn (ERROR message) =>
          if message = "Selected-list nested index exceeds its depth-specific extent"
          then () else error message
      | Exn.Exn exn => Exn.reraise exn
      | Exn.Res _ => error ("Nested selected-list admitted an out-of-extent " ^ label))
    val _ = check_rejected "parent" rejected_parent
    val _ = check_rejected "slot" rejected_slot
  end
\<close>

text \<open>The candidate constructor and its bounded rebase/binding examples
belong to this concrete publisher. Generic refinement theories do not load
or depend on candidate-generation code. Admission still requires the checked
occurrence certificate below.\<close>

ML_file "semantic_b1_template_constructor.ML"

ML_file "semantic_b1_occurrence_publication.ML"

ML \<open>
  local
    structure Candidate = Comma_Semantic_B1_Template_Constructor
    structure Publication = Comma_Semantic_B1_Occurrence_Publication
    val _ = Publication.check_candidate_examples ()
    val ctxt = @{context}
    val refs = [[Candidate.Terminal_Ref (2, 7), Candidate.Goto_Ref (3, 17, 4)]]
    val encoded = Publication.serialize_lift_refs refs
    val expected = @{term
      "[[Comma_B1_Lift_Terminal_Ref 2 7, Comma_B1_Lift_Goto_Ref 3 17 4]]"}
    val wrong_lift = @{term
      "[[Comma_B1_Lift_Terminal_Ref 2 7, Comma_B1_Lift_Goto_Ref 3 17 5]]"}
    val descriptors = [{period = 4, slot = 3, template_cid = 9, net_shift = 17}:
      Candidate.lift_descriptor]
    val encoded_descriptors = Publication.serialize_lift_descriptors descriptors
    val expected_descriptors = @{term
      "([\<lparr>comma_semantic_b1_crt_lift_descriptor_period = 4,
         comma_semantic_b1_crt_lift_descriptor_slot = 3,
         comma_semantic_b1_crt_lift_descriptor_template_cid = 9,
         comma_semantic_b1_crt_lift_descriptor_net_shift = 17\<rparr>]
        :: comma_semantic_b1_crt_lift_descriptor list)"}
    fun prove proposition = Goal.prove ctxt [] [] proposition
      (fn {context, ...} => Simplifier.simp_tac
        (context addsimps [@{thm comma_semantic_b1_crt_lift_descriptor.make_def}]) 1)
    val serialized_refs = prove (HOLogic.mk_Trueprop
      (HOLogic.mk_eq (encoded, expected)))
    val wrong_lift_rejected = prove (HOLogic.mk_Trueprop
      (HOLogic.mk_not (HOLogic.mk_eq (encoded, wrong_lift))))
    val serialized_descriptors = prove (HOLogic.mk_Trueprop
      (HOLogic.mk_eq (encoded_descriptors, expected_descriptors)))
    val _ = Thm.consolidate
      [serialized_refs, wrong_lift_rejected, serialized_descriptors]
  in
    val _ = ()
  end
\<close>

(* Check the compact serializer on a small shared two-level DAG.  The same
   leaf appears at multiple child positions, and the middle node is reused by
   three root positions.  The positive kernel proof pins constructor order;
   the negative one ensures that swapping one leaf is observably different. *)
ML \<open>
  local
    structure Candidate = Comma_Semantic_B1_Template_Constructor
    val ctxt = @{context}
    val leaf = Candidate.MDD_Node (2,
      [Candidate.MDD_False, Candidate.MDD_True, Candidate.MDD_False,
       Candidate.MDD_True, Candidate.MDD_True, Candidate.MDD_False,
       Candidate.MDD_True])
    val alternate_leaf = Candidate.MDD_Node (2,
      [Candidate.MDD_False, Candidate.MDD_True, Candidate.MDD_False,
       Candidate.MDD_True, Candidate.MDD_False, Candidate.MDD_False,
       Candidate.MDD_True])
    val middle = Candidate.MDD_Node (1, [leaf, alternate_leaf, leaf])
    val root = Candidate.MDD_Node (0, [middle, middle, Candidate.MDD_False, middle])
    val swapped_middle = Candidate.MDD_Node (1, [alternate_leaf, leaf, leaf])
    val swapped_root = Candidate.MDD_Node
      (0, [middle, middle, Candidate.MDD_False, swapped_middle])
    fun expand Candidate.MDD_False = @{term "Comma_CRT_Bool False"}
      | expand Candidate.MDD_True = @{term "Comma_CRT_Bool True"}
      | expand (Candidate.MDD_Node (level, children)) =
          @{term Comma_CRT_Node} $ Candidate.nat level $
            HOLogic.mk_list Candidate.columnT (map expand children)
    val compact = #columns_term
      (Comma_Semantic_B1_Occurrence_Publication.compress_template_row [root, root])
    val expected = HOLogic.mk_list Candidate.columnT (map expand [root, root])
    val swapped = HOLogic.mk_list Candidate.columnT
      (map expand [swapped_root, swapped_root])
    fun prove proposition = Goal.prove ctxt [] [] proposition
      (fn {context, ...} =>
        Simplifier.simp_tac (context addsimps [@{thm Let_def}]) 1)
    val compact_correct = prove (HOLogic.mk_Trueprop
      (HOLogic.mk_eq (compact, expected)))
    val swapped_rejected = prove (HOLogic.mk_Trueprop
      (HOLogic.mk_not (HOLogic.mk_eq (compact, swapped))))
    val _ = Thm.consolidate [compact_correct, swapped_rejected]
  in
    val _ = ()
  end
\<close>

local_setup \<open>Comma_Semantic_B1_Occurrence_Publication.publish\<close>

definition comma_semantic_b1_crt_occurrence_at_index ::
    "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option" where
  "comma_semantic_b1_crt_occurrence_at_index index =
    (if index < length comma_semantic_b1_crt_descriptors then
       comma_semantic_b1_crt_resolve_descriptor comma_semantic_b1_crt_templates
         (comma_semantic_b1_crt_descriptors ! index)
     else None)"

definition comma_semantic_b1_crt_template_geometry_at :: "nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_template_geometry_at cid \<longleftrightarrow>
    cid < length comma_semantic_b1_crt_templates \<and>
    comma_semantic_b1_crt_occurrence_geometry_check
      (comma_semantic_b1_crt_templates ! cid)"

definition comma_semantic_b1_crt_occurrence_entry_checked :: "nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_occurrence_entry_checked index \<longleftrightarrow>
    (if index < length comma_semantic_b1_crt_sources \<and>
        index < length comma_semantic_b1_crt_descriptors \<and>
        index < length comma_semantic_b1_crt_lift_refs then
       (case (comma_semantic_b1_crt_sources ! index,
              comma_semantic_b1_crt_occurrence_at_index index,
              comma_semantic_b1_crt_lift_refs ! index) of
          (source, Some occurrence, refs) \<Rightarrow>
            comma_semantic_b1_crt_lift_local_cover_witness
              comma_semantic_b1_crt_sources
              comma_semantic_b1_crt_occurrence_at_index
              comma_semantic_b1_crt_descriptors
              comma_semantic_b1_crt_templates source occurrence refs
              comma_semantic_b1_crt_lift_descriptors
        | _ \<Rightarrow> False)
     else False)"

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
     length comma_semantic_b1_crt_lift_descriptors \<le>
       28 * length comma_semantic_b1_crt_sources \<and>
     list_all comma_semantic_b1_crt_source_order_step
       [0..<length comma_semantic_b1_crt_sources - 1] \<and>
     list_all comma_semantic_b1_crt_template_geometry_at
       [0..<length comma_semantic_b1_crt_templates] \<and>
     list_all comma_semantic_b1_crt_occurrence_entry_checked
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
         step_fact = @{thm comma_indexed_all_Suc}}
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
         step_fact = @{thm comma_indexed_all_Suc}}) ()
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

lemma comma_semantic_b1_crt_occurrence_entry_checked_at:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and index: "index < length comma_semantic_b1_crt_sources"
  shows "comma_semantic_b1_crt_occurrence_entry_checked index"
proof -
  have entries:
    "list_all comma_semantic_b1_crt_occurrence_entry_checked
      [0..<length comma_semantic_b1_crt_sources]"
    using checked
    by (simp add: comma_semantic_b1_crt_occurrence_data_checked_def)
  show ?thesis using entries index
    by (auto simp: list_all_iff)
qed

lemma comma_semantic_b1_crt_template_geometry_at_checked:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and index: "cid < length comma_semantic_b1_crt_templates"
  shows "comma_semantic_b1_crt_template_geometry_at cid"
proof -
  have geometries:
    "list_all comma_semantic_b1_crt_template_geometry_at
      [0..<length comma_semantic_b1_crt_templates]"
    using checked
    by (simp add: comma_semantic_b1_crt_occurrence_data_checked_def)
  show ?thesis using geometries index by (auto simp: list_all_iff)
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

lemma comma_semantic_b1_crt_occurrence_at_index_wellformed_check:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and index: "index < length comma_semantic_b1_crt_sources"
    and occurrence:
      "comma_semantic_b1_crt_occurrence_at_index index = Some value"
  shows "comma_semantic_b1_crt_occurrence_wellformed_check value"
proof -
  have entry:
      "comma_semantic_b1_crt_occurrence_entry_checked index"
    by (rule comma_semantic_b1_crt_occurrence_entry_checked_at[OF checked index])
  have refs_bound: "index<length comma_semantic_b1_crt_lift_refs"
    using checked index
    by (auto simp: comma_semantic_b1_crt_occurrence_data_checked_def)
  let ?source = "comma_semantic_b1_crt_sources ! index"
  let ?refs = "comma_semantic_b1_crt_lift_refs ! index"
  have witness:
      "comma_semantic_b1_crt_lift_local_cover_witness
        comma_semantic_b1_crt_sources comma_semantic_b1_crt_occurrence_at_index
        comma_semantic_b1_crt_descriptors comma_semantic_b1_crt_templates
        ?source value ?refs comma_semantic_b1_crt_lift_descriptors"
    using entry occurrence index refs_bound
    by (auto simp: comma_semantic_b1_crt_occurrence_entry_checked_def
      split: option.splits prod.splits)
  have descriptor_bound: "index<length comma_semantic_b1_crt_descriptors"
    using checked index
    by (auto simp: comma_semantic_b1_crt_occurrence_data_checked_def)
  obtain cid rebase beta where descriptor:
      "comma_semantic_b1_crt_descriptors ! index=(cid,(rebase,beta))"
    by (cases "comma_semantic_b1_crt_descriptors ! index")
      (auto split: prod.splits)
  have cid_bound: "cid<length comma_semantic_b1_crt_templates"
    and value_fields:
      "value=\<lparr>comma_semantic_b1_crt_occurrence_columns=
          comma_semantic_b1_crt_templates ! cid,
        comma_semantic_b1_crt_occurrence_rebase=rebase,
        comma_semantic_b1_crt_occurrence_beta=beta\<rparr>"
    using occurrence descriptor descriptor_bound
    by (auto simp: comma_semantic_b1_crt_occurrence_at_index_def
      comma_semantic_b1_crt_resolve_descriptor_def split: if_splits)
  have geometry:
      "comma_semantic_b1_crt_occurrence_geometry_check
        (comma_semantic_b1_crt_templates ! cid)"
    using comma_semantic_b1_crt_template_geometry_at_checked[OF checked cid_bound]
    by (simp add: comma_semantic_b1_crt_template_geometry_at_def)
  have binding:
      "comma_semantic_b1_crt_occurrence_binding_check value"
    using witness
    by (simp add: comma_semantic_b1_crt_lift_local_cover_witness_def)
  show ?thesis using binding geometry value_fields
    by (rule comma_semantic_b1_crt_occurrence_binding_check_geometry)
qed

lemma comma_semantic_b1_crt_occurrence_at_index_total:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and index: "index < length comma_semantic_b1_crt_sources"
  obtains occ where
    "comma_semantic_b1_crt_occurrence_at_index index = Some occ"
proof -
  have entry:
      "comma_semantic_b1_crt_occurrence_entry_checked index"
    by (rule comma_semantic_b1_crt_occurrence_entry_checked_at[OF checked index])
  show thesis
  proof (cases "comma_semantic_b1_crt_occurrence_at_index index")
    case None
    with entry show thesis
      by (auto simp: comma_semantic_b1_crt_occurrence_entry_checked_def
        split: prod.splits)
  next
    case (Some occ)
    then show thesis by (rule that)
  qed
qed

lemma comma_semantic_b1_crt_published_local_cover_witness:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and published: "comma_semantic_b1_crt_published source = Some occurrence"
  obtains index where
    "index < length comma_semantic_b1_crt_sources"
    "comma_semantic_b1_crt_sources ! index = source"
    "comma_semantic_b1_crt_occurrence_at_index index = Some occurrence"
    "comma_semantic_b1_crt_lift_local_cover_witness
      comma_semantic_b1_crt_sources comma_semantic_b1_crt_occurrence_at_index
      comma_semantic_b1_crt_descriptors comma_semantic_b1_crt_templates
      source occurrence (comma_semantic_b1_crt_lift_refs ! index)
      comma_semantic_b1_crt_lift_descriptors"
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
  have refs_bound: "index<length comma_semantic_b1_crt_lift_refs"
    using checked index_bound
    by (auto simp: comma_semantic_b1_crt_occurrence_data_checked_def)
  have entry_checked:
      "comma_semantic_b1_crt_occurrence_entry_checked index"
    by (rule comma_semantic_b1_crt_occurrence_entry_checked_at
      [OF checked index_bound])
  have witness:
      "comma_semantic_b1_crt_lift_local_cover_witness
        comma_semantic_b1_crt_sources comma_semantic_b1_crt_occurrence_at_index
        comma_semantic_b1_crt_descriptors comma_semantic_b1_crt_templates
        source occurrence (comma_semantic_b1_crt_lift_refs ! index)
        comma_semantic_b1_crt_lift_descriptors"
    using entry_checked occurrence_at_index source_at_index refs_bound
    by (auto simp: comma_semantic_b1_crt_occurrence_entry_checked_def
      split: option.splits prod.splits)
  show thesis
    by (rule that[OF index_bound source_at_index
      occurrence_at_index witness])
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

lemma comma_semantic_b1_crt_published_lift_candidate:
  assumes checked: "comma_semantic_b1_crt_occurrence_data_checked"
    and normalized: "source=comma_source_continuation_base source"
    and admitted: "comma_round_admitted source"
    and published: "comma_semantic_b1_crt_published source=Some occurrence"
  shows "comma_semantic_b1_crt_occurrence_wellformed_check occurrence \<and>
    comma_semantic_b1_crt_occurrence_candidate_matches
      comma_semantic_b1_crt_published source occurrence"
proof -
  obtain index where index: "index<length comma_semantic_b1_crt_sources"
    and source_at_index: "comma_semantic_b1_crt_sources!index=source"
    and occurrence_at_index:
      "comma_semantic_b1_crt_occurrence_at_index index=Some occurrence"
    and witness:
      "comma_semantic_b1_crt_lift_local_cover_witness
        comma_semantic_b1_crt_sources comma_semantic_b1_crt_occurrence_at_index
        comma_semantic_b1_crt_descriptors comma_semantic_b1_crt_templates
        source occurrence (comma_semantic_b1_crt_lift_refs!index)
        comma_semantic_b1_crt_lift_descriptors"
    by (rule comma_semantic_b1_crt_published_local_cover_witness[OF checked published])
  have parent_wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed_check occurrence"
    by (rule comma_semantic_b1_crt_occurrence_at_index_wellformed_check
      [OF checked index occurrence_at_index])
  have parent_semantic:
      "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    by (rule comma_semantic_b1_crt_occurrence_wellformed_check_sound
      [OF parent_wellformed])
  have child_wellformed:
      "\<And>i child. i<length comma_semantic_b1_crt_sources \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_at_index i=Some child \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed child"
  proof -
    fix i child
    assume i: "i<length comma_semantic_b1_crt_sources"
      and child: "comma_semantic_b1_crt_occurrence_at_index i=Some child"
    have checked_child:
        "comma_semantic_b1_crt_occurrence_wellformed_check child"
      by (rule comma_semantic_b1_crt_occurrence_at_index_wellformed_check
        [OF checked i child])
    show "comma_semantic_b1_crt_occurrence_wellformed child"
      by (rule comma_semantic_b1_crt_occurrence_wellformed_check_sound
        [OF checked_child])
  qed
  have child_resolver:
      "\<And>i. i<length comma_semantic_b1_crt_sources \<Longrightarrow>
        comma_semantic_b1_crt_published (comma_semantic_b1_crt_sources!i) =
          comma_semantic_b1_crt_occurrence_at_index i"
    by (rule comma_semantic_b1_crt_published_children_resolve_index[OF checked])
  have candidate:
    "comma_semantic_b1_crt_occurrence_candidate_matches
        comma_semantic_b1_crt_published source occurrence"
    by (rule comma_semantic_b1_crt_lift_local_cover_candidate_matches
      [OF witness parent_semantic child_wellformed child_resolver])
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
        "comma_semantic_b1_crt_occurrence_wellformed_check occurrence \<and>
         comma_semantic_b1_crt_occurrence_candidate_matches
           comma_semantic_b1_crt_published source occurrence"
      by (rule comma_semantic_b1_crt_published_lift_candidate
        [OF checked normalized_source admitted_source present])
    have checked_wellformed:
        "comma_semantic_b1_crt_occurrence_wellformed_check occurrence"
      using candidate by blast
    have wellformed:
        "comma_semantic_b1_crt_occurrence_wellformed occurrence"
      by (rule comma_semantic_b1_crt_occurrence_wellformed_check_sound
        [OF checked_wellformed])
    show "comma_semantic_b1_crt_occurrence_wellformed occurrence \<and>
      comma_semantic_b1_crt_occurrence_candidate_matches
        comma_semantic_b1_crt_published source occurrence"
      using wellformed candidate by blast
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
      "comma_semantic_b1_crt_occurrence_wellformed_check occurrence \<and>
       comma_semantic_b1_crt_occurrence_candidate_matches
         comma_semantic_b1_crt_published source occurrence"
    by (rule comma_semantic_b1_crt_published_lift_candidate
      [OF checked normalized_source admitted_source present])
  have wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    by (rule comma_semantic_b1_crt_occurrence_wellformed_check_sound
      [OF candidate[THEN conjunct1]])
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
  have root_row: "comma_semantic_b1_crt_root_entry_checked root"
    using checked root
    by (auto simp: comma_semantic_b1_crt_occurrence_data_checked_def list_all_iff)
  obtain index occurrence where root_index:
      "comma_semantic_b1_crt_root_occurrence_indices ! root=index"
    and root_bound: "root<length comma_semantic_b1_crt_root_occurrence_indices"
    and index_bound: "index<length comma_semantic_b1_crt_sources"
    and source_at_index:
      "comma_semantic_b1_crt_sources ! index=
        Comma_Entry 1 0 (comma_offset_representatives ! root)"
    and occurrence_at_index:
      "comma_semantic_b1_crt_occurrence_at_index index=Some occurrence"
    using root_row root
    by (auto simp: comma_semantic_b1_crt_root_entry_checked_def Let_def
      split: option.splits)
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
  have root_row: "comma_semantic_b1_crt_root_entry_checked root"
    using checked root
    by (auto simp: comma_semantic_b1_crt_occurrence_data_checked_def list_all_iff)
  obtain index value where root_index:
      "comma_semantic_b1_crt_root_occurrence_indices ! root=index"
    and root_bound: "root<length comma_semantic_b1_crt_root_occurrence_indices"
    and index_bound: "index<length comma_semantic_b1_crt_sources"
    and source_at_index:
      "comma_semantic_b1_crt_sources ! index =
        Comma_Entry 1 0 (comma_offset_representatives ! root)"
    and indexed_occurrence:
      "comma_semantic_b1_crt_occurrence_at_index index=Some value"
    using root_row root
    by (auto simp: comma_semantic_b1_crt_root_entry_checked_def Let_def
      split: option.splits)
  have entry_checked:
      "comma_semantic_b1_crt_occurrence_entry_checked index"
    by (rule comma_semantic_b1_crt_occurrence_entry_checked_at[OF checked index_bound])
  have refs_bound: "index < length comma_semantic_b1_crt_lift_refs"
    using checked index_bound
    by (auto simp: comma_semantic_b1_crt_occurrence_data_checked_def)
  have witness:
      "comma_semantic_b1_crt_lift_local_cover_witness
        comma_semantic_b1_crt_sources comma_semantic_b1_crt_occurrence_at_index
        comma_semantic_b1_crt_descriptors comma_semantic_b1_crt_templates
        (comma_semantic_b1_crt_sources ! index) value
        (comma_semantic_b1_crt_lift_refs ! index)
        comma_semantic_b1_crt_lift_descriptors"
    using entry_checked index_bound source_at_index indexed_occurrence refs_bound
    by (auto simp: comma_semantic_b1_crt_occurrence_entry_checked_def
      split: option.splits prod.splits)
  have binding: "distinct (comma_semantic_b1_crt_occurrence_beta value)"
    using witness
    by (simp add: comma_semantic_b1_crt_lift_local_cover_witness_def)
  have selected:
      "comma_semantic_b1_crt_occurrence_at_index index=Some occurrence"
    using lookup root_index root_bound
    by (simp add: comma_semantic_b1_crt_root_occurrence_def)
  have "value=occurrence" using indexed_occurrence selected by simp
  with binding show ?thesis by simp
qed


ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
    comma_indexed_all_zero
    comma_indexed_all_Suc
    comma_selected_length_nil
    comma_selected_length_cons
    comma_semantic_b1_crt_local_cover_fixtures
    comma_semantic_b1_crt_source_order_steps_sorted
    comma_semantic_b1_crt_source_order_distinct
    comma_semantic_b1_crt_source_order_rejects_equal_adjacent_keys
    comma_semantic_b1_crt_occurrence_data_checked
    comma_semantic_b1_crt_find_source_member
    comma_semantic_b1_crt_occurrence_entry_checked_at
    comma_semantic_b1_crt_template_geometry_at_checked
    comma_semantic_b1_crt_published_resolves_index
    comma_semantic_b1_crt_occurrence_at_index_wellformed_check
    comma_semantic_b1_crt_occurrence_at_index_total
    comma_semantic_b1_crt_published_local_cover_witness
    comma_semantic_b1_crt_published_children_resolve_index
    comma_semantic_b1_crt_published_lift_candidate
    comma_semantic_b1_crt_published_candidate_child_present
    comma_semantic_b1_crt_published_exact
    comma_semantic_b1_crt_root_occurrence_exact
    comma_semantic_b1_crt_root_occurrence_distinct_binding
  }) then ()
  else error "Comma_Semantic_B1_Occurrence_Publication local oracle audit failed"
\<close>
end
