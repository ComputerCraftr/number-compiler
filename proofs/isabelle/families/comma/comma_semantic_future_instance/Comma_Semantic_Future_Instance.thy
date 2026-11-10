theory Comma_Semantic_Future_Instance
  imports Comma_Semantic_Future_Candidate_Data
    Comma_Semantic_Future_Candidate_Integrity
    Comma_Semantic_Future_Candidate_Selector
    Comma_Semantic_Future_Action_Compare
    Comma_Semantic_Future_Candidate_Provider_NF
    Comma_Semantic_Future_Source_NF_Bridge
begin

text \<open>
The candidate CID map is only a proposed quotient.  This instance gives
classes no authority until both its finite class rows and its source binding
to the checked semantic decade provider have kernel-checked certificates.
The source map is a compact binding; controls, ordered children, and ranks
are stored once per class.  Exponent weights remain occurrence data.
\<close>

definition comma_semantic_future_candidate_provider_row ::
    "comma_boundary_state \<Rightarrow> bool" where
  "comma_semantic_future_candidate_provider_row q =
    (case comma_semantic_future_candidate_class_output
        (comma_semantic_future_candidate_class_of q) of
         None \<Rightarrow> False
       | Some (control,children) \<Rightarrow>
           comma_semantic_boundary_control_step comma_semantic_decade_summary q =
             Some control \<and>
           map comma_semantic_future_candidate_class_of
             (comma_semantic_boundary_children comma_semantic_decade_summary q control) =
             children)"

definition comma_semantic_future_candidate_provider_cell ::
    "comma_boundary_kind \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_future_candidate_provider_cell kind a_index r =
    comma_semantic_future_candidate_provider_row (kind,a_index+2,r)"

definition comma_semantic_future_candidate_provider_index_check ::
    "comma_boundary_kind \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_future_candidate_provider_index_check kind a_index =
    list_all (comma_semantic_future_candidate_provider_cell kind a_index)
      [0..<924]"

definition comma_semantic_future_candidate_provider_kind_check ::
    "comma_boundary_kind \<Rightarrow> bool" where
  "comma_semantic_future_candidate_provider_kind_check kind =
    list_all (comma_semantic_future_candidate_provider_index_check kind)
      [0..<8]"

definition comma_semantic_future_candidate_provider_check :: bool where
  "comma_semantic_future_candidate_provider_check \<longleftrightarrow>
    comma_semantic_future_candidate_provider_kind_check Comma_N \<and>
    comma_semantic_future_candidate_provider_kind_check Comma_Z"

definition comma_semantic_concrete_future_rank ::
    "comma_boundary_state \<Rightarrow> nat option" where
  "comma_semantic_concrete_future_rank q =
    comma_semantic_future_candidate_class_rank
      (comma_semantic_future_candidate_class_of q)"

lemma comma_semantic_boundary_step_decisive_round:
  assumes valid: "comma_boundary_valid q"
  shows "comma_semantic_boundary_step provider q =
    (case q of (kind,a,r) \<Rightarrow>
      comma_semantic_boundary_event_outcome provider r
        (comma_decisive_endpoint_round r (comma_finite_initial q)))"
proof -
  obtain kind a r where q: "q=(kind,a,r)"
    by (cases q) auto
  have initial_admitted:
    "comma_round_admitted (comma_finite_initial q)"
    using valid q
    by (cases kind)
      (auto simp: comma_boundary_valid_def comma_finite_initial_def)
  have decisive_observation:
    "comma_decisive_endpoint_round r (comma_finite_initial q) =
      (case comma_round_control_germ r (comma_finite_initial q) of
        (_,_,event) \<Rightarrow> event)"
    using comma_decisive_endpoint_round_refines[OF initial_admitted]
    by (simp add: comma_decisive_endpoint_observation_def)
  have control_germ:
    "comma_round_control_germ r (comma_finite_initial q) =
      comma_round_close r (comma_finite_initial q)"
    by (rule comma_round_control_germ_refines)
  have event:
    "comma_decisive_endpoint_round r (comma_finite_initial q) =
      snd (snd (comma_round_close r (comma_finite_initial q)))"
    using decisive_observation control_germ
    by (cases "comma_round_close r (comma_finite_initial q)") auto
  show ?thesis
    using valid event
    by (simp add: comma_semantic_boundary_step_def q)
qed

ML \<open>
structure Comma_Semantic_Future_Candidate_Check =
struct
local
  fun list_extent equation =
    let
      val rhs = Thm.term_of (Thm.rhs_of equation)
    in length (HOLogic.dest_list rhs) end

  fun selector ctxt name equation pattern =
    let
      val extent = list_extent equation
    in
      Comma_Selected_List_Conversion.make
        {ctxt = ctxt, name = name, root_definition = equation,
         table_pattern = pattern, extents = [extent]}
    end

  fun build ctxt =
    let
      val ids = selector ctxt "future_candidate_source_ids"
        @{thm comma_semantic_future_candidate_class_ids_def}
        @{term "comma_semantic_future_candidate_class_ids ! index"}
      val controls = selector ctxt "future_candidate_controls"
        @{thm comma_semantic_future_candidate_controls_def}
        @{term "comma_semantic_future_candidate_controls ! index"}
      val children = selector ctxt "future_candidate_children"
        @{thm comma_semantic_future_candidate_children_def}
        @{term "comma_semantic_future_candidate_children ! index"}
      val ranks = selector ctxt "future_candidate_ranks"
        @{thm comma_semantic_future_candidate_ranks_def}
        @{term "comma_semantic_future_candidate_ranks ! index"}
      val class_count = list_extent
        @{thm comma_semantic_future_candidate_controls_def}
      val _ = if class_count > 0 andalso class_count <= 65536 then ()
        else error "Candidate class count is outside the checker bound"
      val successor_cache = Comma_Selected_List_Conversion.make_successor_cache ctxt
        (Int.max (class_count, 924))
      val simps = @{thms comma_semantic_future_candidate_class_valid_def
        comma_semantic_future_candidate_class_step_def
        comma_semantic_future_candidate_class_rank_def
        comma_semantic_future_candidate_class_children_def
        comma_semantic_future_candidate_class_row_shape_def
        comma_semantic_future_candidate_class_row_checked_def
        comma_semantic_future_candidate_class_index_def
        comma_semantic_future_candidate_class_of_def
        comma_semantic_concrete_future_rank_def
        comma_semantic_rank_row_checked_def comma_boundary_states_card
        comma_boundary_valid_def
        list_all_Nil_iff list_all_Cons_iff map_filter.simps id_def}
      val proof_context =
        Comma_Entry_Arithmetic.natural_context ctxt
        |> fold Simplifier.add_proc
            [#procedure ids, #procedure controls, #procedure children, #procedure ranks]
        |> Simplifier.add_simps simps
      fun numeral value = HOLogic.mk_number @{typ nat} value
      fun prove_true_in context proposition =
        Goal.prove ctxt [] [] (HOLogic.mk_Trueprop proposition)
          (fn _ => Simplifier.asm_full_simp_tac context 1)
      fun prove_true proposition =
        prove_true_in proof_context proposition
      fun length_term list =
        Const (@{const_name size}, fastype_of list --> @{typ nat}) $ list
      val control_list = @{term comma_semantic_future_candidate_controls}
      val class_rows = Const (@{const_name list_all},
        @{typ "(nat => bool) => nat list => bool"}) $
          @{term comma_semantic_future_candidate_class_row_checked} $
          (Const (@{const_name upt}, @{typ "nat => nat => nat list"}) $
            numeral 0 $ length_term control_list)

      fun prove_table () =
        let
          val target = HOLogic.mk_Trueprop
            @{term comma_semantic_future_candidate_class_table_check}
          val definition = @{thm comma_semantic_future_candidate_class_table_check_def}
            RS @{thm eq_reflection}
          val unfolded = Conv.arg_conv (Conv.rewr_conv definition)
            (Thm.cterm_of ctxt target)
          val rhs = HOLogic.dest_Trueprop (Thm.term_of (Thm.rhs_of unfolded))
          fun conjuncts term =
            (case try (HOLogic.dest_bin @{const_name HOL.conj} @{typ bool}) term of
              SOME (left, right) => conjuncts left @ conjuncts right
            | NONE => [term])
          val pieces = conjuncts rhs
          val _ = if length pieces = 5 andalso List.last pieces aconv class_rows then ()
            else error "Candidate class-table definition changed shape"
          val length_equation = prove_true (HOLogic.mk_eq
            (length_term control_list, numeral class_count))
          val source_ids_range = prove_true_in
            (Simplifier.add_simps (([@{thm comma_semantic_future_candidate_class_ids_range_check_def},
                @{thm comma_semantic_future_candidate_id_vector_in_range_def},
                @{thm comma_semantic_future_candidate_class_ids_def}] @
               @{thms comma_semantic_future_nat_list_max.simps} @
               [length_equation])) (proof_context))
            @{term comma_semantic_future_candidate_class_ids_range_check}
          val indexed_rows =
            Comma_Selected_List_Conversion.prove_indexed_list_all
              {ctxt = ctxt,
               predicate = @{term comma_semantic_future_candidate_class_row_checked},
               bound = class_count,
               zero_fact = @{thm comma_indexed_all_zero},
               step_fact = @{thm comma_indexed_all_Suc},
               successor_equation = #equation successor_cache,
               prove_item = fn index => prove_true
                 (@{term comma_semantic_future_candidate_class_row_checked} $
                   numeral index)}
          val length_rewrite = length_equation RS @{thm eq_reflection}
          val rows_conversion = Conv.arg_conv
            (Conv.arg_conv (Conv.rewr_conv length_rewrite))
            (Thm.cterm_of ctxt class_rows)
          val rows_proposition_conversion = Conv.arg_conv rows_conversion
            (Thm.cterm_of ctxt (HOLogic.mk_Trueprop class_rows))
          val rows = Thm.equal_elim (Thm.symmetric rows_proposition_conversion)
            indexed_rows
          fun prove_rhs term =
            (case try (HOLogic.dest_bin @{const_name HOL.conj} @{typ bool}) term of
              SOME (left, right) => @{thm conjI} OF
                [prove_rhs left, prove_rhs right]
            | NONE => if term aconv class_rows then rows
                else if term aconv
                    @{term comma_semantic_future_candidate_class_ids_range_check}
                  then source_ids_range
                  else prove_true term)
          val rhs_proof = prove_rhs rhs
        in Thm.equal_elim (Thm.symmetric unfolded) rhs_proof end

    in {prove_table = prove_table, prove_true = prove_true,
        proof_context = proof_context} end

  (* This checker owns selectors and the bounded successor cache for this
     exact theory. Rebuilding it for every theorem tactic discarded those
     tables and contexts. Keep the
     captured context private to this theory-local closure, reject callers
     from another theory, and serialize access because the selected-list and
     selector owners contain mutable per-checker memo tables. *)
  val owner_context = @{context}
  val owner_theory = Proof_Context.theory_of owner_context
  val owner_theory_id = Context.theory_id owner_theory
  val owner_theory_name = Context.theory_long_name owner_theory
  type checker =
    {prove_table: unit -> thm,
     prove_true: term -> thm,
     proof_context: Proof.context}
  val checker_cache = Synchronized.var
    "comma semantic future candidate checker" (NONE: checker option)

  fun access_checker operation =
    Synchronized.change_result checker_cache (fn cached =>
      let
        val checker = (case cached of
            SOME existing => existing
          | NONE => build owner_context)
      in (operation checker, SOME checker) end)

  fun with_checker ctxt operation =
    let
      val requested_theory = Proof_Context.theory_of ctxt
      val requested_theory_id = Context.theory_id requested_theory
      val same_owner_lineage =
        Context.subthy_id (owner_theory_id, requested_theory_id) andalso
        Context.theory_long_name requested_theory = owner_theory_name
      val _ = if same_owner_lineage then ()
        else error "Future candidate checker used from a foreign theory"
    in access_checker operation end

  val entry_open_theory_name =
    Long_Name.qualify (Resources.theory_qualifier owner_theory_name)
      "Comma_Semantic_Entry_Open"

in
  (* The adjacent entry-open proof imports this theory. Its simproc closes over
     mutable projection memo state, so run its complete tactic under the same
     checker lock and return only a fully forced sequence, never the context.
     The exact theory-name check prevents any other descendant from using this
     callback boundary to operate on the cached checker context. *)
  fun context_tac ctxt operation i state =
    let
      val requested_theory = Proof_Context.theory_of ctxt
      val requested_theory_id = Context.theory_id requested_theory
      val same_entry_open_lineage =
        Context.subthy_id (owner_theory_id, requested_theory_id) andalso
        Context.theory_long_name requested_theory = entry_open_theory_name
      val _ = if same_entry_open_lineage then ()
        else error "Future candidate setup requested from a foreign theory"
      val results = access_checker (fn checker =>
        Seq.list_of (operation (#proof_context checker) i state))
    in Seq.of_list results end

  fun class_table_tac ctxt i =
    let
      val theorem = with_checker ctxt (fn checker => #prove_table checker ())
    in resolve_tac ctxt [theorem] i end

  fun source_rank_tac ctxt state expected i =
    let
      val proposition = HOLogic.mk_eq
        (@{term comma_semantic_concrete_future_rank} $ state, expected)
      val theorem = with_checker ctxt
        (fn checker => #prove_true checker proposition)
    in resolve_tac ctxt [theorem] i end

end
end
\<close>


lemma comma_semantic_future_candidate_class_table_checked:
  "comma_semantic_future_candidate_class_table_check"
  by (tactic \<open>Comma_Semantic_Future_Candidate_Check.class_table_tac @{context} 1\<close>)

lemma comma_semantic_future_candidate_class_row_checked_on_valid:
  assumes table: "comma_semantic_future_candidate_class_table_check"
    and valid: "comma_semantic_future_candidate_class_valid c"
  shows "comma_semantic_future_candidate_class_row_checked c"
proof -
  have rows:
      "list_all comma_semantic_future_candidate_class_row_checked
        [0..<length comma_semantic_future_candidate_controls]"
    using table
    by (simp add: comma_semantic_future_candidate_class_table_check_def)
  have member: "c\<in>set [0..<length comma_semantic_future_candidate_controls]"
    using valid by (simp add: comma_semantic_future_candidate_class_valid_def)
  show ?thesis using rows member by (simp add: list_all_iff)
qed

lemma comma_semantic_future_candidate_class_fork_children_ordered:
  assumes table: "comma_semantic_future_candidate_class_table_check"
    and valid: "comma_semantic_future_candidate_class_valid c"
    and fork: "comma_semantic_future_candidate_class_step c =
      Some (Comma_Future_Fork a)"
  obtains left right where
    "comma_semantic_future_candidate_children ! c =
      (Some left,Some right)"
    "comma_semantic_future_candidate_class_valid left"
    "comma_semantic_future_candidate_class_valid right"
    "comma_semantic_future_candidate_class_children c
      (Comma_Future_Fork a) = [left,right]"
    "comma_semantic_future_candidate_class_output c =
      Some (Comma_Future_Fork a,[left,right])"
proof -
  have checked_row:
      "comma_semantic_future_candidate_class_row_checked c"
    by (rule comma_semantic_future_candidate_class_row_checked_on_valid
      [OF table valid])
  have shape:
      "comma_semantic_future_candidate_class_row_shape c"
    using checked_row
    by (simp add: comma_semantic_future_candidate_class_row_checked_def)
  have children_bound:
      "c < length comma_semantic_future_candidate_children"
    using shape fork
    by (auto simp: comma_semantic_future_candidate_class_row_shape_def
        split: option.splits prod.splits)
  obtain left right where pair:
      "comma_semantic_future_candidate_children ! c =
        (Some left,Some right)"
    and left_valid:
      "comma_semantic_future_candidate_class_valid left"
    and right_valid:
      "comma_semantic_future_candidate_class_valid right"
    using shape fork children_bound
    by (cases "comma_semantic_future_candidate_children ! c")
      (auto simp: comma_semantic_future_candidate_class_row_shape_def
        split: option.splits prod.splits)
  have ordered:
      "comma_semantic_future_candidate_class_children c
        (Comma_Future_Fork a) = [left,right]"
    using fork pair children_bound
    by (simp add: comma_semantic_future_candidate_class_children_def)
  have fork_output_fact:
      "comma_semantic_future_candidate_class_output c =
        Some (Comma_Future_Fork a,[left,right])"
    using fork ordered
    by (simp add: comma_semantic_future_candidate_class_output_def)
  show thesis
    by (rule that[OF pair left_valid right_valid ordered fork_output_fact])
qed

lemma comma_semantic_future_candidate_class_landmine_children_empty:
  assumes table: "comma_semantic_future_candidate_class_table_check"
    and valid: "comma_semantic_future_candidate_class_valid c"
    and landmine: "comma_semantic_future_candidate_class_step c =
      Some Comma_Future_Landmine"
  shows "comma_semantic_future_candidate_class_children c
      Comma_Future_Landmine = []"
    "comma_semantic_future_candidate_class_output c =
      Some (Comma_Future_Landmine,[])"
proof -
  have checked_row:
      "comma_semantic_future_candidate_class_row_checked c"
    by (rule comma_semantic_future_candidate_class_row_checked_on_valid
      [OF table valid])
  have shape:
      "comma_semantic_future_candidate_class_row_shape c"
    using checked_row
    by (simp add: comma_semantic_future_candidate_class_row_checked_def)
  have children_bound:
      "c < length comma_semantic_future_candidate_children"
    using shape landmine
    by (auto simp: comma_semantic_future_candidate_class_row_shape_def
        split: option.splits prod.splits)
  have children:
      "comma_semantic_future_candidate_class_children c
        Comma_Future_Landmine = []"
    using landmine children_bound
    by (simp add: comma_semantic_future_candidate_class_children_def)
  show "comma_semantic_future_candidate_class_children c
      Comma_Future_Landmine = []"
    by (rule children)
  show "comma_semantic_future_candidate_class_output c =
      Some (Comma_Future_Landmine,[])"
    using landmine children
    by (simp add: comma_semantic_future_candidate_class_output_def)
qed

lemma comma_semantic_future_candidate_weighted_phase_binding:
  fixes action :: "nat \<times> (('a \<times> nat) comma_semantic_weighted_crt_dag)"
    and receiver :: "'a \<Rightarrow> nat comma_semantic_weighted_crt_dag"
  assumes phase: "r<924"
    and source_shape: "comma_weighted_crt_shape 0 (snd action)"
    and receiver_shape:
      "\<And>control. comma_weighted_crt_shape 0 (receiver control)"
    and source:
      "comma_weighted_crt_apply action r = Some ((control,d),height)"
    and candidate_lookup:
      "comma_weighted_crt_eval (receiver control)
        ((r+d+height) mod 924) = Some (class_id,0)"
    and table: "comma_semantic_future_candidate_class_table_check"
    and class_id_valid:
      "comma_semantic_future_candidate_class_valid class_id"
  obtains key where
    "comma_semantic_future_candidate_class_row_checked class_id"
    "comma_semantic_future_candidate_class_output class_id = Some key"
    "comma_weighted_crt_apply
      (comma_semantic_future_crt_phase_bind action
        (\<lambda>(selected,delta). comma_weighted_crt_shift delta
          (comma_semantic_future_candidate_output_tree
            (receiver selected)))) r =
      Some (((control,d),Some key),height)"
proof -
  have row:
      "comma_semantic_future_candidate_class_row_checked class_id"
    by (rule comma_semantic_future_candidate_class_row_checked_on_valid
      [OF table class_id_valid])
  obtain selected children where selected_output_fact:
      "comma_semantic_future_candidate_class_output class_id =
        Some (selected,children)"
    using comma_semantic_future_candidate_class_output_on_valid
      [OF class_id_valid] by blast
  let ?future_key = "(selected,children)"
  have mapped_shape:
      "\<And>selected. comma_weighted_crt_shape 0
        (comma_semantic_future_candidate_output_tree (receiver selected))"
    using receiver_shape
    by (simp add: comma_semantic_future_candidate_output_tree_shape)
  have mapped_lookup:
      "comma_weighted_crt_eval
        (comma_semantic_future_candidate_output_tree (receiver control))
        ((r+d+height) mod 924) = Some (Some future_key,0)"
    using candidate_lookup selected_output_fact
    by (simp add: comma_semantic_future_candidate_output_tree_exact)
  have bound:
      "comma_weighted_crt_apply
        (comma_semantic_future_crt_phase_bind action
          (\<lambda>(selected,delta). comma_weighted_crt_shift delta
            (comma_semantic_future_candidate_output_tree
              (receiver selected)))) r =
        Some (((control,d),Some ?future_key),height)"
    by (rule comma_semantic_future_crt_phase_bind_apply_selected_delta
      [OF phase source_shape mapped_shape source mapped_lookup])
  show thesis by (rule that[OF row output bound])
qed

lemma comma_semantic_future_candidate_class_rank_check:
  "comma_semantic_rank_check
    comma_semantic_future_candidate_class_valid
    comma_semantic_future_candidate_class_rank
    comma_semantic_future_candidate_class_children
    comma_semantic_future_candidate_class_step"
proof (unfold comma_semantic_rank_check_def, intro allI impI)
  fix c
  assume valid: "comma_semantic_future_candidate_class_valid c"
  have table: "comma_semantic_future_candidate_class_table_check"
    by (rule comma_semantic_future_candidate_class_table_checked)
  have dimensions:
    "length comma_semantic_future_candidate_controls =
       length comma_semantic_future_candidate_children"
    "length comma_semantic_future_candidate_controls =
       length comma_semantic_future_candidate_ranks"
    and rows: "list_all comma_semantic_future_candidate_class_row_checked
       [0..<length comma_semantic_future_candidate_controls]"
    using table by (auto simp: comma_semantic_future_candidate_class_table_check_def)
  have member: "c \<in> set [0..<length comma_semantic_future_candidate_controls]"
    using valid by (simp add: comma_semantic_future_candidate_class_valid_def)
  have row: "comma_semantic_future_candidate_class_row_checked c"
    using rows member by (simp add: list_all_iff)
  show "comma_semantic_rank_row_checked
      comma_semantic_future_candidate_class_rank
      comma_semantic_future_candidate_class_children
      comma_semantic_future_candidate_class_step c"
    using row by (simp add: comma_semantic_future_candidate_class_row_checked_def)
qed

lemma comma_semantic_future_candidate_index_on_valid:
  assumes table: "comma_semantic_future_candidate_class_table_check"
    and valid: "comma_boundary_valid q"
  shows "comma_semantic_future_candidate_class_index q <
    length comma_semantic_future_candidate_class_ids"
proof -
  have ids_length:
    "length comma_semantic_future_candidate_class_ids = 14784"
    using table by (simp add: comma_semantic_future_candidate_class_table_check_def
        comma_boundary_states_card)
  show ?thesis
    using valid ids_length
    by (cases q) (auto simp: comma_semantic_future_candidate_class_index_def
        comma_boundary_valid_def)
  qed

lemma comma_semantic_future_candidate_class_of_index_exact:
  assumes table: "comma_semantic_future_candidate_class_table_check"
    and valid: "comma_boundary_valid q"
  shows "comma_semantic_future_candidate_class_of q =
    comma_semantic_future_candidate_class_ids !
      comma_semantic_future_candidate_class_index q"
proof -
  have index:
    "comma_semantic_future_candidate_class_index q <
      length comma_semantic_future_candidate_class_ids"
    by (rule comma_semantic_future_candidate_index_on_valid[OF table valid])
  show ?thesis
    using valid index
    by (simp add: comma_semantic_future_candidate_class_of_def)
qed

lemma comma_semantic_future_candidate_children_off_control:
  assumes selected: "comma_semantic_future_candidate_class_step c = Some selected"
    and different: "control \<noteq> selected"
  shows "comma_semantic_future_candidate_class_children c control = []"
  using selected different
  by (simp add: comma_semantic_future_candidate_class_children_def)

lemma comma_semantic_boundary_children_off_control:
  assumes selected:
      "comma_semantic_boundary_control_step provider q = Some selected"
    and different: "control \<noteq> selected"
  shows "comma_semantic_boundary_children provider q control = []"
  using selected different
  by (cases "comma_semantic_boundary_step provider q")
     (auto simp: comma_semantic_boundary_control_step_def
       comma_semantic_boundary_children_def
       split: comma_finite_outcome.splits)

lemma comma_semantic_future_candidate_provider_row_on_valid:
  assumes checked: "comma_semantic_future_candidate_provider_check"
    and valid: "comma_boundary_valid q"
  shows "comma_semantic_future_candidate_provider_row q"
proof -
  obtain kind a r where q_eq: "q=(kind,a,r)" by (cases q) auto
  have bounds: "2\<le>a \<and> a\<le>9 \<and> r<924"
    using valid q_eq by (auto simp: comma_boundary_valid_def)
  have kind_checked:
      "comma_semantic_future_candidate_provider_kind_check kind"
    using checked by (cases kind)
      (simp only: comma_semantic_future_candidate_provider_check_def)
  have index_checks:
      "list_all (comma_semantic_future_candidate_provider_index_check kind)
        [0..<8]"
    using kind_checked
    by (simp only: comma_semantic_future_candidate_provider_kind_check_def)
  have index_bound: "a-2<8" using bounds by arith
  have index_member: "a-2\<in>set [0..<8]" using index_bound by simp
  have selected_index:
      "comma_semantic_future_candidate_provider_index_check kind (a-2)"
    using index_checks index_member by (simp add: list_all_iff)
  have cell_checks:
      "list_all (comma_semantic_future_candidate_provider_cell kind (a-2))
        [0..<924]"
    using selected_index
    by (simp only: comma_semantic_future_candidate_provider_index_check_def)
  have phase_member: "r\<in>set [0..<924]" using bounds by simp
  have selected_cell:
      "comma_semantic_future_candidate_provider_cell kind (a-2) r"
    using cell_checks phase_member by (simp add: list_all_iff)
  have selected_row:
      "comma_semantic_future_candidate_provider_row (kind,(a-2)+2,r)"
    using selected_cell
    by (simp only: comma_semantic_future_candidate_provider_cell_def)
  have exponent: "(a-2)+2=a" using bounds by arith
  have selected_state: "q=(kind,(a-2)+2,r)"
    using q_eq exponent by simp
  show ?thesis using selected_row selected_state by simp
qed

lemma comma_semantic_future_candidate_class_map_row:
  assumes table: "comma_semantic_future_candidate_class_table_check"
    and checked: "comma_semantic_future_candidate_provider_check"
    and valid: "comma_boundary_valid q"
  shows "comma_semantic_future_candidate_class_index q <
      length comma_semantic_future_candidate_class_ids"
    "comma_semantic_future_candidate_class_valid
      (comma_semantic_future_candidate_class_of q)"
    "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      comma_semantic_future_candidate_class_step
        (comma_semantic_future_candidate_class_of q)"
    "map comma_semantic_future_candidate_class_of
      (comma_semantic_boundary_children comma_semantic_decade_summary q control) =
      comma_semantic_future_candidate_class_children
        (comma_semantic_future_candidate_class_of q) control"
proof -
  have index_bound:
    "comma_semantic_future_candidate_class_index q <
      length comma_semantic_future_candidate_class_ids"
    by (rule comma_semantic_future_candidate_index_on_valid[OF table valid])
  have row: "comma_semantic_future_candidate_provider_row q"
    by (rule comma_semantic_future_candidate_provider_row_on_valid
      [OF checked valid])
  obtain selected where class_step:
      "comma_semantic_future_candidate_class_step
        (comma_semantic_future_candidate_class_of q) = Some selected"
    and control_step:
      "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
        Some selected"
    and selected_children:
      "map comma_semantic_future_candidate_class_of
        (comma_semantic_boundary_children comma_semantic_decade_summary q selected) =
      comma_semantic_future_candidate_class_children
        (comma_semantic_future_candidate_class_of q) selected"
    using row by (auto simp: comma_semantic_future_candidate_provider_row_def
        comma_semantic_future_candidate_class_output_def Let_def
        split: option.splits)
  show "comma_semantic_future_candidate_class_index q <
      length comma_semantic_future_candidate_class_ids"
    by (rule index_bound)
  show "comma_semantic_future_candidate_class_valid
      (comma_semantic_future_candidate_class_of q)"
    using class_step by (simp add: comma_semantic_future_candidate_class_step_def
        comma_semantic_future_candidate_class_valid_def split: if_splits)
  show "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
      comma_semantic_future_candidate_class_step
        (comma_semantic_future_candidate_class_of q)"
    using class_step control_step by simp
  show "map comma_semantic_future_candidate_class_of
      (comma_semantic_boundary_children comma_semantic_decade_summary q control) =
      comma_semantic_future_candidate_class_children
        (comma_semantic_future_candidate_class_of q) control"
  proof (cases "control = selected")
    case True
    then show ?thesis using selected_children by simp
  next
    case False
    have source_empty:
      "comma_semantic_boundary_children comma_semantic_decade_summary q control = []"
      by (rule comma_semantic_boundary_children_off_control[OF control_step False])
    have class_empty:
      "comma_semantic_future_candidate_class_children
        (comma_semantic_future_candidate_class_of q) control = []"
      by (rule comma_semantic_future_candidate_children_off_control[OF class_step False])
    show ?thesis using source_empty class_empty by simp
  qed
qed

lemma comma_semantic_future_provider_check_lifts_rank:
  assumes provider_check: "comma_semantic_future_candidate_provider_check"
  shows "comma_semantic_rank_check comma_boundary_valid
    comma_semantic_concrete_future_rank
    (comma_semantic_boundary_children comma_semantic_decade_summary)
    (comma_semantic_boundary_control_step comma_semantic_decade_summary)"
proof -
  have table: "comma_semantic_future_candidate_class_table_check"
    by (rule comma_semantic_future_candidate_class_table_checked)
  have class_check:
    "comma_semantic_rank_check
      comma_semantic_future_candidate_class_valid
      comma_semantic_future_candidate_class_rank
      comma_semantic_future_candidate_class_children
      comma_semantic_future_candidate_class_step"
    by (rule comma_semantic_future_candidate_class_rank_check)
  have maps_valid:
    "\<And>q. comma_boundary_valid q \<Longrightarrow>
      comma_semantic_future_candidate_class_valid
        (comma_semantic_future_candidate_class_of q)"
  proof -
    fix q assume valid: "comma_boundary_valid q"
    from comma_semantic_future_candidate_class_map_row
      [OF table provider_check valid]
    show "comma_semantic_future_candidate_class_valid
        (comma_semantic_future_candidate_class_of q)"
      by blast
  qed
  have maps_step:
    "\<And>q. comma_boundary_valid q \<Longrightarrow>
      comma_semantic_boundary_control_step comma_semantic_decade_summary q =
        comma_semantic_future_candidate_class_step
          (comma_semantic_future_candidate_class_of q)"
  proof -
    fix q assume valid: "comma_boundary_valid q"
    from comma_semantic_future_candidate_class_map_row
      [OF table provider_check valid]
    show "comma_semantic_boundary_control_step comma_semantic_decade_summary q =
        comma_semantic_future_candidate_class_step
          (comma_semantic_future_candidate_class_of q)"
      by blast
  qed
  have maps_children:
    "\<And>q control. comma_boundary_valid q \<Longrightarrow>
      map comma_semantic_future_candidate_class_of
        (comma_semantic_boundary_children comma_semantic_decade_summary q control) =
      comma_semantic_future_candidate_class_children
        (comma_semantic_future_candidate_class_of q) control"
  proof -
    fix q control assume valid: "comma_boundary_valid q"
    from comma_semantic_future_candidate_class_map_row
      [OF table provider_check valid]
    show "map comma_semantic_future_candidate_class_of
        (comma_semantic_boundary_children comma_semantic_decade_summary q control) =
      comma_semantic_future_candidate_class_children
        (comma_semantic_future_candidate_class_of q) control"
      by blast
  qed
  show ?thesis
    unfolding comma_semantic_concrete_future_rank_def comp_def
    by (rule comma_semantic_rank_check_lifts_through_class_map
      [OF class_check maps_valid maps_step maps_children])
qed

lemma comma_semantic_concrete_source20_unranked:
  "comma_semantic_concrete_future_rank (Comma_N,2,10) = None"
  by (tactic \<open>Comma_Semantic_Future_Candidate_Check.source_rank_tac
    @{context} @{term "(Comma_N,2,10)"} @{term "(None :: nat option)"} 1\<close>)

lemma comma_semantic_concrete_source20_z_ranked_exact:
  "comma_semantic_concrete_future_rank (Comma_Z,2,10) =
    Some (the (comma_semantic_concrete_future_rank (Comma_Z,2,10)))"
  by (tactic \<open>Comma_Semantic_Future_Candidate_Check.source_rank_tac
    @{context} @{term "(Comma_Z,2,10)"}
      @{term "Some (the (comma_semantic_concrete_future_rank (Comma_Z,2,10)))"} 1\<close>)

lemma comma_semantic_concrete_source20_z_ranked:
  "\<exists>rank. comma_semantic_concrete_future_rank (Comma_Z,2,10) = Some rank"
  using comma_semantic_concrete_source20_z_ranked_exact by blast

ML \<open>
  val published = @{thms
    comma_semantic_future_candidate_class_index_def
    comma_semantic_future_candidate_class_of_def
    comma_semantic_future_candidate_class_valid_def
    comma_semantic_future_candidate_class_step_def
    comma_semantic_future_candidate_class_rank_def
    comma_semantic_future_candidate_class_children_def
    comma_semantic_future_candidate_class_output_on_valid
    comma_semantic_future_candidate_output_tree_exact
    comma_semantic_future_candidate_output_tree_shape
    comma_semantic_future_candidate_class_output_def
    comma_semantic_future_candidate_class_row_shape_def
    comma_semantic_future_candidate_class_row_checked_def
    comma_semantic_future_candidate_class_ids_range_check_def
    comma_semantic_future_candidate_class_table_check_def
    comma_semantic_future_candidate_provider_cell_def
    comma_semantic_future_candidate_provider_index_check_def
    comma_semantic_future_candidate_provider_kind_check_def
    comma_semantic_future_candidate_provider_row_def
    comma_semantic_future_candidate_provider_check_def
    comma_semantic_concrete_future_rank_def
    comma_semantic_future_candidate_class_table_checked
    comma_semantic_future_candidate_class_row_checked_on_valid
    comma_semantic_future_candidate_class_fork_children_ordered
    comma_semantic_future_candidate_class_landmine_children_empty
    comma_semantic_future_candidate_weighted_phase_binding
    comma_semantic_future_candidate_class_rank_check
    comma_semantic_future_candidate_index_on_valid
    comma_semantic_future_candidate_class_of_index_exact
    comma_semantic_future_candidate_provider_row_on_valid
    comma_semantic_future_candidate_class_map_row
    comma_semantic_future_provider_check_lifts_rank
    comma_semantic_concrete_future_rank_check
    comma_semantic_boundary_step_decisive_round
    comma_semantic_concrete_source20_unranked
    comma_semantic_concrete_source20_z_ranked_exact
    comma_semantic_concrete_source20_z_ranked}
  val _ = Thm.consolidate published
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Future candidate class certificate and concrete provider rank" published
\<close>

end
