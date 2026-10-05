theory Comma_Semantic_Future_Instance
  imports Comma_Semantic_Future_Candidate_Data
begin

text \<open>
The candidate CID map is only a proposed quotient.  This instance gives
classes no authority until both its finite class rows and its source binding
to the checked semantic decade provider have kernel-checked certificates.
The source map is a compact binding; controls, ordered children, and ranks
are stored once per class.  Exponent weights remain occurrence data.
\<close>

definition comma_semantic_future_candidate_class_index ::
    "comma_boundary_state \<Rightarrow> nat" where
  "comma_semantic_future_candidate_class_index q =
    (case q of (kind,a,r) \<Rightarrow>
      (if kind=Comma_N then 0 else 8*924) + (a-2)*924 + r)"

definition comma_semantic_future_candidate_class_of ::
    "comma_boundary_state \<Rightarrow> nat" where
  "comma_semantic_future_candidate_class_of q =
    (let index = comma_semantic_future_candidate_class_index q in
      if comma_boundary_valid q \<and>
          index < length comma_semantic_future_candidate_class_ids
      then comma_semantic_future_candidate_class_ids ! index
      else length comma_semantic_future_candidate_class_ids +
        length comma_semantic_future_candidate_controls +
        length comma_semantic_future_candidate_children +
        length comma_semantic_future_candidate_ranks + 1)"

definition comma_semantic_future_candidate_class_valid :: "nat \<Rightarrow> bool" where
  "comma_semantic_future_candidate_class_valid c \<longleftrightarrow>
    c < length comma_semantic_future_candidate_controls"

definition comma_semantic_future_candidate_class_step ::
    "nat \<Rightarrow> comma_future_control option" where
  "comma_semantic_future_candidate_class_step c =
    (if comma_semantic_future_candidate_class_valid c then
       Some (comma_semantic_future_candidate_controls ! c)
     else None)"

definition comma_semantic_future_candidate_class_rank ::
    "nat \<Rightarrow> nat option" where
  "comma_semantic_future_candidate_class_rank c =
    (if c < length comma_semantic_future_candidate_ranks
     then comma_semantic_future_candidate_ranks ! c else None)"

definition comma_semantic_future_candidate_class_children ::
    "nat \<Rightarrow> comma_future_control \<Rightarrow> nat list" where
  "comma_semantic_future_candidate_class_children c control =
    (if comma_semantic_future_candidate_class_step c = Some control then
       (if c < length comma_semantic_future_candidate_children then
         (case control of
            Comma_Future_Fork a \<Rightarrow>
              (case comma_semantic_future_candidate_children ! c of
                 (left,right) \<Rightarrow> map_filter id [left,right])
          | Comma_Future_Landmine \<Rightarrow> [])
        else [])
     else [])"

definition comma_semantic_future_candidate_class_row_shape ::
    "nat \<Rightarrow> bool" where
  "comma_semantic_future_candidate_class_row_shape c =
    (case comma_semantic_future_candidate_class_step c of
       None \<Rightarrow> False
     | Some control \<Rightarrow>
         (if c < length comma_semantic_future_candidate_children then
            (case (control, comma_semantic_future_candidate_children ! c) of
              (Comma_Future_Fork a, (Some left, Some right)) \<Rightarrow>
                2 \<le> a \<and> a \<le> 9 \<and>
                comma_semantic_future_candidate_class_valid left \<and>
                comma_semantic_future_candidate_class_valid right
            | (Comma_Future_Landmine, (None, None)) \<Rightarrow> True
            | _ \<Rightarrow> False)
          else False))"

definition comma_semantic_future_candidate_class_row_checked ::
    "nat \<Rightarrow> bool" where
  "comma_semantic_future_candidate_class_row_checked c =
    (comma_semantic_future_candidate_class_row_shape c \<and>
     comma_semantic_rank_row_checked
       comma_semantic_future_candidate_class_rank
       comma_semantic_future_candidate_class_children
       comma_semantic_future_candidate_class_step c)"

definition comma_semantic_future_candidate_class_table_check :: bool where
  "comma_semantic_future_candidate_class_table_check \<longleftrightarrow>
    length comma_semantic_future_candidate_class_ids =
      length comma_boundary_states \<and>
    length comma_semantic_future_candidate_controls =
      length comma_semantic_future_candidate_children \<and>
    length comma_semantic_future_candidate_controls =
      length comma_semantic_future_candidate_ranks \<and>
    list_all comma_semantic_future_candidate_class_row_checked
      [0..<length comma_semantic_future_candidate_controls]"

definition comma_semantic_future_candidate_provider_row ::
    "comma_boundary_state \<Rightarrow> bool" where
  "comma_semantic_future_candidate_provider_row q =
    (let c = comma_semantic_future_candidate_class_of q in
      (case comma_semantic_future_candidate_class_step c of
         None \<Rightarrow> False
       | Some control \<Rightarrow>
           comma_semantic_boundary_control_step comma_semantic_decade_summary q =
             Some control \<and>
           map comma_semantic_future_candidate_class_of
             (comma_semantic_boundary_children comma_semantic_decade_summary q control) =
             comma_semantic_future_candidate_class_children c control))"

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
  have budget:
    "Suc (9-comma_sector_number (comma_finite_initial q)) \<le> 9"
    using initial_admitted
    by (cases "comma_finite_initial q")
      (auto simp: comma_round_admitted.simps comma_sector_number.simps)
  have decisive_fast:
    "comma_decisive_endpoint_round r (comma_finite_initial q) =
      comma_fast_round_aux 9 r (comma_finite_initial q)"
    by (rule comma_decisive_endpoint_round_refines_fast
      [OF initial_admitted budget])
  have fast_close:
    "comma_fast_round_aux 9 r (comma_finite_initial q) =
      snd (snd (comma_round_close r (comma_finite_initial q)))"
    by (rule comma_fast_round_aux_correct[OF initial_admitted budget])
  have event:
    "comma_decisive_endpoint_round r (comma_finite_initial q) =
      snd (snd (comma_round_close r (comma_finite_initial q)))"
    by (rule trans[OF decisive_fast fast_close])
  show ?thesis
    using valid event
    by (simp add: comma_semantic_boundary_step_def q)
qed

ML \<open>
structure Comma_Semantic_Future_Candidate_Check =
struct
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

  fun make ctxt =
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
          val _ = if length pieces = 4 andalso List.last pieces aconv class_rows then ()
            else error "Candidate class-table definition changed shape"
          val length_equation = prove_true (HOLogic.mk_eq
            (length_term control_list, numeral class_count))
          val indexed_rows =
            Comma_Selected_List_Conversion.prove_indexed_list_all
              {ctxt = ctxt,
               predicate = @{term comma_semantic_future_candidate_class_row_checked},
               bound = class_count,
               zero_fact = @{thm comma_indexed_all_zero},
               step_fact = @{thm comma_indexed_all_Suc},
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
            | NONE => if term aconv class_rows then rows else prove_true term)
          val rhs_proof = prove_rhs rhs
        in Thm.equal_elim (Thm.symmetric unfolded) rhs_proof end

      fun prove_provider_check () =
        let
          val projector = Comma_Semantic_B1_B32_Projection.make_projector ctxt
          val fast_kernel = Comma_Fast_Kernel.make ctxt
          val endpoint_kernel = Comma_Decisive_Endpoint_Kernel.make ctxt
            (#context fast_kernel)
          fun dest_nat_at_most bound term =
            (case try HOLogic.dest_number term of
              SOME (typ, value) =>
                if typ = @{typ nat} andalso value >= 0 andalso
                    value <= IntInf.fromInt bound
                then SOME (IntInf.toInt value) else NONE
            | NONE => NONE)
          fun power_projection cterm =
            (case strip_comb (Thm.term_of cterm) of
              (Const (name, _), [base, root, phase]) =>
                if name <> @{const_name comma_semantic_b1_crt_power_result} then NONE
                else
                  (case (dest_nat_at_most 5 base,
                      dest_nat_at_most 45 root,
                      dest_nat_at_most 923 phase) of
                    (SOME 5, SOME root_index, SOME phase_index) =>
                      let
                        val query = #query (projector root_index phase_index)
                        val (lhs, _) = HOLogic.dest_eq
                          (HOLogic.dest_Trueprop (Thm.prop_of query))
                        val _ = if lhs aconv Thm.term_of cterm andalso
                            Thm.nprems_of query = 0 andalso null (Thm.hyps_of query) andalso
                            null (Thm.tpairs_of query)
                          then () else error "B32 projection returned a mismatched query"
                      in SOME (query RS @{thm eq_reflection}) end
                  | _ => NONE)
            | _ => NONE)
          val projection_proc = Simplifier.make_simproc ctxt
            {name = "semantic_future_cached_b32_projection",
             kind = Simplifier.Simproc,
             lhss = [Comma_Selected_List_Conversion.schematize
               @{term "comma_semantic_b1_crt_power_result 5 root phase"}],
             proc = fn _ => fn _ => power_projection, identifier = []}
          val provider_rules = @{thms
            comma_semantic_future_candidate_provider_row_def
            comma_semantic_future_candidate_provider_cell_def
            comma_semantic_future_candidate_provider_index_check_def
            comma_semantic_future_candidate_provider_kind_check_def
            comma_semantic_future_candidate_provider_check_def
            comma_semantic_future_candidate_class_index_def
            comma_semantic_future_candidate_class_of_def
            comma_semantic_future_candidate_class_valid_def
            comma_semantic_future_candidate_class_step_def
            comma_semantic_future_candidate_class_children_def
            comma_semantic_decade_summary_def comma_decade_admitted.simps
            comma_terminal_weight_decode_def comma_terminal_weight_terminal_def
            comma_semantic_boundary_control_step_def
            comma_semantic_boundary_step_decisive_round
            comma_semantic_boundary_event_outcome.simps
            comma_semantic_boundary_control_of.simps
            comma_semantic_boundary_children_def
            comma_native_boundary_children_def comma_boundary_valid_def
            comma_finite_initial_def comma_decisive_endpoint_round.simps
            comma_offset_orbit_def
            comma_digit_orbit_sum_def}
          val selector_procs =
            [#procedure ids, #procedure controls, #procedure children, #procedure ranks]
          val provider_context = #context endpoint_kernel
            |> fold Simplifier.add_proc selector_procs
            |> Simplifier.add_proc projection_proc
            |> Simplifier.add_simps simps
            |> Simplifier.add_simps provider_rules
          val cell = @{term comma_semantic_future_candidate_provider_cell}
          val index_check =
            @{term comma_semantic_future_candidate_provider_index_check}
          val kind_check =
            @{term comma_semantic_future_candidate_provider_kind_check}
          val provider_check =
            @{term comma_semantic_future_candidate_provider_check}
          fun prove_index kind a_index =
            let
              val cell_predicate = cell $ kind $ numeral a_index
              val rows =
                Comma_Selected_List_Conversion.prove_indexed_list_all
                  {ctxt = ctxt, predicate = cell_predicate, bound = 924,
                   zero_fact = @{thm comma_indexed_all_zero},
                   step_fact = @{thm comma_indexed_all_Suc},
                   prove_item = fn r => prove_true_in provider_context
                     (cell $ kind $ numeral a_index $ numeral r)}
              val goal = HOLogic.mk_Trueprop
                (index_check $ kind $ numeral a_index)
            in Goal.prove ctxt [] [] goal
              (fn _ => Simplifier.asm_full_simp_tac
                (provider_context addsimps [rows]) 1) end
          fun prove_kind kind =
            let
              val indices = index_check $ kind
              val checked =
                Comma_Selected_List_Conversion.prove_indexed_list_all
                  {ctxt = ctxt, predicate = indices, bound = 8,
                   zero_fact = @{thm comma_indexed_all_zero},
                   step_fact = @{thm comma_indexed_all_Suc},
                   prove_item = prove_index kind}
              val goal = HOLogic.mk_Trueprop (kind_check $ kind)
            in Goal.prove ctxt [] [] goal
              (fn _ => Simplifier.asm_full_simp_tac
                (provider_context addsimps [checked]) 1) end
          val checked_n = prove_kind @{term Comma_N}
          val checked_z = prove_kind @{term Comma_Z}
          val goal = HOLogic.mk_Trueprop provider_check
        in Goal.prove ctxt [] [] goal
          (fn _ => Simplifier.asm_full_simp_tac
            (provider_context addsimps [checked_n, checked_z]) 1) end
    in {prove_table = prove_table, prove_true = prove_true,
        proof_context = proof_context,
        prove_provider_check = prove_provider_check} end

  fun class_table_tac ctxt i =
    let val checker = make ctxt in resolve_tac ctxt [#prove_table checker ()] i end

  fun source_rank_tac ctxt state expected i =
    let
      val checker = make ctxt
      val proposition = HOLogic.mk_eq
        (@{term comma_semantic_concrete_future_rank} $ state, expected)
      val theorem = #prove_true checker proposition
    in resolve_tac ctxt [theorem] i end

  fun provider_check_tac ctxt i =
    let val checker = make ctxt in
      resolve_tac ctxt [#prove_provider_check checker ()] i
    end
end
\<close>

lemma comma_semantic_future_candidate_class_table_checked:
  "comma_semantic_future_candidate_class_table_check"
  by (tactic \<open>Comma_Semantic_Future_Candidate_Check.class_table_tac @{context} 1\<close>)

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
  using checked valid
  by (cases q) (auto simp: comma_semantic_future_candidate_provider_check_def
      comma_semantic_future_candidate_provider_kind_check_def
      comma_semantic_future_candidate_provider_index_check_def
      comma_semantic_future_candidate_provider_cell_def
      comma_boundary_valid_def list_all_iff set_upt)

lemma comma_semantic_future_candidate_provider_check_checked:
  "comma_semantic_future_candidate_provider_check"
  by (tactic \<open>Comma_Semantic_Future_Candidate_Check.provider_check_tac
    @{context} 1\<close>)

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
    using row by (auto simp: comma_semantic_future_candidate_provider_row_def Let_def
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

lemma comma_semantic_concrete_future_rank_check:
  "comma_semantic_rank_check comma_boundary_valid
    comma_semantic_concrete_future_rank
    (comma_semantic_boundary_children comma_semantic_decade_summary)
    (comma_semantic_boundary_control_step comma_semantic_decade_summary)"
  by (rule comma_semantic_future_provider_check_lifts_rank
      [OF comma_semantic_future_candidate_provider_check_checked])

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

lemma comma_semantic_concrete_future_paths_agree_if_provider_checked:
  assumes provider_check: "comma_semantic_future_candidate_provider_check"
  shows "\<forall>q p left right. comma_boundary_valid q \<longrightarrow>
    5 \<le> p \<longrightarrow> p mod 924 = snd (snd q) \<longrightarrow>
    comma_semantic_infinite_path comma_boundary_value q p left \<longrightarrow>
    comma_semantic_infinite_path comma_boundary_value q p right \<longrightarrow>
    (\<forall>n. left n = right n)"
proof -
  have rank_check:
    "comma_semantic_rank_check comma_boundary_valid
      comma_semantic_concrete_future_rank
      (comma_semantic_boundary_children comma_semantic_decade_summary)
      (comma_semantic_boundary_control_step comma_semantic_decade_summary)"
    by (rule comma_semantic_future_provider_check_lifts_rank[OF provider_check])
  show ?thesis
    by (rule comma_semantic_infinite_paths_agree
      [OF comma_semantic_concrete_boundary_strong_occurrence_bridge rank_check])
qed

lemma comma_semantic_concrete_source20_infinite_path_if_provider_checked:
  assumes provider_check: "comma_semantic_future_candidate_provider_check"
  shows "\<exists>stream. comma_semantic_infinite_path comma_boundary_value
    (Comma_N,2,10) 10 stream"
proof -
  have rank_check:
    "comma_semantic_rank_check comma_boundary_valid
      comma_semantic_concrete_future_rank
      (comma_semantic_boundary_children comma_semantic_decade_summary)
      (comma_semantic_boundary_control_step comma_semantic_decade_summary)"
    by (rule comma_semantic_future_provider_check_lifts_rank[OF provider_check])
  have source_valid: "comma_boundary_valid (Comma_N,2,10)"
    by (simp add: comma_boundary_valid_def)
  have phase_match: "10 mod 924 = snd (snd (Comma_N,2,10))"
    by simp
  show ?thesis
  proof (rule comma_semantic_unranked_state_has_infinite_path
      [where q="(Comma_N,2,10)" and p=10,
       OF comma_semantic_concrete_boundary_occurrence_bridge rank_check])
    show "comma_boundary_valid (Comma_N,2,10)" by (rule source_valid)
    show "5 \<le> 10" by simp
    show "10 mod 924 = snd (snd (Comma_N,2,10))" by (rule phase_match)
    show "comma_semantic_concrete_future_rank (Comma_N,2,10) = None"
      by (rule comma_semantic_concrete_source20_unranked)
  qed
qed

theorem comma_semantic_concrete_source20_infinite_path:
  "\<exists>stream. comma_semantic_infinite_path comma_boundary_value
    (Comma_N,2,10) 10 stream"
  by (rule comma_semantic_concrete_source20_infinite_path_if_provider_checked
      [OF comma_semantic_future_candidate_provider_check_checked])

theorem comma_semantic_concrete_future_paths_agree:
  "\<forall>q p left right. comma_boundary_valid q \<longrightarrow>
    5 \<le> p \<longrightarrow> p mod 924 = snd (snd q) \<longrightarrow>
    comma_semantic_infinite_path comma_boundary_value q p left \<longrightarrow>
    comma_semantic_infinite_path comma_boundary_value q p right \<longrightarrow>
    (\<forall>n. left n = right n)"
  by (rule comma_semantic_concrete_future_paths_agree_if_provider_checked
      [OF comma_semantic_future_candidate_provider_check_checked])

lemma comma_semantic_concrete_source20_path_has_unique_unranked_child_if_provider_checked:
  assumes provider_check: "comma_semantic_future_candidate_provider_check"
    and path: "comma_semantic_infinite_path comma_boundary_value
      (Comma_N,2,10) 10 stream"
  obtains control endpoint weight child tail where
    "comma_semantic_boundary_control_step comma_semantic_decade_summary
      (Comma_N,2,10) = Some control"
    "comma_literal_path weight
      (comma_boundary_value (Comma_N,2,10) 10) endpoint"
    "child \<in> set (comma_semantic_boundary_children comma_semantic_decade_summary
      (Comma_N,2,10) control)"
    "stream (Suc weight) =
      comma_boundary_value child
        (10 + comma_semantic_boundary_exponent_delta comma_semantic_decade_summary
          (Comma_N,2,10) control)"
    "comma_boundary_valid child"
    "5 \<le> 10 + comma_semantic_boundary_exponent_delta
      comma_semantic_decade_summary (Comma_N,2,10) control"
    "(10 + comma_semantic_boundary_exponent_delta comma_semantic_decade_summary
      (Comma_N,2,10) control) mod 924 = snd (snd child)"
    "comma_semantic_infinite_path comma_boundary_value child
      (10 + comma_semantic_boundary_exponent_delta comma_semantic_decade_summary
        (Comma_N,2,10) control) tail"
    "comma_semantic_concrete_future_rank (Comma_N,2,10) = None"
    "comma_semantic_concrete_future_rank child = None"
    "\<forall>other\<in>set (comma_semantic_boundary_children comma_semantic_decade_summary
      (Comma_N,2,10) control).
        other \<noteq> child \<longrightarrow>
        comma_semantic_concrete_future_rank other \<noteq> None"
proof -
  have rank_check:
    "comma_semantic_rank_check comma_boundary_valid
      comma_semantic_concrete_future_rank
      (comma_semantic_boundary_children comma_semantic_decade_summary)
      (comma_semantic_boundary_control_step comma_semantic_decade_summary)"
    by (rule comma_semantic_future_provider_check_lifts_rank[OF provider_check])
  have source_valid: "comma_boundary_valid (Comma_N,2,10)"
    by (simp add: comma_boundary_valid_def)
  have phase_match: "10 mod 924 = snd (snd (Comma_N,2,10))"
    by simp
  show thesis
    by (rule comma_semantic_infinite_path_forces_unique_unranked_child
      [where q="(Comma_N,2,10)" and p=10,
       OF comma_semantic_concrete_boundary_occurrence_bridge rank_check
         source_valid])
      (use path phase_match in simp_all;
       simp_all add: comma_semantic_concrete_source20_unranked)
qed

theorem comma_semantic_concrete_source20_path_has_unique_unranked_child:
  assumes path: "comma_semantic_infinite_path comma_boundary_value
      (Comma_N,2,10) 10 stream"
  obtains control endpoint weight child tail where
    "comma_semantic_boundary_control_step comma_semantic_decade_summary
      (Comma_N,2,10) = Some control"
    "comma_literal_path weight
      (comma_boundary_value (Comma_N,2,10) 10) endpoint"
    "child \<in> set (comma_semantic_boundary_children comma_semantic_decade_summary
      (Comma_N,2,10) control)"
    "stream (Suc weight) =
      comma_boundary_value child
        (10 + comma_semantic_boundary_exponent_delta comma_semantic_decade_summary
          (Comma_N,2,10) control)"
    "comma_boundary_valid child"
    "5 \<le> 10 + comma_semantic_boundary_exponent_delta
      comma_semantic_decade_summary (Comma_N,2,10) control"
    "(10 + comma_semantic_boundary_exponent_delta comma_semantic_decade_summary
      (Comma_N,2,10) control) mod 924 = snd (snd child)"
    "comma_semantic_infinite_path comma_boundary_value child
      (10 + comma_semantic_boundary_exponent_delta comma_semantic_decade_summary
        (Comma_N,2,10) control) tail"
    "comma_semantic_concrete_future_rank (Comma_N,2,10) = None"
    "comma_semantic_concrete_future_rank child = None"
    "\<forall>other\<in>set (comma_semantic_boundary_children comma_semantic_decade_summary
      (Comma_N,2,10) control).
        other \<noteq> child \<longrightarrow>
        comma_semantic_concrete_future_rank other \<noteq> None"
  using comma_semantic_concrete_source20_path_has_unique_unranked_child_if_provider_checked
    [OF comma_semantic_future_candidate_provider_check_checked path] .

theorem comma_semantic_concrete_source20_z_no_infinite_path:
  "\<not> comma_semantic_infinite_path comma_boundary_value
    (Comma_Z,2,10) 10 stream"
proof -
  have state_valid: "comma_boundary_valid (Comma_Z,2,10)"
    by (simp add: comma_boundary_valid_def)
  have exponent: "5 \<le> 10" by simp
  have phase_match: "10 mod 924 = snd (snd (Comma_Z,2,10))" by simp
  obtain k where ranked:
      "comma_semantic_concrete_future_rank (Comma_Z,2,10) = Some k"
    using comma_semantic_concrete_source20_z_ranked by blast
  show ?thesis
    by (rule comma_semantic_ranked_state_no_infinite_path
      [OF comma_semantic_concrete_boundary_occurrence_bridge
        comma_semantic_concrete_future_rank_check state_valid exponent
        phase_match ranked])
qed

ML \<open>
  val checked = @{thms
    comma_semantic_future_candidate_class_table_checked
    comma_semantic_future_candidate_provider_check_checked
    comma_semantic_future_candidate_class_rank_check
    comma_semantic_future_provider_check_lifts_rank
    comma_semantic_concrete_future_rank_check
    comma_semantic_concrete_source20_unranked
    comma_semantic_concrete_source20_z_ranked_exact
    comma_semantic_concrete_future_paths_agree_if_provider_checked
    comma_semantic_concrete_source20_infinite_path_if_provider_checked
    comma_semantic_concrete_source20_path_has_unique_unranked_child_if_provider_checked
    comma_semantic_concrete_future_paths_agree
    comma_semantic_concrete_source20_infinite_path
    comma_semantic_concrete_source20_path_has_unique_unranked_child
    comma_semantic_concrete_source20_z_no_infinite_path
    comma_semantic_boundary_step_decisive_round};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "semantic FutureCID candidate checker and path lift" checked;
\<close>

end
