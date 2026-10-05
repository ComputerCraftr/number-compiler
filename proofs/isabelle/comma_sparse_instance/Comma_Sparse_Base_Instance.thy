theory Comma_Sparse_Base_Instance
  imports Comma_Compact_B1.Comma_Compact_B1
    Comma_Semantic_B1.Comma_Semantic_B1_Columns
begin

unbundle bit_operations_syntax

text \<open>The published B1 table is evaluated from the compact, source-selected
endpoint constructor. Each row value is a closed sparse word obtained from one
root equation; its refinement is that equation transported through the checked
compact B1 theorem. No response evaluator or response-node proof table is used
by this production owner.\<close>

definition comma_sparse_base_word_checked ::
    "nat \<Rightarrow> comma_sparse_word \<Rightarrow> bool" where
  "comma_sparse_base_word_checked i row =
    (i<46 \<and> comma_sparse_refines
      (\<lambda>r. comma_orbit_word 0 r i) row)"

ML_file "compact_sparse_base_constructor.ML"

ML \<open>
  val valid = @{term "[(Comma_Word_Invalid, 1)] :: comma_sparse_word"}
  val zero_mask = @{term "[(Comma_Word_Invalid, 0)] :: comma_sparse_word"}
  val open_label = @{term "[(Comma_Word_Live x, 1)] :: comma_sparse_word"}
  val open_numeral = @{term "[(Comma_Word_Stop x Comma_Terminal_Landmine, 1)] :: comma_sparse_word"}
  val nonliteral = @{term "rev ([(Comma_Word_Invalid, 1)] :: comma_sparse_word)"}
  val live_outside = @{term "[(Comma_Word_Live 46, 1)] :: comma_sparse_word"}
  val fork_zero = @{term "[(Comma_Word_Stop 0 (Comma_Terminal_Fork 0), 1)] :: comma_sparse_word"}
  val fork_one = @{term "[(Comma_Word_Stop 0 (Comma_Terminal_Fork 1), 1)] :: comma_sparse_word"}
  val fork_ten = @{term "[(Comma_Word_Stop 0 (Comma_Terminal_Fork 10), 1)] :: comma_sparse_word"}
  fun power_two_num 0 = Const (@{const_name Num.One}, @{typ num})
    | power_two_num n = Const (@{const_name Num.Bit0}, @{typ num} --> @{typ num}) $
        power_two_num (n-1)
  val oversized = Const (@{const_name numeral}, @{typ num} --> @{typ nat}) $
    power_two_num 924
  val oversized_mask = HOLogic.mk_list
    (HOLogic.mk_prodT (@{typ comma_word_result}, @{typ nat}))
    [HOLogic.mk_prod (@{term Comma_Word_Invalid}, oversized)]
  val _ = Comma_Compact_Sparse_Base_Constructor.check_sparse_value valid
  fun rejected term =
    (case Exn.capture
      (fn () => Comma_Compact_Sparse_Base_Constructor.check_sparse_value term) () of
      Exn.Exn (ERROR _) => ()
    | Exn.Exn failure => Exn.reraise failure
    | Exn.Res _ => error "Compact sparse publisher accepted malformed output")
  val _ = List.app rejected [zero_mask, open_label, open_numeral, nonliteral,
    live_outside, fork_zero, fork_one, fork_ten, oversized_mask]
  val root_zero = Comma_Compact_Sparse_Base_Constructor.root_expression 0
  val root_one_equation = Thm.reflexive
    (Thm.cterm_of @{context} (Comma_Compact_Sparse_Base_Constructor.root_expression 1))
  val _ = Comma_Compact_Sparse_Base_Constructor.check_root_equation
    root_zero (Thm.reflexive (Thm.cterm_of @{context} root_zero))
  val _ = (case Exn.capture (fn () =>
      Comma_Compact_Sparse_Base_Constructor.check_root_equation
        root_zero root_one_equation) () of
    Exn.Exn (ERROR _) => ()
  | Exn.Exn failure => Exn.reraise failure
  | Exn.Res _ => error "Compact sparse publisher accepted a foreign root equation")
\<close>

local_setup \<open>
  fn lthy =>
    let
      val engine = Comma_Compact_Sparse_Base_Constructor.make lthy
      fun check_scope request expected =
        (case #scope_meet engine (Thm.cterm_of lthy request) of
          NONE => error "Admitted CRT scope was not checked"
        | SOME theorem =>
            if Thm.term_of (Thm.lhs_of theorem) aconv request andalso
                Thm.term_of (Thm.rhs_of theorem) aconv expected andalso
                Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
            then () else error "CRT scope lost its exact intersection equation")
      val _ = check_scope
        @{term "comma_phase_class 6 0 1 AND comma_phase_class 4 0 3"}
        @{term "comma_phase_class 12 0 7"}
      val _ = check_scope
        @{term "comma_phase_class 6 0 1 AND comma_phase_class 4 0 0"}
        @{term "0::nat"}
      val _ = (case #scope_meet engine
          @{cterm "comma_phase_class 5 0 0 AND comma_phase_class 4 0 0"} of
          NONE => ()
        | SOME _ => error "CRT scope accepted a period outside the 924 clock")
      val indices = 0 upto 45
      val items = map (#one engine) indices
      val rows = map #value items
      val refinements = map #refinement items
      val _ = if length rows=46 andalso length refinements=46 then ()
        else error "Compact sparse base requires forty-six checked fibers"
      val _ = if forall (fn theorem =>
          Thm.nprems_of theorem=0 andalso null (Thm.hyps_of theorem)) refinements
        then () else error "Compact sparse base refinement has open assumptions"
      val wordT = @{typ comma_sparse_word}
      val natT = @{typ nat}
      val refine = @{term comma_sparse_refines}
      fun expected_refinement (i, row) =
        let
          val observed_result = Abs ("r", natT,
            @{term comma_orbit_word} $ HOLogic.mk_number natT 0 $
              Bound 0 $ HOLogic.mk_number natT i)
        in HOLogic.mk_Trueprop (refine $ observed_result $ row) end
      val _ = List.app (fn (i, row) =>
          if Thm.prop_of (nth refinements i) aconv expected_refinement (i, row) then ()
          else error ("Compact sparse root refinement does not match index " ^
            Int.toString i)) (map_index (fn (i, row) => (i, row)) rows)
      val body = HOLogic.mk_list wordT rows
      val ((data,(_,data_def)), next) = Local_Theory.define
        ((Binding.name "comma_sparse_base_data", NoSyn),
          ((Binding.name "comma_sparse_base_data_def", []), body)) lthy
      val index_terms = @{term "[0..<46] :: nat list"}
      val list_all2T = (natT --> wordT --> HOLogic.boolT) -->
        HOLogic.listT natT --> HOLogic.listT wordT --> HOLogic.boolT
      val checked = Const (@{const_name list_all2}, list_all2T) $
        @{term comma_sparse_base_word_checked} $ index_terms $ data
      val checked_theorem = Goal.prove (Local_Theory.target_of next) [] []
        (HOLogic.mk_Trueprop checked)
        (fn {context,...} => simp_tac (context addsimps
          (data_def :: refinements @
            @{thms comma_sparse_base_word_checked_def upt_rec})) 1)
      val (_, final) = Local_Theory.note
        ((Binding.name "comma_sparse_base_data_refines_all", []),
          [checked_theorem]) next
      val _ = Comma_Fast_Kernel.report (#stats engine ())
    in final end
\<close>

lemma comma_sparse_base_data_length [simp]:
  "length comma_sparse_base_data=46"
proof -
  have "length [0..<46] = length comma_sparse_base_data"
    by (rule list_all2_lengthD[OF comma_sparse_base_data_refines_all])
  then show ?thesis by simp
qed

definition comma_sparse_base_data_row :: "nat \<Rightarrow> comma_sparse_word" where
  "comma_sparse_base_data_row i =
    (if i<46 then comma_sparse_base_data!i
     else [(Comma_Word_Invalid,mask 924)])"

lemma comma_sparse_base_data_refines:
  assumes index: "i<46"
  shows "comma_sparse_refines
    (\<lambda>r. comma_orbit_word 0 r i) (comma_sparse_base_data_row i)"
proof -
  have paired: "comma_sparse_base_word_checked (([0..<46])!i)
      (comma_sparse_base_data!i)"
    using comma_sparse_base_data_refines_all index
    by (rule list_all2_nthD) (use index in simp)
  have member: "comma_sparse_base_word_checked i
      (comma_sparse_base_data!i)"
    using paired by simp
  show ?thesis
    using member index by (simp add: comma_sparse_base_word_checked_def
      comma_sparse_base_data_row_def)
qed

definition comma_sparse_has_semantic_output ::
    "comma_sparse_word \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result \<Rightarrow> bool" where
  "comma_sparse_has_semantic_output rows phase result =
    (\<exists>out. comma_sparse_has rows phase out
      \<and> comma_semantic_b1_of_word out=result)"

lemma comma_sparse_refines_has_semantic_output:
  assumes exact: "comma_sparse_refines F rows"
    and phase: "phase<924"
  shows "comma_sparse_has_semantic_output rows phase
    (comma_semantic_b1_of_word (F phase))"
proof -
  have output: "comma_sparse_has rows phase (F phase)"
    using exact phase by (auto simp: comma_sparse_refines_def)
  show ?thesis
    using output by (auto simp: comma_sparse_has_semantic_output_def)
qed

lemma comma_sparse_base_semantic_output_matches_template:
  assumes root: "i<46" and phase: "phase<924"
  shows "comma_sparse_has_semantic_output (comma_sparse_base_data_row i) phase
      (comma_semantic_b1_occurrence_output_binding
        (comma_semantic_b1_bind_occurrence
          (comma_semantic_b1_id_of_root i) return_shift 0)
        (comma_semantic_b1_occurrence_template_function
          (comma_semantic_b1_bind_occurrence
            (comma_semantic_b1_id_of_root i) return_shift 0)
          ((phase+return_shift) mod 924)))"
proof -
  have sparse_exact:
    "comma_sparse_refines (\<lambda>clock. comma_orbit_word 0 clock i)
      (comma_sparse_base_data_row i)"
    by (rule comma_sparse_base_data_refines[OF root])
  have sparse_output:
    "comma_sparse_has_semantic_output (comma_sparse_base_data_row i) phase
      (comma_semantic_b1_of_word (comma_orbit_word 0 phase i))"
    by (rule comma_sparse_refines_has_semantic_output[OF sparse_exact phase])
  have template_output:
    "comma_semantic_b1_occurrence_output_binding
        (comma_semantic_b1_bind_occurrence
          (comma_semantic_b1_id_of_root i) return_shift 0)
        (comma_semantic_b1_occurrence_template_function
          (comma_semantic_b1_bind_occurrence
            (comma_semantic_b1_id_of_root i) return_shift 0)
          ((phase+return_shift) mod 924)) =
      comma_semantic_b1_of_word (comma_orbit_word 0 phase i)"
    using comma_semantic_b1_root_template_reconstructs[OF root, rule_format,
        of phase return_shift]
    by simp
  show ?thesis using sparse_output template_output by simp
qed

ML \<open>
  val checked = @{thms comma_sparse_refines_has_semantic_output
    comma_sparse_base_semantic_output_matches_template};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Sparse B1 rows preserve bound template outputs" checked;
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "B1 template binding reaches the checked sparse base"
    ["comma_semantic_b1_root_template_reconstructs",
      "comma_sparse_base_data_refines"]
    @{thms comma_sparse_base_semantic_output_matches_template};
\<close>

definition comma_checked_sparse_base :: "nat \<Rightarrow> comma_sparse_word" where
  "comma_checked_sparse_base=comma_sparse_base_data_row"

lemma comma_checked_sparse_base_refines:
  assumes "i<46"
  shows "comma_sparse_refines
    (\<lambda>r. comma_orbit_word 0 r i) (comma_checked_sparse_base i)"
  using comma_sparse_base_data_refines[OF assms]
  by (simp add: comma_checked_sparse_base_def)

theorem comma_checked_sparse_power_refines:
  "comma_sparse_refines (\<lambda>r. comma_orbit_word k r i)
    (comma_sparse_power (comma_sparse_admit comma_checked_sparse_base) k i)"
  by (rule comma_sparse_power_refines)
    (rule comma_checked_sparse_base_refines, assumption)

ML \<open>
  val checked = @{thms comma_sparse_base_data_length comma_sparse_base_data_refines_all
      comma_sparse_base_data_refines comma_checked_sparse_base_refines
      comma_checked_sparse_power_refines}
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Compact sparse base and power refinement depend on an oracle"
\<close>
end
