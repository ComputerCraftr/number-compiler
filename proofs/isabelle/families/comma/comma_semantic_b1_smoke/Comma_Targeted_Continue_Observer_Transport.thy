theory Comma_Targeted_Continue_Observer_Transport
  imports Comma_Semantic_B1.Comma_Targeted_Continue_Observer_Refinement
begin

text \<open>
Transport a completed operator across the external clock while retaining its
admitted class binding. The fused job observer consumes individual child
columns directly; no target-row cache or completed column family is required.
\<close>

lemma comma_continue_operator_clock_equiv:
  assumes contract: "comma_continue_operator_contract operation steps"
    and observer_admitted: "comma_continue_observer_admitted observer"
    and observer_matches: "comma_continue_observer_matches observer predicate"
    and source: "source<46"
    and binding: "comma_semantic_phase_program_for_class source=Some program"
  shows "comma_crt_equiv_check
      (operation observer program clock)
      (comma_crt_shift clock (operation observer program 0))"
proof -
  have left_admitted:
    "comma_crt_admitted 0 (operation observer program clock)"
    using contract observer_admitted
    by (auto simp: comma_continue_operator_contract_def)
  have zero_admitted:
    "comma_crt_admitted 0 (operation observer program 0)"
    using contract observer_admitted
    by (auto simp: comma_continue_operator_contract_def)
  have right_admitted:
    "comma_crt_admitted 0
      (comma_crt_shift clock (operation observer program 0))"
    by (rule comma_crt_shift_admitted[OF zero_admitted])
  have equal_sets:
    "comma_crt_set (operation observer program clock) =
      comma_crt_set (comma_crt_shift clock (operation observer program 0))"
  proof (rule set_eqI)
    fix phase :: nat
    show "phase \<in> comma_crt_set (operation observer program clock) \<longleftrightarrow>
      phase \<in> comma_crt_set (comma_crt_shift clock (operation observer program 0))"
    proof (cases "phase<924")
      case False
      then show ?thesis by (simp add: comma_crt_set_def)
    next
      case True
      let ?next_phase = "(phase+clock) mod 924"
      have next_phase_bound: "?next_phase<924" by simp
      have left_eval:
        "comma_crt_eval phase (operation observer program clock) =
          (case comma_phase_class_continue_power
            comma_semantic_phase_program_class_step steps (?next_phase,source) of
              None \<Rightarrow> False
            | Some (terminal_phase,terminal_source) \<Rightarrow>
                predicate terminal_phase terminal_source)"
        using contract observer_admitted observer_matches source True binding
        by (auto simp: comma_continue_operator_contract_def)
      have zero_eval:
        "comma_crt_eval ?next_phase (operation observer program 0) =
          (case comma_phase_class_continue_power
            comma_semantic_phase_program_class_step steps (?next_phase,source) of
              None \<Rightarrow> False
            | Some (terminal_phase,terminal_source) \<Rightarrow>
                predicate terminal_phase terminal_source)"
        using contract observer_admitted observer_matches source
          next_phase_bound binding
        by (auto simp: comma_continue_operator_contract_def)
      have shift_eval:
        "comma_crt_eval phase
            (comma_crt_shift clock (operation observer program 0)) =
          comma_crt_eval ?next_phase (operation observer program 0)"
      proof -
        have shifted:
          "comma_crt_eval phase
              (comma_crt_shift clock (operation observer program 0)) =
            comma_crt_eval (phase+clock) (operation observer program 0)"
          by (rule comma_crt_shift_refines[OF zero_admitted,
              where phase=phase and shift=clock])
        have periodic:
          "comma_crt_eval (phase+clock) (operation observer program 0) =
            comma_crt_eval ?next_phase (operation observer program 0)"
          by (rule sym[OF comma_crt_eval_periodic[OF zero_admitted]])
        show ?thesis using shifted periodic by simp
      qed
      have evaluations:
        "comma_crt_eval phase (operation observer program clock) =
          comma_crt_eval phase
            (comma_crt_shift clock (operation observer program 0))"
        using left_eval zero_eval shift_eval by simp
      show ?thesis using evaluations True by (simp add: comma_crt_set_def)
    qed
  qed
  show ?thesis
    by (rule comma_crt_equiv_check_complete[OF left_admitted right_admitted
        equal_sets])
qed
lemma comma_continue_operator_applied_observer_admitted:
  assumes contract: "comma_continue_operator_contract operation steps"
    and observer: "comma_continue_observer_admitted observer"
  shows "comma_continue_observer_admitted
    (\<lambda>target clock.
      case comma_semantic_phase_program_for_class target of
        Some child \<Rightarrow> operation observer child clock
      | None \<Rightarrow> Comma_CRT_Bool False)"
proof -
  show ?thesis
    unfolding comma_continue_observer_admitted_def
  proof (intro allI impI)
    fix target clock :: nat
    assume target: "target<46"
    obtain child where binding:
      "comma_semantic_phase_program_for_class target=Some child"
      by (rule comma_semantic_phase_program_for_class_some[OF target])
    show "comma_crt_admitted 0
        (case comma_semantic_phase_program_for_class target of
          Some child \<Rightarrow> operation observer child clock
        | None \<Rightarrow> Comma_CRT_Bool False)"
      using contract observer binding
      by (auto simp: comma_continue_operator_contract_def)
  qed
qed

lemma comma_continue_operator_applied_observer_matches:
  assumes contract: "comma_continue_operator_contract operation steps"
    and observer_admitted: "comma_continue_observer_admitted observer"
    and observer_matches: "comma_continue_observer_matches observer predicate"
  shows "comma_continue_observer_matches
    (\<lambda>target clock.
      case comma_semantic_phase_program_for_class target of
        Some child \<Rightarrow> operation observer child clock
      | None \<Rightarrow> Comma_CRT_Bool False)
    (comma_continue_suffix_predicate steps predicate)"
proof -
  show ?thesis
    unfolding comma_continue_observer_matches_def
  proof (intro allI impI)
    fix phase target clock :: nat
    assume phase: "phase<924" and target: "target<46"
    obtain child where binding:
      "comma_semantic_phase_program_for_class target=Some child"
      by (rule comma_semantic_phase_program_for_class_some[OF target])
    have exact:
      "comma_crt_eval phase (operation observer child clock) =
        comma_continue_suffix_predicate steps predicate
          ((phase+clock) mod 924) target"
      using contract observer_admitted observer_matches phase target binding
      by (auto simp: comma_continue_operator_contract_def
          comma_continue_suffix_predicate_def)
    show "comma_crt_eval phase
        (case comma_semantic_phase_program_for_class target of
          Some child \<Rightarrow> operation observer child clock
        | None \<Rightarrow> Comma_CRT_Bool False) =
      comma_continue_suffix_predicate steps predicate
        ((phase+clock) mod 924) target"
      using exact binding by simp
  qed
qed
lemma comma_continue_operator_contract_admitted:
  assumes contract: "comma_continue_operator_contract operation steps"
    and observer: "comma_continue_observer_admitted observer"
  shows "comma_crt_admitted 0 (operation observer program clock)"
  using contract observer
  by (auto simp: comma_continue_operator_contract_def)

ML \<open>
  val published = @{thms
    comma_continue_operator_clock_equiv
    comma_continue_operator_applied_observer_admitted
    comma_continue_operator_applied_observer_matches
    comma_continue_operator_contract_admitted}
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Continue operator phase transport" published
\<close>

end
