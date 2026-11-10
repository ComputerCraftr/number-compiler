theory Comma_Targeted_Continue_Observer_Refinement
  imports Comma_Targeted_Continue_Observer Comma_Class_Continue_Columns
begin

text \<open>
The observer algebra is refined to exact phase/class Continue paths.  The
operator is keyed by a normalized program, while a source class appears only
in the binding premise that authenticates which program may act for it.
External clock progression is a CRT rotation of the zero-shift action.
\<close>

type_synonym comma_continue_predicate = "nat \<Rightarrow> nat \<Rightarrow> bool"

definition comma_continue_observer_admitted ::
    "comma_continue_observer \<Rightarrow> bool" where
  "comma_continue_observer_admitted observer \<longleftrightarrow>
    (\<forall>target<46. \<forall>clock.
      comma_crt_admitted 0 (observer target clock))"

definition comma_continue_observer_matches ::
    "comma_continue_observer \<Rightarrow> comma_continue_predicate \<Rightarrow> bool"
where
  "comma_continue_observer_matches observer predicate \<longleftrightarrow>
    (\<forall>phase<924. \<forall>target<46. \<forall>clock.
      comma_crt_eval phase (observer target clock) =
        predicate ((phase+clock) mod 924) target)"

lemma comma_semantic_phase_program_for_class_some:
  assumes source: "source<46"
  obtains program where
    "comma_semantic_phase_program_for_class source=Some program"
proof -
  have sector_lower: "1\<le>(1::nat)" by simp
  have sector_upper: "(1::nat)\<le>9" by simp
  obtain core where core_mapping:
      "comma_phase_core_of_modulus
        (comma_core_modulus
          (comma_finite_period_fast 1
            (comma_offset_representatives!source mod 10))) = Some core"
    and program:
    "comma_entry_control_program 1 (comma_offset_representatives!source) =
      Some (Comma_Entry_Core_Program 1
        (comma_offset_representatives!source mod 10)
        (comma_offset_representatives!source mod
          comma_finite_period_fast 1 (comma_offset_representatives!source mod 10))
        core)"
    using comma_entry_control_program_core[OF sector_lower sector_upper,
        where x="comma_offset_representatives!source"] by blast
  have lookup:
    "comma_semantic_phase_program_for_class source =
      Some (Comma_Entry_Core_Program 1
        (comma_offset_representatives!source mod 10)
        (comma_offset_representatives!source mod
          comma_finite_period_fast 1 (comma_offset_representatives!source mod 10))
        core)"
    unfolding comma_semantic_phase_program_for_class_def
    using source program by (simp only: if_True program)
  show thesis
    by (rule that[OF lookup])
qed

lemma comma_continue_endpoint_phase_column_admitted:
  "comma_crt_admitted 0 (comma_continue_endpoint_phase_column target)"
proof -
  have rows:
    "comma_crt_rows_admitted
      (map (\<lambda>endpoint.
        (comma_crt_phase_point (fst endpoint), Comma_Semantic_B1_Invalid))
        (filter (\<lambda>endpoint. snd endpoint=target)
          comma_continue24_endpoint_list))"
    unfolding comma_crt_rows_admitted_def
    using comma_crt_phase_point_admitted
    by (auto simp: list_all_iff)
  show ?thesis
    unfolding comma_continue_endpoint_phase_column_def
    by (rule comma_crt_collect_output_admitted[OF rows])
qed

lemma comma_continue_endpoint_phase_column_set:
  "comma_crt_set (comma_continue_endpoint_phase_column target) =
    {phase. phase<924 \<and>
      (\<exists>endpoint\<in>set comma_continue24_endpoint_list.
        snd endpoint=target \<and>
        phase mod 924=fst endpoint mod 924)}"
proof -
  have rows:
    "comma_crt_rows_admitted
      (map (\<lambda>endpoint.
        (comma_crt_phase_point (fst endpoint), Comma_Semantic_B1_Invalid))
        (filter (\<lambda>endpoint. snd endpoint=target)
          comma_continue24_endpoint_list))"
    unfolding comma_crt_rows_admitted_def
    using comma_crt_phase_point_admitted
    by (auto simp: list_all_iff)
  have collected:
    "comma_crt_set (comma_crt_collect_output Comma_Semantic_B1_Invalid
        (map (\<lambda>endpoint.
          (comma_crt_phase_point (fst endpoint), Comma_Semantic_B1_Invalid))
          (filter (\<lambda>endpoint. snd endpoint=target)
            comma_continue24_endpoint_list))) =
      (\<Union>row\<in>{row\<in>set (map (\<lambda>endpoint.
          (comma_crt_phase_point (fst endpoint), Comma_Semantic_B1_Invalid))
          (filter (\<lambda>endpoint. snd endpoint=target)
            comma_continue24_endpoint_list)).
          snd row=Comma_Semantic_B1_Invalid}. comma_crt_set (fst row))"
    by (rule comma_crt_collect_output_set[OF rows])
  show ?thesis
    unfolding comma_continue_endpoint_phase_column_def
    using collected comma_crt_phase_point_set
    by (auto simp: comma_crt_phase_point_set)
qed

definition comma_continue_outside_endpoints :: comma_continue_predicate where
  "comma_continue_outside_endpoints phase target \<longleftrightarrow>
    (phase,target)\<notin>comma_continue24_endpoints"

lemma comma_continue_bad_endpoint_observer_admitted:
  "comma_continue_observer_admitted comma_continue_bad_endpoint_observer"
  unfolding comma_continue_observer_admitted_def
    comma_continue_bad_endpoint_observer_def
  using comma_continue_endpoint_phase_column_admitted
  by (auto intro: comma_crt_shift_admitted comma_crt_negate_admitted)

lemma comma_continue_bad_endpoint_observer_matches:
  "comma_continue_observer_matches comma_continue_bad_endpoint_observer
    comma_continue_outside_endpoints"
proof -
  have endpoint_admitted:
    "comma_crt_admitted 0 (comma_continue_endpoint_phase_column target)"
    for target
    by (rule comma_continue_endpoint_phase_column_admitted)
  show ?thesis
    unfolding comma_continue_observer_matches_def
  proof (intro allI impI)
    fix phase target clock :: nat
    assume phase: "phase<924" and target: "target<46"
    have shift_refines:
      "comma_crt_eval phase
          (comma_crt_shift clock
            (comma_continue_endpoint_phase_column target)) =
        comma_crt_eval (phase+clock)
          (comma_continue_endpoint_phase_column target)"
      by (rule comma_crt_shift_refines[OF endpoint_admitted,
          where phase=phase and shift=clock])
    have periodic:
      "comma_crt_eval ((phase+clock) mod 924)
          (comma_continue_endpoint_phase_column target) =
        comma_crt_eval (phase+clock)
          (comma_continue_endpoint_phase_column target)"
      by (rule comma_crt_eval_periodic[OF endpoint_admitted])
    have shifted:
      "comma_crt_eval phase
          (comma_crt_shift clock
            (comma_continue_endpoint_phase_column target)) =
        comma_crt_eval ((phase+clock) mod 924)
          (comma_continue_endpoint_phase_column target)"
      by (rule trans[OF shift_refines sym[OF periodic]])
    have shifted_eval:
      "comma_crt_eval ((phase+clock) mod 924)
          (comma_continue_endpoint_phase_column target) \<longleftrightarrow>
        ((phase+clock) mod 924,target)\<in>comma_continue24_endpoints"
    proof -
      let ?p = "(phase+clock) mod 924"
      have bound: "?p<924" by simp
      have member:
        "(?p\<in>comma_crt_set (comma_continue_endpoint_phase_column target)) =
          (?p\<in>{p. p<924 \<and>
            (\<exists>endpoint\<in>set comma_continue24_endpoint_list.
              snd endpoint=target \<and> p mod 924=fst endpoint mod 924)})"
        by (rule arg_cong[OF comma_continue_endpoint_phase_column_set,
            where f="\<lambda>states. ?p\<in>states"])
      have selected:
        "comma_crt_eval ?p (comma_continue_endpoint_phase_column target) =
          (\<exists>endpoint\<in>comma_continue24_endpoints.
            snd endpoint=target \<and> ?p=fst endpoint mod 924)"
        using member
        by (simp only: comma_crt_set_def mem_Collect_eq bound simp_thms
            mod_less[OF bound] comma_continue24_endpoint_list_set)
      show ?thesis
      proof
        assume evaluated:
          "comma_crt_eval ?p (comma_continue_endpoint_phase_column target)"
        obtain endpoint where endpoint:
            "endpoint\<in>comma_continue24_endpoints"
          and target_eq: "snd endpoint=target"
          and phase_eq: "?p=fst endpoint mod 924"
          using iffD1[OF selected evaluated] by blast
        have pair: "(fst endpoint,snd endpoint)\<in>comma_continue24_endpoints"
          using endpoint by (cases endpoint) (simp only: fst_conv snd_conv)
        have endpoint_bound: "fst endpoint<924"
          by (rule comma_continue24_endpoint_phase_bound[OF pair])
        have phase_eq': "?p=fst endpoint"
          using phase_eq by (simp only: mod_less[OF endpoint_bound])
        have same: "(?p,target)=endpoint"
          using phase_eq' target_eq by (cases endpoint) simp
        show "(?p,target)\<in>comma_continue24_endpoints"
          using endpoint by (simp only: same)
      next
        assume endpoint: "(?p,target)\<in>comma_continue24_endpoints"
        have components:
          "snd (?p,target)=target \<and> ?p=fst (?p,target) mod 924"
          by (simp only: fst_conv snd_conv mod_less[OF bound] simp_thms)
        have witness:
          "\<exists>endpoint\<in>comma_continue24_endpoints.
            snd endpoint=target \<and> ?p=fst endpoint mod 924"
          using endpoint components by blast
        show "comma_crt_eval ?p (comma_continue_endpoint_phase_column target)"
          by (rule iffD2[OF selected witness])
      qed
    qed
    have negated:
      "comma_crt_eval phase
          (comma_crt_negate
            (comma_crt_shift clock
              (comma_continue_endpoint_phase_column target))) =
        (\<not> comma_crt_eval phase
          (comma_crt_shift clock
            (comma_continue_endpoint_phase_column target)))"
      by (rule comma_crt_negate_eval[
          OF comma_crt_shift_admitted[OF endpoint_admitted]])
    show "comma_crt_eval phase
        (comma_continue_bad_endpoint_observer target clock) =
      comma_continue_outside_endpoints ((phase+clock) mod 924) target"
      using shifted shifted_eval negated phase
      by (simp only: comma_continue_bad_endpoint_observer_def
          comma_continue_outside_endpoints_def)
  qed
qed

definition comma_continue_operator_contract ::
    "comma_continue_operator \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_continue_operator_contract operation steps \<longleftrightarrow>
    (\<forall>observer. comma_continue_observer_admitted observer \<longrightarrow>
      (\<forall>program clock.
        comma_crt_admitted 0 (operation observer program clock))) \<and>
    (\<forall>observer predicate program source clock phase.
      comma_continue_observer_admitted observer \<longrightarrow>
      comma_continue_observer_matches observer predicate \<longrightarrow>
      source<46 \<longrightarrow> phase<924 \<longrightarrow>
      comma_semantic_phase_program_for_class source=Some program \<longrightarrow>
      comma_crt_eval phase (operation observer program clock) =
        (case comma_phase_class_continue_power
          comma_semantic_phase_program_class_step steps
          (((phase+clock) mod 924),source) of
            None \<Rightarrow> False
          | Some (terminal_phase,terminal_source) \<Rightarrow>
              predicate terminal_phase terminal_source))"

definition comma_continue_suffix_predicate ::
    "nat \<Rightarrow> comma_continue_predicate \<Rightarrow>
      comma_continue_predicate" where
  "comma_continue_suffix_predicate steps predicate phase source =
    (case comma_phase_class_continue_power
      comma_semantic_phase_program_class_step steps (phase,source) of
        None \<Rightarrow> False
      | Some (terminal_phase,terminal_source) \<Rightarrow>
          predicate terminal_phase terminal_source)"

lemma comma_continue_operator_step_rows_admitted:
  assumes observer:
    "comma_continue_observer_admitted observer"
  shows "comma_crt_rows_admitted
    (map (\<lambda>target.
      (let edge=comma_phase_continue_compile_job
          (Comma_Continue_Program_Job program) 0 target
       in (if comma_crt_supported edge then
            comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
              (observer target (Suc clock))
           else Comma_CRT_Bool False,
           Comma_Semantic_B1_Invalid))) [0..<46])"
proof -
  let ?rows = "map (\<lambda>target.
    (let edge=comma_phase_continue_compile_job
        (Comma_Continue_Program_Job program) 0 target
     in (if comma_crt_supported edge then
          comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
            (observer target (Suc clock))
         else Comma_CRT_Bool False,
         Comma_Semantic_B1_Invalid))) [0..<46]"
  have edge_admitted:
    "comma_crt_admitted 0 (comma_phase_continue_compile_job
      (Comma_Continue_Program_Job program) 0 target)"
    if target: "target<46" for target
    using comma_phase_continue_compile_job_admitted[where
        job="Comma_Continue_Program_Job program"] target by auto
  have cell_admitted:
    "comma_crt_admitted 0
      (if comma_crt_supported
          (comma_phase_continue_compile_job
            (Comma_Continue_Program_Job program) 0 target)
       then comma_crt_apply Comma_CRT_And
          (comma_crt_shift clock
            (comma_phase_continue_compile_job
              (Comma_Continue_Program_Job program) 0 target))
          (observer target (Suc clock))
       else Comma_CRT_Bool False)"
    if target: "target<46" for target
  proof -
    have edge:
      "comma_crt_admitted 0
        (comma_phase_continue_compile_job
          (Comma_Continue_Program_Job program) 0 target)"
      by (rule edge_admitted[OF target])
    have shifted:
      "comma_crt_admitted 0
        (comma_crt_shift clock
          (comma_phase_continue_compile_job
            (Comma_Continue_Program_Job program) 0 target))"
      by (rule comma_crt_shift_admitted[OF edge])
    have child: "comma_crt_admitted 0 (observer target (Suc clock))"
      using observer target
      by (auto simp: comma_continue_observer_admitted_def)
    have combined:
      "comma_crt_admitted 0
        (comma_crt_apply Comma_CRT_And
          (comma_crt_shift clock
            (comma_phase_continue_compile_job
              (Comma_Continue_Program_Job program) 0 target))
          (observer target (Suc clock)))"
      by (rule comma_crt_apply_admitted[OF shifted child])
    show ?thesis using combined
      by (cases "comma_crt_supported
        (comma_phase_continue_compile_job
          (Comma_Continue_Program_Job program) 0 target)") simp_all
  qed
  have rows: "comma_crt_rows_admitted ?rows"
    using cell_admitted
    by (auto simp: comma_crt_rows_admitted_def set_map Let_def)
  show ?thesis using rows by simp
qed

lemma comma_continue_operator_step_admitted:
  assumes observer:
    "comma_continue_observer_admitted observer"
  shows "comma_crt_admitted 0
    (comma_continue_operator_step observer program clock)"
proof -
  have rows: "comma_crt_rows_admitted
    (map (\<lambda>target.
      (let edge=comma_phase_continue_compile_job
          (Comma_Continue_Program_Job program) 0 target
       in (if comma_crt_supported edge then
            comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
              (observer target (Suc clock))
           else Comma_CRT_Bool False,
           Comma_Semantic_B1_Invalid))) [0..<46])"
    by (rule comma_continue_operator_step_rows_admitted[OF observer])
  show ?thesis
    unfolding comma_continue_operator_step_def
    by (rule comma_crt_collect_output_admitted[OF rows])
qed

lemma comma_continue_operator_step_pointwise:
  assumes observer_admitted:
    "comma_continue_observer_admitted observer"
    and phase: "phase<924"
  shows "comma_crt_eval phase
      (comma_continue_operator_step observer program clock) =
    (\<exists>target<46.
      comma_crt_eval phase
        (let edge=comma_phase_continue_compile_job
            (Comma_Continue_Program_Job program) 0 target
         in if comma_crt_supported edge then
              comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
                (observer target (Suc clock))
            else Comma_CRT_Bool False))"
proof -
  let ?rows = "map (\<lambda>target.
    (let edge=comma_phase_continue_compile_job
        (Comma_Continue_Program_Job program) 0 target
     in (if comma_crt_supported edge then
          comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
            (observer target (Suc clock))
         else Comma_CRT_Bool False,
         Comma_Semantic_B1_Invalid))) [0..<46]"
  have rows: "comma_crt_rows_admitted ?rows"
    by (rule comma_continue_operator_step_rows_admitted[OF observer_admitted])
  have collect_set:
    "comma_crt_set (comma_continue_operator_step observer program clock) =
      (\<Union>row\<in>{row\<in>set ?rows.
        snd row=Comma_Semantic_B1_Invalid}. comma_crt_set (fst row))"
    unfolding comma_continue_operator_step_def
    by (rule comma_crt_collect_output_set[OF rows])
  have eval_rows:
    "comma_crt_eval phase
        (comma_continue_operator_step observer program clock) \<longleftrightarrow>
      (\<exists>row\<in>set ?rows.
        snd row=Comma_Semantic_B1_Invalid \<and>
        comma_crt_eval phase (fst row))"
    using collect_set phase
    by (auto simp: comma_crt_set_def)
  show ?thesis
    using eval_rows
    by (auto simp: set_map Let_def)
qed

lemma comma_continue_operator_step_exact:
  assumes phase: "phase<924" and source: "source<46"
    and binding: "comma_semantic_phase_program_for_class source=Some program"
    and observer_admitted:
      "comma_continue_observer_admitted observer"
    and observer_matches:
      "comma_continue_observer_matches observer predicate"
  shows "comma_crt_eval phase
      (comma_continue_operator_step observer program clock) =
    (\<exists>target<46.
      comma_semantic_phase_program_class_step ((phase+clock) mod 924) source =
        Comma_Phase_Class_Continue
          ((((phase+clock) mod 924)+1) mod 924) target \<and>
      predicate ((phase+Suc clock) mod 924) target)"
proof -
  have pointwise:
    "comma_crt_eval phase
        (comma_continue_operator_step observer program clock) =
      (\<exists>target<46.
        comma_crt_eval phase
          (let edge=comma_phase_continue_compile_job
              (Comma_Continue_Program_Job program) 0 target
           in if comma_crt_supported edge then
                comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
                  (observer target (Suc clock))
              else Comma_CRT_Bool False))"
    by (rule comma_continue_operator_step_pointwise
        [OF observer_admitted phase])
  have column_binding:
    "comma_semantic_phase_continue_column source target =
      comma_phase_continue_compile_job
        (Comma_Continue_Program_Job program) 0 target"
    if target: "target<46" for target
    using source binding target
    by (simp add: comma_semantic_phase_continue_column_def
        comma_semantic_phase_continue_columns_def)
  have row_eval:
    "comma_crt_eval phase
        (if comma_crt_supported edge then
          comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
            (observer target (Suc clock))
         else Comma_CRT_Bool False) =
      (comma_crt_eval phase (comma_crt_shift clock edge) \<and>
        comma_crt_eval phase (observer target (Suc clock)))"
    if target: "target<46"
      and edge: "edge=comma_phase_continue_compile_job
        (Comma_Continue_Program_Job program) 0 target"
    for target edge
  proof -
    have edge_admitted: "comma_crt_admitted 0 edge"
      using edge comma_phase_continue_compile_job_admitted[where
          job="Comma_Continue_Program_Job program"]
      by auto
    have shifted_admitted: "comma_crt_admitted 0 (comma_crt_shift clock edge)"
      by (rule comma_crt_shift_admitted[OF edge_admitted])
    have child_admitted: "comma_crt_admitted 0 (observer target (Suc clock))"
      using observer_admitted target
      by (auto simp: comma_continue_observer_admitted_def)
    have eval_apply:
      "comma_crt_eval phase
          (comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
            (observer target (Suc clock))) =
        (comma_crt_eval phase (comma_crt_shift clock edge) \<and>
          comma_crt_eval phase (observer target (Suc clock)))"
      using comma_crt_apply_refines_boolean[
          OF shifted_admitted child_admitted, where operation=Comma_CRT_And]
      by (simp add: comma_crt_boolean_value_def)
    have shifted_eval:
      "comma_crt_eval phase (comma_crt_shift clock edge) \<Longrightarrow>
        comma_crt_supported edge"
    proof -
      assume evaluated: "comma_crt_eval phase (comma_crt_shift clock edge)"
      have shift_exact:
        "comma_crt_eval phase (comma_crt_shift clock edge) =
          comma_crt_eval (phase+clock) edge"
        by (rule comma_crt_shift_refines[OF edge_admitted])
      have raw_evaluated: "comma_crt_eval (phase+clock) edge"
        using evaluated shift_exact by simp
      show ?thesis
        by (rule comma_crt_eval_supported[OF edge_admitted raw_evaluated])
    qed
    show ?thesis
    proof (cases "comma_crt_supported edge")
      case True
      then show ?thesis using eval_apply by simp
    next
      case False
      have no_shift_eval:
        "\<not> comma_crt_eval phase (comma_crt_shift clock edge)"
      proof
        assume evaluated: "comma_crt_eval phase (comma_crt_shift clock edge)"
        have "comma_crt_supported edge"
          by (rule shifted_eval[OF evaluated])
        then show False using False by contradiction
      qed
      show ?thesis using eval_apply no_shift_eval by simp
    qed
  qed
  have edge_exact:
    "comma_crt_eval phase
        (comma_crt_shift clock
          (comma_phase_continue_compile_job
            (Comma_Continue_Program_Job program) 0 target)) =
      (comma_semantic_phase_program_class_step ((phase+clock) mod 924) source =
        Comma_Phase_Class_Continue
          ((((phase+clock) mod 924)+1) mod 924) target)"
    if target: "target<46" for target
  proof -
    have column:
      "comma_semantic_phase_continue_column source target =
        comma_phase_continue_compile_job
          (Comma_Continue_Program_Job program) 0 target"
      by (rule column_binding[OF target])
    show ?thesis
      using comma_semantic_phase_continue_column_clock_exact[OF phase source target]
        column by simp
  qed
  have child_exact:
    "comma_crt_eval phase (observer target (Suc clock)) =
      predicate ((phase+Suc clock) mod 924) target"
    if target: "target<46" for target
    using observer_matches phase target
    by (auto simp: comma_continue_observer_matches_def)
  have successor_phase:
    "((phase+Suc clock) mod 924) =
      ((((phase+clock) mod 924)+1) mod 924)"
    by (simp add: mod_Suc_eq)
  have exact_row:
    "comma_crt_eval phase
        (let edge=comma_phase_continue_compile_job
            (Comma_Continue_Program_Job program) 0 target
         in if comma_crt_supported edge then
              comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
                (observer target (Suc clock))
            else Comma_CRT_Bool False) =
      (comma_semantic_phase_program_class_step ((phase+clock) mod 924) source =
        Comma_Phase_Class_Continue
          ((((phase+clock) mod 924)+1) mod 924) target \<and>
        predicate ((((phase+clock) mod 924)+1) mod 924) target)"
    if target: "target<46" for target
  proof -
    have selected_row:
      "comma_crt_eval phase
          (let edge=comma_phase_continue_compile_job
              (Comma_Continue_Program_Job program) 0 target
           in if comma_crt_supported edge then
                comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
                  (observer target (Suc clock))
              else Comma_CRT_Bool False) =
        (comma_crt_eval phase
            (comma_crt_shift clock
              (comma_phase_continue_compile_job
                (Comma_Continue_Program_Job program) 0 target)) \<and>
          comma_crt_eval phase (observer target (Suc clock)))"
      using row_eval[OF target, where edge=
        "comma_phase_continue_compile_job
          (Comma_Continue_Program_Job program) 0 target"]
      by (simp only: Let_def)
    show ?thesis
      using selected_row edge_exact[OF target] child_exact[OF target]
        successor_phase
      by simp
  qed
  show ?thesis
    using pointwise exact_row successor_phase by auto
qed

lemma comma_continue_operator_contract_compose:
  assumes first:
      "comma_continue_operator_contract first first_steps"
    and second:
      "comma_continue_operator_contract second second_steps"
  shows "comma_continue_operator_contract
    (comma_continue_operator_compose first second)
    (first_steps+second_steps)"
proof -
  have class_program:
    "\<exists>program. comma_semantic_phase_program_for_class source=Some program"
    if source: "source<46" for source
  proof -
    obtain program where binding:
      "comma_semantic_phase_program_for_class source=Some program"
      by (rule comma_semantic_phase_program_for_class_some[OF source])
    show ?thesis using binding by blast
  qed
  have second_output:
    "comma_crt_admitted 0 (second observer program clock)"
    if observer: "comma_continue_observer_admitted observer" for observer program clock
    using second observer
    by (auto simp: comma_continue_operator_contract_def)
  have suffix_admitted:
    "comma_continue_observer_admitted
      (\<lambda>target clock. case comma_semantic_phase_program_for_class target of
        Some child \<Rightarrow> second observer child clock
      | None \<Rightarrow> Comma_CRT_Bool False)"
    if observer: "comma_continue_observer_admitted observer" for observer
  proof -
    show ?thesis
      unfolding comma_continue_observer_admitted_def
    proof (intro allI impI)
      fix target clock :: nat
      assume target: "target<46"
      obtain child where binding:
        "comma_semantic_phase_program_for_class target=Some child"
        using comma_semantic_phase_program_for_class_some[OF target] by blast
      show "comma_crt_admitted 0
          (case comma_semantic_phase_program_for_class target of
            Some child \<Rightarrow> second observer child clock
          | None \<Rightarrow> Comma_CRT_Bool False)"
        using second_output[OF observer, of child clock] binding by simp
    qed
  qed
  have suffix_matches:
    "comma_continue_observer_matches
      (\<lambda>target clock. case comma_semantic_phase_program_for_class target of
        Some child \<Rightarrow> second observer child clock
      | None \<Rightarrow> Comma_CRT_Bool False)
      (comma_continue_suffix_predicate second_steps predicate)"
    if observer: "comma_continue_observer_admitted observer"
      and matches: "comma_continue_observer_matches observer predicate"
    for observer predicate
  proof -
    show ?thesis
      unfolding comma_continue_observer_matches_def
    proof (intro allI impI)
      fix phase target clock :: nat
      assume phase: "phase<924" and target: "target<46"
      obtain child where binding:
        "comma_semantic_phase_program_for_class target=Some child"
        using comma_semantic_phase_program_for_class_some[OF target] by blast
      have exact:
        "comma_crt_eval phase (second observer child clock) =
          (case comma_phase_class_continue_power
            comma_semantic_phase_program_class_step second_steps
            (((phase+clock) mod 924),target) of
              None \<Rightarrow> False
            | Some (terminal_phase,terminal_source) \<Rightarrow>
                predicate terminal_phase terminal_source)"
        using second observer matches phase target binding
        by (auto simp: comma_continue_operator_contract_def)
      show "comma_crt_eval phase
          (case comma_semantic_phase_program_for_class target of
            Some child \<Rightarrow> second observer child clock
          | None \<Rightarrow> Comma_CRT_Bool False) =
        comma_continue_suffix_predicate second_steps predicate
          ((phase+clock) mod 924) target"
        using exact binding
        by (simp add: comma_continue_suffix_predicate_def)
    qed
  qed
  have exact:
    "comma_crt_eval phase
        (comma_continue_operator_compose first second observer program clock) =
      (case comma_phase_class_continue_power
        comma_semantic_phase_program_class_step (first_steps+second_steps)
        (((phase+clock) mod 924),source) of
          None \<Rightarrow> False
        | Some (terminal_phase,terminal_source) \<Rightarrow>
            predicate terminal_phase terminal_source)"
    if observer: "comma_continue_observer_admitted observer"
      and matches: "comma_continue_observer_matches observer predicate"
      and source: "source<46" and phase: "phase<924"
      and binding: "comma_semantic_phase_program_for_class source=Some program"
    for observer predicate source program clock phase
  proof -
    let ?suffix = "\<lambda>target clock.
      case comma_semantic_phase_program_for_class target of
        Some child \<Rightarrow> second observer child clock
      | None \<Rightarrow> Comma_CRT_Bool False"
    have prefix:
      "comma_crt_eval phase (first ?suffix program clock) =
        (case comma_phase_class_continue_power
          comma_semantic_phase_program_class_step first_steps
          (((phase+clock) mod 924),source) of
            None \<Rightarrow> False
          | Some (middle_phase,middle_source) \<Rightarrow>
              comma_continue_suffix_predicate second_steps predicate
                middle_phase middle_source)"
      using first suffix_admitted[OF observer] suffix_matches[OF observer matches]
        source phase binding
      by (auto simp: comma_continue_operator_contract_def)
    have power_add:
      "comma_phase_class_continue_power
          comma_semantic_phase_program_class_step (first_steps+second_steps)
          (initial_phase,source) =
        Option.bind
          (comma_phase_class_continue_power
            comma_semantic_phase_program_class_step first_steps
            (initial_phase,source))
          (comma_phase_class_continue_power
            comma_semantic_phase_program_class_step second_steps)"
      for initial_phase
      by (rule comma_phase_class_continue_power_add)
    show ?thesis
      using prefix power_add phase
      by (auto simp: comma_continue_operator_compose_def
          comma_continue_suffix_predicate_def
          split: option.splits prod.splits)
  qed
  show ?thesis
    unfolding comma_continue_operator_contract_def
  proof (intro conjI)
    show "\<forall>observer. comma_continue_observer_admitted observer \<longrightarrow>
        (\<forall>program clock. comma_crt_admitted 0
          (comma_continue_operator_compose first second observer program clock))"
    proof (intro allI impI)
      fix observer program clock
      assume observer: "comma_continue_observer_admitted observer"
      let ?suffix = "\<lambda>target next_clock.
        case comma_semantic_phase_program_for_class target of
          Some child \<Rightarrow> second observer child next_clock
        | None \<Rightarrow> Comma_CRT_Bool False"
      have inner: "comma_continue_observer_admitted ?suffix"
        by (rule suffix_admitted[OF observer])
      have first_adm:
        "comma_crt_admitted 0 (first ?suffix program clock)"
        using first inner by (auto simp: comma_continue_operator_contract_def)
      show "comma_crt_admitted 0
          (comma_continue_operator_compose first second observer program clock)"
        using first_adm by (simp add: comma_continue_operator_compose_def)
    qed
  next
    show "\<forall>observer predicate program source clock phase.
        comma_continue_observer_admitted observer \<longrightarrow>
        comma_continue_observer_matches observer predicate \<longrightarrow>
        source<46 \<longrightarrow> phase<924 \<longrightarrow>
        comma_semantic_phase_program_for_class source=Some program \<longrightarrow>
        comma_crt_eval phase
          (comma_continue_operator_compose first second observer program clock) =
        (case comma_phase_class_continue_power
          comma_semantic_phase_program_class_step (first_steps+second_steps)
          (((phase+clock) mod 924),source) of
            None \<Rightarrow> False
          | Some (terminal_phase,terminal_source) \<Rightarrow>
              predicate terminal_phase terminal_source)"
      using exact by blast
  qed
qed

lemma comma_continue_operator_1_contract:
  "comma_continue_operator_contract comma_continue_operator_1 1"
proof -
  have step_exact:
    "comma_crt_eval phase
        (comma_continue_operator_1 observer program clock) =
      (case comma_phase_class_continue_power
        comma_semantic_phase_program_class_step 1
        (((phase+clock) mod 924),source) of
          None \<Rightarrow> False
        | Some (terminal_phase,terminal_source) \<Rightarrow>
            predicate terminal_phase terminal_source)"
    if phase: "phase<924" and source: "source<46"
      and binding: "comma_semantic_phase_program_for_class source=Some program"
      and observer: "comma_continue_observer_admitted observer"
      and matches: "comma_continue_observer_matches observer predicate"
    for observer predicate program source clock phase
  proof -
    have action:
      "comma_crt_eval phase
          (comma_continue_operator_step observer program clock) =
        (\<exists>target<46.
          comma_semantic_phase_program_class_step ((phase+clock) mod 924) source =
            Comma_Phase_Class_Continue
              ((((phase+clock) mod 924)+1) mod 924) target \<and>
          predicate ((phase+Suc clock) mod 924) target)"
      by (rule comma_continue_operator_step_exact[
          OF phase source binding observer matches])
    have power_one:
      "comma_phase_class_continue_power
        comma_semantic_phase_program_class_step 1
        (((phase+clock) mod 924),source) =
        (case comma_semantic_phase_program_class_step
          ((phase+clock) mod 924) source of
          Comma_Phase_Class_Continue next_phase next_source \<Rightarrow>
            Some (next_phase,next_source)
        | _ \<Rightarrow> None)"
      by (simp add: comma_phase_class_continue_power_def
          comma_phase_class_continue_option_step_def)
    have successor:
      "((phase+Suc clock) mod 924) =
        ((((phase+clock) mod 924)+1) mod 924)"
      by (simp add: mod_Suc_eq)
    have valid_state:
      "comma_semantic_phase_class_valid ((phase+clock) mod 924) source"
      using source by (simp add: comma_semantic_phase_class_valid_def)
    show ?thesis
    proof (cases "comma_semantic_phase_program_class_step
        ((phase+clock) mod 924) source")
      case Comma_Phase_Class_Invalid
      then show ?thesis
        using action power_one
        by (simp add: comma_continue_operator_1_def)
    next
      case (Comma_Phase_Class_Fork left right)
      then show ?thesis
        using action power_one
        by (simp add: comma_continue_operator_1_def)
    next
      case (Comma_Phase_Class_Landmine height)
      then show ?thesis
        using action power_one
        by (simp add: comma_continue_operator_1_def)
    next
      case (Comma_Phase_Class_Continue next_phase next_source)
      have closed:
        "next_phase=(((phase+clock) mod 924)+1) mod 924"
        by (rule comma_semantic_phase_program_class_step_continue_closed(1)
            [OF valid_state Comma_Phase_Class_Continue])
      have next_valid:
        "comma_semantic_phase_class_valid next_phase next_source"
        by (rule comma_semantic_phase_program_class_step_continue_closed(2)
            [OF valid_state Comma_Phase_Class_Continue])
      have next_source_bound: "next_source<46"
        using next_valid
        by (simp add: comma_semantic_phase_class_valid_def)
      show ?thesis
        using action power_one successor closed(1) next_source_bound
          Comma_Phase_Class_Continue
        by (simp add: comma_continue_operator_1_def)
    qed
  qed
  show ?thesis
    unfolding comma_continue_operator_contract_def
  proof (intro conjI)
    show "\<forall>observer. comma_continue_observer_admitted observer \<longrightarrow>
        (\<forall>program clock. comma_crt_admitted 0
          (comma_continue_operator_1 observer program clock))"
      using comma_continue_operator_step_admitted
      by (auto simp only: comma_continue_operator_1_def)
  next
    show "\<forall>observer predicate program source clock phase.
        comma_continue_observer_admitted observer \<longrightarrow>
        comma_continue_observer_matches observer predicate \<longrightarrow>
        source<46 \<longrightarrow> phase<924 \<longrightarrow>
        comma_semantic_phase_program_for_class source=Some program \<longrightarrow>
        comma_crt_eval phase
          (comma_continue_operator_1 observer program clock) =
        (case comma_phase_class_continue_power
          comma_semantic_phase_program_class_step 1
          (((phase+clock) mod 924),source) of
            None \<Rightarrow> False
          | Some (terminal_phase,terminal_source) \<Rightarrow>
              predicate terminal_phase terminal_source)"
      using step_exact by blast
  qed
qed

lemma comma_continue_operator_2_contract:
  "comma_continue_operator_contract comma_continue_operator_2 2"
proof -
  have composed:
    "comma_continue_operator_contract
      (comma_continue_operator_compose comma_continue_operator_1
        comma_continue_operator_1) (1+1)"
    by (rule comma_continue_operator_contract_compose[
        OF comma_continue_operator_1_contract comma_continue_operator_1_contract])
  have composed_two:
    "comma_continue_operator_contract
      (comma_continue_operator_compose comma_continue_operator_1
        comma_continue_operator_1) 2"
    using composed by (simp add: numeral_eq_Suc)
  show ?thesis
    using composed_two
    by (simp add: comma_continue_operator_2_def
        comma_continue_operator_compose_def)
qed

lemma comma_continue_operator_4_contract:
  "comma_continue_operator_contract comma_continue_operator_4 4"
  using comma_continue_operator_contract_compose[
      OF comma_continue_operator_2_contract comma_continue_operator_2_contract]
  by (simp add: comma_continue_operator_4_def
      comma_continue_operator_compose_def)

lemma comma_continue_operator_8_contract:
  "comma_continue_operator_contract comma_continue_operator_8 8"
  using comma_continue_operator_contract_compose[
      OF comma_continue_operator_4_contract comma_continue_operator_4_contract]
  by (simp add: comma_continue_operator_8_def
      comma_continue_operator_compose_def)

lemma comma_continue_operator_16_contract:
  "comma_continue_operator_contract comma_continue_operator_16 16"
  using comma_continue_operator_contract_compose[
      OF comma_continue_operator_8_contract comma_continue_operator_8_contract]
  by (simp add: comma_continue_operator_16_def
      comma_continue_operator_compose_def)

lemma comma_continue_operator_24_contract:
  "comma_continue_operator_contract comma_continue_operator_24 24"
  using comma_continue_operator_contract_compose[
      OF comma_continue_operator_16_contract comma_continue_operator_8_contract]
  by (simp add: comma_continue_operator_24_def
      comma_continue_operator_compose_def)

ML \<open>
  val published = @{thms comma_continue_operator_24_contract}
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "operator-24 chronological observer contract" published
\<close>

end
