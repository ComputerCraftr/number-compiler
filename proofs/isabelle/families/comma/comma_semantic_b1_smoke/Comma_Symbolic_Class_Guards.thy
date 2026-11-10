theory Comma_Symbolic_Class_Guards
  imports Comma_Semantic_B1.Comma_Symbolic_Class_Step
    Comma_Semantic_B1.Comma_CRT_Apply
    Comma_Semantic_B1.Comma_CRT_Power
    Comma_Weighted_CRT_Guard
    Comma_Semantic_B1.Comma_Core_Value_Guards
begin

text \<open>
A source-free symbolic recurrence for the first 27 all-Continue transitions.
Each edge is a certified CRT guard over the external 924 clock.  A frontier
step consumes an already-built suffix column for each target class, combines
it with the edge guard using shifted Boolean apply, and reuses the established
CRT output collector. Its fixed Invalid label is only an internal grouping
label, not a transition outcome. The frontier law is the producer interface: callers
may build one vector of columns per depth and share that vector across all
source classes.  No recursive survival-column term is used as the concrete
certificate or executable fallback.
\<close>

lemma comma_weighted_crt_continue_column_step_exact:
  assumes shape: "comma_weighted_crt_shape 0 tree"
    and action: "comma_weighted_crt_eval tree phase = Some (step phase source,elapsed)"
    and clock: "\<And>next_phase next_class.
      step phase source=Comma_Phase_Class_Continue next_phase next_class \<Longrightarrow>
      next_phase=(phase+1) mod 924"
  shows "comma_crt_eval phase (comma_weighted_crt_continue_column target tree) =
    (step phase source=Comma_Phase_Class_Continue ((phase+1) mod 924) target)"
proof (cases "step phase source")
  case (Comma_Phase_Class_Continue next_phase next_class)
  have phase_eq: "next_phase=(phase+1) mod 924"
    by (rule clock[OF Comma_Phase_Class_Continue])
  show ?thesis
    using comma_weighted_crt_continue_column_eval[OF shape, where phase=phase and target=target]
      action Comma_Phase_Class_Continue phase_eq by simp
qed (use comma_weighted_crt_continue_column_eval[OF shape, where phase=phase and target=target]
    action in auto)

definition comma_phase_guard_survival_rows ::
    "('c \<Rightarrow> 'c \<Rightarrow> comma_crt_column) \<Rightarrow> 'c list \<Rightarrow>
      ('c \<Rightarrow> comma_crt_column) \<Rightarrow> 'c \<Rightarrow>
      comma_crt_return_row list" where
  "comma_phase_guard_survival_rows guard classes suffix source =
    map (\<lambda>target.
      (comma_crt_apply_shifted Comma_CRT_And 1 (guard source target)
        (suffix target), Comma_Semantic_B1_Invalid)) classes"

definition comma_phase_guard_survival_frontier_step ::
    "('c \<Rightarrow> 'c \<Rightarrow> comma_crt_column) \<Rightarrow> 'c list \<Rightarrow>
      ('c \<Rightarrow> comma_crt_column) \<Rightarrow> 'c \<Rightarrow> comma_crt_column" where
  "comma_phase_guard_survival_frontier_step guard classes suffix source =
    comma_crt_collect_output Comma_Semantic_B1_Invalid
      (comma_phase_guard_survival_rows guard classes suffix source)"

lemma comma_phase_guard_survival_rows_admitted:
  assumes guard_admitted:
      "\<And>source target. target \<in> set classes \<Longrightarrow>
        comma_crt_admitted 0 (guard source target)"
    and suffix_admitted:
      "\<And>target. target \<in> set classes \<Longrightarrow>
        comma_crt_admitted 0 (suffix target)"
  shows "comma_crt_rows_admitted
    (comma_phase_guard_survival_rows guard classes suffix source)"
  using guard_admitted suffix_admitted
  by (auto simp: comma_crt_rows_admitted_def
      comma_phase_guard_survival_rows_def
      intro: comma_crt_apply_shifted_admitted)

lemma comma_phase_guard_survival_frontier_step_admitted:
  assumes guard_admitted:
      "\<And>source target. target \<in> set classes \<Longrightarrow>
        comma_crt_admitted 0 (guard source target)"
    and suffix_admitted:
      "\<And>target. target \<in> set classes \<Longrightarrow>
        comma_crt_admitted 0 (suffix target)"
  shows "comma_crt_admitted 0
    (comma_phase_guard_survival_frontier_step guard classes suffix source)"
proof -
  have rows:
      "comma_crt_rows_admitted
        (comma_phase_guard_survival_rows guard classes suffix source)"
    by (rule comma_phase_guard_survival_rows_admitted
      [OF guard_admitted suffix_admitted])
  show ?thesis
    unfolding comma_phase_guard_survival_frontier_step_def
    by (rule comma_crt_collect_output_admitted[OF rows])
qed

lemma comma_crt_collect_output_eval_iff:
  assumes rows: "comma_crt_rows_admitted rows"
    and phase: "phase<924"
  shows "comma_crt_eval phase (comma_crt_collect_output outcome rows) \<longleftrightarrow>
    (\<exists>row\<in>set rows. snd row=outcome \<and>
      comma_crt_eval phase (fst row))"
  using comma_crt_collect_output_set[OF rows] phase
  by (auto simp: comma_crt_set_def)

lemma comma_phase_guard_survival_edge_eval:
  assumes guard: "comma_crt_admitted 0 guard"
    and suffix: "comma_crt_admitted 0 suffix"
  shows "comma_crt_eval phase
      (comma_crt_apply_shifted Comma_CRT_And 1 guard suffix) =
    (comma_crt_eval phase guard \<and>
      comma_crt_eval ((phase+1) mod 924) suffix)"
proof -
  have applied:
      "comma_crt_eval phase
        (comma_crt_apply_shifted Comma_CRT_And 1 guard suffix) =
       comma_crt_boolean_value Comma_CRT_And
         (comma_crt_eval phase guard) (comma_crt_eval (phase+1) suffix)"
    by (rule comma_crt_apply_shifted_refines_boolean[OF guard suffix])
  have periodic:
      "comma_crt_eval ((phase+1) mod 924) suffix =
        comma_crt_eval (phase+1) suffix"
    by (rule comma_crt_eval_periodic[OF suffix])
  show ?thesis
    using applied periodic
    by (simp add: comma_crt_boolean_value_def)
qed

lemma comma_phase_guard_survival_frontier_step_eval:
  assumes guard_admitted:
      "\<And>source target. target \<in> set classes \<Longrightarrow>
        comma_crt_admitted 0 (guard source target)"
    and suffix_admitted:
      "\<And>target. target \<in> set classes \<Longrightarrow>
        comma_crt_admitted 0 (suffix target)"
    and suffix_exact:
      "\<And>phase target. phase<924 \<Longrightarrow> valid phase target \<Longrightarrow>
        comma_crt_eval phase (suffix target) =
          comma_phase_class_survives step depth phase target"
    and guard_exact:
      "\<And>phase source target. phase<924 \<Longrightarrow> valid phase source \<Longrightarrow>
        comma_crt_eval phase (guard source target) =
          (step phase source =
            Comma_Phase_Class_Continue ((phase+1) mod 924) target)"
    and successor_closed:
      "\<And>phase source target_phase target. phase<924 \<Longrightarrow>
        valid phase source \<Longrightarrow>
        step phase source = Comma_Phase_Class_Continue target_phase target \<Longrightarrow>
        target_phase=(phase+1) mod 924 \<and> valid target_phase target \<and>
          target \<in> set classes"
    and phase_bound: "phase<924"
    and source_valid: "valid phase source"
  shows "comma_crt_eval phase
      (comma_phase_guard_survival_frontier_step guard classes suffix source) =
    comma_phase_class_survives step (Suc depth) phase source"
proof -
  let ?phase_next = "(phase+1) mod 924"
  have rows_admitted:
      "comma_crt_rows_admitted
        (comma_phase_guard_survival_rows guard classes suffix source)"
    by (rule comma_phase_guard_survival_rows_admitted
      [OF guard_admitted suffix_admitted])
  have collected:
      "comma_crt_eval phase
        (comma_phase_guard_survival_frontier_step guard classes suffix source) =
       (\<exists>target\<in>set classes.
          comma_crt_eval phase (guard source target) \<and>
          comma_crt_eval ?phase_next (suffix target))"
  proof -
    have collect_exact:
        "comma_crt_eval phase
          (comma_crt_collect_output Comma_Semantic_B1_Invalid
            (comma_phase_guard_survival_rows guard classes suffix source)) =
          (\<exists>row\<in>set (comma_phase_guard_survival_rows guard classes suffix source).
            snd row=Comma_Semantic_B1_Invalid \<and>
            comma_crt_eval phase (fst row))"
      by (rule comma_crt_collect_output_eval_iff[OF rows_admitted phase_bound])
    have rows_exact:
        "(\<exists>row\<in>set (comma_phase_guard_survival_rows guard classes suffix source).
          snd row=Comma_Semantic_B1_Invalid \<and>
          comma_crt_eval phase (fst row)) =
         (\<exists>target\<in>set classes.
          comma_crt_eval phase (guard source target) \<and>
          comma_crt_eval ?phase_next (suffix target))"
    proof -
      have edge:
          "comma_crt_eval phase
              (comma_crt_apply_shifted Comma_CRT_And 1 (guard source target)
                (suffix target)) =
            (comma_crt_eval phase (guard source target) \<and>
              comma_crt_eval ?phase_next (suffix target))"
        if member: "target\<in>set classes" for target
      proof -
        have guard_ok: "comma_crt_admitted 0 (guard source target)"
          by (rule guard_admitted[OF member])
        have suffix_ok: "comma_crt_admitted 0 (suffix target)"
          by (rule suffix_admitted[OF member])
        show ?thesis
          by (rule comma_phase_guard_survival_edge_eval[OF guard_ok suffix_ok])
      qed
      show ?thesis
        using edge
        by (auto simp: comma_phase_guard_survival_rows_def)
    qed
    show ?thesis
      using collect_exact rows_exact
      by (simp only: comma_phase_guard_survival_frontier_step_def)
  qed
  show ?thesis
  proof (cases "step phase source")
    case Comma_Phase_Class_Invalid
    have guard_false:
        "comma_crt_eval phase (guard source target)=False"
      if target_member: "target\<in>set classes" for target
      using guard_exact[OF phase_bound source_valid, of target]
        Comma_Phase_Class_Invalid by simp
    show ?thesis
      using collected guard_false Comma_Phase_Class_Invalid
      by (simp add: comma_phase_class_survives.simps)
  next
    case (Comma_Phase_Class_Fork fork_digit fork_offset)
    have guard_false:
        "comma_crt_eval phase (guard source target)=False"
      if target_member: "target\<in>set classes" for target
      using guard_exact[OF phase_bound source_valid, of target]
        Comma_Phase_Class_Fork by simp
    show ?thesis
      using collected guard_false Comma_Phase_Class_Fork
      by (simp add: comma_phase_class_survives.simps)
  next
    case (Comma_Phase_Class_Landmine landmine_offset)
    have guard_false:
        "comma_crt_eval phase (guard source target)=False"
      if target_member: "target\<in>set classes" for target
      using guard_exact[OF phase_bound source_valid, of target]
        Comma_Phase_Class_Landmine by simp
    show ?thesis
      using collected guard_false Comma_Phase_Class_Landmine
      by (simp add: comma_phase_class_survives.simps)
  next
    case (Comma_Phase_Class_Continue target_phase target)
    have closure:
        "target_phase=?phase_next \<and> valid target_phase target \<and>
          target\<in>set classes"
      by (rule successor_closed[OF phase_bound source_valid
        Comma_Phase_Class_Continue])
    then have phase_eq: "target_phase=?phase_next"
      and target_valid: "valid target_phase target"
      and target_member: "target\<in>set classes" by auto
    have guard_exact_target:
        "comma_crt_eval phase (guard source candidate) = (candidate=target)"
      for candidate
      using guard_exact[OF phase_bound source_valid, of candidate]
        Comma_Phase_Class_Continue phase_eq by (simp add: eq_commute)
    have target_phase_bound: "target_phase<924"
      using phase_eq by simp
    have suffix_refines:
        "comma_crt_eval target_phase (suffix target) =
          comma_phase_class_survives step depth target_phase target"
      by (rule suffix_exact[OF target_phase_bound target_valid])
    have existential_exact:
        "(\<exists>candidate\<in>set classes.
          comma_crt_eval phase (guard source candidate) \<and>
          comma_crt_eval target_phase (suffix candidate)) =
         comma_crt_eval target_phase (suffix target)"
      using guard_exact_target target_member by auto
    have survives_step:
        "comma_phase_class_survives step (Suc depth) phase source =
          comma_phase_class_survives step depth target_phase target"
      by (rule comma_phase_class_survives_continue
        [where step=step and phase=phase and c=source and n=depth,
          OF Comma_Phase_Class_Continue])
    show ?thesis
      using collected existential_exact suffix_refines survives_step phase_eq
      by simp
  qed
qed

lemma comma_phase_guard_survival_frontiers_admitted:
  fixes frontiers :: "nat \<Rightarrow> 'c \<Rightarrow> comma_crt_column"
  assumes guard_admitted:
      "\<And>source target. target \<in> set classes \<Longrightarrow>
        comma_crt_admitted 0 (guard source target)"
    and base:
      "\<And>source. source\<in>set classes \<Longrightarrow>
        frontiers 0 source=Comma_CRT_Bool True"
    and advance:
      "\<And>depth source. depth<horizon \<Longrightarrow> source\<in>set classes \<Longrightarrow>
        frontiers (Suc depth) source=
          comma_phase_guard_survival_frontier_step guard classes
            (frontiers depth) source"
    and bounded: "depth\<le>horizon"
    and member: "source\<in>set classes"
  shows "comma_crt_admitted 0 (frontiers depth source)"
  using bounded member
proof (induction depth arbitrary: source)
  case 0
  have initial: "frontiers 0 source=Comma_CRT_Bool True"
    by (rule base[OF "0.prems"(2)])
  show ?case using initial by simp
next
  case (Suc depth)
  have smaller: "depth\<le>horizon" and strict: "depth<horizon"
    using Suc.prems(1) by arith+
  have suffix_admitted:
      "comma_crt_admitted 0 (frontiers depth target)"
    if target_member: "target\<in>set classes" for target
    by (rule Suc.IH[OF smaller target_member])
  have next_admitted:
      "comma_crt_admitted 0
        (comma_phase_guard_survival_frontier_step guard classes
          (frontiers depth) source)"
    by (rule comma_phase_guard_survival_frontier_step_admitted
      [OF guard_admitted suffix_admitted])
  have step_eq: "frontiers (Suc depth) source=
      comma_phase_guard_survival_frontier_step guard classes
        (frontiers depth) source"
    by (rule advance[OF strict Suc.prems(2)])
  show ?case using step_eq next_admitted by simp
qed

lemma comma_phase_guard_survival_frontiers_exact:
  fixes frontiers :: "nat \<Rightarrow> 'c \<Rightarrow> comma_crt_column"
  assumes guard_admitted:
      "\<And>source target. target \<in> set classes \<Longrightarrow>
        comma_crt_admitted 0 (guard source target)"
    and guard_exact:
      "\<And>phase source target. phase<924 \<Longrightarrow> valid phase source \<Longrightarrow>
        comma_crt_eval phase (guard source target) =
          (step phase source =
            Comma_Phase_Class_Continue ((phase+1) mod 924) target)"
    and successor_closed:
      "\<And>phase source target_phase target. phase<924 \<Longrightarrow>
        valid phase source \<Longrightarrow>
        step phase source = Comma_Phase_Class_Continue target_phase target \<Longrightarrow>
        target_phase=(phase+1) mod 924 \<and> valid target_phase target \<and>
          target \<in> set classes"
    and valid_in_classes:
      "\<And>phase source. valid phase source \<Longrightarrow>
        source\<in>set classes"
    and base:
      "\<And>source. source\<in>set classes \<Longrightarrow>
        frontiers 0 source=Comma_CRT_Bool True"
    and advance:
      "\<And>depth source. depth<horizon \<Longrightarrow> source\<in>set classes \<Longrightarrow>
        frontiers (Suc depth) source=
          comma_phase_guard_survival_frontier_step guard classes
            (frontiers depth) source"
    and bounded: "depth\<le>horizon"
    and phase_bound: "phase<924"
    and source_valid: "valid phase source"
  shows "comma_crt_eval phase (frontiers depth source) =
    comma_phase_class_survives step depth phase source"
  using bounded phase_bound source_valid
proof (induction depth arbitrary: phase source)
  case 0
  have source_member: "source\<in>set classes"
    by (rule valid_in_classes[OF "0.prems"(3)])
  have initial: "frontiers 0 source=Comma_CRT_Bool True"
    by (rule base[OF source_member])
  show ?case using initial
    by (simp only: comma_crt_eval.simps comma_phase_class_survives.simps)
next
  case (Suc depth)
  have smaller: "depth\<le>horizon" and strict: "depth<horizon"
    using Suc.prems(1) by arith+
  have source_member: "source\<in>set classes"
    by (rule valid_in_classes[OF Suc.prems(3)])
  have suffix_admitted:
      "comma_crt_admitted 0 (frontiers depth target)"
    if target_member: "target\<in>set classes" for target
    by (rule comma_phase_guard_survival_frontiers_admitted
      [OF guard_admitted base advance smaller target_member])
  have suffix_exact:
      "comma_crt_eval q (frontiers depth target) =
        comma_phase_class_survives step depth q target"
    if q_bound: "q<924" and target_valid: "valid q target" for q target
    by (rule Suc.IH[OF smaller q_bound target_valid])
  have frontier_exact:
      "comma_crt_eval phase
          (comma_phase_guard_survival_frontier_step guard classes
            (frontiers depth) source) =
        comma_phase_class_survives step (Suc depth) phase source"
    by (rule comma_phase_guard_survival_frontier_step_eval
      [OF guard_admitted suffix_admitted suffix_exact guard_exact successor_closed
        Suc.prems(2) Suc.prems(3)])
  have step: "frontiers (Suc depth) source=
      comma_phase_guard_survival_frontier_step guard classes
        (frontiers depth) source"
    by (rule advance[OF strict source_member])
  show ?case using step frontier_exact by simp
qed

theorem comma_semantic_phase_guarded_B32_if_final_frontier_empty:
  fixes frontiers :: "nat \<Rightarrow> nat \<Rightarrow> comma_crt_column"
  assumes guard_admitted:
      "\<And>source target. target\<in>set [0..<46] \<Longrightarrow>
        comma_crt_admitted 0 (guard source target)"
    and guard_observer:
      "\<And>phase source target. phase<924 \<Longrightarrow>
        comma_semantic_phase_class_valid phase source \<Longrightarrow>
        comma_crt_eval phase (guard source target) =
          comma_semantic_phase_program_class_continue_guard phase source target"
    and base:
      "\<And>source. source\<in>set [0..<46] \<Longrightarrow>
        frontiers 0 source=Comma_CRT_Bool True"
    and advance:
      "\<And>depth source. depth<27 \<Longrightarrow> source\<in>set [0..<46] \<Longrightarrow>
        frontiers (Suc depth) source=
          comma_phase_guard_survival_frontier_step guard [0..<46]
            (frontiers depth) source"
    and final_empty:
      "\<And>source. source<46 \<Longrightarrow>
        frontiers 27 source=Comma_CRT_Bool False"
    and admitted: "comma_decade_admitted s"
  shows "\<exists>height terminal. height\<le>26 \<and>
    comma_decade_block_power 5 s=Comma_Block_Stop height terminal \<and>
    comma_residual_block 32 (height,terminal)=Comma_Residual_Stop height terminal \<and>
    comma_decade_exact_summary s height terminal"
proof -
  have guard_exact:
      "\<And>phase source target. phase<924 \<Longrightarrow>
        comma_semantic_phase_class_valid phase source \<Longrightarrow>
        comma_crt_eval phase (guard source target) =
          (comma_semantic_phase_program_class_step phase source =
            Comma_Phase_Class_Continue ((phase+1) mod 924) target)"
  proof -
    fix phase source target
    assume phase: "phase<924"
      and valid: "comma_semantic_phase_class_valid phase source"
    have bound: "source<46"
      using valid by (simp add: comma_semantic_phase_class_valid_def)
    show "comma_crt_eval phase (guard source target) =
        (comma_semantic_phase_program_class_step phase source =
          Comma_Phase_Class_Continue ((phase+1) mod 924) target)"
      using guard_observer[OF phase valid, of target]
        comma_semantic_phase_program_class_continue_guard_exact
          [OF phase bound, of target] by simp
  qed
  have successor_closed:
      "\<And>phase source target_phase target. phase<924 \<Longrightarrow>
        comma_semantic_phase_class_valid phase source \<Longrightarrow>
        comma_semantic_phase_program_class_step phase source =
          Comma_Phase_Class_Continue target_phase target \<Longrightarrow>
        target_phase=(phase+1) mod 924 \<and>
          comma_semantic_phase_class_valid target_phase target \<and>
          target\<in>set [0..<46]"
  proof -
    fix phase source target_phase target
    assume phase: "phase<924"
      and source_valid: "comma_semantic_phase_class_valid phase source"
      and move: "comma_semantic_phase_program_class_step phase source =
        Comma_Phase_Class_Continue target_phase target"
    have closed:
        "target_phase=(phase+1) mod 924 \<and>
          comma_semantic_phase_class_valid target_phase target"
      using comma_semantic_phase_program_class_step_continue_closed
        [OF source_valid move] by blast
    have target_bound: "target<46"
      using closed by (simp add: comma_semantic_phase_class_valid_def)
    show "target_phase=(phase+1) mod 924 \<and>
        comma_semantic_phase_class_valid target_phase target \<and>
        target\<in>set [0..<46]"
      using closed target_bound by auto
  qed
  have valid_in_classes:
      "\<And>phase source. comma_semantic_phase_class_valid phase source \<Longrightarrow>
        source\<in>set [0..<46]"
    by (auto simp: comma_semantic_phase_class_valid_def)
  have no_27:
      "\<And>phase source. comma_semantic_phase_class_valid phase source \<Longrightarrow>
        \<not> comma_phase_class_survives
          comma_semantic_phase_program_class_step 27 phase source"
  proof -
    fix phase source
    assume valid: "comma_semantic_phase_class_valid phase source"
    have phase_bound: "phase<924"
      using valid by (simp add: comma_semantic_phase_class_valid_def)
    have source_bound: "source<46"
      using valid by (simp add: comma_semantic_phase_class_valid_def)
    have exact:
        "comma_crt_eval phase (frontiers 27 source) =
          comma_phase_class_survives comma_semantic_phase_program_class_step
            27 phase source"
      by (rule comma_phase_guard_survival_frontiers_exact
        [OF guard_admitted guard_exact successor_closed valid_in_classes
          base advance order_refl phase_bound valid])
    have false:
        "frontiers 27 source=Comma_CRT_Bool False"
      by (rule final_empty[OF source_bound])
    show "\<not> comma_phase_class_survives
        comma_semantic_phase_program_class_step 27 phase source"
      using exact false by simp
  qed
  show ?thesis
    by (rule comma_semantic_phase_program_class_step_B32_if_no_27
      [OF no_27 admitted])
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Guarded symbolic class survival and conditional B32 bridge"
    @{thms comma_phase_guard_survival_frontier_step_eval
      comma_phase_guard_survival_frontiers_exact
      comma_semantic_phase_guarded_B32_if_final_frontier_empty};
\<close>

end
