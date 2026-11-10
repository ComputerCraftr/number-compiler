theory Comma_Program_Continue_Guard_Exact
  imports Comma_Program_Continue_Guard
begin

lemma comma_core_value_guard_unsupported_no_eval:
  assumes unsupported:
    "\<not> comma_crt_supported (comma_core_value_guard core wanted)"
  shows "\<not> comma_crt_eval phase (comma_core_value_guard core wanted)"
proof
  assume evaluates: "comma_crt_eval phase (comma_core_value_guard core wanted)"
  have admitted:
    "comma_crt_admitted 0 (comma_core_value_guard core wanted)"
    by (rule comma_core_value_guard_admitted)
  have "comma_crt_supported (comma_core_value_guard core wanted)"
    by (rule comma_crt_eval_supported[OF admitted evaluates])
  with unsupported show False by contradiction
qed

lemma comma_phase_continue_near_residual_step_action:
  assumes structural:
    "comma_phase_program_structurally_admitted
      (Comma_Near_Residual_Program f d residual)"
  shows "comma_phase_program_step_at
      (Comma_Near_Residual_Program f d residual) phase shift =
    comma_phase_program_step_of_action
      (comma_source_continuation_transport shift
        (comma_phase_program_operator_nf
          (Comma_Near_Residual_Program f d residual) 0))"
  using structural
  by (simp add: comma_phase_program_step_at_def
      comma_near_symbolic_port_operator_eval)

lemma comma_phase_continue_near_boundary_step_action:
  assumes structural:
    "comma_phase_program_structurally_admitted
      (Comma_Near_Boundary_Program f)"
  shows "comma_phase_program_step_at
      (Comma_Near_Boundary_Program f) phase shift =
    comma_phase_program_step_of_action
      (comma_source_continuation_transport shift
        (comma_phase_program_operator_nf
          (Comma_Near_Boundary_Program f) 0))"
  using structural
  by (simp add: comma_phase_program_step_at_def
      comma_near_symbolic_port_operator_eval)

lemma comma_phase_continue_compile_job_exact:
  "comma_crt_eval phase
      (comma_phase_continue_compile_job job shift target) =
    comma_phase_continue_compile_job_observer phase job shift target"
proof (induction job arbitrary: phase shift target
    rule: comma_phase_continue_compile_job.induct)
  case (1 program)
  note program_IH = "1.IH"
  show ?case
  proof (cases program)
    case (Comma_Entry_Core_Program f d residue core)
    then show ?thesis
    proof (cases "comma_phase_program_structurally_admitted program")
      case False
      then show ?thesis
        using False Comma_Entry_Core_Program
        by (simp only: comma_phase_continue_compile_job.simps(1) if_False
            comma_crt_eval.simps(1)
            comma_phase_continue_compile_job_observer.simps
            comma_phase_continue_false_columns_def
            comma_phase_program_step_at_def
            comma_phase_continue_step_observer.simps)
    next
      case True
      have child_exact:
        "comma_crt_eval phase
            (comma_phase_continue_compile_job
              (Comma_Continue_Core_Values_Job f residue core
                [0..<comma_phase_core_modulus core]) shift target) =
          comma_phase_continue_compile_job_observer phase
            (Comma_Continue_Core_Values_Job f residue core
              [0..<comma_phase_core_modulus core]) shift target"
        by (rule program_IH(1)[OF True Comma_Entry_Core_Program])
      have structural_entry:
        "comma_phase_program_structurally_admitted
          (Comma_Entry_Core_Program f d residue core)"
        using True Comma_Entry_Core_Program by simp
      have child_observer:
        "comma_phase_continue_compile_job_observer phase
            (Comma_Continue_Core_Values_Job f residue core
              [0..<comma_phase_core_modulus core]) shift target =
          comma_phase_continue_step_observer phase target
            (comma_phase_program_step_at
              (Comma_Entry_Core_Program f d residue core) phase shift)"
        by (rule comma_phase_continue_entry_core_values_observer_exact
          [OF structural_entry])
      have entry_exact:
        "comma_crt_eval phase
            (comma_phase_continue_compile_job
              (Comma_Continue_Core_Values_Job f residue core
                [0..<comma_phase_core_modulus core]) shift target) =
          comma_phase_continue_step_observer phase target
            (comma_phase_program_step_at
              (Comma_Entry_Core_Program f d residue core) phase shift)"
        using child_exact child_observer by simp
      have entry_job:
        "comma_phase_continue_compile_job
            (Comma_Continue_Program_Job program) shift target =
          comma_phase_continue_compile_job
            (Comma_Continue_Core_Values_Job f residue core
              [0..<comma_phase_core_modulus core]) shift target"
        using True Comma_Entry_Core_Program
        by (simp only: comma_phase_continue_compile_job.simps(1) if_True
            comma_semantic_port_program.case)
      have entry_observer:
        "comma_phase_continue_compile_job_observer phase
            (Comma_Continue_Program_Job program) shift target =
          comma_phase_continue_step_observer phase target
            (comma_phase_program_step_at
              (Comma_Entry_Core_Program f d residue core) phase shift)"
        using Comma_Entry_Core_Program
        by (simp only: comma_phase_continue_compile_job_observer.simps)
      show ?thesis
        using entry_exact entry_job entry_observer by simp
    qed
  next
    case (Comma_Near_Residual_Program f d residual)
    then show ?thesis
    proof (cases "comma_phase_program_structurally_admitted program")
      case False
      then show ?thesis
        using False Comma_Near_Residual_Program
        by (simp only: comma_phase_continue_compile_job.simps(1) if_False
            comma_crt_eval.simps(1)
            comma_phase_continue_compile_job_observer.simps
            comma_phase_continue_false_columns_def
            comma_phase_program_step_at_def
            comma_phase_continue_step_observer.simps)
    next
      case True
      have step_action:
        "comma_phase_program_step_at program phase shift =
          comma_phase_program_step_of_action
            (comma_source_continuation_transport shift
              (comma_phase_program_operator_nf program 0))"
        using True Comma_Near_Residual_Program
        by (simp only: comma_phase_continue_near_residual_step_action)
      have goto_bounds:
        "\<And>child child_shift. comma_phase_program_step_at program phase shift =
          Comma_Program_Goto child child_shift \<Longrightarrow>
            f<comma_phase_program_sector child \<and>
            comma_phase_program_sector child\<le>9"
      proof -
        fix child child_shift
        assume goto: "comma_phase_program_step_at program phase shift =
          Comma_Program_Goto child child_shift"
        have bounds:
          "comma_phase_program_sector program <
            comma_phase_program_sector child \<and>
           comma_phase_program_sector child\<le>9"
          by (rule comma_phase_program_step_goto_sector_bounds[OF goto])
        show "f<comma_phase_program_sector child \<and>
            comma_phase_program_sector child\<le>9"
          using bounds Comma_Near_Residual_Program by simp
      qed
      have observer_exact:
        "comma_phase_continue_action_observer phase f shift
            (comma_phase_program_operator_nf program 0) target =
          comma_phase_continue_step_observer phase target
            (comma_phase_program_step_at program phase shift)"
        by (rule comma_phase_continue_action_observer_step_exact
          [OF step_action goto_bounds])
      show ?thesis
        using program_IH observer_exact Comma_Near_Residual_Program True
        by (simp add: comma_phase_continue_compile_job.simps(1)
            comma_phase_continue_compile_job_observer.simps)
    qed
  next
    case (Comma_Near_Boundary_Program f)
    then show ?thesis
    proof (cases "comma_phase_program_structurally_admitted program")
      case False
      then show ?thesis
        using False Comma_Near_Boundary_Program
        by (simp only: comma_phase_continue_compile_job.simps(1) if_False
            comma_crt_eval.simps(1)
            comma_phase_continue_compile_job_observer.simps
            comma_phase_continue_false_columns_def
            comma_phase_program_step_at_def
            comma_phase_continue_step_observer.simps)
    next
      case True
      have step_action:
        "comma_phase_program_step_at program phase shift =
          comma_phase_program_step_of_action
            (comma_source_continuation_transport shift
              (comma_phase_program_operator_nf program 0))"
        using True Comma_Near_Boundary_Program
        by (simp only: comma_phase_continue_near_boundary_step_action)
      have goto_bounds:
        "\<And>child child_shift. comma_phase_program_step_at program phase shift =
          Comma_Program_Goto child child_shift \<Longrightarrow>
            f<comma_phase_program_sector child \<and>
            comma_phase_program_sector child\<le>9"
      proof -
        fix child child_shift
        assume goto: "comma_phase_program_step_at program phase shift =
          Comma_Program_Goto child child_shift"
        have bounds:
          "comma_phase_program_sector program <
            comma_phase_program_sector child \<and>
           comma_phase_program_sector child\<le>9"
          by (rule comma_phase_program_step_goto_sector_bounds[OF goto])
        show "f<comma_phase_program_sector child \<and>
            comma_phase_program_sector child\<le>9"
          using bounds Comma_Near_Boundary_Program by simp
      qed
      have observer_exact:
        "comma_phase_continue_action_observer phase f shift
            (comma_phase_program_operator_nf program 0) target =
          comma_phase_continue_step_observer phase target
            (comma_phase_program_step_at program phase shift)"
        by (rule comma_phase_continue_action_observer_step_exact
          [OF step_action goto_bounds])
      show ?thesis
        using program_IH observer_exact Comma_Near_Boundary_Program True
        by (simp add: comma_phase_continue_compile_job.simps(1)
            comma_phase_continue_compile_job_observer.simps)
    qed
  qed
next
  case (2 f residue core)
  then show ?case
    by (simp add: comma_phase_continue_compile_job.simps(2)
        comma_phase_continue_compile_job_observer.simps
        comma_phase_continue_false_columns_def)
next
  case (3 f residue core wanted remaining)
  note tail_IH = "3.IH"(1)
  note action_IH = "3.IH"(2)
  let ?guard = "comma_core_value_guard core wanted"
  let ?rest_job = "Comma_Continue_Core_Values_Job f residue core remaining"
  let ?rest = "comma_phase_continue_compile_job ?rest_job"
  let ?action =
    "comma_phase_program_entry_core_value_action f residue core wanted"
  let ?action_job = "Comma_Continue_Action_Job f ?action"
  have tail_exact:
    "comma_crt_eval phase (?rest shift target) =
      comma_phase_continue_compile_job_observer phase ?rest_job shift target"
    using tail_IH[of ?guard phase shift target] by simp
  have action_exact:
    "comma_crt_supported ?guard \<Longrightarrow>
      comma_crt_eval phase
        (comma_phase_continue_compile_job ?action_job shift target) =
      comma_phase_continue_compile_job_observer phase ?action_job shift target"
    using action_IH[of ?guard ?rest phase shift target] by simp
  have guard_admitted: "comma_crt_admitted 0 ?guard"
    by (rule comma_core_value_guard_admitted)
  have shifted_guard_admitted:
    "comma_crt_admitted 0 (comma_crt_shift shift ?guard)"
    by (rule comma_crt_shift_admitted[OF guard_admitted])
  have action_admitted:
    "comma_crt_admitted 0
      (comma_phase_continue_compile_job ?action_job shift target)"
    using comma_phase_continue_compile_job_admitted[of ?action_job]
    by blast
  have rest_admitted:
    "comma_crt_admitted 0 (?rest shift target)"
    using comma_phase_continue_compile_job_admitted[of ?rest_job]
    by blast
  have shifted_guard_eval:
    "comma_crt_eval phase (comma_crt_shift shift ?guard) =
      comma_crt_eval (phase+shift) ?guard"
    by (rule comma_crt_shift_refines[OF guard_admitted])
  show ?case
  proof (cases "comma_crt_supported ?guard")
      case False
      have no_guard_eval:
        "\<not> comma_crt_eval (phase+shift) ?guard"
        by (rule comma_core_value_guard_unsupported_no_eval[OF False])
      show ?thesis
        using False no_guard_eval tail_exact
        by (simp only: comma_phase_continue_compile_job.simps(3)
            comma_phase_continue_compile_job_observer.simps
            Let_def if_False list_ex_Nil_iff list_ex_Cons_iff
            HOL.simp_thms)
    next
      case True
      have selected_action_exact:
        "comma_crt_eval phase
            (comma_phase_continue_compile_job ?action_job shift target) =
          comma_phase_continue_compile_job_observer phase ?action_job shift target"
        using action_exact True by blast
      have inner_admitted:
        "comma_crt_admitted 0
          (comma_crt_apply Comma_CRT_And
            (comma_crt_shift shift ?guard)
            (comma_phase_continue_compile_job ?action_job shift target))"
        by (rule comma_crt_apply_admitted[OF shifted_guard_admitted
          action_admitted])
      have inner_eval:
        "comma_crt_eval phase
            (comma_crt_apply Comma_CRT_And
              (comma_crt_shift shift ?guard)
              (comma_phase_continue_compile_job ?action_job shift target)) =
          (comma_crt_eval (phase+shift) ?guard \<and>
            comma_phase_continue_compile_job_observer phase ?action_job
              shift target)"
        using comma_crt_apply_refines_boolean[OF shifted_guard_admitted
            action_admitted, where operation=Comma_CRT_And]
          shifted_guard_eval selected_action_exact
        by (simp add: comma_crt_boolean_value_def)
      have outer_admitted:
        "comma_crt_admitted 0
          (comma_crt_apply Comma_CRT_Or
            (comma_crt_apply Comma_CRT_And
              (comma_crt_shift shift ?guard)
              (comma_phase_continue_compile_job ?action_job shift target))
            (?rest shift target))"
        by (rule comma_crt_apply_admitted[OF inner_admitted rest_admitted])
      have outer_eval:
        "comma_crt_eval phase
            (comma_crt_apply Comma_CRT_Or
              (comma_crt_apply Comma_CRT_And
                (comma_crt_shift shift ?guard)
                (comma_phase_continue_compile_job ?action_job shift target))
              (?rest shift target)) =
          ((comma_crt_eval (phase+shift) ?guard \<and>
              comma_phase_continue_compile_job_observer phase ?action_job
                shift target) \<or>
            comma_phase_continue_compile_job_observer phase ?rest_job
              shift target)"
        using comma_crt_apply_refines_boolean[OF inner_admitted rest_admitted,
            where operation=Comma_CRT_Or]
          inner_eval tail_exact
        by (simp add: comma_crt_boolean_value_def)
      show ?thesis
        using outer_eval True
        by (simp only: comma_phase_continue_compile_job.simps(3)
            comma_phase_continue_compile_job_observer.simps
            Let_def if_True comma_phase_continue_columns_or_def
            comma_phase_continue_columns_and_def
            list_ex_Nil_iff list_ex_Cons_iff HOL.simp_thms)
  qed
next
  case (4 parent action)
  then show ?case
    by (cases action)
      (auto simp: comma_phase_continue_compile_job.simps(4)
        comma_phase_continue_false_columns_def
        comma_phase_continue_compile_job_observer.simps
        comma_phase_continue_action_observer_def
        comma_phase_continue_exit_target_exact
        comma_semantic_phase_program_continue_guard_step
        comma_phase_continue_compile_job_admitted
        split: option.splits if_splits)
qed

ML \<open>
  val published = @{thms
    comma_core_value_guard_unsupported_no_eval
    comma_phase_continue_compile_job_exact}
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "program Continue guard exactness" published
\<close>

end
