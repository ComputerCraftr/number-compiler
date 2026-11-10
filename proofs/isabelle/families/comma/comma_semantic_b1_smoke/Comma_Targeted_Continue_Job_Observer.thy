theory Comma_Targeted_Continue_Job_Observer
  imports Comma_Semantic_B1.Comma_Targeted_Continue_Observer_Refinement
begin

text \<open>
Fuse a demanded suffix observer through one source-free Continue job.  Unlike
the source/target column family, this result is one Boolean CRT column.  The
internal shift records a within-round seam; the external clock shifts only
the guards, while the suffix observer is queried at the next temporal clock.
The corresponding 46-target column union below is a semantic specification
only.  Production normalization consumes the job equations and does not
construct that union or the function-valued compiler result.
\<close>

type_synonym comma_continue_job_observer =
  "comma_continue_observer \<Rightarrow> comma_phase_continue_job \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> comma_crt_column"

definition comma_continue_job_exit_observer ::
    "comma_continue_observer \<Rightarrow> comma_finite_position \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> comma_crt_column" where
  "comma_continue_job_exit_observer observer source shift clock =
    (case comma_shift_position shift source of
       Comma_Entry f delta x \<Rightarrow>
         if comma_decade_root_admitted (Comma_Entry f delta x) \<and>
            delta mod 924=1
         then observer (comma_offset_orbit x) (Suc clock)
         else Comma_CRT_Bool False
     | _ \<Rightarrow> Comma_CRT_Bool False)"

function (sequential) comma_continue_job_observe ::
    comma_continue_job_observer where
  "comma_continue_job_observe observer
      (Comma_Continue_Program_Job program) shift clock =
    (if comma_phase_program_structurally_admitted program then
       (case program of
          Comma_Entry_Core_Program f d residue core \<Rightarrow>
            comma_continue_job_observe observer
              (Comma_Continue_Core_Values_Job f residue core
                [0..<comma_phase_core_modulus core]) shift clock
        | Comma_Near_Residual_Program f d residual \<Rightarrow>
            comma_continue_job_observe observer
              (Comma_Continue_Action_Job f
                (comma_phase_program_operator_nf program 0)) shift clock
        | Comma_Near_Boundary_Program f \<Rightarrow>
            comma_continue_job_observe observer
              (Comma_Continue_Action_Job f
                (comma_phase_program_operator_nf program 0)) shift clock)
     else Comma_CRT_Bool False)"
| "comma_continue_job_observe observer
      (Comma_Continue_Core_Values_Job f residue core []) shift clock =
    Comma_CRT_Bool False"
| "comma_continue_job_observe observer
      (Comma_Continue_Core_Values_Job f residue core (wanted#remaining))
      shift clock =
    (let guard=comma_core_value_guard core wanted;
         rest=comma_continue_job_observe observer
           (Comma_Continue_Core_Values_Job f residue core remaining) shift clock
     in if comma_crt_supported guard then
          comma_crt_apply Comma_CRT_Or
            (comma_crt_apply Comma_CRT_And
              (comma_crt_shift (clock+shift) guard)
              (comma_continue_job_observe observer
                (Comma_Continue_Action_Job f
                  (comma_phase_program_entry_core_value_action
                    f residue core wanted)) shift clock))
            rest
        else rest)"
| "comma_continue_job_observe observer
      (Comma_Continue_Action_Job parent action) shift clock =
    (case action of
       Comma_Continuation_Goto source delta \<Rightarrow>
         (case comma_semantic_port_program_of_source source of
            Some child \<Rightarrow>
              if parent < comma_phase_program_sector child \<and>
                 comma_phase_program_sector child \<le> 9
              then comma_continue_job_observe observer
                (Comma_Continue_Program_Job child) (shift+delta) clock
              else Comma_CRT_Bool False
          | None \<Rightarrow> Comma_CRT_Bool False)
     | Comma_Continuation_Exit source delta \<Rightarrow>
         comma_continue_job_exit_observer observer source
           (shift+delta) clock
     | _ \<Rightarrow> Comma_CRT_Bool False)"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(observer,job,shift,clock).
      comma_phase_continue_job_measure job)")
    (auto intro: comma_phase_continue_program_entry_decreases[simplified in_measure]
      comma_phase_continue_program_action_decreases
      comma_phase_continue_tail_decreases
      comma_phase_continue_core_action_decreases
      comma_phase_continue_goto_decreases)

text \<open>Keep the recursive equations out of generic simplification.  Each
normalization step must select one checked job equation and retain its child
certificate instead of recursively expanding the entire descendant tree.\<close>
declare comma_continue_job_observe.simps [simp del]

lemma comma_continue_job_exit_observer_exact:
  shows "comma_crt_eval phase
      (comma_continue_job_exit_observer observer source shift clock) =
    (\<exists>target<46. comma_phase_continue_exit_target target source shift \<and>
      comma_crt_eval phase (observer target (Suc clock)))"
proof (cases "comma_shift_position shift source")
  case (Comma_Entry f delta x)
  have target_bound: "comma_offset_orbit x<46"
    by (rule comma_offset_orbit_bound)
  show ?thesis
    using Comma_Entry target_bound
    by (auto simp: comma_continue_job_exit_observer_def
        comma_phase_continue_exit_target_def)
qed (simp_all add: comma_continue_job_exit_observer_def
    comma_phase_continue_exit_target_def)

lemma comma_continue_job_exit_observer_admitted:
  assumes observer: "comma_continue_observer_admitted observer"
  shows "comma_crt_admitted 0
    (comma_continue_job_exit_observer observer source shift clock)"
proof (cases "comma_shift_position shift source")
  case (Comma_Entry f delta x)
  have target: "comma_offset_orbit x<46"
    by (rule comma_offset_orbit_bound)
  have suffix: "comma_crt_admitted 0
      (observer (comma_offset_orbit x) (Suc clock))"
    using observer target
    by (auto simp: comma_continue_observer_admitted_def)
  show ?thesis
    using Comma_Entry suffix
    by (simp add: comma_continue_job_exit_observer_def)
qed (simp_all add: comma_continue_job_exit_observer_def)

lemma comma_continue_job_observe_admitted:
  assumes observer: "comma_continue_observer_admitted observer"
  shows "comma_crt_admitted 0
    (comma_continue_job_observe observer job shift clock)"
  using observer
proof (induction observer job shift clock rule: comma_continue_job_observe.induct)
  case (1 observer program shift clock)
  then show ?case
    by (cases program)
      (auto simp: comma_continue_job_observe.simps(1)
        intro: comma_crt_apply_admitted comma_crt_shift_admitted
          comma_core_value_guard_admitted
          comma_continue_job_exit_observer_admitted
        split: if_splits option.splits)
next
  case (2 observer f residue core shift clock)
  show ?case
    by (simp only: comma_continue_job_observe.simps(2)
      comma_crt_admitted.simps)
next
  case (3 observer f residue core wanted remaining shift clock)
  note tail_IH = "3.IH"(1)
  note action_IH = "3.IH"(2)
  let ?guard = "comma_core_value_guard core wanted"
  let ?rest_job = "Comma_Continue_Core_Values_Job f residue core remaining"
  let ?action_job = "Comma_Continue_Action_Job f
    (comma_phase_program_entry_core_value_action f residue core wanted)"
  let ?rest = "comma_continue_job_observe observer ?rest_job shift clock"
  let ?action = "comma_continue_job_observe observer ?action_job shift clock"
  have rest_admitted:
    "comma_crt_admitted 0 ?rest"
    using tail_IH[of ?guard] "3.prems" by simp
  have guard_admitted: "comma_crt_admitted 0 ?guard"
    by (rule comma_core_value_guard_admitted)
  have shifted_guard_admitted:
    "comma_crt_admitted 0 (comma_crt_shift (clock+shift) ?guard)"
    by (rule comma_crt_shift_admitted[OF guard_admitted])
  show ?case
  proof (cases "comma_crt_supported ?guard")
    case True
    have action_admitted_if_supported:
      "comma_crt_supported ?guard \<Longrightarrow>
        comma_crt_admitted 0 ?action"
      using action_IH[of ?guard ?rest] "3.prems" by simp
    have action_admitted: "comma_crt_admitted 0 ?action"
      using action_admitted_if_supported True by blast
    have inner_admitted:
      "comma_crt_admitted 0
        (comma_crt_apply Comma_CRT_And
          (comma_crt_shift (clock+shift) ?guard)
          ?action)"
      by (rule comma_crt_apply_admitted[OF shifted_guard_admitted action_admitted])
    have outer_admitted:
      "comma_crt_admitted 0
        (comma_crt_apply Comma_CRT_Or
          (comma_crt_apply Comma_CRT_And
            (comma_crt_shift (clock+shift) ?guard)
            ?action)
          ?rest)"
      by (rule comma_crt_apply_admitted[OF inner_admitted rest_admitted])
    show ?thesis using True outer_admitted
      by (simp only: comma_continue_job_observe.simps(3) Let_def if_True)
  next
    case False
    then show ?thesis using rest_admitted
      by (simp only: comma_continue_job_observe.simps(3) Let_def if_False)
  qed
next
  case (4 observer parent action shift clock)
  then show ?case
    by (cases action)
      (auto simp: comma_continue_job_observe.simps(4)
        intro: comma_crt_apply_admitted comma_crt_shift_admitted
          comma_continue_job_exit_observer_admitted
        split: option.splits if_splits)
qed

lemma comma_continue_job_observe_columns_exact:
  assumes observer: "comma_continue_observer_admitted observer"
  shows "comma_crt_eval phase
      (comma_continue_job_observe observer job shift clock) =
    (\<exists>target<46.
      comma_crt_eval (phase+clock)
        (comma_phase_continue_compile_job job shift target) \<and>
      comma_crt_eval phase (observer target (Suc clock)))"
  using observer
proof (induction observer job shift clock arbitrary: phase
    rule: comma_continue_job_observe.induct)
  case (1 observer program shift clock)
  then show ?case
    by (cases program)
      (simp_all add: comma_continue_job_observe.simps(1)
        comma_phase_continue_compile_job.simps(1)
        comma_phase_continue_false_columns_def)
next
  case (2 observer f residue core shift clock)
  then show ?case
    by (simp add: comma_continue_job_observe.simps(2)
      comma_phase_continue_compile_job.simps(2)
      comma_phase_continue_false_columns_def)
next
  case (3 observer f residue core wanted remaining shift clock)
  note tail_IH = "3.IH"(1)
  note action_IH = "3.IH"(2)
  let ?guard = "comma_core_value_guard core wanted"
  let ?tail_job = "Comma_Continue_Core_Values_Job f residue core remaining"
  let ?action_job = "Comma_Continue_Action_Job f
    (comma_phase_program_entry_core_value_action f residue core wanted)"
  let ?tail_observer = "comma_continue_job_observe observer ?tail_job shift clock"
  let ?action_observer = "comma_continue_job_observe observer ?action_job shift clock"
  let ?tail_column = "comma_phase_continue_compile_job ?tail_job shift"
  let ?action_column = "comma_phase_continue_compile_job ?action_job shift"
  have tail_exact:
    "comma_crt_eval phase ?tail_observer =
      (\<exists>target<46. comma_crt_eval (phase+clock) (?tail_column target) \<and>
        comma_crt_eval phase (observer target (Suc clock)))"
    using tail_IH[of ?guard phase] "3.prems" by simp
  have action_exact_if_supported:
    "comma_crt_supported ?guard \<Longrightarrow>
      comma_crt_eval phase ?action_observer =
        (\<exists>target<46. comma_crt_eval (phase+clock)
            (?action_column target) \<and>
          comma_crt_eval phase (observer target (Suc clock)))"
    using action_IH[of ?guard ?tail_observer phase] "3.prems" by simp
  have guard_admitted: "comma_crt_admitted 0 ?guard"
    by (rule comma_core_value_guard_admitted)
  have direct_guard_admitted:
    "comma_crt_admitted 0 (comma_crt_shift (clock+shift) ?guard)"
    by (rule comma_crt_shift_admitted[OF guard_admitted])
  have direct_action_admitted:
    "comma_crt_admitted 0 ?action_observer"
    by (rule comma_continue_job_observe_admitted[OF "3.prems"])
  have direct_tail_admitted: "comma_crt_admitted 0 ?tail_observer"
    by (rule comma_continue_job_observe_admitted[OF "3.prems"])
  have direct_inner_admitted:
    "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_And
        (comma_crt_shift (clock+shift) ?guard) ?action_observer)"
    by (rule comma_crt_apply_admitted[OF direct_guard_admitted
      direct_action_admitted])
  have direct_outer_admitted:
    "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_Or
        (comma_crt_apply Comma_CRT_And
          (comma_crt_shift (clock+shift) ?guard) ?action_observer)
        ?tail_observer)"
    by (rule comma_crt_apply_admitted[OF direct_inner_admitted
      direct_tail_admitted])
  have direct_guard_eval:
    "comma_crt_eval phase (comma_crt_shift (clock+shift) ?guard) =
      comma_crt_eval (phase+clock+shift) ?guard"
    using comma_crt_shift_refines[OF guard_admitted, of phase "clock+shift"]
    by (simp add: add.assoc)
  have direct_inner_eval:
    "comma_crt_eval phase
        (comma_crt_apply Comma_CRT_And
          (comma_crt_shift (clock+shift) ?guard) ?action_observer) =
      (comma_crt_eval (phase+clock+shift) ?guard \<and>
        comma_crt_eval phase ?action_observer)"
    using comma_crt_apply_refines_boolean[
        OF direct_guard_admitted direct_action_admitted,
        where operation=Comma_CRT_And]
      direct_guard_eval
    by (simp add: comma_crt_boolean_value_def)
  have direct_outer_eval:
    "comma_crt_eval phase
        (comma_crt_apply Comma_CRT_Or
          (comma_crt_apply Comma_CRT_And
            (comma_crt_shift (clock+shift) ?guard) ?action_observer)
          ?tail_observer) =
      ((comma_crt_eval (phase+clock+shift) ?guard \<and>
          comma_crt_eval phase ?action_observer) \<or>
        comma_crt_eval phase ?tail_observer)"
    using comma_crt_apply_refines_boolean[
        OF direct_inner_admitted direct_tail_admitted,
        where operation=Comma_CRT_Or]
      direct_inner_eval
    by (simp add: comma_crt_boolean_value_def)
  have compile_guard_admitted:
    "comma_crt_admitted 0 (comma_crt_shift shift ?guard)"
    by (rule comma_crt_shift_admitted[OF guard_admitted])
  have compile_action_admitted:
    "comma_crt_admitted 0 (?action_column target)" for target
    using comma_phase_continue_compile_job_admitted[of ?action_job]
    by blast
  have compile_tail_admitted:
    "comma_crt_admitted 0 (?tail_column target)" for target
    using comma_phase_continue_compile_job_admitted[of ?tail_job]
    by blast
  have compile_inner_admitted:
    "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_And (comma_crt_shift shift ?guard)
        (?action_column target))" for target
    by (rule comma_crt_apply_admitted[OF compile_guard_admitted
      compile_action_admitted])
  have compile_outer_admitted:
    "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_Or
        (comma_crt_apply Comma_CRT_And (comma_crt_shift shift ?guard)
          (?action_column target)) (?tail_column target))" for target
    by (rule comma_crt_apply_admitted[OF compile_inner_admitted
      compile_tail_admitted])
  have compile_guard_eval:
    "comma_crt_eval (phase+clock) (comma_crt_shift shift ?guard) =
      comma_crt_eval (phase+clock+shift) ?guard"
    by (rule comma_crt_shift_refines[OF guard_admitted])
  have compile_inner_eval:
    "comma_crt_eval (phase+clock)
        (comma_crt_apply Comma_CRT_And (comma_crt_shift shift ?guard)
          (?action_column target)) =
      (comma_crt_eval (phase+clock+shift) ?guard \<and>
        comma_crt_eval (phase+clock) (?action_column target))" for target
    using comma_crt_apply_refines_boolean[
        OF compile_guard_admitted compile_action_admitted,
        where operation=Comma_CRT_And and phase="phase+clock"]
      compile_guard_eval
    by (simp add: comma_crt_boolean_value_def)
  have compile_outer_eval:
    "comma_crt_eval (phase+clock)
        (comma_crt_apply Comma_CRT_Or
          (comma_crt_apply Comma_CRT_And (comma_crt_shift shift ?guard)
            (?action_column target)) (?tail_column target)) =
      ((comma_crt_eval (phase+clock+shift) ?guard \<and>
          comma_crt_eval (phase+clock) (?action_column target)) \<or>
        comma_crt_eval (phase+clock) (?tail_column target))" for target
    using comma_crt_apply_refines_boolean[
        OF compile_inner_admitted compile_tail_admitted,
        where operation=Comma_CRT_Or and phase="phase+clock"]
      compile_inner_eval
    by (simp add: comma_crt_boolean_value_def)
  show ?case
  proof (cases "comma_crt_supported ?guard")
    case True
    have action_exact:
      "comma_crt_eval phase ?action_observer =
        (\<exists>target<46. comma_crt_eval (phase+clock) (?action_column target) \<and>
          comma_crt_eval phase (observer target (Suc clock)))"
      by (rule action_exact_if_supported[OF True])
    have observed:
      "comma_crt_eval phase
          (comma_continue_job_observe observer
            (Comma_Continue_Core_Values_Job f residue core (wanted#remaining))
            shift clock) =
        ((comma_crt_eval (phase+clock+shift) ?guard \<and>
            (\<exists>target<46. comma_crt_eval (phase+clock)
                (?action_column target) \<and>
              comma_crt_eval phase (observer target (Suc clock)))) \<or>
          (\<exists>target<46. comma_crt_eval (phase+clock)
              (?tail_column target) \<and>
            comma_crt_eval phase (observer target (Suc clock))))"
      using True direct_outer_eval action_exact tail_exact
      by (simp only: comma_continue_job_observe.simps(3) Let_def if_True)
    have compiled:
      "comma_crt_eval (phase+clock)
          (comma_phase_continue_compile_job
            (Comma_Continue_Core_Values_Job f residue core (wanted#remaining))
            shift target) =
        ((comma_crt_eval (phase+clock+shift) ?guard \<and>
            comma_crt_eval (phase+clock) (?action_column target)) \<or>
          comma_crt_eval (phase+clock) (?tail_column target))" for target
      using True compile_outer_eval
      by (simp only: comma_phase_continue_compile_job.simps(3) Let_def if_True
          comma_phase_continue_columns_or_def comma_phase_continue_columns_and_def)
    show ?thesis using observed compiled by auto
  next
    case False
    have observed:
      "comma_crt_eval phase
          (comma_continue_job_observe observer
            (Comma_Continue_Core_Values_Job f residue core (wanted#remaining))
            shift clock) =
        (\<exists>target<46. comma_crt_eval (phase+clock) (?tail_column target) \<and>
          comma_crt_eval phase (observer target (Suc clock)))"
      using False tail_exact
      by (simp only: comma_continue_job_observe.simps(3) Let_def if_False)
    have compiled:
      "comma_crt_eval (phase+clock)
          (comma_phase_continue_compile_job
            (Comma_Continue_Core_Values_Job f residue core (wanted#remaining))
            shift target) =
        comma_crt_eval (phase+clock) (?tail_column target)" for target
      using False by (simp only: comma_phase_continue_compile_job.simps(3)
          Let_def if_False)
    show ?thesis using observed compiled by auto
  qed
next
  case (4 observer parent action shift clock)
  then show ?case
    using "4.IH" "4.prems"
    by (cases action)
      (auto simp: comma_continue_job_observe.simps(4)
        comma_phase_continue_compile_job.simps(4)
        comma_phase_continue_false_columns_def
        comma_phase_continue_exit_target_exact
        comma_phase_continue_exit_target_def
        comma_continue_job_exit_observer_exact
        comma_continue_observer_admitted_def
        split: option.splits if_splits comma_finite_position.splits)
qed

lemma comma_continue_job_observe_exact:
  assumes observer: "comma_continue_observer_admitted observer"
  shows "comma_crt_eval phase
      (comma_continue_job_observe observer job shift clock) =
    (\<exists>target<46.
      comma_phase_continue_compile_job_observer (phase+clock) job shift target \<and>
      comma_crt_eval phase (observer target (Suc clock)))"
proof -
  have columns:
    "comma_crt_eval phase
        (comma_continue_job_observe observer job shift clock) =
      (\<exists>target<46.
        comma_crt_eval (phase+clock)
          (comma_phase_continue_compile_job job shift target) \<and>
        comma_crt_eval phase (observer target (Suc clock)))"
    by (rule comma_continue_job_observe_columns_exact[OF observer])
  show ?thesis
    using columns comma_phase_continue_compile_job_exact[of "phase+clock" job shift]
    by auto
qed

lemma comma_continue_job_observe_operator_step_eval:
  assumes observer: "comma_continue_observer_admitted observer"
    and phase: "phase<924"
  shows "comma_crt_eval phase
      (comma_continue_job_observe observer
        (Comma_Continue_Program_Job program) 0 clock) =
    comma_crt_eval phase (comma_continue_operator_step observer program clock)"
proof -
  have job_exact:
    "comma_crt_eval phase
        (comma_continue_job_observe observer
          (Comma_Continue_Program_Job program) 0 clock) =
      (\<exists>target<46.
        comma_crt_eval (phase+clock)
          (comma_phase_continue_compile_job
            (Comma_Continue_Program_Job program) 0 target) \<and>
        comma_crt_eval phase (observer target (Suc clock)))"
    by (rule comma_continue_job_observe_columns_exact[OF observer])
  have operator_exact:
    "comma_crt_eval phase (comma_continue_operator_step observer program clock) =
      (\<exists>target<46.
        comma_crt_eval phase
          (let edge=comma_phase_continue_compile_job
              (Comma_Continue_Program_Job program) 0 target
           in if comma_crt_supported edge then
                comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
                  (observer target (Suc clock))
              else Comma_CRT_Bool False))"
    by (rule comma_continue_operator_step_pointwise[OF observer phase])
  have row_exact:
    "comma_crt_eval phase
        (if comma_crt_supported edge then
          comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
            (observer target (Suc clock))
         else Comma_CRT_Bool False) =
      (comma_crt_eval (phase+clock) edge \<and>
        comma_crt_eval phase (observer target (Suc clock)))"
    if target: "target<46"
      and edge:
        "edge=comma_phase_continue_compile_job
          (Comma_Continue_Program_Job program) 0 target"
    for target edge
  proof -
    have edge_admitted: "comma_crt_admitted 0 edge"
      using edge comma_phase_continue_compile_job_admitted[of
          "Comma_Continue_Program_Job program"]
      by auto
    have shifted_admitted: "comma_crt_admitted 0 (comma_crt_shift clock edge)"
      by (rule comma_crt_shift_admitted[OF edge_admitted])
    have observer_admitted:
      "comma_crt_admitted 0 (observer target (Suc clock))"
      using observer target
      by (auto simp: comma_continue_observer_admitted_def)
    have shifted_exact:
      "comma_crt_eval phase (comma_crt_shift clock edge) =
        comma_crt_eval (phase+clock) edge"
      by (rule comma_crt_shift_refines[OF edge_admitted])
    have applied:
      "comma_crt_eval phase
          (comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
            (observer target (Suc clock))) =
        (comma_crt_eval phase (comma_crt_shift clock edge) \<and>
          comma_crt_eval phase (observer target (Suc clock)))"
      using comma_crt_apply_refines_boolean[
          OF shifted_admitted observer_admitted,
          where operation=Comma_CRT_And]
      by (simp add: comma_crt_boolean_value_def)
    show ?thesis
    proof (cases "comma_crt_supported edge")
      case True
      then show ?thesis using applied shifted_exact by simp
    next
      case False
      have no_eval: "\<not> comma_crt_eval (phase+clock) edge"
      proof
        assume evaluates: "comma_crt_eval (phase+clock) edge"
        have "comma_crt_supported edge"
          by (rule comma_crt_eval_supported[OF edge_admitted evaluates])
        with False show False by contradiction
      qed
      show ?thesis using False no_eval by simp
    qed
  qed
  have row_exact_at:
    "comma_crt_eval phase
        (let edge=comma_phase_continue_compile_job
            (Comma_Continue_Program_Job program) 0 target
         in
          if comma_crt_supported edge then
            comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
              (observer target (Suc clock))
          else Comma_CRT_Bool False) =
      (comma_crt_eval (phase+clock)
          (comma_phase_continue_compile_job
            (Comma_Continue_Program_Job program) 0 target) \<and>
        comma_crt_eval phase (observer target (Suc clock)))"
    if target_bound: "target<46" for target
    using row_exact[of target
        "comma_phase_continue_compile_job
          (Comma_Continue_Program_Job program) 0 target"]
      target_bound
    by (simp add: Let_def)
  have rows_equal:
    "(\<exists>target<46. comma_crt_eval phase
        (let edge=comma_phase_continue_compile_job
            (Comma_Continue_Program_Job program) 0 target
         in if comma_crt_supported edge then
              comma_crt_apply Comma_CRT_And (comma_crt_shift clock edge)
                (observer target (Suc clock))
            else Comma_CRT_Bool False)) =
      (\<exists>target<46. comma_crt_eval (phase+clock)
          (comma_phase_continue_compile_job
            (Comma_Continue_Program_Job program) 0 target) \<and>
        comma_crt_eval phase (observer target (Suc clock)))"
    using row_exact_at by auto
  have step_rows:
    "comma_crt_eval phase (comma_continue_operator_step observer program clock) =
      (\<exists>target<46. comma_crt_eval (phase+clock)
          (comma_phase_continue_compile_job
            (Comma_Continue_Program_Job program) 0 target) \<and>
        comma_crt_eval phase (observer target (Suc clock)))"
    using operator_exact rows_equal by simp
  show ?thesis using job_exact step_rows by simp
qed

lemma comma_continue_job_observe_operator_step_equiv:
  assumes observer: "comma_continue_observer_admitted observer"
  shows "comma_crt_equiv_check
    (comma_continue_operator_step observer program clock)
    (comma_continue_job_observe observer
      (Comma_Continue_Program_Job program) 0 clock)"
proof (rule comma_crt_equiv_check_complete)
  show "comma_crt_admitted 0
      (comma_continue_operator_step observer program clock)"
    by (rule comma_continue_operator_step_admitted[OF observer])
  show "comma_crt_admitted 0
      (comma_continue_job_observe observer
        (Comma_Continue_Program_Job program) 0 clock)"
    by (rule comma_continue_job_observe_admitted[OF observer])
  show "comma_crt_set (comma_continue_operator_step observer program clock) =
      comma_crt_set (comma_continue_job_observe observer
        (Comma_Continue_Program_Job program) 0 clock)"
    using comma_continue_job_observe_operator_step_eval[OF observer, of _ program clock]
    by (auto simp: comma_crt_set_def)
qed

ML \<open>
  val published = @{thms
    comma_continue_job_exit_observer_def
    comma_continue_job_observe.simps
    comma_continue_job_exit_observer_exact
    comma_continue_job_exit_observer_admitted
    comma_continue_job_observe_admitted
    comma_continue_job_observe_columns_exact
    comma_continue_job_observe_exact
    comma_continue_job_observe_operator_step_eval
    comma_continue_job_observe_operator_step_equiv}
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "fused Continue job observer" published
\<close>

end
