theory Comma_Program_Continue_Guard
  imports Comma_Continue_Image_Bridge Comma_CRT_Support
begin

text \<open>
Compile only the Continue observer of a normalized source program.  The
result is a target-indexed family of Boolean CRT columns: a terminal crossing
publishes its one destination class, a Goto reuses the child family, and an
Entry splits on the shared cyclotomic core-value guards.  No complete B1
action row, occurrence identifier, or 924-phase mask is constructed here.
\<close>

type_synonym comma_phase_continue_columns =
  "nat \<Rightarrow> nat \<Rightarrow> comma_crt_column"

datatype comma_phase_continue_job =
    Comma_Continue_Program_Job comma_semantic_port_program
  | Comma_Continue_Core_Values_Job nat nat comma_phase_core_id "nat list"
  | Comma_Continue_Action_Job nat comma_source_continuation_action

fun comma_phase_continue_job_sector ::
    "comma_phase_continue_job \<Rightarrow> nat"
where
  "comma_phase_continue_job_sector (Comma_Continue_Program_Job program) =
    comma_phase_program_sector program"
| "comma_phase_continue_job_sector
      (Comma_Continue_Core_Values_Job f residue core values) = f"
| "comma_phase_continue_job_sector
      (Comma_Continue_Action_Job f action) = f"

fun comma_phase_continue_job_stage ::
    "comma_phase_continue_job \<Rightarrow> nat"
where
  "comma_phase_continue_job_stage (Comma_Continue_Program_Job program) = 2"
| "comma_phase_continue_job_stage
      (Comma_Continue_Core_Values_Job f residue core values) = 1"
| "comma_phase_continue_job_stage (Comma_Continue_Action_Job f action) = 0"

fun comma_phase_continue_job_tail ::
    "comma_phase_continue_job \<Rightarrow> nat"
where
  "comma_phase_continue_job_tail
      (Comma_Continue_Core_Values_Job f residue core values) =
    length values"
| "comma_phase_continue_job_tail _ = 0"

definition comma_phase_continue_job_measure ::
    "comma_phase_continue_job \<Rightarrow> nat" where
  "comma_phase_continue_job_measure job =
    (let sector=comma_phase_continue_job_sector job;
         rank=(if sector\<le>9 then 9-sector else 0)
     in 100*rank + 30*comma_phase_continue_job_stage job +
        comma_phase_continue_job_tail job)"

definition comma_phase_continue_false_columns :: comma_phase_continue_columns where
  "comma_phase_continue_false_columns = (\<lambda>shift target. Comma_CRT_Bool False)"

definition comma_phase_continue_columns_or ::
    "comma_phase_continue_columns \<Rightarrow> comma_phase_continue_columns \<Rightarrow>
      comma_phase_continue_columns" where
  "comma_phase_continue_columns_or left right =
    (\<lambda>shift target. comma_crt_apply Comma_CRT_Or
      (left shift target) (right shift target))"

definition comma_phase_continue_columns_and ::
    "comma_crt_column \<Rightarrow> comma_phase_continue_columns \<Rightarrow>
      comma_phase_continue_columns" where
  "comma_phase_continue_columns_and gate columns =
    (\<lambda>shift target. comma_crt_apply Comma_CRT_And
      (comma_crt_shift shift gate) (columns shift target))"

definition comma_phase_program_entry_core_value_action ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_phase_core_id \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action" where
  "comma_phase_program_entry_core_value_action f residue core wanted =
    (let key=comma_decisive_entry_clock_key_from_core_residue f residue
         (comma_phase_core_modulus core) wanted
     in case comma_entry_port_refined_locator f (fst key) (snd key) of
       Some (active,residual,h) \<Rightarrow>
         comma_semantic_b1_near_control_port_action f 0 h
     | None \<Rightarrow> Comma_Continuation_Invalid)"

definition comma_phase_continue_exit_target ::
    "nat \<Rightarrow> comma_finite_position \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_phase_continue_exit_target target source shift =
    (case comma_shift_position shift source of
       Comma_Entry f delta x \<Rightarrow>
         comma_decade_root_admitted (Comma_Entry f delta x) \<and>
         delta mod 924=1 \<and> comma_offset_orbit x=target
     | _ \<Rightarrow> False)"

lemma comma_phase_continue_exit_target_partition:
  assumes orbit: "comma_offset_orbit x = cid"
  shows "comma_phase_continue_exit_target target (Comma_Entry f delta x) shift =
    (target=cid \<and>
      comma_phase_continue_exit_target cid (Comma_Entry f delta x) shift)"
  by (auto simp: comma_phase_continue_exit_target_def
      comma_shift_position.simps orbit)

lemma comma_phase_continue_exit_target_exact:
  "comma_phase_continue_exit_target target source shift =
    comma_phase_program_continue_observer target phase
      (Comma_Round_Cross (comma_shift_position shift source))"
proof -
  have phase_delta:
    "(phase+delta) mod 924=(Suc phase) mod 924 \<longleftrightarrow>
      delta mod 924=1" for delta :: nat
  proof -
    have cancel:
      "[phase+delta=phase+1] (mod 924) \<longleftrightarrow>
        [delta=1] (mod 924)"
      by (rule cong_add_lcancel_nat)
    show ?thesis using cancel by (simp add: cong_def)
  qed
  show ?thesis
    by (cases "comma_shift_position shift source")
      (auto simp: comma_phase_continue_exit_target_def
        comma_phase_program_continue_observer_def phase_delta
        split: comma_finite_position.splits)
qed

definition comma_phase_continue_action_observer ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_phase_continue_action_observer phase parent shift action target =
    (case action of
       Comma_Continuation_Goto source delta \<Rightarrow>
         (case comma_semantic_port_program_of_source source of
            Some child \<Rightarrow>
              parent < comma_phase_program_sector child \<and>
              comma_phase_program_sector child \<le> 9 \<and>
              comma_semantic_phase_program_continue_guard phase child
                (shift+delta) target
          | None \<Rightarrow> False)
     | Comma_Continuation_Exit source delta \<Rightarrow>
         comma_phase_continue_exit_target target source (shift+delta)
     | _ \<Rightarrow> False)"

fun comma_phase_continue_step_observer ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_phase_program_step \<Rightarrow> bool" where
  "comma_phase_continue_step_observer phase target
      (Comma_Program_Goto child shift) =
    comma_semantic_phase_program_continue_guard phase child shift target"
| "comma_phase_continue_step_observer phase target
      (Comma_Program_Exit position shift) =
    comma_phase_program_continue_observer target phase
      (Comma_Round_Cross (comma_shift_position shift position))"
| "comma_phase_continue_step_observer phase target
      (Comma_Program_Fork a shift) = False"
| "comma_phase_continue_step_observer phase target
      (Comma_Program_Landmine shift) = False"
| "comma_phase_continue_step_observer phase target
      Comma_Program_Invalid = False"

lemma comma_semantic_phase_program_continue_guard_step:
  "comma_semantic_phase_program_continue_guard phase program shift target =
    comma_phase_continue_step_observer phase target
      (comma_phase_program_step_at program phase shift)"
proof -
  have equation:
    "comma_semantic_phase_program_fold
        (comma_phase_program_continue_observer target) phase program shift =
      (case comma_phase_program_step_at program phase shift of
         Comma_Program_Goto child child_shift \<Rightarrow>
           comma_semantic_phase_program_fold
             (comma_phase_program_continue_observer target) phase child child_shift
       | Comma_Program_Exit position position_shift \<Rightarrow>
           comma_phase_program_continue_observer target phase
             (Comma_Round_Cross (comma_shift_position position_shift position))
       | Comma_Program_Fork a position_shift \<Rightarrow>
           comma_phase_program_continue_observer target phase
             (Comma_Round_Fork a position_shift)
       | Comma_Program_Landmine position_shift \<Rightarrow>
           comma_phase_program_continue_observer target phase
             (Comma_Round_Landmine position_shift)
       | Comma_Program_Invalid \<Rightarrow>
           comma_phase_program_continue_observer target phase Comma_Round_Invalid)"
    by (rule comma_semantic_phase_program_fold.simps)
  show ?thesis
    using equation
    by (cases "comma_phase_program_step_at program phase shift")
      (simp_all add: comma_semantic_phase_program_continue_guard_def
        comma_phase_continue_step_observer.simps
        comma_phase_program_continue_observer_def)
qed

lemma comma_semantic_port_program_sector_upper_bound:
  assumes binding:
    "comma_semantic_port_program_of_source source=Some program"
  shows "comma_phase_program_sector program\<le>9"
proof -
  have source_bound: "comma_sector_number source\<le>9"
    using binding
    by (cases source)
      (auto simp: comma_semantic_port_program_of_source_def
        comma_canonical_position_admitted_def comma_sector_entry_bound_def
        comma_source_continuation_base.simps
        split: if_splits option.splits)
  have same_sector:
    "comma_phase_program_sector program=comma_sector_number source"
    by (rule comma_semantic_port_program_sector[OF binding])
  show ?thesis using source_bound same_sector by simp
qed

lemma comma_phase_program_step_goto_sector_bounds:
  assumes step:
    "comma_phase_program_step_at program phase shift =
      Comma_Program_Goto child child_shift"
  shows "comma_phase_program_sector program <
      comma_phase_program_sector child \<and>
    comma_phase_program_sector child\<le>9"
proof -
  have structural: "comma_phase_program_structurally_admitted program"
    by (rule comma_phase_program_step_goto_structural[OF step])
  have rank_decrease:
    "9-comma_phase_program_sector child <
      9-comma_phase_program_sector program"
    by (rule comma_phase_program_step_goto_decreases_from_packet
      [OF structural step])
  have local_step:
    "comma_phase_program_step_of_action
        (comma_source_continuation_transport shift
          (comma_phase_program_operator_nf program ((phase+shift) mod 924))) =
      Comma_Program_Goto child child_shift"
    using step structural by (simp add: comma_phase_program_step_at_def)
  obtain source delta where action:
      "comma_phase_program_operator_nf program ((phase+shift) mod 924) =
        Comma_Continuation_Goto source delta"
    and binding: "comma_semantic_port_program_of_source source=Some child"
    using local_step
    by (cases "comma_phase_program_operator_nf program ((phase+shift) mod 924)")
      (auto simp: comma_phase_program_step_of_action.simps
        comma_source_continuation_transport.simps split: option.splits)
  have child_bound: "comma_phase_program_sector child\<le>9"
    by (rule comma_semantic_port_program_sector_upper_bound[OF binding])
  have parent_bound: "comma_phase_program_sector program\<le>9"
    using structural by (cases program)
      (auto simp: comma_phase_program_structurally_admitted_def Let_def)
  show ?thesis using rank_decrease child_bound parent_bound by arith
qed

lemma comma_phase_continue_action_observer_step_exact:
  assumes action_step:
    "step=comma_phase_program_step_of_action
      (comma_source_continuation_transport shift action)"
    and goto_bounds:
    "\<And>child child_shift. step=Comma_Program_Goto child child_shift \<Longrightarrow>
      parent<comma_phase_program_sector child \<and>
      comma_phase_program_sector child\<le>9"
  shows "comma_phase_continue_action_observer phase parent shift action target =
    comma_phase_continue_step_observer phase target step"
proof (cases action)
  case (Comma_Continuation_Goto source delta)
  then show ?thesis
    using action_step goto_bounds
    by (cases "comma_semantic_port_program_of_source source")
      (auto simp: comma_phase_continue_action_observer_def
        comma_phase_continue_step_observer.simps
        comma_phase_program_step_of_action.simps
        comma_source_continuation_transport.simps add.commute
        split: option.splits)
next
  case (Comma_Continuation_Exit source delta)
  then show ?thesis
    using action_step
    by (simp add: comma_phase_continue_action_observer_def
        comma_phase_continue_step_observer.simps
        comma_phase_program_step_of_action.simps
        comma_source_continuation_transport.simps
        comma_phase_continue_exit_target_exact add.commute)
next
  case (Comma_Continuation_Fork a delta)
  then show ?thesis
    using action_step
    by (simp add: comma_phase_continue_action_observer_def
        comma_phase_continue_step_observer.simps
        comma_phase_program_step_of_action.simps
        comma_source_continuation_transport.simps)
next
  case (Comma_Continuation_Landmine delta)
  then show ?thesis
    using action_step
    by (simp add: comma_phase_continue_action_observer_def
        comma_phase_continue_step_observer.simps
        comma_phase_program_step_of_action.simps
        comma_source_continuation_transport.simps)
next
  case Comma_Continuation_Invalid
  then show ?thesis
    using action_step
    by (simp add: comma_phase_continue_action_observer_def
        comma_phase_continue_step_observer.simps
        comma_phase_program_step_of_action.simps
        comma_source_continuation_transport.simps)
qed

fun comma_phase_continue_compile_job_observer ::
    "nat \<Rightarrow> comma_phase_continue_job \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_phase_continue_compile_job_observer phase
      (Comma_Continue_Program_Job program) shift target =
    comma_phase_continue_step_observer phase target
      (comma_phase_program_step_at program phase shift)"
| "comma_phase_continue_compile_job_observer phase
      (Comma_Continue_Core_Values_Job f residue core values) shift target =
    list_ex (\<lambda>wanted.
      comma_crt_eval (phase+shift) (comma_core_value_guard core wanted) \<and>
      comma_phase_continue_action_observer phase f shift
        (comma_phase_program_entry_core_value_action f residue core wanted)
        target) values"
| "comma_phase_continue_compile_job_observer phase
      (Comma_Continue_Action_Job parent action) shift target =
    comma_phase_continue_action_observer phase parent shift action target"

lemma comma_phase_continue_entry_core_values_observer_exact:
  assumes structural:
    "comma_phase_program_structurally_admitted
      (Comma_Entry_Core_Program f d residue core)"
  shows "comma_phase_continue_compile_job_observer phase
      (Comma_Continue_Core_Values_Job f residue core
        [0..<comma_phase_core_modulus core]) shift target =
    comma_phase_continue_step_observer phase target
      (comma_phase_program_step_at
        (Comma_Entry_Core_Program f d residue core) phase shift)"
proof -
  let ?program = "Comma_Entry_Core_Program f d residue core"
  let ?effective = "(phase+shift) mod 924"
  let ?modulus = "comma_phase_core_modulus core"
  let ?value =
    "comma_cyclotomic_clock_core_value
      (comma_cyclotomic_clock_of ?effective) ?modulus"
  have parameters:
    "1\<le>f" "f\<le>9" "d<10" "residue mod 10=d"
    "?modulus=comma_core_modulus (comma_finite_period_fast f d)"
    using structural
    by (auto simp: comma_phase_program_structurally_admitted_def)
  have value_bound: "?value<?modulus"
    by (rule comma_phase_core_clock_value_bound)
  have clock_period:
    "comma_cyclotomic_clock_of (phase+shift) =
      comma_cyclotomic_clock_of ?effective"
  proof -
    have d4: "(4::nat) dvd 924" by presburger
    have d3: "(3::nat) dvd 924" by presburger
    have d7: "(7::nat) dvd 924" by presburger
    have d11: "(11::nat) dvd 924" by presburger
    show ?thesis
      by (simp add: comma_cyclotomic_clock_of_def
        mod_mod_cancel[OF d4] mod_mod_cancel[OF d3]
        mod_mod_cancel[OF d7] mod_mod_cancel[OF d11])
  qed
  have guard_eval:
    "comma_crt_eval (phase+shift) (comma_core_value_guard core wanted) =
      (wanted=?value)" for wanted
    using comma_core_value_guard_eval[of "phase+shift" core wanted]
      clock_period by (simp add: eq_commute)
  have selected_guard:
    "comma_crt_eval ?effective (comma_core_value_guard core ?value)"
    using comma_core_value_guard_eval[of ?effective core ?value] by simp
  have effective_bound: "?effective<924" by simp
  have digit: "d=residue mod 10" using parameters(4) by simp
  have selected_action:
    "comma_phase_program_entry_core_value_action f residue core ?value =
      comma_phase_program_operator_nf ?program ?effective"
    using comma_entry_guard_selects_action[OF effective_bound selected_guard
        digit parameters(5)]
    by (simp add: comma_phase_program_entry_core_value_action_def)
  have branch_partition:
    "list_ex (\<lambda>wanted.
        comma_crt_eval (phase+shift) (comma_core_value_guard core wanted) \<and>
        comma_phase_continue_action_observer phase f shift
          (comma_phase_program_entry_core_value_action f residue core wanted)
          target) [0..< ?modulus] =
      comma_phase_continue_action_observer phase f shift
        (comma_phase_program_operator_nf ?program ?effective) target"
    using value_bound selected_action guard_eval
    by (auto simp: list_ex_iff)
  have selected_step:
    "comma_phase_program_step_at ?program phase shift =
      comma_phase_program_step_of_action
        (comma_source_continuation_transport shift
          (comma_phase_program_entry_core_value_action f residue core ?value))"
    using structural selected_action
    by (simp add: comma_phase_program_step_at_def)
  have goto_bounds:
    "comma_phase_program_step_at ?program phase shift =
       Comma_Program_Goto child child_shift \<Longrightarrow>
      f<comma_phase_program_sector child \<and>
      comma_phase_program_sector child\<le>9"
    for child child_shift
  proof -
    assume goto:
      "comma_phase_program_step_at ?program phase shift =
         Comma_Program_Goto child child_shift"
    have bounds:
      "comma_phase_program_sector ?program <
          comma_phase_program_sector child \<and>
       comma_phase_program_sector child\<le>9"
      by (rule comma_phase_program_step_goto_sector_bounds[OF goto])
    show ?thesis using bounds by simp
  qed
  have action_step_helper:
    "comma_phase_continue_action_observer phase f shift
        (comma_phase_program_entry_core_value_action f residue core ?value) target =
      comma_phase_continue_step_observer phase target
        (comma_phase_program_step_at ?program phase shift)"
    by (rule comma_phase_continue_action_observer_step_exact
      [OF selected_step goto_bounds])
  have action_step:
    "comma_phase_continue_action_observer phase f shift
        (comma_phase_program_operator_nf ?program ?effective) target =
      comma_phase_continue_step_observer phase target
        (comma_phase_program_step_at ?program phase shift)"
    using action_step_helper selected_action by simp
  show ?thesis
    using branch_partition action_step
    by (simp add: comma_phase_continue_compile_job_observer.simps)
qed

function (sequential) comma_phase_continue_compile_job ::
    "comma_phase_continue_job \<Rightarrow> comma_phase_continue_columns"
where
  "comma_phase_continue_compile_job (Comma_Continue_Program_Job program) =
    (if comma_phase_program_structurally_admitted program then
       (case program of
          Comma_Entry_Core_Program f d residue core \<Rightarrow>
            comma_phase_continue_compile_job
              (Comma_Continue_Core_Values_Job f residue core
                [0..<comma_phase_core_modulus core])
        | Comma_Near_Residual_Program f d residual \<Rightarrow>
            comma_phase_continue_compile_job
              (Comma_Continue_Action_Job f
                (comma_phase_program_operator_nf program 0))
        | Comma_Near_Boundary_Program f \<Rightarrow>
            comma_phase_continue_compile_job
              (Comma_Continue_Action_Job f
                (comma_phase_program_operator_nf program 0)))
     else comma_phase_continue_false_columns)"
| "comma_phase_continue_compile_job
      (Comma_Continue_Core_Values_Job f residue core []) =
    comma_phase_continue_false_columns"
| "comma_phase_continue_compile_job
      (Comma_Continue_Core_Values_Job f residue core (wanted#remaining)) =
    (let guard=comma_core_value_guard core wanted;
         rest=comma_phase_continue_compile_job
           (Comma_Continue_Core_Values_Job f residue core remaining)
     in if comma_crt_supported guard then
          comma_phase_continue_columns_or
            (comma_phase_continue_columns_and guard
              (comma_phase_continue_compile_job
                (Comma_Continue_Action_Job f
                  (comma_phase_program_entry_core_value_action
                    f residue core wanted))))
            rest
        else rest)"
| "comma_phase_continue_compile_job
      (Comma_Continue_Action_Job parent action) =
    (case action of
       Comma_Continuation_Goto source delta \<Rightarrow>
         (case comma_semantic_port_program_of_source source of
            Some child \<Rightarrow>
              if parent < comma_phase_program_sector child \<and>
                 comma_phase_program_sector child \<le> 9
              then (let child_columns=comma_phase_continue_compile_job
                    (Comma_Continue_Program_Job child)
                in (\<lambda>shift target.
                    child_columns (shift+delta) target))
              else comma_phase_continue_false_columns
          | None \<Rightarrow> comma_phase_continue_false_columns)
     | Comma_Continuation_Exit source delta \<Rightarrow>
         (\<lambda>shift target. Comma_CRT_Bool
           (comma_phase_continue_exit_target target source (shift+delta)))
     | _ \<Rightarrow> comma_phase_continue_false_columns)"
  by pat_completeness auto

lemma comma_phase_continue_program_entry_decreases:
  assumes program:
    "program = Comma_Entry_Core_Program f d residue core"
  shows "(Comma_Continue_Core_Values_Job f residue core
      [0..<comma_phase_core_modulus core],
    Comma_Continue_Program_Job program)
      \<in> measure comma_phase_continue_job_measure"
proof -
  have core_bound: "comma_phase_core_modulus core<30"
    by (cases core) simp_all
  show ?thesis
    using core_bound program
    by (simp add: in_measure comma_phase_continue_job_measure_def
        comma_phase_continue_job_sector.simps comma_phase_continue_job_stage.simps
        comma_phase_continue_job_tail.simps comma_phase_program_sector.simps
        Let_def)
qed

lemma comma_phase_continue_program_action_decreases:
  assumes sector: "comma_phase_program_sector program=f"
  shows "comma_phase_continue_job_measure
      (Comma_Continue_Action_Job f action) <
    comma_phase_continue_job_measure (Comma_Continue_Program_Job program)"
  using sector
  by (simp add: comma_phase_continue_job_measure_def
      comma_phase_continue_job_sector.simps comma_phase_continue_job_stage.simps
      comma_phase_continue_job_tail.simps Let_def)

lemma comma_phase_continue_tail_decreases:
  "comma_phase_continue_job_measure
      (Comma_Continue_Core_Values_Job f residue core remaining) <
    comma_phase_continue_job_measure
      (Comma_Continue_Core_Values_Job f residue core (wanted#remaining))"
  by (simp add: comma_phase_continue_job_measure_def
      comma_phase_continue_job_sector.simps comma_phase_continue_job_stage.simps
      comma_phase_continue_job_tail.simps Let_def)

lemma comma_phase_continue_core_action_decreases:
  "comma_phase_continue_job_measure (Comma_Continue_Action_Job f action) <
    comma_phase_continue_job_measure
      (Comma_Continue_Core_Values_Job f residue core (wanted#remaining))"
  by (simp add: comma_phase_continue_job_measure_def
      comma_phase_continue_job_sector.simps comma_phase_continue_job_stage.simps
      comma_phase_continue_job_tail.simps Let_def)

lemma comma_phase_continue_goto_decreases:
  assumes sector: "parent < comma_phase_program_sector child"
    and bound: "comma_phase_program_sector child\<le>9"
  shows "comma_phase_continue_job_measure
      (Comma_Continue_Program_Job child) <
    comma_phase_continue_job_measure
      (Comma_Continue_Action_Job parent (Comma_Continuation_Goto source delta))"
  using sector bound
  by (simp add: comma_phase_continue_job_measure_def
      comma_phase_continue_job_sector.simps comma_phase_continue_job_stage.simps
      comma_phase_continue_job_tail.simps comma_phase_program_sector.simps Let_def)

termination
  apply (relation "measure comma_phase_continue_job_measure")
  apply (rule wf_measure)
  subgoal
    by (rule comma_phase_continue_program_entry_decreases; assumption)
  apply (simp_all only: in_measure)
  by (auto simp: comma_phase_continue_job_measure_def
      comma_phase_continue_job_sector.simps
      comma_phase_continue_job_stage.simps
      comma_phase_continue_job_tail.simps comma_phase_program_sector.simps
      Let_def
      intro: comma_phase_continue_program_action_decreases
        comma_phase_continue_tail_decreases
        comma_phase_continue_core_action_decreases
        comma_phase_continue_goto_decreases)

text \<open>The recursive compiler is unfolded one job at a time. Its induction
hypotheses and published child equations must take precedence over evaluation
of descendants. Code equations remain available to the checked publisher.\<close>
declare comma_phase_continue_compile_job.simps [simp del]

lemma comma_phase_continue_compile_job_admitted:
  "\<forall>shift target. comma_crt_admitted 0
    (comma_phase_continue_compile_job job shift target)"
proof (induction job rule: comma_phase_continue_compile_job.induct)
  case (1 program)
  note program_IH = "1.IH"
  have program_equation:
    "comma_phase_continue_compile_job (Comma_Continue_Program_Job program) =
      (if comma_phase_program_structurally_admitted program then
         (case program of
            Comma_Entry_Core_Program f d residue core \<Rightarrow>
              comma_phase_continue_compile_job
                (Comma_Continue_Core_Values_Job f residue core
                  [0..<comma_phase_core_modulus core])
          | Comma_Near_Residual_Program f d residual \<Rightarrow>
              comma_phase_continue_compile_job
                (Comma_Continue_Action_Job f
                  (comma_phase_program_operator_nf program 0))
          | Comma_Near_Boundary_Program f \<Rightarrow>
              comma_phase_continue_compile_job
                (Comma_Continue_Action_Job f
                  (comma_phase_program_operator_nf program 0)))
       else comma_phase_continue_false_columns)"
    by (rule comma_phase_continue_compile_job.simps(1))
  show ?case
  proof (cases program)
    case (Comma_Entry_Core_Program f d residue core)
    show ?thesis
    proof (cases "comma_phase_program_structurally_admitted program")
      case False
      then show ?thesis
        using Comma_Entry_Core_Program program_equation
        by (subst program_equation)
           (simp add: comma_phase_continue_false_columns_def)
    next
      case True
      have child_IH:
        "\<forall>shift target. comma_crt_admitted 0
          (comma_phase_continue_compile_job
            (Comma_Continue_Core_Values_Job f residue core
              [0..<comma_phase_core_modulus core]) shift target)"
        using program_IH Comma_Entry_Core_Program True by blast
      show ?thesis
        using child_IH Comma_Entry_Core_Program True program_equation
        by (subst program_equation) simp
    qed
  next
    case (Comma_Near_Residual_Program f d residual)
    show ?thesis
    proof (cases "comma_phase_program_structurally_admitted program")
      case False
      then show ?thesis
        using Comma_Near_Residual_Program program_equation
        by (subst program_equation)
           (simp add: comma_phase_continue_false_columns_def)
    next
      case True
      have child_IH:
        "\<forall>shift target. comma_crt_admitted 0
          (comma_phase_continue_compile_job
            (Comma_Continue_Action_Job f
              (comma_phase_program_operator_nf program 0)) shift target)"
        using program_IH Comma_Near_Residual_Program True by blast
      show ?thesis
        using child_IH Comma_Near_Residual_Program True program_equation
        by (subst program_equation) simp
    qed
  next
    case (Comma_Near_Boundary_Program f)
    show ?thesis
    proof (cases "comma_phase_program_structurally_admitted program")
      case False
      then show ?thesis
        using Comma_Near_Boundary_Program program_equation
        by (subst program_equation)
           (simp add: comma_phase_continue_false_columns_def)
    next
      case True
      have child_IH:
        "\<forall>shift target. comma_crt_admitted 0
          (comma_phase_continue_compile_job
            (Comma_Continue_Action_Job f
              (comma_phase_program_operator_nf program 0)) shift target)"
        using program_IH Comma_Near_Boundary_Program True by blast
      show ?thesis
        using child_IH Comma_Near_Boundary_Program True program_equation
        by (subst program_equation) simp
    qed
  qed
next
  case (2 f residue core)
  then show ?case
    by (simp add: comma_phase_continue_compile_job.simps(2)
        comma_phase_continue_false_columns_def)
next
  case (3 f residue core wanted remaining)
  note tail_IH = "3.IH"(1)
  note action_IH = "3.IH"(2)
  let ?guard = "comma_core_value_guard core wanted"
  let ?rest = "comma_phase_continue_compile_job
    (Comma_Continue_Core_Values_Job f residue core remaining)"
  let ?action_job = "Comma_Continue_Action_Job f
    (comma_phase_program_entry_core_value_action f residue core wanted)"
  have rest_admitted:
    "\<forall>shift target. comma_crt_admitted 0 (?rest shift target)"
    using tail_IH[of ?guard] by simp
  have action_admitted_if_supported:
    "comma_crt_supported ?guard \<Longrightarrow>
      (\<forall>shift target. comma_crt_admitted 0
        (comma_phase_continue_compile_job ?action_job shift target))"
    using action_IH[of ?guard ?rest] by simp
  show ?case
  proof (intro allI)
    fix shift target
    have rest_at: "comma_crt_admitted 0 (?rest shift target)"
      using rest_admitted by blast
    show "comma_crt_admitted 0
      (comma_phase_continue_compile_job
        (Comma_Continue_Core_Values_Job f residue core (wanted#remaining))
        shift target)"
    proof (cases "comma_crt_supported ?guard")
      case False
      then show ?thesis
        using rest_at
        by (simp only: comma_phase_continue_compile_job.simps(3)
            Let_def if_False)
    next
      case True
      have action_at:
        "comma_crt_admitted 0
          (comma_phase_continue_compile_job ?action_job shift target)"
        using action_admitted_if_supported True by blast
      have guard_admitted: "comma_crt_admitted 0 ?guard"
        by (rule comma_core_value_guard_admitted)
      have shifted_guard:
        "comma_crt_admitted 0 (comma_crt_shift shift ?guard)"
        by (rule comma_crt_shift_admitted[OF guard_admitted])
      have inner:
        "comma_crt_admitted 0
          (comma_crt_apply Comma_CRT_And
            (comma_crt_shift shift ?guard)
            (comma_phase_continue_compile_job ?action_job shift target))"
        by (rule comma_crt_apply_admitted[OF shifted_guard action_at])
      have combined:
        "comma_crt_admitted 0
          (comma_crt_apply Comma_CRT_Or
            (comma_crt_apply Comma_CRT_And
              (comma_crt_shift shift ?guard)
              (comma_phase_continue_compile_job ?action_job shift target))
            (?rest shift target))"
        by (rule comma_crt_apply_admitted[OF inner rest_at])
      show ?thesis
        using True combined
        by (simp only: comma_phase_continue_compile_job.simps(3)
            Let_def if_True comma_phase_continue_columns_or_def
            comma_phase_continue_columns_and_def)
    qed
  qed
next
  case (4 parent action)
  show ?case
    using "4.IH"
    by (cases action)
      (auto simp: comma_phase_continue_compile_job.simps(4)
        comma_phase_continue_false_columns_def Let_def
        split: option.splits if_splits)
qed

ML \<open>
  val published = @{thms
    comma_phase_continue_exit_target_partition
    comma_phase_continue_compile_job_admitted
    comma_phase_continue_action_observer_step_exact}
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "program Continue guard compiler" published
\<close>

end
