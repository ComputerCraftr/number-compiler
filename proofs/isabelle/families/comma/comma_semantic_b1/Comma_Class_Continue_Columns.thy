theory Comma_Class_Continue_Columns
  imports Comma_Program_Continue_Guard_Exact
begin

definition comma_semantic_phase_continue_columns ::
    "nat \<Rightarrow> comma_phase_continue_columns" where
  "comma_semantic_phase_continue_columns source =
    (if source<46 then
       (case comma_semantic_phase_program_for_class source of
          Some program \<Rightarrow>
            comma_phase_continue_compile_job
              (Comma_Continue_Program_Job program)
        | None \<Rightarrow> comma_phase_continue_false_columns)
     else comma_phase_continue_false_columns)"

definition comma_semantic_phase_continue_column ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_crt_column" where
  "comma_semantic_phase_continue_column source target =
    comma_semantic_phase_continue_columns source 0 target"

lemma comma_semantic_phase_continue_column_admitted:
  assumes source: "source<46" and target: "target<46"
  shows "comma_crt_admitted 0
    (comma_semantic_phase_continue_column source target)"
proof -
  have family_admitted:
    "comma_crt_admitted 0
      (comma_phase_continue_compile_job
        (Comma_Continue_Program_Job program) 0 target)" for program
    using comma_phase_continue_compile_job_admitted[of
        "Comma_Continue_Program_Job program"] by simp
  show ?thesis
    using source target family_admitted
    by (auto simp: comma_semantic_phase_continue_column_def
      comma_semantic_phase_continue_columns_def
      comma_phase_continue_false_columns_def
      split: option.splits)
qed

lemma comma_semantic_phase_continue_column_exact:
  assumes phase: "phase<924" and source: "source<46" and target: "target<46"
  shows "comma_crt_eval phase
      (comma_semantic_phase_continue_column source target) =
    (comma_semantic_phase_program_class_step phase source =
      Comma_Phase_Class_Continue ((phase+1) mod 924) target)"
proof -
  have guard_exact:
    "comma_semantic_phase_program_class_continue_guard phase source target =
      (comma_semantic_phase_program_class_step phase source =
        Comma_Phase_Class_Continue ((phase+1) mod 924) target)"
    by (rule comma_semantic_phase_program_class_continue_guard_exact
      [OF phase source])
  show ?thesis
  proof (cases "comma_semantic_phase_program_for_class source")
    case None
    then show ?thesis
      using guard_exact source phase
      by (simp add: comma_semantic_phase_continue_column_def
          comma_semantic_phase_continue_columns_def
          comma_phase_continue_false_columns_def
          comma_semantic_phase_program_class_continue_guard_def)
  next
    case (Some program)
    have column_job:
      "comma_semantic_phase_continue_column source target =
        comma_phase_continue_compile_job
          (Comma_Continue_Program_Job program) 0 target"
      using source Some
      by (simp add: comma_semantic_phase_continue_column_def
          comma_semantic_phase_continue_columns_def)
    have compiler_exact:
      "comma_crt_eval phase
          (comma_phase_continue_compile_job
            (Comma_Continue_Program_Job program) 0 target) =
        comma_phase_continue_compile_job_observer phase
          (Comma_Continue_Program_Job program) 0 target"
      by (rule comma_phase_continue_compile_job_exact)
    have observer_guard:
      "comma_phase_continue_compile_job_observer phase
          (Comma_Continue_Program_Job program) 0 target =
        comma_semantic_phase_program_continue_guard phase program 0 target"
      by (simp only: comma_phase_continue_compile_job_observer.simps
          comma_semantic_phase_program_continue_guard_step[symmetric])
    have class_guard:
      "comma_semantic_phase_program_class_continue_guard phase source target =
        comma_semantic_phase_program_continue_guard phase program 0 target"
      using phase source Some
      by (simp add: comma_semantic_phase_program_class_continue_guard_def)
    have generic_to_class_guard:
      "comma_semantic_phase_program_continue_guard phase program 0 target =
        comma_semantic_phase_program_class_continue_guard phase source target"
      using class_guard by (rule sym)
    have first:
      "comma_crt_eval phase
        (comma_semantic_phase_continue_column source target) =
        comma_phase_continue_compile_job_observer phase
          (Comma_Continue_Program_Job program) 0 target"
      using column_job compiler_exact by simp
    also have "... =
          comma_semantic_phase_program_continue_guard phase program 0 target"
      by (rule observer_guard)
    also have "... =
          comma_semantic_phase_program_class_continue_guard phase source target"
      by (rule generic_to_class_guard)
    also have "... =
          (comma_semantic_phase_program_class_step phase source =
            Comma_Phase_Class_Continue ((phase+1) mod 924) target)"
      by (rule guard_exact)
    finally show ?thesis .
  qed
qed

text \<open>External phase transport acts on the certified zero-offset column.
The compiler's internal shift records a within-round source seam and is not
an external clock argument.\<close>

lemma comma_semantic_phase_continue_column_clock_exact:
  assumes phase: "phase<924" and source: "source<46" and target: "target<46"
  shows "comma_crt_eval phase
      (comma_crt_shift clock
        (comma_semantic_phase_continue_column source target)) =
    (comma_semantic_phase_program_class_step ((phase+clock) mod 924) source =
      Comma_Phase_Class_Continue
        ((((phase+clock) mod 924)+1) mod 924) target)"
proof -
  have admitted:
    "comma_crt_admitted 0 (comma_semantic_phase_continue_column source target)"
    by (rule comma_semantic_phase_continue_column_admitted[OF source target])
  have shift:
    "comma_crt_eval phase
        (comma_crt_shift clock (comma_semantic_phase_continue_column source target)) =
      comma_crt_eval (phase+clock) (comma_semantic_phase_continue_column source target)"
    by (rule comma_crt_shift_refines[OF admitted])
  have periodic:
    "comma_crt_eval (phase+clock) (comma_semantic_phase_continue_column source target) =
      comma_crt_eval ((phase+clock) mod 924)
        (comma_semantic_phase_continue_column source target)"
    by (rule sym[OF comma_crt_eval_periodic[OF admitted]])
  have exact:
    "comma_crt_eval ((phase+clock) mod 924)
        (comma_semantic_phase_continue_column source target) =
      (comma_semantic_phase_program_class_step ((phase+clock) mod 924) source =
        Comma_Phase_Class_Continue
          ((((phase+clock) mod 924)+1) mod 924) target)"
    by (rule comma_semantic_phase_continue_column_exact[OF _ source target]) simp
  show ?thesis using shift periodic exact by simp
qed

ML \<open>
  val published = @{thms
    comma_semantic_phase_continue_column_admitted
    comma_semantic_phase_continue_column_exact
    comma_semantic_phase_continue_column_clock_exact}
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "source-free class Continue columns" published
\<close>

end
