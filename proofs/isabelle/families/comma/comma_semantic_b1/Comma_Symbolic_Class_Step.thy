theory Comma_Symbolic_Class_Step
  imports Comma_Semantic_Phase_Program_Round
begin

text \<open>
The class transition is evaluated by the normalized phase program for the
admitted sector-1 representative. The recursive evaluator receives only the
program, external phase, and shift; the physical source is used here only to
establish the binding and exactness theorem.
\<close>

definition comma_phase_program_continue_observer ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_round_result \<Rightarrow> bool" where
  "comma_phase_program_continue_observer target phase output =
    (case output of
       Comma_Round_Cross (Comma_Entry f delta x) \<Rightarrow>
         comma_decade_root_admitted (Comma_Entry f delta x) \<and>
         (phase+delta) mod 924 = (phase+1) mod 924 \<and>
         comma_offset_orbit x=target
     | _ \<Rightarrow> False)"

definition comma_semantic_phase_program_continue_guard ::
    "nat \<Rightarrow> comma_semantic_port_program \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_phase_program_continue_guard phase program shift target =
    comma_semantic_phase_program_fold
      (comma_phase_program_continue_observer target) phase program shift"

lemma comma_semantic_phase_program_continue_guard_exact:
  "comma_semantic_phase_program_continue_guard phase program shift target =
    (comma_phase_classify_decade_control comma_offset_orbit
      (comma_decade_decode phase
        (comma_semantic_phase_program_round phase program shift)) =
      Comma_Phase_Class_Continue ((phase+1) mod 924) target)"
proof -
  have fused:
    "comma_semantic_phase_program_continue_guard phase program shift target =
      comma_phase_program_continue_observer target phase
        (comma_semantic_phase_program_round phase program shift)"
    unfolding comma_semantic_phase_program_continue_guard_def
    by (rule comma_semantic_phase_program_fold_observer_fusion)
  show ?thesis
    using fused
    by (cases "comma_semantic_phase_program_round phase program shift")
      (auto simp: comma_phase_program_continue_observer_def
        split: comma_finite_position.splits)
qed

definition comma_semantic_phase_program_for_class ::
    "nat \<Rightarrow> comma_semantic_port_program option" where
  "comma_semantic_phase_program_for_class cid =
    (if cid<46 then
       comma_entry_control_program 1 (comma_offset_representatives!cid)
     else None)"

definition comma_semantic_phase_program_class_step ::
    "nat \<Rightarrow> nat \<Rightarrow> nat comma_phase_class_action" where
  "comma_semantic_phase_program_class_step phase cid =
    (if phase<924 \<and> cid<46 then
       (case comma_semantic_phase_program_for_class cid of
          None \<Rightarrow> Comma_Phase_Class_Invalid
        | Some program \<Rightarrow>
            comma_phase_classify_decade_control comma_offset_orbit
              (comma_decade_decode phase
                (comma_semantic_phase_program_round phase program 0)))
     else Comma_Phase_Class_Invalid)"

lemma comma_semantic_phase_program_class_step_exact:
  assumes phase: "phase<924" and class_bound: "cid<46"
  shows "comma_semantic_phase_program_class_step phase cid =
    comma_semantic_phase_class_step phase cid"
proof -
  have valid: "comma_semantic_phase_class_valid phase cid"
    using phase class_bound by (simp add: comma_semantic_phase_class_valid_def)
  let ?offset = "comma_offset_representatives!cid"
  let ?source = "Comma_Entry 1 0 ?offset"
  have rep_admitted:
      "comma_decade_admitted (Comma_Decade phase ?offset)"
    by (rule comma_semantic_phase_class_representative(1)[OF valid])
  have rep_bound: "?offset\<le>90" using rep_admitted by simp
  have rep_class: "comma_offset_orbit ?offset=cid"
    by (rule comma_semantic_phase_class_representative(2)[OF valid])
  have entry_bound: "comma_sector_entry_bound 1 ?offset"
    using rep_bound by (simp add: comma_sector_entry_bound_def)
  have canonical: "comma_canonical_position_admitted ?source"
    using entry_bound by (simp add: comma_canonical_position_admitted_def)
  have admitted: "comma_round_admitted ?source"
    by (rule comma_canonical_position_implies_round_admitted[OF canonical])
  have normalized: "?source=comma_source_continuation_base ?source"
    by simp
  obtain core where program:
      "comma_entry_control_program 1 ?offset =
        Some (Comma_Entry_Core_Program 1 (?offset mod 10)
          (?offset mod comma_finite_period_fast 1 (?offset mod 10)) core)"
    using comma_entry_control_program_core[where f=1 and x="?offset"] by auto
  let ?program = "Comma_Entry_Core_Program 1 (?offset mod 10)
    (?offset mod comma_finite_period_fast 1 (?offset mod 10)) core"
  have binding:
      "comma_semantic_port_program_of_source ?source=Some ?program"
    using comma_semantic_port_program_of_entry[OF entry_bound] program by simp
  have round_exact:
      "comma_semantic_phase_program_round phase ?program 0 =
        comma_decisive_endpoint_round phase ?source"
    using comma_semantic_phase_program_round_exact
      [OF canonical admitted normalized binding, of phase 0] by simp
  have endpoint_control:
      "comma_decade_control (Comma_Decade phase ?offset) =
        comma_decade_decode phase
          (comma_semantic_phase_program_round phase ?program 0)"
    using comma_decisive_endpoint_round_decade_control[OF rep_bound]
      round_exact by simp
  have class_step:
      "comma_semantic_phase_class_step phase cid =
        comma_phase_classify_decade_control comma_offset_orbit
          (comma_decade_control (Comma_Decade phase ?offset))"
    using valid rep_class
    by (simp add: comma_semantic_phase_class_step_def)
  show ?thesis using program endpoint_control class_step phase class_bound
    by (simp add: comma_semantic_phase_program_class_step_def
      comma_semantic_phase_program_for_class_def)
qed

definition comma_semantic_phase_program_class_continue_guard ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_phase_program_class_continue_guard phase cid target =
    (if phase<924 \<and> cid<46 then
       (case comma_semantic_phase_program_for_class cid of
          Some program \<Rightarrow>
            comma_semantic_phase_program_continue_guard phase program 0 target
        | None \<Rightarrow> False)
     else False)"

lemma comma_semantic_phase_program_class_continue_guard_exact:
  assumes phase: "phase<924" and cid: "cid<46"
  shows "comma_semantic_phase_program_class_continue_guard phase cid target =
    (comma_semantic_phase_program_class_step phase cid =
      Comma_Phase_Class_Continue ((phase+1) mod 924) target)"
  using phase cid comma_semantic_phase_program_continue_guard_exact
  by (simp add: comma_semantic_phase_program_class_continue_guard_def
      comma_semantic_phase_program_for_class_def
      comma_semantic_phase_program_class_step_def
      split: option.splits)

lemma comma_semantic_phase_program_class_step_not_invalid:
  assumes valid: "comma_semantic_phase_class_valid phase cid"
  shows "comma_semantic_phase_program_class_step phase cid \<noteq>
    Comma_Phase_Class_Invalid"
proof -
  have phase: "phase<924" and class_bound: "cid<46"
    using valid by (auto simp: comma_semantic_phase_class_valid_def)
  have exact:
    "comma_semantic_phase_program_class_step phase cid =
      comma_semantic_phase_class_step phase cid"
    by (rule comma_semantic_phase_program_class_step_exact[OF phase class_bound])
  show ?thesis
    using exact comma_semantic_phase_class_step_not_invalid[OF valid] by simp
qed

lemma comma_semantic_phase_program_class_step_continue_closed:
  assumes valid: "comma_semantic_phase_class_valid phase cid"
    and continued:
      "comma_semantic_phase_program_class_step phase cid =
        Comma_Phase_Class_Continue next_phase next_class"
  shows "next_phase=(phase+1) mod 924"
    "comma_semantic_phase_class_valid next_phase next_class"
proof -
  have phase: "phase<924" and class_bound: "cid<46"
    using valid by (auto simp: comma_semantic_phase_class_valid_def)
  have exact:
    "comma_semantic_phase_program_class_step phase cid =
      comma_semantic_phase_class_step phase cid"
    by (rule comma_semantic_phase_program_class_step_exact[OF phase class_bound])
  have old_continue:
      "comma_semantic_phase_class_step phase cid =
        Comma_Phase_Class_Continue next_phase next_class"
    using exact continued by simp
  show "next_phase=(phase+1) mod 924"
    and "comma_semantic_phase_class_valid next_phase next_class"
    by (rule comma_semantic_phase_class_continue_closed[OF valid old_continue])+
qed

theorem comma_semantic_phase_program_class_step_B32_if_no_27:
  fixes s :: comma_decade_state
  assumes no_27:
      "\<And>phase cid. comma_semantic_phase_class_valid phase cid \<Longrightarrow>
        \<not> comma_phase_class_survives
          comma_semantic_phase_program_class_step 27 phase cid"
    and admitted: "comma_decade_admitted s"
  shows "\<exists>h tau. h \<le> 26 \<and>
    comma_decade_block_power 5 s = Comma_Block_Stop h tau \<and>
    comma_residual_block 32 (h,tau) = Comma_Residual_Stop h tau \<and>
    comma_decade_exact_summary s h tau"
proof -
  have no_invalid:
      "\<And>phase cid. comma_semantic_phase_class_valid phase cid \<Longrightarrow>
        comma_semantic_phase_program_class_step phase cid \<noteq>
          Comma_Phase_Class_Invalid"
    by (rule comma_semantic_phase_program_class_step_not_invalid; assumption)
  have continue_closed:
      "\<And>phase cid next_phase next_class.
        comma_semantic_phase_class_valid phase cid \<Longrightarrow>
        comma_semantic_phase_program_class_step phase cid =
          Comma_Phase_Class_Continue next_phase next_class \<Longrightarrow>
        comma_semantic_phase_class_valid next_phase next_class"
    by (rule comma_semantic_phase_program_class_step_continue_closed(2); assumption)
  have source_valid:
      "\<And>phase x. comma_decade_admitted (Comma_Decade phase x) \<Longrightarrow>
        comma_semantic_phase_class_valid phase (comma_offset_orbit x)"
    by (rule comma_semantic_phase_class_source_valid; assumption)
  have source_control:
      "\<And>phase x. comma_decade_admitted (Comma_Decade phase x) \<Longrightarrow>
        comma_semantic_phase_program_class_step phase (comma_offset_orbit x) =
          comma_phase_classify_decade_control comma_offset_orbit
            (comma_decade_control (Comma_Decade phase x))"
  proof -
    fix phase x
    assume source: "comma_decade_admitted (Comma_Decade phase x)"
    have class_valid:
        "comma_semantic_phase_class_valid phase (comma_offset_orbit x)"
      by (rule comma_semantic_phase_class_source_valid[OF source])
    have exact:
        "comma_semantic_phase_program_class_step phase (comma_offset_orbit x) =
          comma_semantic_phase_class_step phase (comma_offset_orbit x)"
      by (rule comma_semantic_phase_program_class_step_exact;
        use class_valid in \<open>auto simp: comma_semantic_phase_class_valid_def\<close>)
    have control:
        "comma_semantic_phase_class_step phase (comma_offset_orbit x) =
          comma_phase_classify_decade_control comma_offset_orbit
            (comma_decade_control (Comma_Decade phase x))"
      by (rule comma_semantic_phase_class_source_control[OF source])
    show "comma_semantic_phase_program_class_step phase (comma_offset_orbit x) =
        comma_phase_classify_decade_control comma_offset_orbit
          (comma_decade_control (Comma_Decade phase x))"
      using exact control by simp
  qed
  show ?thesis
    by (rule comma_phase_class_survival_rank_B32
      [where class_of=comma_offset_orbit
        and valid=comma_semantic_phase_class_valid
        and step=comma_semantic_phase_program_class_step
        and s=s,
       OF no_invalid continue_closed no_27 source_valid source_control admitted])
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Program class-step refinement and conditional B32 contract"
    @{thms comma_semantic_phase_program_continue_guard_exact
      comma_semantic_phase_program_class_step_exact
      comma_semantic_phase_program_class_continue_guard_exact
      comma_semantic_phase_program_class_step_B32_if_no_27};
\<close>

end
