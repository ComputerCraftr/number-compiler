theory Comma_Direct_Bellman_Projection
  imports Comma_Direct_Action_Constructors Comma_Targeted_Continue_Observer_Refinement
begin

text \<open>The value 243 is outside the admitted Bellman range. The projection
is an interface for independently checked symbolic operators; this theory
does not certify any particular candidate value function.\<close>

fun comma_direct_bellman_mask_projection ::
  "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> comma_phase_rank_mask_action \<Rightarrow> nat" where
  "comma_direct_bellman_mask_projection D phase Comma_Phase_Rank_Mask_Invalid = 243"
| "comma_direct_bellman_mask_projection D phase (Comma_Phase_Rank_Mask_Continue target) =
    (if target < 46 then 9 + D ((phase+1) mod 924) target else 243)"
| "comma_direct_bellman_mask_projection D phase (Comma_Phase_Rank_Mask_Fork digit delta) =
    (if 2 \<le> digit \<and> digit \<le> 9 \<and> delta=0 then digit-2 else 243)"
| "comma_direct_bellman_mask_projection D phase (Comma_Phase_Rank_Mask_Landmine delta) =
    (if delta=0 then 8 else 243)"

fun comma_direct_bellman_class_projection ::
  "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat comma_phase_class_action \<Rightarrow> nat" where
  "comma_direct_bellman_class_projection D phase Comma_Phase_Class_Invalid = 243"
| "comma_direct_bellman_class_projection D phase (Comma_Phase_Class_Continue next target) =
    (if next=(phase+1) mod 924 \<and> target<46 then 9+D next target else 243)"
| "comma_direct_bellman_class_projection D phase (Comma_Phase_Class_Fork digit delta) =
    (if 2 \<le> digit \<and> digit \<le> 9 \<and> delta=0 then digit-2 else 243)"
| "comma_direct_bellman_class_projection D phase (Comma_Phase_Class_Landmine delta) =
    (if delta=0 then 8 else 243)"

lemma comma_direct_bellman_lift_projection:
  "comma_direct_bellman_mask_projection D phase action =
    comma_direct_bellman_class_projection D phase (comma_phase_rank_mask_lift phase action)"
  by (cases action) simp_all

lemma comma_direct_bellman_terminal_projection:
  "comma_direct_bellman_mask_projection D phase
    (comma_direct_action_interpret Comma_Direct_Invalid phase shift) = 243"
  "comma_direct_bellman_mask_projection D phase
    (comma_direct_action_interpret (Comma_Direct_Continue target delta) phase shift) =
      (if (delta+shift) mod 924=1 \<and> target<46
        then 9+D ((phase+1) mod 924) target else 243)"
  "comma_direct_bellman_mask_projection D phase
    (comma_direct_action_interpret (Comma_Direct_Fork digit delta) phase shift) =
      (if 2\<le>digit \<and> digit\<le>9 \<and> shift+delta=0 then digit-2 else 243)"
  "comma_direct_bellman_mask_projection D phase
    (comma_direct_action_interpret (Comma_Direct_Landmine delta) phase shift) =
      (if shift+delta=0 then 8 else 243)"
proof -
  have cancel: "(phase+k) mod 924 = (Suc phase) mod 924 \<longleftrightarrow> k mod 924=1"
    for k :: nat
  proof -
    have "[phase+k=phase+1] (mod 924) \<longleftrightarrow> [k=1] (mod 924)"
      by (rule cong_add_lcancel_nat)
    then show ?thesis by (simp add: cong_def)
  qed
  show "comma_direct_bellman_mask_projection D phase
    (comma_direct_action_interpret Comma_Direct_Invalid phase shift) = 243" by simp
  show "comma_direct_bellman_mask_projection D phase
    (comma_direct_action_interpret (Comma_Direct_Continue target delta) phase shift) =
      (if (delta+shift) mod 924=1 \<and> target<46
        then 9+D ((phase+1) mod 924) target else 243)"
    by (simp add: cancel)
  show "comma_direct_bellman_mask_projection D phase
    (comma_direct_action_interpret (Comma_Direct_Fork digit delta) phase shift) =
      (if 2\<le>digit \<and> digit\<le>9 \<and> shift+delta=0 then digit-2 else 243)" by simp
  show "comma_direct_bellman_mask_projection D phase
    (comma_direct_action_interpret (Comma_Direct_Landmine delta) phase shift) =
      (if shift+delta=0 then 8 else 243)" by simp
qed

lemma comma_direct_bellman_from_projection:
  assumes projected: "\<And>phase cid program. phase<924 \<Longrightarrow> cid<46 \<Longrightarrow>
      comma_semantic_phase_program_for_class cid = Some program \<Longrightarrow>
      D phase cid \<le> 242 \<and> D phase cid =
        comma_direct_bellman_mask_projection D phase
          (comma_semantic_phase_program_fold comma_phase_program_full_action_output
            phase program 0)"
  shows "comma_frontier_m204_bellman D"
proof (unfold comma_frontier_m204_bellman_def, intro allI impI)
  fix phase cid :: nat
  assume phase: "phase<924" and cid: "cid<46"
  obtain program where binding: "comma_semantic_phase_program_for_class cid = Some program"
    by (rule comma_semantic_phase_program_for_class_some[OF cid])
  have checked: "D phase cid \<le> 242 \<and> D phase cid =
      comma_direct_bellman_mask_projection D phase
        (comma_semantic_phase_program_fold comma_phase_program_full_action_output phase program 0)"
    by (rule projected[OF phase cid binding])
  have step: "comma_phase_rank_mask_lift phase
      (comma_semantic_phase_program_fold comma_phase_program_full_action_output phase program 0) =
    comma_semantic_phase_program_class_step phase cid"
    using comma_phase_program_full_action_class_exact[OF phase cid binding]
      comma_phase_program_full_action_fold_fusion by simp
  have class_value: "D phase cid = comma_direct_bellman_class_projection D phase
      (comma_semantic_phase_program_class_step phase cid)"
    using checked comma_direct_bellman_lift_projection step by metis
  have bound: "D phase cid \<le> 242" using checked by simp
  show "D phase cid \<le> 242 \<and>
      (case comma_semantic_phase_program_class_step phase cid of
         Comma_Phase_Class_Invalid \<Rightarrow> False
       | Comma_Phase_Class_Fork a delta \<Rightarrow>
           2 \<le> a \<and> a \<le> 9 \<and> delta=0 \<and> D phase cid=a-2
       | Comma_Phase_Class_Landmine delta \<Rightarrow> delta=0 \<and> D phase cid=8
       | Comma_Phase_Class_Continue next target \<Rightarrow>
           next=(phase+1) mod 924 \<and> target<46 \<and> D phase cid=9+D next target)"
  proof (cases "comma_semantic_phase_program_class_step phase cid")
    case Comma_Phase_Class_Invalid
    then show ?thesis using bound class_value by simp
  next
    case (Comma_Phase_Class_Fork a delta)
    then show ?thesis using bound class_value
      by (auto split: if_splits; arith)
  next
    case (Comma_Phase_Class_Landmine delta)
    then show ?thesis using bound class_value by (auto split: if_splits)
  next
    case (Comma_Phase_Class_Continue next_phase target)
    then show ?thesis using bound class_value
      by (auto split: if_splits; arith)
  qed
qed

lemma comma_direct_bellman_from_class_rows:
  assumes rows: "list_all (\<lambda>cid. \<exists>program.
      comma_semantic_phase_program_for_class cid = Some program \<and>
      (\<forall>phase<924. D phase cid \<le> 242 \<and> D phase cid =
        comma_direct_bellman_mask_projection D phase
          (comma_semantic_phase_program_fold comma_phase_program_full_action_output
            phase program 0))) [0..<46]"
  shows "comma_frontier_m204_bellman D"
proof (rule comma_direct_bellman_from_projection)
  fix phase cid :: nat and program :: comma_semantic_port_program
  assume phase: "phase<924" and cid: "cid<46"
    and binding: "comma_semantic_phase_program_for_class cid = Some program"
  have member: "cid \<in> set [0..<46]" using cid by simp
  obtain selected where selected:
      "comma_semantic_phase_program_for_class cid = Some selected"
      "\<forall>phase<924. D phase cid \<le> 242 \<and> D phase cid =
        comma_direct_bellman_mask_projection D phase
          (comma_semantic_phase_program_fold comma_phase_program_full_action_output
            phase selected 0)"
    using rows member unfolding list_all_iff by blast
  have selected_eq: "selected = program" using selected(1) binding by simp
  show "D phase cid \<le> 242 \<and> D phase cid =
      comma_direct_bellman_mask_projection D phase
        (comma_semantic_phase_program_fold comma_phase_program_full_action_output
          phase program 0)"
    using selected(2)[rule_format, OF phase] unfolding selected_eq .
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Direct Bellman projection" @{thms comma_direct_bellman_lift_projection
      comma_direct_bellman_terminal_projection
      comma_direct_bellman_from_projection comma_direct_bellman_from_class_rows};
\<close>

end
