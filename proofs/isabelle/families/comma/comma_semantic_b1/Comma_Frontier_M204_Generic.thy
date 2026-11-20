theory Comma_Frontier_M204_Generic
  imports Comma_Symbolic_Class_Step Comma_Semantic_Action_Power
begin

text \<open>
A *generic*, uninstantiated exact-Frontier certificate interface.  The
concrete 4804-node MDD still needs Isabelle-kernel authentication against the
physical source action.  No theorem in this file admits untrusted candidate
nodes.  The generator's D values are exact B1 Stop encodings, NOT literal
physical elapsed times or standalone Goto child identity.
\<close>

definition comma_frontier_m204_bellman ::
  "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "comma_frontier_m204_bellman D \<longleftrightarrow>
    (\<forall>phase<924. \<forall>cid<46.
      D phase cid \<le> 242 \<and>
      (case comma_semantic_phase_program_class_step phase cid of
         Comma_Phase_Class_Invalid \<Rightarrow> False
       | Comma_Phase_Class_Fork a delta \<Rightarrow>
           2 \<le> a \<and> a \<le> 9 \<and> delta = 0 \<and> D phase cid = a - 2
       | Comma_Phase_Class_Landmine delta \<Rightarrow>
           delta = 0 \<and> D phase cid = 8
       | Comma_Phase_Class_Continue next_phase next_class \<Rightarrow>
           next_phase = (phase+1) mod 924 \<and> next_class < 46 \<and>
           D phase cid = 9 + D next_phase next_class))"

text \<open>The finite typed action code is an observation only.  Its equality
with the actual symbolic step remains an explicit checked premise.\<close>

fun comma_frontier_m204_action_code ::
    "nat \<Rightarrow> nat comma_phase_class_action \<Rightarrow> nat" where
  "comma_frontier_m204_action_code phase Comma_Phase_Class_Invalid = 0"
| "comma_frontier_m204_action_code phase (Comma_Phase_Class_Fork a delta) =
    (if 2 \<le> a \<and> a \<le> 9 \<and> delta=0 then 45+a else 0)"
| "comma_frontier_m204_action_code phase (Comma_Phase_Class_Landmine delta) =
    (if delta=0 then 55 else 0)"
| "comma_frontier_m204_action_code phase (Comma_Phase_Class_Continue next_phase next_class) =
    (if next_phase=(phase+1) mod 924 \<and> next_class<46 then Suc next_class else 0)"

definition comma_frontier_m204_code_bellman ::
    "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "comma_frontier_m204_code_bellman D action \<longleftrightarrow>
    (\<forall>phase<924. \<forall>cid<46.
      D phase cid \<le> 242 \<and>
      (let code=action phase cid in
        if code=0 then False
        else if code\<le>46 then
          D phase cid = 9 + D ((phase+1) mod 924) (code-1)
        else if code\<le>55 then D phase cid=code-47
        else False))"

lemma comma_frontier_m204_code_to_bellman:
  assumes checked: "comma_frontier_m204_code_bellman D action"
    and exact: "\<And>phase cid. phase<924 \<Longrightarrow> cid<46 \<Longrightarrow>
      action phase cid = comma_frontier_m204_action_code phase
        (comma_semantic_phase_program_class_step phase cid)"
  shows "comma_frontier_m204_bellman D"
proof (unfold comma_frontier_m204_bellman_def, intro allI impI)
  fix phase cid :: nat
  assume phase: "phase<924" and cid: "cid<46"
  have D_bound: "D phase cid \<le> 242" and condition:
    "let code=action phase cid in
      if code=0 then False
      else if code\<le>46 then D phase cid = 9 + D ((phase+1) mod 924) (code-1)
      else if code\<le>55 then D phase cid=code-47
      else False"
    using checked phase cid by (auto simp: comma_frontier_m204_code_bellman_def)
  have binding: "action phase cid = comma_frontier_m204_action_code phase
      (comma_semantic_phase_program_class_step phase cid)"
    by (rule exact[OF phase cid])
  show "D phase cid \<le> 242 \<and>
      (case comma_semantic_phase_program_class_step phase cid of
         Comma_Phase_Class_Invalid \<Rightarrow> False
       | Comma_Phase_Class_Fork a delta \<Rightarrow>
           2 \<le> a \<and> a \<le> 9 \<and> delta = 0 \<and> D phase cid = a - 2
       | Comma_Phase_Class_Landmine delta \<Rightarrow> delta = 0 \<and> D phase cid = 8
       | Comma_Phase_Class_Continue next_phase next_class \<Rightarrow>
           next_phase = (phase+1) mod 924 \<and> next_class < 46 \<and>
           D phase cid = 9 + D next_phase next_class)"
  proof (cases "comma_semantic_phase_program_class_step phase cid")
    case Comma_Phase_Class_Invalid
    then show ?thesis using condition binding by (simp add: Let_def)
  next
    case (Comma_Phase_Class_Fork a delta)
    then show ?thesis using D_bound condition binding
      by (auto simp: Let_def split: if_splits; arith)
  next
    case (Comma_Phase_Class_Landmine delta)
    then show ?thesis using D_bound condition binding
      by (auto simp: Let_def split: if_splits)
  next
    case (Comma_Phase_Class_Continue next_phase next_class)
    then show ?thesis using D_bound condition binding
      by (auto simp: Let_def split: if_splits; arith)
  qed
qed

lemma comma_frontier_m204_rank_checked:
  assumes cert: "comma_frontier_m204_bellman D"
  shows "comma_phase_class_rank_check
    comma_semantic_phase_class_valid
    (\<lambda>phase cid. D phase cid div 9)
    comma_semantic_phase_program_class_step"
proof (unfold comma_phase_class_rank_check_def, intro allI impI)
  fix phase cid
  assume valid: "comma_semantic_phase_class_valid phase cid"
  have phase: "phase<924" and cid: "cid<46"
    using valid by (auto simp: comma_semantic_phase_class_valid_def)
  have row:
    "case comma_semantic_phase_program_class_step phase cid of
       Comma_Phase_Class_Invalid \<Rightarrow> False
     | Comma_Phase_Class_Fork a delta \<Rightarrow>
         2 \<le> a \<and> a \<le> 9 \<and> delta = 0 \<and> D phase cid = a-2
     | Comma_Phase_Class_Landmine delta \<Rightarrow>
         delta = 0 \<and> D phase cid = 8
     | Comma_Phase_Class_Continue next_phase next_class \<Rightarrow>
         next_phase = (phase+1) mod 924 \<and> next_class < 46 \<and>
         D phase cid = 9 + D next_phase next_class"
    using cert phase cid
    by (auto simp: comma_frontier_m204_bellman_def)
  show "case comma_semantic_phase_program_class_step phase cid of
    Comma_Phase_Class_Invalid \<Rightarrow> False
  | Comma_Phase_Class_Fork a delta \<Rightarrow> True
  | Comma_Phase_Class_Landmine delta \<Rightarrow> True
  | Comma_Phase_Class_Continue next_phase next_class \<Rightarrow>
      comma_semantic_phase_class_valid next_phase next_class \<and>
      D next_phase next_class div 9 < D phase cid div 9"
  proof (cases "comma_semantic_phase_program_class_step phase cid")
    case Comma_Phase_Class_Invalid
    then show ?thesis using row by simp
  next
    case (Comma_Phase_Class_Fork a delta)
    then show ?thesis by simp
  next
    case (Comma_Phase_Class_Landmine delta)
    then show ?thesis by simp
  next
    case (Comma_Phase_Class_Continue next_phase next_class)
    have next_phase: "next_phase=(phase+1) mod 924"
      and next_class: "next_class<46"
      and decrease: "D phase cid=9+D next_phase next_class"
      using row Comma_Phase_Class_Continue by simp_all
    have next_valid: "comma_semantic_phase_class_valid next_phase next_class"
      using next_phase next_class
      by (simp add: comma_semantic_phase_class_valid_def)
    have strict: "D next_phase next_class div 9 < D phase cid div 9"
      using decrease by simp
    show ?thesis using Comma_Phase_Class_Continue next_valid strict by simp
  qed
qed

lemma comma_frontier_m204_rank_bound:
  assumes cert: "comma_frontier_m204_bellman D"
      and valid: "comma_semantic_phase_class_valid phase cid"
  shows "D phase cid div 9 \<le> 26"
proof -
  have limits: "phase<924" "cid<46"
    using valid by (auto simp: comma_semantic_phase_class_valid_def)
  have "D phase cid \<le> 242"
    using cert limits by (auto simp: comma_frontier_m204_bellman_def)
  then show ?thesis by simp
qed

fun comma_frontier_m204_state_value ::
    "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> comma_decade_state \<Rightarrow> nat" where
  "comma_frontier_m204_state_value D (Comma_Decade phase off) =
    D phase (comma_offset_orbit off)"

lemma comma_frontier_m204_source_bellman:
  assumes cert: "comma_frontier_m204_bellman D"
    and admitted: "comma_decade_admitted source"
  shows "case comma_decade_control source of
      Comma_Decade_Fork a delta \<Rightarrow> comma_frontier_m204_state_value D source = a-2
    | Comma_Decade_Landmine delta \<Rightarrow> comma_frontier_m204_state_value D source = 8
    | Comma_Decade_Continue target \<Rightarrow> comma_frontier_m204_state_value D source =
        9 + comma_frontier_m204_state_value D target
    | Comma_Decade_Invalid \<Rightarrow> False"
proof -
  obtain phase off where source: "source = Comma_Decade phase off"
    by (cases source) auto
  have valid: "comma_semantic_phase_class_valid phase (comma_offset_orbit off)"
    by (rule comma_semantic_phase_class_source_valid) (use admitted source in simp)
  have phase: "phase < 924" and cid: "comma_offset_orbit off < 46"
    using valid by (auto simp: comma_semantic_phase_class_valid_def)
  have step:
    "comma_semantic_phase_program_class_step phase (comma_offset_orbit off) =
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control (Comma_Decade phase off))"
    using comma_semantic_phase_program_class_step_exact[OF phase cid]
      comma_semantic_phase_class_source_control[of phase off] admitted source by simp
  have row:
    "case comma_semantic_phase_program_class_step phase (comma_offset_orbit off) of
       Comma_Phase_Class_Invalid \<Rightarrow> False
     | Comma_Phase_Class_Fork a delta \<Rightarrow>
         2 \<le> a \<and> a \<le> 9 \<and> delta = 0 \<and> D phase (comma_offset_orbit off) = a-2
     | Comma_Phase_Class_Landmine delta \<Rightarrow>
         delta = 0 \<and> D phase (comma_offset_orbit off) = 8
     | Comma_Phase_Class_Continue next_phase next_class \<Rightarrow>
         next_phase = (phase+1) mod 924 \<and> next_class < 46 \<and>
         D phase (comma_offset_orbit off) = 9 + D next_phase next_class"
    using cert phase cid by (auto simp: comma_frontier_m204_bellman_def)
  show ?thesis
  proof (cases "comma_decade_control (Comma_Decade phase off)")
    case (Comma_Decade_Fork a delta)
    show ?thesis using row
      by (auto simp only: source step Comma_Decade_Fork
        comma_phase_classify_decade_control.simps comma_phase_class_action.case
        comma_decade_outcome.case comma_frontier_m204_state_value.simps)
  next
    case (Comma_Decade_Landmine delta)
    show ?thesis using row
      by (auto simp only: source step Comma_Decade_Landmine
        comma_phase_classify_decade_control.simps comma_phase_class_action.case
        comma_decade_outcome.case comma_frontier_m204_state_value.simps)
  next
    case (Comma_Decade_Continue target)
    obtain next_phase next_off where target: "target = Comma_Decade next_phase next_off"
      by (cases target) auto
    show ?thesis using row
      by (auto simp only: source step Comma_Decade_Continue target
        comma_phase_classify_decade_control.simps comma_phase_class_action.case
        comma_decade_outcome.case comma_frontier_m204_state_value.simps)
  next
    case Comma_Decade_Invalid
    show ?thesis using row
      by (auto simp only: source step Comma_Decade_Invalid
        comma_phase_classify_decade_control.simps comma_phase_class_action.case
        comma_decade_outcome.case comma_frontier_m204_state_value.simps)
  qed
qed

lemma comma_frontier_m204_summary_value:
  assumes cert: "comma_frontier_m204_bellman D"
    and summary: "comma_decade_exact_summary source h tau"
    and admitted: "comma_decade_admitted source"
  shows "comma_frontier_m204_state_value D source = comma_terminal_weight_encode h tau"
  using summary admitted
proof (induction rule: comma_decade_exact_summary.induct)
  case (fork source a)
  have step: "comma_frontier_m204_state_value D source = a-2"
    using comma_frontier_m204_source_bellman[OF cert fork.prems] fork.hyps by simp
  show ?case using step by (simp add: comma_terminal_weight_encode_def)
next
  case (landmine source)
  have step: "comma_frontier_m204_state_value D source = 8"
    using comma_frontier_m204_source_bellman[OF cert landmine.prems] landmine.hyps by simp
  show ?case using step by (simp add: comma_terminal_weight_encode_def)
next
  case (crossing source target h tau)
  have target_admitted: "comma_decade_admitted target"
    by (rule comma_decade_control_closed(2)[OF crossing.prems crossing.hyps(1) refl])
  have step: "comma_frontier_m204_state_value D source =
      9 + comma_frontier_m204_state_value D target"
    using comma_frontier_m204_source_bellman[OF cert crossing.prems] crossing.hyps(1) by simp
  have tail: "comma_frontier_m204_state_value D target = comma_terminal_weight_encode h tau"
    by (rule crossing.IH[OF target_admitted])
  show ?case using step tail by (simp add: comma_terminal_weight_encode_def algebra_simps)
qed

text \<open>
This instantiation already preserves exact B32 terminal labels and the
`comma_decade_exact_summary` property from the existing verified rank-to-B32
bridge.  It does not assert a concrete MDD root equality.
\<close>

theorem comma_frontier_m204_B32_from_checked_bellman:
  fixes source :: comma_decade_state
  assumes cert: "comma_frontier_m204_bellman D"
      and admitted: "comma_decade_admitted source"
  shows "\<exists>h tau. h \<le> 26 \<and>
    comma_decade_block_power 5 source = Comma_Block_Stop h tau \<and>
    comma_residual_block 32 (h,tau) = Comma_Residual_Stop h tau \<and>
    comma_decade_exact_summary source h tau"
proof (rule comma_phase_class_rank_B32
    [where class_of=comma_offset_orbit
      and valid=comma_semantic_phase_class_valid
      and rank="\<lambda>r c. D r c div 9"
      and step=comma_semantic_phase_program_class_step
      and s=source])
  show "comma_phase_class_rank_check
     comma_semantic_phase_class_valid (\<lambda>r c. D r c div 9)
     comma_semantic_phase_program_class_step"
    by (rule comma_frontier_m204_rank_checked[OF cert])
next
  fix phase x
  assume a: "comma_decade_admitted (Comma_Decade phase x)"
  show "comma_semantic_phase_class_valid phase (comma_offset_orbit x)"
    by (rule comma_semantic_phase_class_source_valid[OF a])
next
  fix phase x
  assume a: "comma_decade_admitted (Comma_Decade phase x)"
  have valid: "comma_semantic_phase_class_valid phase (comma_offset_orbit x)"
    by (rule comma_semantic_phase_class_source_valid[OF a])
  have exact:
    "comma_semantic_phase_program_class_step phase (comma_offset_orbit x) =
     comma_semantic_phase_class_step phase (comma_offset_orbit x)"
    using valid by (auto simp: comma_semantic_phase_class_valid_def
      intro: comma_semantic_phase_program_class_step_exact)
  show "comma_semantic_phase_program_class_step phase (comma_offset_orbit x) =
       comma_phase_classify_decade_control comma_offset_orbit
          (comma_decade_control (Comma_Decade phase x))"
    using exact comma_semantic_phase_class_source_control[OF a] by simp
next
  fix phase cid
  assume valid: "comma_semantic_phase_class_valid phase cid"
  show "D phase cid div 9 \<le> 26"
    by (rule comma_frontier_m204_rank_bound[OF cert valid])
next
  show "comma_decade_admitted source" by (rule admitted)
qed

text \<open>The Stop action is derived from the independently checked summary;
the summary induction also authenticates the Bellman value as its encoding.\<close>

theorem comma_frontier_m204_exact_stop_from_checked_bellman:
  assumes cert: "comma_frontier_m204_bellman D"
    and phase: "phase < 924" and root: "root < 46"
  shows "\<exists>h tau. h \<le> 26 \<and>
    comma_decade_exact_summary (Comma_Decade phase (comma_offset_representatives ! root)) h tau \<and>
    D phase root = comma_terminal_weight_encode h tau \<and>
    comma_semantic_b1_action_power 5 phase root =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode h tau) \<and>
    comma_terminal_weight_encode h tau \<le> 242"
proof -
  have representative: "comma_offset_representatives ! root \<le> 90"
    using comma_orbit_representative_index[OF root] by blast
  have representative_class: "comma_offset_orbit (comma_offset_representatives ! root) = root"
    using comma_orbit_representative_index[OF root] by blast
  have admitted: "comma_decade_admitted
      (Comma_Decade phase (comma_offset_representatives ! root))"
    using phase representative by simp
  obtain h tau where bound: "h \<le> 26"
    and summary: "comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives ! root)) h tau"
    using comma_frontier_m204_B32_from_checked_bellman[OF cert admitted] by blast
  have action: "comma_semantic_b1_action_power 5 phase root =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode h tau) \<and>
      comma_terminal_weight_encode h tau \<le> 242"
    by (rule comma_semantic_b1_action_stop_from_exact_summary[OF phase root summary bound])
  have encoded_weight: "D phase root = comma_terminal_weight_encode h tau"
    using comma_frontier_m204_summary_value[OF cert summary admitted] representative_class by simp
  show ?thesis using bound summary encoded_weight action by blast
qed

lemma comma_frontier_m204_exact_weight_from_checked_bellman:
  assumes cert: "comma_frontier_m204_bellman D"
    and phase: "phase < 924" and root: "root < 46"
  shows "comma_semantic_b1_action_power 5 phase root =
    Comma_Semantic_B1_Stop (D phase root)"
proof -
  obtain h tau where encoded:
      "D phase root = comma_terminal_weight_encode h tau"
    and stopped: "comma_semantic_b1_action_power 5 phase root =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode h tau)"
    using comma_frontier_m204_exact_stop_from_checked_bellman[OF cert phase root] by blast
  show ?thesis using stopped encoded by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Conditional M204 rank and exact Stop action"
    @{thms comma_frontier_m204_code_to_bellman
      comma_frontier_m204_rank_checked comma_frontier_m204_rank_bound
      comma_frontier_m204_source_bellman comma_frontier_m204_summary_value
      comma_frontier_m204_B32_from_checked_bellman
      comma_frontier_m204_exact_stop_from_checked_bellman
      comma_frontier_m204_exact_weight_from_checked_bellman};
\<close>

end
