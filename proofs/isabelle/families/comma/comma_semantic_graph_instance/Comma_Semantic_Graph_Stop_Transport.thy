theory Comma_Semantic_Graph_Stop_Transport
  imports Comma_Semantic_Graph_Action_Power
    Comma_Semantic_B1.Comma_Semantic_Weighted_Action
    Comma_Semantic_B1.Comma_Semantic_Graph_Phase_Fold
begin

definition comma_semantic_graph_root_weighted_action ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result" where
  "comma_semantic_graph_root_weighted_action phase root =
    (case comma_semantic_graph_root_action phase root of
       Comma_Semantic_B1_Live next_root \<Rightarrow>
         Comma_Semantic_B1_Continue next_root
     | Comma_Semantic_B1_Stop D \<Rightarrow>
         Comma_Semantic_B1_Stop_At (D mod 9) (D div 9)
     | Comma_Semantic_B1_Invalid \<Rightarrow>
         Comma_Semantic_B1_Weighted_Invalid)"

lemma comma_semantic_graph_root_weighted_action_exact:
  "comma_semantic_b1_weighted_encode
      (comma_semantic_graph_root_weighted_action phase root) =
    comma_semantic_graph_root_action phase root"
  by (cases "comma_semantic_graph_root_action phase root")
    (simp_all add: comma_semantic_graph_root_weighted_action_def
      div_mult_mod_eq)

lemma comma_semantic_graph_weighted_power_exact:
  "comma_semantic_b1_weighted_encode
      (comma_semantic_b1_weighted_action_power k
        comma_semantic_graph_root_weighted_action phase root) =
    comma_semantic_graph_action_power k phase root"
proof -
  have power_from:
    "comma_semantic_b1_action_power_from k
        (\<lambda>r i. comma_semantic_b1_weighted_encode
          (comma_semantic_graph_root_weighted_action r i)) =
      comma_semantic_graph_action_power k"
  proof (induction k)
    case 0
    then show ?case
      by (rule ext)+
        (simp add: comma_semantic_graph_root_weighted_action_exact)
  next
    case (Suc k)
    have same_functions:
      "comma_semantic_b1_action_power_from k
          (\<lambda>r i. comma_semantic_b1_weighted_encode
            (comma_semantic_graph_root_weighted_action r i)) =
        comma_semantic_graph_action_power k"
      by (rule Suc.IH)
    show ?case
      by (simp only: comma_semantic_b1_action_power_from.simps
        comma_semantic_graph_action_power.simps same_functions)
  qed
  have power_from_phase:
    "comma_semantic_b1_action_power_from k
        (\<lambda>r i. comma_semantic_b1_weighted_encode
          (comma_semantic_graph_root_weighted_action r i)) phase =
      comma_semantic_graph_action_power k phase"
    by (rule fun_cong[OF power_from])
  have power_from_point:
    "comma_semantic_b1_action_power_from k
        (\<lambda>r i. comma_semantic_b1_weighted_encode
          (comma_semantic_graph_root_weighted_action r i)) phase root =
      comma_semantic_graph_action_power k phase root"
    by (rule fun_cong[OF power_from_phase])
  show ?thesis
    using comma_semantic_b1_weighted_action_power_encode[of k
        comma_semantic_graph_root_weighted_action phase root]
      power_from_point by simp
qed

text \<open>
The graph root is an occurrence-independent orbit key.  This interface
transports its checked action back to the canonical decade control and lifts
an arbitrary phase/root rank to the admitted decade rectangle.  It does not
identify graph node addresses with decade rank values.
\<close>

lemma comma_semantic_graph_root_atom_exact:
  assumes phase: "phase<924" and root: "root<46"
  shows "comma_semantic_graph_root_action phase root =
    comma_semantic_b1_of_word
      (comma_word_project comma_offset_orbit
        (comma_decade_block_atom
          (Comma_Decade phase (comma_offset_representatives!root))))"
proof -
  have root_exact:
    "comma_semantic_graph_root_action phase root = comma_semantic_b1 phase root"
    by (rule comma_semantic_graph_root_action_exact
      [OF comma_semantic_graph_valid_checked phase root])
  have orbit_exact:
    "comma_semantic_b1 phase root =
      comma_semantic_b1_of_word (comma_orbit_word 0 phase root)"
    by (rule comma_semantic_b1_exact_orbit[OF phase root])
  show ?thesis
    using root_exact orbit_exact phase root
    by (simp add: comma_orbit_word_def comma_decade_block_power.simps)
qed

lemma comma_semantic_graph_root_evaluation:
  assumes phase: "phase<924" and root: "root<46"
  shows "\<exists>result. comma_semantic_b1_graph_eval
      comma_semantic_graph_nodes (comma_semantic_graph_root_ids!root) phase=
        Some result \<and> comma_semantic_graph_root_action phase root=result"
proof -
  have graph:
    "comma_semantic_b1_graph_completed_valid comma_semantic_graph_bindings
      comma_semantic_graph_nodes"
    by (rule comma_semantic_graph_valid_checked)
  obtain binding where member: "binding\<in>set comma_semantic_graph_bindings"
    and source: "comma_semantic_b1_binding_source binding=
      Comma_Entry 1 0 (comma_offset_representatives!root)"
    and cid: "comma_semantic_b1_binding_cid binding=
      comma_semantic_graph_root_ids!root"
    using comma_semantic_graph_root_binding_exists[OF root] by blast
  have correct_all:
    "\<forall>cid. comma_semantic_b1_graph_correct_at
      comma_semantic_graph_bindings comma_semantic_graph_nodes cid"
    by (rule comma_semantic_b1_graph_completed_eval_refines_endpoint[OF graph])
  have correct:
    "comma_semantic_b1_graph_correct_at comma_semantic_graph_bindings
      comma_semantic_graph_nodes (comma_semantic_graph_root_ids!root)"
    using correct_all cid member by blast
  have evaluation:
    "comma_semantic_b1_graph_eval comma_semantic_graph_nodes
        (comma_semantic_graph_root_ids!root) phase=
      Some (comma_semantic_b1_round_output phase
        (Comma_Entry 1 0 (comma_offset_representatives!root)))"
    using correct member source cid
    by (auto simp: comma_semantic_b1_graph_correct_at_def)
  have selected:
    "comma_semantic_graph_root_action phase root=
      comma_semantic_b1_round_output phase
        (Comma_Entry 1 0 (comma_offset_representatives!root))"
    using evaluation by (simp add: comma_semantic_graph_root_action_def)
  show ?thesis
    by (rule exI[where x="comma_semantic_b1_round_output phase
      (Comma_Entry 1 0 (comma_offset_representatives!root))"])
      (rule conjI[OF evaluation selected])
qed

lemma comma_semantic_graph_root_control_transport:
  assumes phase: "phase<924"
    and root: "root<46"
    and offset: "x\<le>90"
    and orbit: "comma_offset_orbit x=root"
  shows
    "comma_decade_control (Comma_Decade phase x) =
        Comma_Decade_Continue (Comma_Decade next_phase next_offset) \<Longrightarrow>
      next_phase=(phase+1) mod 924 \<and> next_offset\<le>90 \<and>
      comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Live (comma_offset_orbit next_offset)"
    "comma_decade_control (Comma_Decade phase x) =
        Comma_Decade_Fork arm delta \<Longrightarrow>
      delta=0 \<and> comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 (Comma_Terminal_Fork arm))"
    "comma_decade_control (Comma_Decade phase x) =
        Comma_Decade_Landmine delta \<Longrightarrow>
      delta=0 \<and> comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 Comma_Terminal_Landmine)"
proof -
  let ?representative = "comma_offset_representatives!root"
  let ?representative_state = "Comma_Decade phase ?representative"
  have representative_bound: "?representative\<le>90"
    by (rule comma_orbit_representative_index(1)[OF root])
  have representative_orbit: "comma_offset_orbit ?representative=root"
    by (rule comma_orbit_representative_index(2)[OF root])
  have representative_control:
    "comma_decade_control (Comma_Decade phase x) =
      comma_decade_control ?representative_state"
    by (rule comma_decade_control_orbit_congruent[OF offset representative_bound])
      (simp add: orbit representative_orbit)
  have representative_phase: "comma_decade_admitted ?representative_state"
    using phase representative_bound by simp
  have action:
    "comma_semantic_graph_root_action phase root =
      comma_semantic_b1_of_word
        (comma_word_project comma_offset_orbit
          (comma_decade_block_atom ?representative_state))"
    by (rule comma_semantic_graph_root_atom_exact[OF phase root])

  show
    "comma_decade_control (Comma_Decade phase x) =
        Comma_Decade_Continue (Comma_Decade next_phase next_offset) \<Longrightarrow>
      next_phase=(phase+1) mod 924 \<and> next_offset\<le>90 \<and>
      comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Live (comma_offset_orbit next_offset)"
  proof -
    assume control:
      "comma_decade_control (Comma_Decade phase x) =
        Comma_Decade_Continue (Comma_Decade next_phase next_offset)"
    have valid_state: "comma_decade_admitted (Comma_Decade phase x)"
      using phase offset by simp
    have next_phase: "next_phase=(phase+1) mod 924"
      by (rule comma_decade_continue_helix(1)[OF valid_state control])
    have next_offset: "next_offset\<le>90"
      by (rule comma_decade_continue_helix(2)[OF valid_state control])
    have representative_step:
      "comma_decade_control ?representative_state =
        Comma_Decade_Continue (Comma_Decade next_phase next_offset)"
      using representative_control control by simp
    have next_admitted:
      "comma_decade_admitted (Comma_Decade next_phase next_offset)"
      using comma_decade_control_closed(2)
        [OF representative_phase representative_step] by simp
    have atom:
      "comma_decade_block_atom ?representative_state =
        Comma_Block_Live (Comma_Decade next_phase next_offset)"
      using representative_phase representative_step next_admitted
      by (simp add: comma_decade_block_atom_def)
    have graph_live:
      "comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Live (comma_offset_orbit next_offset)"
      using action atom by simp
    show "next_phase=(phase+1) mod 924 \<and> next_offset\<le>90 \<and>
        comma_semantic_graph_root_action phase root =
          Comma_Semantic_B1_Live (comma_offset_orbit next_offset)"
      using next_phase next_offset graph_live by blast
  qed

  show
    "comma_decade_control (Comma_Decade phase x) =
        Comma_Decade_Fork arm delta \<Longrightarrow>
      delta=0 \<and> comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 (Comma_Terminal_Fork arm))"
  proof -
    assume control:
      "comma_decade_control (Comma_Decade phase x) =
        Comma_Decade_Fork arm delta"
    have valid_state: "comma_decade_admitted (Comma_Decade phase x)"
      using phase offset by simp
    have delta: "delta=0"
      by (rule comma_decade_terminal_delta(1)[OF valid_state control])
    have representative_step:
      "comma_decade_control ?representative_state =
        Comma_Decade_Fork arm delta"
      using representative_control control by simp
    have atom:
      "comma_decade_block_atom ?representative_state =
        Comma_Block_Stop 0 (Comma_Terminal_Fork arm)"
      using representative_phase representative_step delta
      by (simp add: comma_decade_block_atom_def)
    have graph_stop:
      "comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 (Comma_Terminal_Fork arm))"
      using action atom by simp
    show "delta=0 \<and> comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 (Comma_Terminal_Fork arm))"
      using delta graph_stop by blast
  qed

  show
    "comma_decade_control (Comma_Decade phase x) =
        Comma_Decade_Landmine delta \<Longrightarrow>
      delta=0 \<and> comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 Comma_Terminal_Landmine)"
  proof -
    assume control:
      "comma_decade_control (Comma_Decade phase x) =
        Comma_Decade_Landmine delta"
    have valid_state: "comma_decade_admitted (Comma_Decade phase x)"
      using phase offset by simp
    have delta: "delta=0"
      by (rule comma_decade_terminal_delta(2)[OF valid_state control])
    have representative_step:
      "comma_decade_control ?representative_state =
        Comma_Decade_Landmine delta"
      using representative_control control by simp
    have atom:
      "comma_decade_block_atom ?representative_state =
        Comma_Block_Stop 0 Comma_Terminal_Landmine"
      using representative_phase representative_step delta
      by (simp add: comma_decade_block_atom_def)
    have graph_stop:
      "comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 Comma_Terminal_Landmine)"
      using action atom by simp
    show "delta=0 \<and> comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 Comma_Terminal_Landmine)"
      using delta graph_stop by blast
  qed
qed

lemma comma_semantic_graph_root_action_not_invalid:
  assumes phase: "phase<924" and root: "root<46"
  shows "comma_semantic_graph_root_action phase root \<noteq>
    Comma_Semantic_B1_Invalid"
proof -
  let ?representative = "comma_offset_representatives!root"
  let ?state = "Comma_Decade phase ?representative"
  have representative_bound: "?representative\<le>90"
    by (rule comma_orbit_representative_index(1)[OF root])
  have representative_orbit: "comma_offset_orbit ?representative=root"
    by (rule comma_orbit_representative_index(2)[OF root])
  have valid: "comma_decade_admitted ?state"
    using phase representative_bound by simp
  have control_valid:
    "comma_decade_control ?state \<noteq> Comma_Decade_Invalid"
    by (rule comma_decade_control_closed(1)[OF valid refl])
  show ?thesis
  proof (cases "comma_decade_control ?state")
    case (Comma_Decade_Continue q)
    obtain next_phase next_offset where q:
      "q=Comma_Decade next_phase next_offset"
      by (cases q) auto
    have image:
      "comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Live (comma_offset_orbit next_offset)"
      using comma_semantic_graph_root_control_transport(1)
        [OF phase root representative_bound representative_orbit]
        Comma_Decade_Continue q by blast
    then show ?thesis by simp
  next
    case (Comma_Decade_Fork arm delta)
    have image:
      "comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 (Comma_Terminal_Fork arm))"
      using comma_semantic_graph_root_control_transport(2)
        [OF phase root representative_bound representative_orbit]
        Comma_Decade_Fork by blast
    then show ?thesis by simp
  next
    case (Comma_Decade_Landmine delta)
    have image:
      "comma_semantic_graph_root_action phase root =
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 Comma_Terminal_Landmine)"
      using comma_semantic_graph_root_control_transport(3)
        [OF phase root representative_bound representative_orbit]
        Comma_Decade_Landmine by blast
    then show ?thesis by simp
  next
    case Comma_Decade_Invalid
    then show ?thesis using control_valid by simp
  qed
qed

lemma comma_decade_exact_summary_same_control:
  assumes controls: "comma_decade_control source=comma_decade_control target"
    and summary: "comma_decade_exact_summary source height terminal"
  shows "comma_decade_exact_summary target height terminal"
  using summary controls
proof (induction rule: comma_decade_exact_summary.induct)
  case (fork source arm)
  have target_control:
    "comma_decade_control target=Comma_Decade_Fork arm 0"
    using fork.hyps fork.prems by simp
  show ?case by (rule comma_decade_exact_summary.fork[OF target_control])
next
  case (landmine source)
  have target_control:
    "comma_decade_control target=Comma_Decade_Landmine 0"
    using landmine.hyps landmine.prems by simp
  show ?case by (rule comma_decade_exact_summary.landmine[OF target_control])
next
  case (crossing source successor height terminal)
  have target_control:
    "comma_decade_control target=Comma_Decade_Continue successor"
    using crossing.hyps crossing.prems by simp
  have target_summary: "comma_decade_exact_summary successor height terminal"
    using crossing.hyps by blast
  show ?case
    by (rule comma_decade_exact_summary.crossing[OF target_control target_summary])
qed

lemma comma_semantic_graph_root_live_control:
  assumes phase: "phase<924" and root: "root<46"
    and live: "comma_semantic_graph_root_action phase root=
      Comma_Semantic_B1_Live child"
  obtains next_offset where
    "comma_decade_control
        (Comma_Decade phase (comma_offset_representatives!root)) =
      Comma_Decade_Continue
        (Comma_Decade ((phase+1) mod 924) next_offset)"
    "next_offset\<le>90"
    "comma_offset_orbit next_offset=child"
proof -
  let ?representative = "comma_offset_representatives!root"
  let ?source = "Comma_Decade phase ?representative"
  have representative_bound: "?representative\<le>90"
    by (rule comma_orbit_representative_index(1)[OF root])
  have representative_orbit: "comma_offset_orbit ?representative=root"
    by (rule comma_orbit_representative_index(2)[OF root])
  have admitted: "comma_decade_admitted ?source"
    using phase representative_bound by simp
  have control_valid: "comma_decade_control ?source\<noteq>Comma_Decade_Invalid"
    by (rule comma_decade_control_closed(1)[OF admitted refl])
  show thesis
  proof (cases "comma_decade_control ?source")
    case (Comma_Decade_Continue continuation)
    obtain next_phase next_offset where continuation_shape:
      "continuation=Comma_Decade next_phase next_offset"
      by (cases continuation) auto
    have image:
      "comma_semantic_graph_root_action phase root=
        Comma_Semantic_B1_Live (comma_offset_orbit next_offset)"
      using comma_semantic_graph_root_control_transport(1)
        [OF phase root representative_bound representative_orbit]
        Comma_Decade_Continue continuation_shape by blast
    have phase_exact: "next_phase=(phase+1) mod 924"
      and offset_bound: "next_offset\<le>90"
      using comma_semantic_graph_root_control_transport(1)
        [OF phase root representative_bound representative_orbit]
        Comma_Decade_Continue continuation_shape by auto
    have child_exact: "comma_offset_orbit next_offset=child"
      using image live by simp
    have control_exact:
      "comma_decade_control ?source = Comma_Decade_Continue
        (Comma_Decade ((phase+1) mod 924) next_offset)"
      using Comma_Decade_Continue continuation_shape phase_exact by simp
    show thesis by (rule that[OF control_exact offset_bound child_exact])
  next
    case (Comma_Decade_Fork arm delta)
    have image:
      "comma_semantic_graph_root_action phase root=
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 (Comma_Terminal_Fork arm))"
      using comma_semantic_graph_root_control_transport(2)
        [OF phase root representative_bound representative_orbit]
        Comma_Decade_Fork by blast
    show thesis using image live by simp
  next
    case (Comma_Decade_Landmine delta)
    have image:
      "comma_semantic_graph_root_action phase root=
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 Comma_Terminal_Landmine)"
      using comma_semantic_graph_root_control_transport(3)
        [OF phase root representative_bound representative_orbit]
        Comma_Decade_Landmine by blast
    show thesis using image live by simp
  next
    case Comma_Decade_Invalid
    then show thesis using control_valid by simp
  qed
qed

lemma comma_semantic_graph_root_weighted_action_admitted:
  assumes phase: "phase<924" and root: "root<46"
  shows "comma_semantic_b1_weighted_result_admitted
      (comma_semantic_graph_root_weighted_action phase root)"
proof -
  have not_invalid:
    "comma_semantic_graph_root_action phase root\<noteq>
      Comma_Semantic_B1_Invalid"
    by (rule comma_semantic_graph_root_action_not_invalid[OF phase root])
  show ?thesis
  proof (cases "comma_semantic_graph_root_action phase root")
    case (Comma_Semantic_B1_Live child)
    obtain offset where orbit: "comma_offset_orbit offset=child"
      using comma_semantic_graph_root_live_control[OF phase root Comma_Semantic_B1_Live]
      by blast
    have "comma_offset_orbit offset<46" by (rule comma_offset_orbit_bound)
    then have "child<46" using orbit by simp
    then show ?thesis
      using Comma_Semantic_B1_Live
      by (simp add: comma_semantic_graph_root_weighted_action_def)
  next
    case (Comma_Semantic_B1_Stop D)
    show ?thesis
      using Comma_Semantic_B1_Stop
      by (simp add: comma_semantic_graph_root_weighted_action_def)
  next
    case Comma_Semantic_B1_Invalid
    then show ?thesis using not_invalid by simp
  qed
qed

lemma comma_semantic_graph_root_stop_summary:
  assumes phase: "phase<924" and root: "root<46"
    and stopped: "comma_semantic_graph_root_action phase root=
      Comma_Semantic_B1_Stop D"
  obtains terminal where
    "D=comma_terminal_weight_encode 0 terminal"
    "comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives!root)) 0 terminal"
proof -
  let ?representative = "comma_offset_representatives!root"
  let ?source = "Comma_Decade phase ?representative"
  have representative_bound: "?representative\<le>90"
    by (rule comma_orbit_representative_index(1)[OF root])
  have representative_orbit: "comma_offset_orbit ?representative=root"
    by (rule comma_orbit_representative_index(2)[OF root])
  have admitted: "comma_decade_admitted ?source"
    using phase representative_bound by simp
  have control_valid: "comma_decade_control ?source\<noteq>Comma_Decade_Invalid"
    by (rule comma_decade_control_closed(1)[OF admitted refl])
  show thesis
  proof (cases "comma_decade_control ?source")
    case (Comma_Decade_Continue continuation)
    obtain next_phase next_offset where continuation_shape:
      "continuation=Comma_Decade next_phase next_offset"
      by (cases continuation) auto
    have image:
      "comma_semantic_graph_root_action phase root=
        Comma_Semantic_B1_Live (comma_offset_orbit next_offset)"
      using comma_semantic_graph_root_control_transport(1)
        [OF phase root representative_bound representative_orbit]
        Comma_Decade_Continue continuation_shape by blast
    show thesis using image stopped by simp
  next
    case (Comma_Decade_Fork arm delta)
    have image:
      "delta=0 \<and> comma_semantic_graph_root_action phase root=
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 (Comma_Terminal_Fork arm))"
      using comma_semantic_graph_root_control_transport(2)
        [OF phase root representative_bound representative_orbit]
        Comma_Decade_Fork by blast
    have terminal: "D=comma_terminal_weight_encode 0 (Comma_Terminal_Fork arm)"
      using image stopped by simp
    have summary:
      "comma_decade_exact_summary ?source 0 (Comma_Terminal_Fork arm)"
      by (rule comma_decade_exact_summary.fork) (use Comma_Decade_Fork image in simp)
    show thesis by (rule that[OF terminal summary])
  next
    case (Comma_Decade_Landmine delta)
    have image:
      "delta=0 \<and> comma_semantic_graph_root_action phase root=
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode 0 Comma_Terminal_Landmine)"
      using comma_semantic_graph_root_control_transport(3)
        [OF phase root representative_bound representative_orbit]
        Comma_Decade_Landmine by blast
    have terminal: "D=comma_terminal_weight_encode 0 Comma_Terminal_Landmine"
      using image stopped by simp
    have summary:
      "comma_decade_exact_summary ?source 0 Comma_Terminal_Landmine"
      by (rule comma_decade_exact_summary.landmine) (use Comma_Decade_Landmine image in simp)
    show thesis by (rule that[OF terminal summary])
  next
    case Comma_Decade_Invalid
    then show thesis using control_valid by simp
  qed
qed

theorem comma_semantic_graph_stop_within_summary:
  assumes phase: "phase<924" and root: "root<46"
    and within: "comma_semantic_b1_stop_within k
      comma_semantic_graph_root_action phase root"
  shows "\<exists>height terminal. height\<le>k \<and>
    comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives!root)) height terminal"
  using phase root within
proof (induction k arbitrary: phase root)
  case 0
  then show ?case
    by (auto simp: comma_semantic_b1_stop_within.simps
      elim!: comma_semantic_graph_root_stop_summary)
next
  case (Suc k)
  have phase_bound: "phase<924" and root_bound: "root<46"
    and within:
      "comma_semantic_b1_stop_within (Suc k)
        comma_semantic_graph_root_action phase root"
    using Suc.prems by auto
  have predecessor:
    "comma_semantic_b1_stop_within k comma_semantic_graph_root_action phase root
    \<or> (\<exists>child. comma_semantic_graph_root_action phase root=
        Comma_Semantic_B1_Live child \<and>
      comma_semantic_b1_stop_within k comma_semantic_graph_root_action
        ((phase+1) mod 924) child)"
    using within by simp
  show ?case
  proof (cases "comma_semantic_b1_stop_within k
      comma_semantic_graph_root_action phase root")
    case True
    obtain height terminal where height_bound: "height\<le>k"
      and summary:
        "comma_decade_exact_summary
          (Comma_Decade phase (comma_offset_representatives!root)) height terminal"
      using Suc.IH[OF phase_bound root_bound True] by blast
    have height_suc: "height\<le>Suc k"
      using height_bound by (rule le_SucI)
    show ?thesis
      by (rule exI[where x=height], rule exI[where x=terminal],
        rule conjI[OF height_suc summary])
  next
    case False
    obtain child where live:
        "comma_semantic_graph_root_action phase root=
          Comma_Semantic_B1_Live child"
      and child_within:
        "comma_semantic_b1_stop_within k comma_semantic_graph_root_action
          ((phase+1) mod 924) child"
      using predecessor False by blast
    obtain next_offset where source_control:
        "comma_decade_control
            (Comma_Decade phase (comma_offset_representatives!root)) =
          Comma_Decade_Continue
            (Comma_Decade ((phase+1) mod 924) next_offset)"
      and next_bound: "next_offset\<le>90"
      and next_orbit: "comma_offset_orbit next_offset=child"
      by (rule comma_semantic_graph_root_live_control[OF phase_bound root_bound live])
    have child_bound: "child<46"
    proof -
      have "comma_offset_orbit next_offset<46"
        by (rule comma_offset_orbit_bound)
      then show ?thesis using next_orbit by simp
    qed
    have next_phase_bound: "((phase+1) mod 924)<924" by simp
    obtain height terminal where height_bound: "height\<le>k"
      and representative_summary:
        "comma_decade_exact_summary
          (Comma_Decade ((phase+1) mod 924)
            (comma_offset_representatives!child)) height terminal"
      using Suc.IH[OF next_phase_bound child_bound child_within] by blast
    have representative_bound:
        "comma_offset_representatives!child\<le>90"
      by (rule comma_orbit_representative_index(1)[OF child_bound])
    have representative_orbit:
        "comma_offset_orbit (comma_offset_representatives!child)=child"
      by (rule comma_orbit_representative_index(2)[OF child_bound])
    have same_orbit:
      "comma_offset_orbit (comma_offset_representatives!child)=
        comma_offset_orbit next_offset"
      using representative_orbit next_orbit by simp
    have same_control:
      "comma_decade_control
          (Comma_Decade ((phase+1) mod 924)
            (comma_offset_representatives!child)) =
       comma_decade_control
          (Comma_Decade ((phase+1) mod 924) next_offset)"
      by (rule comma_decade_control_orbit_congruent
        [OF representative_bound next_bound same_orbit])
    have next_summary:
      "comma_decade_exact_summary
        (Comma_Decade ((phase+1) mod 924) next_offset) height terminal"
      by (rule comma_decade_exact_summary_same_control
        [OF same_control representative_summary])
    have summary:
      "comma_decade_exact_summary
        (Comma_Decade phase (comma_offset_representatives!root)
          ) (Suc height) terminal"
      by (rule comma_decade_exact_summary.crossing[OF source_control next_summary])
    have height_suc: "Suc height\<le>Suc k"
      using height_bound by simp
    show ?thesis
      by (rule exI[where x="Suc height"], rule exI[where x=terminal],
        rule conjI[OF height_suc summary])
  qed
qed

theorem comma_semantic_graph_stop_within_exact_action:
  assumes phase: "phase<924" and root: "root<46"
    and within: "comma_semantic_b1_stop_within k
      comma_semantic_graph_root_action phase root"
    and bound: "k\<le>26"
  obtains height terminal where
    "height\<le>k"
    "comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives!root))
      height terminal"
    "comma_semantic_graph_action_power 5 phase root =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
    "comma_semantic_b1_action_power 5 phase root =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
    "comma_semantic_b1_weighted_encode
      (comma_semantic_b1_weighted_action_power 5
        comma_semantic_graph_root_weighted_action phase root) =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
    "comma_terminal_weight_encode height terminal\<le>242"
proof -
  obtain height terminal where height: "height\<le>k"
    and summary:
      "comma_decade_exact_summary
        (Comma_Decade phase (comma_offset_representatives!root))
        height terminal"
    using comma_semantic_graph_stop_within_summary[OF phase root within]
    by blast
  have height26: "height\<le>26" using height bound by arith
  have exact:
    "comma_semantic_graph_action_power 5 phase root =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
    and terminal_bound:
      "comma_terminal_weight_encode height terminal\<le>242"
    using comma_semantic_graph_stop_from_exact_summary
      [OF phase root summary height26] by auto
  have semantic:
    "comma_semantic_b1_action_power 5 phase root =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
    using comma_semantic_graph_action_power_refines[OF phase root]
      exact by simp
  have weighted:
    "comma_semantic_b1_weighted_encode
      (comma_semantic_b1_weighted_action_power 5
        comma_semantic_graph_root_weighted_action phase root) =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
    using comma_semantic_graph_weighted_power_exact exact by simp
  show thesis
    by (rule that[OF height summary exact semantic weighted terminal_bound])
qed

corollary comma_semantic_graph_stop242_from_stop_within:
  assumes phase: "phase<924" and root: "root<46"
    and within: "comma_semantic_b1_stop_within 26
      comma_semantic_graph_root_action phase root"
  shows "\<exists>D. comma_semantic_graph_action_power 5 phase root=
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
proof -
  obtain height terminal where exact:
      "comma_semantic_graph_action_power 5 phase root =
        Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
    and limit: "comma_terminal_weight_encode height terminal\<le>242"
    by (rule comma_semantic_graph_stop_within_exact_action
      [OF phase root within order_refl]) blast
  show ?thesis using exact limit by blast
qed

theorem comma_semantic_graph_stop242_from_transfer_masks:
  fixes transfers ::
    "((comma_semantic_b1_result \<Rightarrow> nat) \<Rightarrow> nat) list"
  assumes transfer_count: "length transfers=46"
    and transfer_refinement: "\<And>root observe. root<46 \<Longrightarrow>
      comma_semantic_b1_graph_mask_refines comma_semantic_graph_nodes
        (comma_semantic_graph_root_ids!root) observe ((transfers!root) observe)"
    and root: "root<46"
    and full: "comma_semantic_b1_stop_mask_iteration transfers 26!root=mask 924"
  shows "\<forall>phase<924. \<exists>D. comma_semantic_graph_action_power 5 phase root=
    Comma_Semantic_B1_Stop D \<and> D\<le>242"
proof -
  have source_root_length:
    "length (map (\<lambda>index. Comma_Entry 1 0
      (comma_offset_representatives!index)) [0..<46])=46"
    by simp
  have root_binding_length:
    "length (map (\<lambda>index. Comma_Entry 1 0
      (comma_offset_representatives!index)) [0..<46]) =
      length comma_semantic_graph_root_ids"
    by (rule list_all2_lengthD[OF comma_semantic_graph_root_binding_exact])
  have root_count: "length comma_semantic_graph_root_ids=46"
    using source_root_length root_binding_length by simp
  have root_evaluation:
    "\<And>root phase. root<46 \<Longrightarrow> phase<924 \<Longrightarrow>
      \<exists>result. comma_semantic_b1_graph_eval comma_semantic_graph_nodes
        (comma_semantic_graph_root_ids!root) phase=Some result
        \<and> comma_semantic_graph_root_action phase root=result"
    by (rule comma_semantic_graph_root_evaluation)
  have within:
    "\<forall>phase<924. comma_semantic_b1_stop_within 26
      comma_semantic_graph_root_action phase root"
    by (rule comma_semantic_b1_full_stop_mask_iteration_sound
      [where transfers=transfers and action=comma_semantic_graph_root_action,
        OF root_count transfer_count root_evaluation transfer_refinement root full])
  show ?thesis
  proof (intro allI impI)
    fix phase :: nat
    assume phase: "phase<924"
    have bounded:
      "\<exists>D. comma_semantic_graph_action_power 5 phase root=
        Comma_Semantic_B1_Stop D \<and> D\<le>242"
      by (rule comma_semantic_graph_stop242_from_stop_within
        [OF phase root]) (rule within[rule_format, OF phase])
    show "\<exists>D. comma_semantic_graph_action_power 5 phase root=
        Comma_Semantic_B1_Stop D \<and> D\<le>242"
      by (rule bounded)
  qed
qed

corollary comma_semantic_graph_global_stop242_from_transfer_masks:
  fixes transfers ::
    "((comma_semantic_b1_result \<Rightarrow> nat) \<Rightarrow> nat) list"
  assumes transfer_count: "length transfers=46"
    and transfer_refinement: "\<And>root observe. root<46 \<Longrightarrow>
      comma_semantic_b1_graph_mask_refines comma_semantic_graph_nodes
        (comma_semantic_graph_root_ids!root) observe ((transfers!root) observe)"
    and full: "\<forall>root<46.
      comma_semantic_b1_stop_mask_iteration transfers 26!root=mask 924"
  shows "\<forall>root<46. \<forall>phase<924.
    \<exists>D. comma_semantic_graph_action_power 5 phase root=
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
proof (intro allI impI allI impI)
  fix root phase :: nat
  assume root: "root<46" and phase: "phase<924"
  have root_full:
    "comma_semantic_b1_stop_mask_iteration transfers 26!root=mask 924"
    using full root by blast
  have all_phases:
    "\<forall>phase<924. \<exists>D. comma_semantic_graph_action_power 5 phase root=
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
    by (rule comma_semantic_graph_stop242_from_transfer_masks
      [where transfers=transfers,
        OF transfer_count transfer_refinement root root_full])
  show "\<exists>D. comma_semantic_graph_action_power 5 phase root=
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
    using all_phases phase by blast
qed

ML \<open>
  val checked = @{thms comma_semantic_graph_root_atom_exact
    comma_semantic_graph_root_evaluation
    comma_semantic_graph_root_control_transport
    comma_semantic_graph_root_action_not_invalid
    comma_semantic_b1_weighted_word_then_encode
    comma_semantic_b1_weighted_word_then_admitted
    comma_semantic_b1_weighted_action_power_admitted
    comma_semantic_b1_weighted_action_power_encode
    comma_semantic_graph_root_weighted_action_exact
    comma_semantic_graph_root_weighted_action_admitted
    comma_semantic_graph_weighted_power_exact
    comma_semantic_graph_stop_within_summary
    comma_semantic_graph_stop_within_exact_action
    comma_semantic_graph_stop242_from_stop_within
    comma_semantic_graph_stop242_from_transfer_masks
    comma_semantic_graph_global_stop242_from_transfer_masks};
  Thm.consolidate checked;
  Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Semantic graph Stop-mask transport" checked;
  if null (Thm_Deps.all_oracles checked)
  then () else error "Graph mask transport depends on an oracle"
\<close>

end
