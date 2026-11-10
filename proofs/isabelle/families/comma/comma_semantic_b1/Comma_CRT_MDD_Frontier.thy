theory Comma_CRT_MDD_Frontier
  imports Comma_CRT_MDD_Shift Comma_Continue_Frontier_Induction Comma_CRT_Phase_Clock
begin

text \<open>
Relate a total nat-valued MDD action to the exact Continue option step. The
MDD payload encoding reserves zero for every non-Continue action and uses
Suc target for Continue target. The target equivalence is unbounded, so this
bridge does not assume or enumerate a target range.
\<close>

lemma comma_frontier_successor_map:
  assumes "target < length roots"
  shows "map_of (zip [1..<Suc (length roots)] roots) (Suc target) =
    Some (roots ! target)"
proof -
  have widths: "length [1..<Suc (length roots)] = length roots"
    by (simp only: length_upt One_nat_def diff_Suc_Suc diff_zero)
  have index: "[1..<Suc (length roots)] ! target = Suc target"
    using assms
    by (simp only: nth_upt One_nat_def add_Suc add_0_left Suc_less_eq)
  have lookup:
    "map_of (zip [1..<Suc (length roots)] roots)
        ([1..<Suc (length roots)] ! target) = Some (roots ! target)"
    by (rule map_of_zip_nth[OF widths distinct_upt assms])
  show ?thesis using lookup by (simp only: index)
qed

lemma comma_frontier_successor_map_zero:
  "map_of (zip [1..<Suc (length roots)] roots) 0 = None"
proof -
  have widths: "length [1..<Suc (length roots)] = length roots"
    by (simp only: length_upt One_nat_def diff_Suc_Suc diff_zero)
  have absent: "0 \<notin> set [1..<Suc (length roots)]"
    by (simp only: set_upt atLeastLessThan_iff; simp)
  show ?thesis by (rule iffD2[OF map_of_zip_is_None[OF widths] absent])
qed

lemma comma_frontier_radices_divide:
  assumes "axis < length ([3,4,11,7] :: nat list)"
  shows "[3,4,11,7] ! axis dvd (924 :: nat)"
  using nth_mem[OF assms] by auto

lemma comma_crt_mdd_frontier_action_option:
  fixes radices :: "nat list"
    and nodes :: "nat comma_crt_mdd_node list"
    and step :: "nat \<Rightarrow> nat \<Rightarrow> nat comma_phase_class_action"
  assumes wellformed:
      "comma_crt_mdd_table_wellformed radices nodes"
    and root_bound: "root < length nodes"
    and exact:
      "\<And>target. (comma_crt_mdd_eval_phase radices nodes phase root =
          Some (Suc target)) =
        (step phase cid =
          Comma_Phase_Class_Continue ((phase+1) mod 924) target)"
    and clock:
      "\<And>next_phase next_cid. step phase cid =
        Comma_Phase_Class_Continue next_phase next_cid \<Longrightarrow>
        next_phase = (phase+1) mod 924"
  shows "comma_phase_class_continue_option_step step (Some (phase,cid)) =
    (case comma_crt_mdd_eval_phase radices nodes phase root of
       None \<Rightarrow> None
     | Some 0 \<Rightarrow> None
     | Some (Suc target) \<Rightarrow>
         Some (((phase+1) mod 924,target)))"
proof -
  have total:
    "\<exists>payload. comma_crt_mdd_eval_phase radices nodes phase root =
      Some payload"
    using comma_crt_mdd_eval_raw_total[OF wellformed root_bound] wellformed
    by (simp add: comma_crt_mdd_eval_phase_def comma_crt_mdd_eval_def)
  obtain payload where evaluation:
    "comma_crt_mdd_eval_phase radices nodes phase root = Some payload"
    using total by blast
  show ?thesis
  proof (cases payload)
    case 0
    have no_continue:
      "step phase cid \<noteq> Comma_Phase_Class_Continue next_phase next_cid"
      for next_phase next_cid
    proof
      assume continuation:
        "step phase cid = Comma_Phase_Class_Continue next_phase next_cid"
      have clocked: "next_phase=(phase+1) mod 924"
        by (rule clock[OF continuation])
      have "comma_crt_mdd_eval_phase radices nodes phase root =
          Some (Suc next_cid)"
        using exact[of next_cid] continuation clocked by blast
      with evaluation 0 show False by simp
    qed
    show ?thesis
    proof (cases "step phase cid")
      case Comma_Phase_Class_Invalid
      then show ?thesis using evaluation 0
        by (simp add: comma_phase_class_continue_option_step_def)
    next
      case (Comma_Phase_Class_Fork left right)
      then show ?thesis using evaluation 0
        by (simp add: comma_phase_class_continue_option_step_def)
    next
      case (Comma_Phase_Class_Landmine next_class)
      then show ?thesis using evaluation 0
        by (simp add: comma_phase_class_continue_option_step_def)
    next
      case (Comma_Phase_Class_Continue next_phase next_cid)
      have False using no_continue[of next_phase next_cid]
        Comma_Phase_Class_Continue by simp
      then show ?thesis by simp
    qed
  next
    case (Suc target)
    have continuation:
      "step phase cid =
        Comma_Phase_Class_Continue ((phase+1) mod 924) target"
      using exact[of target] evaluation Suc by blast
    show ?thesis using evaluation Suc continuation
      by (simp add: comma_phase_class_continue_option_step_def)
  qed
qed

lemma comma_crt_mdd_frontier_action_option_invert:
  fixes radices :: "nat list"
    and nodes :: "nat comma_crt_mdd_node list"
    and step :: "nat \<Rightarrow> nat \<Rightarrow> nat comma_phase_class_action"
  assumes total:
      "\<exists>payload. comma_crt_mdd_eval_phase radices nodes phase root =
        Some payload"
    and option_exact:
      "comma_phase_class_continue_option_step step (Some (phase,cid)) =
        (case comma_crt_mdd_eval_phase radices nodes phase root of
           None \<Rightarrow> None
         | Some 0 \<Rightarrow> None
         | Some (Suc target) \<Rightarrow>
             Some (((phase+1) mod 924,target)))"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    (case step phase cid of
       Comma_Phase_Class_Continue _ target \<Rightarrow> Some (Suc target)
     | _ \<Rightarrow> Some 0)"
proof -
  obtain payload where evaluation:
    "comma_crt_mdd_eval_phase radices nodes phase root = Some payload"
    using total by blast
  show ?thesis
  proof (cases "step phase cid")
    case Comma_Phase_Class_Invalid
    have "payload=0" using option_exact evaluation Comma_Phase_Class_Invalid
      by (cases payload)
        (auto simp: comma_phase_class_continue_option_step_def)
    with evaluation Comma_Phase_Class_Invalid show ?thesis by simp
  next
    case (Comma_Phase_Class_Fork left right)
    have "payload=0" using option_exact evaluation Comma_Phase_Class_Fork
      by (cases payload)
        (auto simp: comma_phase_class_continue_option_step_def)
    with evaluation Comma_Phase_Class_Fork show ?thesis by simp
  next
    case (Comma_Phase_Class_Landmine next_class)
    have "payload=0" using option_exact evaluation Comma_Phase_Class_Landmine
      by (cases payload)
        (auto simp: comma_phase_class_continue_option_step_def)
    with evaluation Comma_Phase_Class_Landmine show ?thesis by simp
  next
    case (Comma_Phase_Class_Continue next_phase target)
    have "payload = Suc target"
      using option_exact evaluation Comma_Phase_Class_Continue
      by (cases payload)
        (auto simp: comma_phase_class_continue_option_step_def)
    with evaluation Comma_Phase_Class_Continue show ?thesis by simp
  qed
qed

lemma comma_crt_mdd_frontier_action_option_needs_clock:
  "(\<forall>target. (comma_crt_mdd_eval_phase [3,4,11,7]
        [Comma_CRT_MDD_Leaf (0::nat)] 0 0 = Some (Suc target)) =
      ((\<lambda>(_::nat) (_::nat). Comma_Phase_Class_Continue 0 0) 0 0 =
        Comma_Phase_Class_Continue ((0+1) mod 924) target)) \<and>
    comma_phase_class_continue_option_step
      (\<lambda>(_::nat) (_::nat). Comma_Phase_Class_Continue 0 0) (Some (0,0)) \<noteq>
      (case comma_crt_mdd_eval_phase [3,4,11,7]
          [Comma_CRT_MDD_Leaf (0::nat)] 0 0 of
         None \<Rightarrow> None
       | Some 0 \<Rightarrow> None
       | Some (Suc target) \<Rightarrow>
           Some (((0+1) mod 924,target)))"
proof -
  have root_bound:
      "0 < length ([Comma_CRT_MDD_Leaf (0::nat)] :: nat comma_crt_mdd_node list)"
    by simp
  have table_wf:
      "comma_crt_mdd_table_wellformed [3,4,11,7]
        [Comma_CRT_MDD_Leaf (0::nat)]"
    by (simp add: comma_crt_mdd_table_wellformed_def
        comma_crt_mdd_node_ordered_def)
  have binding:
      "([Comma_CRT_MDD_Leaf (0::nat)] :: nat comma_crt_mdd_node list) ! 0 =
        Comma_CRT_MDD_Leaf 0"
    by simp
  have eval:
      "comma_crt_mdd_eval_phase [3,4,11,7]
        [Comma_CRT_MDD_Leaf (0::nat)] 0 0 = Some 0"
    unfolding comma_crt_mdd_eval_phase_def comma_crt_mdd_eval_def
    using comma_crt_mdd_eval_raw_leaf[OF root_bound binding] table_wf
    by (simp add: comma_crt_mdd_eval_def)
  show ?thesis using eval
    by (simp add: comma_phase_class_continue_option_step_def)
qed

lemma comma_crt_mdd_eval_raw_branch_except:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and root: "root < length nodes"
    and branch: "nodes ! root = Comma_CRT_MDD_Branch axis children"
    and selected: "selected < radices ! axis"
    and special: "special = children ! selected"
    and off_path: "\<And>slot. slot < length children \<Longrightarrow>
      slot \<noteq> selected \<Longrightarrow>
      comma_crt_mdd_eval_raw radices nodes coordinate (children ! slot) =
        Some value"
  shows "comma_crt_mdd_eval_raw radices nodes coordinate root =
    (if coordinate axis mod radices ! axis = selected then
       comma_crt_mdd_eval_raw radices nodes coordinate special
     else Some value)"
proof -
  have facts:
    "axis < length radices"
    "0 < radices ! axis"
    "length children = radices ! axis"
    "\<forall>child\<in>set children. child < root \<and>
      (case comma_crt_mdd_node_axis (nodes ! child) of
         None \<Rightarrow> True | Some child_axis \<Rightarrow> axis < child_axis)"
    by (rule comma_crt_mdd_branch_facts[OF wellformed root branch])+
  let ?slot = "coordinate axis mod radices ! axis"
  have slot_bound: "?slot < length children"
    using facts(2,3) by simp
  have branch_step:
    "comma_crt_mdd_eval_raw radices nodes coordinate root =
      comma_crt_mdd_eval_raw radices nodes coordinate (children ! ?slot)"
    by (rule comma_crt_mdd_eval_raw_branch_selected[OF wellformed root branch])
  show ?thesis
  proof (cases "?slot = selected")
    case True
    then have "children ! ?slot = special" using special by simp
    with branch_step True show ?thesis by simp
  next
    case False
    have off: "comma_crt_mdd_eval_raw radices nodes coordinate (children ! ?slot) =
        Some value"
      by (rule off_path[OF slot_bound False])
    show ?thesis using branch_step False off by simp
  qed
qed

lemma comma_crt_mdd_frontier_bind_step:
  fixes radices :: "nat list"
    and nodes :: "nat comma_crt_mdd_node list"
    and step :: "nat \<Rightarrow> nat \<Rightarrow> nat comma_phase_class_action"
    and mapping :: "(nat \<times> nat) list"
    and shifted_root :: "nat \<Rightarrow> nat"
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and bind_certificate:
      "comma_crt_mdd_bind_certificate radices nodes mapping fallback_root
        source_root result_root"
    and action_evaluation:
      "comma_crt_mdd_eval_phase radices nodes phase source_root =
        (case step phase cid of
           Comma_Phase_Class_Continue next_phase target \<Rightarrow>
             Some (Suc target)
         | _ \<Rightarrow> Some 0)"
    and fallback_evaluation:
      "comma_crt_mdd_eval_phase radices nodes phase fallback_root = Some 0"
    and zero_unmapped: "map_of mapping 0 = None"
    and target_mapped:
      "\<And>target. target < 46 \<Longrightarrow>
        map_of mapping (Suc target) = Some (shifted_root target)"
    and target_bound:
      "\<And>next_phase target. step phase cid =
        Comma_Phase_Class_Continue next_phase target \<Longrightarrow>
        target < 46"
    and one_tick:
      "\<And>next_phase target. step phase cid =
        Comma_Phase_Class_Continue next_phase target \<Longrightarrow>
        next_phase = (phase+1) mod 924"
    and shifted_evaluation:
      "\<And>target. target < 46 \<Longrightarrow>
        comma_crt_mdd_eval_phase radices nodes phase (shifted_root target) =
          comma_crt_mdd_eval_phase radices nodes (phase+1) (previous_root target)"
    and period_divides:
      "\<And>axis. axis < length radices \<Longrightarrow> radices ! axis dvd 924"
  shows "comma_crt_mdd_eval_phase radices nodes phase result_root =
    (case step phase cid of
       Comma_Phase_Class_Continue next_phase target \<Rightarrow>
         comma_crt_mdd_eval_phase radices nodes next_phase (previous_root target)
     | _ \<Rightarrow> Some 0)"
proof -
  have bind_evaluation:
    "comma_crt_mdd_eval_phase radices nodes phase result_root =
      (case comma_crt_mdd_eval_phase radices nodes phase source_root of
         None \<Rightarrow> comma_crt_mdd_eval_phase radices nodes phase fallback_root
       | Some payload \<Rightarrow>
           comma_crt_mdd_eval_phase radices nodes phase
             (comma_crt_mdd_bind_target fallback_root mapping payload))"
    by (rule comma_crt_mdd_bind_certificate_eval_phase
      [OF wellformed bind_certificate])
  show ?thesis
  proof (cases "step phase cid")
    case Comma_Phase_Class_Invalid
    then show ?thesis
      using bind_evaluation action_evaluation fallback_evaluation zero_unmapped
      by (simp add: comma_crt_mdd_bind_target_def)
  next
    case (Comma_Phase_Class_Fork left right)
    then show ?thesis
      using bind_evaluation action_evaluation fallback_evaluation zero_unmapped
      by (simp add: comma_crt_mdd_bind_target_def)
  next
    case (Comma_Phase_Class_Landmine next_class)
    then show ?thesis
      using bind_evaluation action_evaluation fallback_evaluation zero_unmapped
      by (simp add: comma_crt_mdd_bind_target_def)
  next
    case (Comma_Phase_Class_Continue next_phase target)
    have bound: "target < 46"
      by (rule target_bound[OF Comma_Phase_Class_Continue])
    have mapped: "map_of mapping (Suc target) = Some (shifted_root target)"
      by (rule target_mapped[OF bound])
    have phase_clock: "next_phase=(phase+1) mod 924"
      by (rule one_tick[OF Comma_Phase_Class_Continue])
    have next_periodic:
      "comma_crt_mdd_eval_phase radices nodes next_phase (previous_root target) =
        comma_crt_mdd_eval_phase radices nodes (phase+1) (previous_root target)"
      using phase_clock comma_crt_mdd_eval_phase_periodic
        [OF wellformed period_divides, of "phase+1" "previous_root target"]
      by simp
    have shifted:
      "comma_crt_mdd_eval_phase radices nodes phase (shifted_root target) =
        comma_crt_mdd_eval_phase radices nodes (phase+1) (previous_root target)"
      by (rule shifted_evaluation[OF bound])
    show ?thesis
      using bind_evaluation action_evaluation fallback_evaluation mapped shifted
        next_periodic Comma_Phase_Class_Continue
      by (simp add: comma_crt_mdd_bind_target_def)
  qed
qed

lemma comma_crt_phase_point_iff_axis_residues:
  fixes phase point :: nat
  assumes point: "point < 924"
  shows "phase mod 924 = point \<longleftrightarrow>
    (phase mod 3 = point mod 3 \<and>
     phase mod 4 = point mod 4 \<and>
     phase mod 11 = point mod 11 \<and>
     phase mod 7 = point mod 7)"
proof
  assume equal: "phase mod 924 = point"
  have d3: "(3::nat) dvd (924::nat)" and d4: "(4::nat) dvd (924::nat)"
    and d11: "(11::nat) dvd (924::nat)" and d7: "(7::nat) dvd (924::nat)"
    by simp_all
  have r3: "phase mod 3 = point mod 3"
    using arg_cong[OF equal, where f="\<lambda>x. x mod 3"]
    by (simp only: mod_mod_cancel[OF d3])
  have r4: "phase mod 4 = point mod 4"
    using arg_cong[OF equal, where f="\<lambda>x. x mod 4"]
    by (simp only: mod_mod_cancel[OF d4])
  have r11: "phase mod 11 = point mod 11"
    using arg_cong[OF equal, where f="\<lambda>x. x mod 11"]
    by (simp only: mod_mod_cancel[OF d11])
  have r7: "phase mod 7 = point mod 7"
    using arg_cong[OF equal, where f="\<lambda>x. x mod 7"]
    by (simp only: mod_mod_cancel[OF d7])
  show "phase mod 3 = point mod 3 \<and>
      phase mod 4 = point mod 4 \<and>
      phase mod 11 = point mod 11 \<and>
      phase mod 7 = point mod 7"
    using r3 r4 r11 r7 by blast
next
  assume residues: "phase mod 3 = point mod 3 \<and>
      phase mod 4 = point mod 4 \<and>
      phase mod 11 = point mod 11 \<and>
      phase mod 7 = point mod 7"
  have r3: "phase mod 3 = point mod 3" and r4: "phase mod 4 = point mod 4"
    and r11: "phase mod 11 = point mod 11" and r7: "phase mod 7 = point mod 7"
    using residues by blast+
  have clock: "comma_crt_clock phase = comma_crt_clock point"
    using r4 r3 r11 r7 by (simp add: comma_crt_clock_def)
  have left: "comma_crt_clock phase = phase mod 924"
    by (rule comma_crt_clock_reconstruct)
  have right: "comma_crt_clock point = point"
    using point comma_crt_clock_reconstruct by simp
  show "phase mod 924 = point" using clock left right by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Total MDD action decodes to the exact Continue option step"
    @{thms comma_frontier_successor_map comma_frontier_successor_map_zero
      comma_frontier_radices_divide comma_crt_mdd_frontier_action_option
      comma_crt_mdd_frontier_action_option_invert
      comma_crt_mdd_frontier_action_option_needs_clock
      comma_crt_mdd_eval_raw_branch_except
      comma_crt_mdd_frontier_bind_step
      comma_crt_phase_point_iff_axis_residues}
\<close>

end
