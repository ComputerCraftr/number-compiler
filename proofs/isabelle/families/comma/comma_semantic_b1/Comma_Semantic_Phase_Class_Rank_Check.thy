theory Comma_Semantic_Phase_Class_Rank_Check
  imports Comma_Semantic_Phase_Class Comma_Weighted_CRT_Data
    Comma_Semantic_Phase_Class_Action
begin

text \<open>
Rank is a proof sidecar in leaf payloads of the existing CRT algebra. CRT
edge weights are physical weights, never rank. Missing evaluations stay
explicit. A Continue leaf asks for only its named successor rank.
\<close>

definition comma_crt_rank_relation ::
    "comma_phase_rank_mask_action comma_semantic_weighted_crt_dag \<Rightarrow>
     nat comma_semantic_weighted_crt_dag \<Rightarrow>
     (nat \<Rightarrow> nat comma_semantic_weighted_crt_dag option) \<Rightarrow>
     nat \<Rightarrow> bool" where
  "comma_crt_rank_relation action current successors phase \<longleftrightarrow>
    (case (comma_crt_payload action phase,comma_crt_payload current phase) of
       (Some move,Some now) \<Rightarrow>
         now\<le>26 \<and> move\<noteq>Comma_Phase_Rank_Mask_Invalid \<and>
         (\<forall>child. move=Comma_Phase_Rank_Mask_Continue child \<longrightarrow>
           (\<exists>target successor. successors child=Some target \<and>
             comma_crt_payload target phase=Some successor \<and>
             successor<now))
     | _ \<Rightarrow> False)"

lemma comma_crt_rank_relation_fork_leaf:
  assumes "now\<le>26"
  shows "comma_crt_rank_relation
    (Comma_Weighted_CRT_Leaf (Comma_Phase_Rank_Mask_Fork a d))
    (Comma_Weighted_CRT_Leaf now) successors phase"
  using assms by (simp add: comma_crt_rank_relation_def
    comma_crt_payload_def)

lemma comma_crt_rank_relation_landmine_leaf:
  assumes "now\<le>26"
  shows "comma_crt_rank_relation
    (Comma_Weighted_CRT_Leaf (Comma_Phase_Rank_Mask_Landmine d))
    (Comma_Weighted_CRT_Leaf now) successors phase"
  using assms by (simp add: comma_crt_rank_relation_def
    comma_crt_payload_def)

lemma comma_crt_rank_relation_continue_leaf:
  assumes bound: "now\<le>26"
    and target: "successors child=Some tree"
    and selected_value: "comma_crt_payload tree phase=Some later"
    and descent: "later<now"
  shows "comma_crt_rank_relation
    (Comma_Weighted_CRT_Leaf (Comma_Phase_Rank_Mask_Continue child))
    (Comma_Weighted_CRT_Leaf now) successors phase"
proof -
  have witness: "\<exists>tree' successor. successors child=Some tree' \<and>
      comma_crt_payload tree' phase=Some successor \<and> successor<now"
    using target selected_value descent by blast
  show ?thesis using bound witness
    by (auto simp: comma_crt_rank_relation_def comma_crt_payload_def)
qed

lemma comma_crt_cofactor_shape_advance:
  assumes axis: "axis<4"
    and slot: "slot<comma_crt_axis_radix axis"
    and shape: "comma_weighted_crt_shape axis tree"
  shows "comma_weighted_crt_shape (Suc axis)
    (snd (comma_weighted_crt_cofactor_all_raw axis slot tree))"
proof -
  have old_shape: "comma_weighted_crt_shape axis
      (snd (comma_weighted_crt_cofactor_all_raw axis slot tree))"
    by (rule comma_weighted_crt_cofactor_all_raw_shape[OF axis slot shape])
  have absent: "comma_weighted_crt_axis_absent axis
      (snd (comma_weighted_crt_cofactor_all_raw axis slot tree))"
    by (rule comma_weighted_crt_cofactor_all_raw_absent
      [OF axis slot comma_weighted_crt_shape_wellformed[OF shape]])
  show ?thesis using old_shape absent
    by (cases "snd (comma_weighted_crt_cofactor_all_raw axis slot tree)") auto
qed

lemma comma_crt_rank_successor_shape:
  assumes extent: "length ranks=46"
    and shapes: "list_all (comma_weighted_crt_shape 0) ranks"
    and selected: "(if child<46 then
      Some (comma_weighted_crt_shift 1 (ranks!child)) else None)=Some target"
  shows "comma_weighted_crt_shape 0 target"
proof -
  have child: "child<46" using selected
    by (cases "child<46") auto
  have member: "ranks!child\<in>set ranks"
    using child extent by simp
  have source_shape: "comma_weighted_crt_shape 0 (ranks!child)"
    using shapes member by (auto simp: list_all_iff)
  have target: "target=comma_weighted_crt_shift 1 (ranks!child)"
    using selected child by simp
  show ?thesis using source_shape target
    by (simp only: comma_weighted_crt_shift_shape)
qed

lemma comma_crt_rank_successor_shape_cofactor:
  assumes axis: "axis<4"
    and slot: "slot<comma_crt_axis_radix axis"
    and source: "\<And>child tree. successors child=Some tree \<Longrightarrow>
      comma_weighted_crt_shape axis tree"
    and selected: "map_option
      (\<lambda>tree. snd (comma_weighted_crt_cofactor_all_raw axis slot tree))
      (successors child)=Some target"
  shows "comma_weighted_crt_shape (Suc axis) target"
proof -
  obtain tree where tree: "successors child=Some tree"
    and target: "target=snd
      (comma_weighted_crt_cofactor_all_raw axis slot tree)"
    using selected by (cases "successors child") auto
  show ?thesis using target
    by (simp only: comma_crt_cofactor_shape_advance
      [OF axis slot source[OF tree]])
qed

lemma comma_crt_rank_relation_cofactor:
  assumes axis: "axis<4"
    and slot: "slot=phase mod comma_crt_axis_radix axis"
    and action: "comma_weighted_crt_shape lower action"
    and current: "comma_weighted_crt_shape lower current"
    and successor_shape: "\<And>child target. successors child=Some target \<Longrightarrow>
      comma_weighted_crt_shape lower target"
    and reduced: "comma_crt_rank_relation
      (snd (comma_weighted_crt_cofactor_all_raw axis slot action))
      (snd (comma_weighted_crt_cofactor_all_raw axis slot current))
      (\<lambda>child. map_option
        (\<lambda>tree. snd (comma_weighted_crt_cofactor_all_raw axis slot tree))
        (successors child))
      phase"
  shows "comma_crt_rank_relation action current successors phase"
proof -
  have action_value: "comma_crt_payload
      (snd (comma_weighted_crt_cofactor_all_raw axis slot action)) phase =
      comma_crt_payload action phase"
    by (rule comma_crt_payload_cofactor_selected[OF axis slot action])
  have current_value: "comma_crt_payload
      (snd (comma_weighted_crt_cofactor_all_raw axis slot current)) phase =
      comma_crt_payload current phase"
    by (rule comma_crt_payload_cofactor_selected[OF axis slot current])
  have next_value: "\<And>child target. successors child=Some target \<Longrightarrow>
      comma_crt_payload
        (snd (comma_weighted_crt_cofactor_all_raw axis slot target)) phase =
      comma_crt_payload target phase"
  proof -
    fix child target
    assume chosen: "successors child=Some target"
    have target_shape: "comma_weighted_crt_shape lower target"
      by (rule successor_shape[OF chosen])
    show "comma_crt_payload
        (snd (comma_weighted_crt_cofactor_all_raw axis slot target)) phase =
      comma_crt_payload target phase"
      by (rule comma_crt_payload_cofactor_selected
        [OF axis slot target_shape])
  qed
  show ?thesis using reduced action_value current_value next_value
    by (auto simp: comma_crt_rank_relation_def
      split: option.splits)
qed

lemma comma_crt_rank_relation_all_cofactors:
  assumes axis: "axis<4"
    and action: "comma_weighted_crt_shape lower action"
    and current: "comma_weighted_crt_shape lower current"
    and successor_shape: "\<And>child target. successors child=Some target
      \<Longrightarrow> comma_weighted_crt_shape lower target"
    and children: "\<And>slot phase. slot<comma_crt_axis_radix axis \<Longrightarrow>
      comma_crt_rank_relation
        (snd (comma_weighted_crt_cofactor_all_raw axis slot action))
        (snd (comma_weighted_crt_cofactor_all_raw axis slot current))
        (\<lambda>child. map_option
          (\<lambda>tree. snd
            (comma_weighted_crt_cofactor_all_raw axis slot tree))
          (successors child)) phase"
  shows "comma_crt_rank_relation action current successors phase"
proof -
  let ?slot = "phase mod comma_crt_axis_radix axis"
  have slot_bound: "?slot<comma_crt_axis_radix axis"
    using comma_weighted_crt_axis_positive[OF axis] by simp
  have selected: "comma_crt_rank_relation
      (snd (comma_weighted_crt_cofactor_all_raw axis ?slot action))
      (snd (comma_weighted_crt_cofactor_all_raw axis ?slot current))
      (\<lambda>child. map_option
        (\<lambda>tree. snd
          (comma_weighted_crt_cofactor_all_raw axis ?slot tree))
        (successors child)) phase"
    by (rule children[OF slot_bound])
  show ?thesis
    by (rule comma_crt_rank_relation_cofactor
      [OF axis refl action current successor_shape selected])
qed

lemma comma_crt_rank_relation_list_cofactors:
  assumes axis: "axis<4"
    and action: "comma_weighted_crt_shape lower action"
    and current: "comma_weighted_crt_shape lower current"
    and successor_shape: "\<And>child target. successors child=Some target
      \<Longrightarrow> comma_weighted_crt_shape lower target"
    and children: "list_all (\<lambda>slot. \<forall>phase.
      comma_crt_rank_relation
        (snd (comma_weighted_crt_cofactor_all_raw axis slot action))
        (snd (comma_weighted_crt_cofactor_all_raw axis slot current))
        (\<lambda>child. map_option
          (\<lambda>tree. snd
            (comma_weighted_crt_cofactor_all_raw axis slot tree))
          (successors child)) phase)
      [0..<comma_crt_axis_radix axis]"
  shows "comma_crt_rank_relation action current successors phase"
proof -
  have child: "\<And>slot phase. slot<comma_crt_axis_radix axis \<Longrightarrow>
      comma_crt_rank_relation
        (snd (comma_weighted_crt_cofactor_all_raw axis slot action))
        (snd (comma_weighted_crt_cofactor_all_raw axis slot current))
        (\<lambda>child. map_option
          (\<lambda>tree. snd
            (comma_weighted_crt_cofactor_all_raw axis slot tree))
          (successors child)) phase"
    using children by (auto simp: list_all_iff)
  show ?thesis by (rule comma_crt_rank_relation_all_cofactors
    [OF axis action current successor_shape child])
qed

definition comma_crt_rank_at ::
    "nat comma_semantic_weighted_crt_dag list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "comma_crt_rank_at ranks phase cid =
    (case comma_crt_payload (ranks!cid) phase of
       None \<Rightarrow> 0 | Some rank \<Rightarrow> rank)"

lemma comma_crt_payload_shift_one:
  assumes shape: "comma_weighted_crt_shape 0 tree"
  shows "comma_crt_payload (comma_weighted_crt_shift 1 tree) phase =
    comma_crt_payload tree ((phase+1) mod 924)"
proof -
  have wellformed: "comma_weighted_crt_wellformed tree"
    by (rule comma_weighted_crt_shape_wellformed[OF shape])
  show ?thesis
    using comma_weighted_crt_shift_exact[OF wellformed, of 1 phase]
      comma_weighted_crt_eval_mod_924[OF wellformed, of "phase+1"]
    by (simp only: comma_crt_payload_def)
qed

theorem comma_crt_rank_relations_sound:
  assumes relations: "\<And>phase cid. phase<924 \<Longrightarrow> cid<46 \<Longrightarrow>
      comma_crt_rank_relation (actions!cid) (ranks!cid)
        (\<lambda>child. if child<46 then
          Some (comma_weighted_crt_shift 1 (ranks!child)) else None) phase"
    and rank_shapes: "\<And>cid. cid<46 \<Longrightarrow>
      comma_weighted_crt_shape 0 (ranks!cid)"
    and exact: "\<And>phase cid. phase<924 \<Longrightarrow> cid<46 \<Longrightarrow>
      \<exists>move. comma_crt_payload (actions!cid) phase=Some move \<and>
        comma_phase_rank_mask_lift phase move =
          comma_semantic_phase_class_step phase cid"
  shows "comma_phase_class_rank_check
      comma_semantic_phase_class_valid (comma_crt_rank_at ranks)
      comma_semantic_phase_class_step"
    and "\<And>phase cid. comma_semantic_phase_class_valid phase cid
      \<Longrightarrow> comma_crt_rank_at ranks phase cid\<le>26"
proof -
  have row: "\<And>phase cid. comma_semantic_phase_class_valid phase cid
      \<Longrightarrow> \<exists>move now. comma_crt_payload (actions!cid) phase=Some move
        \<and> comma_crt_payload (ranks!cid) phase=Some now
        \<and> now\<le>26 \<and> move\<noteq>Comma_Phase_Rank_Mask_Invalid
        \<and> (\<forall>child. move=Comma_Phase_Rank_Mask_Continue child \<longrightarrow>
          child<46 \<and>
          (\<exists>successor. comma_crt_payload
            (comma_weighted_crt_shift 1 (ranks!child)) phase=Some successor
            \<and> successor<now))"
  proof -
    fix phase cid
    assume valid: "comma_semantic_phase_class_valid phase cid"
    then have phase_bound: "phase<924" and class_bound: "cid<46"
      by (simp_all add: comma_semantic_phase_class_valid_def)
    have relation: "comma_crt_rank_relation (actions!cid) (ranks!cid)
      (\<lambda>child. if child<46 then
        Some (comma_weighted_crt_shift 1 (ranks!child)) else None) phase"
      by (rule relations[OF phase_bound class_bound])
    show "\<exists>move now. comma_crt_payload (actions!cid) phase=Some move
        \<and> comma_crt_payload (ranks!cid) phase=Some now
        \<and> now\<le>26 \<and> move\<noteq>Comma_Phase_Rank_Mask_Invalid
        \<and> (\<forall>child. move=Comma_Phase_Rank_Mask_Continue child \<longrightarrow>
          child<46 \<and>
          (\<exists>successor. comma_crt_payload
            (comma_weighted_crt_shift 1 (ranks!child)) phase=Some successor
            \<and> successor<now))"
      using relation
      by (auto simp: comma_crt_rank_relation_def
        split: option.splits if_splits)
  qed
  show "comma_phase_class_rank_check
      comma_semantic_phase_class_valid (comma_crt_rank_at ranks)
      comma_semantic_phase_class_step"
  proof (unfold comma_phase_class_rank_check_def, intro allI impI)
    fix phase cid
    assume valid: "comma_semantic_phase_class_valid phase cid"
    then have phase: "phase<924" and class_bound: "cid<46"
      by (simp_all add: comma_semantic_phase_class_valid_def)
    obtain move now where move: "comma_crt_payload (actions!cid) phase=Some move"
      and now: "comma_crt_payload (ranks!cid) phase=Some now"
      and bound: "now\<le>26"
      and noninvalid: "move\<noteq>Comma_Phase_Rank_Mask_Invalid"
      and descent: "\<forall>child. move=Comma_Phase_Rank_Mask_Continue child \<longrightarrow>
        child<46 \<and>
        (\<exists>successor. comma_crt_payload
          (comma_weighted_crt_shift 1 (ranks!child)) phase=Some successor
          \<and> successor<now)"
      using row[OF valid] by blast
    have actual: "comma_phase_rank_mask_lift phase move =
      comma_semantic_phase_class_step phase cid"
      using exact[OF phase class_bound] move by auto
    show "case comma_semantic_phase_class_step phase cid of
       Comma_Phase_Class_Invalid \<Rightarrow> False
     | Comma_Phase_Class_Fork a d \<Rightarrow> True
     | Comma_Phase_Class_Landmine d \<Rightarrow> True
     | Comma_Phase_Class_Continue next_phase next_class \<Rightarrow>
         comma_semantic_phase_class_valid next_phase next_class \<and>
         comma_crt_rank_at ranks next_phase next_class <
           comma_crt_rank_at ranks phase cid"
    proof (cases move)
      case Comma_Phase_Rank_Mask_Invalid
      then show ?thesis using noninvalid by simp
    next
      case (Comma_Phase_Rank_Mask_Fork a d)
      have step_eq: "comma_semantic_phase_class_step phase cid =
        Comma_Phase_Class_Fork a d"
        using actual Comma_Phase_Rank_Mask_Fork by simp
      show ?thesis by (simp only: step_eq
        comma_phase_class_action.case)
    next
      case (Comma_Phase_Rank_Mask_Landmine d)
      have step_eq: "comma_semantic_phase_class_step phase cid =
        Comma_Phase_Class_Landmine d"
        using actual Comma_Phase_Rank_Mask_Landmine by simp
      show ?thesis by (simp only: step_eq
        comma_phase_class_action.case)
    next
      case (Comma_Phase_Rank_Mask_Continue child)
      then obtain successor where child: "child<46"
        and successor: "comma_crt_payload
          (comma_weighted_crt_shift 1 (ranks!child)) phase=Some successor"
        and decreasing: "successor<now"
        using descent by blast
      have rank_shape: "comma_weighted_crt_shape 0 (ranks!child)"
        by (rule rank_shapes[OF child])
      have shifted: "comma_crt_payload (ranks!child)
          ((phase+1) mod 924)=Some successor"
        using successor comma_crt_payload_shift_one[OF rank_shape, of phase]
        by simp
      have step_eq: "comma_semantic_phase_class_step phase cid =
        Comma_Phase_Class_Continue ((phase+1) mod 924) child"
        using actual Comma_Phase_Rank_Mask_Continue by simp
      have next_phase_bound: "((phase+1) mod 924)<924" by simp
      show ?thesis
        using now shifted decreasing phase child next_phase_bound
        by (simp only: step_eq comma_phase_class_action.case
          comma_semantic_phase_class_valid_def
          comma_crt_rank_at_def option.simps; simp)
    qed
  qed
  show "\<And>phase cid. comma_semantic_phase_class_valid phase cid
      \<Longrightarrow> comma_crt_rank_at ranks phase cid\<le>26"
  proof -
    fix phase cid
    assume valid: "comma_semantic_phase_class_valid phase cid"
    obtain move now where rank: "comma_crt_payload (ranks!cid) phase=Some now"
      and bound: "now\<le>26"
      using row[OF valid] by blast
    show "comma_crt_rank_at ranks phase cid\<le>26"
      using bound by (simp only: comma_crt_rank_at_def rank option.simps)
  qed
qed

theorem comma_crt_rank_relations_B32:
  assumes relations: "\<And>phase cid. phase<924 \<Longrightarrow> cid<46 \<Longrightarrow>
      comma_crt_rank_relation (actions!cid) (ranks!cid)
        (\<lambda>child. if child<46 then
          Some (comma_weighted_crt_shift 1 (ranks!child)) else None) phase"
    and rank_shapes: "\<And>cid. cid<46 \<Longrightarrow>
      comma_weighted_crt_shape 0 (ranks!cid)"
    and exact: "\<And>phase cid. phase<924 \<Longrightarrow> cid<46 \<Longrightarrow>
      \<exists>move. comma_crt_payload (actions!cid) phase=Some move \<and>
        comma_phase_rank_mask_lift phase move =
          comma_semantic_phase_class_step phase cid"
    and admitted: "comma_decade_admitted s"
  shows "\<exists>h tau. h\<le>26 \<and>
    comma_decade_block_power 5 s = Comma_Block_Stop h tau \<and>
    comma_residual_block 32 (h,tau) = Comma_Residual_Stop h tau \<and>
    comma_decade_exact_summary s h tau"
proof -
  have rank_check: "comma_phase_class_rank_check
      comma_semantic_phase_class_valid (comma_crt_rank_at ranks)
      comma_semantic_phase_class_step"
    by (rule comma_crt_rank_relations_sound(1)
      [OF relations rank_shapes exact])
  have bounded: "\<And>phase cid. comma_semantic_phase_class_valid phase cid
      \<Longrightarrow> comma_crt_rank_at ranks phase cid\<le>26"
    by (rule comma_crt_rank_relations_sound(2)
      [OF relations rank_shapes exact])
  show ?thesis
    by (rule comma_phase_class_rank_B32
      [where class_of=comma_offset_orbit
       and valid=comma_semantic_phase_class_valid
       and rank="comma_crt_rank_at ranks"
       and step=comma_semantic_phase_class_step,
       OF rank_check comma_semantic_phase_class_source_valid
         comma_semantic_phase_class_source_control bounded admitted])
qed

ML \<open>
  val rank_checker_rules =
    @{thms comma_crt_rank_relation_fork_leaf
      comma_crt_rank_relation_landmine_leaf
      comma_crt_rank_relation_continue_leaf
      comma_crt_cofactor_shape_advance
      comma_crt_rank_successor_shape
      comma_crt_rank_successor_shape_cofactor
      comma_crt_rank_relation_list_cofactors
      comma_crt_rank_relation_all_cofactors
      comma_crt_rank_relations_sound comma_crt_rank_relations_B32};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Comma Semantic Phase Class Rank Check" rank_checker_rules;
\<close>

ML_file "semantic_phase_class_rank_candidate.ML"
ML_file "semantic_phase_class_rank_certificate.ML"
ML_file "semantic_phase_class_rank_joint_certifier.ML"
ML_file "semantic_phase_class_rank_shift_certificate.ML"
ML_file "semantic_phase_class_rank_relation_compiler.ML"

end
