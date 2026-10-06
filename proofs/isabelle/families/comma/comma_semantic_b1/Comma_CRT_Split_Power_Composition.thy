theory Comma_CRT_Split_Power_Composition
  imports Comma_CRT_Split_Power_Admission
begin

text \<open>The cofactor composer computes the same complete control/weight
  result as pointwise semantic composition.  The induction follows the four
  CRT dimensions; a selected branch is justified by the cofactor evaluation
  theorem, so no return-row product is part of this refinement.\<close>

lemma comma_crt_split_leaf_refines:
  fixes remaining span phase :: nat
    and control :: comma_crt_control
    and weights :: comma_crt_weight_mdd
    and controls_for :: "nat \<Rightarrow> comma_crt_control_mdd"
    and weights_for :: "nat \<Rightarrow> comma_crt_weight_mdd"
  assumes weights_admitted:
      "comma_crt_mdd_admitted (4-remaining) weights"
    and right_controls_admitted:
      "\<And>root. comma_crt_mdd_admitted (4-remaining) (controls_for root)"
    and right_weights_admitted:
      "\<And>root. comma_crt_mdd_admitted (4-remaining) (weights_for root)"
  shows "comma_crt_split_mdd_result_at phase
      (fst (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf control) weights controls_for weights_for))
      (snd (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf control) weights controls_for weights_for)) =
    comma_crt_split_compose_expected_at span
      (Comma_CRT_MDD_Leaf control) weights controls_for weights_for phase"
proof (cases control)
  case (Comma_CRT_Control_Live root)
  have exact:
    "comma_crt_split_mdd_result_at phase
        (fst (comma_crt_split_compose_from remaining span
          (Comma_CRT_MDD_Leaf (Comma_CRT_Control_Live root)) weights
          controls_for weights_for))
        (snd (comma_crt_split_compose_from remaining span
          (Comma_CRT_MDD_Leaf (Comma_CRT_Control_Live root)) weights
          controls_for weights_for)) =
      comma_crt_split_compose_expected_at span
        (Comma_CRT_MDD_Leaf (Comma_CRT_Control_Live root)) weights
        controls_for weights_for phase"
    by (rule comma_crt_split_live_leaf_refines[
      where lower = "4-remaining" and root = root and left_weight = weights
        and right_controls = controls_for and right_weights = weights_for
        and phase = phase and remaining = remaining and span = span,
      OF weights_admitted right_controls_admitted[of root]
        right_weights_admitted[of root]])
  show "comma_crt_split_mdd_result_at phase
      (fst (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf control) weights controls_for weights_for))
      (snd (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf control) weights controls_for weights_for)) =
    comma_crt_split_compose_expected_at span
      (Comma_CRT_MDD_Leaf control) weights controls_for weights_for phase"
    using exact Comma_CRT_Control_Live by simp
next
  case Comma_CRT_Control_Stop
  obtain payload_weight where weight_eval:
      "comma_crt_mdd_eval phase weights=Some payload_weight"
    using comma_crt_mdd_admitted_eval_some[
      where lower = "4-remaining" and diagram = weights and phase = phase,
      OF weights_admitted] by blast
  have built:
    "comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop) weights
        controls_for weights_for =
      (Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop, weights)"
    by (cases remaining) simp_all
  show "comma_crt_split_mdd_result_at phase
      (fst (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf control) weights controls_for weights_for))
      (snd (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf control) weights controls_for weights_for)) =
    comma_crt_split_compose_expected_at span
      (Comma_CRT_MDD_Leaf control) weights controls_for weights_for phase"
    using built weight_eval Comma_CRT_Control_Stop
    by (cases payload_weight)
      (simp_all add: comma_crt_split_mdd_result_at_def
        comma_crt_split_compose_expected_at_def)
next
  case Comma_CRT_Control_Invalid
  obtain payload_weight where weight_eval:
      "comma_crt_mdd_eval phase weights=Some payload_weight"
    using comma_crt_mdd_admitted_eval_some[
      where lower = "4-remaining" and diagram = weights and phase = phase,
      OF weights_admitted] by blast
  have built:
    "comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid) weights
        controls_for weights_for =
      (Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid, weights)"
    by (cases remaining) simp_all
  show "comma_crt_split_mdd_result_at phase
      (fst (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf control) weights controls_for weights_for))
      (snd (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf control) weights controls_for weights_for)) =
    comma_crt_split_compose_expected_at span
      (Comma_CRT_MDD_Leaf control) weights controls_for weights_for phase"
    using built weight_eval Comma_CRT_Control_Invalid
    by (cases payload_weight)
      (simp_all add: comma_crt_split_mdd_result_at_def
        comma_crt_split_compose_expected_at_def)
qed

lemma comma_crt_split_compose_from_refines:
  fixes remaining :: nat
  assumes bound: "remaining\<le>4"
    and controls_admitted: "comma_crt_mdd_admitted (4-remaining) controls"
    and weights_admitted: "comma_crt_mdd_admitted (4-remaining) weights"
    and right_controls_admitted:
      "\<And>root. comma_crt_mdd_admitted (4-remaining) (controls_for root)"
    and right_weights_admitted:
      "\<And>root. comma_crt_mdd_admitted (4-remaining) (weights_for root)"
  shows "comma_crt_split_mdd_result_at phase
      (fst (comma_crt_split_compose_from remaining span controls weights
        controls_for weights_for))
      (snd (comma_crt_split_compose_from remaining span controls weights
        controls_for weights_for)) =
    comma_crt_split_compose_expected_at span controls weights
      controls_for weights_for phase"
  using bound controls_admitted weights_admitted
    right_controls_admitted right_weights_admitted
proof (induction remaining arbitrary: span controls weights controls_for
    weights_for phase)
  case 0
  have controls_leaf: "\<exists>value. controls = Comma_CRT_MDD_Leaf value"
  proof (cases controls)
    case (Comma_CRT_MDD_Leaf payload)
    then show ?thesis by blast
  next
    case (Comma_CRT_MDD_Node level children)
    have node_eq: "controls = Comma_CRT_MDD_Node level children"
      using Comma_CRT_MDD_Node .
    have False using "0.prems"(2)
      by (simp only: node_eq comma_crt_mdd_admitted.simps; arith)
    then show ?thesis by blast
  qed
  then obtain leaf_value where controls_eq:
      "controls = Comma_CRT_MDD_Leaf leaf_value"
    by blast
  have leaf_exact:
    "comma_crt_split_mdd_result_at phase
        (fst (comma_crt_split_compose_from 0 span
          (Comma_CRT_MDD_Leaf leaf_value) weights controls_for weights_for))
        (snd (comma_crt_split_compose_from 0 span
          (Comma_CRT_MDD_Leaf leaf_value) weights controls_for weights_for)) =
      comma_crt_split_compose_expected_at span
        (Comma_CRT_MDD_Leaf leaf_value) weights
        controls_for weights_for phase"
    by (rule comma_crt_split_leaf_refines[
      where remaining = 0 and span = span and phase = phase
        and control = leaf_value and weights = weights
        and controls_for = controls_for and weights_for = weights_for,
      OF "0.prems"(3) "0.prems"(4) "0.prems"(5)])
  show ?case using leaf_exact controls_eq by simp
next
  case (Suc remaining)
  have rem_bound: "remaining\<le>4" using Suc.prems(1) by arith
  have level_bound: "4-Suc remaining<4" using Suc.prems(1) by arith
  have lower_suc: "Suc (4-Suc remaining)=4-remaining"
    using Suc.prems(1) by arith
  show ?case
  proof (cases controls)
    case (Comma_CRT_MDD_Leaf payload)
    have leaf_exact:
      "comma_crt_split_mdd_result_at phase
          (fst (comma_crt_split_compose_from (Suc remaining) span
            (Comma_CRT_MDD_Leaf payload)
            weights controls_for weights_for))
          (snd (comma_crt_split_compose_from (Suc remaining) span
            (Comma_CRT_MDD_Leaf payload)
            weights controls_for weights_for)) =
        comma_crt_split_compose_expected_at span
          (Comma_CRT_MDD_Leaf payload) weights
          controls_for weights_for phase"
      by (rule comma_crt_split_leaf_refines[
        where remaining = "Suc remaining" and span = span and phase = phase
          and control = payload and weights = weights
          and controls_for = controls_for and weights_for = weights_for,
        OF Suc.prems(3) Suc.prems(4) Suc.prems(5)])
    show "comma_crt_split_mdd_result_at phase
          (fst (comma_crt_split_compose_from (Suc remaining) span controls
            weights controls_for weights_for))
          (snd (comma_crt_split_compose_from (Suc remaining) span controls
            weights controls_for weights_for)) =
        comma_crt_split_compose_expected_at span controls weights
          controls_for weights_for phase"
      using leaf_exact Comma_CRT_MDD_Leaf by simp
  next
    case (Comma_CRT_MDD_Node node_level children)
    let ?level = "4-Suc remaining"
    let ?period = "comma_crt_period ?level"
    let ?digit = "phase mod ?period"
    let ?left_control = "comma_crt_mdd_cofactor_or_self ?level ?digit controls"
    let ?left_weight = "comma_crt_mdd_cofactor_or_self ?level ?digit weights"
    let ?right_control = "\<lambda>root. comma_crt_mdd_cofactor_or_self ?level
      ((?digit+span) mod ?period) (controls_for root)"
    let ?right_weight = "\<lambda>root. comma_crt_mdd_cofactor_or_self ?level
      ((?digit+span) mod ?period) (weights_for root)"
    have level: "?level<4" using level_bound .
    have periods: "0<?period" by (rule comma_crt_period_positive[OF level])
    have index: "?digit<?period" using periods by simp
    have recursive_left_control:
      "comma_crt_mdd_admitted (4-remaining) ?left_control"
      using comma_crt_mdd_cofactor_or_self_admitted[
        OF Suc.prems(2) level index] lower_suc by simp
    have recursive_left_weight:
      "comma_crt_mdd_admitted (4-remaining) ?left_weight"
      using comma_crt_mdd_cofactor_or_self_admitted[
        OF Suc.prems(3) level index] lower_suc by simp
    have recursive_right_controls:
      "\<And>root. comma_crt_mdd_admitted (4-remaining) (?right_control root)"
    proof -
      fix root
      have digit_bound: "(?digit+span) mod ?period<?period"
        using periods by simp
      show "comma_crt_mdd_admitted (4-remaining) (?right_control root)"
        using comma_crt_mdd_cofactor_or_self_admitted[
          OF Suc.prems(4)[of root] level digit_bound] lower_suc by simp
    qed
    have recursive_right_weights:
      "\<And>root. comma_crt_mdd_admitted (4-remaining) (?right_weight root)"
    proof -
      fix root
      have digit_bound: "(?digit+span) mod ?period<?period"
        using periods by simp
      show "comma_crt_mdd_admitted (4-remaining) (?right_weight root)"
        using comma_crt_mdd_cofactor_or_self_admitted[
          OF Suc.prems(5)[of root] level digit_bound] lower_suc by simp
    qed
    have recursive_exact:
      "comma_crt_split_mdd_result_at phase
          (fst (comma_crt_split_compose_from remaining span
            ?left_control ?left_weight ?right_control ?right_weight))
          (snd (comma_crt_split_compose_from remaining span
            ?left_control ?left_weight ?right_control ?right_weight)) =
        comma_crt_split_compose_expected_at span
          ?left_control ?left_weight ?right_control ?right_weight phase"
      using Suc.IH[where span = span and controls = ?left_control
        and weights = ?left_weight and controls_for = ?right_control
        and weights_for = ?right_weight and phase = phase]
        rem_bound recursive_left_control recursive_left_weight
        recursive_right_controls recursive_right_weights by blast
    have left_control_eval:
      "comma_crt_mdd_eval phase ?left_control =
        comma_crt_mdd_eval phase controls"
      by (rule comma_crt_mdd_cofactor_or_self_eval[
        OF Suc.prems(2) level]) simp
    have left_weight_eval:
      "comma_crt_mdd_eval phase ?left_weight =
        comma_crt_mdd_eval phase weights"
      by (rule comma_crt_mdd_cofactor_or_self_eval[
        OF Suc.prems(3) level]) simp
    have shifted_index:
      "(?digit+span) mod ?period=(phase+span) mod ?period"
      by (rule mod_add_left_eq)
    have right_control_eval:
      "\<And>root. comma_crt_mdd_eval (phase+span) (?right_control root) =
        comma_crt_mdd_eval (phase+span) (controls_for root)"
    proof -
      fix root
      show "comma_crt_mdd_eval (phase+span) (?right_control root) =
          comma_crt_mdd_eval (phase+span) (controls_for root)"
        using comma_crt_mdd_cofactor_or_self_eval[
          where level = ?level
            and digit = "(?digit+span) mod ?period"
            and diagram = "controls_for root"
            and phase = "phase+span",
          OF Suc.prems(4)[of root] level shifted_index] .
    qed
    have right_weight_eval:
      "\<And>root. comma_crt_mdd_eval (phase+span) (?right_weight root) =
        comma_crt_mdd_eval (phase+span) (weights_for root)"
    proof -
      fix root
      show "comma_crt_mdd_eval (phase+span) (?right_weight root) =
          comma_crt_mdd_eval (phase+span) (weights_for root)"
        using comma_crt_mdd_cofactor_or_self_eval[
          where level = ?level
            and digit = "(?digit+span) mod ?period"
            and diagram = "weights_for root"
            and phase = "phase+span",
          OF Suc.prems(5)[of root] level shifted_index] .
    qed
    have expected_cofactor:
      "comma_crt_split_compose_expected_at span
          ?left_control ?left_weight ?right_control ?right_weight phase =
        comma_crt_split_compose_expected_at span controls weights
          controls_for weights_for phase"
      by (simp only: comma_crt_split_compose_expected_at_def
        comma_crt_split_mdd_result_at_def left_control_eval left_weight_eval
        right_control_eval right_weight_eval)
    let ?branches = "map (\<lambda>digit. comma_crt_split_compose_from remaining span
      (comma_crt_mdd_cofactor_or_self ?level digit controls)
      (comma_crt_mdd_cofactor_or_self ?level digit weights)
      (\<lambda>root. comma_crt_mdd_cofactor_or_self ?level
        ((digit+span) mod ?period) (controls_for root))
      (\<lambda>root. comma_crt_mdd_cofactor_or_self ?level
        ((digit+span) mod ?period) (weights_for root))) [0..<?period]"
    have built:
      "comma_crt_split_compose_from (Suc remaining) span controls weights
          controls_for weights_for =
        (comma_crt_mdd_node ?level (map fst ?branches),
         comma_crt_mdd_node ?level (map snd ?branches))"
      using Comma_CRT_MDD_Node level
      by (simp add: comma_crt_split_compose_from.simps Let_def)
    have branch_exact:
      "comma_crt_split_mdd_result_at phase
          (fst (?branches!?digit)) (snd (?branches!?digit)) =
        comma_crt_split_compose_expected_at span
          ?left_control ?left_weight ?right_control ?right_weight phase"
      using recursive_exact index
      by (simp add: nth_map nth_upt)
    have branches_width: "length ?branches=?period" by simp
    have output_control:
      "comma_crt_mdd_eval phase
          (comma_crt_mdd_node ?level (map fst ?branches)) =
        comma_crt_mdd_eval phase (fst (?branches!?digit))"
      by (rule comma_crt_mdd_node_map_projection_eval[
        where level = ?level and phase = phase and branches = ?branches
          and project = fst,
        OF level branches_width])
    have output_weight:
      "comma_crt_mdd_eval phase
          (comma_crt_mdd_node ?level (map snd ?branches)) =
        comma_crt_mdd_eval phase (snd (?branches!?digit))"
      by (rule comma_crt_mdd_node_map_projection_eval[
        where level = ?level and phase = phase and branches = ?branches
          and project = snd,
        OF level branches_width])
    show "comma_crt_split_mdd_result_at phase
        (fst (comma_crt_split_compose_from (Suc remaining) span controls
          weights controls_for weights_for))
        (snd (comma_crt_split_compose_from (Suc remaining) span controls
          weights controls_for weights_for)) =
      comma_crt_split_compose_expected_at span controls weights
        controls_for weights_for phase"
      using built branch_exact expected_cofactor output_control output_weight
      by (simp add: comma_crt_split_mdd_result_at_def)
  qed
qed


ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
    comma_crt_split_leaf_refines
    comma_crt_split_compose_from_refines
  }) then ()
  else error "Comma_CRT_Split_Power_Composition local oracle audit failed"
\<close>
end
