theory Comma_CRT_Split_Power_Admission
  imports Comma_CRT_Split_Power
begin

text \<open>
Repeated cofactor composition preserves both structural admission and the
paired control/weight invariant.  The pointwise proof follows only the
selected CRT branch; it never identifies Stop values by their erased control
tags.
\<close>

lemma comma_crt_mdd_eval_periodic:
  assumes admitted: "comma_crt_mdd_admitted lower diagram"
  shows "comma_crt_mdd_eval (phase mod 924) diagram =
    comma_crt_mdd_eval phase diagram"
  using admitted
proof (induction diagram arbitrary: lower phase)
  case (Comma_CRT_MDD_Leaf payload)
  then show ?case by simp
next
  case (Comma_CRT_MDD_Node level children)
  have level: "level<4"
    and width: "length children=comma_crt_period level"
    and children_admitted:
      "list_all (comma_crt_mdd_admitted (Suc level)) children"
    using Comma_CRT_MDD_Node.prems by auto
  have divides: "comma_crt_period level dvd 924"
    by (rule comma_crt_period_divides[OF level])
  have residue:
    "(phase mod 924) mod comma_crt_period level =
      phase mod comma_crt_period level"
    by (rule mod_mod_cancel[OF divides])
  have positive: "0<comma_crt_period level"
    by (rule comma_crt_period_positive[OF level])
  have index: "phase mod comma_crt_period level<length children"
    using positive width by simp
  have child_admitted:
    "comma_crt_mdd_admitted (Suc level)
      (children!(phase mod comma_crt_period level))"
    using children_admitted nth_mem[OF index] by (auto simp: list_all_iff)
  have child_periodic:
    "comma_crt_mdd_eval (phase mod 924)
        (children!(phase mod comma_crt_period level)) =
      comma_crt_mdd_eval phase
        (children!(phase mod comma_crt_period level))"
    by (rule Comma_CRT_MDD_Node.IH[OF nth_mem[OF index] child_admitted])
  show ?case using level width index residue child_periodic
    by (simp add: comma_crt_mdd_eval_node_selected)
qed

lemma comma_crt_mdd_node_map_projection_eval:
  fixes level phase :: nat
    and branches :: "'b list"
    and project :: "'b \<Rightarrow> 'a comma_crt_mdd"
  assumes level: "level<4"
    and width: "length branches=comma_crt_period level"
  shows "comma_crt_mdd_eval phase
      (comma_crt_mdd_node level (map project branches)) =
    comma_crt_mdd_eval phase
      (project (branches!(phase mod comma_crt_period level)))"
proof -
  have positive: "0<comma_crt_period level"
    by (rule comma_crt_period_positive[OF level])
  have index: "phase mod comma_crt_period level<length branches"
    using positive width by simp
  have node_width: "length (map project branches)=comma_crt_period level"
    using width by simp
  have reduced:
    "comma_crt_mdd_eval phase
        (comma_crt_mdd_node level (map project branches)) =
      comma_crt_mdd_eval phase
        (Comma_CRT_MDD_Node level (map project branches))"
    by (rule comma_crt_mdd_node_eval[OF level node_width])
  have selected:
    "comma_crt_mdd_eval phase
        (Comma_CRT_MDD_Node level (map project branches)) =
      comma_crt_mdd_eval phase
        ((map project branches)!(phase mod comma_crt_period level))"
    using level node_width index
    by (simp add: comma_crt_mdd_eval_node_selected nth_map)
  have mapped:
    "(map project branches)!(phase mod comma_crt_period level) =
      project (branches!(phase mod comma_crt_period level))"
    by (rule nth_map[OF index])
  show ?thesis using reduced selected mapped by simp
qed

lemma comma_crt_split_compose_from_admitted:
  fixes remaining :: nat
  assumes bound: "remaining\<le>4"
    and left_control: "comma_crt_mdd_admitted (4-remaining) controls"
    and left_weight: "comma_crt_mdd_admitted (4-remaining) weights"
    and right_control:
      "\<And>root. comma_crt_mdd_admitted (4-remaining) (controls_for root)"
    and right_weight:
      "\<And>root. comma_crt_mdd_admitted (4-remaining) (weights_for root)"
  shows "comma_crt_mdd_admitted (4-remaining)
      (fst (comma_crt_split_compose_from remaining span controls weights
        controls_for weights_for)) \<and>
    comma_crt_mdd_admitted (4-remaining)
      (snd (comma_crt_split_compose_from remaining span controls weights
        controls_for weights_for))"
  using bound left_control left_weight right_control right_weight
proof (induction remaining arbitrary: span controls weights controls_for weights_for)
  case 0
  show ?case
  proof (cases controls)
    case (Comma_CRT_MDD_Leaf control)
    then show ?thesis
    proof (cases control)
      case (Comma_CRT_Control_Live root)
      have rc: "comma_crt_mdd_admitted 4 (controls_for root)"
        using "0.prems"(4)[of root] by simp
      have rw: "comma_crt_mdd_admitted 4 (weights_for root)"
        using "0.prems"(5)[of root] by simp
      show ?thesis using Comma_CRT_MDD_Leaf Comma_CRT_Control_Live rc rw
        by (auto intro: comma_crt_mdd_shift_admitted
          comma_crt_mdd_weight_after_span_admitted)
    next
      case Comma_CRT_Control_Stop
      then show ?thesis using "0.prems"(2,3) Comma_CRT_MDD_Leaf by simp
    next
      case Comma_CRT_Control_Invalid
      then show ?thesis using "0.prems"(2,3) Comma_CRT_MDD_Leaf by simp
    qed
  next
    case (Comma_CRT_MDD_Node level children)
    then show ?thesis by simp
  qed
next
  case (Suc remaining)
  have rem_bound: "remaining\<le>4" using Suc.prems(1) by arith
  have level: "4-Suc remaining<4" using Suc.prems(1) by arith
  have depth_eq: "Suc (4-Suc remaining)=4-remaining"
    using Suc.prems(1) by arith
  show ?case
  proof (cases controls)
    case (Comma_CRT_MDD_Leaf control)
    then show ?thesis
    proof (cases control)
      case (Comma_CRT_Control_Live root)
      have rc: "comma_crt_mdd_admitted (4-Suc remaining) (controls_for root)"
        by (rule Suc.prems(4))
      have rw: "comma_crt_mdd_admitted (4-Suc remaining) (weights_for root)"
        by (rule Suc.prems(5))
      show ?thesis using Comma_CRT_MDD_Leaf Comma_CRT_Control_Live rc rw
        by (auto intro: comma_crt_mdd_shift_admitted
          comma_crt_mdd_weight_after_span_admitted)
    next
      case Comma_CRT_Control_Stop
      then show ?thesis using Suc.prems(2,3) Comma_CRT_MDD_Leaf by simp
    next
      case Comma_CRT_Control_Invalid
      then show ?thesis using Suc.prems(2,3) Comma_CRT_MDD_Leaf by simp
    qed
  next
    case (Comma_CRT_MDD_Node node_level children)
    let ?period = "comma_crt_period (4-Suc remaining)"
    let ?branch = "\<lambda>digit. comma_crt_split_compose_from remaining span
      (comma_crt_mdd_cofactor_or_self (4-Suc remaining) digit controls)
      (comma_crt_mdd_cofactor_or_self (4-Suc remaining) digit weights)
      (\<lambda>root. comma_crt_mdd_cofactor_or_self (4-Suc remaining)
        ((digit+span) mod ?period) (controls_for root))
      (\<lambda>root. comma_crt_mdd_cofactor_or_self (4-Suc remaining)
        ((digit+span) mod ?period) (weights_for root))"
    let ?branches = "map ?branch [0..<?period]"
    have period_positive: "0<?period"
      by (rule comma_crt_period_positive[OF level])
    have branches_admitted:
      "list_all (\<lambda>branch.
        comma_crt_mdd_admitted (Suc (4-Suc remaining)) (fst branch) \<and>
        comma_crt_mdd_admitted (Suc (4-Suc remaining)) (snd branch)) ?branches"
    proof -
      have each:
        "\<forall>digit\<in>set [0..<?period].
          comma_crt_mdd_admitted (Suc (4-Suc remaining)) (fst (?branch digit)) \<and>
          comma_crt_mdd_admitted (Suc (4-Suc remaining)) (snd (?branch digit))"
      proof (intro ballI)
        fix digit
        assume digit_in: "digit\<in>set [0..<?period]"
        have digit_bound: "digit<?period" using digit_in by simp
        have left_control_admitted:
          "comma_crt_mdd_admitted (4-remaining)
            (comma_crt_mdd_cofactor_or_self (4-Suc remaining) digit controls)"
          using comma_crt_mdd_cofactor_or_self_admitted[
              OF Suc.prems(2) level digit_bound] depth_eq
          by (simp only: depth_eq)
        have left_weight_admitted:
          "comma_crt_mdd_admitted (4-remaining)
            (comma_crt_mdd_cofactor_or_self (4-Suc remaining) digit weights)"
          using comma_crt_mdd_cofactor_or_self_admitted[
              OF Suc.prems(3) level digit_bound] depth_eq
          by (simp only: depth_eq)
        have right_control_admitted:
          "\<And>root. comma_crt_mdd_admitted (4-remaining)
            (comma_crt_mdd_cofactor_or_self (4-Suc remaining)
              ((digit+span) mod ?period) (controls_for root))"
        proof -
          fix root
          have index: "(digit+span) mod ?period<?period"
            using period_positive by simp
          show "comma_crt_mdd_admitted (4-remaining)
            (comma_crt_mdd_cofactor_or_self (4-Suc remaining)
              ((digit+span) mod ?period) (controls_for root))"
            using comma_crt_mdd_cofactor_or_self_admitted[
              OF Suc.prems(4)[of root] level index] depth_eq
            by (simp only: depth_eq)
        qed
        have right_weight_admitted:
          "\<And>root. comma_crt_mdd_admitted (4-remaining)
            (comma_crt_mdd_cofactor_or_self (4-Suc remaining)
              ((digit+span) mod ?period) (weights_for root))"
        proof -
          fix root
          have index: "(digit+span) mod ?period<?period"
            using period_positive by simp
          show "comma_crt_mdd_admitted (4-remaining)
            (comma_crt_mdd_cofactor_or_self (4-Suc remaining)
              ((digit+span) mod ?period) (weights_for root))"
            using comma_crt_mdd_cofactor_or_self_admitted[
              OF Suc.prems(5)[of root] level index] depth_eq
            by (simp only: depth_eq)
        qed
        have recursive:
          "comma_crt_mdd_admitted (4-remaining) (fst (?branch digit)) \<and>
            comma_crt_mdd_admitted (4-remaining) (snd (?branch digit))"
          using Suc.IH[where span=span
              and controls="comma_crt_mdd_cofactor_or_self (4-Suc remaining) digit controls"
              and weights="comma_crt_mdd_cofactor_or_self (4-Suc remaining) digit weights"
              and controls_for="\<lambda>root. comma_crt_mdd_cofactor_or_self (4-Suc remaining)
                ((digit+span) mod ?period) (controls_for root)"
              and weights_for="\<lambda>root. comma_crt_mdd_cofactor_or_self (4-Suc remaining)
                ((digit+span) mod ?period) (weights_for root)"]
            rem_bound left_control_admitted left_weight_admitted
            right_control_admitted right_weight_admitted by blast
        show "comma_crt_mdd_admitted (Suc (4-Suc remaining)) (fst (?branch digit)) \<and>
          comma_crt_mdd_admitted (Suc (4-Suc remaining)) (snd (?branch digit))"
          using recursive by (simp only: depth_eq)
      qed
      show ?thesis using each by (simp add: list_all_iff)
    qed
    have branches_control:
      "list_all (comma_crt_mdd_admitted (Suc (4-Suc remaining))) (map fst ?branches)"
      using branches_admitted by (auto simp: list_all_iff)
    have branches_weight:
      "list_all (comma_crt_mdd_admitted (Suc (4-Suc remaining))) (map snd ?branches)"
      using branches_admitted by (auto simp: list_all_iff)
    have branch_lengths:
      "length (map fst ?branches)=?period"
      "length (map snd ?branches)=?period"
      by (simp_all add: length_map)
    have composed:
      "comma_crt_split_compose_from (Suc remaining) span controls weights
          controls_for weights_for =
        (comma_crt_mdd_node (4-Suc remaining) (map fst ?branches),
         comma_crt_mdd_node (4-Suc remaining) (map snd ?branches))"
      using level Comma_CRT_MDD_Node by (simp add: Let_def)
    have output_control:
      "comma_crt_mdd_admitted (4-Suc remaining)
        (comma_crt_mdd_node (4-Suc remaining) (map fst ?branches))"
      by (rule comma_crt_mdd_node_admitted[OF order_refl level
        branch_lengths(1) branches_control])
    have output_weight:
      "comma_crt_mdd_admitted (4-Suc remaining)
        (comma_crt_mdd_node (4-Suc remaining) (map snd ?branches))"
      by (rule comma_crt_mdd_node_admitted[OF order_refl level
        branch_lengths(2) branches_weight])
    show ?thesis using composed output_control output_weight by simp
  qed
qed

lemma comma_crt_split_compose_from_pointwise_consistent:
  fixes remaining :: nat
  assumes bound: "remaining\<le>4"
    and left_control: "comma_crt_mdd_admitted (4-remaining) controls"
    and left_weight: "comma_crt_mdd_admitted (4-remaining) weights"
    and right_control:
      "\<And>root. comma_crt_mdd_admitted (4-remaining) (controls_for root)"
    and right_weight:
      "\<And>root. comma_crt_mdd_admitted (4-remaining) (weights_for root)"
    and left_values:
      "\<exists>control weight.
        comma_crt_mdd_eval phase controls=Some control \<and>
        comma_crt_mdd_eval phase weights=Some weight \<and>
        comma_crt_split_value_consistent control weight"
    and right_values:
      "\<And>root. \<exists>control weight.
        comma_crt_mdd_eval (phase+span) (controls_for root)=Some control \<and>
        comma_crt_mdd_eval (phase+span) (weights_for root)=Some weight \<and>
        comma_crt_split_value_consistent control weight"
  shows "\<exists>control weight.
    comma_crt_mdd_eval phase
      (fst (comma_crt_split_compose_from remaining span controls weights
        controls_for weights_for))=Some control \<and>
    comma_crt_mdd_eval phase
      (snd (comma_crt_split_compose_from remaining span controls weights
        controls_for weights_for))=Some weight \<and>
    comma_crt_split_value_consistent control weight"
  using bound left_control left_weight right_control right_weight left_values right_values
proof (induction remaining arbitrary: span controls weights controls_for weights_for)
  case 0
  show ?case
  proof (cases controls)
    case (Comma_CRT_MDD_Leaf control)
    then show ?thesis
    proof (cases control)
      case (Comma_CRT_Control_Live root)
      obtain right_control_value right_weight_value where
        right_control_eval:
          "comma_crt_mdd_eval (phase+span) (controls_for root)=Some right_control_value"
        and right_weight_eval:
          "comma_crt_mdd_eval (phase+span) (weights_for root)=Some right_weight_value"
        and right_consistent:
          "comma_crt_split_value_consistent right_control_value right_weight_value"
        using "0.prems"(7)[of root] by blast
      have shifted_control_eval:
        "comma_crt_mdd_eval phase (comma_crt_mdd_shift span (controls_for root)) =
          Some right_control_value"
        using right_control_eval comma_crt_mdd_shift_eval[
          OF "0.prems"(4), of phase span] by simp
      have shifted_weight_admitted:
        "comma_crt_mdd_admitted 4 (comma_crt_mdd_shift span (weights_for root))"
        using comma_crt_mdd_shift_admitted[OF "0.prems"(5)[of root]] by simp
      have shifted_weight_eval:
        "comma_crt_mdd_eval phase (comma_crt_mdd_shift span (weights_for root)) =
          Some right_weight_value"
        using right_weight_eval comma_crt_mdd_shift_eval[
          OF "0.prems"(5), of phase span] by simp
      have mapped_weight_eval:
        "comma_crt_mdd_eval phase
          (comma_crt_mdd_map (\<lambda>weight. case weight of None \<Rightarrow> None
            | Some D \<Rightarrow> Some (9*span+D))
            (comma_crt_mdd_shift span (weights_for root))) =
          map_option (\<lambda>weight. case weight of None \<Rightarrow> None
            | Some D \<Rightarrow> Some (9*span+D)) (Some right_weight_value)"
        using comma_crt_mdd_map_eval[OF shifted_weight_admitted, of phase
          "\<lambda>weight. case weight of None \<Rightarrow> None
            | Some D \<Rightarrow> Some (9*span+D)"] shifted_weight_eval by simp
      show ?thesis using shifted_control_eval mapped_weight_eval
          Comma_CRT_MDD_Leaf Comma_CRT_Control_Live right_consistent
        by (cases right_control_value; cases right_weight_value)
          (auto simp: comma_crt_mdd_weight_after_span_def
            comma_crt_split_value_consistent.simps)
    next
      case Comma_CRT_Control_Stop
      obtain control_value weight_value where
        control_eval: "comma_crt_mdd_eval phase controls=Some control_value"
        and weight_eval: "comma_crt_mdd_eval phase weights=Some weight_value"
        and consistent:
          "comma_crt_split_value_consistent control_value weight_value"
        using "0.prems"(6) by blast
      have composed:
        "comma_crt_split_compose_from 0 span controls weights controls_for weights_for =
          (Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop, weights)"
        using Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop by simp
      have control_value_eq: "control_value=Comma_CRT_Control_Stop"
        using control_eval Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop by simp
      have output_control_eval:
        "comma_crt_mdd_eval phase
          (fst (comma_crt_split_compose_from 0 span controls weights
            controls_for weights_for))=Some Comma_CRT_Control_Stop"
        using composed by (simp only: composed fst_conv comma_crt_mdd_eval.simps(1))
      have output_weight_eval:
        "comma_crt_mdd_eval phase
          (snd (comma_crt_split_compose_from 0 span controls weights
            controls_for weights_for))=Some weight_value"
        using composed weight_eval by (simp only: composed snd_conv weight_eval)
      have output_consistent:
        "comma_crt_split_value_consistent Comma_CRT_Control_Stop weight_value"
        using consistent control_value_eq by simp
      show ?thesis
      proof (rule exI[of _ Comma_CRT_Control_Stop], rule exI[of _ weight_value])
        show "comma_crt_mdd_eval phase
              (fst (comma_crt_split_compose_from 0 span controls weights
                controls_for weights_for))=Some Comma_CRT_Control_Stop \<and>
            comma_crt_mdd_eval phase
              (snd (comma_crt_split_compose_from 0 span controls weights
                controls_for weights_for))=Some weight_value \<and>
            comma_crt_split_value_consistent Comma_CRT_Control_Stop weight_value"
          by (intro conjI; fact output_control_eval output_weight_eval output_consistent)
      qed
    next
      case Comma_CRT_Control_Invalid
      obtain control_value weight_value where
        control_eval: "comma_crt_mdd_eval phase controls=Some control_value"
        and weight_eval: "comma_crt_mdd_eval phase weights=Some weight_value"
        and consistent:
          "comma_crt_split_value_consistent control_value weight_value"
        using "0.prems"(6) by blast
      have composed:
        "comma_crt_split_compose_from 0 span controls weights controls_for weights_for =
          (Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid, weights)"
        using Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid by simp
      have control_value_eq: "control_value=Comma_CRT_Control_Invalid"
        using control_eval Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid by simp
      have output_control_eval:
        "comma_crt_mdd_eval phase
          (fst (comma_crt_split_compose_from 0 span controls weights
            controls_for weights_for))=Some Comma_CRT_Control_Invalid"
        using composed by (simp only: composed fst_conv comma_crt_mdd_eval.simps(1))
      have output_weight_eval:
        "comma_crt_mdd_eval phase
          (snd (comma_crt_split_compose_from 0 span controls weights
            controls_for weights_for))=Some weight_value"
        using composed weight_eval by (simp only: composed snd_conv weight_eval)
      have output_consistent:
        "comma_crt_split_value_consistent Comma_CRT_Control_Invalid weight_value"
        using consistent control_value_eq by simp
      show ?thesis
      proof (rule exI[of _ Comma_CRT_Control_Invalid], rule exI[of _ weight_value])
        show "comma_crt_mdd_eval phase
              (fst (comma_crt_split_compose_from 0 span controls weights
                controls_for weights_for))=Some Comma_CRT_Control_Invalid \<and>
            comma_crt_mdd_eval phase
              (snd (comma_crt_split_compose_from 0 span controls weights
                controls_for weights_for))=Some weight_value \<and>
            comma_crt_split_value_consistent Comma_CRT_Control_Invalid weight_value"
          by (intro conjI; fact output_control_eval output_weight_eval output_consistent)
      qed
    qed
  next
    case (Comma_CRT_MDD_Node level children)
    have composed:
      "comma_crt_split_compose_from 0 span controls weights controls_for weights_for =
        (Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid,
         Comma_CRT_MDD_Leaf None)"
      using Comma_CRT_MDD_Node by simp
    show ?thesis
    proof (rule exI[of _ Comma_CRT_Control_Invalid], rule exI[of _ None])
      show "comma_crt_mdd_eval phase
            (fst (comma_crt_split_compose_from 0 span controls weights
              controls_for weights_for))=Some Comma_CRT_Control_Invalid \<and>
          comma_crt_mdd_eval phase
            (snd (comma_crt_split_compose_from 0 span controls weights
              controls_for weights_for))=Some None \<and>
          comma_crt_split_value_consistent Comma_CRT_Control_Invalid None"
        using composed
        by (simp only: composed fst_conv snd_conv comma_crt_mdd_eval.simps(1)
          comma_crt_split_value_consistent.simps)
    qed
  qed
next
  case (Suc remaining)
  have rem_bound: "remaining\<le>4" using Suc.prems(1) by arith
  have level: "4-Suc remaining<4" using Suc.prems(1) by arith
  have depth_eq: "Suc (4-Suc remaining)=4-remaining"
    using Suc.prems(1) by arith
  show ?case
  proof (cases controls)
    case (Comma_CRT_MDD_Leaf control)
    then show ?thesis
    proof (cases control)
      case (Comma_CRT_Control_Live root)
      obtain right_control_value right_weight_value where
        right_control_eval:
          "comma_crt_mdd_eval (phase+span) (controls_for root)=Some right_control_value"
        and right_weight_eval:
          "comma_crt_mdd_eval (phase+span) (weights_for root)=Some right_weight_value"
        and right_consistent:
          "comma_crt_split_value_consistent right_control_value right_weight_value"
        using Suc.prems(7)[of root] by blast
      have shifted_control_eval:
        "comma_crt_mdd_eval phase (comma_crt_mdd_shift span (controls_for root)) =
          Some right_control_value"
        using right_control_eval comma_crt_mdd_shift_eval[
          OF Suc.prems(4), of phase span] by simp
      have shifted_weight_admitted:
        "comma_crt_mdd_admitted (4-Suc remaining)
          (comma_crt_mdd_shift span (weights_for root))"
        by (rule comma_crt_mdd_shift_admitted[OF Suc.prems(5)])
      have shifted_weight_eval:
        "comma_crt_mdd_eval phase (comma_crt_mdd_shift span (weights_for root)) =
          Some right_weight_value"
        using right_weight_eval comma_crt_mdd_shift_eval[
          OF Suc.prems(5), of phase span] by simp
      have mapped_weight_eval:
        "comma_crt_mdd_eval phase
          (comma_crt_mdd_map (\<lambda>weight. case weight of None \<Rightarrow> None
            | Some D \<Rightarrow> Some (9*span+D))
            (comma_crt_mdd_shift span (weights_for root))) =
          map_option (\<lambda>weight. case weight of None \<Rightarrow> None
            | Some D \<Rightarrow> Some (9*span+D)) (Some right_weight_value)"
        using comma_crt_mdd_map_eval[OF shifted_weight_admitted, of phase
          "\<lambda>weight. case weight of None \<Rightarrow> None
            | Some D \<Rightarrow> Some (9*span+D)"] shifted_weight_eval by simp
      show ?thesis using shifted_control_eval mapped_weight_eval
          Comma_CRT_MDD_Leaf Comma_CRT_Control_Live right_consistent
        by (cases right_control_value; cases right_weight_value)
          (auto simp: comma_crt_mdd_weight_after_span_def
            comma_crt_split_value_consistent.simps)
    next
      case Comma_CRT_Control_Stop
      obtain control_value weight_value where
        control_eval: "comma_crt_mdd_eval phase controls=Some control_value"
        and weight_eval: "comma_crt_mdd_eval phase weights=Some weight_value"
        and consistent:
          "comma_crt_split_value_consistent control_value weight_value"
        using Suc.prems(6) by blast
      have composed:
        "comma_crt_split_compose_from (Suc remaining) span controls weights
          controls_for weights_for =
          (Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop, weights)"
        using Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop by simp
      have control_value_eq: "control_value=Comma_CRT_Control_Stop"
        using control_eval Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop by simp
      have output_control_eval:
        "comma_crt_mdd_eval phase
          (fst (comma_crt_split_compose_from (Suc remaining) span controls weights
            controls_for weights_for))=Some Comma_CRT_Control_Stop"
        using composed by (simp only: composed fst_conv comma_crt_mdd_eval.simps(1))
      have output_weight_eval:
        "comma_crt_mdd_eval phase
          (snd (comma_crt_split_compose_from (Suc remaining) span controls weights
            controls_for weights_for))=Some weight_value"
        using composed weight_eval by (simp only: composed snd_conv weight_eval)
      have output_consistent:
        "comma_crt_split_value_consistent Comma_CRT_Control_Stop weight_value"
        using consistent control_value_eq by simp
      show ?thesis
      proof (rule exI[of _ Comma_CRT_Control_Stop], rule exI[of _ weight_value])
        show "comma_crt_mdd_eval phase
              (fst (comma_crt_split_compose_from (Suc remaining) span controls weights
                controls_for weights_for))=Some Comma_CRT_Control_Stop \<and>
            comma_crt_mdd_eval phase
              (snd (comma_crt_split_compose_from (Suc remaining) span controls weights
                controls_for weights_for))=Some weight_value \<and>
            comma_crt_split_value_consistent Comma_CRT_Control_Stop weight_value"
          by (intro conjI; fact output_control_eval output_weight_eval output_consistent)
      qed
    next
      case Comma_CRT_Control_Invalid
      obtain control_value weight_value where
        control_eval: "comma_crt_mdd_eval phase controls=Some control_value"
        and weight_eval: "comma_crt_mdd_eval phase weights=Some weight_value"
        and consistent:
          "comma_crt_split_value_consistent control_value weight_value"
        using Suc.prems(6) by blast
      have composed:
        "comma_crt_split_compose_from (Suc remaining) span controls weights
          controls_for weights_for =
          (Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid, weights)"
        using Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid by simp
      have control_value_eq: "control_value=Comma_CRT_Control_Invalid"
        using control_eval Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid by simp
      have output_control_eval:
        "comma_crt_mdd_eval phase
          (fst (comma_crt_split_compose_from (Suc remaining) span controls weights
            controls_for weights_for))=Some Comma_CRT_Control_Invalid"
        using composed by (simp only: composed fst_conv comma_crt_mdd_eval.simps(1))
      have output_weight_eval:
        "comma_crt_mdd_eval phase
          (snd (comma_crt_split_compose_from (Suc remaining) span controls weights
            controls_for weights_for))=Some weight_value"
        using composed weight_eval by (simp only: composed snd_conv weight_eval)
      have output_consistent:
        "comma_crt_split_value_consistent Comma_CRT_Control_Invalid weight_value"
        using consistent control_value_eq by simp
      show ?thesis
      proof (rule exI[of _ Comma_CRT_Control_Invalid], rule exI[of _ weight_value])
        show "comma_crt_mdd_eval phase
              (fst (comma_crt_split_compose_from (Suc remaining) span controls weights
                controls_for weights_for))=Some Comma_CRT_Control_Invalid \<and>
            comma_crt_mdd_eval phase
              (snd (comma_crt_split_compose_from (Suc remaining) span controls weights
                controls_for weights_for))=Some weight_value \<and>
            comma_crt_split_value_consistent Comma_CRT_Control_Invalid weight_value"
          by (intro conjI; fact output_control_eval output_weight_eval output_consistent)
      qed
    qed
  next
    case (Comma_CRT_MDD_Node node_level children)
    let ?period = "comma_crt_period (4-Suc remaining)"
    let ?digit = "phase mod ?period"
    let ?left_control =
      "comma_crt_mdd_cofactor_or_self (4-Suc remaining) ?digit controls"
    let ?left_weight =
      "comma_crt_mdd_cofactor_or_self (4-Suc remaining) ?digit weights"
    let ?right_control = "\<lambda>root. comma_crt_mdd_cofactor_or_self (4-Suc remaining)
      ((?digit+span) mod ?period) (controls_for root)"
    let ?right_weight = "\<lambda>root. comma_crt_mdd_cofactor_or_self (4-Suc remaining)
      ((?digit+span) mod ?period) (weights_for root)"
    let ?branch = "\<lambda>digit. comma_crt_split_compose_from remaining span
      (comma_crt_mdd_cofactor_or_self (4-Suc remaining) digit controls)
      (comma_crt_mdd_cofactor_or_self (4-Suc remaining) digit weights)
      (\<lambda>root. comma_crt_mdd_cofactor_or_self (4-Suc remaining)
        ((digit+span) mod ?period) (controls_for root))
      (\<lambda>root. comma_crt_mdd_cofactor_or_self (4-Suc remaining)
        ((digit+span) mod ?period) (weights_for root))"
    let ?branches = "map ?branch [0..<?period]"
    have period_positive: "0<?period"
      by (rule comma_crt_period_positive[OF level])
    have digit_bound: "?digit<?period" using period_positive by simp
    have right_index:
      "(?digit+span) mod ?period=(phase+span) mod ?period"
      by (simp add: mod_add_left_eq)
    have left_control_admitted:
      "comma_crt_mdd_admitted (4-remaining) ?left_control"
      using comma_crt_mdd_cofactor_or_self_admitted[
        OF Suc.prems(2) level digit_bound] depth_eq
      by (simp only: depth_eq)
    have left_weight_admitted:
      "comma_crt_mdd_admitted (4-remaining) ?left_weight"
      using comma_crt_mdd_cofactor_or_self_admitted[
        OF Suc.prems(3) level digit_bound] depth_eq
      by (simp only: depth_eq)
    have right_control_admitted:
      "\<And>root. comma_crt_mdd_admitted (4-remaining) (?right_control root)"
    proof -
      fix root
      have index: "((?digit+span) mod ?period)<?period"
        using period_positive by simp
      show "comma_crt_mdd_admitted (4-remaining) (?right_control root)"
        using comma_crt_mdd_cofactor_or_self_admitted[
          OF Suc.prems(4)[of root] level index] depth_eq
        by (simp only: depth_eq)
    qed
    have right_weight_admitted:
      "\<And>root. comma_crt_mdd_admitted (4-remaining) (?right_weight root)"
    proof -
      fix root
      have index: "((?digit+span) mod ?period)<?period"
        using period_positive by simp
      show "comma_crt_mdd_admitted (4-remaining) (?right_weight root)"
        using comma_crt_mdd_cofactor_or_self_admitted[
          OF Suc.prems(5)[of root] level index] depth_eq
        by (simp only: depth_eq)
    qed
    obtain left_control_value left_weight_value where
      left_control_eval:
        "comma_crt_mdd_eval phase controls=Some left_control_value"
      and left_weight_eval:
        "comma_crt_mdd_eval phase weights=Some left_weight_value"
      and left_consistent:
        "comma_crt_split_value_consistent left_control_value left_weight_value"
      using Suc.prems(6) by blast
    have left_control_cofactor_eval:
      "comma_crt_mdd_eval phase ?left_control=Some left_control_value"
      using comma_crt_mdd_cofactor_or_self_eval[OF Suc.prems(2) level]
        left_control_eval by simp
    have left_weight_cofactor_eval:
      "comma_crt_mdd_eval phase ?left_weight=Some left_weight_value"
      using comma_crt_mdd_cofactor_or_self_eval[OF Suc.prems(3) level]
        left_weight_eval by simp
    have recursive_left_values:
      "\<exists>control weight. comma_crt_mdd_eval phase ?left_control=Some control \<and>
        comma_crt_mdd_eval phase ?left_weight=Some weight \<and>
        comma_crt_split_value_consistent control weight"
      using left_control_cofactor_eval left_weight_cofactor_eval left_consistent by blast
    have recursive_right_values:
      "\<And>root. \<exists>control weight.
        comma_crt_mdd_eval (phase+span) (?right_control root)=Some control \<and>
        comma_crt_mdd_eval (phase+span) (?right_weight root)=Some weight \<and>
        comma_crt_split_value_consistent control weight"
    proof -
      fix root
      obtain control_value weight_value where
        control_eval:
          "comma_crt_mdd_eval (phase+span) (controls_for root)=Some control_value"
        and weight_eval:
          "comma_crt_mdd_eval (phase+span) (weights_for root)=Some weight_value"
        and consistent:
          "comma_crt_split_value_consistent control_value weight_value"
        using Suc.prems(7)[of root] by blast
      have control_cofactor_eval:
        "comma_crt_mdd_eval (phase+span) (?right_control root)=Some control_value"
        using comma_crt_mdd_cofactor_or_self_eval[
            OF Suc.prems(4)[of root] level]
          control_eval right_index by simp
      have weight_cofactor_eval:
        "comma_crt_mdd_eval (phase+span) (?right_weight root)=Some weight_value"
        using comma_crt_mdd_cofactor_or_self_eval[
            OF Suc.prems(5)[of root] level]
          weight_eval right_index by simp
      show "\<exists>control weight.
        comma_crt_mdd_eval (phase+span) (?right_control root)=Some control \<and>
        comma_crt_mdd_eval (phase+span) (?right_weight root)=Some weight \<and>
        comma_crt_split_value_consistent control weight"
        using control_cofactor_eval weight_cofactor_eval consistent by blast
    qed
    have recursive:
      "\<exists>control weight.
        comma_crt_mdd_eval phase (fst (?branch ?digit))=Some control \<and>
        comma_crt_mdd_eval phase (snd (?branch ?digit))=Some weight \<and>
        comma_crt_split_value_consistent control weight"
      using Suc.IH[where span=span and controls="?left_control"
          and weights="?left_weight" and controls_for="?right_control"
          and weights_for="?right_weight"]
        rem_bound left_control_admitted left_weight_admitted
        right_control_admitted right_weight_admitted
        recursive_left_values recursive_right_values by blast
    have branches_length: "length ?branches=?period"
      by (simp add: length_map)
    have composed:
      "comma_crt_split_compose_from (Suc remaining) span controls weights
          controls_for weights_for =
        (comma_crt_mdd_node (4-Suc remaining) (map fst ?branches),
         comma_crt_mdd_node (4-Suc remaining) (map snd ?branches))"
      using level Comma_CRT_MDD_Node by (simp add: Let_def)
    have output_control:
      "comma_crt_mdd_eval phase (fst
          (comma_crt_split_compose_from (Suc remaining) span controls weights
            controls_for weights_for)) =
        comma_crt_mdd_eval phase (fst (?branch ?digit))"
    proof -
      have selected:
        "comma_crt_mdd_eval phase
            (comma_crt_mdd_node (4-Suc remaining) (map fst ?branches)) =
          comma_crt_mdd_eval phase (fst (?branches!?digit))"
        by (rule comma_crt_mdd_node_map_projection_eval[where project=fst, OF level])
          (simp add: branches_length)
      have branch_at: "?branches!?digit=?branch ?digit"
        using digit_bound by simp
      show ?thesis using selected branch_at composed by simp
    qed
    have output_weight:
      "comma_crt_mdd_eval phase (snd
          (comma_crt_split_compose_from (Suc remaining) span controls weights
            controls_for weights_for)) =
        comma_crt_mdd_eval phase (snd (?branch ?digit))"
    proof -
      have selected:
        "comma_crt_mdd_eval phase
            (comma_crt_mdd_node (4-Suc remaining) (map snd ?branches)) =
          comma_crt_mdd_eval phase (snd (?branches!?digit))"
        by (rule comma_crt_mdd_node_map_projection_eval[where project=snd, OF level])
          (simp add: branches_length)
      have branch_at: "?branches!?digit=?branch ?digit"
        using digit_bound by simp
      show ?thesis using selected branch_at composed by simp
    qed
    obtain control_value weight_value where
      control_eval: "comma_crt_mdd_eval phase (fst (?branch ?digit))=Some control_value"
      and weight_eval: "comma_crt_mdd_eval phase (snd (?branch ?digit))=Some weight_value"
      and consistent:
        "comma_crt_split_value_consistent control_value weight_value"
      using recursive by blast
    show ?thesis
    proof (rule exI[of _ control_value], rule exI[of _ weight_value])
      show "comma_crt_mdd_eval phase
          (fst (comma_crt_split_compose_from (Suc remaining) span controls weights
            controls_for weights_for))=Some control_value \<and>
        comma_crt_mdd_eval phase
          (snd (comma_crt_split_compose_from (Suc remaining) span controls weights
            controls_for weights_for))=Some weight_value \<and>
        comma_crt_split_value_consistent control_value weight_value"
        using output_control output_weight control_eval weight_eval consistent
        by (simp only: output_control output_weight control_eval weight_eval; fact)
    qed
  qed
qed

lemma comma_crt_split_compose_from_consistent:
  fixes remaining :: nat
  assumes bound: "remaining\<le>4"
    and left:
      "comma_crt_mdd_split_consistent (4-remaining) controls weights"
    and right:
      "\<And>root. comma_crt_mdd_split_consistent (4-remaining)
        (controls_for root) (weights_for root)"
  shows "comma_crt_mdd_split_consistent (4-remaining)
    (fst (comma_crt_split_compose_from remaining span controls weights
      controls_for weights_for))
    (snd (comma_crt_split_compose_from remaining span controls weights
      controls_for weights_for))"
proof -
  have left_control:
    "comma_crt_mdd_admitted (4-remaining) controls"
    and left_weight:
    "comma_crt_mdd_admitted (4-remaining) weights"
    using left by (auto simp: comma_crt_mdd_split_consistent_def)
  have right_control:
    "\<And>root. comma_crt_mdd_admitted (4-remaining) (controls_for root)"
    and right_weight:
    "\<And>root. comma_crt_mdd_admitted (4-remaining) (weights_for root)"
    using right by (auto simp: comma_crt_mdd_split_consistent_def)
  have output_admitted:
    "comma_crt_mdd_admitted (4-remaining)
        (fst (comma_crt_split_compose_from remaining span controls weights
          controls_for weights_for)) \<and>
      comma_crt_mdd_admitted (4-remaining)
        (snd (comma_crt_split_compose_from remaining span controls weights
          controls_for weights_for))"
    by (rule comma_crt_split_compose_from_admitted[
      OF bound left_control left_weight right_control right_weight])
  have output_values_consistent:
    "\<forall>phase<924. case
      (comma_crt_mdd_eval phase
        (fst (comma_crt_split_compose_from remaining span controls weights
          controls_for weights_for)),
       comma_crt_mdd_eval phase
        (snd (comma_crt_split_compose_from remaining span controls weights
          controls_for weights_for))) of
        (Some control,Some weight) \<Rightarrow>
          comma_crt_split_value_consistent control weight
      | _ \<Rightarrow> False"
  proof (intro allI impI)
    fix phase :: nat
    assume phase_bound: "phase<924"
    obtain left_control_value left_weight_value where
      left_control_eval: "comma_crt_mdd_eval phase controls=Some left_control_value"
      and left_weight_eval: "comma_crt_mdd_eval phase weights=Some left_weight_value"
      and left_value_consistent:
        "comma_crt_split_value_consistent left_control_value left_weight_value"
    proof -
      obtain control_value where eval_control:
        "comma_crt_mdd_eval phase controls=Some control_value"
        using comma_crt_mdd_admitted_eval_some[OF left_control] by blast
      obtain weight_value where eval_weight:
        "comma_crt_mdd_eval phase weights=Some weight_value"
        using comma_crt_mdd_admitted_eval_some[OF left_weight] by blast
      have pair_consistent:
        "case (comma_crt_mdd_eval phase controls,
          comma_crt_mdd_eval phase weights) of
          (Some control,Some weight) \<Rightarrow>
            comma_crt_split_value_consistent control weight | _ \<Rightarrow> False"
        using left phase_bound by (auto simp: comma_crt_mdd_split_consistent_def)
      show thesis using that[of control_value weight_value]
        eval_control eval_weight pair_consistent by simp
    qed
    have right_values:
      "\<And>root. \<exists>control weight.
        comma_crt_mdd_eval (phase+span) (controls_for root)=Some control \<and>
        comma_crt_mdd_eval (phase+span) (weights_for root)=Some weight \<and>
        comma_crt_split_value_consistent control weight"
    proof -
      fix root
      let ?right_phase = "(phase+span) mod 924"
      have right_phase_bound: "?right_phase<924" by simp
      obtain control_value weight_value where
        control_eval:
          "comma_crt_mdd_eval ?right_phase (controls_for root)=Some control_value"
        and weight_eval:
          "comma_crt_mdd_eval ?right_phase (weights_for root)=Some weight_value"
        and consistent:
          "comma_crt_split_value_consistent control_value weight_value"
      proof -
        obtain control_value where eval_control:
          "comma_crt_mdd_eval ?right_phase (controls_for root)=Some control_value"
          using comma_crt_mdd_admitted_eval_some[OF right_control[of root]] by blast
        obtain weight_value where eval_weight:
          "comma_crt_mdd_eval ?right_phase (weights_for root)=Some weight_value"
          using comma_crt_mdd_admitted_eval_some[OF right_weight[of root]] by blast
        have pair_consistent:
          "case (comma_crt_mdd_eval ?right_phase (controls_for root),
            comma_crt_mdd_eval ?right_phase (weights_for root)) of
            (Some control,Some weight) \<Rightarrow>
              comma_crt_split_value_consistent control weight | _ \<Rightarrow> False"
          using right[of root] right_phase_bound
          by (auto simp: comma_crt_mdd_split_consistent_def)
        show thesis using that[of control_value weight_value]
          eval_control eval_weight pair_consistent by simp
      qed
      have control_periodic:
        "comma_crt_mdd_eval ?right_phase (controls_for root) =
          comma_crt_mdd_eval (phase+span) (controls_for root)"
        by (rule comma_crt_mdd_eval_periodic[OF right_control[of root]])
      have weight_periodic:
        "comma_crt_mdd_eval ?right_phase (weights_for root) =
          comma_crt_mdd_eval (phase+span) (weights_for root)"
        by (rule comma_crt_mdd_eval_periodic[OF right_weight[of root]])
      show "\<exists>control weight.
        comma_crt_mdd_eval (phase+span) (controls_for root)=Some control \<and>
        comma_crt_mdd_eval (phase+span) (weights_for root)=Some weight \<and>
        comma_crt_split_value_consistent control weight"
      proof (rule exI[of _ control_value], rule exI[of _ weight_value])
        show "comma_crt_mdd_eval (phase+span) (controls_for root)=Some control_value \<and>
          comma_crt_mdd_eval (phase+span) (weights_for root)=Some weight_value \<and>
          comma_crt_split_value_consistent control_value weight_value"
        proof -
          have control_direct:
            "comma_crt_mdd_eval (phase+span) (controls_for root)=Some control_value"
          proof -
            have "comma_crt_mdd_eval (phase+span) (controls_for root) =
                comma_crt_mdd_eval ?right_phase (controls_for root)"
              by (rule sym[OF control_periodic])
            also have "...=Some control_value" by (rule control_eval)
            finally show ?thesis .
          qed
          have weight_direct:
            "comma_crt_mdd_eval (phase+span) (weights_for root)=Some weight_value"
          proof -
            have "comma_crt_mdd_eval (phase+span) (weights_for root) =
                comma_crt_mdd_eval ?right_phase (weights_for root)"
              by (rule sym[OF weight_periodic])
            also have "...=Some weight_value" by (rule weight_eval)
            finally show ?thesis .
          qed
          show ?thesis using control_direct weight_direct consistent
            by blast
        qed
      qed
      qed
    have left_values:
      "\<exists>control weight.
        comma_crt_mdd_eval phase controls=Some control \<and>
        comma_crt_mdd_eval phase weights=Some weight \<and>
        comma_crt_split_value_consistent control weight"
      using left_control_eval left_weight_eval left_value_consistent by blast
    have composed_values:
      "\<exists>control weight.
        comma_crt_mdd_eval phase
          (fst (comma_crt_split_compose_from remaining span controls weights
            controls_for weights_for))=Some control \<and>
        comma_crt_mdd_eval phase
          (snd (comma_crt_split_compose_from remaining span controls weights
            controls_for weights_for))=Some weight \<and>
        comma_crt_split_value_consistent control weight"
      using comma_crt_split_compose_from_pointwise_consistent[
        where remaining=remaining and span=span and phase=phase and controls=controls
          and weights=weights and controls_for=controls_for and weights_for=weights_for,
        OF bound left_control left_weight right_control right_weight left_values right_values] .
    then obtain control_value weight_value where
      control_eval:
        "comma_crt_mdd_eval phase
          (fst (comma_crt_split_compose_from remaining span controls weights
            controls_for weights_for))=Some control_value"
      and weight_eval:
        "comma_crt_mdd_eval phase
          (snd (comma_crt_split_compose_from remaining span controls weights
            controls_for weights_for))=Some weight_value"
      and consistent:
        "comma_crt_split_value_consistent control_value weight_value"
      by blast
    show "case
      (comma_crt_mdd_eval phase
        (fst (comma_crt_split_compose_from remaining span controls weights
          controls_for weights_for)),
       comma_crt_mdd_eval phase
        (snd (comma_crt_split_compose_from remaining span controls weights
          controls_for weights_for))) of
        (Some control,Some weight) \<Rightarrow>
          comma_crt_split_value_consistent control weight
      | _ \<Rightarrow> False"
      using control_eval weight_eval consistent by simp
  qed
  show ?thesis
    unfolding comma_crt_mdd_split_consistent_def
    using output_admitted output_values_consistent by blast
qed


ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
    comma_crt_mdd_eval_periodic
    comma_crt_mdd_node_map_projection_eval
    comma_crt_split_compose_from_admitted
    comma_crt_split_compose_from_pointwise_consistent
    comma_crt_split_compose_from_consistent
  }) then ()
  else error "Comma_CRT_Split_Power_Admission local oracle audit failed"
\<close>
end
