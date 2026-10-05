theory Comma_Semantic_B1_CRT_Split_Occurrence
  imports Comma_Semantic_B1_CRT_Occurrence_Fold
    Comma_CRT_Split_Power_Composition
begin

text \<open>
Build an occurrence's B1 action directly into independent control and weight
diagrams.  A Boolean support paints its binding into each projection
separately.  In particular, geometry reduction compares only
`comma_crt_control` leaves; exact Stop weights are reduced only in the
parallel nat-option diagram.  This avoids constructing an outcome-valued MDD
whose node reduction would retain distinctions caused only by Stop D.
\<close>

primrec comma_crt_column_tree_size :: "comma_crt_column \<Rightarrow> nat" where
  "comma_crt_column_tree_size (Comma_CRT_Bool _) = 1"
| "comma_crt_column_tree_size (Comma_CRT_Node level children) =
    Suc (sum_list (map comma_crt_column_tree_size children))"

primrec comma_crt_mdd_tree_size :: "'a comma_crt_mdd \<Rightarrow> nat" where
  "comma_crt_mdd_tree_size (Comma_CRT_MDD_Leaf _) = 1"
| "comma_crt_mdd_tree_size (Comma_CRT_MDD_Node level children) =
    Suc (sum_list (map comma_crt_mdd_tree_size children))"

lemma comma_crt_sum_child_le:
  fixes child :: "'a" and children :: "'a list"
    and size_of :: "'a \<Rightarrow> nat"
  assumes member: "child \<in> set children"
  shows "size_of child \<le> sum_list (map size_of children)"
  using member
proof (induction children)
  case Nil
  then show ?case by simp
next
  case (Cons head tail)
  then show ?case by (auto intro: le_trans)
qed

lemma comma_crt_column_tree_child_less:
  fixes child :: comma_crt_column
    and children :: "comma_crt_column list" and level :: nat
  shows "child \<in> set children \<Longrightarrow>
    comma_crt_column_tree_size child <
      Suc (sum_list (map comma_crt_column_tree_size children))"
proof -
  assume member: "child \<in> set children"
  have bounded: "comma_crt_column_tree_size child \<le>
      sum_list (map comma_crt_column_tree_size children)"
    by (rule comma_crt_sum_child_le
      [where child=child and children=children
        and size_of=comma_crt_column_tree_size, OF member])
  show "comma_crt_column_tree_size child <
      Suc (sum_list (map comma_crt_column_tree_size children))"
    using bounded by arith
qed

lemma comma_crt_mdd_tree_child_less:
  fixes child :: "'a comma_crt_mdd"
    and children :: "'a comma_crt_mdd list" and level :: nat
  shows "child \<in> set children \<Longrightarrow>
    comma_crt_mdd_tree_size child <
      Suc (sum_list (map comma_crt_mdd_tree_size children))"
proof -
  assume member: "child \<in> set children"
  have bounded: "comma_crt_mdd_tree_size child \<le>
      sum_list (map comma_crt_mdd_tree_size children)"
    by (rule comma_crt_sum_child_le
      [where child=child and children=children
        and size_of=comma_crt_mdd_tree_size, OF member])
  show "comma_crt_mdd_tree_size child <
      Suc (sum_list (map comma_crt_mdd_tree_size children))"
    using bounded by arith
qed

lemma comma_crt_paint_zip_pair_less:
  fixes column :: comma_crt_column and diagram :: "'a comma_crt_mdd"
    and masks :: "comma_crt_column list"
    and children :: "'a comma_crt_mdd list"
  assumes member: "(column, diagram) \<in> set (zip masks children)"
  shows "comma_crt_column_tree_size column + comma_crt_mdd_tree_size diagram <
      Suc (Suc (sum_list (map comma_crt_column_tree_size masks) +
        sum_list (map comma_crt_mdd_tree_size children)))"
proof -
  have column_member: "column \<in> set masks"
    by (meson member set_zip_leftD)
  have diagram_member: "diagram \<in> set children"
    by (meson member set_zip_rightD)
  have column_less: "comma_crt_column_tree_size column <
      Suc (sum_list (map comma_crt_column_tree_size masks))"
    by (rule comma_crt_column_tree_child_less[OF column_member])
  have diagram_less: "comma_crt_mdd_tree_size diagram <
      Suc (sum_list (map comma_crt_mdd_tree_size children))"
    by (rule comma_crt_mdd_tree_child_less[OF diagram_member])
  show ?thesis using column_less diagram_less by arith
qed

function comma_crt_mdd_paint_column ::
    "comma_crt_column \<Rightarrow> 'a comma_crt_mdd \<Rightarrow> 'a \<Rightarrow>
      'a comma_crt_mdd" where
  "comma_crt_mdd_paint_column (Comma_CRT_Bool False) current value = current"
| "comma_crt_mdd_paint_column (Comma_CRT_Bool True) current value =
    Comma_CRT_MDD_Leaf value"
| "comma_crt_mdd_paint_column
      (Comma_CRT_Node level masks) (Comma_CRT_MDD_Leaf old) value =
    (if level<4 \<and> length masks=comma_crt_period level then
       comma_crt_mdd_node level
         (map (\<lambda>mask. comma_crt_mdd_paint_column mask
           (Comma_CRT_MDD_Leaf old) value) masks)
     else Comma_CRT_MDD_Leaf old)"
| "comma_crt_mdd_paint_column
      (Comma_CRT_Node level masks)
      (Comma_CRT_MDD_Node old_level children) value =
    (if level<4 \<and> length masks=comma_crt_period level \<and>
        old_level<4 \<and> length children=comma_crt_period old_level then
       (if old_level<level then
          comma_crt_mdd_node old_level
            (map (\<lambda>child. comma_crt_mdd_paint_column
              (Comma_CRT_Node level masks) child value) children)
        else if level<old_level then
          comma_crt_mdd_node level
            (map (\<lambda>mask. comma_crt_mdd_paint_column mask
              (Comma_CRT_MDD_Node old_level children) value) masks)
        else comma_crt_mdd_node level
          (map (\<lambda>pair. comma_crt_mdd_paint_column
            (fst pair) (snd pair) value) (zip masks children)))
     else Comma_CRT_MDD_Node old_level children)"
  by pat_completeness auto

termination comma_crt_mdd_paint_column
  apply (relation
    "measure (\<lambda>(column, diagram, value).
      comma_crt_column_tree_size column + comma_crt_mdd_tree_size diagram)")
  apply (auto simp: comma_crt_column_tree_size.simps
      comma_crt_mdd_tree_size.simps
      intro: comma_crt_column_tree_child_less comma_crt_mdd_tree_child_less
        comma_crt_paint_zip_pair_less)
  done

lemma comma_crt_period_index_in_range:
  fixes level phase :: nat and children :: "'a list"
  assumes level: "level<4"
    and width: "length children=comma_crt_period level"
  shows "phase mod comma_crt_period level<length children"
  using comma_crt_period_positive[OF level] width by simp

lemma comma_crt_mdd_paint_column_eval:
  fixes column :: comma_crt_column and current :: "'a comma_crt_mdd"
    and payload :: "'a" and lower phase :: nat
  assumes column_admitted: "comma_crt_admitted lower column"
    and diagram: "comma_crt_mdd_admitted lower current"
  shows "comma_crt_mdd_eval phase
      (comma_crt_mdd_paint_column column current payload) =
    (if comma_crt_eval phase column then Some payload
     else comma_crt_mdd_eval phase current)"
  using column_admitted diagram
proof (induction column current payload arbitrary: phase lower
    rule: comma_crt_mdd_paint_column.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 level masks old payload)
  have lower_bound: "lower\<le>level"
    and level_bound: "level<4"
    and width: "length masks=comma_crt_period level"
    and masks_admitted:
      "list_all (comma_crt_admitted (Suc level)) masks"
    using "3.prems"(1) by (auto simp: comma_crt_admitted.simps)
  have index: "phase mod comma_crt_period level<length masks"
    by (rule comma_crt_period_index_in_range[OF level_bound width])
  have selected_member: "masks!(phase mod comma_crt_period level)\<in>set masks"
    by (rule nth_mem[OF index])
  have selected_suc:
      "comma_crt_admitted (Suc level)
        (masks!(phase mod comma_crt_period level))"
    using masks_admitted selected_member by (simp add: list_all_iff)
  have lower_suc: "lower\<le>Suc level" using lower_bound by arith
  have selected_admitted:
      "comma_crt_admitted lower (masks!(phase mod comma_crt_period level))"
    by (rule comma_crt_admitted_mono[OF lower_suc selected_suc])
  have recursive_guard: "level<4 \<and> length masks=comma_crt_period level"
    using level_bound width by blast
  have leaf_admitted: "comma_crt_mdd_admitted lower (Comma_CRT_MDD_Leaf old)"
    by simp
  have child_eval:
      "comma_crt_mdd_eval phase
        (comma_crt_mdd_paint_column
          (masks!(phase mod comma_crt_period level))
          (Comma_CRT_MDD_Leaf old) payload) =
       (if comma_crt_eval phase (masks!(phase mod comma_crt_period level))
        then Some payload else Some old)"
    using "3.IH"[OF recursive_guard selected_member selected_admitted leaf_admitted]
    by simp
  have mapped_eval:
      "comma_crt_mdd_eval phase
        (comma_crt_mdd_node level
          (map (\<lambda>mask. comma_crt_mdd_paint_column mask
            (Comma_CRT_MDD_Leaf old) payload) masks)) =
       comma_crt_mdd_eval phase
        (comma_crt_mdd_paint_column
          (masks!(phase mod comma_crt_period level))
          (Comma_CRT_MDD_Leaf old) payload)"
    by (rule comma_crt_mdd_node_map_projection_eval
      [where project="\<lambda>mask. comma_crt_mdd_paint_column mask
        (Comma_CRT_MDD_Leaf old) payload", OF level_bound width])
  have column_index:
      "phase mod comma_crt_period level<length masks"
    by (rule comma_crt_period_index_in_range[OF level_bound width])
  have mapped_column:
      "map (comma_crt_eval phase) masks !
          (phase mod comma_crt_period level) =
       comma_crt_eval phase (masks!(phase mod comma_crt_period level))"
    by (rule nth_map[OF column_index])
  have node_map:
      "comma_crt_eval phase (Comma_CRT_Node level masks) =
       map (comma_crt_eval phase) masks !
          (phase mod comma_crt_period level)"
    by (simp only: comma_crt_eval.simps(2) recursive_guard simp_thms if_True)
  have column_eval:
      "comma_crt_eval phase (Comma_CRT_Node level masks) =
       comma_crt_eval phase (masks!(phase mod comma_crt_period level))"
    using node_map mapped_column by simp
  show ?case
    using mapped_eval child_eval column_eval lower_bound level_bound width
    by (simp add: comma_crt_mdd_paint_column.simps)
next
  case (4 level masks old_level children payload)
  have column_lower: "lower\<le>level"
    and level_bound: "level<4"
    and masks_width: "length masks=comma_crt_period level"
    and masks_admitted:
      "list_all (comma_crt_admitted (Suc level)) masks"
    using "4.prems"(1) by (auto simp: comma_crt_admitted.simps)
  have diagram_lower: "lower\<le>old_level"
    and old_level_bound: "old_level<4"
    and children_width: "length children=comma_crt_period old_level"
    and children_admitted:
      "list_all (comma_crt_mdd_admitted (Suc old_level)) children"
    using "4.prems"(2) by (auto simp: comma_crt_mdd_admitted.simps)
  have recursive_guard:
    "level<4 \<and> length masks=comma_crt_period level \<and>
     old_level<4 \<and> length children=comma_crt_period old_level"
    using level_bound masks_width old_level_bound children_width by blast
  have column_index:
      "phase mod comma_crt_period level<length masks"
    by (rule comma_crt_period_index_in_range[OF level_bound masks_width])
  have selected_mask_member:
      "masks!(phase mod comma_crt_period level)\<in>set masks"
    by (rule nth_mem[OF column_index])
  have selected_mask_suc:
      "comma_crt_admitted (Suc level)
        (masks!(phase mod comma_crt_period level))"
    using masks_admitted selected_mask_member by (simp add: list_all_iff)
  have lower_suc_level: "lower\<le>Suc level"
    using column_lower by arith
  have selected_mask_admitted:
      "comma_crt_admitted lower (masks!(phase mod comma_crt_period level))"
    by (rule comma_crt_admitted_mono[OF lower_suc_level selected_mask_suc])
  have column_eval:
      "comma_crt_eval phase (Comma_CRT_Node level masks) =
       comma_crt_eval phase (masks!(phase mod comma_crt_period level))"
    using level_bound masks_width
    by (simp only: comma_crt_eval_node_selected level_bound masks_width simp_thms if_True)
  show ?case
  proof (cases "old_level<level")
    case True
    note old_first = True
    have output_index:
        "phase mod comma_crt_period old_level<length children"
      by (rule comma_crt_period_index_in_range[OF old_level_bound children_width])
    have selected_child:
        "children!(phase mod comma_crt_period old_level)\<in>set children"
      by (rule nth_mem[OF output_index])
    have selected_child_suc:
        "comma_crt_mdd_admitted (Suc old_level)
          (children!(phase mod comma_crt_period old_level))"
      using children_admitted selected_child by (simp add: list_all_iff)
    have lower_suc_old: "lower\<le>Suc old_level"
      using diagram_lower by arith
    have selected_child_admitted:
        "comma_crt_mdd_admitted lower
          (children!(phase mod comma_crt_period old_level))"
      by (rule comma_crt_mdd_admitted_mono[OF lower_suc_old selected_child_suc])
    have column_admitted_at_lower:
        "comma_crt_admitted lower (Comma_CRT_Node level masks)"
      using column_lower level_bound masks_width masks_admitted
      by (simp add: comma_crt_admitted.simps)
    have child_eval:
        "comma_crt_mdd_eval phase
          (comma_crt_mdd_paint_column (Comma_CRT_Node level masks)
            (children!(phase mod comma_crt_period old_level)) payload) =
         (if comma_crt_eval phase (Comma_CRT_Node level masks)
          then Some payload
          else comma_crt_mdd_eval phase
            (children!(phase mod comma_crt_period old_level)))"
      using recursive_guard old_first selected_child column_admitted_at_lower
        selected_child_admitted
      by (rule "4.IH"(1); assumption)
    have mapped_eval:
        "comma_crt_mdd_eval phase
          (comma_crt_mdd_node old_level
            (map (\<lambda>child. comma_crt_mdd_paint_column
              (Comma_CRT_Node level masks) child payload) children)) =
         comma_crt_mdd_eval phase
          (comma_crt_mdd_paint_column (Comma_CRT_Node level masks)
            (children!(phase mod comma_crt_period old_level)) payload)"
      by (rule comma_crt_mdd_node_map_projection_eval
        [where project="\<lambda>child. comma_crt_mdd_paint_column
          (Comma_CRT_Node level masks) child payload",
          OF old_level_bound children_width])
    show ?thesis using recursive_guard old_first mapped_eval child_eval column_eval
        output_index
      by (simp add: comma_crt_mdd_paint_column.simps)
  next
    case False
    note old_not_first = False
    show ?thesis
    proof (cases "level<old_level")
      case True
      note new_first = True
      have selected_admitted:
          "comma_crt_admitted lower (masks!(phase mod comma_crt_period level))"
        by (rule selected_mask_admitted)
      have diagram_admitted_at_lower:
          "comma_crt_mdd_admitted lower (Comma_CRT_MDD_Node old_level children)"
        using diagram_lower old_level_bound children_width children_admitted
        by (simp add: comma_crt_mdd_admitted.simps)
      have child_eval:
          "comma_crt_mdd_eval phase
            (comma_crt_mdd_paint_column
              (masks!(phase mod comma_crt_period level))
              (Comma_CRT_MDD_Node old_level children) payload) =
           (if comma_crt_eval phase (masks!(phase mod comma_crt_period level))
            then Some payload
            else comma_crt_mdd_eval phase
              (Comma_CRT_MDD_Node old_level children))"
        using recursive_guard old_not_first new_first selected_mask_member
          selected_admitted diagram_admitted_at_lower
        by (rule "4.IH"(2); assumption)
      have mapped_eval:
          "comma_crt_mdd_eval phase
            (comma_crt_mdd_node level
              (map (\<lambda>mask. comma_crt_mdd_paint_column mask
                (Comma_CRT_MDD_Node old_level children) payload) masks)) =
           comma_crt_mdd_eval phase
            (comma_crt_mdd_paint_column
              (masks!(phase mod comma_crt_period level))
              (Comma_CRT_MDD_Node old_level children) payload)"
        by (rule comma_crt_mdd_node_map_projection_eval
          [where project="\<lambda>mask. comma_crt_mdd_paint_column mask
            (Comma_CRT_MDD_Node old_level children) payload",
            OF level_bound masks_width])
      show ?thesis using recursive_guard old_not_first new_first mapped_eval
          child_eval column_eval
        by (simp add: comma_crt_mdd_paint_column.simps)
    next
      case False
      note new_not_first = False
      have same_level: "old_level=level"
        using old_not_first new_not_first by arith
      have output_index:
          "phase mod comma_crt_period level<length children"
        using comma_crt_period_index_in_range[OF old_level_bound children_width]
          same_level by simp
      have pair_index:
          "phase mod comma_crt_period level<length (zip masks children)"
        using column_index output_index by (simp add: length_zip)
      have pair_member:
          "(zip masks children)!(phase mod comma_crt_period level)
            \<in>set (zip masks children)"
        by (rule nth_mem[OF pair_index])
      have pair_value:
          "(zip masks children)!(phase mod comma_crt_period level) =
            (masks!(phase mod comma_crt_period level),
             children!(phase mod comma_crt_period level))"
        using column_index output_index by (simp add: nth_zip)
      have selected_child:
          "children!(phase mod comma_crt_period level)\<in>set children"
        by (rule nth_mem[OF output_index])
      have selected_child_suc:
          "comma_crt_mdd_admitted (Suc level)
            (children!(phase mod comma_crt_period level))"
        using same_level children_admitted selected_child
        by (simp add: list_all_iff)
      have lower_suc_level: "lower\<le>Suc level"
        using column_lower by arith
      have selected_child_admitted:
          "comma_crt_mdd_admitted lower
            (children!(phase mod comma_crt_period level))"
        by (rule comma_crt_mdd_admitted_mono[OF lower_suc_level selected_child_suc])
      have pair_column_admitted:
          "comma_crt_admitted lower
            (fst ((zip masks children)!(phase mod comma_crt_period level)))"
        using pair_value selected_mask_admitted by simp
      have pair_diagram_admitted:
          "comma_crt_mdd_admitted lower
            (snd ((zip masks children)!(phase mod comma_crt_period level)))"
        using pair_value selected_child_admitted by simp
      have pair_eval:
          "comma_crt_mdd_eval phase
            (comma_crt_mdd_paint_column
              (fst ((zip masks children)!(phase mod comma_crt_period level)))
              (snd ((zip masks children)!(phase mod comma_crt_period level)))
              payload) =
           (if comma_crt_eval phase
                (fst ((zip masks children)!(phase mod comma_crt_period level)))
            then Some payload
            else comma_crt_mdd_eval phase
              (snd ((zip masks children)!(phase mod comma_crt_period level))))"
        by (rule "4.IH"(3)[where
          x="(zip masks children)!(phase mod comma_crt_period level)"
          and lower=lower and phase=phase,
          OF recursive_guard old_not_first new_not_first pair_member
            pair_column_admitted pair_diagram_admitted])
      have mapped_eval:
          "comma_crt_mdd_eval phase
            (comma_crt_mdd_node level
              (map (\<lambda>pair. comma_crt_mdd_paint_column
                (fst pair) (snd pair) payload) (zip masks children))) =
           comma_crt_mdd_eval phase
            (comma_crt_mdd_paint_column
              (fst ((zip masks children)!(phase mod comma_crt_period level)))
              (snd ((zip masks children)!(phase mod comma_crt_period level)))
              payload)"
        by (rule comma_crt_mdd_node_map_projection_eval
          [where project="\<lambda>pair. comma_crt_mdd_paint_column
            (fst pair) (snd pair) payload", OF level_bound])
          (use masks_width children_width same_level in simp)
      have diagram_eval:
          "comma_crt_mdd_eval phase (Comma_CRT_MDD_Node old_level children) =
           comma_crt_mdd_eval phase
             (children!(phase mod comma_crt_period old_level))"
        using old_level_bound children_width
        by (simp only: comma_crt_mdd_eval_node_selected
          old_level_bound children_width simp_thms if_True)
      show ?thesis using recursive_guard old_not_first new_not_first same_level
          pair_eval mapped_eval column_eval diagram_eval output_index column_index pair_value
        by (simp add: comma_crt_mdd_paint_column.simps)
    qed
  qed
qed

lemma comma_crt_mdd_paint_column_admitted:
  fixes column :: comma_crt_column and current :: "'a comma_crt_mdd"
    and payload :: "'a" and lower :: nat
  assumes column_admitted: "comma_crt_admitted lower column"
    and diagram: "comma_crt_mdd_admitted lower current"
  shows "comma_crt_mdd_admitted lower
    (comma_crt_mdd_paint_column column current payload)"
  using column_admitted diagram
proof (induction column current payload arbitrary: lower
    rule: comma_crt_mdd_paint_column.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 level masks old payload)
  have lower_bound: "lower\<le>level"
    and level_bound: "level<4"
    and width: "length masks=comma_crt_period level"
    and masks_admitted:
      "list_all (comma_crt_admitted (Suc level)) masks"
    using "3.prems"(1) by (auto simp: comma_crt_admitted.simps)
  have painted_children:
      "list_all (comma_crt_mdd_admitted (Suc level))
        (map (\<lambda>mask. comma_crt_mdd_paint_column mask
          (Comma_CRT_MDD_Leaf old) payload) masks)"
    unfolding list_all_iff
  proof (intro ballI)
    fix painted assume painted_member:
      "painted \<in> set (map (\<lambda>mask. comma_crt_mdd_paint_column mask
        (Comma_CRT_MDD_Leaf old) payload) masks)"
    obtain mask where member: "mask\<in>set masks"
      and painted_eq: "painted=comma_crt_mdd_paint_column mask
        (Comma_CRT_MDD_Leaf old) payload"
      using painted_member by auto
    have admitted: "comma_crt_admitted (Suc level) mask"
      using masks_admitted member by (simp add: list_all_iff)
    have recursive_guard: "level<4 \<and> length masks=comma_crt_period level"
      using level_bound width by blast
    have leaf_admitted:
      "comma_crt_mdd_admitted (Suc level) (Comma_CRT_MDD_Leaf old)"
      by simp
    have recursive_admitted: "comma_crt_mdd_admitted (Suc level)
        (comma_crt_mdd_paint_column mask (Comma_CRT_MDD_Leaf old) payload)"
      by (rule "3.IH"[OF recursive_guard member admitted leaf_admitted])
    show "comma_crt_mdd_admitted (Suc level) painted"
      using recursive_admitted painted_eq by simp
  qed
  show ?case
    using painted_children lower_bound level_bound width
    by (simp add: comma_crt_mdd_paint_column.simps
      comma_crt_mdd_node_admitted)
next
  case (4 level masks old_level children payload)
  have column_lower: "lower\<le>level"
    and level_bound: "level<4"
    and masks_width: "length masks=comma_crt_period level"
    and masks_admitted:
      "list_all (comma_crt_admitted (Suc level)) masks"
    using "4.prems"(1) by (auto simp: comma_crt_admitted.simps)
  have diagram_lower: "lower\<le>old_level"
    and old_level_bound: "old_level<4"
    and children_width: "length children=comma_crt_period old_level"
    and children_admitted:
      "list_all (comma_crt_mdd_admitted (Suc old_level)) children"
    using "4.prems"(2) by (auto simp: comma_crt_mdd_admitted.simps)
  have recursive_guard:
    "level<4 \<and> length masks=comma_crt_period level \<and>
     old_level<4 \<and> length children=comma_crt_period old_level"
    using level_bound masks_width old_level_bound children_width by blast
  show ?case
  proof (cases "old_level<level")
    case old_first: True
    have child_bound: "Suc old_level\<le>level"
      using old_first by arith
    have painted_children:
        "list_all (comma_crt_mdd_admitted (Suc old_level))
          (map (\<lambda>child. comma_crt_mdd_paint_column
            (Comma_CRT_Node level masks) child payload) children)"
      unfolding list_all_iff
    proof (intro ballI)
      fix painted assume painted_member:
        "painted \<in> set (map (\<lambda>child. comma_crt_mdd_paint_column
          (Comma_CRT_Node level masks) child payload) children)"
      obtain child where member: "child\<in>set children"
        and painted_eq: "painted=comma_crt_mdd_paint_column
          (Comma_CRT_Node level masks) child payload"
        using painted_member by auto
      have admitted: "comma_crt_mdd_admitted (Suc old_level) child"
        using children_admitted member by (simp add: list_all_iff)
      have column_admitted_at_child:
        "comma_crt_admitted (Suc old_level) (Comma_CRT_Node level masks)"
        using child_bound level_bound masks_width masks_admitted
        by (simp add: comma_crt_admitted.simps)
      have child_result: "comma_crt_mdd_admitted (Suc old_level)
          (comma_crt_mdd_paint_column (Comma_CRT_Node level masks)
            child payload)"
        using recursive_guard old_first member column_admitted_at_child admitted
        by (rule "4.IH"(1); assumption)
      show "comma_crt_mdd_admitted (Suc old_level) painted"
        using child_result painted_eq by simp
    qed
    show ?thesis
      using recursive_guard old_first painted_children diagram_lower
      by (simp add: comma_crt_mdd_paint_column.simps
        comma_crt_mdd_node_admitted)
  next
    case old_not_first: False
    show ?thesis
    proof (cases "level<old_level")
      case new_first: True
      have masks_bound: "Suc level\<le>old_level"
        using new_first by arith
      have painted_masks:
          "list_all (comma_crt_mdd_admitted (Suc level))
            (map (\<lambda>mask. comma_crt_mdd_paint_column mask
              (Comma_CRT_MDD_Node old_level children) payload) masks)"
        unfolding list_all_iff
      proof (intro ballI)
        fix painted assume painted_member:
          "painted \<in> set (map (\<lambda>mask. comma_crt_mdd_paint_column mask
            (Comma_CRT_MDD_Node old_level children) payload) masks)"
        obtain mask where member: "mask\<in>set masks"
          and painted_eq: "painted=comma_crt_mdd_paint_column mask
            (Comma_CRT_MDD_Node old_level children) payload"
          using painted_member by auto
      have admitted: "comma_crt_admitted (Suc level) mask"
        using masks_admitted member by (simp add: list_all_iff)
      have diagram_admitted_at_level:
        "comma_crt_mdd_admitted (Suc level)
          (Comma_CRT_MDD_Node old_level children)"
        using masks_bound old_level_bound children_width children_admitted
        by (simp add: comma_crt_mdd_admitted.simps)
      have mask_result: "comma_crt_mdd_admitted (Suc level)
            (comma_crt_mdd_paint_column mask
              (Comma_CRT_MDD_Node old_level children) payload)"
          using recursive_guard old_not_first new_first member admitted
            diagram_admitted_at_level
          by (rule "4.IH"(2); assumption)
        show "comma_crt_mdd_admitted (Suc level) painted"
          using mask_result painted_eq by simp
      qed
      show ?thesis
        using recursive_guard old_not_first new_first painted_masks column_lower
        by (simp add: comma_crt_mdd_paint_column.simps
          comma_crt_mdd_node_admitted)
    next
      case new_not_first: False
      have same_level: "old_level=level"
        using old_not_first new_not_first by arith
      have pairs_width: "length (zip masks children)=comma_crt_period level"
        using same_level masks_width children_width by simp
      have painted_pairs:
          "list_all (comma_crt_mdd_admitted (Suc level))
            (map (\<lambda>pair. comma_crt_mdd_paint_column
              (fst pair) (snd pair) payload) (zip masks children))"
        unfolding list_all_iff
      proof (intro ballI)
        fix painted assume painted_member:
          "painted \<in> set (map (\<lambda>pair. comma_crt_mdd_paint_column
            (fst pair) (snd pair) payload) (zip masks children))"
        obtain pair where member: "pair\<in>set (zip masks children)"
          and painted_eq: "painted=comma_crt_mdd_paint_column
            (fst pair) (snd pair) payload"
          using painted_member by auto
        have paired_member:
          "(fst pair, snd pair)\<in>set (zip masks children)"
          using member by simp
        have mask_member: "fst pair\<in>set masks"
          by (rule set_zip_leftD[OF paired_member])
        have child_member: "snd pair\<in>set children"
          by (rule set_zip_rightD[OF paired_member])
        have mask_admitted: "comma_crt_admitted (Suc level) (fst pair)"
          using masks_admitted mask_member by (simp add: list_all_iff)
        have child_admitted: "comma_crt_mdd_admitted (Suc level) (snd pair)"
          using same_level children_admitted child_member
          by (simp add: list_all_iff)
        have pair_result: "comma_crt_mdd_admitted (Suc level)
            (comma_crt_mdd_paint_column (fst pair) (snd pair) payload)"
          by (rule "4.IH"(3)[where x=pair and lower="Suc level",
            OF recursive_guard old_not_first new_not_first member
              mask_admitted child_admitted])
        show "comma_crt_mdd_admitted (Suc level) painted"
          using pair_result painted_eq by simp
      qed
      show ?thesis
        using recursive_guard old_not_first new_not_first same_level painted_pairs
          column_lower pairs_width
        by (simp add: comma_crt_mdd_paint_column.simps
          comma_crt_mdd_node_admitted)
    qed
  qed
qed

definition comma_crt_mdd_paint_binding ::
    "nat \<Rightarrow> comma_crt_column \<Rightarrow> comma_semantic_b1_result \<Rightarrow>
      comma_crt_split_action \<Rightarrow> comma_crt_split_action" where
  "comma_crt_mdd_paint_binding rebase column outcome action =
    (let mask = comma_crt_shift rebase column in
       \<lparr>comma_crt_split_control =
          comma_crt_mdd_paint_column mask (comma_crt_split_control action)
            (comma_crt_control_of_result outcome),
        comma_crt_split_weight =
        comma_crt_mdd_paint_column mask (comma_crt_split_weight action)
          (comma_crt_weight_of_result outcome)\<rparr>)"

lemma comma_crt_mdd_paint_binding_admitted:
  fixes lower shift :: nat and mask :: comma_crt_column
    and outcome :: comma_semantic_b1_result
    and current :: comma_crt_split_action
  assumes column: "comma_crt_admitted lower mask"
    and action: "comma_crt_mdd_split_consistent lower
      (comma_crt_split_control current) (comma_crt_split_weight current)"
  shows "comma_crt_mdd_split_consistent lower
    (comma_crt_split_control (comma_crt_mdd_paint_binding shift mask outcome current))
    (comma_crt_split_weight (comma_crt_mdd_paint_binding shift mask outcome current))"
proof -
  have shifted: "comma_crt_admitted lower (comma_crt_shift shift mask)"
    by (rule comma_crt_shift_admitted[OF column])
  have control_admitted: "comma_crt_mdd_admitted lower
      (comma_crt_split_control current)"
    and weight_admitted: "comma_crt_mdd_admitted lower
      (comma_crt_split_weight current)"
    using action by (simp_all add: comma_crt_mdd_split_consistent_def)
  have control_result: "comma_crt_mdd_admitted lower
      (comma_crt_mdd_paint_column (comma_crt_shift shift mask)
        (comma_crt_split_control current) (comma_crt_control_of_result outcome))"
    by (rule comma_crt_mdd_paint_column_admitted[OF shifted control_admitted])
  have weight_result: "comma_crt_mdd_admitted lower
      (comma_crt_mdd_paint_column (comma_crt_shift shift mask)
        (comma_crt_split_weight current) (comma_crt_weight_of_result outcome))"
    by (rule comma_crt_mdd_paint_column_admitted[OF shifted weight_admitted])
  have values_consistent: "comma_crt_split_value_consistent
      (comma_crt_control_of_result outcome) (comma_crt_weight_of_result outcome)"
    by (cases outcome) simp_all
  show ?thesis
    using action control_result weight_result values_consistent
      comma_crt_mdd_paint_column_eval[OF shifted control_admitted]
      comma_crt_mdd_paint_column_eval[OF shifted weight_admitted]
    unfolding comma_crt_mdd_split_consistent_def
      comma_crt_mdd_paint_binding_def
    by (auto simp: Let_def comma_crt_split_value_consistent.simps
      split: if_splits)
qed

definition comma_crt_split_invalid_action :: "comma_crt_split_action" where
  "comma_crt_split_invalid_action =
    \<lparr>comma_crt_split_control =
        Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid,
      comma_crt_split_weight = Comma_CRT_MDD_Leaf None\<rparr>"

definition comma_crt_occurrence_split_initial :: "comma_crt_split_action" where
  "comma_crt_occurrence_split_initial = comma_crt_split_invalid_action"

fun comma_crt_occurrence_split_from_bindings ::
    "nat \<Rightarrow> comma_crt_column list \<Rightarrow>
      comma_semantic_b1_result list \<Rightarrow> comma_crt_split_action \<Rightarrow>
      comma_crt_split_action" where
  "comma_crt_occurrence_split_from_bindings rebase [] [] action = action"
| "comma_crt_occurrence_split_from_bindings rebase
      (column#columns) (outcome#outcomes) action =
    comma_crt_occurrence_split_from_bindings rebase columns outcomes
      (comma_crt_mdd_paint_binding rebase column outcome action)"
| "comma_crt_occurrence_split_from_bindings rebase [] (_#_) action =
    comma_crt_split_invalid_action"
| "comma_crt_occurrence_split_from_bindings rebase (_#_) [] action =
    comma_crt_split_invalid_action"

definition comma_crt_occurrence_split_action ::
    "comma_semantic_b1_crt_occurrence \<Rightarrow> comma_crt_split_action" where
  "comma_crt_occurrence_split_action occurrence =
    comma_crt_occurrence_split_from_bindings
      (comma_semantic_b1_crt_occurrence_rebase occurrence)
      (comma_semantic_b1_crt_occurrence_columns occurrence)
      (comma_semantic_b1_crt_occurrence_beta occurrence)
      comma_crt_occurrence_split_initial"

lemma comma_crt_occurrence_split_mismatched_bindings_fail_closed:
  "let stale = \<lparr>comma_crt_split_control =
        Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop,
      comma_crt_split_weight = Comma_CRT_MDD_Leaf (Some 13)\<rparr>
   in comma_crt_occurrence_split_from_bindings 0
        [Comma_CRT_Bool True] [] stale = comma_crt_split_invalid_action \<and>
      comma_crt_occurrence_split_from_bindings 0 []
        [Comma_Semantic_B1_Stop 13] stale = comma_crt_split_invalid_action"
  by (simp add: comma_crt_period_def)

lemma comma_crt_occurrence_split_stop_weight_fibers:
  "let left = Comma_CRT_Node 0
      [Comma_CRT_Bool True, Comma_CRT_Bool True,
       Comma_CRT_Bool False, Comma_CRT_Bool False];
    right = Comma_CRT_Node 0
      [Comma_CRT_Bool False, Comma_CRT_Bool False,
       Comma_CRT_Bool True, Comma_CRT_Bool True];
    initial = \<lparr>comma_crt_split_control =
        Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid,
      comma_crt_split_weight = Comma_CRT_MDD_Leaf None\<rparr>;
    painted = comma_crt_mdd_paint_binding 0 right
        (Comma_Semantic_B1_Stop 14)
      (comma_crt_mdd_paint_binding 0 left
        (Comma_Semantic_B1_Stop 13) initial)
   in comma_crt_split_control painted =
        Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop \<and>
      comma_crt_split_weight painted = Comma_CRT_MDD_Node 0
        [Comma_CRT_MDD_Leaf (Some 13), Comma_CRT_MDD_Leaf (Some 13),
         Comma_CRT_MDD_Leaf (Some 14), Comma_CRT_MDD_Leaf (Some 14)] \<and>
      comma_crt_split_mdd_result_at 0
        (comma_crt_split_control painted) (comma_crt_split_weight painted) =
        Some (Comma_Semantic_B1_Stop 13) \<and>
      comma_crt_split_mdd_result_at 2
        (comma_crt_split_control painted) (comma_crt_split_weight painted) =
        Some (Comma_Semantic_B1_Stop 14)"
  by (simp add: comma_crt_mdd_paint_binding_def Let_def
      comma_crt_mdd_node_def comma_crt_split_mdd_result_at_def
      comma_crt_split_invalid_action_def comma_crt_period_def)

end
