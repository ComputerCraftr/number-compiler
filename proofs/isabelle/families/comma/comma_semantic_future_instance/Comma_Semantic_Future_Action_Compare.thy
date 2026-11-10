theory Comma_Semantic_Future_Action_Compare
  imports Comma_Semantic_Future_Source_Action
    Comma_Semantic_Future_Candidate_Selector
    Comma_Semantic_Future_Rank_B1_Transport
begin

text \<open>
The future source is evaluated for one complete B1 round from its
authenticated source CID.  A local Stop ends there with height zero.  A
Continue selects a decade root and composes with the checked 32-decade root
action at span one.  The resulting Stop height is the total source-to-event
exponent \<delta>; the boundary adapter below separates that value back into
the local displacement d and complete-decade payload H.
\<close>

text \<open>
The child IDs are separate phase receivers.  Both query the same authenticated
candidate-ID bank after the source displacement; no receiver stores an
ordered pair leaf.
\<close>

definition comma_semantic_future_candidate_child_receiver_north ::
    "comma_future_control option \<Rightarrow>
      nat comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_candidate_child_receiver_north selected =
    (case selected of
       Some (Comma_Future_Fork target_family_digit) \<Rightarrow>
         (if 2 \<le> target_family_digit \<and> target_family_digit \<le> 9 \<and>
             length comma_semantic_future_candidate_id_selector_actions=16 then
           snd (comma_semantic_future_candidate_id_selector_actions!
             (target_family_digit-2))
          else Comma_Weighted_CRT_Leaf 0)
     | _ \<Rightarrow> Comma_Weighted_CRT_Leaf 0)"

definition comma_semantic_future_candidate_child_receiver_south ::
    "comma_future_control option \<Rightarrow>
      nat comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_candidate_child_receiver_south selected =
    (case selected of
       Some (Comma_Future_Fork target_family_digit) \<Rightarrow>
         (if 2 \<le> target_family_digit \<and> target_family_digit \<le> 9 \<and>
             length comma_semantic_future_candidate_id_selector_actions=16 then
           snd (comma_semantic_future_candidate_id_selector_actions!
             (8+target_family_digit-2))
          else Comma_Weighted_CRT_Leaf 0)
     | _ \<Rightarrow> Comma_Weighted_CRT_Leaf 0)"

lemma comma_semantic_future_candidate_child_receiver_north_shape:
  "\<And>selected. comma_weighted_crt_shape 0
      (comma_semantic_future_candidate_child_receiver_north selected)"
proof -
  fix selected
  show "comma_weighted_crt_shape 0
      (comma_semantic_future_candidate_child_receiver_north selected)"
  proof (cases selected)
    case None then show ?thesis
      by (simp add: comma_semantic_future_candidate_child_receiver_north_def)
  next
    case (Some control)
    then show ?thesis
    proof (cases control)
      case (Comma_Future_Fork target)
      have bound: "target-2<16" using Comma_Future_Fork by simp
      have shapes: "list_all (\<lambda>action. comma_weighted_crt_shape 0 (snd action))
          comma_semantic_future_candidate_id_selector_actions"
        by (rule comma_semantic_future_candidate_id_selector_actions_shape)
      have count: "length comma_semantic_future_candidate_id_selector_actions=16"
        by (rule comma_semantic_future_candidate_id_selector_actions_length)
      show ?thesis using Some Comma_Future_Fork bound shapes count
        by (auto simp: comma_semantic_future_candidate_child_receiver_north_def
          list_all_iff)
    next
      case Comma_Future_Landmine
      then show ?thesis using Some
        by (simp add: comma_semantic_future_candidate_child_receiver_north_def)
    qed
  qed
qed

lemma comma_semantic_future_candidate_child_receiver_south_shape:
  "\<And>selected. comma_weighted_crt_shape 0
      (comma_semantic_future_candidate_child_receiver_south selected)"
proof -
  fix selected
  show "comma_weighted_crt_shape 0
      (comma_semantic_future_candidate_child_receiver_south selected)"
  proof (cases selected)
    case None then show ?thesis
      by (simp add: comma_semantic_future_candidate_child_receiver_south_def)
  next
    case (Some control)
    then show ?thesis
    proof (cases control)
      case (Comma_Future_Fork target)
      have bound: "8+target-2<16" using Comma_Future_Fork by simp
      have shapes: "list_all (\<lambda>action. comma_weighted_crt_shape 0 (snd action))
          comma_semantic_future_candidate_id_selector_actions"
        by (rule comma_semantic_future_candidate_id_selector_actions_shape)
      have count: "length comma_semantic_future_candidate_id_selector_actions=16"
        by (rule comma_semantic_future_candidate_id_selector_actions_length)
      show ?thesis using Some Comma_Future_Fork bound shapes count
        by (auto simp: comma_semantic_future_candidate_child_receiver_south_def
          list_all_iff)
    next
      case Comma_Future_Landmine
      then show ?thesis using Some
        by (simp add: comma_semantic_future_candidate_child_receiver_south_def)
    qed
  qed
qed

lemma comma_semantic_future_candidate_child_receiver_north_fork_exact:
  assumes target: "2 \<le> target_family_digit" "target_family_digit \<le> 9"
    and phase: "phase<924"
  shows "comma_weighted_crt_eval
      (comma_semantic_future_candidate_child_receiver_north
        (Some (Comma_Future_Fork target_family_digit))) phase =
    Some (comma_semantic_future_candidate_class_ids!
      (924*(target_family_digit-2)+phase),0)"
  using comma_semantic_future_candidate_id_selector_action_at_exact
    [OF phase] target
  by (simp add: comma_semantic_future_candidate_child_receiver_north_def
      comma_weighted_crt_apply_def
      comma_semantic_future_candidate_id_selector_action_at_def)

lemma comma_semantic_future_candidate_child_receiver_south_fork_exact:
  assumes target: "2 \<le> target_family_digit" "target_family_digit \<le> 9"
    and phase: "phase<924"
  shows "comma_weighted_crt_eval
      (comma_semantic_future_candidate_child_receiver_south
        (Some (Comma_Future_Fork target_family_digit))) phase =
    Some (comma_semantic_future_candidate_class_ids!
      (924*(8+target_family_digit-2)+phase),0)"
  using comma_semantic_future_candidate_id_selector_action_at_exact
    [OF phase] target
  by (simp add: comma_semantic_future_candidate_child_receiver_south_def
      comma_weighted_crt_apply_def
      comma_semantic_future_candidate_id_selector_action_at_def)

lemma comma_semantic_future_candidate_child_receiver_north_landmine_placeholder:
  "comma_weighted_crt_eval
      (comma_semantic_future_candidate_child_receiver_north
        (Some Comma_Future_Landmine)) phase = Some (0,0)"
  by (simp add: comma_semantic_future_candidate_child_receiver_north_def
      comma_weighted_crt_apply_def)

lemma comma_semantic_future_candidate_child_receiver_south_landmine_placeholder:
  "comma_weighted_crt_eval
      (comma_semantic_future_candidate_child_receiver_south
        (Some Comma_Future_Landmine)) phase = Some (0,0)"
  by (simp add: comma_semantic_future_candidate_child_receiver_south_def
      comma_weighted_crt_apply_def)

text \<open>
The zero-valued receiver outside Fork makes the total function well-typed.
The projected-key observer never evaluates this value for Landmine, so it is
not an authorized child ID.
\<close>

definition comma_semantic_future_candidate_child_ids_at ::
    "comma_future_control option \<Rightarrow> nat \<Rightarrow> nat list option" where
  "comma_semantic_future_candidate_child_ids_at selected phase =
    (case selected of
       Some (Comma_Future_Fork target_digit) \<Rightarrow>
         (if 2 \<le> target_digit \<and> target_digit \<le> 9 then
            map_option (\<lambda>(north,south). [north,south])
              (comma_semantic_future_candidate_child_id_pair_projection
                (target_digit-2) phase)
          else None)
     | Some Comma_Future_Landmine \<Rightarrow> Some []
     | None \<Rightarrow> None)"

lemma comma_semantic_future_candidate_child_ids_fork_exact:
  assumes target: "2 \<le> target_digit" "target_digit \<le> 9"
    and phase: "phase<924"
  shows "comma_semantic_future_candidate_child_ids_at
      (Some (Comma_Future_Fork target_digit)) phase =
    Some [comma_semantic_future_candidate_class_ids!
        (924*(target_digit-2)+phase),
      comma_semantic_future_candidate_class_ids!
        (924*(8+target_digit-2)+phase)]"
  using comma_semantic_future_candidate_child_id_pair_projection_exact
    [OF phase] target
  by (simp add: comma_semantic_future_candidate_child_ids_at_def)

lemma comma_semantic_future_candidate_child_ids_landmine:
  "comma_semantic_future_candidate_child_ids_at
      (Some Comma_Future_Landmine) phase = Some []"
  by (simp add: comma_semantic_future_candidate_child_ids_at_def)

definition comma_semantic_future_candidate_class_output_key ::
    "nat \<Rightarrow> comma_future_control option \<times> nat list" where
  "comma_semantic_future_candidate_class_output_key class_id =
    (if class_id<length comma_semantic_future_candidate_controls then
       (let control=comma_semantic_future_candidate_controls!class_id;
            children=
              (if class_id<length comma_semantic_future_candidate_children then
                 (case control of
                   Comma_Future_Fork a \<Rightarrow>
                     (case comma_semantic_future_candidate_children!class_id of
                        (left,right) \<Rightarrow> map_filter id [left,right])
                 | Comma_Future_Landmine \<Rightarrow> [])
               else [])
        in (Some control,children))
     else (None,[]))"

definition comma_semantic_future_candidate_output_control ::
    "nat \<Rightarrow> comma_future_control option" where
  "comma_semantic_future_candidate_output_control class_id =
    comma_semantic_future_candidate_class_step class_id"

definition comma_semantic_future_candidate_output_north ::
    "nat \<Rightarrow> nat option" where
  "comma_semantic_future_candidate_output_north class_id =
    (if class_id<length comma_semantic_future_candidate_controls then
       (case comma_semantic_future_candidate_controls!class_id of
          Comma_Future_Fork _ \<Rightarrow>
            (if class_id<length comma_semantic_future_candidate_children then
               fst (comma_semantic_future_candidate_children!class_id)
             else None)
        | Comma_Future_Landmine \<Rightarrow> None)
     else None)"

definition comma_semantic_future_candidate_output_south ::
    "nat \<Rightarrow> nat option" where
  "comma_semantic_future_candidate_output_south class_id =
    (if class_id<length comma_semantic_future_candidate_controls then
       (case comma_semantic_future_candidate_controls!class_id of
          Comma_Future_Fork _ \<Rightarrow>
            (if class_id<length comma_semantic_future_candidate_children then
               snd (comma_semantic_future_candidate_children!class_id)
             else None)
        | Comma_Future_Landmine \<Rightarrow> None)
     else None)"

definition comma_semantic_future_candidate_output_north_id :: "nat \<Rightarrow> nat" where
  "comma_semantic_future_candidate_output_north_id class_id =
    (case comma_semantic_future_candidate_output_north class_id of
       Some child \<Rightarrow> child | None \<Rightarrow> 0)"

definition comma_semantic_future_candidate_output_south_id :: "nat \<Rightarrow> nat" where
  "comma_semantic_future_candidate_output_south_id class_id =
    (case comma_semantic_future_candidate_output_south class_id of
       Some child \<Rightarrow> child | None \<Rightarrow> 0)"

lemma comma_semantic_future_candidate_class_output_key_from_projections:
  "comma_semantic_future_candidate_class_output_key class_id =
    (comma_semantic_future_candidate_output_control class_id,
     map_filter id [comma_semantic_future_candidate_output_north class_id,
       comma_semantic_future_candidate_output_south class_id])"
  by (cases "class_id<length comma_semantic_future_candidate_controls")
    (auto simp: comma_semantic_future_candidate_class_output_key_def
      comma_semantic_future_candidate_output_control_def
      comma_semantic_future_candidate_output_north_def
      comma_semantic_future_candidate_output_south_def
      split: comma_future_control.splits prod.splits)

definition comma_semantic_future_candidate_parent_key_action ::
    "nat \<Rightarrow> comma_semantic_future_projected_key_action" where
  "comma_semantic_future_candidate_parent_key_action family_slot =
    (if family_slot<16 \<and>
        length comma_semantic_future_candidate_id_selector_actions=16 then
       (comma_semantic_future_crt_map_action_control
          comma_semantic_future_candidate_output_control
          (comma_semantic_future_candidate_id_selector_actions!family_slot),
        (comma_semantic_future_crt_map_action_control
          comma_semantic_future_candidate_output_north_id
          (comma_semantic_future_candidate_id_selector_actions!family_slot),
         comma_semantic_future_crt_map_action_control
          comma_semantic_future_candidate_output_south_id
          (comma_semantic_future_candidate_id_selector_actions!family_slot)))
     else ((0,Comma_Weighted_CRT_Leaf None),
       ((0,Comma_Weighted_CRT_Leaf 0),(0,Comma_Weighted_CRT_Leaf 0)))"

lemma comma_semantic_future_candidate_parent_key_action_shape:
  assumes family: "family_slot<16"
  shows "comma_weighted_crt_shape 0
      (snd (fst (comma_semantic_future_candidate_parent_key_action family_slot))) \<and>
    comma_weighted_crt_shape 0
      (snd (fst (snd (comma_semantic_future_candidate_parent_key_action family_slot)))) \<and>
    comma_weighted_crt_shape 0
      (snd (snd (snd (comma_semantic_future_candidate_parent_key_action family_slot))))"
proof -
  have actions_length:
    "length comma_semantic_future_candidate_id_selector_actions=16"
    by (rule comma_semantic_future_candidate_id_selector_actions_length)
  have actions_shape:
    "list_all (\<lambda>action. comma_weighted_crt_shape 0 (snd action))
      comma_semantic_future_candidate_id_selector_actions"
    by (rule comma_semantic_future_candidate_id_selector_actions_shape)
  have member: "family_slot\<in>set [0..<16]" using family by simp
  have selected_shape:
    "comma_weighted_crt_shape 0
      (snd (comma_semantic_future_candidate_id_selector_actions!family_slot))"
    using actions_shape actions_length member by (auto simp: list_all_iff)
  show ?thesis using family actions_length selected_shape
    by (simp add: comma_semantic_future_candidate_parent_key_action_def
        comma_semantic_future_crt_map_control_shape)
qed

lemma comma_semantic_future_candidate_parent_key_action_apply:
  assumes table: "comma_semantic_future_candidate_class_table_check"
    and family: "family_slot<16"
    and phase: "phase<924"
  shows "comma_semantic_future_projected_key_apply
      (comma_semantic_future_candidate_parent_key_action family_slot) phase =
    Some (comma_semantic_future_candidate_class_output_key
      (comma_semantic_future_candidate_class_ids!
        (924*family_slot+phase)))"
proof -
  have family_rows:
    "list_all (\<lambda>family. \<forall>phase<924.
      comma_weighted_crt_apply
        (comma_semantic_future_candidate_id_selector_actions!family) phase =
        Some (comma_semantic_future_candidate_class_ids!(924*family+phase),0))
      [0..<16]"
    by (rule comma_semantic_future_candidate_id_selector_actions_refine)
  have actions_length:
    "length comma_semantic_future_candidate_id_selector_actions=16"
    by (rule comma_semantic_future_candidate_id_selector_actions_length)
  have member: "family_slot\<in>set [0..<16]" using family by simp
  have selected:
    "comma_weighted_crt_apply
      (comma_semantic_future_candidate_id_selector_actions!family_slot) phase =
      Some (comma_semantic_future_candidate_class_ids!
        (924*family_slot+phase),0)"
    using family_rows member phase by (auto simp: list_all_iff)
  let ?class = "comma_semantic_future_candidate_class_ids!(924*family_slot+phase)"
  have ids_range:
    "list_all (\<lambda>id. id < length comma_semantic_future_candidate_controls)
      comma_semantic_future_candidate_class_ids"
    using table
    by (auto simp: comma_semantic_future_candidate_class_table_check_def
      comma_semantic_future_candidate_class_ids_range_check_def
      intro: comma_semantic_future_candidate_id_vector_all_in_range)
  have index_bound:
    "924*family_slot+phase < length comma_semantic_future_candidate_class_ids"
  proof -
    have ids_length:
      "length comma_semantic_future_candidate_class_ids = length comma_boundary_states"
      using table
      by (simp add: comma_semantic_future_candidate_class_table_check_def)
    show ?thesis using ids_length family phase
    by (simp add: comma_boundary_states_card; arith)
  qed
  have class_member:
    "?class \<in> set comma_semantic_future_candidate_class_ids"
    by (rule nth_mem[OF index_bound])
  have class_bound:
    "?class < length comma_semantic_future_candidate_controls"
    using ids_range class_member by (simp add: list_all_iff)
  have class_valid:
    "comma_semantic_future_candidate_class_valid ?class"
    using class_bound by (simp add: comma_semantic_future_candidate_class_valid_def)
  have checked_rows:
    "list_all comma_semantic_future_candidate_class_row_checked
      [0..<length comma_semantic_future_candidate_controls]"
    using table
    by (simp add: comma_semantic_future_candidate_class_table_check_def)
  have class_row_member:
    "?class \<in> set [0..<length comma_semantic_future_candidate_controls]"
    using class_bound by simp
  have checked_row:
    "comma_semantic_future_candidate_class_row_checked ?class"
    using checked_rows class_row_member by (simp add: list_all_iff)
  have class_shape:
    "comma_semantic_future_candidate_class_row_shape ?class"
    using checked_row
    by (simp add: comma_semantic_future_candidate_class_row_checked_def)
  have step:
    "comma_semantic_future_candidate_class_step ?class =
      Some (comma_semantic_future_candidate_controls!?class)"
    using class_valid
    by (simp add: comma_semantic_future_candidate_class_step_def)
  have control:
    "comma_weighted_crt_apply
      (fst (comma_semantic_future_candidate_parent_key_action family_slot)) phase =
      Some (comma_semantic_future_candidate_output_control
        ?class,0)"
    using selected family actions_length
    by (simp add: comma_semantic_future_candidate_parent_key_action_def
      comma_semantic_future_crt_map_action_control_def
      comma_semantic_future_crt_map_control_eval comma_weighted_crt_apply_def)
  have north:
    "comma_weighted_crt_apply
      (fst (snd (comma_semantic_future_candidate_parent_key_action family_slot))) phase =
      Some (comma_semantic_future_candidate_output_north_id
        ?class,0)"
    using selected family actions_length
    by (simp add: comma_semantic_future_candidate_parent_key_action_def
      comma_semantic_future_crt_map_action_control_def
      comma_semantic_future_crt_map_control_eval comma_weighted_crt_apply_def)
  have south:
    "comma_weighted_crt_apply
      (snd (snd (comma_semantic_future_candidate_parent_key_action family_slot))) phase =
      Some (comma_semantic_future_candidate_output_south_id
        ?class,0)"
    using selected family actions_length
    by (simp add: comma_semantic_future_candidate_parent_key_action_def
      comma_semantic_future_crt_map_action_control_def
      comma_semantic_future_crt_map_control_eval comma_weighted_crt_apply_def)
  have selected_control:
    "comma_semantic_future_candidate_output_control ?class =
      Some (comma_semantic_future_candidate_controls!?class)"
    using class_valid
    by (simp add: comma_semantic_future_candidate_output_control_def
      comma_semantic_future_candidate_class_output_key_def)
  show ?thesis
  proof (cases "comma_semantic_future_candidate_controls!?class")
    case (Comma_Future_Fork target)
    obtain left right where pair:
      "comma_semantic_future_candidate_children!?class = (Some left,Some right)"
      and left_valid:
      "comma_semantic_future_candidate_class_valid left"
      and right_valid:
      "comma_semantic_future_candidate_class_valid right"
      and ordered:
      "comma_semantic_future_candidate_class_children ?class
        (Comma_Future_Fork target) = [left,right]"
      and output:
      "comma_semantic_future_candidate_class_output ?class =
        Some (Comma_Future_Fork target,[left,right])"
      using class_shape step Comma_Future_Fork
      by (cases "comma_semantic_future_candidate_children!?class")
        (auto simp: comma_semantic_future_candidate_class_row_shape_def
          comma_semantic_future_candidate_class_output_def
          comma_semantic_future_candidate_class_children_def
          split: option.splits prod.splits)
    have north_id:
      "comma_semantic_future_candidate_output_north_id ?class = left"
      using pair step Comma_Future_Fork
      by (simp add: comma_semantic_future_candidate_output_north_id_def
        comma_semantic_future_candidate_output_north_def
        comma_semantic_future_candidate_class_step_def)
    have south_id:
      "comma_semantic_future_candidate_output_south_id ?class = right"
      using pair step Comma_Future_Fork
      by (simp add: comma_semantic_future_candidate_output_south_id_def
        comma_semantic_future_candidate_output_south_def
        comma_semantic_future_candidate_class_step_def)
    have control_fork:
      "comma_weighted_crt_apply
        (comma_semantic_future_projected_control_action
          (comma_semantic_future_candidate_parent_key_action family_slot)) phase =
        Some (Some (Comma_Future_Fork target),0)"
      using control selected_control Comma_Future_Fork
      by (simp add: comma_semantic_future_projected_control_action_def)
    have north_fork:
      "comma_weighted_crt_apply
        (comma_semantic_future_projected_north_action
          (comma_semantic_future_candidate_parent_key_action family_slot)) phase =
        Some (left,0)"
      using north north_id by (simp add: comma_semantic_future_projected_north_action_def)
    have south_fork:
      "comma_weighted_crt_apply
        (comma_semantic_future_projected_south_action
          (comma_semantic_future_candidate_parent_key_action family_slot)) phase =
        Some (right,0)"
      using south south_id by (simp add: comma_semantic_future_projected_south_action_def)
    have target_bounds: "2 \<le> target" "target \<le> 9"
      using class_shape step Comma_Future_Fork
      by (auto simp: comma_semantic_future_candidate_class_row_shape_def)
    have children_shape:
      "comma_semantic_future_action_children_shape
        (Comma_Future_Fork target) [left,right]"
      using target_bounds by (simp add: comma_semantic_future_action_children_shape.simps)
    have projected:
      "comma_semantic_future_projected_key_apply
        (comma_semantic_future_candidate_parent_key_action family_slot) phase =
        Some (Some (Comma_Future_Fork target),[left,right])"
      by (rule comma_semantic_future_projected_key_apply_exact
        [OF control_fork north_fork south_fork target_bounds children_shape])
    show ?thesis
      using projected output pair step
      by (simp add: comma_semantic_future_candidate_class_output_key_def
        comma_semantic_future_candidate_parent_key_action_def
        comma_semantic_future_candidate_output_control_def
        comma_semantic_future_candidate_output_north_def
        comma_semantic_future_candidate_output_south_def)
  next
    case Comma_Future_Landmine
    have landmine:
      "comma_weighted_crt_apply
        (comma_semantic_future_projected_control_action
          (comma_semantic_future_candidate_parent_key_action family_slot)) phase =
        Some (Some Comma_Future_Landmine,0)"
      using control selected_control Comma_Future_Landmine
      by (simp add: comma_semantic_future_projected_control_action_def)
    have output:
      "comma_semantic_future_candidate_class_output ?class =
        Some (Comma_Future_Landmine,[])"
    proof -
      have pair:
        "comma_semantic_future_candidate_children!?class = (None,None)"
        using class_shape step Comma_Future_Landmine
        by (cases "comma_semantic_future_candidate_children!?class")
          (auto simp: comma_semantic_future_candidate_class_row_shape_def
            split: option.splits prod.splits)
      show ?thesis
        using step pair Comma_Future_Landmine
        by (simp add: comma_semantic_future_candidate_class_output_def
          comma_semantic_future_candidate_class_children_def)
    qed
    have projected:
      "comma_semantic_future_projected_key_apply
        (comma_semantic_future_candidate_parent_key_action family_slot) phase =
        Some (Some Comma_Future_Landmine,[])"
      by (rule comma_semantic_future_projected_key_apply_landmine[OF landmine])
    show ?thesis using projected output step
      by (simp add: comma_semantic_future_candidate_parent_key_action_def
        comma_semantic_future_candidate_class_output_key_def
        comma_semantic_future_candidate_output_control_def)
  qed
qed

fun comma_semantic_future_nf_control_of_crt ::
    "comma_semantic_b1_crt_control \<Rightarrow> comma_future_control option" where
  "comma_semantic_future_nf_control_of_crt
      (Comma_Semantic_B1_CRT_Continue root) = None"
| "comma_semantic_future_nf_control_of_crt
      (Comma_Semantic_B1_CRT_Stop J) =
    (if J<9 then Some (comma_semantic_future_control_of_terminal_position J)
     else None)"
| "comma_semantic_future_nf_control_of_crt
      Comma_Semantic_B1_CRT_Invalid = None"

definition comma_semantic_future_nf_key_action ::
    "nat \<times> comma_semantic_b1_crt_dag \<Rightarrow>
      nat \<times> (comma_future_control option \<times> nat)
        comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_nf_key_action action =
    comma_semantic_future_crt_map_action_control
      (\<lambda>control. (comma_semantic_future_nf_control_of_crt control,0))
      action"

lemma comma_semantic_future_nf_key_action_shape:
  "comma_weighted_crt_shape lower
      (snd (comma_semantic_future_nf_key_action action)) =
    comma_weighted_crt_shape lower (snd action)"
  by (cases action)
    (simp add: comma_semantic_future_nf_key_action_def
      comma_semantic_future_crt_map_action_control_def
      comma_semantic_future_crt_map_control_shape)

lemma comma_semantic_future_nf_key_action_apply:
  assumes source:
    "comma_weighted_crt_apply action phase = Some (control,delta)"
  shows "comma_weighted_crt_apply
      (comma_semantic_future_nf_key_action action) phase =
    Some ((comma_semantic_future_nf_control_of_crt control,0),delta)"
  using source
  by (cases action)
    (auto simp: comma_semantic_future_nf_key_action_def
      comma_semantic_future_crt_map_action_control_def
      comma_semantic_future_crt_map_control_eval
      comma_weighted_crt_apply_def split: option.splits prod.splits)

definition comma_semantic_future_initial_nf_key_action ::
    "nat \<Rightarrow> nat \<Rightarrow>
      nat \<times> (comma_future_control option \<times> nat)
        comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_initial_nf_key_action phase family_slot =
    (if phase<924 \<and> family_slot<16 then
       comma_semantic_future_nf_key_action
         (comma_semantic_future_initial_nf_dags!family_slot)
     else (0,Comma_Weighted_CRT_Leaf (None,0)))"

lemma comma_semantic_future_initial_nf_key_action_exact:
  assumes phase: "phase<924"
    and slot: "family_slot<16"
    and source_length:
      "length comma_semantic_graph_initial_source_actions=16"
    and b32_length:
      "length comma_semantic_future_rank_b32_weighted_actions=46"
  shows "comma_semantic_future_initial_nf_key_action phase family_slot =
    comma_semantic_future_nf_key_action
      (comma_semantic_future_initial_nf_dags!family_slot)"
  using phase slot by (simp add: comma_semantic_future_initial_nf_key_action_def)

lemma comma_semantic_future_family_action_nf_direct_stop:
  assumes source: "source_round phase source_cid =
      Comma_Semantic_B1_Stop_At J 0"
  shows "comma_semantic_future_family_action_nf_spec source_round b32_action
      phase source_cid = Comma_Semantic_B1_Stop_At J 0"
  using source
  by (simp add: comma_semantic_future_family_action_nf_spec_def)

lemma comma_semantic_future_family_action_nf_crossing_stop:
  assumes source: "source_round phase source_cid =
      Comma_Semantic_B1_Continue root"
    and target: "b32_action ((phase+1) mod 924) root =
      Comma_Semantic_B1_Stop_At J H"
  shows "comma_semantic_future_family_action_nf_spec source_round b32_action
      phase source_cid = Comma_Semantic_B1_Stop_At J (1+H)"
  using source target
  by (simp add: comma_semantic_future_family_action_nf_spec_def)

lemma comma_semantic_future_source_nf_reconstruct_delta:
  "(if delta=0 then 0 else 1) +
      (delta - (if delta=0 then 0 else 1)) = delta"
  by (cases delta) simp_all

lemma comma_semantic_future_source_nf_crossing_reconstruct:
  assumes height: "delta=1+H"
  shows "(if delta=0 then 0 else 1)=1"
    "delta - (if delta=0 then 0 else 1)=H"
  using height by simp_all

lemma comma_semantic_future_source_nf_direct_reconstruct:
  "(if 0=0 then 0 else 1)=0"
    "0 - (if 0=0 then 0 else 1)=0"
  by simp_all

definition comma_semantic_future_action_of_source_nf_stop ::
    "nat list \<Rightarrow> comma_semantic_b1_weighted_result \<Rightarrow>
      comma_semantic_future_weighted_action option" where
  "comma_semantic_future_action_of_source_nf_stop children result =
    (case result of
       Comma_Semantic_B1_Stop_At J delta \<Rightarrow>
         comma_semantic_future_action_of_weighted_stop
           (if delta=0 then 0 else 1) children
           (Comma_Semantic_B1_Stop_At J
             (delta - (if delta=0 then 0 else 1)))
     | _ \<Rightarrow> None)"

lemma comma_semantic_future_action_of_source_nf_direct_exact:
  assumes stop: "result=Comma_Semantic_B1_Stop_At J 0"
    and position: "J<9"
    and children_shape:
      "comma_semantic_future_action_children_shape
        (comma_semantic_future_control_of_terminal_position J) children"
  obtains action where
    "comma_semantic_future_action_of_source_nf_stop children result =
      Some action"
    "comma_semantic_future_action_local_delta action=0"
    "comma_semantic_future_action_complete_decades action=0"
    "comma_semantic_future_action_completed_delta action=0"
    "comma_semantic_future_action_stop_weight action=J"
    "comma_semantic_future_action_ordered_children action=children"
proof -
  have height: "0\<le>26" by simp
  obtain action where selected:
      "comma_semantic_future_action_of_weighted_stop 0 children result =
        Some action"
    and local_delta: "comma_semantic_future_action_local_delta action=0"
    and complete: "comma_semantic_future_action_complete_decades action=0"
    and delta: "comma_semantic_future_action_completed_delta action=0"
    and weight: "comma_semantic_future_action_stop_weight action=J"
    and ordered: "comma_semantic_future_action_ordered_children action=children"
    by (rule comma_semantic_future_action_of_weighted_stop_exact
        [OF stop position height children_shape])
  have decoded:
    "comma_semantic_future_action_of_source_nf_stop children result =
      Some action"
    using selected local_delta complete stop
    by (simp add: comma_semantic_future_action_of_source_nf_stop_def)
  show thesis
    by (rule that[OF decoded local_delta complete delta weight ordered])
qed

lemma comma_semantic_future_action_of_source_nf_crossing_exact:
  assumes stop: "result=Comma_Semantic_B1_Stop_At J (1+H)"
    and position: "J<9"
    and height: "H\<le>26"
    and children_shape:
      "comma_semantic_future_action_children_shape
        (comma_semantic_future_control_of_terminal_position J) children"
  obtains action where
    "comma_semantic_future_action_of_source_nf_stop children result =
      Some action"
    "comma_semantic_future_action_local_delta action=1"
    "comma_semantic_future_action_complete_decades action=H"
    "comma_semantic_future_action_completed_delta action=1+H"
    "comma_semantic_future_action_stop_weight action=9*H+J"
    "comma_semantic_future_action_ordered_children action=children"
proof -
  have total: "1+H - 1 = H" using height by simp
  obtain action where selected:
      "comma_semantic_future_action_of_weighted_stop 1 children result =
        Some action"
    and local_delta: "comma_semantic_future_action_local_delta action=1"
    and complete: "comma_semantic_future_action_complete_decades action=H"
    and delta: "comma_semantic_future_action_completed_delta action=1+H"
    and weight: "comma_semantic_future_action_stop_weight action=9*H+J"
    and ordered: "comma_semantic_future_action_ordered_children action=children"
    by (rule comma_semantic_future_action_of_weighted_stop_exact
        [OF stop position height children_shape])
  have decoded:
    "comma_semantic_future_action_of_source_nf_stop children result =
      Some action"
    using selected local_delta complete stop total
    by (simp add: comma_semantic_future_action_of_source_nf_stop_def)
  show thesis
    by (rule that[OF decoded local_delta complete delta weight ordered])
qed

text \<open>
The source action carries its local displacement as a value and its accumulated
complete-decade height as the weighted result.  The bind below transports
those two quantities into a receiver before the consumer projects a child
component.  The public comparison uses the three component actions above:
Fork checks both IDs and their shared weight, while Landmine observes only its
control and arity.
\<close>

definition comma_semantic_future_selected_phase_bind ::
    "nat \<times> (('a \<times> nat) comma_semantic_weighted_crt_dag) \<Rightarrow>
      ('a \<Rightarrow> 'b comma_semantic_weighted_crt_dag) \<Rightarrow>
      nat \<times> ((('a \<times> nat) \<times> 'b) comma_semantic_weighted_crt_dag)" where
  "comma_semantic_future_selected_phase_bind action receiver =
    comma_semantic_future_crt_phase_bind action
      (\<lambda>(control,delta).
        comma_weighted_crt_shift delta (receiver control))"

lemma comma_semantic_future_selected_phase_bind_apply:
  fixes action :: "nat \<times> (('a \<times> nat) comma_semantic_weighted_crt_dag)"
    and receiver :: "'a \<Rightarrow> 'b comma_semantic_weighted_crt_dag"
  assumes phase: "r<924"
    and source_shape: "comma_weighted_crt_shape 0 (snd action)"
    and receiver_shape:
      "\<And>control. comma_weighted_crt_shape 0 (receiver control)"
    and source:
      "comma_weighted_crt_apply action r = Some ((control,delta),height)"
    and target:
      "comma_weighted_crt_eval (receiver control)
        ((r+delta+height) mod 924) = Some (children,0)"
  shows "comma_weighted_crt_apply
      (comma_semantic_future_selected_phase_bind action receiver) r =
    Some (((control,delta),children),height)"
proof -
  have selected:
    "comma_weighted_crt_apply
      (comma_semantic_future_crt_phase_bind action
        (\<lambda>(selected,delta). comma_weighted_crt_shift delta
          (receiver selected))) r =
      Some (((control,delta),children),height+0)"
    by (rule comma_semantic_future_crt_phase_bind_apply_selected_delta
      [OF phase source_shape receiver_shape source target])
  show ?thesis
    using selected
    by (simp add: comma_semantic_future_selected_phase_bind_def)
qed

definition comma_semantic_future_control_projection_action ::
    "nat \<times> (('a \<times> nat) comma_semantic_weighted_crt_dag) \<Rightarrow>
      nat \<times> 'a comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_control_projection_action action =
    comma_semantic_future_crt_map_action_control fst action"

definition comma_semantic_future_child_projection_action ::
    "nat \<times> (('a \<times> nat) comma_semantic_weighted_crt_dag) \<Rightarrow>
      ('a \<Rightarrow> 'b comma_semantic_weighted_crt_dag) \<Rightarrow>
      nat \<times> 'b comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_child_projection_action action receiver =
    comma_semantic_future_crt_map_action_control snd
      (comma_semantic_future_selected_phase_bind action receiver)"

lemma comma_semantic_future_control_projection_action_apply:
  assumes source:
    "comma_weighted_crt_apply action phase = Some ((control,local_delta),height)"
  shows "comma_weighted_crt_apply
      (comma_semantic_future_control_projection_action action) phase =
    Some (control,height)"
  using source
  by (cases action)
    (simp add: comma_semantic_future_control_projection_action_def
      comma_semantic_future_crt_map_action_control_def
      comma_semantic_future_crt_map_control_eval comma_weighted_crt_apply_def
      split: option.splits prod.splits)

lemma comma_semantic_future_child_projection_action_shape:
  "comma_weighted_crt_shape 0
      (snd (comma_semantic_future_child_projection_action action receiver)) =
    (comma_weighted_crt_shape 0 (snd action) \<and>
      (\<forall>control. comma_weighted_crt_shape 0 (receiver control)))"
  by (cases action)
    (simp add: comma_semantic_future_child_projection_action_def
      comma_semantic_future_selected_phase_bind_def
      comma_semantic_future_crt_phase_bind_def
      comma_semantic_future_crt_phase_bind_aux_shape
      comma_semantic_future_crt_map_action_control_def
      comma_semantic_future_crt_map_control_shape)

lemma comma_semantic_future_child_projection_action_apply:
  assumes phase: "phase<924"
    and source_shape: "comma_weighted_crt_shape 0 (snd action)"
    and receiver_shape:
      "\<And>control. comma_weighted_crt_shape 0 (receiver control)"
    and source:
      "comma_weighted_crt_apply action phase =
        Some ((control,local_delta),height)"
    and target:
      "comma_weighted_crt_eval (receiver control)
        ((phase+local_delta+height) mod 924) = Some (child,0)"
  shows "comma_weighted_crt_apply
      (comma_semantic_future_child_projection_action action receiver) phase =
    Some (child,height)"
proof -
  have bound:
    "comma_weighted_crt_apply
      (comma_semantic_future_selected_phase_bind action receiver) phase =
      Some (((control,local_delta),child),height)"
    by (rule comma_semantic_future_selected_phase_bind_apply
      [OF phase source_shape receiver_shape source target])
  show ?thesis using bound
    by (cases action)
      (simp add: comma_semantic_future_child_projection_action_def
        comma_semantic_future_crt_map_action_control_def
        comma_semantic_future_crt_map_control_eval comma_weighted_crt_apply_def
        split: option.splits prod.splits)
qed

ML \<open>
  val published = @{thms
    comma_semantic_future_candidate_child_receiver_north_def
    comma_semantic_future_candidate_child_receiver_south_def
    comma_semantic_future_candidate_child_receiver_north_shape
    comma_semantic_future_candidate_child_receiver_south_shape
    comma_semantic_future_candidate_child_receiver_north_fork_exact
    comma_semantic_future_candidate_child_receiver_south_fork_exact
    comma_semantic_future_candidate_child_receiver_north_landmine_placeholder
    comma_semantic_future_candidate_child_receiver_south_landmine_placeholder
    comma_semantic_future_candidate_class_output_key_def
    comma_semantic_future_candidate_parent_key_action_def
    comma_semantic_future_candidate_parent_key_action_shape
    comma_semantic_future_candidate_parent_key_action_apply
    comma_semantic_future_candidate_class_output_key_from_projections
    comma_semantic_future_nf_key_action_shape
    comma_semantic_future_nf_key_action_apply
    comma_semantic_future_initial_nf_key_action_exact
    comma_semantic_future_action_of_source_nf_stop_def
    comma_semantic_future_family_action_nf_direct_stop
    comma_semantic_future_family_action_nf_crossing_stop
    comma_semantic_future_source_nf_reconstruct_delta
    comma_semantic_future_source_nf_crossing_reconstruct
    comma_semantic_future_source_nf_direct_reconstruct
    comma_semantic_future_action_of_source_nf_direct_exact
    comma_semantic_future_action_of_source_nf_crossing_exact
    comma_semantic_future_selected_phase_bind_def
    comma_semantic_future_selected_phase_bind_apply}
  val _ = Thm.consolidate published
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Future action normal forms and weighted source-key comparison" published
\<close>

end
