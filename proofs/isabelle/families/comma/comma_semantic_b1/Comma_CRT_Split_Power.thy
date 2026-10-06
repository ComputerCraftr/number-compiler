theory Comma_CRT_Split_Power
  imports Comma_CRT_Equivalence
begin

text \<open>
The powered owner keeps control geometry and terminal weight in separate
multi-terminal CRT diagrams.  A geometry leaf records only Live root, Stop,
or Invalid; the exact D value lives in the independent nat-option diagram.
Consequently geometry node reduction never compares Stop weights.

Composition is a recursive cofactor walk over the four CRT dimensions.  It
does not enumerate return rows or build a left-row/right-row Cartesian list.
At a left Live leaf the selected receiving root is composed by translating
the remaining CRT diagram; a left Stop or Invalid leaf is absorbing.
\<close>

datatype comma_crt_control =
    Comma_CRT_Control_Live nat
  | Comma_CRT_Control_Stop
  | Comma_CRT_Control_Invalid

datatype 'a comma_crt_mdd =
    Comma_CRT_MDD_Leaf 'a
  | Comma_CRT_MDD_Node nat "'a comma_crt_mdd list"

type_synonym comma_crt_control_mdd = "comma_crt_control comma_crt_mdd"
type_synonym comma_crt_weight_mdd = "nat option comma_crt_mdd"

record comma_crt_split_action =
  comma_crt_split_control :: comma_crt_control_mdd
  comma_crt_split_weight :: comma_crt_weight_mdd

fun comma_crt_control_of_result ::
    "comma_semantic_b1_result \<Rightarrow> comma_crt_control" where
  "comma_crt_control_of_result (Comma_Semantic_B1_Live root) =
    Comma_CRT_Control_Live root"
| "comma_crt_control_of_result (Comma_Semantic_B1_Stop D) =
    Comma_CRT_Control_Stop"
| "comma_crt_control_of_result Comma_Semantic_B1_Invalid =
    Comma_CRT_Control_Invalid"

fun comma_crt_weight_of_result ::
    "comma_semantic_b1_result \<Rightarrow> nat option" where
  "comma_crt_weight_of_result (Comma_Semantic_B1_Live root) = None"
| "comma_crt_weight_of_result (Comma_Semantic_B1_Stop D) = Some D"
| "comma_crt_weight_of_result Comma_Semantic_B1_Invalid = None"

fun comma_crt_result_of_split ::
    "comma_crt_control \<Rightarrow> nat option \<Rightarrow> comma_semantic_b1_result" where
  "comma_crt_result_of_split (Comma_CRT_Control_Live root) weight =
    Comma_Semantic_B1_Live root"
| "comma_crt_result_of_split Comma_CRT_Control_Stop (Some D) =
    Comma_Semantic_B1_Stop D"
| "comma_crt_result_of_split Comma_CRT_Control_Stop None =
    Comma_Semantic_B1_Invalid"
| "comma_crt_result_of_split Comma_CRT_Control_Invalid weight =
    Comma_Semantic_B1_Invalid"

primrec comma_crt_mdd_eval :: "nat \<Rightarrow> 'a comma_crt_mdd \<Rightarrow> 'a option" where
  "comma_crt_mdd_eval phase (Comma_CRT_MDD_Leaf value) = Some value"
| "comma_crt_mdd_eval phase (Comma_CRT_MDD_Node level children) =
    (if level<4 \<and> length children=comma_crt_period level then
       map (comma_crt_mdd_eval phase) children !
         (phase mod comma_crt_period level)
     else None)"

declare comma_crt_mdd_eval.simps(2)[code del]

lemma comma_crt_mdd_eval_node_selected[code]:
  "comma_crt_mdd_eval phase (Comma_CRT_MDD_Node level children) =
    (if level<4 \<and> length children=comma_crt_period level then
       comma_crt_mdd_eval phase (children!(phase mod comma_crt_period level))
     else None)"
proof (cases "level<4 \<and> length children=comma_crt_period level")
  case True
  then have level: "level<4"
    and width: "length children=comma_crt_period level" by auto
  have positive: "0<comma_crt_period level"
    by (rule comma_crt_period_positive[OF level])
  have selected: "phase mod comma_crt_period level<length children"
    using positive width by simp
  have map_selected:
    "map (comma_crt_mdd_eval phase) children !
        (phase mod comma_crt_period level) =
      comma_crt_mdd_eval phase (children!(phase mod comma_crt_period level))"
    by (rule nth_map[OF selected])
  show ?thesis using True map_selected by simp
next
  case False
  then show ?thesis
    by (simp only: comma_crt_mdd_eval.simps if_False)
qed

primrec comma_crt_mdd_admitted ::
    "nat \<Rightarrow> 'a comma_crt_mdd \<Rightarrow> bool" where
  "comma_crt_mdd_admitted lower (Comma_CRT_MDD_Leaf value) = True"
| "comma_crt_mdd_admitted lower (Comma_CRT_MDD_Node level children) =
    (lower\<le>level \<and> level<4 \<and>
      length children=comma_crt_period level \<and>
      list_all (comma_crt_mdd_admitted (Suc level)) children)"

definition comma_crt_mdd_node ::
    "nat \<Rightarrow> 'a comma_crt_mdd list \<Rightarrow> 'a comma_crt_mdd" where
  "comma_crt_mdd_node level children =
    (if children\<noteq>[] \<and>
        list_all (\<lambda>child. child=hd children) children
     then hd children else Comma_CRT_MDD_Node level children)"

fun comma_crt_mdd_cofactor ::
    "nat \<Rightarrow> nat \<Rightarrow> 'a comma_crt_mdd \<Rightarrow>
      'a comma_crt_mdd option" where
  "comma_crt_mdd_cofactor level digit (Comma_CRT_MDD_Leaf value) =
    Some (Comma_CRT_MDD_Leaf value)"
| "comma_crt_mdd_cofactor level digit (Comma_CRT_MDD_Node node_level children) =
    (if node_level<level then None
     else if level<node_level then
       Some (Comma_CRT_MDD_Node node_level children)
     else if digit<length children then Some (children!digit) else None)"

lemma comma_crt_mdd_cofactor_admitted_digit:
  assumes admitted: "comma_crt_mdd_admitted level diagram"
    and level: "level<4"
    and digit: "digit<comma_crt_period level"
  obtains child where
    "comma_crt_mdd_cofactor level digit diagram=Some child"
    "comma_crt_mdd_admitted (Suc level) child"
proof (cases diagram)
  case (Comma_CRT_MDD_Leaf payload)
  show thesis
    by (rule that[of diagram]) (simp_all add: Comma_CRT_MDD_Leaf)
next
  case (Comma_CRT_MDD_Node node_level children)
  have lower: "level\<le>node_level" and node_bound: "node_level<4"
    and width: "length children=comma_crt_period node_level"
    and children_admitted:
      "list_all (comma_crt_mdd_admitted (Suc node_level)) children"
    using admitted Comma_CRT_MDD_Node by auto
  show thesis
  proof (cases "node_level=level")
    case True
    have digit_bound: "digit<length children"
      using digit width True by simp
    have child_admitted:
      "comma_crt_mdd_admitted (Suc level) (children!digit)"
      using children_admitted digit_bound True by (auto simp: list_all_iff)
    show thesis
      by (rule that[of "children!digit"])
        (use Comma_CRT_MDD_Node True digit_bound child_admitted in simp_all)
  next
    case False
    have later: "level<node_level" using lower False by arith
    have child_admitted:
      "comma_crt_mdd_admitted (Suc level) diagram"
      using admitted Comma_CRT_MDD_Node later by simp
    show thesis
      by (rule that[of diagram])
        (use Comma_CRT_MDD_Node later child_admitted in simp_all)
  qed
qed

definition comma_crt_mdd_cofactor_or_self ::
    "nat \<Rightarrow> nat \<Rightarrow> 'a comma_crt_mdd \<Rightarrow> 'a comma_crt_mdd" where
  "comma_crt_mdd_cofactor_or_self level digit diagram =
    (case comma_crt_mdd_cofactor level digit diagram of
       Some child \<Rightarrow> child | None \<Rightarrow> diagram)"

primrec comma_crt_mdd_shift :: "nat \<Rightarrow> 'a comma_crt_mdd \<Rightarrow> 'a comma_crt_mdd" where
  "comma_crt_mdd_shift shift (Comma_CRT_MDD_Leaf value) =
    Comma_CRT_MDD_Leaf value"
| "comma_crt_mdd_shift shift (Comma_CRT_MDD_Node level children) =
    Comma_CRT_MDD_Node level
      (rotate shift (map (comma_crt_mdd_shift shift) children))"

primrec comma_crt_mdd_map ::
    "('a \<Rightarrow> 'b) \<Rightarrow> 'a comma_crt_mdd \<Rightarrow> 'b comma_crt_mdd" where
  "comma_crt_mdd_map f (Comma_CRT_MDD_Leaf value) =
    Comma_CRT_MDD_Leaf (f value)"
| "comma_crt_mdd_map f (Comma_CRT_MDD_Node level children) =
    Comma_CRT_MDD_Node level (map (comma_crt_mdd_map f) children)"

lemma comma_crt_mdd_cofactor_or_self_admitted:
  assumes admitted: "comma_crt_mdd_admitted level diagram"
    and level: "level<4"
    and digit: "digit<comma_crt_period level"
  shows "comma_crt_mdd_admitted (Suc level)
    (comma_crt_mdd_cofactor_or_self level digit diagram)"
proof -
  obtain child where cofactor:
    "comma_crt_mdd_cofactor level digit diagram=Some child"
    and child: "comma_crt_mdd_admitted (Suc level) child"
    by (rule comma_crt_mdd_cofactor_admitted_digit[OF admitted level digit])
  show ?thesis using cofactor child
    by (simp add: comma_crt_mdd_cofactor_or_self_def)
qed

lemma comma_crt_mdd_map_admitted:
  assumes "comma_crt_mdd_admitted lower diagram"
  shows "comma_crt_mdd_admitted lower (comma_crt_mdd_map f diagram)"
  using assms
  by (induction diagram arbitrary: lower)
    (auto simp: list_all_iff)

definition comma_crt_mdd_weight_after_span :: "nat \<Rightarrow> comma_crt_weight_mdd \<Rightarrow>
    comma_crt_weight_mdd" where
  "comma_crt_mdd_weight_after_span span diagram =
    comma_crt_mdd_map (\<lambda>weight. case weight of None \<Rightarrow> None
      | Some D \<Rightarrow> Some (9*span+D)) diagram"

lemma comma_crt_mdd_weight_after_span_admitted:
  "comma_crt_mdd_admitted lower diagram \<Longrightarrow>
    comma_crt_mdd_admitted lower (comma_crt_mdd_weight_after_span span diagram)"
  by (simp add: comma_crt_mdd_weight_after_span_def comma_crt_mdd_map_admitted)

lemma comma_crt_split_result_of_source:
  "comma_crt_result_of_split (comma_crt_control_of_result result)
      (comma_crt_weight_of_result result) = result"
  by (cases result) simp_all

lemma comma_crt_split_control_weight_distinguish:
  assumes "left\<noteq>right"
  shows "comma_crt_result_of_split Comma_CRT_Control_Stop (Some left) \<noteq>
    comma_crt_result_of_split Comma_CRT_Control_Stop (Some right)"
  using assms by simp

lemma comma_crt_split_live_ignores_weight:
  "comma_crt_result_of_split (Comma_CRT_Control_Live root) weight =
    Comma_Semantic_B1_Live root"
  by (cases weight) simp_all

lemma comma_crt_split_invalid_never_stops:
  "comma_crt_result_of_split Comma_CRT_Control_Invalid weight =
      Comma_Semantic_B1_Invalid \<and>
    comma_crt_result_of_split Comma_CRT_Control_Stop None =
      Comma_Semantic_B1_Invalid"
  by (cases weight) simp_all

lemma comma_crt_split_live_right_weight_after:
  "comma_crt_result_of_split right_control
      (case right_weight of None \<Rightarrow> None | Some D \<Rightarrow> Some (9*span+D)) =
    comma_semantic_b1_cell_result span
      (Comma_Semantic_B1_Live left_root)
      (comma_crt_result_of_split right_control right_weight)"
  by (cases right_control; cases right_weight)
    (simp_all add: comma_semantic_b1_cell_result_def
    comma_semantic_b1_weight_after_def)

definition comma_crt_split_mdd_result_at ::
    "nat \<Rightarrow> comma_crt_control_mdd \<Rightarrow>
      comma_crt_weight_mdd \<Rightarrow> comma_semantic_b1_result option" where
  "comma_crt_split_mdd_result_at phase controls weights =
    (case (comma_crt_mdd_eval phase controls,
        comma_crt_mdd_eval phase weights) of
       (Some control,Some weight) \<Rightarrow>
         Some (comma_crt_result_of_split control weight)
     | _ \<Rightarrow> None)"

definition comma_crt_split_compose_expected_at ::
    "nat \<Rightarrow> comma_crt_control_mdd \<Rightarrow>
      comma_crt_weight_mdd \<Rightarrow>
      (nat \<Rightarrow> comma_crt_control_mdd) \<Rightarrow>
      (nat \<Rightarrow> comma_crt_weight_mdd) \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_result option" where
  "comma_crt_split_compose_expected_at span left_control left_weight
      right_controls right_weights phase =
    (case comma_crt_split_mdd_result_at phase left_control left_weight of
       Some (Comma_Semantic_B1_Live root) \<Rightarrow>
         map_option (comma_semantic_b1_cell_result span
             (Comma_Semantic_B1_Live root))
           (comma_crt_split_mdd_result_at (phase+span)
             (right_controls root) (right_weights root))
     | Some result \<Rightarrow> Some result
     | None \<Rightarrow> None)"

fun comma_crt_split_value_consistent ::
    "comma_crt_control \<Rightarrow> nat option \<Rightarrow> bool" where
  "comma_crt_split_value_consistent (Comma_CRT_Control_Live root) weight =
    (weight=None)"
| "comma_crt_split_value_consistent Comma_CRT_Control_Stop weight =
    (\<exists>D. weight=Some D)"
| "comma_crt_split_value_consistent Comma_CRT_Control_Invalid weight =
    (weight=None)"

definition comma_crt_mdd_split_consistent ::
    "nat \<Rightarrow> comma_crt_control_mdd \<Rightarrow> comma_crt_weight_mdd \<Rightarrow> bool" where
  "comma_crt_mdd_split_consistent lower controls weights \<longleftrightarrow>
    comma_crt_mdd_admitted lower controls \<and>
    comma_crt_mdd_admitted lower weights \<and>
    (\<forall>phase<924. case (comma_crt_mdd_eval phase controls,
        comma_crt_mdd_eval phase weights) of
      (Some control,Some weight) \<Rightarrow>
        comma_crt_split_value_consistent control weight
    | _ \<Rightarrow> False)"

lemma comma_crt_split_stop_weights_fixture:
  "comma_crt_split_mdd_result_at 0
      (Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop)
      (Comma_CRT_MDD_Leaf (Some 13)) = Some (Comma_Semantic_B1_Stop 13) \<and>
    comma_crt_split_mdd_result_at 0
      (Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop)
      (Comma_CRT_MDD_Leaf (Some 14)) = Some (Comma_Semantic_B1_Stop 14) \<and>
    Some (Comma_Semantic_B1_Stop 13) \<noteq>
      Some (Comma_Semantic_B1_Stop 14)"
  by (simp add: comma_crt_split_mdd_result_at_def)

lemma comma_crt_split_absent_weight_fixture:
  "comma_crt_split_mdd_result_at 0
      (Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop)
      (Comma_CRT_MDD_Leaf None) = Some Comma_Semantic_B1_Invalid"
  by (simp add: comma_crt_split_mdd_result_at_def)

lemma comma_crt_split_invalid_weight_fixture:
  "comma_crt_split_mdd_result_at 0
      (Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid)
      (Comma_CRT_MDD_Leaf (Some 13)) = Some Comma_Semantic_B1_Invalid"
  by (simp add: comma_crt_split_mdd_result_at_def)

lemma comma_crt_split_shifted_live_weight_fixture:
  "comma_crt_result_of_split Comma_CRT_Control_Stop
      (case Some D of None \<Rightarrow> None | Some weight \<Rightarrow>
        Some (9*span+weight)) =
    comma_semantic_b1_cell_result span
      (Comma_Semantic_B1_Live root)
      (Comma_Semantic_B1_Stop D)"
  by (simp add: comma_semantic_b1_cell_result_def
      comma_semantic_b1_weight_after_def)

lemma comma_crt_mdd_admitted_mono:
  "lower\<le>upper \<Longrightarrow> comma_crt_mdd_admitted upper diagram \<Longrightarrow>
    comma_crt_mdd_admitted lower diagram"
  by (induction diagram arbitrary: lower upper) auto

lemma comma_crt_mdd_node_admitted:
  assumes order: "lower\<le>level" and level: "level<4"
    and width: "length children=comma_crt_period level"
    and children: "list_all (comma_crt_mdd_admitted (Suc level)) children"
  shows "comma_crt_mdd_admitted lower (comma_crt_mdd_node level children)"
proof (cases children)
  case Nil
  then show ?thesis using width comma_crt_period_positive[OF level]
    by (simp add: comma_crt_mdd_node_def)
next
  case (Cons first rest)
  have lower_first: "lower\<le>Suc level" using order by arith
  have first_admitted: "comma_crt_mdd_admitted (Suc level) first"
    using children Cons by simp
  have first_lower: "comma_crt_mdd_admitted lower first"
    by (rule comma_crt_mdd_admitted_mono[OF lower_first first_admitted])
  show ?thesis
    using order level width children first_lower Cons
    by (auto simp: comma_crt_mdd_node_def)
qed

lemma comma_crt_mdd_node_eval:
  assumes level: "level<4" and width: "length children=comma_crt_period level"
  shows "comma_crt_mdd_eval phase (comma_crt_mdd_node level children) =
    comma_crt_mdd_eval phase
      (Comma_CRT_MDD_Node level children)"
proof -
  have positive: "0<comma_crt_period level"
    by (rule comma_crt_period_positive[OF level])
  have nonempty: "children\<noteq>[]" using positive width by auto
  have selected: "phase mod comma_crt_period level<length children"
    using positive width by simp
  show ?thesis
  proof (cases "list_all (\<lambda>child. child=hd children) children")
    case True
    have selected_member:
      "children!(phase mod comma_crt_period level)\<in>set children"
      by (rule nth_mem[OF selected])
    then have same:
      "children!(phase mod comma_crt_period level)=hd children"
      using True selected_member by (auto simp: list_all_iff)
    show ?thesis using True nonempty level width selected same
      by (simp add: comma_crt_mdd_node_def)
  next
    case False
    then show ?thesis using nonempty
      by (simp add: comma_crt_mdd_node_def)
  qed
qed

lemma comma_crt_mdd_cofactor_exact:
  assumes valid: "comma_crt_mdd_admitted level diagram"
    and level: "level<4"
    and digit: "digit=phase mod comma_crt_period level"
  obtains child where
    "comma_crt_mdd_cofactor level digit diagram=Some child"
    "comma_crt_mdd_admitted (Suc level) child"
    "comma_crt_mdd_eval phase child=comma_crt_mdd_eval phase diagram"
proof (cases diagram)
  case (Comma_CRT_MDD_Leaf payload)
  show thesis by (rule that[of diagram]) (simp_all add: Comma_CRT_MDD_Leaf)
next
  case (Comma_CRT_MDD_Node node_level children)
  have order: "level\<le>node_level" and node_bound: "node_level<4"
    and width: "length children=comma_crt_period node_level"
    and child_admitted:
      "list_all (comma_crt_mdd_admitted (Suc node_level)) children"
    using valid Comma_CRT_MDD_Node by auto
  show thesis
  proof (cases "node_level=level")
    case True
    have positive: "0<comma_crt_period level"
      by (rule comma_crt_period_positive[OF level])
    have selected_bound: "digit<length children"
      using digit width True positive by simp
    have selected_admitted:
      "comma_crt_mdd_admitted (Suc level) (children!digit)"
    proof -
      have all_children:
        "\<forall>child\<in>set children. comma_crt_mdd_admitted (Suc level) child"
        using child_admitted True by (simp only: list_all_iff)
      show ?thesis
        using all_children nth_mem[OF selected_bound] by blast
    qed
    have selected_eval:
      "comma_crt_mdd_eval phase (children!digit) =
        comma_crt_mdd_eval phase diagram"
      using Comma_CRT_MDD_Node digit width True level selected_bound
      by simp
    show thesis
      by (rule that[of "children!digit"])
        (use Comma_CRT_MDD_Node True selected_bound selected_admitted selected_eval
          in \<open>simp_all add: digit\<close>)
  next
    case False
    have later: "level<node_level" using order False by arith
    have admitted: "comma_crt_mdd_admitted (Suc level) diagram"
      using valid Comma_CRT_MDD_Node later by simp
    show thesis
      by (rule that[of diagram])
        (use Comma_CRT_MDD_Node later admitted in simp_all)
  qed
qed

lemma comma_crt_mdd_cofactor_or_self_eval:
  assumes admitted: "comma_crt_mdd_admitted level diagram"
    and level: "level<4"
    and index: "digit=phase mod comma_crt_period level"
  shows "comma_crt_mdd_eval phase
      (comma_crt_mdd_cofactor_or_self level digit diagram) =
    comma_crt_mdd_eval phase diagram"
proof -
  obtain child where cofactor:
    "comma_crt_mdd_cofactor level digit diagram=Some child"
    and child_eval: "comma_crt_mdd_eval phase child=comma_crt_mdd_eval phase diagram"
    by (rule comma_crt_mdd_cofactor_exact[OF admitted level index])
  show ?thesis using cofactor child_eval
    by (simp add: comma_crt_mdd_cofactor_or_self_def)
qed

lemma comma_crt_mdd_shift_admitted:
  "comma_crt_mdd_admitted lower diagram \<Longrightarrow>
    comma_crt_mdd_admitted lower (comma_crt_mdd_shift shift diagram)"
  by (induction diagram arbitrary: lower) (auto simp: list_all_iff)

lemma comma_crt_mdd_shift_eval:
  assumes valid: "comma_crt_mdd_admitted lower diagram"
  shows "comma_crt_mdd_eval phase (comma_crt_mdd_shift shift diagram) =
    comma_crt_mdd_eval (phase+shift) diagram"
  using valid
proof (induction diagram arbitrary: lower phase)
  case (Comma_CRT_MDD_Leaf payload)
  then show ?case by simp
next
  case (Comma_CRT_MDD_Node level children)
  have level: "level<4" and width: "length children=comma_crt_period level"
    and children_valid:
      "list_all (comma_crt_mdd_admitted (Suc level)) children"
    using Comma_CRT_MDD_Node.prems by auto
  have positive: "0<comma_crt_period level"
    by (rule comma_crt_period_positive[OF level])
  have target_index: "(phase+shift) mod comma_crt_period level<length children"
    using positive width by simp
  have child_valid:
    "comma_crt_mdd_admitted (Suc level)
      (children!((phase+shift) mod comma_crt_period level))"
    using children_valid target_index by (auto simp: list_all_iff nth_mem)
  have child_eq:
    "comma_crt_mdd_eval phase
       (comma_crt_mdd_shift shift
         (children!((phase+shift) mod comma_crt_period level))) =
     comma_crt_mdd_eval (phase+shift)
       (children!((phase+shift) mod comma_crt_period level))"
    using Comma_CRT_MDD_Node.IH[OF nth_mem[OF target_index] child_valid] .
  have rotated_index:
    "(shift + phase mod comma_crt_period level) mod comma_crt_period level =
      (phase+shift) mod comma_crt_period level"
    using width by (simp add: mod_add_right_eq add.commute)
  show ?case using level width target_index child_eq rotated_index
    by (simp add: nth_rotate nth_map)
qed

lemma comma_crt_mdd_admitted_eval_some:
  assumes "comma_crt_mdd_admitted lower diagram"
  shows "\<exists>value. comma_crt_mdd_eval phase diagram=Some value"
  using assms
proof (induction diagram arbitrary: lower phase)
  case (Comma_CRT_MDD_Leaf payload)
  then show ?case by simp
next
  case (Comma_CRT_MDD_Node level children)
  have level_valid: "level<4"
    and width: "length children=comma_crt_period level"
    and children_valid:
      "list_all (comma_crt_mdd_admitted (Suc level)) children"
    using Comma_CRT_MDD_Node.prems by auto
  have positive: "0<comma_crt_period level"
    by (rule comma_crt_period_positive[OF level_valid])
  have selected: "phase mod comma_crt_period level<length children"
    using positive width by simp
  have child_valid:
    "comma_crt_mdd_admitted (Suc level)
      (children!(phase mod comma_crt_period level))"
    using children_valid nth_mem[OF selected] by (auto simp: list_all_iff)
  obtain child_value where child_eval:
    "comma_crt_mdd_eval phase
      (children!(phase mod comma_crt_period level))=Some child_value"
    using Comma_CRT_MDD_Node.IH[OF nth_mem[OF selected] child_valid] by blast
  show ?case using level_valid width selected child_eval
    by (auto simp: nth_map)
qed

lemma comma_crt_mdd_map_eval:
  assumes admitted: "comma_crt_mdd_admitted lower diagram"
  shows "comma_crt_mdd_eval phase (comma_crt_mdd_map f diagram) =
    map_option f (comma_crt_mdd_eval phase diagram)"
  using admitted
proof (induction diagram arbitrary: lower phase)
  case (Comma_CRT_MDD_Leaf payload)
  then show ?case by simp
next
  case (Comma_CRT_MDD_Node level children)
  have level_valid: "level<4"
    and width: "length children=comma_crt_period level"
    and children_valid:
      "list_all (comma_crt_mdd_admitted (Suc level)) children"
    using Comma_CRT_MDD_Node.prems by auto
  have positive: "0<comma_crt_period level"
    by (rule comma_crt_period_positive[OF level_valid])
  have selected: "phase mod comma_crt_period level<length children"
    using positive width by simp
  have child_valid:
    "comma_crt_mdd_admitted (Suc level)
      (children!(phase mod comma_crt_period level))"
    using children_valid nth_mem[OF selected] by (auto simp: list_all_iff)
  have child_map:
    "comma_crt_mdd_eval phase
      (comma_crt_mdd_map f (children!(phase mod comma_crt_period level))) =
      map_option f (comma_crt_mdd_eval phase
        (children!(phase mod comma_crt_period level)))"
    by (rule Comma_CRT_MDD_Node.IH[OF nth_mem[OF selected] child_valid])
  show ?case using level_valid width selected child_map
    by (simp add: nth_map)
qed

lemma comma_crt_mdd_shift_all_clock_components:
  assumes admitted: "comma_crt_mdd_admitted lower diagram"
  shows "comma_crt_mdd_eval phase
      (comma_crt_mdd_shift 4 diagram) = comma_crt_mdd_eval (phase+4) diagram \<and>
    comma_crt_mdd_eval phase
      (comma_crt_mdd_shift 3 diagram) = comma_crt_mdd_eval (phase+3) diagram \<and>
    comma_crt_mdd_eval phase
      (comma_crt_mdd_shift 7 diagram) = comma_crt_mdd_eval (phase+7) diagram \<and>
    comma_crt_mdd_eval phase
      (comma_crt_mdd_shift 11 diagram) = comma_crt_mdd_eval (phase+11) diagram"
  using comma_crt_mdd_shift_eval[OF admitted, of phase 4]
    comma_crt_mdd_shift_eval[OF admitted, of phase 3]
    comma_crt_mdd_shift_eval[OF admitted, of phase 7]
    comma_crt_mdd_shift_eval[OF admitted, of phase 11]
  by blast

lemma comma_crt_mdd_shift_period_component:
  assumes admitted: "comma_crt_mdd_admitted lower diagram"
  shows "comma_crt_mdd_eval phase
      (comma_crt_mdd_shift (comma_crt_period level) diagram) =
    comma_crt_mdd_eval (phase+comma_crt_period level) diagram"
  by (rule comma_crt_mdd_shift_eval[OF admitted])

lemma comma_crt_split_mdd_result_at_of_result:
  assumes admitted: "comma_crt_mdd_admitted lower diagram"
  shows "comma_crt_split_mdd_result_at phase
      (comma_crt_mdd_map comma_crt_control_of_result diagram)
      (comma_crt_mdd_map comma_crt_weight_of_result diagram) =
    comma_crt_mdd_eval phase diagram"
proof -
  obtain result_value where result_eval:
    "comma_crt_mdd_eval phase diagram=Some result_value"
    using comma_crt_mdd_admitted_eval_some[OF admitted] by blast
  have control_eval:
    "comma_crt_mdd_eval phase
      (comma_crt_mdd_map comma_crt_control_of_result diagram) =
      Some (comma_crt_control_of_result result_value)"
    using comma_crt_mdd_map_eval[OF admitted, of phase comma_crt_control_of_result]
      result_eval by simp
  have weight_eval:
    "comma_crt_mdd_eval phase
      (comma_crt_mdd_map comma_crt_weight_of_result diagram) =
      Some (comma_crt_weight_of_result result_value)"
    using comma_crt_mdd_map_eval[OF admitted, of phase comma_crt_weight_of_result]
      result_eval by simp
  show ?thesis
    using control_eval weight_eval result_eval
    by (simp add: comma_crt_split_mdd_result_at_def
      comma_crt_split_result_of_source)
qed

lemma comma_crt_split_mdd_projection_consistent:
  assumes admitted: "comma_crt_mdd_admitted lower diagram"
  shows "comma_crt_mdd_split_consistent lower
      (comma_crt_mdd_map comma_crt_control_of_result diagram)
      (comma_crt_mdd_map comma_crt_weight_of_result diagram)"
proof -
  have controls_admitted:
    "comma_crt_mdd_admitted lower
      (comma_crt_mdd_map comma_crt_control_of_result diagram)"
    by (rule comma_crt_mdd_map_admitted[OF admitted])
  have weights_admitted:
    "comma_crt_mdd_admitted lower
      (comma_crt_mdd_map comma_crt_weight_of_result diagram)"
    by (rule comma_crt_mdd_map_admitted[OF admitted])
  have pointwise:
    "\<forall>phase<924. case
      (comma_crt_mdd_eval phase
        (comma_crt_mdd_map comma_crt_control_of_result diagram),
       comma_crt_mdd_eval phase
        (comma_crt_mdd_map comma_crt_weight_of_result diagram)) of
        (Some control,Some weight) \<Rightarrow>
          comma_crt_split_value_consistent control weight
      | _ \<Rightarrow> False"
  proof (intro allI impI)
    fix phase :: nat
    assume phase: "phase<924"
    obtain result_value where result_eval:
      "comma_crt_mdd_eval phase diagram=Some result_value"
      using comma_crt_mdd_admitted_eval_some[OF admitted] by blast
    have control_eval:
      "comma_crt_mdd_eval phase
        (comma_crt_mdd_map comma_crt_control_of_result diagram) =
        Some (comma_crt_control_of_result result_value)"
      using comma_crt_mdd_map_eval[OF admitted, of phase comma_crt_control_of_result]
        result_eval by simp
    have weight_eval:
      "comma_crt_mdd_eval phase
        (comma_crt_mdd_map comma_crt_weight_of_result diagram) =
        Some (comma_crt_weight_of_result result_value)"
      using comma_crt_mdd_map_eval[OF admitted, of phase comma_crt_weight_of_result]
        result_eval by simp
    show "case (comma_crt_mdd_eval phase
          (comma_crt_mdd_map comma_crt_control_of_result diagram),
         comma_crt_mdd_eval phase
          (comma_crt_mdd_map comma_crt_weight_of_result diagram)) of
        (Some control,Some weight) \<Rightarrow>
          comma_crt_split_value_consistent control weight
      | _ \<Rightarrow> False"
      using control_eval weight_eval by (cases result_value) simp_all
  qed
  show ?thesis
    unfolding comma_crt_mdd_split_consistent_def
    using controls_admitted weights_admitted pointwise by blast
qed

fun comma_crt_split_compose_from ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_crt_control_mdd \<Rightarrow>
      comma_crt_weight_mdd \<Rightarrow>
      (nat \<Rightarrow> comma_crt_control_mdd) \<Rightarrow>
      (nat \<Rightarrow> comma_crt_weight_mdd) \<Rightarrow>
      comma_crt_control_mdd \<times> comma_crt_weight_mdd" where
  "comma_crt_split_compose_from 0 span left_control left_weight
      right_controls right_weights =
    (case left_control of
       Comma_CRT_MDD_Leaf (Comma_CRT_Control_Live root) \<Rightarrow>
         (comma_crt_mdd_shift span (right_controls root),
          comma_crt_mdd_weight_after_span span
            (comma_crt_mdd_shift span (right_weights root)))
     | Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop \<Rightarrow>
         (left_control,left_weight)
     | Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid \<Rightarrow>
         (left_control,left_weight)
     | Comma_CRT_MDD_Node level children \<Rightarrow>
         (Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid,
          Comma_CRT_MDD_Leaf None))"
| "comma_crt_split_compose_from (Suc remaining) span left_control left_weight
      right_controls right_weights =
    (case left_control of
       Comma_CRT_MDD_Leaf (Comma_CRT_Control_Live root) \<Rightarrow>
         (comma_crt_mdd_shift span (right_controls root),
          comma_crt_mdd_weight_after_span span
            (comma_crt_mdd_shift span (right_weights root)))
     | Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop \<Rightarrow>
         (left_control,left_weight)
     | Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid \<Rightarrow>
         (left_control,left_weight)
     | Comma_CRT_MDD_Node _ _ \<Rightarrow>
         (let level = 4-Suc remaining in
          if level<4 then
            (let branches = map (\<lambda>digit.
              comma_crt_split_compose_from remaining span
                (comma_crt_mdd_cofactor_or_self level digit left_control)
                (comma_crt_mdd_cofactor_or_self level digit left_weight)
                (\<lambda>root. comma_crt_mdd_cofactor_or_self level
                  ((digit+span) mod comma_crt_period level) (right_controls root))
                (\<lambda>root. comma_crt_mdd_cofactor_or_self level
                  ((digit+span) mod comma_crt_period level) (right_weights root)))
                [0..<comma_crt_period level]
             in (comma_crt_mdd_node level (map fst branches),
                 comma_crt_mdd_node level (map snd branches)))
          else (Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid,
                Comma_CRT_MDD_Leaf None)))"

definition comma_crt_split_compose ::
    "nat \<Rightarrow> comma_crt_split_action \<Rightarrow>
      (nat \<Rightarrow> comma_crt_split_action) \<Rightarrow> comma_crt_split_action" where
  "comma_crt_split_compose span left right =
    (let result = comma_crt_split_compose_from 4 span
        (comma_crt_split_control left) (comma_crt_split_weight left)
        (\<lambda>root. comma_crt_split_control (right root))
        (\<lambda>root. comma_crt_split_weight (right root))
     in \<lparr>comma_crt_split_control=fst result,
         comma_crt_split_weight=snd result\<rparr>)"

lemma comma_crt_split_live_leaf_refines:
  assumes left_weight_admitted:
      "comma_crt_mdd_admitted lower left_weight"
    and control_admitted:
      "comma_crt_mdd_admitted lower (right_controls root)"
    and weight_admitted:
      "comma_crt_mdd_admitted lower (right_weights root)"
  shows "comma_crt_split_mdd_result_at phase
      (fst (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf (Comma_CRT_Control_Live root)) left_weight
        right_controls right_weights))
      (snd (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf (Comma_CRT_Control_Live root)) left_weight
        right_controls right_weights)) =
    comma_crt_split_compose_expected_at span
      (Comma_CRT_MDD_Leaf (Comma_CRT_Control_Live root)) left_weight
      right_controls right_weights phase"
proof -
  obtain left_weight_value where left_weight_eval:
    "comma_crt_mdd_eval phase left_weight=Some left_weight_value"
    using comma_crt_mdd_admitted_eval_some[OF left_weight_admitted] by blast
  obtain control where control_eval:
    "comma_crt_mdd_eval (phase+span) (right_controls root)=Some control"
    using comma_crt_mdd_admitted_eval_some[OF control_admitted] by blast
  obtain weight where weight_eval:
    "comma_crt_mdd_eval (phase+span) (right_weights root)=Some weight"
    using comma_crt_mdd_admitted_eval_some[OF weight_admitted] by blast
  have right_result:
    "comma_crt_split_mdd_result_at (phase+span)
      (right_controls root) (right_weights root) =
      Some (comma_crt_result_of_split control weight)"
    using control_eval weight_eval
    by (simp add: comma_crt_split_mdd_result_at_def)
  have left_result:
    "comma_crt_split_mdd_result_at phase
      (Comma_CRT_MDD_Leaf (Comma_CRT_Control_Live root)) left_weight =
      Some (Comma_Semantic_B1_Live root)"
    using left_weight_eval by (simp add: comma_crt_split_mdd_result_at_def)
  have shifted_controls:
    "comma_crt_mdd_eval phase (comma_crt_mdd_shift span (right_controls root)) =
      Some control"
    using control_eval comma_crt_mdd_shift_eval[OF control_admitted, of phase span]
    by simp
  have shifted_weight_diagram_admitted:
    "comma_crt_mdd_admitted lower
      (comma_crt_mdd_shift span (right_weights root))"
    by (rule comma_crt_mdd_shift_admitted[OF weight_admitted])
  have shifted_weight_eval:
    "comma_crt_mdd_eval phase (comma_crt_mdd_shift span (right_weights root)) =
      Some weight"
    using weight_eval comma_crt_mdd_shift_eval[OF weight_admitted, of phase span]
    by simp
  have shifted_weight_map_eval:
    "comma_crt_mdd_eval phase
      (comma_crt_mdd_map (\<lambda>weight. case weight of None \<Rightarrow> None
        | Some D \<Rightarrow> Some (9*span+D))
        (comma_crt_mdd_shift span (right_weights root))) =
      map_option (\<lambda>weight. case weight of None \<Rightarrow> None
        | Some D \<Rightarrow> Some (9*span+D))
        (comma_crt_mdd_eval phase (comma_crt_mdd_shift span (right_weights root)))"
    by (rule comma_crt_mdd_map_eval[OF shifted_weight_diagram_admitted])
  have shifted_weights:
    "comma_crt_mdd_eval phase
      (comma_crt_mdd_weight_after_span span
        (comma_crt_mdd_shift span (right_weights root))) =
      Some (case weight of None \<Rightarrow> None | Some D \<Rightarrow> Some (9*span+D))"
    using shifted_weight_eval shifted_weight_map_eval
    by (simp add: comma_crt_mdd_weight_after_span_def)
  have composed_shape:
    "comma_crt_split_compose_from remaining span
      (Comma_CRT_MDD_Leaf (Comma_CRT_Control_Live root)) left_weight
      right_controls right_weights =
      (comma_crt_mdd_shift span (right_controls root),
       comma_crt_mdd_weight_after_span span
         (comma_crt_mdd_shift span (right_weights root)))"
    by (cases remaining) simp_all
  show ?thesis
    using shifted_controls shifted_weights right_result composed_shape
      left_result
    by (cases weight; cases control)
      (simp_all add: comma_crt_split_mdd_result_at_def
        comma_crt_split_compose_expected_at_def
        comma_semantic_b1_cell_result_def comma_semantic_b1_weight_after_def)
qed

lemma comma_crt_split_stop_leaf_absorbing:
  "comma_crt_split_mdd_result_at phase
      (fst (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop)
        (Comma_CRT_MDD_Leaf (Some D)) right_controls right_weights))
      (snd (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf Comma_CRT_Control_Stop)
        (Comma_CRT_MDD_Leaf (Some D)) right_controls right_weights)) =
    Some (Comma_Semantic_B1_Stop D)"
  by (cases remaining)
    (simp_all add: comma_crt_split_mdd_result_at_def)

lemma comma_crt_split_invalid_leaf_absorbing:
  "comma_crt_split_mdd_result_at phase
      (fst (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid)
        (Comma_CRT_MDD_Leaf None) right_controls right_weights))
      (snd (comma_crt_split_compose_from remaining span
        (Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid)
        (Comma_CRT_MDD_Leaf None) right_controls right_weights)) =
    Some Comma_Semantic_B1_Invalid"
  by (cases remaining)
    (simp_all add: comma_crt_split_mdd_result_at_def)



ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
    comma_crt_mdd_eval_node_selected
    comma_crt_mdd_cofactor_admitted_digit
    comma_crt_mdd_cofactor_or_self_admitted
    comma_crt_mdd_map_admitted
    comma_crt_mdd_weight_after_span_admitted
    comma_crt_split_result_of_source
    comma_crt_split_control_weight_distinguish
    comma_crt_split_live_ignores_weight
    comma_crt_split_invalid_never_stops
    comma_crt_split_live_right_weight_after
    comma_crt_split_stop_weights_fixture
    comma_crt_split_absent_weight_fixture
    comma_crt_split_invalid_weight_fixture
    comma_crt_split_shifted_live_weight_fixture
    comma_crt_mdd_admitted_mono
    comma_crt_mdd_node_admitted
    comma_crt_mdd_node_eval
    comma_crt_mdd_cofactor_exact
    comma_crt_mdd_cofactor_or_self_eval
    comma_crt_mdd_shift_admitted
    comma_crt_mdd_shift_eval
    comma_crt_mdd_admitted_eval_some
    comma_crt_mdd_map_eval
    comma_crt_mdd_shift_all_clock_components
    comma_crt_mdd_shift_period_component
    comma_crt_split_mdd_result_at_of_result
    comma_crt_split_mdd_projection_consistent
    comma_crt_split_live_leaf_refines
    comma_crt_split_stop_leaf_absorbing
    comma_crt_split_invalid_leaf_absorbing
  }) then ()
  else error "Comma_CRT_Split_Power local oracle audit failed"
\<close>
end
