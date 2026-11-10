theory Comma_Continue_Frontier24_Core_Guard
  imports Comma_CRT_MDD Comma_Program_Continue_Guard_Exact
begin

text \<open>
Translate the shared cyclotomic core-value guards into the frontier MDD axis
order (3,4,11,7).  Only the axes used by a core are present.  In particular,
the C7/C13/C21 guards transpose their old C4-then-C3 tree to C3-then-C4.
These small guard diagrams are source-side inputs to the checked MDD arena;
they contain no phase rows or semantic class identifiers.
\<close>

definition comma_frontier24_guard_value_at ::
    "comma_phase_core_id \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_frontier24_guard_value_at core wanted r3 r4 r11 r7 =
    (comma_cyclotomic_clock_core_value
      (comma_core_guard_clock r4 r3 r7 r11)
      (comma_phase_core_modulus core) = wanted)"

definition comma_frontier24_guard_leaf ::
    "comma_phase_core_id \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> bool comma_crt_mdd_node" where
  "comma_frontier24_guard_leaf core wanted r3 r4 r11 r7 =
    Comma_CRT_MDD_Leaf
      (comma_frontier24_guard_value_at core wanted r3 r4 r11 r7)"

definition comma_frontier24_guard_3x4_nodes ::
    "comma_phase_core_id \<Rightarrow> nat \<Rightarrow> bool comma_crt_mdd_node list" where
  "comma_frontier24_guard_3x4_nodes core wanted =
      map (\<lambda>i. comma_frontier24_guard_leaf core wanted
        (i div 4) (i mod 4) 0 0) [0..<12] @
      map (\<lambda>r3. Comma_CRT_MDD_Branch 1
        (map (\<lambda>r4. r3*4+r4) [0..<4])) [0..<3] @
      [Comma_CRT_MDD_Branch 0 (map (\<lambda>r3. 12+r3) [0..<3])]"

definition comma_frontier24_core_guard_nodes ::
    "comma_phase_core_id \<Rightarrow> nat \<Rightarrow> bool comma_crt_mdd_node list" where
  "comma_frontier24_core_guard_nodes core wanted =
    (case core of
       Comma_Core_1 \<Rightarrow>
         [Comma_CRT_MDD_Leaf (wanted=0)]
     | Comma_Core_3 \<Rightarrow>
         [Comma_CRT_MDD_Leaf (wanted=1)]
     | Comma_Core_7 \<Rightarrow>
         comma_frontier24_guard_3x4_nodes Comma_Core_7 wanted
     | Comma_Core_11 \<Rightarrow>
         map (\<lambda>r4. comma_frontier24_guard_leaf Comma_Core_11 wanted
           0 r4 0 0) [0..<4] @
         [Comma_CRT_MDD_Branch 1 (map (\<lambda>r4. r4) [0..<4])]
     | Comma_Core_13 \<Rightarrow>
         comma_frontier24_guard_3x4_nodes Comma_Core_13 wanted
     | Comma_Core_21 \<Rightarrow>
         comma_frontier24_guard_3x4_nodes Comma_Core_21 wanted
     | Comma_Core_23 \<Rightarrow>
         map (\<lambda>i. comma_frontier24_guard_leaf Comma_Core_23 wanted
           0 (i div 11) (i mod 11) 0) [0..<44] @
         map (\<lambda>r4. Comma_CRT_MDD_Branch 2
           (map (\<lambda>r11. r4*11+r11) [0..<11])) [0..<4] @
         [Comma_CRT_MDD_Branch 1 (map (\<lambda>r4. 44+r4) [0..<4])]
     | Comma_Core_27 \<Rightarrow>
         map (\<lambda>r3. comma_frontier24_guard_leaf Comma_Core_27 wanted
           r3 0 0 0) [0..<3] @
         [Comma_CRT_MDD_Branch 0 (map (\<lambda>r3. r3) [0..<3])]
     | Comma_Core_29 \<Rightarrow>
         map (\<lambda>i. comma_frontier24_guard_leaf Comma_Core_29 wanted
           0 (i div 7) 0 (i mod 7)) [0..<28] @
         map (\<lambda>r4. Comma_CRT_MDD_Branch 3
           (map (\<lambda>r7. r4*7+r7) [0..<7])) [0..<4] @
         [Comma_CRT_MDD_Branch 1 (map (\<lambda>r4. 28+r4) [0..<4])])"

fun comma_frontier24_core_guard_root :: "comma_phase_core_id \<Rightarrow> nat" where
  "comma_frontier24_core_guard_root Comma_Core_1 = 0"
| "comma_frontier24_core_guard_root Comma_Core_3 = 0"
| "comma_frontier24_core_guard_root Comma_Core_7 = 15"
| "comma_frontier24_core_guard_root Comma_Core_11 = 4"
| "comma_frontier24_core_guard_root Comma_Core_13 = 15"
| "comma_frontier24_core_guard_root Comma_Core_21 = 15"
| "comma_frontier24_core_guard_root Comma_Core_23 = 48"
| "comma_frontier24_core_guard_root Comma_Core_27 = 3"
| "comma_frontier24_core_guard_root Comma_Core_29 = 32"

definition comma_frontier24_core_guard_value ::
    "comma_phase_core_id \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "comma_frontier24_core_guard_value core wanted coordinate =
    comma_frontier24_guard_value_at core wanted
      (coordinate 0 mod 3) (coordinate 1 mod 4)
      (coordinate 2 mod 11) (coordinate 3 mod 7)"

lemma comma_frontier24_eval_branch_at:
  fixes coordinate :: "nat \<Rightarrow> nat"
  assumes wellformed:
      "comma_crt_mdd_table_wellformed radices nodes"
    and root_bound: "root < length nodes"
    and node: "nodes ! root = Comma_CRT_MDD_Branch axis children"
    and axis_bound: "axis < length radices"
    and positive: "0 < radices ! axis"
    and width: "length children = radices ! axis"
  shows "comma_crt_mdd_eval radices nodes coordinate root =
    comma_crt_mdd_eval radices nodes coordinate
      (children ! (coordinate axis mod radices ! axis))"
proof -
  let ?child = "children ! (coordinate axis mod radices ! axis)"
  have ordered:
      "comma_crt_mdd_node_ordered radices nodes root"
    using wellformed root_bound
    unfolding comma_crt_mdd_table_wellformed_def by blast
  have index_bound: "coordinate axis mod radices ! axis < length children"
    using width positive by (simp add: mod_less_divisor)
  have selected: "?child \<in> set children"
    using index_bound by (rule nth_mem)
  have child_bound: "?child < root"
    using ordered root_bound node selected axis_bound positive width
    by (auto simp: comma_crt_mdd_node_ordered_def)
  have raw:
      "comma_crt_mdd_eval_raw radices nodes coordinate root =
       comma_crt_mdd_eval_raw radices nodes coordinate ?child"
    by (rule comma_crt_mdd_eval_raw_branch[OF root_bound node
        axis_bound positive width _ child_bound]) simp
  show ?thesis
    using wellformed raw
    by (simp only: comma_crt_mdd_eval_def if_True)
qed

lemma comma_frontier24_eval_leaf_at:
  fixes coordinate :: "nat \<Rightarrow> nat"
  assumes wellformed:
      "comma_crt_mdd_table_wellformed radices nodes"
    and root_bound: "root < length nodes"
    and node: "nodes ! root = Comma_CRT_MDD_Leaf value"
  shows "comma_crt_mdd_eval radices nodes coordinate root = Some value"
  using wellformed comma_crt_mdd_eval_raw_leaf[OF root_bound node]
  by (simp only: comma_crt_mdd_eval_def if_True)

lemma comma_frontier24_table_wellformed_iff_list_all:
  "comma_crt_mdd_table_wellformed radices nodes =
    list_all (comma_crt_mdd_node_ordered radices nodes)
      [0..<length nodes]"
  by (auto simp: comma_crt_mdd_table_wellformed_def list_all_iff set_upt)

lemma comma_frontier24_eval_flat_one_axis:
  fixes coordinate :: "nat \<Rightarrow> nat"
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and axis_bound: "axis < length radices"
    and radix: "radices ! axis = width"
    and positive: "0 < width"
    and layout: "nodes = map (\<lambda>i. Comma_CRT_MDD_Leaf (leaf_value i))
        [0..<width] @ [Comma_CRT_MDD_Branch axis (map (\<lambda>i. i) [0..<width])]"
  shows "comma_crt_mdd_eval radices nodes coordinate width =
    Some (leaf_value (coordinate axis mod width))"
proof -
  let ?selected = "coordinate axis mod width"
  have selected_bound: "?selected < width"
    using positive by simp
  have root_bound: "width < length nodes"
    using layout by (simp add: nth_append)
  have root_node:
    "nodes ! width = Comma_CRT_MDD_Branch axis (map (\<lambda>i. i) [0..<width])"
    using layout by (simp add: nth_append)
  have root_step_raw:
    "comma_crt_mdd_eval radices nodes coordinate width =
      comma_crt_mdd_eval radices nodes coordinate
        (map (\<lambda>i. i) [0..<width] !
          (coordinate axis mod radices ! axis))"
    by (rule comma_frontier24_eval_branch_at[OF wellformed root_bound root_node])
       (use axis_bound radix positive in simp_all)
  have root_step:
    "comma_crt_mdd_eval radices nodes coordinate width =
      comma_crt_mdd_eval radices nodes coordinate
        (map (\<lambda>i. i) [0..<width] ! ?selected)"
    using root_step_raw radix by simp
  have index:
    "map (\<lambda>i. i) [0..<width] ! ?selected = ?selected"
    using selected_bound by simp
  have leaf_node:
    "nodes ! ?selected = Comma_CRT_MDD_Leaf (leaf_value ?selected)"
    using layout selected_bound by (simp add: nth_append)
  have leaf_step:
    "comma_crt_mdd_eval radices nodes coordinate ?selected =
       Some (leaf_value ?selected)"
    by (rule comma_frontier24_eval_leaf_at[OF wellformed])
       (use layout selected_bound leaf_node in simp_all)
  show ?thesis using root_step index leaf_step by simp
qed

lemma comma_frontier24_eval_flat_two_axes:
  fixes coordinate :: "nat \<Rightarrow> nat"
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and outer_axis_bound: "outer_axis < length radices"
    and inner_axis_bound: "inner_axis < length radices"
    and outer_radix: "radices ! outer_axis = outer_width"
    and inner_radix: "radices ! inner_axis = inner_width"
    and outer_positive: "0 < outer_width"
    and inner_positive: "0 < inner_width"
    and layout:
      "nodes =
        map (\<lambda>i. Comma_CRT_MDD_Leaf
          (leaf_value (i div inner_width) (i mod inner_width)))
          [0..<outer_width * inner_width] @
        map (\<lambda>i. Comma_CRT_MDD_Branch inner_axis
          (map (\<lambda>j. i * inner_width + j) [0..<inner_width]))
          [0..<outer_width] @
        [Comma_CRT_MDD_Branch outer_axis
          (map (\<lambda>i. outer_width * inner_width + i) [0..<outer_width])]"
  shows "comma_crt_mdd_eval radices nodes coordinate
      (outer_width * inner_width + outer_width) =
    Some (leaf_value (coordinate outer_axis mod outer_width)
      (coordinate inner_axis mod inner_width))"
proof -
  let ?outer = "coordinate outer_axis mod outer_width"
  let ?inner = "coordinate inner_axis mod inner_width"
  let ?root = "outer_width * inner_width + outer_width"
  let ?middle = "outer_width * inner_width + ?outer"
  let ?leaf = "?outer * inner_width + ?inner"
  have outer_bound: "?outer < outer_width"
    using outer_positive by simp
  have inner_bound: "?inner < inner_width"
    using inner_positive by simp
  have root_bound: "?root < length nodes"
    using layout by simp
  have root_node:
    "nodes ! ?root = Comma_CRT_MDD_Branch outer_axis
      (map (\<lambda>i. outer_width * inner_width + i) [0..<outer_width])"
    using layout by (simp add: nth_append)
  have root_step_raw:
    "comma_crt_mdd_eval radices nodes coordinate ?root =
      comma_crt_mdd_eval radices nodes coordinate
        (map (\<lambda>i. outer_width * inner_width + i) [0..<outer_width] !
          (coordinate outer_axis mod radices ! outer_axis))"
    by (rule comma_frontier24_eval_branch_at[OF wellformed root_bound root_node])
       (use outer_axis_bound outer_radix outer_positive in simp_all)
  have root_step:
    "comma_crt_mdd_eval radices nodes coordinate ?root =
      comma_crt_mdd_eval radices nodes coordinate
        (map (\<lambda>i. outer_width * inner_width + i) [0..<outer_width] ! ?outer)"
    using root_step_raw outer_radix by simp
  have root_index:
    "map (\<lambda>i. outer_width * inner_width + i) [0..<outer_width] ! ?outer = ?middle"
    using outer_bound by simp
  have middle_bound: "?middle < length nodes"
    using layout outer_bound by simp
  have middle_node:
    "nodes ! ?middle = Comma_CRT_MDD_Branch inner_axis
      (map (\<lambda>j. ?outer * inner_width + j) [0..<inner_width])"
    using layout outer_bound by (simp add: nth_append)
  have middle_step_raw:
    "comma_crt_mdd_eval radices nodes coordinate ?middle =
      comma_crt_mdd_eval radices nodes coordinate
        (map (\<lambda>j. ?outer * inner_width + j) [0..<inner_width] !
          (coordinate inner_axis mod radices ! inner_axis))"
    by (rule comma_frontier24_eval_branch_at[OF wellformed middle_bound middle_node])
       (use inner_axis_bound inner_radix inner_positive in simp_all)
  have middle_step:
    "comma_crt_mdd_eval radices nodes coordinate ?middle =
      comma_crt_mdd_eval radices nodes coordinate
        (map (\<lambda>j. ?outer * inner_width + j) [0..<inner_width] ! ?inner)"
    using middle_step_raw inner_radix by simp
  have middle_index:
    "map (\<lambda>j. ?outer * inner_width + j) [0..<inner_width] ! ?inner = ?leaf"
    using inner_bound by simp
  have successor_bound: "Suc ?outer \<le> outer_width"
    using outer_bound by simp
  have scaled_outer: "Suc ?outer * inner_width \<le> outer_width * inner_width"
    by (rule mult_le_mono1[OF successor_bound])
  have leaf_bound: "?leaf < outer_width * inner_width"
    using inner_bound scaled_outer by (simp; arith)
  have leaf_node:
    "nodes ! ?leaf = Comma_CRT_MDD_Leaf
      (leaf_value (?leaf div inner_width) (?leaf mod inner_width))"
    using layout leaf_bound by (simp add: nth_append)
  have leaf_step:
    "comma_crt_mdd_eval radices nodes coordinate ?leaf =
      Some (leaf_value (?leaf div inner_width) (?leaf mod inner_width))"
    by (rule comma_frontier24_eval_leaf_at[OF wellformed])
       (use layout leaf_bound leaf_node in simp_all)
  have div_mod:
    "?leaf div inner_width = ?outer"
    "?leaf mod inner_width = ?inner"
    using inner_bound inner_positive
    by (simp_all add: div_add1_eq mod_add_eq)
  show ?thesis
    using root_step root_index middle_step middle_index leaf_step div_mod by simp
qed

lemma comma_frontier24_core_guard_nodes_wellformed:
  "comma_crt_mdd_table_wellformed [3,4,11,7]
    (comma_frontier24_core_guard_nodes core wanted)"
  unfolding comma_frontier24_table_wellformed_iff_list_all
  by (cases core)
    (simp_all add: comma_frontier24_core_guard_nodes_def
      comma_frontier24_guard_3x4_nodes_def comma_frontier24_guard_leaf_def
      comma_crt_mdd_node_ordered_def list_all_Cons_iff list_all_Nil_iff
      upt_conv_Cons)

lemma comma_frontier24_core_guard_eval:
  fixes coordinate :: "nat \<Rightarrow> nat"
  shows "comma_crt_mdd_eval [3,4,11,7]
      (comma_frontier24_core_guard_nodes core wanted) coordinate
      (comma_frontier24_core_guard_root core) =
    Some (comma_frontier24_core_guard_value core wanted coordinate)"
proof -
  have wellformed:
    "comma_crt_mdd_table_wellformed [3,4,11,7]
      (comma_frontier24_core_guard_nodes core wanted)"
    by (rule comma_frontier24_core_guard_nodes_wellformed)
  have one: "comma_recursive_core_residue 1 t = 0" for t
    by (simp add: comma_recursive_core_residue_def)
  have three: "comma_recursive_core_residue 3 t = 1" for t
    by (simp add: comma_recursive_core_residue_def)
  show ?thesis
  proof (cases core)
    case Comma_Core_1
    have root_bound: "0 < length (comma_frontier24_core_guard_nodes Comma_Core_1 wanted)"
      by (simp add: comma_frontier24_core_guard_nodes_def)
    have leaf:
      "comma_frontier24_core_guard_nodes Comma_Core_1 wanted ! 0 =
        Comma_CRT_MDD_Leaf (wanted=0)"
      by (simp add: comma_frontier24_core_guard_nodes_def)
    have result:
      "comma_crt_mdd_eval [3,4,11,7]
        (comma_frontier24_core_guard_nodes Comma_Core_1 wanted)
        coordinate 0 = Some (wanted=0)"
      by (rule comma_frontier24_eval_leaf_at[OF
        comma_frontier24_core_guard_nodes_wellformed[of Comma_Core_1 wanted]
        root_bound leaf])
    show ?thesis using result Comma_Core_1 one
      by (simp add: comma_frontier24_core_guard_root.simps
          comma_frontier24_guard_value_at_def
          comma_frontier24_core_guard_value_def
          comma_cyclotomic_clock_core_value_def comma_phase_core_modulus.simps
          comma_core_period_def comma_cyclotomic_phase_def)
  next
    case Comma_Core_3
    have root_bound: "0 < length (comma_frontier24_core_guard_nodes Comma_Core_3 wanted)"
      by (simp add: comma_frontier24_core_guard_nodes_def)
    have leaf:
      "comma_frontier24_core_guard_nodes Comma_Core_3 wanted ! 0 =
        Comma_CRT_MDD_Leaf (wanted=1)"
      by (simp add: comma_frontier24_core_guard_nodes_def)
    have result:
      "comma_crt_mdd_eval [3,4,11,7]
        (comma_frontier24_core_guard_nodes Comma_Core_3 wanted)
        coordinate 0 = Some (wanted=1)"
      by (rule comma_frontier24_eval_leaf_at[OF
        comma_frontier24_core_guard_nodes_wellformed[of Comma_Core_3 wanted]
        root_bound leaf])
    show ?thesis using result Comma_Core_3 three
      by (simp add: eq_commute comma_frontier24_core_guard_root.simps
          comma_frontier24_guard_value_at_def
          comma_frontier24_core_guard_value_def
          comma_cyclotomic_clock_core_value_def comma_phase_core_modulus.simps
          comma_core_period_def comma_cyclotomic_phase_def)
  next
    case Comma_Core_7
    have result:
      "comma_crt_mdd_eval [3,4,11,7]
        (comma_frontier24_core_guard_nodes Comma_Core_7 wanted)
        coordinate 15 = Some (comma_frontier24_guard_value_at Comma_Core_7 wanted
          (coordinate 0 mod 3) (coordinate 1 mod 4) 0 0)"
      using comma_frontier24_eval_flat_two_axes[where radices="[3,4,11,7]"
          and nodes="comma_frontier24_core_guard_nodes Comma_Core_7 wanted"
          and coordinate=coordinate and
          outer_axis=0 and inner_axis=1 and outer_width=3 and inner_width=4
          and leaf_value="\<lambda>r3 r4. comma_frontier24_guard_value_at
            Comma_Core_7 wanted r3 r4 0 0", OF
          comma_frontier24_core_guard_nodes_wellformed[of Comma_Core_7 wanted]]
      by (simp add: comma_frontier24_core_guard_nodes_wellformed
          comma_frontier24_core_guard_nodes_def
          comma_frontier24_guard_3x4_nodes_def comma_frontier24_guard_leaf_def)
    show ?thesis using result Comma_Core_7
      by (simp add: comma_frontier24_core_guard_root.simps
          comma_frontier24_guard_value_at_def
          comma_frontier24_core_guard_value_def comma_frontier24_guard_leaf_def
          comma_core_guard_clock_def comma_cyclotomic_clock_core_value_def
          comma_phase_core_modulus.simps comma_core_period_def comma_cyclotomic_phase_def)
  next
    case Comma_Core_11
    have result:
      "comma_crt_mdd_eval [3,4,11,7]
        (comma_frontier24_core_guard_nodes Comma_Core_11 wanted)
        coordinate 4 = Some (comma_frontier24_guard_value_at Comma_Core_11 wanted
          0 (coordinate 1 mod 4) 0 0)"
      using comma_frontier24_eval_flat_one_axis[where radices="[3,4,11,7]"
          and nodes="comma_frontier24_core_guard_nodes Comma_Core_11 wanted"
          and coordinate=coordinate and axis=1 and width=4
          and leaf_value="\<lambda>r4. comma_frontier24_guard_value_at
            Comma_Core_11 wanted 0 r4 0 0", OF
          comma_frontier24_core_guard_nodes_wellformed[of Comma_Core_11 wanted]]
      by (simp add: comma_frontier24_core_guard_nodes_def
          comma_frontier24_guard_leaf_def)
    show ?thesis using result Comma_Core_11
      by (simp add: comma_frontier24_core_guard_root.simps
          comma_frontier24_guard_value_at_def
          comma_frontier24_core_guard_value_def comma_frontier24_guard_leaf_def
          comma_core_guard_clock_def comma_cyclotomic_clock_core_value_def
          comma_phase_core_modulus.simps comma_core_period_def comma_cyclotomic_phase_def)
  next
    case Comma_Core_13
    have result:
      "comma_crt_mdd_eval [3,4,11,7]
        (comma_frontier24_core_guard_nodes Comma_Core_13 wanted)
        coordinate 15 = Some (comma_frontier24_guard_value_at Comma_Core_13 wanted
          (coordinate 0 mod 3) (coordinate 1 mod 4) 0 0)"
      using comma_frontier24_eval_flat_two_axes[where radices="[3,4,11,7]"
          and nodes="comma_frontier24_core_guard_nodes Comma_Core_13 wanted"
          and coordinate=coordinate and
          outer_axis=0 and inner_axis=1 and outer_width=3 and inner_width=4
          and leaf_value="\<lambda>r3 r4. comma_frontier24_guard_value_at
            Comma_Core_13 wanted r3 r4 0 0", OF
          comma_frontier24_core_guard_nodes_wellformed[of Comma_Core_13 wanted]]
      by (simp add: comma_frontier24_core_guard_nodes_wellformed
          comma_frontier24_core_guard_nodes_def
          comma_frontier24_guard_3x4_nodes_def comma_frontier24_guard_leaf_def)
    show ?thesis using result Comma_Core_13
      by (simp add: comma_frontier24_core_guard_root.simps
          comma_frontier24_guard_value_at_def
          comma_frontier24_core_guard_value_def comma_frontier24_guard_leaf_def
          comma_core_guard_clock_def comma_cyclotomic_clock_core_value_def
          comma_phase_core_modulus.simps comma_core_period_def comma_cyclotomic_phase_def)
  next
    case Comma_Core_21
    have result:
      "comma_crt_mdd_eval [3,4,11,7]
        (comma_frontier24_core_guard_nodes Comma_Core_21 wanted)
        coordinate 15 = Some (comma_frontier24_guard_value_at Comma_Core_21 wanted
          (coordinate 0 mod 3) (coordinate 1 mod 4) 0 0)"
      using comma_frontier24_eval_flat_two_axes[where radices="[3,4,11,7]"
          and nodes="comma_frontier24_core_guard_nodes Comma_Core_21 wanted"
          and coordinate=coordinate and
          outer_axis=0 and inner_axis=1 and outer_width=3 and inner_width=4
          and leaf_value="\<lambda>r3 r4. comma_frontier24_guard_value_at
            Comma_Core_21 wanted r3 r4 0 0", OF
          comma_frontier24_core_guard_nodes_wellformed[of Comma_Core_21 wanted]]
      by (simp add: comma_frontier24_core_guard_nodes_wellformed
          comma_frontier24_core_guard_nodes_def
          comma_frontier24_guard_3x4_nodes_def comma_frontier24_guard_leaf_def)
    show ?thesis using result Comma_Core_21
      by (simp add: comma_frontier24_core_guard_root.simps
          comma_frontier24_guard_value_at_def
          comma_frontier24_core_guard_value_def comma_frontier24_guard_leaf_def
          comma_core_guard_clock_def comma_cyclotomic_clock_core_value_def
          comma_phase_core_modulus.simps comma_core_period_def comma_cyclotomic_phase_def)
  next
    case Comma_Core_23
    have result:
      "comma_crt_mdd_eval [3,4,11,7]
        (comma_frontier24_core_guard_nodes Comma_Core_23 wanted)
        coordinate 48 = Some (comma_frontier24_guard_value_at Comma_Core_23 wanted
          0 (coordinate 1 mod 4) (coordinate 2 mod 11) 0)"
      using comma_frontier24_eval_flat_two_axes[where radices="[3,4,11,7]"
          and nodes="comma_frontier24_core_guard_nodes Comma_Core_23 wanted"
          and coordinate=coordinate and
          outer_axis=1 and inner_axis=2 and outer_width=4 and inner_width=11
          and leaf_value="\<lambda>r4 r11. comma_frontier24_guard_value_at
            Comma_Core_23 wanted 0 r4 r11 0", OF
          comma_frontier24_core_guard_nodes_wellformed[of Comma_Core_23 wanted]]
      by (simp add: comma_frontier24_core_guard_nodes_wellformed
          comma_frontier24_core_guard_nodes_def
          comma_frontier24_guard_leaf_def)
    show ?thesis using result Comma_Core_23
      by (simp add: comma_frontier24_core_guard_root.simps
          comma_frontier24_guard_value_at_def
          comma_frontier24_core_guard_value_def comma_frontier24_guard_leaf_def
          comma_core_guard_clock_def comma_cyclotomic_clock_core_value_def
          comma_phase_core_modulus.simps comma_core_period_def comma_cyclotomic_phase_def)
  next
    case Comma_Core_27
    have result:
      "comma_crt_mdd_eval [3,4,11,7]
        (comma_frontier24_core_guard_nodes Comma_Core_27 wanted)
        coordinate 3 = Some (comma_frontier24_guard_value_at Comma_Core_27 wanted
          (coordinate 0 mod 3) 0 0 0)"
      using comma_frontier24_eval_flat_one_axis[where radices="[3,4,11,7]"
          and nodes="comma_frontier24_core_guard_nodes Comma_Core_27 wanted"
          and coordinate=coordinate and axis=0 and width=3
          and leaf_value="\<lambda>r3. comma_frontier24_guard_value_at
            Comma_Core_27 wanted r3 0 0 0", OF
          comma_frontier24_core_guard_nodes_wellformed[of Comma_Core_27 wanted]]
      by (simp add: comma_frontier24_core_guard_nodes_def
          comma_frontier24_guard_leaf_def)
    show ?thesis using result Comma_Core_27
      by (simp add: comma_frontier24_core_guard_root.simps
          comma_frontier24_guard_value_at_def
          comma_frontier24_core_guard_value_def comma_frontier24_guard_leaf_def
          comma_core_guard_clock_def comma_cyclotomic_clock_core_value_def
          comma_phase_core_modulus.simps comma_core_period_def comma_cyclotomic_phase_def)
  next
    case Comma_Core_29
    have result:
      "comma_crt_mdd_eval [3,4,11,7]
        (comma_frontier24_core_guard_nodes Comma_Core_29 wanted)
        coordinate 32 = Some (comma_frontier24_guard_value_at Comma_Core_29 wanted
          0 (coordinate 1 mod 4) 0 (coordinate 3 mod 7))"
      using comma_frontier24_eval_flat_two_axes[where radices="[3,4,11,7]"
          and nodes="comma_frontier24_core_guard_nodes Comma_Core_29 wanted"
          and coordinate=coordinate and
          outer_axis=1 and inner_axis=3 and outer_width=4 and inner_width=7
          and leaf_value="\<lambda>r4 r7. comma_frontier24_guard_value_at
            Comma_Core_29 wanted 0 r4 0 r7", OF
          comma_frontier24_core_guard_nodes_wellformed[of Comma_Core_29 wanted]]
      by (simp add: comma_frontier24_core_guard_nodes_wellformed
          comma_frontier24_core_guard_nodes_def
          comma_frontier24_guard_leaf_def)
    show ?thesis using result Comma_Core_29
      by (simp add: comma_frontier24_core_guard_root.simps
          comma_frontier24_guard_value_at_def
          comma_frontier24_core_guard_value_def comma_frontier24_guard_leaf_def
          comma_core_guard_clock_def comma_cyclotomic_clock_core_value_def
          comma_phase_core_modulus.simps comma_core_period_def comma_cyclotomic_phase_def)
  qed
qed

lemma comma_frontier24_core_guard_phase_eval:
  "comma_crt_mdd_eval_phase [3,4,11,7]
      (comma_frontier24_core_guard_nodes core wanted) phase
      (comma_frontier24_core_guard_root core) =
    Some (comma_crt_eval phase (comma_core_value_guard core wanted))"
proof -
  have exact: "comma_crt_mdd_eval [3,4,11,7]
      (comma_frontier24_core_guard_nodes core wanted) (\<lambda>axis. phase)
      (comma_frontier24_core_guard_root core) =
      Some (comma_frontier24_core_guard_value core wanted (\<lambda>axis. phase))"
    by (rule comma_frontier24_core_guard_eval)
  show ?thesis
    using exact
    by (simp add: comma_crt_mdd_eval_phase_def
        comma_frontier24_core_guard_value_def comma_frontier24_guard_value_at_def
        comma_core_value_guard_eval
        comma_core_guard_clock_def comma_cyclotomic_clock_of_def)
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "frontier24 active-axis core guard MDD translation"
    @{thms comma_frontier24_core_guard_nodes_wellformed
      comma_frontier24_core_guard_eval comma_frontier24_core_guard_phase_eval}
\<close>

end
