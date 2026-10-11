theory Comma_Semantic_B1_CRT_Structural_Partition
  imports Comma_Semantic_B1_CRT_Occurrence_Fold
begin

text \<open>
Partition certificates follow the constructor.  This layer states the
set-level facts used by the ColumnCID checker: source slot cylinders partition
the external clock; lifting every cell of a child partition into one slot
partitions that slot; grouping disjoint cells by their result preserves the
partition; and a common clock rebase preserves a partition.  These facts do
not build a prefix OR accumulator over published template columns.
\<close>

definition comma_semantic_b1_crt_slot_cylinder ::
    "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "comma_semantic_b1_crt_slot_cylinder period slot =
    {phase. phase<924 \<and> phase mod period=slot}"

definition comma_semantic_b1_crt_slot_cells :: "nat \<Rightarrow> nat set list" where
  "comma_semantic_b1_crt_slot_cells period =
    map (comma_semantic_b1_crt_slot_cylinder period) [0..<period]"

definition comma_semantic_b1_crt_rebase_set :: "nat \<Rightarrow> nat set \<Rightarrow> nat set" where
  "comma_semantic_b1_crt_rebase_set shift cells =
    {phase. phase<924 \<and> (phase+shift) mod 924 \<in> cells}"
lemma comma_semantic_b1_crt_distinct_concat_tagged_rows:
  fixes slots :: "'s::equal list"
    and rows :: "'s \<Rightarrow> ('s \<times> 'a::equal) list"
  assumes slots_distinct: "distinct slots"
    and rows_distinct: "\<And>slot. slot \<in> set slots \<Longrightarrow> distinct (rows slot)"
    and tagged: "\<And>slot entry. slot \<in> set slots \<Longrightarrow>
      entry \<in> set (rows slot) \<Longrightarrow> fst entry=slot"
  shows "distinct (concat (map rows slots))"
proof -
  have general:
    "\<And>xs. distinct xs \<Longrightarrow>
      (\<forall>slot\<in>set xs. distinct (rows slot)) \<Longrightarrow>
      (\<forall>slot\<in>set xs. \<forall>entry\<in>set (rows slot). fst entry=slot) \<Longrightarrow>
      distinct (concat (map rows xs))"
  proof -
    fix xs
    show "distinct xs \<Longrightarrow>
        (\<forall>slot\<in>set xs. distinct (rows slot)) \<Longrightarrow>
        (\<forall>slot\<in>set xs. \<forall>entry\<in>set (rows slot). fst entry=slot) \<Longrightarrow>
        distinct (concat (map rows xs))"
    proof (induction xs)
      case Nil
      then show ?case by simp
    next
      case (Cons slot slots)
      have slots_distinct: "distinct slots" using Cons.prems(1) by simp
      have tail_rows_distinct:
        "\<forall>other\<in>set slots. distinct (rows other)"
        using Cons.prems(2) by auto
      have tail_tagged:
        "\<forall>other\<in>set slots. \<forall>entry\<in>set (rows other). fst entry=other"
        using Cons.prems(3) by auto
      have tail_distinct: "distinct (concat (map rows slots))"
        by (rule Cons.IH[OF slots_distinct tail_rows_distinct tail_tagged])
      have head_distinct: "distinct (rows slot)"
        using Cons.prems(2) by auto
      have slot_notin: "slot \<notin> set slots" using Cons.prems(1) by simp
      have head_disjoint:
        "set (rows slot) \<inter> set (concat (map rows slots)) = {}"
        using Cons.prems(3) slot_notin by (auto simp: set_concat; fastforce)
      show ?case using head_distinct tail_distinct head_disjoint by simp
    qed
  qed
  show ?thesis
    by (rule general[OF slots_distinct]) (use rows_distinct tagged in auto)
qed

lemma comma_semantic_b1_crt_rebase_nonempty:
  assumes shift: "shift<924" and cells: "cells\<noteq>{}"
    and bounded: "cells\<subseteq>{..<924}"
  shows "comma_semantic_b1_crt_rebase_set shift cells\<noteq>{}"
proof -
  obtain phase where phase: "phase\<in>cells" using cells by blast
  have selected_bound: "phase<924" using bounded phase by blast
  let ?source="(phase+(924-shift)) mod 924"
  have source_bound: "?source<924" by simp
  have inverse: "(?source+shift) mod 924=phase"
  proof -
    have "(?source+shift) mod 924 =
      (phase+(924-shift)+shift) mod 924"
      by (simp add: mod_add_left_eq)
    also have "... = phase" using selected_bound shift
      by (simp add: add.assoc)
    finally show ?thesis .
  qed
  have "?source\<in>comma_semantic_b1_crt_rebase_set shift cells"
    using phase source_bound inverse
    by (auto simp: comma_semantic_b1_crt_rebase_set_def)
  then show ?thesis by blast
qed
lemma comma_semantic_b1_crt_list_all_upt_index:
  assumes all: "list_all P [0..<n]" and index: "i<n"
  shows "P i"
  using all index by (auto simp: list_all_iff)

definition comma_semantic_b1_crt_lift_cells ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set list \<Rightarrow> nat set list" where
  "comma_semantic_b1_crt_lift_cells period slot shift child_cells =
    map (\<lambda>cell. comma_semantic_b1_crt_slot_cylinder period slot \<inter>
      {phase. phase<924 \<and> (phase+shift) mod 924 \<in> cell}) child_cells"

definition comma_semantic_b1_crt_group_support ::
    "'a list \<Rightarrow> nat set list \<Rightarrow> 'a \<Rightarrow> nat set" where
  "comma_semantic_b1_crt_group_support labels cells result =
    {phase. \<exists>i<length cells. labels!i=result \<and> phase\<in>cells!i}"

definition comma_semantic_b1_crt_group_supports ::
    "'a list \<Rightarrow> nat set list \<Rightarrow> 'a list \<Rightarrow> nat set list" where
  "comma_semantic_b1_crt_group_supports labels cells results =
    map (comma_semantic_b1_crt_group_support labels cells) results"

lemma comma_semantic_b1_crt_slot_cells_partition:
  assumes period: "0<period"
  shows "comma_semantic_b1_crt_cells_partition {..<924}
    (comma_semantic_b1_crt_slot_cells period)"
proof -
  have length_slots:
      "length (comma_semantic_b1_crt_slot_cells period)=period"
    by (simp add: comma_semantic_b1_crt_slot_cells_def)
  have bounded:
      "\<forall>i<length (comma_semantic_b1_crt_slot_cells period).
        comma_semantic_b1_crt_slot_cells period ! i \<subseteq> {..<924}"
  proof (intro allI impI)
    fix i
    assume i: "i<length (comma_semantic_b1_crt_slot_cells period)"
    have i': "i<period" using i length_slots by simp
    show "comma_semantic_b1_crt_slot_cells period ! i \<subseteq> {..<924}"
      using i' by (auto simp: comma_semantic_b1_crt_slot_cells_def
        comma_semantic_b1_crt_slot_cylinder_def)
  qed
  have covered:
      "\<forall>phase\<in>{..<924}. \<exists>i<length (comma_semantic_b1_crt_slot_cells period).
        phase\<in>comma_semantic_b1_crt_slot_cells period ! i"
  proof (intro ballI)
    fix phase :: nat
    assume phase: "phase\<in>{..<924}"
    have residue: "phase mod period < period"
      using mod_less_divisor[OF period, of phase] .
    have in_slot:
        "phase\<in>comma_semantic_b1_crt_slot_cylinder period (phase mod period)"
      using phase by (simp add: comma_semantic_b1_crt_slot_cylinder_def)
    have residue_bound:
        "phase mod period < length (comma_semantic_b1_crt_slot_cells period)"
      using residue length_slots by simp
    have residue_cell:
        "comma_semantic_b1_crt_slot_cells period ! (phase mod period) =
          comma_semantic_b1_crt_slot_cylinder period (phase mod period)"
      using residue by (simp add: comma_semantic_b1_crt_slot_cells_def)
    show "\<exists>i<length (comma_semantic_b1_crt_slot_cells period).
        phase\<in>comma_semantic_b1_crt_slot_cells period ! i"
      using residue_bound in_slot residue_cell by blast
  qed
  have pairwise:
      "\<forall>i<length (comma_semantic_b1_crt_slot_cells period).
       \<forall>j<length (comma_semantic_b1_crt_slot_cells period).
         i\<noteq>j \<longrightarrow>
         comma_semantic_b1_crt_slot_cells period ! i \<inter>
           comma_semantic_b1_crt_slot_cells period ! j = {}"
  proof (intro allI impI allI impI impI)
    fix i j
    assume i: "i<length (comma_semantic_b1_crt_slot_cells period)"
      and j: "j<length (comma_semantic_b1_crt_slot_cells period)"
      and different: "i\<noteq>j"
    have i': "i<period" and j': "j<period"
      using i j length_slots by simp_all
    show "comma_semantic_b1_crt_slot_cells period ! i \<inter>
        comma_semantic_b1_crt_slot_cells period ! j = {}"
      using i' j' different
      by (auto simp: comma_semantic_b1_crt_slot_cells_def
        comma_semantic_b1_crt_slot_cylinder_def)
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_cells_partition_def
    using bounded covered pairwise by blast
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_slot_cells_partition}]; Comma_Proof_Profile.report "Structural partition: slot cells checked"\<close>

lemma comma_semantic_b1_crt_partition_append_disjoint:
  assumes left_partition:
      "comma_semantic_b1_crt_cells_partition left_universe left_cells"
    and right_partition:
      "comma_semantic_b1_crt_cells_partition right_universe right_cells"
    and universes_disjoint: "left_universe \<inter> right_universe = {}"
  shows "comma_semantic_b1_crt_cells_partition
    (left_universe \<union> right_universe) (left_cells @ right_cells)"
proof -
  have left_bounded:
      "\<forall>i<length left_cells. left_cells!i\<subseteq>left_universe"
    and left_covered:
      "\<forall>phase\<in>left_universe. \<exists>i<length left_cells. phase\<in>left_cells!i"
    and left_disjoint:
      "\<forall>i<length left_cells. \<forall>j<length left_cells.
        i\<noteq>j \<longrightarrow> left_cells!i\<inter>left_cells!j={}"
    using left_partition by (auto simp: comma_semantic_b1_crt_cells_partition_def)
  have right_bounded:
      "\<forall>i<length right_cells. right_cells!i\<subseteq>right_universe"
    and right_covered:
      "\<forall>phase\<in>right_universe. \<exists>i<length right_cells. phase\<in>right_cells!i"
    and right_disjoint:
      "\<forall>i<length right_cells. \<forall>j<length right_cells.
        i\<noteq>j \<longrightarrow> right_cells!i\<inter>right_cells!j={}"
    using right_partition by (auto simp: comma_semantic_b1_crt_cells_partition_def)
  have appended_bounded:
      "\<forall>i<length (left_cells@right_cells).
        (left_cells@right_cells)!i \<subseteq> left_universe\<union>right_universe"
  proof (intro allI impI)
    fix i
    assume i_bound: "i<length (left_cells@right_cells)"
    show "(left_cells@right_cells)!i \<subseteq> left_universe\<union>right_universe"
    proof (cases "i<length left_cells")
      case True
      have source_bound: "left_cells!i\<subseteq>left_universe"
        by (rule left_bounded[rule_format, OF True])
      have appended_index: "(left_cells@right_cells)!i=left_cells!i"
        using True by (simp add: nth_append)
      show ?thesis using source_bound appended_index by blast
    next
      case False
      have right_index: "i-length left_cells<length right_cells"
        using i_bound False by simp
      have source_bound:
          "right_cells!(i-length left_cells)\<subseteq>right_universe"
        by (rule right_bounded[rule_format, OF right_index])
      have appended_index: "(left_cells@right_cells)!i=right_cells!(i-length left_cells)"
        using False by (simp add: nth_append)
      show ?thesis using source_bound appended_index by blast
    qed
  qed
  have appended_covered:
      "\<forall>phase\<in>left_universe\<union>right_universe.
        \<exists>i<length (left_cells@right_cells). phase\<in>(left_cells@right_cells)!i"
  proof (intro ballI)
    fix phase
    assume phase: "phase\<in>left_universe\<union>right_universe"
    show "\<exists>i<length (left_cells@right_cells). phase\<in>(left_cells@right_cells)!i"
    proof (cases "phase\<in>left_universe")
      case True
      obtain i where i_bound: "i<length left_cells" and member: "phase\<in>left_cells!i"
        using left_covered True by blast
      show ?thesis
      proof (rule exI[of _ i])
        show "i<length (left_cells@right_cells) \<and>
            phase\<in>(left_cells@right_cells)!i"
          using i_bound member by (simp add: nth_append)
      qed
    next
      case False
      have in_right: "phase\<in>right_universe" using phase False by blast
      obtain j where j_bound: "j<length right_cells" and member: "phase\<in>right_cells!j"
        using right_covered in_right by blast
      let ?index = "length left_cells+j"
      show ?thesis
      proof (rule exI[of _ ?index])
        show "?index<length (left_cells@right_cells) \<and>
            phase\<in>(left_cells@right_cells)!?index"
          using j_bound member by simp
      qed
    qed
  qed
  have appended_disjoint:
      "\<forall>i<length (left_cells@right_cells).
       \<forall>j<length (left_cells@right_cells).
         i\<noteq>j \<longrightarrow>
         (left_cells@right_cells)!i\<inter>(left_cells@right_cells)!j={}"
  proof (intro allI impI allI impI impI)
    fix i j
    assume i_bound: "i<length (left_cells@right_cells)"
      and j_bound: "j<length (left_cells@right_cells)"
      and different: "i\<noteq>j"
    show "(left_cells@right_cells)!i\<inter>(left_cells@right_cells)!j={}"
    proof (cases "i<length left_cells")
      case i_left: True
      show ?thesis
      proof (cases "j<length left_cells")
        case j_left: True
        have source_disjoint: "left_cells!i\<inter>left_cells!j={}"
          by (rule left_disjoint[rule_format, OF i_left j_left different])
        show ?thesis using source_disjoint i_left j_left by (simp add: nth_append)
      next
        case j_right: False
        have left_piece: "(left_cells@right_cells)!i\<subseteq>left_universe"
          using left_bounded[rule_format, OF i_left] i_left by (simp add: nth_append)
        have right_index: "j-length left_cells<length right_cells"
          using j_bound j_right by simp
        have right_piece:
            "(left_cells@right_cells)!j\<subseteq>right_universe"
          using right_bounded[rule_format, OF right_index] j_right
          by (simp add: nth_append)
        show ?thesis using left_piece right_piece universes_disjoint by blast
      qed
    next
      case i_right: False
      have i_index: "i-length left_cells<length right_cells"
        using i_bound i_right by simp
      show ?thesis
      proof (cases "j<length left_cells")
        case j_left: True
        have left_piece: "(left_cells@right_cells)!j\<subseteq>left_universe"
          using left_bounded[rule_format, OF j_left] j_left by (simp add: nth_append)
        have right_piece:
            "(left_cells@right_cells)!i\<subseteq>right_universe"
          using right_bounded[rule_format, OF i_index] i_right
          by (simp add: nth_append)
        show ?thesis using left_piece right_piece universes_disjoint by blast
      next
        case j_right: False
        have j_index: "j-length left_cells<length right_cells"
          using j_bound j_right by simp
        have indices_differ: "i-length left_cells\<noteq>j-length left_cells"
          using different i_right j_right by simp
        have source_disjoint:
            "right_cells!(i-length left_cells)\<inter>
             right_cells!(j-length left_cells)={}"
          by (rule right_disjoint[rule_format, OF i_index j_index indices_differ])
        show ?thesis using source_disjoint i_right j_right
          by (simp add: nth_append)
      qed
    qed
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_cells_partition_def
    using appended_bounded appended_covered appended_disjoint by blast
qed

lemma comma_semantic_b1_crt_partition_concat_disjoint:
  fixes slots :: "'a list"
    and slot_universe :: "'a \<Rightarrow> nat set"
    and slot_cells :: "'a \<Rightarrow> nat set list"
  assumes slots_distinct: "distinct slots"
    and each_partition:
      "list_all (\<lambda>slot. comma_semantic_b1_crt_cells_partition
        (slot_universe slot) (slot_cells slot)) slots"
    and universes_disjoint:
      "\<And>left right. left\<in>set slots \<Longrightarrow> right\<in>set slots \<Longrightarrow>
        left\<noteq>right \<Longrightarrow>
        slot_universe left \<inter> slot_universe right = {}"
  shows "comma_semantic_b1_crt_cells_partition
    (\<Union>slot\<in>set slots. slot_universe slot)
    (concat (map slot_cells slots))"
  using slots_distinct each_partition universes_disjoint
proof (induction slots)
  case Nil
  then show ?case
    by (simp add: comma_semantic_b1_crt_cells_partition_def)
next
  case (Cons slot slots)
  have head_partition:
    "comma_semantic_b1_crt_cells_partition
      (slot_universe slot) (slot_cells slot)"
    using Cons.prems(2) by simp
  have tail_distinct: "distinct slots"
    using Cons.prems(1) by simp
  have tail_partitions:
    "list_all (
      (\<lambda>slot. comma_semantic_b1_crt_cells_partition
        (slot_universe slot) (slot_cells slot))) slots"
    using Cons.prems(2) by simp
  have tail_disjoint:
    "\<And>left right. left\<in>set slots \<Longrightarrow> right\<in>set slots \<Longrightarrow>
      left\<noteq>right \<Longrightarrow>
      slot_universe left \<inter> slot_universe right = {}"
    using Cons.prems(3) by auto
  have tail_partition:
    "comma_semantic_b1_crt_cells_partition
      (\<Union>item\<in>set slots. slot_universe item)
      (concat (map slot_cells slots))"
    by (rule Cons.IH[OF tail_distinct tail_partitions tail_disjoint])
  have slot_notin_tail: "slot\<notin>set slots"
    using Cons.prems(1) by simp
  have head_tail_disjoint:
    "slot_universe slot \<inter> (\<Union>item\<in>set slots. slot_universe item) = {}"
  proof (rule ccontr)
    assume not_empty:
      "\<not> slot_universe slot \<inter>
        (\<Union>item\<in>set slots. slot_universe item) = {}"
    then obtain phase item where phase_slot: "phase\<in>slot_universe slot"
      and item_in: "item\<in>set slots"
      and phase_item: "phase\<in>slot_universe item"
      by blast
    have different: "slot\<noteq>item"
      using slot_notin_tail item_in by blast
    have empty:
      "slot_universe slot \<inter> slot_universe item = {}"
      by (rule Cons.prems(3)[of slot item]) (use item_in different in auto)
    show False using empty phase_slot phase_item by blast
  qed
  have combined:
    "comma_semantic_b1_crt_cells_partition
      (slot_universe slot \<union>
        (\<Union>item\<in>set slots. slot_universe item))
      (slot_cells slot @ concat (map slot_cells slots))"
    by (rule comma_semantic_b1_crt_partition_append_disjoint
      [OF head_partition tail_partition head_tail_disjoint])
  show ?case using combined by simp
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_partition_append_disjoint}, @{thm comma_semantic_b1_crt_partition_concat_disjoint}]; Comma_Proof_Profile.report "Structural partition: append and concat checked"\<close>

lemma comma_semantic_b1_crt_lift_cells_partition:
  assumes child_partition:
      "comma_semantic_b1_crt_cells_partition {..<924} child_cells"
    and period: "0<period"
    and slot: "slot<period"
  shows "comma_semantic_b1_crt_cells_partition
    (comma_semantic_b1_crt_slot_cylinder period slot)
    (comma_semantic_b1_crt_lift_cells period slot shift child_cells)"
proof -
  have child_subsets:
      "\<forall>i<length child_cells. child_cells!i\<subseteq>{..<924}"
    using child_partition
    by (auto simp: comma_semantic_b1_crt_cells_partition_def)
  have child_covered:
      "\<forall>phase\<in>{..<924}. \<exists>i<length child_cells. phase\<in>child_cells!i"
    using child_partition
    by (auto simp: comma_semantic_b1_crt_cells_partition_def)
  have child_disjoint:
      "\<forall>i<length child_cells. \<forall>j<length child_cells.
        i\<noteq>j \<longrightarrow> child_cells!i\<inter>child_cells!j={}"
    using child_partition
    by (auto simp: comma_semantic_b1_crt_cells_partition_def)
  have lifted_length:
      "length (comma_semantic_b1_crt_lift_cells period slot shift child_cells) =
       length child_cells"
    by (simp add: comma_semantic_b1_crt_lift_cells_def)
  have bounded:
      "\<forall>i<length (comma_semantic_b1_crt_lift_cells period slot shift child_cells).
        comma_semantic_b1_crt_lift_cells period slot shift child_cells ! i
          \<subseteq> comma_semantic_b1_crt_slot_cylinder period slot"
  proof (intro allI impI)
    fix i
    assume i: "i<length (comma_semantic_b1_crt_lift_cells period slot shift child_cells)"
    have i': "i<length child_cells" using i lifted_length by simp
    show "comma_semantic_b1_crt_lift_cells period slot shift child_cells ! i
        \<subseteq> comma_semantic_b1_crt_slot_cylinder period slot"
      using i' by (auto simp: comma_semantic_b1_crt_lift_cells_def)
  qed
  have covered:
      "\<forall>phase\<in>comma_semantic_b1_crt_slot_cylinder period slot.
        \<exists>i<length (comma_semantic_b1_crt_lift_cells period slot shift child_cells).
          phase\<in>comma_semantic_b1_crt_lift_cells period slot shift child_cells ! i"
  proof (intro ballI)
    fix phase
    assume phase_in_slot:
      "phase\<in>comma_semantic_b1_crt_slot_cylinder period slot"
    have phase_bound: "phase<924"
      using phase_in_slot by (auto simp: comma_semantic_b1_crt_slot_cylinder_def)
    have shifted_bound: "(phase+shift) mod 924<924"
      by simp
    obtain i where i: "i<length child_cells"
      and child: "(phase+shift) mod 924\<in>child_cells!i"
      using child_covered shifted_bound by blast
    have member:
      "phase\<in>comma_semantic_b1_crt_lift_cells period slot shift child_cells ! i"
      using phase_in_slot phase_bound child i
      by (auto simp: comma_semantic_b1_crt_lift_cells_def)
    show "\<exists>i<length
        (comma_semantic_b1_crt_lift_cells period slot shift child_cells).
        phase\<in>comma_semantic_b1_crt_lift_cells period slot shift child_cells ! i"
    proof (rule exI[of _ i])
      show "i<length
          (comma_semantic_b1_crt_lift_cells period slot shift child_cells) \<and>
          phase\<in>comma_semantic_b1_crt_lift_cells period slot shift child_cells ! i"
        using i lifted_length member by simp
    qed
  qed
  have pairwise:
      "\<forall>i<length (comma_semantic_b1_crt_lift_cells period slot shift child_cells).
       \<forall>j<length (comma_semantic_b1_crt_lift_cells period slot shift child_cells).
         i\<noteq>j \<longrightarrow>
         comma_semantic_b1_crt_lift_cells period slot shift child_cells ! i \<inter>
           comma_semantic_b1_crt_lift_cells period slot shift child_cells ! j = {}"
  proof (intro allI impI allI impI impI)
    fix i j
    assume i: "i<length (comma_semantic_b1_crt_lift_cells period slot shift child_cells)"
      and j: "j<length (comma_semantic_b1_crt_lift_cells period slot shift child_cells)"
      and different: "i\<noteq>j"
    have i': "i<length child_cells" and j': "j<length child_cells"
      using i j lifted_length by simp_all
    have disjoint_child: "child_cells!i\<inter>child_cells!j={}"
      using child_disjoint i' j' different by blast
    show "comma_semantic_b1_crt_lift_cells period slot shift child_cells ! i \<inter>
        comma_semantic_b1_crt_lift_cells period slot shift child_cells ! j = {}"
      using i' j' disjoint_child
      by (auto simp: comma_semantic_b1_crt_lift_cells_def)
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_cells_partition_def
    using bounded covered pairwise by blast
qed

lemma comma_semantic_b1_crt_rebase_cells_partition:
  assumes partition:
    "comma_semantic_b1_crt_cells_partition {..<924} cells"
  shows "comma_semantic_b1_crt_cells_partition {..<924}
    (map (comma_semantic_b1_crt_rebase_set shift) cells)"
proof -
  have subsets:
      "\<forall>i<length cells. cells!i\<subseteq>{..<924}"
    using partition by (auto simp: comma_semantic_b1_crt_cells_partition_def)
  have covered:
      "\<forall>phase\<in>{..<924}. \<exists>i<length cells. phase\<in>cells!i"
    using partition by (auto simp: comma_semantic_b1_crt_cells_partition_def)
  have disjoint:
      "\<forall>i<length cells. \<forall>j<length cells.
        i\<noteq>j \<longrightarrow> cells!i\<inter>cells!j={}"
    using partition by (auto simp: comma_semantic_b1_crt_cells_partition_def)
  have len: "length (map (comma_semantic_b1_crt_rebase_set shift) cells)=length cells"
    by simp
  have rebase_bounded:
      "\<forall>i<length (map (comma_semantic_b1_crt_rebase_set shift) cells).
        map (comma_semantic_b1_crt_rebase_set shift) cells ! i \<subseteq> {..<924}"
  proof (intro allI impI)
    fix i
    assume i: "i<length (map (comma_semantic_b1_crt_rebase_set shift) cells)"
    have i': "i<length cells" using i len by simp
    show "map (comma_semantic_b1_crt_rebase_set shift) cells ! i \<subseteq> {..<924}"
      using i' by (auto simp: comma_semantic_b1_crt_rebase_set_def)
  qed
  have rebase_covered:
      "\<forall>phase\<in>{..<924}.
        \<exists>i<length (map (comma_semantic_b1_crt_rebase_set shift) cells).
          phase\<in>map (comma_semantic_b1_crt_rebase_set shift) cells ! i"
  proof (intro ballI)
    fix phase :: nat
    assume phase: "phase\<in>{..<924}"
    have shifted: "(phase+shift) mod 924\<in>{..<924}" by simp
    obtain i where i: "i<length cells"
      and cell: "(phase+shift) mod 924\<in>cells!i"
      using covered shifted by blast
    have member: "phase\<in>comma_semantic_b1_crt_rebase_set shift (cells!i)"
      using phase cell by (simp add: comma_semantic_b1_crt_rebase_set_def)
    show "\<exists>i<length (map (comma_semantic_b1_crt_rebase_set shift) cells).
        phase\<in>map (comma_semantic_b1_crt_rebase_set shift) cells ! i"
      using i member len by (auto simp: comma_semantic_b1_crt_rebase_set_def)
  qed
  have rebase_pairwise:
      "\<forall>i<length (map (comma_semantic_b1_crt_rebase_set shift) cells).
       \<forall>j<length (map (comma_semantic_b1_crt_rebase_set shift) cells).
         i\<noteq>j \<longrightarrow>
         map (comma_semantic_b1_crt_rebase_set shift) cells ! i \<inter>
           map (comma_semantic_b1_crt_rebase_set shift) cells ! j = {}"
  proof (intro allI impI allI impI impI)
    fix i j
    assume i: "i<length (map (comma_semantic_b1_crt_rebase_set shift) cells)"
      and j: "j<length (map (comma_semantic_b1_crt_rebase_set shift) cells)"
      and different: "i\<noteq>j"
    have i': "i<length cells" and j': "j<length cells"
      using i j len by simp_all
    have original_disjoint: "cells!i\<inter>cells!j={}"
      using disjoint i' j' different by blast
    show "map (comma_semantic_b1_crt_rebase_set shift) cells ! i \<inter>
        map (comma_semantic_b1_crt_rebase_set shift) cells ! j = {}"
      using i' j' original_disjoint
      by (auto simp: comma_semantic_b1_crt_rebase_set_def)
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_cells_partition_def
    using rebase_bounded rebase_covered rebase_pairwise by blast
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_lift_cells_partition}, @{thm comma_semantic_b1_crt_rebase_cells_partition}]; Comma_Proof_Profile.report "Structural partition: lift and rebase checked"\<close>

lemma comma_semantic_b1_crt_grouping_preserves_partition:
  assumes width: "length labels=length cells"
    and partition: "comma_semantic_b1_crt_cells_partition universe cells"
    and label_set: "set labels=set results"
    and results_distinct: "distinct results"
  shows "comma_semantic_b1_crt_cells_partition universe
    (comma_semantic_b1_crt_group_supports labels cells results)"
proof -
  have cell_subset:
    "\<forall>i<length cells. cells!i\<subseteq>universe"
    and cell_cover:
    "\<forall>phase\<in>universe. \<exists>i<length cells. phase\<in>cells!i"
    and cell_disjoint:
    "\<forall>i<length cells. \<forall>j<length cells.
       i\<noteq>j \<longrightarrow> cells!i\<inter>cells!j={}"
    using partition by (auto simp: comma_semantic_b1_crt_cells_partition_def)
  have group_length:
      "length (comma_semantic_b1_crt_group_supports labels cells results)=length results"
    by (simp add: comma_semantic_b1_crt_group_supports_def)
  have group_bounded:
      "\<forall>i<length (comma_semantic_b1_crt_group_supports labels cells results).
        comma_semantic_b1_crt_group_supports labels cells results ! i \<subseteq> universe"
  proof (intro allI impI)
    fix i
    assume i: "i<length (comma_semantic_b1_crt_group_supports labels cells results)"
    have i': "i<length results" using i group_length by simp
    show "comma_semantic_b1_crt_group_supports labels cells results ! i \<subseteq> universe"
      using width cell_subset i'
      by (auto simp: comma_semantic_b1_crt_group_supports_def
        comma_semantic_b1_crt_group_support_def)
  qed
  have group_covered:
      "\<forall>phase\<in>universe.
        \<exists>i<length (comma_semantic_b1_crt_group_supports labels cells results).
          phase\<in>comma_semantic_b1_crt_group_supports labels cells results ! i"
  proof (intro ballI)
    fix phase
    assume phase: "phase\<in>universe"
    obtain cell_index where cell_index: "cell_index<length cells"
      and member: "phase\<in>cells!cell_index"
      using cell_cover phase by blast
    have label_member: "labels!cell_index\<in>set labels"
      using width cell_index by (auto simp: in_set_conv_nth)
    then have result_member: "labels!cell_index\<in>set results"
      using label_set by simp
    then obtain result_index where result_index: "result_index<length results"
      and result_value: "results!result_index=labels!cell_index"
      by (auto simp: in_set_conv_nth)
    have grouped:
      "phase\<in>comma_semantic_b1_crt_group_support labels cells
        (results!result_index)"
      using cell_index member result_value
      by (auto simp: comma_semantic_b1_crt_group_support_def)
    have result_index_bound:
      "result_index<length
        (comma_semantic_b1_crt_group_supports labels cells results)"
      using result_index group_length by simp
    have result_index_member:
      "phase\<in>comma_semantic_b1_crt_group_supports labels cells results ! result_index"
      using grouped result_index
      by (simp add: comma_semantic_b1_crt_group_supports_def)
    show "\<exists>i<length
        (comma_semantic_b1_crt_group_supports labels cells results).
        phase\<in>comma_semantic_b1_crt_group_supports labels cells results ! i"
      using result_index_bound result_index_member by blast
  qed
  have group_pairwise:
      "\<forall>i<length (comma_semantic_b1_crt_group_supports labels cells results).
       \<forall>j<length (comma_semantic_b1_crt_group_supports labels cells results).
         i\<noteq>j \<longrightarrow>
         comma_semantic_b1_crt_group_supports labels cells results ! i \<inter>
           comma_semantic_b1_crt_group_supports labels cells results ! j = {}"
  proof (intro allI impI allI impI impI)
    fix i j
    assume i: "i<length (comma_semantic_b1_crt_group_supports labels cells results)"
      and j: "j<length (comma_semantic_b1_crt_group_supports labels cells results)"
      and different: "i\<noteq>j"
    have i': "i<length results" and j': "j<length results"
      using i j group_length by simp_all
    have labels_differ: "results!i\<noteq>results!j"
      using results_distinct i' j' different
      by (auto simp: nth_eq_iff_index_eq)
    have no_common_cell:
        "\<not> (phase \<in>
          comma_semantic_b1_crt_group_supports labels cells results ! i \<and>
          phase \<in>
          comma_semantic_b1_crt_group_supports labels cells results ! j)"
      if phase: "phase \<in>
          comma_semantic_b1_crt_group_supports labels cells results ! i \<inter>
            comma_semantic_b1_crt_group_supports labels cells results ! j"
      for phase
    proof -
      obtain left_cell where left_bound: "left_cell<length cells"
        and left_label: "labels!left_cell=results!i"
        and left_member: "phase\<in>cells!left_cell"
        using phase i' by (auto simp: comma_semantic_b1_crt_group_supports_def
          comma_semantic_b1_crt_group_support_def)
      obtain right_cell where right_bound: "right_cell<length cells"
        and right_label: "labels!right_cell=results!j"
        and right_member: "phase\<in>cells!right_cell"
        using phase j' by (auto simp: comma_semantic_b1_crt_group_supports_def
          comma_semantic_b1_crt_group_support_def)
      have cells_differ: "left_cell\<noteq>right_cell"
        using labels_differ left_label right_label by auto
      have source_cells_disjoint: "cells!left_cell\<inter>cells!right_cell={}"
        using cell_disjoint left_bound right_bound cells_differ by blast
      show ?thesis using source_cells_disjoint left_member right_member by blast
    qed
    show "comma_semantic_b1_crt_group_supports labels cells results ! i \<inter>
        comma_semantic_b1_crt_group_supports labels cells results ! j = {}"
      using no_common_cell by blast
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_cells_partition_def
    using group_bounded group_covered group_pairwise by blast
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_grouping_preserves_partition}]; Comma_Proof_Profile.report "Structural partition: grouping checked"\<close>

lemma comma_semantic_b1_crt_zip_indexed:
  assumes width: "length left=length right"
  shows "zip left right = map (\<lambda>i. (left!i,right!i)) [0..<length left]"
proof (rule nth_equalityI)
  show "length (zip left right) =
      length (map (\<lambda>i. (left!i,right!i)) [0..<length left])"
    using width by simp
  fix i
  assume index: "i<length (zip left right)"
  have left: "i<length left" and right: "i<length right"
    using index by simp_all
  show "(zip left right)!i =
      (map (\<lambda>i. (left!i,right!i)) [0..<length left])!i"
    using left right by simp
qed
lemma comma_semantic_b1_crt_map_nth:
  fixes f :: "'a \<Rightarrow> 'b" and xs :: "'a list" and ys :: "'b list" and i :: nat
  assumes mapped: "map f xs=ys" and i_bound: "i<length ys"
  shows "ys!i=f(xs!i)"
proof -
  have mapped_length: "length (map f xs)=length ys"
    by (rule arg_cong[where f=length, OF mapped])
  have length_eq: "length xs=length ys" using mapped_length by simp
  have index_bound: "i<length xs" using i_bound length_eq by simp
  have point_eq: "(map f xs)!i=ys!i"
    by (rule arg_cong[where f="\<lambda>entries. entries!i", OF mapped])
  show ?thesis using point_eq index_bound by (simp add: nth_map)
qed
lemma comma_semantic_b1_crt_map_set_member:
  fixes f :: "'a \<Rightarrow> 'b" and x :: "'a" and xs :: "'a list"
  assumes member: "x\<in>set xs"
  shows "f x\<in>set (map f xs)"
proof -
  have "f x\<in>f ` set xs" by (rule imageI[OF member])
  then show ?thesis by (simp only: set_map)
qed
lemma comma_semantic_b1_crt_concat_member_row:
  fixes rows :: "'a list list" and piece :: "'a"
  assumes member: "piece\<in>set (concat rows)"
  shows "\<exists>row<length rows. piece\<in>set (rows!row)"
proof -
  have row_pieces_exists: "\<exists>row_pieces\<in>set rows. piece\<in>set row_pieces"
    using member by (simp only: set_concat UN_iff)
  then obtain row_pieces where row_pieces: "row_pieces\<in>set rows"
    and piece_row: "piece\<in>set row_pieces" by blast
  obtain row where row: "row<length rows" and row_at: "rows!row=row_pieces"
    using row_pieces by (auto simp: in_set_conv_nth)
  show ?thesis using row piece_row row_at by blast
qed
lemma comma_semantic_b1_crt_grouped_rebase_wellformed:
  fixes parent :: comma_semantic_b1_crt_occurrence
    and labels :: "comma_semantic_b1_result list"
    and cells :: "nat set list"
  assumes binding: "comma_semantic_b1_crt_occurrence_binding_check parent"
    and admitted: "list_all (comma_crt_admitted 0)
      (comma_semantic_b1_crt_occurrence_columns parent)"
    and source_width: "length labels=length cells"
    and source_partition:
      "comma_semantic_b1_crt_cells_partition {..<924} cells"
    and label_set:
      "set labels=set (comma_semantic_b1_crt_occurrence_beta parent)"
    and results_distinct:
      "distinct (comma_semantic_b1_crt_occurrence_beta parent)"
    and grouped_rebased:
      "map comma_crt_set (comma_semantic_b1_crt_occurrence_columns parent) =
        map (comma_semantic_b1_crt_rebase_set shift)
          (comma_semantic_b1_crt_group_supports labels cells
            (comma_semantic_b1_crt_occurrence_beta parent))"
    and shift: "shift<924"
    and group_support_nonempty:
      "list_all (\<lambda>row. comma_semantic_b1_crt_group_support labels cells
        (comma_semantic_b1_crt_occurrence_beta parent!row)\<noteq>{})
        [0..<length (comma_semantic_b1_crt_occurrence_beta parent)]"
  shows "comma_semantic_b1_crt_occurrence_wellformed parent"
proof -
  let ?columns="comma_semantic_b1_crt_occurrence_columns parent"
  let ?beta="comma_semantic_b1_crt_occurrence_beta parent"
  have binding_facts:
    "comma_semantic_b1_crt_occurrence_rebase parent<924 \<and>
     length ?columns=length ?beta \<and> ?columns\<noteq>[]"
    using binding by (simp add: comma_semantic_b1_crt_occurrence_binding_check_def)
  have grouped_partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (comma_semantic_b1_crt_group_supports labels cells ?beta)"
    by (rule comma_semantic_b1_crt_grouping_preserves_partition
      [OF source_width source_partition label_set results_distinct])
  have rebased_partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map (comma_semantic_b1_crt_rebase_set shift)
          (comma_semantic_b1_crt_group_supports labels cells ?beta))"
    by (rule comma_semantic_b1_crt_rebase_cells_partition[OF grouped_partition])
  have columns_partition:
      "comma_semantic_b1_crt_cells_partition {..<924} (map comma_crt_set ?columns)"
    using rebased_partition grouped_rebased by simp
  have disjoint: "comma_semantic_b1_crt_occurrence_disjoint ?columns"
  proof (unfold comma_semantic_b1_crt_occurrence_disjoint_def
      comma_semantic_b1_crt_occurrence_indexed_columns_def, intro ballI impI)+
    fix left right
    assume left: "left\<in>set (zip [0..<length ?columns] ?columns)"
      and right: "right\<in>set (zip [0..<length ?columns] ?columns)"
      and different: "fst left\<noteq>fst right"
    have left_facts:
      "fst left<length ?columns \<and> snd left=?columns!fst left"
      using left by (auto simp: in_set_conv_nth nth_zip)
    have right_facts:
      "fst right<length ?columns \<and> snd right=?columns!fst right"
      using right by (auto simp: in_set_conv_nth nth_zip)
    have cells_disjoint:
      "(map comma_crt_set ?columns)!fst left \<inter>
        (map comma_crt_set ?columns)!fst right={}"
      using columns_partition left_facts right_facts different
      by (auto simp: comma_semantic_b1_crt_cells_partition_def nth_map)
    show "comma_crt_set (snd left)\<inter>comma_crt_set (snd right)={}"
      using cells_disjoint left_facts right_facts by simp
  qed
  have covered: "comma_semantic_b1_crt_occurrence_covered ?columns"
  proof (unfold comma_semantic_b1_crt_occurrence_covered_def
      comma_semantic_b1_crt_occurrence_indexed_columns_def, intro allI impI)
    fix phase :: nat
    assume phase: "phase<924"
    have partition_cover: "\<forall>phase\<in>{..<924}. \<exists>i<length (map comma_crt_set ?columns). phase\<in>(map comma_crt_set ?columns)!i"
      using columns_partition by (auto simp: comma_semantic_b1_crt_cells_partition_def)
    have phase_member: "phase\<in>{..<924}" using phase by simp
    obtain i where i: "i<length (map comma_crt_set ?columns)"
      and phase_cell: "phase\<in>(map comma_crt_set ?columns)!i"
      using bspec[OF partition_cover phase_member] by blast
    have i_bound: "i<length ?columns" using i by simp
    have member: "(i,?columns!i)\<in>set (zip [0..<length ?columns] ?columns)"
      using i_bound by (auto simp: in_set_conv_nth nth_zip)
    have phase_column: "phase\<in>comma_crt_set (snd (i,?columns!i))"
      using phase_cell i_bound by (simp add: nth_map)
    show "\<exists>entry\<in>set (zip [0..<length ?columns] ?columns).
        phase\<in>comma_crt_set (snd entry)"
      using member phase_column by blast
  qed
  have supported: "list_all comma_crt_supported ?columns"
  proof (unfold list_all_iff, intro ballI)
    fix column
    assume column: "column\<in>set ?columns"
    then obtain i where i: "i<length ?columns" and column_at: "?columns!i=column"
      by (auto simp: in_set_conv_nth)
    have i_beta: "i<length ?beta" using i binding_facts by simp
    have grouped_cell_nonempty:
      "comma_semantic_b1_crt_group_support labels cells (?beta!i)\<noteq>{}"
      by (rule comma_semantic_b1_crt_list_all_upt_index[OF group_support_nonempty i_beta])
    have i_group:
      "i<length (comma_semantic_b1_crt_group_supports labels cells ?beta)"
      using i_beta by (simp add: comma_semantic_b1_crt_group_supports_def)
    have grouped_cell_bounded:
      "comma_semantic_b1_crt_group_support labels cells (?beta!i)\<subseteq>{..<924}"
      using grouped_partition i_group
      by (auto simp: comma_semantic_b1_crt_cells_partition_def
        comma_semantic_b1_crt_group_supports_def nth_map)
    have parent_cell_nonempty: "comma_crt_set column\<noteq>{}"
    proof -
      have cell_eq: "comma_crt_set (?columns!i) = comma_semantic_b1_crt_rebase_set shift (comma_semantic_b1_crt_group_support labels cells (?beta!i))"
        using arg_cong[where f="\<lambda>xs. xs!i", OF grouped_rebased] i i_beta i_group
        by (simp add: nth_map comma_semantic_b1_crt_group_supports_def)
      show ?thesis using comma_semantic_b1_crt_rebase_nonempty[OF shift
        grouped_cell_nonempty grouped_cell_bounded] cell_eq column_at by simp
    qed
    have admitted_at: "comma_crt_admitted 0 column"
      using admitted column by (auto simp: list_all_iff)
    show "comma_crt_supported column"
      using comma_crt_supported_nonempty[OF admitted_at] parent_cell_nonempty by blast
  qed
  show ?thesis
    using binding_facts admitted supported disjoint covered
    by (auto simp: comma_semantic_b1_crt_occurrence_wellformed_def)
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_grouped_rebase_wellformed}]; Comma_Proof_Profile.report "Structural parent geometry checked"\<close>
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_zip_indexed}]; Comma_Proof_Profile.report "Structural partition: zip-indexed checked"\<close>
lemma comma_semantic_b1_crt_filter_map_equiv:
  assumes predicates: "\<And>x. keep (map_value x) \<longleftrightarrow> select x"
  shows "filter keep (map map_value values) =
    map map_value (filter select values)"
  using predicates
  by (induction "values") auto
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_filter_map_equiv}]; Comma_Proof_Profile.report "Structural partition: filter-map checked"\<close>
lemma comma_semantic_b1_crt_group_row_union_from_origins:
  fixes entries :: "('origin \<times> (nat set \<times> 'result)) list"
    and rows :: "'piece list list"
    and origin_of :: "'piece \<Rightarrow> 'origin"
    and support_of :: "'piece \<Rightarrow> nat set"
    and results :: "'result list"
    and row :: nat
  assumes rows_width: "length rows=length results"
    and row_bound: "row<length results"
    and results_distinct: "distinct results"
    and entries_origin_injective: "inj_on fst (set entries)"
    and origins_exact:
      "set (map origin_of (concat rows)) = set (map fst entries)"
    and row_binding:
      "\<And>row piece. row<length results \<Longrightarrow>
        piece\<in>set (rows!row) \<Longrightarrow>
        \<exists>entry\<in>set entries.
          origin_of piece=fst entry \<and>
          support_of piece=fst (snd entry) \<and>
          snd (snd entry)=results!row"
  shows "(\<Union>piece\<in>set (rows!row). support_of piece) =
    comma_semantic_b1_crt_group_support
      (map (\<lambda>entry. snd (snd entry)) entries)
      (map (\<lambda>entry. fst (snd entry)) entries) (results!row)"
proof (rule set_eqI)
  fix phase :: nat
  show "phase\<in>(\<Union>piece\<in>set (rows!row). support_of piece) \<longleftrightarrow>
      phase\<in>comma_semantic_b1_crt_group_support
        (map (\<lambda>entry. snd (snd entry)) entries)
        (map (\<lambda>entry. fst (snd entry)) entries) (results!row)"
  proof
    assume phase:
      "phase\<in>(\<Union>piece\<in>set (rows!row). support_of piece)"
    then obtain piece where piece: "piece\<in>set (rows!row)"
      and phase_piece: "phase\<in>support_of piece" by blast
    have entry_exists:
      "\<exists>entry\<in>set entries.
        origin_of piece=fst entry \<and>
        support_of piece=fst (snd entry) \<and>
        snd (snd entry)=results!row"
      by (rule row_binding[OF row_bound piece])
    obtain entry where entry: "entry\<in>set entries"
      and origin: "origin_of piece=fst entry"
      and support: "support_of piece=fst (snd entry)"
      and label: "snd (snd entry)=results!row"
      using entry_exists by blast
    obtain index where index: "index<length entries" and entry_index: "entries!index=entry"
      using entry by (auto simp: in_set_conv_nth)
    ML_prf \<open>Comma_Proof_Profile.report "Structural row union: left entry indexed"\<close>
    show "phase\<in>comma_semantic_b1_crt_group_support
        (map (\<lambda>entry. snd (snd entry)) entries)
        (map (\<lambda>entry. fst (snd entry)) entries) (results!row)"
      using phase_piece support label index entry_index
      by (auto simp: comma_semantic_b1_crt_group_support_def)
    ML_prf \<open>Comma_Proof_Profile.report "Structural row union: left direction passed"\<close>
  next
    assume phase:
      "phase\<in>comma_semantic_b1_crt_group_support
        (map (\<lambda>entry. snd (snd entry)) entries)
        (map (\<lambda>entry. fst (snd entry)) entries) (results!row)"
    then obtain index where index: "index<length entries"
      and label: "snd (snd (entries!index))=results!row"
      and phase_entry: "phase\<in>fst (snd (entries!index))"
      by (auto simp: comma_semantic_b1_crt_group_support_def)
    have entry_member: "entries!index\<in>set entries"
      by (rule nth_mem[OF index])
    have origin_member: "fst (entries!index)\<in>set (map fst entries)"
      using entry_member by auto
    have piece_origin_member:
      "fst (entries!index)\<in>set (map origin_of (concat rows))"
      using origins_exact origin_member by simp
    have piece_exists_rev:
        "\<exists>piece\<in>set (concat rows).
          fst (entries!index)=origin_of piece"
      using piece_origin_member by (simp only: set_map image_iff)
    obtain piece where piece: "piece\<in>set (concat rows)"
      and origin_rev: "fst (entries!index)=origin_of piece"
      using piece_exists_rev by blast
    have origin: "origin_of piece=fst (entries!index)"
      by (rule sym[OF origin_rev])
    ML_prf \<open>Comma_Proof_Profile.report "Structural row union: exact-origin piece found"\<close>
    have row_pieces_exists:
        "\<exists>row_pieces\<in>set rows. piece\<in>set row_pieces"
      using piece by (simp only: set_concat UN_iff)
    then obtain row_pieces where row_pieces: "row_pieces\<in>set rows"
      and piece_row: "piece\<in>set row_pieces"
      by blast
    obtain destination where destination:
        "destination<length rows" and row_at: "rows!destination=row_pieces"
      using row_pieces by (auto simp: in_set_conv_nth)
    ML_prf \<open>Comma_Proof_Profile.report "Structural row union: source destination found"\<close>
    have destination_bound: "destination<length results"
      using destination rows_width by simp
    have matching_exists:
        "\<exists>entry\<in>set entries.
          origin_of piece=fst entry \<and>
          support_of piece=fst (snd entry) \<and>
          snd (snd entry)=results!destination"
      by (rule row_binding[OF destination_bound]) (use piece_row row_at in simp)
    then obtain matching_entry where matching_entry: "matching_entry\<in>set entries"
      and matching_origin: "origin_of piece=fst matching_entry"
      and matching_support: "support_of piece=fst (snd matching_entry)"
      and matching_label: "snd (snd matching_entry)=results!destination"
      by blast
    ML_prf \<open>Comma_Proof_Profile.report "Structural row union: destination row bound"\<close>
    have same_entry: "matching_entry=entries!index"
      using entries_origin_injective matching_entry entry_member origin matching_origin
      by (auto simp: inj_on_def)
    have values_equal: "results!destination=results!row"
      using label matching_label same_entry by simp
    have destination_eq: "destination=row"
      using results_distinct destination_bound row_bound values_equal
      by (auto simp: nth_eq_iff_index_eq)
    have piece_in_row: "piece\<in>set (rows!row)"
      using piece_row row_at destination_eq by simp
    show "phase\<in>(\<Union>piece\<in>set (rows!row). support_of piece)"
      using piece_in_row phase_entry matching_support same_entry by blast
    ML_prf \<open>Comma_Proof_Profile.report "Structural row union: right direction passed"\<close>
  qed
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_group_row_union_from_origins}]; Comma_Proof_Profile.report "Structural partition: row-union checked"\<close>
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_map_set_member}, @{thm comma_semantic_b1_crt_concat_member_row}]; Comma_Proof_Profile.report "Structural partition: list algebra checked"\<close>
ML \<open>Comma_Proof_Profile.report "Structural partition: final oracle audit entered"\<close>
ML \<open>
val _ = if null (Thm_Deps.all_oracles @{thms
  comma_semantic_b1_crt_rebase_nonempty comma_semantic_b1_crt_list_all_upt_index comma_semantic_b1_crt_slot_cells_partition comma_semantic_b1_crt_partition_append_disjoint comma_semantic_b1_crt_partition_concat_disjoint comma_semantic_b1_crt_lift_cells_partition comma_semantic_b1_crt_rebase_cells_partition comma_semantic_b1_crt_grouping_preserves_partition comma_semantic_b1_crt_partition_subset_cells_eq comma_semantic_b1_crt_zip_indexed comma_semantic_b1_crt_map_nth comma_semantic_b1_crt_map_set_member comma_semantic_b1_crt_concat_member_row comma_semantic_b1_crt_grouped_rebase_wellformed comma_semantic_b1_crt_filter_map_equiv comma_semantic_b1_crt_group_row_union_from_origins comma_semantic_b1_crt_distinct_concat_tagged_rows
}) then () else error "Comma_Semantic_B1_CRT_Structural_Partition local oracle audit failed"
val _ = Comma_Proof_Profile.report "Structural partition: final oracle audit passed"
\<close>
end
