theory Comma_Semantic_B1_CRT_Partition_Coverage
  imports Comma_Semantic_B1_CRT_Local_Cover
begin

text \<open>
Symbolic support certificates turn local no-overlap checks into set
containment.  A certified partition plus this per-cell containment rule
recovers exact grouped geometry without reconstructing a group OR fold.
\<close>

lemma comma_semantic_b1_crt_admitted_unsupported_empty:
  assumes admitted: "comma_crt_admitted 0 column"
    and unsupported: "\<not> comma_crt_supported column"
  shows "comma_crt_set column={}"
proof (rule ccontr)
  assume "comma_crt_set column \<noteq> {}"
  then obtain phase where phase: "phase\<in>comma_crt_set column" by blast
  have evaluates: "comma_crt_eval phase column"
    using phase by (auto simp: comma_crt_set_def)
  have supported: "comma_crt_supported column"
    by (rule comma_crt_eval_supported[OF admitted evaluates])
  show False using supported unsupported by blast
qed

lemma comma_semantic_b1_crt_unsupported_and_subset:
  assumes piece_admitted: "comma_crt_admitted 0 piece"
    and parent_admitted: "comma_crt_admitted 0 parent"
    and unsupported:
      "\<not> comma_crt_supported
        (comma_crt_apply Comma_CRT_And piece (comma_crt_negate parent))"
  shows "comma_crt_set piece\<subseteq>comma_crt_set parent"
proof -
  have negated_admitted: "comma_crt_admitted 0 (comma_crt_negate parent)"
    by (rule comma_crt_negate_admitted[OF parent_admitted])
  have difference_admitted:
      "comma_crt_admitted 0
        (comma_crt_apply Comma_CRT_And piece (comma_crt_negate parent))"
    by (rule comma_crt_apply_admitted[OF piece_admitted negated_admitted])
  have difference_empty:
      "comma_crt_set (comma_crt_apply Comma_CRT_And piece
        (comma_crt_negate parent))={}"
    by (rule comma_semantic_b1_crt_admitted_unsupported_empty
      [OF difference_admitted unsupported])
  have bounded: "comma_crt_set piece\<subseteq>{..<924}"
    by (auto simp: comma_crt_set_def)
  show ?thesis
    using bounded difference_empty comma_crt_apply_and_set[OF piece_admitted negated_admitted]
      comma_crt_negate_set[OF parent_admitted]
    by auto
qed

lemma comma_semantic_b1_crt_rebase_inverse_set_left:
  assumes shift: "shift<924" and cells: "cells\<subseteq>{..<924}"
  shows "comma_semantic_b1_crt_rebase_set ((924-shift) mod 924)
      (comma_semantic_b1_crt_rebase_set shift cells)=cells"
proof (rule set_eqI)
  fix phase
  have inverse:
      "(924-shift) mod 924=comma_semantic_b1_inverse_shift shift"
    using shift by (simp add: comma_semantic_b1_inverse_shift_def)
  have cancel:
      "(((phase+comma_semantic_b1_inverse_shift shift) mod 924+shift) mod 924)=
        phase mod 924"
    by (rule comma_semantic_b1_inverse_shift_cancel_right)
  show "phase\<in>comma_semantic_b1_crt_rebase_set ((924-shift) mod 924)
      (comma_semantic_b1_crt_rebase_set shift cells) \<longleftrightarrow>
      phase\<in>cells"
  proof
    assume member:
      "phase\<in>comma_semantic_b1_crt_rebase_set ((924-shift) mod 924)
        (comma_semantic_b1_crt_rebase_set shift cells)"
    then have phase_bound: "phase<924"
      and inner:
        "(phase+(924-shift) mod 924) mod 924\<in>
          comma_semantic_b1_crt_rebase_set shift cells"
      by (auto simp: comma_semantic_b1_crt_rebase_set_def inverse)
    have inner_bound:
        "(phase+(924-shift) mod 924) mod 924<924"
      by simp
    have result:
        "(((phase+comma_semantic_b1_inverse_shift shift) mod 924+shift) mod 924)
          \<in>cells"
      using inner by (auto simp: comma_semantic_b1_crt_rebase_set_def inverse)
    show "phase\<in>cells" using result cancel phase_bound by simp
  next
    assume member: "phase\<in>cells"
    have phase_bound: "phase<924" using cells member by blast
    have shifted_bound:
        "(phase+comma_semantic_b1_inverse_shift shift) mod 924<924"
      by simp
    have result:
        "((phase+comma_semantic_b1_inverse_shift shift) mod 924+shift) mod 924
          \<in>cells"
      using member cancel phase_bound by simp
    show "phase\<in>comma_semantic_b1_crt_rebase_set ((924-shift) mod 924)
        (comma_semantic_b1_crt_rebase_set shift cells)"
      using phase_bound shifted_bound result
      by (auto simp: comma_semantic_b1_crt_rebase_set_def inverse)
  qed
qed

lemma comma_semantic_b1_crt_partition_pointwise_rebase_eq:
  assumes source:
      "comma_semantic_b1_crt_cells_partition {..<924} source_cells"
    and target:
      "comma_semantic_b1_crt_cells_partition {..<924} target_cells"
    and width: "length source_cells=length target_cells"
    and shift: "shift<924"
    and covered:
      "\<forall>i<length source_cells.
        source_cells!i\<subseteq>
          comma_semantic_b1_crt_rebase_set shift (target_cells!i)"
  shows "map (comma_semantic_b1_crt_rebase_set ((924-shift) mod 924))
      source_cells=target_cells"
proof -
  have inverse_source:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map (comma_semantic_b1_crt_rebase_set ((924-shift) mod 924))
          source_cells)"
    by (rule comma_semantic_b1_crt_rebase_cells_partition[OF source])
  have inverse_covered:
      "\<forall>i<length source_cells.
        comma_semantic_b1_crt_rebase_set ((924-shift) mod 924)
          (source_cells!i)\<subseteq>target_cells!i"
  proof (intro allI impI)
    fix i
    assume i: "i<length source_cells"
    have source_subset:
        "source_cells!i\<subseteq>
          comma_semantic_b1_crt_rebase_set shift (target_cells!i)"
      using covered i by blast
    have target_bounded: "target_cells!i\<subseteq>{..<924}"
      using target i width
      by (auto simp: comma_semantic_b1_crt_cells_partition_def)
    have inverse_target:
        "comma_semantic_b1_crt_rebase_set ((924-shift) mod 924)
          (comma_semantic_b1_crt_rebase_set shift (target_cells!i))=
          target_cells!i"
      by (rule comma_semantic_b1_crt_rebase_inverse_set_left[OF shift target_bounded])
    show "comma_semantic_b1_crt_rebase_set ((924-shift) mod 924)
        (source_cells!i)\<subseteq>target_cells!i"
      using source_subset inverse_target
      by (auto simp: comma_semantic_b1_crt_rebase_set_def)
  qed
  show ?thesis
    by (rule comma_semantic_b1_crt_partition_subset_cells_eq
      [OF inverse_source target]) (use width inverse_covered in auto)
qed

lemma comma_semantic_b1_crt_group_partition_rebase_local_eq:
  assumes source_width: "length labels=length source_cells"
    and source_partition:
      "comma_semantic_b1_crt_cells_partition {..<924} source_cells"
    and label_set: "set labels=set results"
    and results_distinct: "distinct results"
    and parent_partition:
      "comma_semantic_b1_crt_cells_partition {..<924} parent_cells"
    and parent_width: "length results=length parent_cells"
    and rebase: "rebase<924"
    and local_coverage:
      "\<forall>i<length results.
        comma_semantic_b1_crt_group_support labels source_cells (results!i) \<subseteq>
          comma_semantic_b1_crt_rebase_set rebase (parent_cells!i)"
  shows "map (comma_semantic_b1_crt_rebase_set ((924-rebase) mod 924))
      (comma_semantic_b1_crt_group_supports labels source_cells results) =
    parent_cells"
proof -
  have grouped_partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (comma_semantic_b1_crt_group_supports labels source_cells results)"
    by (rule comma_semantic_b1_crt_grouping_preserves_partition
      [OF source_width source_partition label_set results_distinct])
  have width:
      "length (comma_semantic_b1_crt_group_supports labels source_cells results) =
        length parent_cells"
    using parent_width by (simp add: comma_semantic_b1_crt_group_supports_def)
  have covered:
      "\<forall>i<length (comma_semantic_b1_crt_group_supports labels source_cells results).
        comma_semantic_b1_crt_group_supports labels source_cells results!i \<subseteq>
          comma_semantic_b1_crt_rebase_set rebase (parent_cells!i)"
    using local_coverage by (simp add: comma_semantic_b1_crt_group_supports_def)
  show ?thesis
    by (rule comma_semantic_b1_crt_partition_pointwise_rebase_eq
      [OF grouped_partition parent_partition width rebase covered])
qed

fun comma_semantic_b1_crt_partition_drop_false ::
    "comma_crt_column list \<Rightarrow> comma_crt_column list" where
  "comma_semantic_b1_crt_partition_drop_false [] = []"
| "comma_semantic_b1_crt_partition_drop_false (column#columns) =
    (if column=Comma_CRT_Bool False
     then comma_semantic_b1_crt_partition_drop_false columns
     else column#comma_semantic_b1_crt_partition_drop_false columns)"

lemma comma_semantic_b1_crt_partition_drop_false_false_head:
  "comma_semantic_b1_crt_partition_drop_false
      (Comma_CRT_Bool False#columns) =
    comma_semantic_b1_crt_partition_drop_false columns"
  by simp

lemma comma_semantic_b1_crt_partition_drop_false_nonfalse_head:
  assumes "column \<noteq> Comma_CRT_Bool False"
  shows "comma_semantic_b1_crt_partition_drop_false (column#columns) =
    column#comma_semantic_b1_crt_partition_drop_false columns"
  using assms by simp

lemma comma_semantic_b1_crt_partition_true_nonfalse:
  "(Comma_CRT_Bool True \<noteq> Comma_CRT_Bool False) = True"
  by simp

lemma comma_semantic_b1_crt_partition_node_nonfalse:
  "(Comma_CRT_Node level children \<noteq> Comma_CRT_Bool False) = True"
  by simp

lemma comma_semantic_b1_crt_partition_drop_false_idempotent:
  "comma_semantic_b1_crt_partition_drop_false
      (comma_semantic_b1_crt_partition_drop_false columns) =
    comma_semantic_b1_crt_partition_drop_false columns"
  by (induction columns) (auto split: if_splits)

fun comma_semantic_b1_crt_partition_has_node_at ::
    "nat \<Rightarrow> comma_crt_column list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_partition_has_node_at level [] = False"
| "comma_semantic_b1_crt_partition_has_node_at level (column#columns) =
    ((case column of Comma_CRT_Bool _ \<Rightarrow> False
      | Comma_CRT_Node node_level _ \<Rightarrow> node_level=level) \<or>
      comma_semantic_b1_crt_partition_has_node_at level columns)"

fun comma_semantic_b1_crt_partition_cofactor_checked ::
    "nat list \<Rightarrow> comma_crt_column list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_partition_cofactor_checked [] columns =
    (comma_semantic_b1_crt_partition_drop_false columns =
      [Comma_CRT_Bool True])"
| "comma_semantic_b1_crt_partition_cofactor_checked (level#levels) columns =
    (let residual=comma_semantic_b1_crt_partition_drop_false columns
     in if residual=[Comma_CRT_Bool True] then True
        else if comma_semantic_b1_crt_partition_has_node_at level residual then
          list_all (\<lambda>digit.
            comma_semantic_b1_crt_partition_cofactor_checked levels
              (comma_semantic_b1_crt_partition_drop_false
                (map (comma_crt_cofactor_or_false level digit) residual)))
            [0..<comma_crt_period level]
        else comma_semantic_b1_crt_partition_cofactor_checked levels residual)"

definition comma_semantic_b1_crt_columns_partition_certified ::
    "comma_crt_column list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_columns_partition_certified columns \<longleftrightarrow>
    list_all (comma_crt_admitted 0) columns \<and>
    comma_semantic_b1_crt_partition_cofactor_checked [0..<4] columns"

definition comma_semantic_b1_crt_eval_count ::
    "nat \<Rightarrow> comma_crt_column list \<Rightarrow> nat" where
  "comma_semantic_b1_crt_eval_count phase columns =
    length (filter id (map (comma_crt_eval phase) columns))"

lemma comma_semantic_b1_crt_partition_drop_false_admitted:
  assumes admitted: "list_all (comma_crt_admitted lower) columns"
  shows "list_all (comma_crt_admitted lower)
    (comma_semantic_b1_crt_partition_drop_false columns)"
  using admitted
  by (induction columns) (auto simp: list_all_iff)

lemma comma_semantic_b1_crt_partition_drop_false_eval_count:
  "comma_semantic_b1_crt_eval_count phase
    (comma_semantic_b1_crt_partition_drop_false columns) =
   comma_semantic_b1_crt_eval_count phase columns"
  by (induction columns) (auto simp: comma_semantic_b1_crt_eval_count_def)

lemma comma_semantic_b1_crt_partition_admitted_advance:
  assumes admitted: "list_all (comma_crt_admitted level) columns"
    and level: "level<4"
    and no_node: "\<not> comma_semantic_b1_crt_partition_has_node_at level columns"
  shows "list_all (comma_crt_admitted (Suc level)) columns"
  using admitted no_node
  by (induction columns) (auto simp: list_all_iff split: comma_crt_column.splits)

lemma comma_semantic_b1_crt_partition_cofactor_admitted:
  assumes admitted: "list_all (comma_crt_admitted level) columns"
    and level: "level<4"
    and digit: "digit<comma_crt_period level"
  shows "list_all (comma_crt_admitted (Suc level))
    (map (comma_crt_cofactor_or_false level digit) columns)"
  using admitted
proof (induction columns)
  case Nil
  then show ?case by simp
next
  case (Cons column columns)
  have column_admitted: "comma_crt_admitted level column"
    using Cons.prems by (simp add: list_all_iff)
  have rest_admitted: "list_all (comma_crt_admitted level) columns"
    using Cons.prems by (simp add: list_all_iff)
  obtain child where cofactor:
      "comma_crt_cofactor level digit column=Some child"
    and child_admitted: "comma_crt_admitted (Suc level) child"
    by (rule comma_crt_cofactor_admitted_digit[OF column_admitted level digit])
  have head_admitted:
      "comma_crt_admitted (Suc level)
        (comma_crt_cofactor_or_false level digit column)"
    using cofactor child_admitted
    by (simp add: comma_crt_cofactor_or_false_def)
  have tail_admitted: "list_all (comma_crt_admitted (Suc level))
      (map (comma_crt_cofactor_or_false level digit) columns)"
    by (rule Cons.IH[OF rest_admitted])
  show ?case using head_admitted tail_admitted by simp
qed

lemma comma_semantic_b1_crt_partition_cofactor_eval_map:
  assumes admitted: "list_all (comma_crt_admitted level) columns"
    and level: "level<4"
    and digit: "digit=phase mod comma_crt_period level"
  shows "map (comma_crt_eval phase)
      (map (comma_crt_cofactor_or_false level digit) columns) =
    map (comma_crt_eval phase) columns"
  using admitted
proof (induction columns)
  case Nil
  then show ?case by simp
next
  case (Cons column columns)
  have column_admitted: "comma_crt_admitted level column"
    using Cons.prems by (simp add: list_all_iff)
  have rest_admitted: "list_all (comma_crt_admitted level) columns"
    using Cons.prems by (simp add: list_all_iff)
  obtain child where cofactor:
      "comma_crt_cofactor level digit column=Some child"
    and child_admitted: "comma_crt_admitted (Suc level) child"
    and child_eval: "comma_crt_eval phase child=comma_crt_eval phase column"
    by (rule comma_crt_cofactor_exact[OF column_admitted level digit])
  have head_eval: "comma_crt_eval phase
      (comma_crt_cofactor_or_false level digit column)=comma_crt_eval phase column"
    using cofactor child_eval by (simp add: comma_crt_cofactor_or_false_def)
  show ?case using head_eval Cons.IH[OF rest_admitted] by simp
qed

lemma comma_semantic_b1_crt_partition_cofactor_branch_eval_count:
  assumes admitted: "list_all (comma_crt_admitted level) columns"
    and level: "level<4"
    and digit_bound: "digit<comma_crt_period level"
    and digit: "digit=phase mod comma_crt_period level"
  shows "comma_semantic_b1_crt_eval_count phase
      (comma_semantic_b1_crt_partition_drop_false
        (map (comma_crt_cofactor_or_false level digit) columns)) =
    comma_semantic_b1_crt_eval_count phase columns"
proof -
  have eval_map:
      "map (comma_crt_eval phase)
        (map (comma_crt_cofactor_or_false level digit) columns) =
       map (comma_crt_eval phase) columns"
    by (rule comma_semantic_b1_crt_partition_cofactor_eval_map
      [OF admitted level digit])
  have dropped_count:
      "comma_semantic_b1_crt_eval_count phase
        (comma_semantic_b1_crt_partition_drop_false
          (map (comma_crt_cofactor_or_false level digit) columns)) =
       comma_semantic_b1_crt_eval_count phase
         (map (comma_crt_cofactor_or_false level digit) columns)"
    by (rule comma_semantic_b1_crt_partition_drop_false_eval_count)
  have mapped_count:
      "comma_semantic_b1_crt_eval_count phase
        (map (comma_crt_cofactor_or_false level digit) columns) =
       comma_semantic_b1_crt_eval_count phase columns"
    unfolding comma_semantic_b1_crt_eval_count_def
    by (simp only: eval_map)
  show ?thesis using dropped_count mapped_count by simp
qed

lemma comma_semantic_b1_crt_partition_cofactor_checked_sound:
  assumes schedule: "levels=[lower..<4]"
    and admitted: "list_all (comma_crt_admitted lower) columns"
    and checked:
      "comma_semantic_b1_crt_partition_cofactor_checked levels columns"
  shows "comma_semantic_b1_crt_eval_count phase columns=1"
  using schedule admitted checked
proof (induction levels arbitrary: lower columns)
  case Nil
  have singleton:
      "comma_semantic_b1_crt_partition_drop_false columns=
        [Comma_CRT_Bool True]"
    using Nil.prems(3) by simp
  show ?case
    using comma_semantic_b1_crt_partition_drop_false_eval_count[of phase columns]
      singleton
    by (simp add: comma_semantic_b1_crt_eval_count_def)
next
  case (Cons level levels)
  have schedule: "level#levels=[lower..<4]" by (rule Cons.prems(1))
  have lower_bound: "lower<4"
    using schedule by (cases "lower<4") (simp_all add: upt_rec)
  have range_decomposition: "[lower..<4]=lower#[Suc lower..<4]"
    using lower_bound by (simp add: upt_rec)
  have level_eq: "level=lower"
    and tail_schedule: "levels=[Suc lower..<4]"
    using schedule range_decomposition by simp_all
  let ?residual = "comma_semantic_b1_crt_partition_drop_false columns"
  have residual_admitted: "list_all (comma_crt_admitted lower) ?residual"
    by (rule comma_semantic_b1_crt_partition_drop_false_admitted[OF Cons.prems(2)])
  have initial_count:
      "comma_semantic_b1_crt_eval_count phase columns=
        comma_semantic_b1_crt_eval_count phase ?residual"
    by (rule sym; rule comma_semantic_b1_crt_partition_drop_false_eval_count)
  show ?case
  proof (cases "?residual=[Comma_CRT_Bool True]")
    case True
    then show ?thesis using initial_count
      by (simp add: comma_semantic_b1_crt_eval_count_def)
  next
    case False
    note residual_not_singleton = False
    show ?thesis
    proof (cases "comma_semantic_b1_crt_partition_has_node_at lower ?residual")
      case True
      have branches_checked:
          "list_all (\<lambda>digit.
            comma_semantic_b1_crt_partition_cofactor_checked levels
              (comma_semantic_b1_crt_partition_drop_false
                (map (comma_crt_cofactor_or_false lower digit) ?residual)))
            [0..<comma_crt_period lower]"
        using Cons.prems(3) residual_not_singleton True level_eq
        by (simp add: Let_def)
      have period_positive: "0<comma_crt_period lower"
        by (rule comma_crt_period_positive[OF lower_bound])
      have digit_bound: "phase mod comma_crt_period lower < comma_crt_period lower"
        using period_positive by simp
      have digit_mem: "phase mod comma_crt_period lower \<in>
          set [0..<comma_crt_period lower]"
        using digit_bound by simp
      have branch_checked:
          "comma_semantic_b1_crt_partition_cofactor_checked levels
            (comma_semantic_b1_crt_partition_drop_false
              (map (comma_crt_cofactor_or_false lower
                (phase mod comma_crt_period lower)) ?residual))"
        using branches_checked digit_mem by (simp add: list_all_iff)
      have branch_admitted:
          "list_all (comma_crt_admitted (Suc lower))
            (comma_semantic_b1_crt_partition_drop_false
              (map (comma_crt_cofactor_or_false lower
                (phase mod comma_crt_period lower)) ?residual))"
      proof (rule comma_semantic_b1_crt_partition_drop_false_admitted)
        show "list_all (comma_crt_admitted (Suc lower))
            (map (comma_crt_cofactor_or_false lower
              (phase mod comma_crt_period lower)) ?residual)"
          by (rule comma_semantic_b1_crt_partition_cofactor_admitted
            [OF residual_admitted lower_bound digit_bound])
      qed
      have branch_count:
          "comma_semantic_b1_crt_eval_count phase
            (comma_semantic_b1_crt_partition_drop_false
              (map (comma_crt_cofactor_or_false lower
                (phase mod comma_crt_period lower)) ?residual))=1"
        by (rule Cons.IH[OF tail_schedule branch_admitted branch_checked])
      have transfer:
          "comma_semantic_b1_crt_eval_count phase
            (comma_semantic_b1_crt_partition_drop_false
              (map (comma_crt_cofactor_or_false lower
                (phase mod comma_crt_period lower)) ?residual)) =
           comma_semantic_b1_crt_eval_count phase ?residual"
        by (rule comma_semantic_b1_crt_partition_cofactor_branch_eval_count
          [OF residual_admitted lower_bound digit_bound refl])
      show ?thesis using branch_count transfer initial_count by simp
    next
      case False
      have skipped_checked:
          "comma_semantic_b1_crt_partition_cofactor_checked levels ?residual"
        using Cons.prems(3) residual_not_singleton False level_eq
        by (simp add: Let_def)
      have advanced_admitted:
          "list_all (comma_crt_admitted (Suc lower)) ?residual"
        by (rule comma_semantic_b1_crt_partition_admitted_advance
          [OF residual_admitted lower_bound False])
      have residual_count:
          "comma_semantic_b1_crt_eval_count phase ?residual=1"
        by (rule Cons.IH[OF tail_schedule advanced_admitted skipped_checked])
      show ?thesis using initial_count residual_count by simp
    qed
  qed
qed

lemma comma_semantic_b1_crt_eval_count_positive_at:
  assumes index: "i<length columns"
    and evaluates: "comma_crt_eval phase (columns!i)"
  shows "0<comma_semantic_b1_crt_eval_count phase columns"
  using index evaluates
proof (induction columns arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons column columns)
  show ?case
  proof (cases i)
    case "0"
    have head: "comma_crt_eval phase column"
      using Cons.prems(2) "0" by simp
    show ?thesis using head
      by (simp add: comma_semantic_b1_crt_eval_count_def)
  next
    case (Suc j)
    have j_bound: "j<length columns"
      using Cons.prems(1) Suc by simp
    have tail_eval: "comma_crt_eval phase (columns!j)"
      using Cons.prems(2) Suc by simp
    have tail_positive: "0<comma_semantic_b1_crt_eval_count phase columns"
      by (rule Cons.IH[OF j_bound tail_eval])
    show ?thesis using tail_positive
      by (cases "comma_crt_eval phase column")
        (simp_all add: comma_semantic_b1_crt_eval_count_def)
  qed
qed

lemma comma_semantic_b1_crt_eval_count_two_true:
  assumes i: "i<length columns" and j: "j<length columns"
    and distinct: "i\<noteq>j"
    and eval_i: "comma_crt_eval phase (columns!i)"
    and eval_j: "comma_crt_eval phase (columns!j)"
  shows "2\<le>comma_semantic_b1_crt_eval_count phase columns"
  using i j distinct eval_i eval_j
proof (induction columns arbitrary: i j)
  case Nil
  then show ?case by simp
next
  case (Cons column columns)
  show ?case
  proof (cases i)
    case "0"
    then obtain j' where j: "j=Suc j'"
      using Cons.prems(3) by (cases j) auto
    have head: "comma_crt_eval phase column"
      using Cons.prems(4) "0" by simp
    have tail_index: "j'<length columns"
      using Cons.prems(2) j by simp
    have tail_eval: "comma_crt_eval phase (columns!j')"
      using Cons.prems(5) j by simp
    have tail_positive:
        "0<comma_semantic_b1_crt_eval_count phase columns"
      by (rule comma_semantic_b1_crt_eval_count_positive_at
        [OF tail_index tail_eval])
    have count:
      "comma_semantic_b1_crt_eval_count phase (column#columns) =
        Suc (comma_semantic_b1_crt_eval_count phase columns)"
      using head by (simp add: comma_semantic_b1_crt_eval_count_def)
    show ?thesis using count tail_positive by arith
  next
    case (Suc i')
    note i_suc = Suc
    show ?thesis
    proof (cases j)
      case "0"
      have head: "comma_crt_eval phase column"
        using Cons.prems(5) "0" by simp
      have tail_index: "i'<length columns"
        using Cons.prems(1) i_suc by simp
      have tail_eval: "comma_crt_eval phase (columns!i')"
        using Cons.prems(4) i_suc by simp
      have tail_positive:
          "0<comma_semantic_b1_crt_eval_count phase columns"
        by (rule comma_semantic_b1_crt_eval_count_positive_at
          [OF tail_index tail_eval])
      have count:
        "comma_semantic_b1_crt_eval_count phase (column#columns) =
          Suc (comma_semantic_b1_crt_eval_count phase columns)"
        using head by (simp add: comma_semantic_b1_crt_eval_count_def)
      show ?thesis using count tail_positive by arith
    next
      case (Suc j')
      have i_bound: "i'<length columns"
        using Cons.prems(1) i_suc by simp
      have j_bound: "j'<length columns"
        using Cons.prems(2) Suc by simp
      have indices_distinct: "i'\<noteq>j'"
        using Cons.prems(3) i_suc Suc by simp
      have eval_i': "comma_crt_eval phase (columns!i')"
        using Cons.prems(4) i_suc by simp
      have eval_j': "comma_crt_eval phase (columns!j')"
        using Cons.prems(5) Suc by simp
      have tail_count:
          "2\<le>comma_semantic_b1_crt_eval_count phase columns"
        by (rule Cons.IH[OF i_bound j_bound indices_distinct eval_i' eval_j'])
      show ?thesis using tail_count
        by (cases "comma_crt_eval phase column")
          (simp_all add: comma_semantic_b1_crt_eval_count_def)
    qed
  qed
qed

lemma comma_semantic_b1_crt_columns_partition_certified_sound:
  assumes certified: "comma_semantic_b1_crt_columns_partition_certified row"
  shows "comma_semantic_b1_crt_cells_partition {..<924}
    (map comma_crt_set row)"
proof -
  have columns_admitted: "list_all (comma_crt_admitted 0) row"
    and checked: "comma_semantic_b1_crt_partition_cofactor_checked [0..<4] row"
    using certified by (auto simp: comma_semantic_b1_crt_columns_partition_certified_def)
  have eval_exact: "\<And>phase.
      comma_semantic_b1_crt_eval_count phase row=1"
  proof -
    fix phase
    have schedule: "[0..<4]=[0..<4]" by simp
    show "comma_semantic_b1_crt_eval_count phase row=1"
      by (rule comma_semantic_b1_crt_partition_cofactor_checked_sound
        [OF schedule columns_admitted checked])
  qed
  have bounded:
      "\<forall>i<length (map comma_crt_set row).
        map comma_crt_set row!i\<subseteq>{..<924}"
    by (auto simp: comma_crt_set_def)
  have covered:
      "\<forall>phase\<in>{..<924}. \<exists>i<length (map comma_crt_set row).
        phase\<in>map comma_crt_set row!i"
  proof (intro ballI)
    fix phase :: nat
    assume phase_bound: "phase\<in>{..<924}"
    have filtered_length:
        "length (filter id (map (comma_crt_eval phase) row))=1"
      using eval_exact[of phase]
      by (simp add: comma_semantic_b1_crt_eval_count_def)
    have nonempty:
        "filter id (map (comma_crt_eval phase) row)\<noteq>[]"
      using filtered_length by (cases "filter id (map (comma_crt_eval phase) row)") auto
    obtain selected_bool rest where filtered:
        "filter id (map (comma_crt_eval phase) row)=selected_bool#rest"
      using nonempty by (cases "filter id (map (comma_crt_eval phase) row)") auto
    have selected_member:
        "selected_bool\<in>set (filter id (map (comma_crt_eval phase) row))"
      by (simp add: filtered)
    have selected_true: "selected_bool=True"
      using selected_member by (auto simp: set_filter)
    have selected_value_member:
        "selected_bool\<in>set (map (comma_crt_eval phase) row)"
      using selected_member by (auto simp: set_filter)
    obtain i where i: "i<length row"
      and eval_at: "(map (comma_crt_eval phase) row)!i=selected_bool"
      using selected_value_member by (auto simp: in_set_conv_nth)
    show "\<exists>i<length (map comma_crt_set row).
        phase\<in>map comma_crt_set row!i"
      using i eval_at selected_true phase_bound
      by (intro exI[of _ i]) (auto simp: comma_crt_set_def nth_map)
  qed
  have pairwise:
      "\<forall>i<length (map comma_crt_set row).
       \<forall>j<length (map comma_crt_set row).
       i\<noteq>j \<longrightarrow>
         map comma_crt_set row!i \<inter>map comma_crt_set row!j={}"
  proof (intro allI impI allI impI impI)
    fix i j
    assume i: "i<length (map comma_crt_set row)"
      and j: "j<length (map comma_crt_set row)" and different: "i\<noteq>j"
    have i_row: "i<length row" and j_row: "j<length row"
      using i j by simp_all
    show "map comma_crt_set row!i \<inter>map comma_crt_set row!j={}"
    proof (rule ccontr)
      assume nonempty: "map comma_crt_set row!i \<inter>
        map comma_crt_set row!j\<noteq>{}"
      then obtain phase where phase:
          "phase\<in>map comma_crt_set row!i"
          "phase\<in>map comma_crt_set row!j"
        by blast
      have eval_i: "comma_crt_eval phase (row!i)"
        using phase(1) i_row by (auto simp: comma_crt_set_def nth_map)
      have eval_j: "comma_crt_eval phase (row!j)"
        using phase(2) j_row by (auto simp: comma_crt_set_def nth_map)
      have at_least_two:
          "2\<le>comma_semantic_b1_crt_eval_count phase row"
        by (rule comma_semantic_b1_crt_eval_count_two_true
          [OF i_row j_row different eval_i eval_j])
      have exactly_one:
          "comma_semantic_b1_crt_eval_count phase row=1"
        by (rule eval_exact)
      show False using at_least_two exactly_one by simp
    qed
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_cells_partition_def
    using bounded covered pairwise by blast
qed

lemma comma_semantic_b1_crt_columns_partition_certified_rejects_empty:
  "\<not> comma_semantic_b1_crt_columns_partition_certified []"
  by (simp add: comma_semantic_b1_crt_columns_partition_certified_def upt_rec)

lemma comma_semantic_b1_crt_columns_partition_certified_accepts_true:
  "comma_semantic_b1_crt_columns_partition_certified [Comma_CRT_Bool True]"
  by (simp add: comma_semantic_b1_crt_columns_partition_certified_def upt_rec)

lemma comma_semantic_b1_crt_columns_partition_certified_rejects_missing_coverage:
  "\<not> comma_semantic_b1_crt_columns_partition_certified
    [Comma_CRT_Bool False]"
  by code_simp

lemma comma_semantic_b1_crt_columns_partition_certified_rejects_duplicate_true:
  "\<not> comma_semantic_b1_crt_columns_partition_certified
    [Comma_CRT_Bool True,Comma_CRT_Bool True]"
  by code_simp

lemma comma_semantic_b1_crt_columns_partition_certified_rejects_missing_quarter:
  "\<not> comma_semantic_b1_crt_columns_partition_certified
    [Comma_CRT_Node 0
      [Comma_CRT_Bool True,Comma_CRT_Bool True,
       Comma_CRT_Bool False,Comma_CRT_Bool False],
     Comma_CRT_Node 0
      [Comma_CRT_Bool False,Comma_CRT_Bool False,
       Comma_CRT_Bool False,Comma_CRT_Bool True]]"
  by code_simp

lemma comma_semantic_b1_crt_columns_partition_certified_accepts_complementary_quarters:
  "comma_semantic_b1_crt_columns_partition_certified
    [Comma_CRT_Node 0
      [Comma_CRT_Bool True,Comma_CRT_Bool True,
       Comma_CRT_Bool False,Comma_CRT_Bool False],
     Comma_CRT_Node 0
      [Comma_CRT_Bool False,Comma_CRT_Bool False,
       Comma_CRT_Bool True,Comma_CRT_Bool True]]"
  by code_simp

lemma comma_semantic_b1_crt_columns_partition_certified_rejects_malformed_level:
  "\<not> comma_semantic_b1_crt_columns_partition_certified
    [Comma_CRT_Node 4 [Comma_CRT_Bool True]]"
  by code_simp

lemma comma_semantic_b1_crt_columns_partition_certified_rejects_malformed_width:
  "\<not> comma_semantic_b1_crt_columns_partition_certified
    [Comma_CRT_Node 0
      [Comma_CRT_Bool True,Comma_CRT_Bool False,Comma_CRT_Bool True]]"
  by code_simp

lemma comma_semantic_b1_crt_columns_partition_certified_rejects_backward_child:
  "\<not> comma_semantic_b1_crt_columns_partition_certified
    [Comma_CRT_Node 0
      [Comma_CRT_Node 0
        [Comma_CRT_Bool True,Comma_CRT_Bool True,
         Comma_CRT_Bool True,Comma_CRT_Bool True],
       Comma_CRT_Bool False,Comma_CRT_Bool False,Comma_CRT_Bool False]]"
  by code_simp

lemmas comma_semantic_b1_crt_partition_coverage_oracle_audit_bundle =
  comma_semantic_b1_crt_admitted_unsupported_empty
  comma_semantic_b1_crt_partition_drop_false_false_head
  comma_semantic_b1_crt_partition_drop_false_nonfalse_head
  comma_semantic_b1_crt_partition_true_nonfalse
  comma_semantic_b1_crt_partition_node_nonfalse
  comma_semantic_b1_crt_partition_drop_false_idempotent
  comma_semantic_b1_crt_partition_drop_false_admitted
  comma_semantic_b1_crt_partition_drop_false_eval_count
  comma_semantic_b1_crt_partition_admitted_advance
  comma_semantic_b1_crt_partition_cofactor_admitted
  comma_semantic_b1_crt_partition_cofactor_eval_map
  comma_semantic_b1_crt_partition_cofactor_branch_eval_count
  comma_semantic_b1_crt_partition_cofactor_checked_sound
  comma_semantic_b1_crt_eval_count_positive_at
  comma_semantic_b1_crt_eval_count_two_true
  comma_semantic_b1_crt_columns_partition_certified_sound
  comma_semantic_b1_crt_columns_partition_certified_rejects_empty
  comma_semantic_b1_crt_columns_partition_certified_accepts_true
  comma_semantic_b1_crt_columns_partition_certified_rejects_missing_coverage
  comma_semantic_b1_crt_columns_partition_certified_rejects_duplicate_true
  comma_semantic_b1_crt_columns_partition_certified_rejects_missing_quarter
  comma_semantic_b1_crt_columns_partition_certified_accepts_complementary_quarters
  comma_semantic_b1_crt_columns_partition_certified_rejects_malformed_level
  comma_semantic_b1_crt_columns_partition_certified_rejects_malformed_width
  comma_semantic_b1_crt_columns_partition_certified_rejects_backward_child
  comma_semantic_b1_crt_unsupported_and_subset
  comma_semantic_b1_crt_rebase_inverse_set_left
  comma_semantic_b1_crt_partition_pointwise_rebase_eq
  comma_semantic_b1_crt_group_partition_rebase_local_eq
ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_semantic_b1_crt_partition_coverage_oracle_audit_bundle})
    then () else error "Partition coverage local oracle audit failed"
  Thm.consolidate @{thms comma_semantic_b1_crt_partition_coverage_oracle_audit_bundle};
  Comma_Proof_Profile.report "Partition coverage: local oracle audit checked"
\<close>

end
