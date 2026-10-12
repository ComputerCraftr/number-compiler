theory Comma_Semantic_B1_CRT_Labelled_Selector
  imports Comma_Semantic_B1_CRT_Partition_Coverage
    Comma_Semantic_B1_CRT_Split_Occurrence
begin

text \<open>
A simultaneous labelled CRT zipper carries the ordered Boolean source columns
and their selected index through one shared four-level MDD.  The witness
below is the kernel interface for that zipper: terminal rows must be exactly
one-hot, skipped dimensions preserve the vector, and a split records one
recursive witness for each radix cofactor.  It contains neither a phase table
nor the result of the legacy recursive checker.
\<close>

primrec comma_semantic_b1_crt_label_fiber ::
    "nat \<Rightarrow> nat option comma_crt_mdd \<Rightarrow> comma_crt_column" where
  "comma_semantic_b1_crt_label_fiber label (Comma_CRT_MDD_Leaf value) =
    Comma_CRT_Bool (value=Some label)"
| "comma_semantic_b1_crt_label_fiber label
      (Comma_CRT_MDD_Node level children) =
    comma_crt_node level (map (comma_semantic_b1_crt_label_fiber label) children)"

lemma comma_semantic_b1_crt_label_fiber_admitted:
  assumes admitted: "comma_crt_mdd_admitted lower selector"
  shows "comma_crt_admitted lower
    (comma_semantic_b1_crt_label_fiber label selector)"
  using admitted
proof (induction selector arbitrary: lower)
  case (Comma_CRT_MDD_Leaf payload)
  then show ?case by simp
next
  case (Comma_CRT_MDD_Node level children)
  have lower: "lower\<le>level"
    and level: "level<4"
    and width: "length children=comma_crt_period level"
    and child_admitted:
      "list_all (comma_crt_mdd_admitted (Suc level)) children"
    using Comma_CRT_MDD_Node.prems by auto
  have fibers_admitted:
      "list_all (comma_crt_admitted (Suc level))
        (map (comma_semantic_b1_crt_label_fiber label) children)"
  proof -
    have each:
        "comma_crt_admitted (Suc level)
          (comma_semantic_b1_crt_label_fiber label child)"
      if child_mem: "child\<in>set children" for child
    proof -
      have child_valid: "comma_crt_mdd_admitted (Suc level) child"
        using child_admitted child_mem by (simp add: list_all_iff)
      show ?thesis
        by (rule Comma_CRT_MDD_Node.IH[OF child_mem child_valid])
    qed
    show ?thesis using each by (simp add: list_all_iff)
  qed
  have fibers_width:
      "length (map (comma_semantic_b1_crt_label_fiber label) children)=
        comma_crt_period level"
    using width by simp
  show ?case
    unfolding comma_semantic_b1_crt_label_fiber.simps
    by (rule comma_crt_node_admitted[OF lower level fibers_width fibers_admitted])
qed

lemma comma_semantic_b1_crt_label_fiber_eval:
  assumes admitted: "comma_crt_mdd_admitted lower selector"
  shows "comma_crt_eval phase
      (comma_semantic_b1_crt_label_fiber label selector) =
    (comma_crt_mdd_eval phase selector=Some (Some label))"
  using admitted
proof (induction selector arbitrary: lower)
  case (Comma_CRT_MDD_Leaf payload)
  then show ?case by simp
next
  case (Comma_CRT_MDD_Node level children)
  have level: "level<4"
    and width: "length children=comma_crt_period level"
    and child_admitted:
      "list_all (comma_crt_mdd_admitted (Suc level)) children"
    using Comma_CRT_MDD_Node.prems by auto
  have selected: "phase mod comma_crt_period level<length children"
    using level width comma_crt_period_positive by simp
  have child: "comma_crt_mdd_admitted (Suc level)
      (children!(phase mod comma_crt_period level))"
    using child_admitted selected by (simp add: list_all_iff)
  have selected_mem: "children!(phase mod comma_crt_period level) \<in> set children"
    using nth_mem[OF selected] .
  have child_eval:
      "comma_crt_eval phase
        (comma_semantic_b1_crt_label_fiber label
          (children!(phase mod comma_crt_period level))) =
       (comma_crt_mdd_eval phase
          (children!(phase mod comma_crt_period level)) = Some (Some label))"
    by (rule Comma_CRT_MDD_Node.IH[OF selected_mem child])
  have fiber_width:
      "length (map (comma_semantic_b1_crt_label_fiber label) children)=
        comma_crt_period level"
    using width by simp
  have fiber_child_selected:
      "map (comma_semantic_b1_crt_label_fiber label) children!
        (phase mod comma_crt_period level) =
       comma_semantic_b1_crt_label_fiber label
        (children!(phase mod comma_crt_period level))"
    by (rule nth_map[OF selected])
  have fiber_node_value:
      "comma_crt_eval phase
        (Comma_CRT_Node level
          (map (comma_semantic_b1_crt_label_fiber label) children)) =
       comma_crt_eval phase
        (map (comma_semantic_b1_crt_label_fiber label) children!
          (phase mod comma_crt_period level))"
    using comma_crt_eval_node_selected[of phase level
        "map (comma_semantic_b1_crt_label_fiber label) children"]
      level fiber_width by simp
  have fiber_node:
      "comma_crt_eval phase
        (comma_crt_node level
          (map (comma_semantic_b1_crt_label_fiber label) children)) =
       comma_crt_eval phase
        (comma_semantic_b1_crt_label_fiber label
          (children!(phase mod comma_crt_period level)))"
    using comma_crt_node_eval[OF level fiber_width] fiber_node_value
      fiber_child_selected by simp
  show ?case
    using child_eval fiber_node selected level width
      comma_crt_mdd_eval_node_selected[of phase level children]
    by simp
qed

lemma comma_semantic_b1_crt_label_terminal_fiber_exact:
  assumes width: "length columns=width"
    and index: "index<width"
    and one_hot: "\<And>i. i<width \<Longrightarrow>
      columns!i=Comma_CRT_Bool (i=index)"
  shows "comma_crt_mdd_admitted lower
      (Comma_CRT_MDD_Leaf (Some index))"
    "\<And>i phase. i<width \<Longrightarrow>
      comma_crt_eval phase (comma_semantic_b1_crt_label_fiber i
        (Comma_CRT_MDD_Leaf (Some index))) =
      comma_crt_eval phase (columns!i)"
  using width index one_hot by (simp_all add: eq_commute)

lemma comma_semantic_b1_crt_label_node_fiber_exact:
  assumes level: "level<4"
    and width: "length children=comma_crt_period level"
    and children_admitted:
      "list_all (comma_crt_mdd_admitted (Suc level)) children"
    and columns_admitted:
      "list_all (comma_crt_admitted level) columns"
    and branch_exact:
      "\<And>digit i phase. digit<comma_crt_period level \<Longrightarrow>
        i<length columns \<Longrightarrow>
        comma_crt_eval phase
          (comma_semantic_b1_crt_label_fiber i (children!digit)) =
        comma_crt_eval phase
          (comma_crt_cofactor_or_false level digit (columns!i))"
  shows "comma_crt_mdd_admitted level (comma_crt_mdd_node level children)"
    "\<And>i phase. i<length columns \<Longrightarrow>
      comma_crt_eval phase (comma_semantic_b1_crt_label_fiber i
        (comma_crt_mdd_node level children)) =
      comma_crt_eval phase (columns!i)"
proof -
  show "comma_crt_mdd_admitted level (comma_crt_mdd_node level children)"
    by (rule comma_crt_mdd_node_admitted[OF le_refl level width children_admitted])
next
  fix i phase
  assume i: "i<length columns"
  have column_admitted: "comma_crt_admitted level (columns!i)"
    using columns_admitted i by (simp add: list_all_iff)
  have digit: "phase mod comma_crt_period level<comma_crt_period level"
    using comma_crt_period_positive[OF level] by simp
  have selected_bound:
      "phase mod comma_crt_period level<length children"
    using digit width by simp
  have selected_child:
      "comma_crt_mdd_admitted (Suc level)
        (children!(phase mod comma_crt_period level))"
    using children_admitted selected_bound by (simp add: list_all_iff)
  have output_eval:
      "comma_crt_mdd_eval phase (comma_crt_mdd_node level children) =
       comma_crt_mdd_eval phase
         (children!(phase mod comma_crt_period level))"
  proof (rule trans)
    show "comma_crt_mdd_eval phase
        (comma_crt_mdd_node level children) =
      comma_crt_mdd_eval phase (Comma_CRT_MDD_Node level children)"
      by (rule comma_crt_mdd_node_eval[OF level width])
    show "comma_crt_mdd_eval phase (Comma_CRT_MDD_Node level children) =
      comma_crt_mdd_eval phase (children!(phase mod comma_crt_period level))"
      using level width comma_crt_period_positive[OF level]
      by (simp add: comma_crt_mdd_eval_node_selected)
  qed
  have output_fiber:
      "comma_crt_eval phase
        (comma_semantic_b1_crt_label_fiber i (comma_crt_mdd_node level children)) =
       (comma_crt_mdd_eval phase (comma_crt_mdd_node level children) = Some (Some i))"
    by (rule comma_semantic_b1_crt_label_fiber_eval
        [OF comma_crt_mdd_node_admitted[OF le_refl level width children_admitted]])
  have child_fiber:
      "comma_crt_eval phase
        (comma_semantic_b1_crt_label_fiber i
          (children!(phase mod comma_crt_period level))) =
       (comma_crt_mdd_eval phase
          (children!(phase mod comma_crt_period level)) = Some (Some i))"
    by (rule comma_semantic_b1_crt_label_fiber_eval[OF selected_child])
  have selected_fiber:
      "comma_crt_eval phase
        (comma_semantic_b1_crt_label_fiber i
          (comma_crt_mdd_node level children)) =
       comma_crt_eval phase
        (comma_semantic_b1_crt_label_fiber i
          (children!(phase mod comma_crt_period level)))"
    using output_fiber child_fiber output_eval by simp
  obtain child_column where cofactor:
      "comma_crt_cofactor level (phase mod comma_crt_period level) (columns!i) =
        Some child_column"
    and child_column_admitted:
      "comma_crt_admitted (Suc level) child_column"
    and cofactor_eval:
      "comma_crt_eval phase child_column=comma_crt_eval phase (columns!i)"
    by (rule comma_crt_cofactor_exact[OF column_admitted level refl])
  have branch:
      "comma_crt_eval phase
        (comma_semantic_b1_crt_label_fiber i
          (children!(phase mod comma_crt_period level))) =
       comma_crt_eval phase
        (comma_crt_cofactor_or_false level
          (phase mod comma_crt_period level) (columns!i))"
    by (rule branch_exact[OF digit i])
  have cofactor_or_false_eval:
      "comma_crt_eval phase
        (comma_crt_cofactor_or_false level
          (phase mod comma_crt_period level) (columns!i)) =
       comma_crt_eval phase (columns!i)"
    using cofactor cofactor_eval
    by (simp add: comma_crt_cofactor_or_false_def)
  show "comma_crt_eval phase
      (comma_semantic_b1_crt_label_fiber i (comma_crt_mdd_node level children)) =
      comma_crt_eval phase (columns!i)"
    using selected_fiber branch cofactor_or_false_eval by simp
qed

lemma comma_semantic_b1_crt_label_terminal_checker:
  assumes index: "index<length columns"
    and one_hot: "\<And>i. i<length columns \<Longrightarrow>
      columns!i=Comma_CRT_Bool (i=index)"
  shows "comma_semantic_b1_crt_partition_cofactor_checked levels columns"
proof -
  have dropped:
      "comma_semantic_b1_crt_partition_drop_false columns=
        [Comma_CRT_Bool True]"
    using index one_hot
  proof (induction columns arbitrary: index)
    case Nil
    then show ?case by simp
  next
    case (Cons column columns)
    have head: "column=Comma_CRT_Bool (0=index)"
      using Cons.prems(2)[of 0] by simp
    show ?case
    proof (cases index)
      case 0
      have tail_false: "columns!i=Comma_CRT_Bool False"
        if "i<length columns" for i
        using Cons.prems(2)[of "Suc i"] that 0 by simp
      have tail_false_all:
          "list_all (\<lambda>column. column=Comma_CRT_Bool False) columns"
      proof (unfold list_all_iff)
        show "\<forall>column\<in>set columns. column=Comma_CRT_Bool False"
          using tail_false by (auto simp: in_set_conv_nth)
      qed
      have "comma_semantic_b1_crt_partition_drop_false columns=[]"
        using tail_false_all
      proof (induction columns)
        case Nil
        then show ?case by simp
      next
        case (Cons column columns)
        have head_false: "column=Comma_CRT_Bool False"
          using Cons.prems by simp
        have rest_false:
            "list_all (\<lambda>column. column=Comma_CRT_Bool False) columns"
          using Cons.prems by simp
        show ?case using head_false rest_false Cons.IH by simp
      qed
      with head 0 show ?thesis by simp
    next
      case (Suc j)
      have j_bound: "j<length columns" using Cons.prems(1) Suc by simp
      have tail_one_hot: "columns!i=Comma_CRT_Bool (i=j)"
        if "i<length columns" for i
        using Cons.prems(2)[of "Suc i"] that Suc by simp
      have tail_drop:
        "comma_semantic_b1_crt_partition_drop_false columns=[Comma_CRT_Bool True]"
        by (rule Cons.IH[OF j_bound tail_one_hot])
      show ?thesis using head Suc tail_drop by simp
    qed
  qed
  show ?thesis using dropped
    by (induction levels) (simp_all add: Let_def)
qed

lemma comma_semantic_b1_crt_partition_checker_drop_false:
  "comma_semantic_b1_crt_partition_cofactor_checked levels
      (comma_semantic_b1_crt_partition_drop_false columns) =
    comma_semantic_b1_crt_partition_cofactor_checked levels columns"
  by (induction levels arbitrary: columns)
    (simp_all add: comma_semantic_b1_crt_partition_drop_false_idempotent Let_def)

lemma comma_semantic_b1_crt_partition_has_node_drop_false:
  "comma_semantic_b1_crt_partition_has_node_at level
      (comma_semantic_b1_crt_partition_drop_false columns) =
    comma_semantic_b1_crt_partition_has_node_at level columns"
  by (induction columns)
    (auto simp: comma_semantic_b1_crt_partition_drop_false.simps
      split: if_splits comma_crt_column.splits)

lemma comma_semantic_b1_crt_partition_drop_false_cofactor:
  "comma_semantic_b1_crt_partition_drop_false
      (map (comma_crt_cofactor_or_false level digit)
        (comma_semantic_b1_crt_partition_drop_false columns)) =
    comma_semantic_b1_crt_partition_drop_false
      (map (comma_crt_cofactor_or_false level digit) columns)"
  by (induction columns)
    (auto simp: comma_semantic_b1_crt_partition_drop_false.simps
      comma_crt_cofactor_or_false_def split: option.splits if_splits)

lemma comma_semantic_b1_crt_partition_cofactor_step:
  assumes level: "level<4"
    and admitted: "list_all (comma_crt_admitted level) columns"
    and branches:
      "\<And>digit. digit<comma_crt_period level \<Longrightarrow>
        comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4]
          (map (comma_crt_cofactor_or_false level digit) columns)"
  shows "comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns"
proof -
  let ?residual = "comma_semantic_b1_crt_partition_drop_false columns"
  have schedule: "[level..<4]=level#[Suc level..<4]"
    by (rule upt_conv_Cons[OF level])
  have unfold:
    "comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns =
      (let residual=comma_semantic_b1_crt_partition_drop_false columns
       in if residual=[Comma_CRT_Bool True] then True
          else if comma_semantic_b1_crt_partition_has_node_at level residual then
            list_all (\<lambda>digit.
              comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4]
                (comma_semantic_b1_crt_partition_drop_false
                  (map (comma_crt_cofactor_or_false level digit) residual)))
              [0..<comma_crt_period level]
          else comma_semantic_b1_crt_partition_cofactor_checked
            [Suc level..<4] residual)"
    by (simp only: schedule comma_semantic_b1_crt_partition_cofactor_checked.simps)
  show ?thesis
  proof (cases "?residual=[Comma_CRT_Bool True]")
    case True
    then show ?thesis using unfold by simp
  next
    case False
    show ?thesis
    proof (cases "comma_semantic_b1_crt_partition_has_node_at level ?residual")
      case True
      have node: "comma_semantic_b1_crt_partition_has_node_at level columns"
        using True by (simp add: comma_semantic_b1_crt_partition_has_node_drop_false)
      have branch_checked:
        "comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4]
          (comma_semantic_b1_crt_partition_drop_false
            (map (comma_crt_cofactor_or_false level digit) ?residual))"
        if digit: "digit<comma_crt_period level" for digit
      proof -
        have raw:
          "comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4]
            (map (comma_crt_cofactor_or_false level digit) columns)"
          by (rule branches[OF digit])
        have cleaned:
          "comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4]
            (comma_semantic_b1_crt_partition_drop_false
              (map (comma_crt_cofactor_or_false level digit) columns))"
          using comma_semantic_b1_crt_partition_checker_drop_false[of
              "[Suc level..<4]"
              "map (comma_crt_cofactor_or_false level digit) columns"] raw
          by simp
        have same:
          "comma_semantic_b1_crt_partition_drop_false
              (map (comma_crt_cofactor_or_false level digit) ?residual) =
           comma_semantic_b1_crt_partition_drop_false
              (map (comma_crt_cofactor_or_false level digit) columns)"
          by (simp add: comma_semantic_b1_crt_partition_drop_false_cofactor)
        show ?thesis using cleaned same by simp
      qed
      have branch_list:
        "list_all (\<lambda>digit.
          comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4]
            (comma_semantic_b1_crt_partition_drop_false
              (map (comma_crt_cofactor_or_false level digit) ?residual)))
          [0..<comma_crt_period level]"
        using branch_checked by (simp add: list_all_iff)
      show ?thesis
        using unfold False True node branch_list by simp
    next
      case False
      have no_node: "\<not> comma_semantic_b1_crt_partition_has_node_at level columns"
        using False by (simp add: comma_semantic_b1_crt_partition_has_node_drop_false)
      have positive: "0<comma_crt_period level"
        by (rule comma_crt_period_positive[OF level])
      have cofactor_same:
        "map (comma_crt_cofactor_or_false level digit) columns=columns"
        if digit: "digit<comma_crt_period level" for digit
        using admitted no_node level
        by (induction columns)
          (auto simp: list_all_iff comma_crt_cofactor_or_false_def
            split: comma_crt_column.splits option.splits if_splits)
      have tail:
        "comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4] columns"
      proof -
        have same_zero:
            "map (comma_crt_cofactor_or_false level 0) columns=columns"
          using cofactor_same[of 0] positive by blast
        show ?thesis using branches[OF positive] same_zero by simp
      qed
      have tail_residual:
        "comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4] ?residual"
        using comma_semantic_b1_crt_partition_checker_drop_false[of
            "[Suc level..<4]" columns] tail by simp
      show ?thesis using unfold False no_node tail_residual by simp
    qed
  qed
qed

lemma comma_semantic_b1_crt_partition_no_node_cofactor_identity:
  assumes level: "level<4"
    and admitted: "list_all (comma_crt_admitted level) columns"
    and no_node:
      "\<not> comma_semantic_b1_crt_partition_has_node_at level columns"
  shows "map (comma_crt_cofactor_or_false level digit) columns=columns"
  using admitted no_node
proof (induction columns)
  case Nil
  then show ?case by simp
next
  case (Cons column columns)
  have head_admitted: "comma_crt_admitted level column"
    using Cons.prems(1) by simp
  have tail_admitted: "list_all (comma_crt_admitted level) columns"
    using Cons.prems(1) by simp
  have head_no_node:
      "case column of Comma_CRT_Bool _ \<Rightarrow> True
       | Comma_CRT_Node node_level _ \<Rightarrow> node_level\<noteq>level"
    using Cons.prems(2) by (cases column) auto
  have tail_no_node:
      "\<not> comma_semantic_b1_crt_partition_has_node_at level columns"
    using Cons.prems(2) by auto
  have head_same:
      "comma_crt_cofactor_or_false level digit column=column"
  proof (cases column)
    case (Comma_CRT_Bool payload)
    then show ?thesis by (simp add: comma_crt_cofactor_or_false_def)
  next
    case (Comma_CRT_Node node_level children)
    have order: "level\<le>node_level"
      using head_admitted Comma_CRT_Node by auto
    have strict: "level<node_level"
      using order head_no_node Comma_CRT_Node by auto
    show ?thesis
      using Comma_CRT_Node strict by (simp add: comma_crt_cofactor_or_false_def)
  qed
  show ?case
    using head_same Cons.IH[OF tail_admitted tail_no_node] by simp
qed

inductive comma_semantic_b1_crt_labelled_zip_witness ::
    "nat \<Rightarrow> comma_crt_column list \<Rightarrow>
      nat option comma_crt_mdd \<Rightarrow> bool" where
  labelled_zip_terminal:
    "index<length columns \<Longrightarrow>
     (\<And>i. i<length columns \<Longrightarrow>
       columns!i=Comma_CRT_Bool (i=index)) \<Longrightarrow>
     comma_semantic_b1_crt_labelled_zip_witness level columns
       (Comma_CRT_MDD_Leaf (Some index))"
| labelled_zip_skip:
    "level<4 \<Longrightarrow>
     list_all (comma_crt_admitted level) columns \<Longrightarrow>
     \<not> comma_semantic_b1_crt_partition_has_node_at level columns \<Longrightarrow>
     comma_semantic_b1_crt_labelled_zip_witness (Suc level) columns selector \<Longrightarrow>
     comma_semantic_b1_crt_labelled_zip_witness level columns selector"
| labelled_zip_node:
    "level<4 \<Longrightarrow>
     list_all (comma_crt_admitted level) columns \<Longrightarrow>
     comma_semantic_b1_crt_partition_has_node_at level columns \<Longrightarrow>
     length children=comma_crt_period level \<Longrightarrow>
     (\<And>digit. digit<comma_crt_period level \<Longrightarrow>
       comma_semantic_b1_crt_labelled_zip_witness (Suc level)
         (map (comma_crt_cofactor_or_false level digit) columns) (children!digit)) \<Longrightarrow>
     comma_semantic_b1_crt_labelled_zip_witness level columns
       (comma_crt_mdd_node level children)"

lemma comma_semantic_b1_crt_labelled_zip_node_from_pairs:
  assumes level: "level<4"
    and admitted: "list_all (comma_crt_admitted level) columns"
    and node: "comma_semantic_b1_crt_partition_has_node_at level columns"
    and children:
      "list_all2 (\<lambda>digit child.
        comma_semantic_b1_crt_labelled_zip_witness (Suc level)
          (map (comma_crt_cofactor_or_false level digit) columns) child)
        [0..<comma_crt_period level] children"
  shows "comma_semantic_b1_crt_labelled_zip_witness level columns
    (comma_crt_mdd_node level children)"
proof -
  have range_width: "length [0..<comma_crt_period level] = length children"
    using list_all2_lengthD[OF children] .
  have width: "length children=comma_crt_period level"
    using range_width by simp
  have branch:
    "\<And>digit. digit<comma_crt_period level \<Longrightarrow>
      comma_semantic_b1_crt_labelled_zip_witness (Suc level)
        (map (comma_crt_cofactor_or_false level digit) columns) (children!digit)"
  proof -
    fix digit
    assume digit: "digit<comma_crt_period level"
    have in_range: "digit<length [0..<comma_crt_period level]"
      using digit by simp
    have paired:
      "comma_semantic_b1_crt_labelled_zip_witness (Suc level)
        (map (comma_crt_cofactor_or_false level ([0..<comma_crt_period level]!digit))
          columns) (children!digit)"
      using children in_range by (rule list_all2_nthD)
    show "comma_semantic_b1_crt_labelled_zip_witness (Suc level)
        (map (comma_crt_cofactor_or_false level digit) columns) (children!digit)"
      using paired digit by simp
  qed
  show ?thesis
    by (rule labelled_zip_node[OF level admitted node width branch])
qed

lemma comma_semantic_b1_crt_labelled_zip_node_from_children:
  assumes level: "level<4"
    and admitted: "list_all (comma_crt_admitted level) columns"
    and node: "comma_semantic_b1_crt_partition_has_node_at level columns"
    and width: "length children=comma_crt_period level"
    and children:
      "list_all (\<lambda>digit.
        comma_semantic_b1_crt_labelled_zip_witness (Suc level)
          (map (comma_crt_cofactor_or_false level digit) columns) (children!digit))
        [0..<comma_crt_period level]"
  shows "comma_semantic_b1_crt_labelled_zip_witness level columns
    (comma_crt_mdd_node level children)"
proof -
  let ?branches = "\<lambda>digit child.
    comma_semantic_b1_crt_labelled_zip_witness (Suc level)
      (map (comma_crt_cofactor_or_false level digit) columns) child"
  have paired: "list_all2 ?branches [0..<comma_crt_period level] children"
    using children width
    by (simp add: list_all2_conv_all_nth list_all_iff)
  show ?thesis
    by (rule comma_semantic_b1_crt_labelled_zip_node_from_pairs
      [OF level admitted node paired])
qed

lemma comma_semantic_b1_crt_labelled_zip_terminal_from_columns:
  assumes index: "index<length columns"
    and code:
      "columns=map (\<lambda>i. Comma_CRT_Bool (i=index)) [0..<length columns]"
  shows "comma_semantic_b1_crt_labelled_zip_witness level columns
    (Comma_CRT_MDD_Leaf (Some index))"
proof (rule labelled_zip_terminal[OF index])
  fix i
  assume i: "i<length columns"
  have index_range: "i<length [0..<length columns]"
    using i by simp
  have nth_code:
      "columns!i=(map (\<lambda>j. Comma_CRT_Bool (j=index))
        [0..<length columns])!i"
    by (rule arg_cong[where f="\<lambda>row. row!i", OF code])
  have nth_map_value:
      "(map (\<lambda>j. Comma_CRT_Bool (j=index))
        [0..<length columns])!i=Comma_CRT_Bool (i=index)"
    using index_range by (simp add: nth_map)
  show "columns!i=Comma_CRT_Bool (i=index)"
    using nth_code nth_map_value by simp
qed

lemma comma_semantic_b1_crt_labelled_zip_witness_sound_all:
  assumes witness:
    "comma_semantic_b1_crt_labelled_zip_witness level columns selector"
  shows "list_all (comma_crt_admitted level) columns \<and>
    comma_crt_mdd_admitted level selector \<and>
    (\<forall>i<length columns. \<forall>phase.
      comma_crt_eval phase (comma_semantic_b1_crt_label_fiber i selector) =
      comma_crt_eval phase (columns!i)) \<and>
    comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns"
  using witness
proof (induction rule: comma_semantic_b1_crt_labelled_zip_witness.induct)
  case (labelled_zip_terminal index columns level)
  have columns_admitted: "list_all (comma_crt_admitted level) columns"
  proof (unfold list_all_iff)
    show "\<forall>column\<in>set columns. comma_crt_admitted level column"
    proof (intro ballI)
      fix column
      assume member: "column\<in>set columns"
      then obtain i where bound: "i<length columns" and column:
          "column=columns!i"
        by (auto simp: in_set_conv_nth)
      have one_hot:
          "columns!i=Comma_CRT_Bool (i=index)"
        by (rule labelled_zip_terminal.hyps(2)[OF bound])
      show "comma_crt_admitted level column"
        using column one_hot by simp
    qed
  qed
  have checked:
    "comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns"
    by (rule comma_semantic_b1_crt_label_terminal_checker
        [OF labelled_zip_terminal.hyps(1) labelled_zip_terminal.hyps(2)])
  show ?case
  proof (intro conjI)
    show "list_all (comma_crt_admitted level) columns"
      using columns_admitted .
    show "comma_crt_mdd_admitted level (Comma_CRT_MDD_Leaf (Some index))"
      by simp
    show "\<forall>i<length columns. \<forall>phase.
        comma_crt_eval phase
          (comma_semantic_b1_crt_label_fiber i (Comma_CRT_MDD_Leaf (Some index))) =
        comma_crt_eval phase (columns!i)"
    proof (intro allI impI allI)
      fix i phase
      assume i: "i<length columns"
      have column: "columns!i=Comma_CRT_Bool (i=index)"
        by (rule labelled_zip_terminal.hyps(2)[OF i])
      show "comma_crt_eval phase
          (comma_semantic_b1_crt_label_fiber i (Comma_CRT_MDD_Leaf (Some index))) =
        comma_crt_eval phase (columns!i)"
        using column by (simp add: comma_semantic_b1_crt_label_fiber.simps eq_commute)
    qed
    show "comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns"
      using checked .
  qed
next
  case (labelled_zip_skip level columns selector)
  have rec_columns:
      "list_all (comma_crt_admitted (Suc level)) columns"
    using labelled_zip_skip.IH by (rule conjunct1)
  have rec_selector: "comma_crt_mdd_admitted (Suc level) selector"
    using labelled_zip_skip.IH by (rule conjunct1[OF conjunct2])
  have rec_fiber: "\<forall>i<length columns. \<forall>phase.
        comma_crt_eval phase (comma_semantic_b1_crt_label_fiber i selector) =
        comma_crt_eval phase (columns!i)"
    using labelled_zip_skip.IH
    by (rule conjunct1[OF conjunct2[OF conjunct2]])
  have rec_checker:
      "comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4] columns"
    using labelled_zip_skip.IH
    by (rule conjunct2[OF conjunct2[OF conjunct2]])
  have selector_admitted: "comma_crt_mdd_admitted level selector"
    using comma_crt_mdd_admitted_mono[OF _ rec_selector] by simp
  have branches:
    "\<And>digit. digit<comma_crt_period level \<Longrightarrow>
      comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4]
        (map (comma_crt_cofactor_or_false level digit) columns)"
  proof -
    fix digit
    assume digit: "digit<comma_crt_period level"
    have unchanged:
      "map (comma_crt_cofactor_or_false level digit) columns=columns"
      by (rule comma_semantic_b1_crt_partition_no_node_cofactor_identity
          [OF labelled_zip_skip.hyps(1,2,3)])
    show "comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4]
        (map (comma_crt_cofactor_or_false level digit) columns)"
      using rec_checker unchanged by simp
  qed
  have checked:
    "comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns"
    by (rule comma_semantic_b1_crt_partition_cofactor_step
        [OF labelled_zip_skip.hyps(1,2) branches])
  show ?case
  proof (intro conjI)
    show "list_all (comma_crt_admitted level) columns"
      using labelled_zip_skip.hyps(2) .
    show "comma_crt_mdd_admitted level selector" using selector_admitted .
    show "\<forall>i<length columns. \<forall>phase.
        comma_crt_eval phase (comma_semantic_b1_crt_label_fiber i selector) =
        comma_crt_eval phase (columns!i)"
      using rec_fiber .
    show "comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns"
      using checked .
  qed
next
  case (labelled_zip_node level columns children)
  have child_facts:
    "list_all (comma_crt_admitted (Suc level))
        (map (comma_crt_cofactor_or_false level digit) columns) \<and>
     comma_crt_mdd_admitted (Suc level) (children!digit) \<and>
     (\<forall>i<length (map (comma_crt_cofactor_or_false level digit) columns).
       \<forall>phase.
        comma_crt_eval phase
          (comma_semantic_b1_crt_label_fiber i (children!digit)) =
        comma_crt_eval phase
          (map (comma_crt_cofactor_or_false level digit) columns ! i)) \<and>
     comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4]
       (map (comma_crt_cofactor_or_false level digit) columns)"
    if digit: "digit<comma_crt_period level" for digit
    using labelled_zip_node.IH[OF digit] .
  have children_admitted:
    "list_all (comma_crt_mdd_admitted (Suc level)) children"
  proof (simp add: list_all_iff, intro ballI)
    fix child
    assume child_in: "child\<in>set children"
    then obtain digit where digit_bound: "digit<length children"
      and child: "child=children!digit"
      by (auto simp: in_set_conv_nth)
    have digit: "digit<comma_crt_period level"
      using digit_bound labelled_zip_node.hyps(4) by simp
    have child_admitted:
      "comma_crt_mdd_admitted (Suc level) (children!digit)"
      using child_facts[OF digit] by (rule conjunct1[OF conjunct2])
    show "comma_crt_mdd_admitted (Suc level) child"
      using child_admitted child by simp
  qed
  have branch_exact:
    "\<And>digit i phase. digit<comma_crt_period level \<Longrightarrow>
       i<length columns \<Longrightarrow>
       comma_crt_eval phase
         (comma_semantic_b1_crt_label_fiber i (children!digit)) =
       comma_crt_eval phase
         (comma_crt_cofactor_or_false level digit (columns!i))"
  proof -
    fix digit i phase
    assume digit: "digit<comma_crt_period level"
      and i: "i<length columns"
    have facts: "(\<forall>j<length (map (comma_crt_cofactor_or_false level digit) columns).
        \<forall>p. comma_crt_eval p
          (comma_semantic_b1_crt_label_fiber j (children!digit)) =
        comma_crt_eval p
          (map (comma_crt_cofactor_or_false level digit) columns ! j))"
      using child_facts[OF digit]
      by (rule conjunct1[OF conjunct2[OF conjunct2]])
    have at_i_imp:
      "i<length (map (comma_crt_cofactor_or_false level digit) columns) \<longrightarrow>
       (\<forall>p. comma_crt_eval p
          (comma_semantic_b1_crt_label_fiber i (children!digit)) =
        comma_crt_eval p
          (map (comma_crt_cofactor_or_false level digit) columns ! i))"
      by (rule spec[OF facts])
    have at_i:
      "\<forall>p. comma_crt_eval p
          (comma_semantic_b1_crt_label_fiber i (children!digit)) =
        comma_crt_eval p
          (map (comma_crt_cofactor_or_false level digit) columns ! i)"
    proof -
      have mapped_bound:
        "i<length (map (comma_crt_cofactor_or_false level digit) columns)"
        using i by simp
      show ?thesis using at_i_imp mapped_bound by (rule mp)
    qed
    have facts_i: "\<forall>p. comma_crt_eval p
        (comma_semantic_b1_crt_label_fiber i (children!digit)) =
      comma_crt_eval p
        (map (comma_crt_cofactor_or_false level digit) columns ! i)"
      using at_i .
    have at_phase:
      "comma_crt_eval phase
          (comma_semantic_b1_crt_label_fiber i (children!digit)) =
       comma_crt_eval phase
          (map (comma_crt_cofactor_or_false level digit) columns ! i)"
      by (rule spec[OF facts_i])
    show "comma_crt_eval phase
        (comma_semantic_b1_crt_label_fiber i (children!digit)) =
      comma_crt_eval phase
        (comma_crt_cofactor_or_false level digit (columns!i))"
      using at_phase i by (simp add: nth_map)
  qed
  have node_admitted:
    "comma_crt_mdd_admitted level (comma_crt_mdd_node level children)"
    by (rule comma_semantic_b1_crt_label_node_fiber_exact(1)
      [OF labelled_zip_node.hyps(1,4) children_admitted labelled_zip_node.hyps(2)
        branch_exact])
  have node_fibers:
    "\<forall>i<length columns. \<forall>phase.
       comma_crt_eval phase
         (comma_semantic_b1_crt_label_fiber i (comma_crt_mdd_node level children)) =
       comma_crt_eval phase (columns!i)"
  proof (intro allI impI allI)
    fix i phase
    assume i: "i<length columns"
    show "comma_crt_eval phase
        (comma_semantic_b1_crt_label_fiber i (comma_crt_mdd_node level children)) =
        comma_crt_eval phase (columns!i)"
      by (rule comma_semantic_b1_crt_label_node_fiber_exact(2)
        [OF labelled_zip_node.hyps(1,4) children_admitted labelled_zip_node.hyps(2)
          branch_exact i])
  qed
  have branches:
    "\<And>digit. digit<comma_crt_period level \<Longrightarrow>
      comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4]
        (map (comma_crt_cofactor_or_false level digit) columns)"
  proof -
    fix digit
    assume digit: "digit<comma_crt_period level"
    show "comma_semantic_b1_crt_partition_cofactor_checked [Suc level..<4]
        (map (comma_crt_cofactor_or_false level digit) columns)"
      using child_facts[OF digit]
      by (rule conjunct2[OF conjunct2[OF conjunct2]])
  qed
  have checked:
    "comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns"
    by (rule comma_semantic_b1_crt_partition_cofactor_step
        [OF labelled_zip_node.hyps(1,2) branches])
  have selector_admitted:
    "comma_crt_mdd_admitted level (comma_crt_mdd_node level children)"
    using node_admitted .
  show ?case
  proof (intro conjI)
    show "list_all (comma_crt_admitted level) columns"
      using labelled_zip_node.hyps(2) .
    show "comma_crt_mdd_admitted level (comma_crt_mdd_node level children)"
      using selector_admitted .
    show "\<forall>i<length columns. \<forall>phase.
        comma_crt_eval phase
          (comma_semantic_b1_crt_label_fiber i (comma_crt_mdd_node level children)) =
        comma_crt_eval phase (columns!i)"
      using node_fibers .
    show "comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns"
      using checked .
  qed
qed

ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_labelled_zip_witness_sound_all}];
\<close>

lemma comma_semantic_b1_crt_labelled_zip_witness_sound:
  assumes witness:
    "comma_semantic_b1_crt_labelled_zip_witness level columns selector"
  shows "list_all (comma_crt_admitted level) columns"
    "comma_crt_mdd_admitted level selector"
    "\<And>i phase. i<length columns \<Longrightarrow>
      comma_crt_eval phase (comma_semantic_b1_crt_label_fiber i selector) =
      comma_crt_eval phase (columns!i)"
    "comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns"
proof -
  have facts:
      "list_all (comma_crt_admitted level) columns \<and>
       comma_crt_mdd_admitted level selector \<and>
       (\<forall>i<length columns. \<forall>phase.
          comma_crt_eval phase (comma_semantic_b1_crt_label_fiber i selector) =
          comma_crt_eval phase (columns!i)) \<and>
       comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns"
    by (rule comma_semantic_b1_crt_labelled_zip_witness_sound_all[OF witness])
  show "list_all (comma_crt_admitted level) columns"
    using facts by (rule conjunct1)
  show "comma_crt_mdd_admitted level selector"
    using facts by (rule conjunct1[OF conjunct2])
  show "\<And>i phase. i<length columns \<Longrightarrow>
      comma_crt_eval phase (comma_semantic_b1_crt_label_fiber i selector) =
      comma_crt_eval phase (columns!i)"
  proof -
    fix i phase
    assume i: "i<length columns"
    have fibers:
      "\<forall>j<length columns. \<forall>p.
        comma_crt_eval p (comma_semantic_b1_crt_label_fiber j selector) =
        comma_crt_eval p (columns!j)"
      using facts by (rule conjunct1[OF conjunct2[OF conjunct2]])
    have at_i_imp:
      "i<length columns \<longrightarrow> (\<forall>p.
        comma_crt_eval p (comma_semantic_b1_crt_label_fiber i selector) =
        comma_crt_eval p (columns!i))"
      by (rule spec[OF fibers])
    have at_i:
      "\<forall>p. comma_crt_eval p
        (comma_semantic_b1_crt_label_fiber i selector) =
        comma_crt_eval p (columns!i)"
      using at_i_imp i by (rule mp)
    show "comma_crt_eval phase
        (comma_semantic_b1_crt_label_fiber i selector) =
        comma_crt_eval phase (columns!i)"
      by (rule spec[OF at_i])
  qed
  show "comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns"
    using facts by (rule conjunct2[OF conjunct2[OF conjunct2]])
qed

lemma comma_semantic_b1_crt_labelled_zip_witness_checker_true:
  assumes witness:
    "comma_semantic_b1_crt_labelled_zip_witness level columns selector"
  shows "comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns=True"
proof -
  have checked:
      "comma_semantic_b1_crt_partition_cofactor_checked [level..<4] columns"
    using comma_semantic_b1_crt_labelled_zip_witness_sound_all[OF witness]
    by (rule conjunct2[OF conjunct2[OF conjunct2]])
  show ?thesis by (rule eqTrueI[OF checked])
qed

lemma comma_semantic_b1_crt_labelled_zip_witness_fiber_exact:
  assumes witness:
    "comma_semantic_b1_crt_labelled_zip_witness level columns selector"
  shows "\<forall>i<length columns. \<forall>phase.
    comma_crt_eval phase (comma_semantic_b1_crt_label_fiber i selector) =
    comma_crt_eval phase (columns!i)"
  using comma_semantic_b1_crt_labelled_zip_witness_sound_all[OF witness]
  by (rule conjunct1[OF conjunct2[OF conjunct2]])

corollary comma_semantic_b1_crt_labelled_zip_witness_certified:
  assumes witness:
    "comma_semantic_b1_crt_labelled_zip_witness 0 columns selector"
  shows "comma_semantic_b1_crt_columns_partition_certified columns"
    "comma_crt_mdd_admitted 0 selector"
    "\<And>i phase. i<length columns \<Longrightarrow>
      comma_crt_eval phase (comma_semantic_b1_crt_label_fiber i selector) =
      comma_crt_eval phase (columns!i)"
proof -
  have facts:
      "list_all (comma_crt_admitted 0) columns \<and>
       comma_crt_mdd_admitted 0 selector \<and>
       (\<forall>i<length columns. \<forall>phase.
          comma_crt_eval phase (comma_semantic_b1_crt_label_fiber i selector) =
          comma_crt_eval phase (columns!i)) \<and>
       comma_semantic_b1_crt_partition_cofactor_checked [0..<4] columns"
    by (rule comma_semantic_b1_crt_labelled_zip_witness_sound_all[OF witness])
  have columns_admitted: "list_all (comma_crt_admitted 0) columns"
    using facts by (rule conjunct1)
  have selector_admitted: "comma_crt_mdd_admitted 0 selector"
    using facts by (rule conjunct1[OF conjunct2])
  have fibers:
      "\<forall>i<length columns. \<forall>phase.
        comma_crt_eval phase (comma_semantic_b1_crt_label_fiber i selector) =
        comma_crt_eval phase (columns!i)"
    using facts by (rule conjunct1[OF conjunct2[OF conjunct2]])
  have checked:
      "comma_semantic_b1_crt_partition_cofactor_checked [0..<4] columns"
    using facts by (rule conjunct2[OF conjunct2[OF conjunct2]])
  show "comma_semantic_b1_crt_columns_partition_certified columns"
    unfolding comma_semantic_b1_crt_columns_partition_certified_def
    by (rule conjI[OF columns_admitted checked])
  show "comma_crt_mdd_admitted 0 selector" using selector_admitted .
  show "\<And>i phase. i<length columns \<Longrightarrow>
      comma_crt_eval phase (comma_semantic_b1_crt_label_fiber i selector) =
      comma_crt_eval phase (columns!i)"
  proof -
    fix i phase
    assume i: "i<length columns"
    have at_i_imp:
      "i<length columns \<longrightarrow> (\<forall>p.
        comma_crt_eval p (comma_semantic_b1_crt_label_fiber i selector) =
        comma_crt_eval p (columns!i))"
      by (rule spec[OF fibers])
    have at_i:
      "\<forall>p. comma_crt_eval p
        (comma_semantic_b1_crt_label_fiber i selector) =
        comma_crt_eval p (columns!i)"
      using at_i_imp i by (rule mp)
    show "comma_crt_eval phase
        (comma_semantic_b1_crt_label_fiber i selector) =
        comma_crt_eval phase (columns!i)"
      by (rule spec[OF at_i])
  qed
qed

lemmas comma_semantic_b1_crt_labelled_selector_oracle_audit_bundle =
  comma_semantic_b1_crt_label_fiber_admitted
  comma_semantic_b1_crt_label_fiber_eval
  comma_semantic_b1_crt_label_terminal_fiber_exact
  comma_semantic_b1_crt_label_node_fiber_exact
  comma_semantic_b1_crt_labelled_zip_terminal_from_columns
  comma_semantic_b1_crt_labelled_zip_node_from_pairs
  comma_semantic_b1_crt_labelled_zip_node_from_children
  comma_semantic_b1_crt_labelled_zip_witness_sound_all
  comma_semantic_b1_crt_labelled_zip_witness_sound
  comma_semantic_b1_crt_labelled_zip_witness_checker_true
  comma_semantic_b1_crt_labelled_zip_witness_fiber_exact
  comma_semantic_b1_crt_labelled_zip_witness_certified

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_labelled_selector_oracle_audit_bundle}
  val _ = Thm.consolidate checked
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Comma labelled selector proof bundle depends on an oracle"
\<close>

end
