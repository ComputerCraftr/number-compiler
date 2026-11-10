theory Comma_CRT_Equivalence
  imports Comma_CRT_Power
begin

text \<open>
Structural equivalence checks for admitted CRT columns.  The checker never
constructs a clock-phase list.  It negates the ordered decision tree and
tests both directional differences with the existing matched-cofactor apply
and structural support checker.  Admission is part of the Boolean result, so
malformed trees cannot compare equivalent, including a malformed tree against
itself.
\<close>

primrec comma_crt_negate :: "comma_crt_column \<Rightarrow> comma_crt_column" where
  "comma_crt_negate (Comma_CRT_Bool value) = Comma_CRT_Bool (\<not> value)"
| "comma_crt_negate (Comma_CRT_Node level children) =
    Comma_CRT_Node level (map comma_crt_negate children)"

lemma comma_crt_negate_admitted:
  assumes admitted: "comma_crt_admitted lower column"
  shows "comma_crt_admitted lower (comma_crt_negate column)"
  using admitted
  by (induction column arbitrary: lower)
     (auto simp: list_all_iff)

lemma comma_crt_negate_eval:
  assumes admitted: "comma_crt_admitted lower column"
  shows "comma_crt_eval phase (comma_crt_negate column) =
    (\<not> comma_crt_eval phase column)"
  using admitted
proof (induction column arbitrary: lower phase)
  case (Comma_CRT_Bool bit)
  then show ?case by simp
next
  case (Comma_CRT_Node level children)
  have level_bound: "lower \<le> level"
    and level_valid: "level<4"
    and width: "length children=comma_crt_period level"
    and children_valid:
      "\<forall>child\<in>set children. comma_crt_admitted (Suc level) child"
    using Comma_CRT_Node.prems by (auto simp: list_all_iff)
  have index: "phase mod comma_crt_period level < length children"
    using width comma_crt_period_positive[OF level_valid] by simp
  have child_valid:
      "comma_crt_admitted (Suc level)
        (children!(phase mod comma_crt_period level))"
    using children_valid nth_mem[OF index] by blast
  have child_negation:
      "comma_crt_eval phase
          (comma_crt_negate (children!(phase mod comma_crt_period level))) =
        (\<not> comma_crt_eval phase (children!(phase mod comma_crt_period level)))"
    by (rule Comma_CRT_Node.IH[OF nth_mem[OF index] child_valid])
  show ?case
    using level_bound level_valid width index child_negation
    by (simp add: nth_map)
qed

lemma comma_crt_negate_set:
  assumes admitted: "comma_crt_admitted 0 column"
  shows "comma_crt_set (comma_crt_negate column) =
    {phase. phase<924 \<and> phase\<notin>comma_crt_set column}"
  using comma_crt_negate_eval[OF admitted, of _]
  by (auto simp: comma_crt_set_def)

definition comma_crt_equiv_check ::
    "comma_crt_column \<Rightarrow> comma_crt_column \<Rightarrow> bool" where
  "comma_crt_equiv_check left right \<longleftrightarrow>
    comma_crt_admitted 0 left \<and> comma_crt_admitted 0 right \<and>
    \<not> comma_crt_supported
      (comma_crt_apply Comma_CRT_And left (comma_crt_negate right)) \<and>
    \<not> comma_crt_supported
      (comma_crt_apply Comma_CRT_And right (comma_crt_negate left))"

lemma comma_crt_equiv_check_admitted_iff:
  assumes left: "comma_crt_admitted 0 left"
    and right: "comma_crt_admitted 0 right"
  shows "comma_crt_equiv_check left right \<longleftrightarrow>
    comma_crt_set left=comma_crt_set right"
proof -
  have left_neg_admitted:
      "comma_crt_admitted 0 (comma_crt_negate left)"
    by (rule comma_crt_negate_admitted[OF left])
  have right_neg_admitted:
      "comma_crt_admitted 0 (comma_crt_negate right)"
    by (rule comma_crt_negate_admitted[OF right])
  have left_difference_admitted:
      "comma_crt_admitted 0
        (comma_crt_apply Comma_CRT_And left (comma_crt_negate right))"
    by (rule comma_crt_apply_admitted[OF left right_neg_admitted])
  have right_difference_admitted:
      "comma_crt_admitted 0
        (comma_crt_apply Comma_CRT_And right (comma_crt_negate left))"
    by (rule comma_crt_apply_admitted[OF right left_neg_admitted])
  have left_difference:
      "comma_crt_set (comma_crt_apply Comma_CRT_And left
          (comma_crt_negate right)) = comma_crt_set left - comma_crt_set right"
    using comma_crt_apply_and_set[OF left right_neg_admitted]
      comma_crt_negate_set[OF right]
    by (auto simp: comma_crt_set_def)
  have right_difference:
      "comma_crt_set (comma_crt_apply Comma_CRT_And right
          (comma_crt_negate left)) = comma_crt_set right - comma_crt_set left"
    using comma_crt_apply_and_set[OF right left_neg_admitted]
      comma_crt_negate_set[OF left]
    by (auto simp: comma_crt_set_def)
  have left_difference_empty:
      "\<not> comma_crt_supported
          (comma_crt_apply Comma_CRT_And left (comma_crt_negate right)) \<longleftrightarrow>
        comma_crt_set left - comma_crt_set right={}"
    using comma_crt_supported_nonempty[OF left_difference_admitted]
      left_difference by auto
  have right_difference_empty:
      "\<not> comma_crt_supported
          (comma_crt_apply Comma_CRT_And right (comma_crt_negate left)) \<longleftrightarrow>
        comma_crt_set right - comma_crt_set left={}"
    using comma_crt_supported_nonempty[OF right_difference_admitted]
      right_difference by auto
  show ?thesis
    unfolding comma_crt_equiv_check_def
    using left right left_difference_empty right_difference_empty
    by auto
qed

lemma comma_crt_equiv_check_iff:
  "comma_crt_equiv_check left right \<longleftrightarrow>
    comma_crt_admitted 0 left \<and> comma_crt_admitted 0 right \<and>
    comma_crt_set left=comma_crt_set right"
proof (cases "comma_crt_admitted 0 left")
  case False
  then show ?thesis by (simp add: comma_crt_equiv_check_def)
next
  case True
  note left_admitted = True
  show ?thesis
  proof (cases "comma_crt_admitted 0 right")
    case False
    then show ?thesis by (simp add: comma_crt_equiv_check_def)
  next
    case True
    note right_admitted = True
    have "comma_crt_equiv_check left right \<longleftrightarrow>
        comma_crt_set left=comma_crt_set right"
      by (rule comma_crt_equiv_check_admitted_iff[OF left_admitted right_admitted])
    with left_admitted right_admitted show ?thesis by simp
  qed
qed

lemma comma_crt_equiv_check_sound:
  assumes equivalent: "comma_crt_equiv_check left right"
  shows "comma_crt_set left=comma_crt_set right"
  using comma_crt_equiv_check_iff[of left right] equivalent by blast

lemma comma_crt_equiv_check_supported:
  assumes equivalent: "comma_crt_equiv_check left right"
  shows "comma_crt_supported left = comma_crt_supported right"
proof -
  have left_admitted: "comma_crt_admitted 0 left"
    and right_admitted: "comma_crt_admitted 0 right"
    and equal_sets: "comma_crt_set left=comma_crt_set right"
    using comma_crt_equiv_check_iff[of left right] equivalent by blast+
  have left_nonempty:
    "comma_crt_set left\<noteq>{} \<longleftrightarrow> comma_crt_supported left"
    by (rule comma_crt_supported_nonempty[OF left_admitted])
  have right_nonempty:
    "comma_crt_set right\<noteq>{} \<longleftrightarrow> comma_crt_supported right"
    by (rule comma_crt_supported_nonempty[OF right_admitted])
  show ?thesis using left_nonempty right_nonempty equal_sets by blast
qed

lemma comma_crt_equiv_check_complete:
  assumes left: "comma_crt_admitted 0 left"
    and right: "comma_crt_admitted 0 right"
    and equal: "comma_crt_set left=comma_crt_set right"
  shows "comma_crt_equiv_check left right"
  using comma_crt_equiv_check_iff[of left right] left right equal by blast

lemma comma_crt_equiv_check_refl:
  assumes "comma_crt_admitted 0 column"
  shows "comma_crt_equiv_check column column"
  using assms by (simp only: comma_crt_equiv_check_iff)

lemma comma_crt_equiv_check_trans:
  assumes "comma_crt_equiv_check left middle"
    and "comma_crt_equiv_check middle right"
  shows "comma_crt_equiv_check left right"
  using assms by (auto simp only: comma_crt_equiv_check_iff)

text \<open>Consume certified child equivalences before constructing a parent.
These laws transport admission and denotation; they do not run the executable
equivalence checker over either child's expanded construction.\<close>

lemma comma_crt_equiv_check_apply:
  assumes left: "comma_crt_equiv_check left left'"
    and right: "comma_crt_equiv_check right right'"
  shows "comma_crt_equiv_check
    (comma_crt_apply operation left right)
    (comma_crt_apply operation left' right')"
proof -
  have admitted:
    "comma_crt_admitted 0 left" "comma_crt_admitted 0 left'"
    "comma_crt_admitted 0 right" "comma_crt_admitted 0 right'"
    and equal:
    "comma_crt_set left=comma_crt_set left'"
    "comma_crt_set right=comma_crt_set right'"
    using left right by (auto simp only: comma_crt_equiv_check_iff)
  have parent: "comma_crt_admitted 0 (comma_crt_apply operation left right)"
    by (rule comma_crt_apply_admitted[OF admitted(1,3)])
  have parent': "comma_crt_admitted 0 (comma_crt_apply operation left' right')"
    by (rule comma_crt_apply_admitted[OF admitted(2,4)])
  have sets: "comma_crt_set (comma_crt_apply operation left right) =
      comma_crt_set (comma_crt_apply operation left' right')"
    using equal
    by (cases operation)
      (simp_all only: comma_crt_apply_and_set[OF admitted(1,3)]
        comma_crt_apply_and_set[OF admitted(2,4)]
        comma_crt_apply_or_set[OF admitted(1,3)]
        comma_crt_apply_or_set[OF admitted(2,4)])
  show ?thesis
    by (rule comma_crt_equiv_check_complete[OF parent parent' sets])
qed

lemma comma_crt_equiv_check_shift:
  assumes equivalent: "comma_crt_equiv_check left right"
  shows "comma_crt_equiv_check
    (comma_crt_shift clock left) (comma_crt_shift clock right)"
proof -
  have left: "comma_crt_admitted 0 left"
    and right: "comma_crt_admitted 0 right"
    and equal: "comma_crt_set left=comma_crt_set right"
    using equivalent by (auto simp only: comma_crt_equiv_check_iff)
  have shifted_left: "comma_crt_admitted 0 (comma_crt_shift clock left)"
    by (rule comma_crt_shift_admitted[OF left])
  have shifted_right: "comma_crt_admitted 0 (comma_crt_shift clock right)"
    by (rule comma_crt_shift_admitted[OF right])
  have sets: "comma_crt_set (comma_crt_shift clock left) =
      comma_crt_set (comma_crt_shift clock right)"
    by (simp only: comma_crt_shift_column_exact[OF left]
        comma_crt_shift_column_exact[OF right] equal)
  show ?thesis
    by (rule comma_crt_equiv_check_complete[OF shifted_left shifted_right sets])
qed

text \<open>
The row relation preserves the output label.  This is deliberately stronger
than equality of unlabeled partitions: a candidate column can only stand for
the provider column carrying the same Live, Stop, or Invalid result.
\<close>

definition comma_crt_labeled_rows_equivalent ::
    "comma_crt_return_row list \<Rightarrow> comma_crt_return_row list \<Rightarrow> bool" where
  "comma_crt_labeled_rows_equivalent candidate provider \<longleftrightarrow>
    list_all2 (\<lambda>row other. snd row=snd other \<and>
      comma_crt_equiv_check (fst row) (fst other)) candidate provider"

lemma comma_crt_labeled_rows_equivalent_projection:
  assumes equivalent: "comma_crt_labeled_rows_equivalent candidate provider"
  shows "map comma_crt_project_row candidate = map comma_crt_project_row provider"
  using equivalent unfolding comma_crt_labeled_rows_equivalent_def
proof (induction rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons row rows other others)
  have columns: "comma_crt_set (fst row)=comma_crt_set (fst other)"
    using Cons.hyps(1) comma_crt_equiv_check_sound by blast
  have labels: "snd row=snd other" using Cons.hyps(1) by blast
  show ?case
    using columns labels Cons.IH by (simp add: comma_crt_project_row_def)
qed

lemma comma_crt_labeled_rows_equivalent_table_transfer:
  assumes provider_exact:
      "comma_semantic_b1_binding_table_exact action shift
        (map comma_crt_project_row provider)"
    and equivalent: "comma_crt_labeled_rows_equivalent candidate provider"
  shows "comma_semantic_b1_binding_table_exact action shift
    (map comma_crt_project_row candidate)"
  using provider_exact
  by (simp only: comma_crt_labeled_rows_equivalent_projection[OF equivalent])

lemma comma_crt_exact_rows_group_column_fiber:
  assumes labels: "distinct (map snd rows)"
    and exact_rows: "\<forall>row\<in>set rows.
      comma_semantic_b1_binding_row_exact action 0
        (comma_crt_project_row row)"
    and covered: "(\<Union> (fst ` set (map comma_crt_project_row rows)))={..<924}"
  shows "comma_crt_set (comma_crt_group_column outcome rows) =
    {phase. phase<924 \<and> action phase=outcome}"
proof (rule set_eqI)
  fix phase :: nat
  show "phase \<in> comma_crt_set (comma_crt_group_column outcome rows) \<longleftrightarrow>
      phase \<in> {phase. phase<924 \<and> action phase=outcome}"
  proof
    assume member: "phase \<in> comma_crt_set
        (comma_crt_group_column outcome rows)"
    have nonempty: "comma_crt_set (comma_crt_group_column outcome rows) \<noteq> {}"
      using member by blast
    obtain row where row: "row\<in>set rows" "snd row=outcome"
      using comma_crt_group_column_nonempty_member[OF nonempty] by blast
    have selected_column:
      "comma_crt_group_column (snd row) rows=fst row"
      by (rule comma_crt_group_column_member[OF labels row(1)])
    have column: "comma_crt_group_column outcome rows=fst row"
      using selected_column row(2) by simp
    have row_exact:
      "comma_semantic_b1_binding_row_exact action 0
        (comma_crt_project_row row)"
      using exact_rows row(1) by blast
    have phase_exact:
      "comma_crt_set (fst row) = {phase. phase<924 \<and> action phase=snd row}"
      using row_exact
      by (simp only: comma_semantic_b1_binding_row_exact_zero_iff
        comma_crt_project_row_def fst_conv snd_conv)
    show "phase \<in> {phase. phase<924 \<and> action phase=outcome}"
      using member column phase_exact row(2) by simp
  next
    assume phase: "phase \<in> {phase. phase<924 \<and> action phase=outcome}"
    then have phase_bound: "phase<924"
      and output_value: "action phase=outcome"
      by auto
    have phase_covered:
      "phase\<in>(\<Union> (fst ` set (map comma_crt_project_row rows)))"
      using covered phase_bound by simp
    then obtain cell where cell_in:
        "cell\<in>fst ` set (map comma_crt_project_row rows)"
      and phase_in_cell: "phase\<in>cell"
      by blast
    obtain projected where projected_in:
        "projected\<in>set (map comma_crt_project_row rows)"
      and cell_eq: "cell=fst projected"
      using cell_in by blast
    obtain row where row: "row\<in>set rows"
      and projected_eq: "projected=comma_crt_project_row row"
      using projected_in by auto
    have phase_column: "phase\<in>fst (comma_crt_project_row row)"
      using phase_in_cell cell_eq projected_eq by simp
    have row_exact:
      "comma_semantic_b1_binding_row_exact action 0
        (comma_crt_project_row row)"
      using exact_rows row by blast
    have row_value: "snd row=action phase"
      using row_exact phase_column phase_bound
      by (auto simp: comma_semantic_b1_binding_row_exact_zero_iff
          comma_crt_project_row_def comma_crt_set_def)
    have label: "snd row=outcome" using row_value output_value by simp
    have selected_column:
      "comma_crt_group_column (snd row) rows=fst row"
      by (rule comma_crt_group_column_member[OF labels row(1)])
    have column: "comma_crt_group_column outcome rows=fst row"
      using selected_column label by simp
    show "phase \<in> comma_crt_set (comma_crt_group_column outcome rows)"
      using phase_column column by (simp add: comma_crt_project_row_def)
  qed
qed

lemma comma_crt_exact_table_from_fibers:
  fixes action :: "nat \<Rightarrow> comma_semantic_b1_result"
  assumes admitted: "comma_crt_rows_admitted rows"
    and supported: "\<forall>row\<in>set rows. comma_crt_supported (fst row)"
    and labels: "distinct (map snd rows)"
    and fibers: "\<And>outcome. comma_crt_set
      (comma_crt_group_column outcome rows) =
      {phase. phase<924 \<and> action phase=outcome}"
  shows "comma_semantic_b1_binding_table_exact action 0
    (map comma_crt_project_row rows)"
proof -
  have rows_distinct: "distinct rows"
    using labels by (simp add: distinct_map)
  have labels_injective: "inj_on snd (set rows)"
    using labels by (simp add: distinct_map)
  have row_exact:
    "\<forall>row\<in>set rows. comma_semantic_b1_binding_row_exact action 0
      (comma_crt_project_row row)"
  proof (intro ballI impI)
    fix row
    assume row: "row\<in>set rows"
    have row_admitted: "comma_crt_admitted 0 (fst row)"
      using admitted row by (auto simp: comma_crt_rows_admitted_def)
    have row_supported: "comma_crt_supported (fst row)"
      using supported row by blast
    have row_nonempty: "comma_crt_set (fst row)\<noteq>{}"
      using comma_crt_supported_nonempty[OF row_admitted] row_supported by blast
    have group_column:
      "comma_crt_group_column (snd row) rows=fst row"
      by (rule comma_crt_group_column_member[OF labels row])
    have fiber:
      "comma_crt_set (fst row) =
        {phase. phase<924 \<and> action phase=snd row}"
      using fibers[of "snd row"] group_column by simp
    show "comma_semantic_b1_binding_row_exact action 0
        (comma_crt_project_row row)"
      using row_nonempty fiber
      by (simp add: comma_semantic_b1_binding_row_exact_zero_iff
          comma_crt_project_row_def)
  qed
  have geometry_injective:
    "inj_on (\<lambda>row. comma_crt_set (fst row)) (set rows)"
  proof (rule inj_onI)
    fix left right
    assume left: "left\<in>set rows" and right: "right\<in>set rows"
      and same: "comma_crt_set (fst left)=comma_crt_set (fst right)"
    have left_admitted: "comma_crt_admitted 0 (fst left)"
      using admitted left by (auto simp: comma_crt_rows_admitted_def)
    have right_admitted: "comma_crt_admitted 0 (fst right)"
      using admitted right by (auto simp: comma_crt_rows_admitted_def)
    have left_supported: "comma_crt_supported (fst left)"
      using supported left by blast
    have left_nonempty: "comma_crt_set (fst left)\<noteq>{}"
      using comma_crt_supported_nonempty[OF left_admitted] left_supported by blast
    obtain phase where phase: "phase\<in>comma_crt_set (fst left)"
      using left_nonempty by blast
    have right_phase: "phase\<in>comma_crt_set (fst right)"
      using phase same by simp
    have left_exact: "comma_semantic_b1_binding_row_exact action 0
        (comma_crt_project_row left)"
      using row_exact left by blast
    have right_exact: "comma_semantic_b1_binding_row_exact action 0
        (comma_crt_project_row right)"
      using row_exact right by blast
    have left_fiber:
      "comma_crt_set (fst left) =
        {phase. phase<924 \<and> action phase=snd left}"
      using left_exact
      by (simp only: comma_semantic_b1_binding_row_exact_zero_iff
        comma_crt_project_row_def fst_conv snd_conv)
    have right_fiber:
      "comma_crt_set (fst right) =
        {phase. phase<924 \<and> action phase=snd right}"
      using right_exact
      by (simp only: comma_semantic_b1_binding_row_exact_zero_iff
        comma_crt_project_row_def fst_conv snd_conv)
    have left_value: "action phase=snd left"
      using phase left_fiber by blast
    have right_value: "action phase=snd right"
      using right_phase right_fiber by blast
    have label_eq: "snd left=snd right"
      using left_value right_value by simp
    show "left=right"
      by (rule inj_onD[OF labels_injective label_eq left right])
  qed
  have distinct_columns: "distinct (map fst (map comma_crt_project_row rows))"
  proof -
    have "distinct (map (\<lambda>row. comma_crt_set (fst row)) rows)"
      using rows_distinct geometry_injective by (simp add: distinct_map)
    then show ?thesis by (simp add: comma_crt_project_row_def comp_def)
  qed
  have covered:
    "(\<Union> (fst ` set (map comma_crt_project_row rows)))={..<924}"
  proof (rule set_eqI)
    fix phase :: nat
    show "phase\<in>(\<Union> (fst ` set (map comma_crt_project_row rows)))
        \<longleftrightarrow> phase\<in>{..<924}"
    proof
      assume member: "phase\<in>(\<Union> (fst ` set (map comma_crt_project_row rows)))"
      then obtain row where row: "row\<in>set rows"
        and phase: "phase\<in>comma_crt_set (fst row)"
        by (auto simp: comma_crt_project_row_def)
      have exact: "comma_semantic_b1_binding_row_exact action 0
          (comma_crt_project_row row)"
        using row_exact row by blast
      show "phase\<in>{..<924}"
        using exact phase by (auto simp: comma_semantic_b1_binding_row_exact_def
          comma_crt_project_row_def)
    next
      assume phase: "phase\<in>{..<924}"
      obtain outcome where outcome: "action phase=outcome"
        by (cases "action phase") auto
      have in_group:
        "phase\<in>comma_crt_set (comma_crt_group_column outcome rows)"
        using fibers[of outcome] phase outcome by auto
      have nonempty:
        "comma_crt_set (comma_crt_group_column outcome rows)\<noteq>{}"
        using in_group by blast
      obtain row where row: "row\<in>set rows" "snd row=outcome"
        using comma_crt_group_column_nonempty_member[OF nonempty] by blast
      have selected_column:
        "comma_crt_group_column (snd row) rows=fst row"
        by (rule comma_crt_group_column_member[OF labels row(1)])
      have group_column:
        "comma_crt_group_column outcome rows=fst row"
        using selected_column row(2) by simp
      show "phase\<in>(\<Union> (fst ` set (map comma_crt_project_row rows)))"
        using in_group group_column row(1)
        by (auto simp: comma_crt_project_row_def)
    qed
  qed
  have disjoint:
    "\<forall>left\<in>set (map comma_crt_project_row rows).
      \<forall>right\<in>set (map comma_crt_project_row rows).
        left\<noteq>right \<longrightarrow> fst left \<inter> fst right={}"
  proof (intro ballI impI)
    fix left right
    assume left: "left\<in>set (map comma_crt_project_row rows)"
      and right: "right\<in>set (map comma_crt_project_row rows)"
      and different: "left\<noteq>right"
    obtain lrow where lrow: "lrow\<in>set rows"
      and left_eq: "left=comma_crt_project_row lrow"
      using left by auto
    obtain rrow where rrow: "rrow\<in>set rows"
      and right_eq: "right=comma_crt_project_row rrow"
      using right by auto
    have l_exact: "comma_semantic_b1_binding_row_exact action 0
        (comma_crt_project_row lrow)"
      using row_exact lrow by blast
    have r_exact: "comma_semantic_b1_binding_row_exact action 0
        (comma_crt_project_row rrow)"
      using row_exact rrow by blast
    have l_fiber:
      "comma_crt_set (fst lrow) =
        {phase. phase<924 \<and> action phase=snd lrow}"
      using l_exact
      by (simp only: comma_semantic_b1_binding_row_exact_zero_iff
        comma_crt_project_row_def fst_conv snd_conv)
    have r_fiber:
      "comma_crt_set (fst rrow) =
        {phase. phase<924 \<and> action phase=snd rrow}"
      using r_exact
      by (simp only: comma_semantic_b1_binding_row_exact_zero_iff
        comma_crt_project_row_def fst_conv snd_conv)
    show "fst left \<inter> fst right={}"
    proof (rule ccontr)
      assume "fst left \<inter> fst right\<noteq>{}"
      then obtain phase where phase: "phase\<in>fst left" "phase\<in>fst right"
        by blast
      have l_phase: "phase\<in>comma_crt_set (fst lrow)"
        using phase(1) left_eq
        by (simp only: comma_crt_project_row_def fst_conv)
      have r_phase: "phase\<in>comma_crt_set (fst rrow)"
        using phase(2) right_eq
        by (simp only: comma_crt_project_row_def fst_conv)
      have lvalue: "action phase=snd lrow"
        using l_phase l_fiber by blast
      have rvalue: "action phase=snd rrow"
        using r_phase r_fiber by blast
      have labels_equal: "snd lrow=snd rrow" using lvalue rvalue by simp
      have rows_equal: "lrow=rrow"
        by (rule inj_onD[OF labels_injective labels_equal lrow rrow])
      show False using different left_eq right_eq rows_equal by simp
    qed
  qed
  have projected_exact:
    "\<forall>row\<in>set (map comma_crt_project_row rows).
      comma_semantic_b1_binding_row_exact action 0 row"
  proof (intro ballI impI)
    fix row
    assume row: "row\<in>set (map comma_crt_project_row rows)"
    then obtain original where original: "original\<in>set rows"
      and row_eq: "row=comma_crt_project_row original"
      by auto
    show "comma_semantic_b1_binding_row_exact action 0 row"
      using row_exact original row_eq by simp
  qed
  show ?thesis
    unfolding comma_semantic_b1_binding_table_exact_def
    using distinct_columns covered projected_exact disjoint by blast
qed


text \<open>
Transport a completed binding table by one common clock translation.  The
translation is applied to every decision column while the result label stays
with its occurrence.  The set proofs below use the cyclic phase inverse; they
do not enumerate clock phases or reconstruct a semantic function table.
\<close>

definition comma_crt_shift_return_row ::
    "nat \<Rightarrow> comma_crt_return_row \<Rightarrow> comma_crt_return_row" where
  "comma_crt_shift_return_row shift row =
    (comma_crt_shift shift (fst row), snd row)"

definition comma_crt_shift_return_rows ::
    "nat \<Rightarrow> comma_crt_return_row list \<Rightarrow>
      comma_crt_return_row list" where
  "comma_crt_shift_return_rows shift rows = map (comma_crt_shift_return_row shift) rows"

lemma comma_semantic_b1_inverse_shift_cancel_right:
  "(((phase + comma_semantic_b1_inverse_shift shift) mod 924 + shift) mod 924) =
    phase mod 924"
proof -
  have "(((phase + comma_semantic_b1_inverse_shift shift) mod 924 + shift) mod 924) =
      ((phase + comma_semantic_b1_inverse_shift shift + shift) mod 924)"
    by (rule mod_add_left_eq)
  also have "... =
      ((phase + shift + comma_semantic_b1_inverse_shift shift) mod 924)"
    by (simp only: add.commute add.left_commute)
  also have "... = (((phase+shift) mod 924 +
      comma_semantic_b1_inverse_shift shift) mod 924)"
    by (rule sym[OF mod_add_left_eq])
  also have "... = phase mod 924"
    by (rule comma_semantic_b1_cancel_shift)
  finally show ?thesis .
qed

lemma comma_semantic_b1_column_advance_injective:
  assumes left: "phases \<subseteq> {..<924}"
    and right: "other \<subseteq> {..<924}"
    and equal: "comma_semantic_b1_column_advance shift phases =
      comma_semantic_b1_column_advance shift other"
  shows "phases=other"
proof (rule set_eqI)
  fix phase
  let ?before = "(phase + comma_semantic_b1_inverse_shift shift) mod 924"
  have before_bound: "?before<924" by simp
  have cancel: "(?before+shift) mod 924=phase mod 924"
    using comma_semantic_b1_inverse_shift_cancel_right[of phase shift] by simp
  show "phase \<in> phases \<longleftrightarrow> phase \<in> other"
  proof (cases "phase<924")
    case False
    then show ?thesis using left right by auto
  next
    case True
    have before_left:
      "?before \<in> comma_semantic_b1_column_advance shift phases \<longleftrightarrow>
        phase \<in> phases"
      using before_bound cancel True
      by (auto simp: comma_semantic_b1_column_advance_def)
    have before_right:
      "?before \<in> comma_semantic_b1_column_advance shift other \<longleftrightarrow>
        phase \<in> other"
      using before_bound cancel True
      by (auto simp: comma_semantic_b1_column_advance_def)
    show ?thesis
      using equal before_left before_right by blast
  qed
qed

lemma comma_semantic_b1_column_advance_nonempty:
  assumes subset: "phases \<subseteq> {..<924}" and nonempty: "phases\<noteq>{}"
  shows "comma_semantic_b1_column_advance shift phases \<noteq>{}"
proof -
  obtain phase where phase: "phase\<in>phases" using nonempty by blast
  let ?before = "(phase + comma_semantic_b1_inverse_shift shift) mod 924"
  have before_bound: "?before<924" by simp
  have cancel: "(?before+shift) mod 924=phase mod 924"
    using comma_semantic_b1_inverse_shift_cancel_right[of phase shift] by simp
  have phase_bound: "phase<924" using subset phase by blast
  have "?before\<in>comma_semantic_b1_column_advance shift phases"
    using before_bound phase phase_bound cancel
    by (auto simp: comma_semantic_b1_column_advance_def)
  then show ?thesis by blast
qed

lemma comma_semantic_b1_shift_binding_table_exact:
  assumes exact: "comma_semantic_b1_binding_table_exact action 0 rows"
  shows "comma_semantic_b1_binding_table_exact action shift
    (map (\<lambda>row. (comma_semantic_b1_column_advance shift (fst row), snd row)) rows)"
proof -
  let ?translated = "map (\<lambda>row. (comma_semantic_b1_column_advance shift (fst row), snd row)) rows"
  have original_distinct: "distinct (map fst rows)"
    using exact by (simp add: comma_semantic_b1_binding_table_exact_def)
  have original_cover: "(\<Union> (fst ` set rows))={..<924}"
    using exact by (simp add: comma_semantic_b1_binding_table_exact_def)
  have original_row_exact:
    "\<And>row. row\<in>set rows \<Longrightarrow>
      comma_semantic_b1_binding_row_exact action 0 row"
    using exact by (auto simp: comma_semantic_b1_binding_table_exact_def)
  have original_disjoint:
    "\<And>left right. left\<in>set rows \<Longrightarrow> right\<in>set rows \<Longrightarrow>
      left\<noteq>right \<Longrightarrow> fst left \<inter> fst right={}"
    using exact by (auto simp: comma_semantic_b1_binding_table_exact_def)
  have original_rows_distinct: "distinct rows"
    and original_keys_injective: "inj_on fst (set rows)"
    using original_distinct by (auto simp: distinct_map)
  have translated_keys_injective:
      "inj_on (\<lambda>row. comma_semantic_b1_column_advance shift (fst row)) (set rows)"
  proof (rule inj_onI)
    fix left right
    assume left: "left\<in>set rows" and right: "right\<in>set rows"
      and translated_equal:
        "comma_semantic_b1_column_advance shift (fst left) =
          comma_semantic_b1_column_advance shift (fst right)"
    have left_subset: "fst left\<subseteq>{..<924}"
      using original_row_exact[OF left]
      by (auto simp: comma_semantic_b1_binding_row_exact_def)
    have right_subset: "fst right\<subseteq>{..<924}"
      using original_row_exact[OF right]
      by (auto simp: comma_semantic_b1_binding_row_exact_def)
    have keys_equal: "fst left=fst right"
      by (rule comma_semantic_b1_column_advance_injective
        [OF left_subset right_subset translated_equal])
    show "left=right"
      by (rule inj_onD[OF original_keys_injective keys_equal left right])
  qed
  have translated_distinct: "distinct (map fst ?translated)"
    using original_rows_distinct translated_keys_injective
    by (simp add: distinct_map comp_def)
  have translated_cover: "(\<Union> (fst ` set ?translated))={..<924}"
  proof (rule set_eqI)
    fix phase
    show "phase\<in>(\<Union> (fst ` set ?translated)) \<longleftrightarrow> phase\<in>{..<924}"
    proof
      assume "phase\<in>(\<Union> (fst ` set ?translated))"
      then obtain row where row: "row\<in>set rows"
        and member: "phase\<in>comma_semantic_b1_column_advance shift (fst row)"
        by auto
      from member show "phase\<in>{..<924}"
        by (auto simp: comma_semantic_b1_column_advance_def)
    next
      assume phase: "phase\<in>{..<924}"
      let ?advanced = "(phase+shift) mod 924"
      have advanced: "?advanced<924" by simp
      obtain row where row: "row\<in>set rows" and member: "?advanced\<in>fst row"
        using original_cover advanced by blast
      have "phase\<in>comma_semantic_b1_column_advance shift (fst row)"
        using phase member by (auto simp: comma_semantic_b1_column_advance_def)
      then show "phase\<in>(\<Union> (fst ` set ?translated))"
        using row by auto
    qed
  qed
  have translated_rows_exact:
    "\<forall>row\<in>set ?translated.
      comma_semantic_b1_binding_row_exact action shift row"
  proof (intro ballI)
    fix row
    assume row: "row\<in>set ?translated"
    then obtain original where original: "original\<in>set rows"
      and row_eq: "row=(comma_semantic_b1_column_advance shift (fst original),snd original)"
      by auto
    have exact_row: "comma_semantic_b1_binding_row_exact action 0 original"
      by (rule original_row_exact[OF original])
    have original_subset: "fst original\<subseteq>{..<924}"
      using exact_row by (auto simp: comma_semantic_b1_binding_row_exact_def)
    have original_fiber:
      "fst original={phase. phase<924 \<and> action phase=snd original}"
      using exact_row by (simp add: comma_semantic_b1_binding_row_exact_zero_iff)
    have original_nonempty: "fst original\<noteq>{}"
      by (rule conjunct1[OF iffD1[OF
        comma_semantic_b1_binding_row_exact_zero_iff exact_row]])
    have translated_nonempty:
      "comma_semantic_b1_column_advance shift (fst original)\<noteq>{}"
      by (rule comma_semantic_b1_column_advance_nonempty
        [OF original_subset original_nonempty])
    have translated_fiber:
      "comma_semantic_b1_column_advance shift (fst original) =
        {phase. phase<924 \<and> action ((phase+shift) mod 924)=snd original}"
      using original_fiber by (auto simp: comma_semantic_b1_column_advance_def)
    show "comma_semantic_b1_binding_row_exact action shift row"
      using translated_nonempty translated_fiber row_eq
      by (simp add: comma_semantic_b1_binding_row_exact_def)
  qed
  have translated_disjoint:
    "\<forall>left\<in>set ?translated. \<forall>right\<in>set ?translated.
      left\<noteq>right \<longrightarrow> fst left \<inter> fst right={}"
  proof (intro ballI impI)
    fix left right
    assume left: "left\<in>set ?translated" and right: "right\<in>set ?translated"
      and different: "left\<noteq>right"
    obtain old_left where old_left: "old_left\<in>set rows"
      and left_eq: "left=(comma_semantic_b1_column_advance shift (fst old_left),snd old_left)"
      using left by auto
    obtain old_right where old_right: "old_right\<in>set rows"
      and right_eq: "right=(comma_semantic_b1_column_advance shift (fst old_right),snd old_right)"
      using right by auto
    have old_different: "old_left\<noteq>old_right"
    proof
      assume same: "old_left=old_right"
      then show False using different left_eq right_eq by simp
    qed
    have disjoint: "fst old_left \<inter> fst old_right={}"
      by (rule original_disjoint[OF old_left old_right old_different])
    show "fst left \<inter> fst right={}"
      using disjoint left_eq right_eq
      by (auto simp: comma_semantic_b1_column_advance_def)
  qed
  show ?thesis
    unfolding comma_semantic_b1_binding_table_exact_def
    using translated_distinct translated_cover translated_rows_exact translated_disjoint
    by blast
qed

lemma comma_crt_shift_return_rows_admitted:
  assumes admitted: "comma_crt_rows_admitted rows"
  shows "comma_crt_rows_admitted (comma_crt_shift_return_rows shift rows)"
  using admitted comma_crt_shift_admitted
  by (auto simp: comma_crt_rows_admitted_def comma_crt_shift_return_rows_def
      comma_crt_shift_return_row_def)

theorem comma_crt_shift_return_rows_exact:
  assumes admitted: "comma_crt_rows_admitted rows"
    and exact: "comma_semantic_b1_binding_table_exact action 0
      (map comma_crt_project_row rows)"
  shows "comma_semantic_b1_binding_table_exact action shift
    (map comma_crt_project_row (comma_crt_shift_return_rows shift rows))"
proof -
  have projected:
    "map comma_crt_project_row (comma_crt_shift_return_rows shift rows) =
      map (\<lambda>row. (comma_semantic_b1_column_advance shift
          (fst (comma_crt_project_row row)), snd (comma_crt_project_row row))) rows"
    unfolding comma_crt_shift_return_rows_def map_map comp_def
  proof (rule map_cong[OF refl])
    fix row
    assume row: "row\<in>set rows"
    have row_admitted: "comma_crt_admitted 0 (fst row)"
      using admitted row by (auto simp: comma_crt_rows_admitted_def)
    have shifted_set:
      "comma_crt_set (comma_crt_shift shift (fst row)) =
        comma_semantic_b1_column_advance shift (comma_crt_set (fst row))"
      by (rule comma_crt_shift_is_power_advance[OF row_admitted])
    show "comma_crt_project_row (comma_crt_shift_return_row shift row) =
        (comma_semantic_b1_column_advance shift
          (fst (comma_crt_project_row row)), snd (comma_crt_project_row row))"
      using shifted_set
      by (simp add: comma_crt_shift_return_row_def comma_crt_project_row_def)
  qed
  have shifted_exact:
    "comma_semantic_b1_binding_table_exact action shift
      (map (\<lambda>row. (comma_semantic_b1_column_advance shift (fst row), snd row))
        (map comma_crt_project_row rows))"
    by (rule comma_semantic_b1_shift_binding_table_exact[OF exact])
  show ?thesis
    using shifted_exact by (simp only: projected map_map comp_def)
qed

ML \<open>
  val checked = @{thms comma_crt_negate_admitted comma_crt_negate_eval
    comma_crt_equiv_check_iff comma_crt_equiv_check_sound
    comma_crt_labeled_rows_equivalent_projection
    comma_crt_labeled_rows_equivalent_table_transfer
    comma_semantic_b1_shift_binding_table_exact
    comma_crt_shift_return_rows_exact};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "structural CRT equivalence and labeled occurrence transport" checked;
\<close>

end
