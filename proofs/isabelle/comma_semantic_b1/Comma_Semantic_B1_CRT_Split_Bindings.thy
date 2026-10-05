theory Comma_Semantic_B1_CRT_Split_Bindings
  imports Comma_Semantic_B1_CRT_Split_Occurrence
begin

text \<open>
This theory proves the provider-independent binding-fold contract for the
paired control and weight MDDs.  Each outcome paints both projections under
the same shifted support, so a terminal weight is retained as occurrence
data while control reduction remains independent of that weight.
\<close>

lemma comma_crt_mdd_paint_binding_control_eval:
  fixes rebase phase :: nat
    and column :: comma_crt_column
    and outcome :: comma_semantic_b1_result
    and action :: comma_crt_split_action
  assumes column: "comma_crt_admitted 0 column"
    and current: "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control action) (comma_crt_split_weight action)"
  shows "comma_crt_mdd_eval phase
      (comma_crt_split_control
        (comma_crt_mdd_paint_binding rebase column outcome action)) =
    (if comma_crt_eval phase (comma_crt_shift rebase column)
     then Some (comma_crt_control_of_result outcome)
     else comma_crt_mdd_eval phase (comma_crt_split_control action))"
proof -
  have shifted: "comma_crt_admitted 0 (comma_crt_shift rebase column)"
    by (rule comma_crt_shift_admitted[OF column])
  have current_admitted: "comma_crt_mdd_admitted 0 (comma_crt_split_control action)"
    using current by (simp add: comma_crt_mdd_split_consistent_def)
  show ?thesis
    using comma_crt_mdd_paint_column_eval[OF shifted current_admitted, of phase
        "comma_crt_control_of_result outcome"]
    by (simp add: comma_crt_mdd_paint_binding_def Let_def)
qed

lemma comma_crt_mdd_paint_binding_weight_eval:
  fixes rebase phase :: nat
    and column :: comma_crt_column
    and outcome :: comma_semantic_b1_result
    and action :: comma_crt_split_action
  assumes column: "comma_crt_admitted 0 column"
    and current: "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control action) (comma_crt_split_weight action)"
  shows "comma_crt_mdd_eval phase
      (comma_crt_split_weight
        (comma_crt_mdd_paint_binding rebase column outcome action)) =
    (if comma_crt_eval phase (comma_crt_shift rebase column)
     then Some (comma_crt_weight_of_result outcome)
     else comma_crt_mdd_eval phase (comma_crt_split_weight action))"
proof -
  have shifted: "comma_crt_admitted 0 (comma_crt_shift rebase column)"
    by (rule comma_crt_shift_admitted[OF column])
  have current_admitted: "comma_crt_mdd_admitted 0 (comma_crt_split_weight action)"
    using current by (simp add: comma_crt_mdd_split_consistent_def)
  show ?thesis
    using comma_crt_mdd_paint_column_eval[OF shifted current_admitted, of phase
        "comma_crt_weight_of_result outcome"]
    by (simp add: comma_crt_mdd_paint_binding_def Let_def)
qed

lemma comma_crt_occurrence_split_from_bindings_no_hit:
  fixes rebase phase :: nat
    and columns :: "comma_crt_column list"
    and outcomes :: "comma_semantic_b1_result list"
    and action :: comma_crt_split_action
  assumes width: "length columns = length outcomes"
    and columns_admitted: "list_all (comma_crt_admitted 0) columns"
    and action_consistent: "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control action) (comma_crt_split_weight action)"
    and no_hit: "\<forall>i<length columns.
      \<not> comma_crt_eval phase (comma_crt_shift rebase (columns!i))"
  shows "comma_crt_mdd_eval phase (comma_crt_split_control
      (comma_crt_occurrence_split_from_bindings rebase columns outcomes action)) =
        comma_crt_mdd_eval phase (comma_crt_split_control action) \<and>
    comma_crt_mdd_eval phase (comma_crt_split_weight
      (comma_crt_occurrence_split_from_bindings rebase columns outcomes action)) =
        comma_crt_mdd_eval phase (comma_crt_split_weight action)"
  using width columns_admitted action_consistent no_hit
proof (induction columns arbitrary: outcomes action)
  case Nil
  then show ?case by simp
next
  case (Cons column columns)
  note width_assm = Cons.prems(1)
  note admitted_assm = Cons.prems(2)
  note consistent_assm = Cons.prems(3)
  note no_hit_assm = Cons.prems(4)
  note induct_ih = Cons.IH
  show ?case
  proof (cases outcomes)
    case Nil
    then show ?thesis using width_assm by simp
  next
    case (Cons outcome outcomes')
    let ?painted =
      "comma_crt_mdd_paint_binding rebase column outcome action"
    have head_admitted: "comma_crt_admitted 0 column"
      using admitted_assm by simp
    have tail_admitted: "list_all (comma_crt_admitted 0) columns"
      using admitted_assm by simp
    have painted_consistent: "comma_crt_mdd_split_consistent 0
        (comma_crt_split_control ?painted) (comma_crt_split_weight ?painted)"
      by (rule comma_crt_mdd_paint_binding_admitted[OF head_admitted consistent_assm])
    have tail_width: "length columns=length outcomes'"
      using width_assm Cons by simp
    have head_no_hit:
      "\<not> comma_crt_eval phase (comma_crt_shift rebase column)"
    proof -
      have zero_bound: "0<length (column#columns)" by simp
      have at_zero:
        "0<length (column#columns) \<longrightarrow>
          \<not> comma_crt_eval phase
            (comma_crt_shift rebase ((column#columns)!0))"
        by (rule spec[OF no_hit_assm])
      show ?thesis using at_zero zero_bound by simp
    qed
    have tail_no_hit:
      "\<forall>i<length columns.
        \<not> comma_crt_eval phase (comma_crt_shift rebase (columns!i))"
    proof (intro allI impI)
      fix i assume i_bound: "i<length columns"
      show "\<not> comma_crt_eval phase (comma_crt_shift rebase (columns!i))"
        using no_hit_assm i_bound by auto
    qed
    have tail_same:
      "comma_crt_mdd_eval phase (comma_crt_split_control
          (comma_crt_occurrence_split_from_bindings rebase columns outcomes' ?painted)) =
        comma_crt_mdd_eval phase (comma_crt_split_control ?painted) \<and>
       comma_crt_mdd_eval phase (comma_crt_split_weight
          (comma_crt_occurrence_split_from_bindings rebase columns outcomes' ?painted)) =
        comma_crt_mdd_eval phase (comma_crt_split_weight ?painted)"
      by (rule induct_ih[OF tail_width tail_admitted painted_consistent tail_no_hit])
    have head_control:
      "comma_crt_mdd_eval phase (comma_crt_split_control ?painted) =
        comma_crt_mdd_eval phase (comma_crt_split_control action)"
      using comma_crt_mdd_paint_binding_control_eval
        [OF head_admitted consistent_assm, of phase] head_no_hit by simp
    have head_weight:
      "comma_crt_mdd_eval phase (comma_crt_split_weight ?painted) =
        comma_crt_mdd_eval phase (comma_crt_split_weight action)"
      using comma_crt_mdd_paint_binding_weight_eval
        [OF head_admitted consistent_assm, of phase] head_no_hit by simp
    show ?thesis
      using tail_same head_control head_weight Cons by simp
  qed
qed

lemma comma_crt_occurrence_split_from_bindings_eval_at:
  fixes rebase phase :: nat
    and result :: comma_semantic_b1_result
    and columns :: "comma_crt_column list"
    and outcomes :: "comma_semantic_b1_result list"
    and action :: comma_crt_split_action
  assumes width: "length columns=length outcomes"
    and columns_admitted: "list_all (comma_crt_admitted 0) columns"
    and action_consistent: "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control action) (comma_crt_split_weight action)"
    and selected: "\<exists>i<length columns.
      comma_crt_eval phase (comma_crt_shift rebase (columns!i))"
    and disjoint: "\<forall>i<length columns. \<forall>j<length columns. i\<noteq>j \<longrightarrow>
      \<not> (comma_crt_eval phase (comma_crt_shift rebase (columns!i)) \<and>
        comma_crt_eval phase (comma_crt_shift rebase (columns!j)))"
    and binding: "\<forall>i<length columns.
      comma_crt_eval phase (comma_crt_shift rebase (columns!i)) \<longrightarrow>
      outcomes!i=result"
  shows "comma_crt_mdd_eval phase (comma_crt_split_control
      (comma_crt_occurrence_split_from_bindings rebase columns outcomes action)) =
        Some (comma_crt_control_of_result result) \<and>
    comma_crt_mdd_eval phase (comma_crt_split_weight
      (comma_crt_occurrence_split_from_bindings rebase columns outcomes action)) =
        Some (comma_crt_weight_of_result result)"
  using width columns_admitted action_consistent selected disjoint binding
proof (induction columns arbitrary: outcomes action)
  case Nil
  then show ?case by simp
next
  case (Cons column columns)
  note width_assm = Cons.prems(1)
  note admitted_assm = Cons.prems(2)
  note consistent_assm = Cons.prems(3)
  note selected_assm = Cons.prems(4)
  note disjoint_assm = Cons.prems(5)
  note binding_assm = Cons.prems(6)
  note induct_ih = Cons.IH
  show ?case
  proof (cases outcomes)
    case Nil
    then show ?thesis using width_assm by simp
  next
    case (Cons outcome outcomes')
    let ?mask = "comma_crt_shift rebase column"
    let ?painted = "comma_crt_mdd_paint_binding rebase column outcome action"
    have head_admitted: "comma_crt_admitted 0 column"
      using admitted_assm by simp
    have tail_admitted: "list_all (comma_crt_admitted 0) columns"
      using admitted_assm by simp
    have painted_consistent: "comma_crt_mdd_split_consistent 0
        (comma_crt_split_control ?painted) (comma_crt_split_weight ?painted)"
      by (rule comma_crt_mdd_paint_binding_admitted[OF head_admitted consistent_assm])
    have tail_width: "length columns=length outcomes'"
      using width_assm Cons by simp
    show ?thesis
    proof (cases "comma_crt_eval phase ?mask")
      case True
      have zero_bound: "0<length (column#columns)" by simp
      have at_zero:
        "0<length (column#columns) \<longrightarrow>
          (comma_crt_eval phase
              (comma_crt_shift rebase ((column#columns)!0)) \<longrightarrow>
            outcomes!0=result)"
        by (rule spec[OF binding_assm])
      have head_binding: "outcome=result"
        using at_zero zero_bound True Cons by simp
      have tail_no_hit:
        "\<forall>i<length columns.
          \<not> comma_crt_eval phase (comma_crt_shift rebase (columns!i))"
      proof (intro allI impI)
        fix i assume i_bound: "i<length columns"
        have zero_bound: "0<length (column#columns)" by simp
        have different: "0\<noteq>Suc i" by simp
        have disjoint_at_zero:
          "0<length (column#columns) \<longrightarrow>
            (\<forall>j<length (column#columns). 0\<noteq>j \<longrightarrow>
              \<not> (comma_crt_eval phase
                    (comma_crt_shift rebase ((column#columns)!0)) \<and>
                comma_crt_eval phase
                    (comma_crt_shift rebase ((column#columns)!j))))"
          by (rule spec[OF disjoint_assm])
        have all_disjoint_at_zero:
          "\<forall>j<length (column#columns). 0\<noteq>j \<longrightarrow>
            \<not> (comma_crt_eval phase
                  (comma_crt_shift rebase ((column#columns)!0)) \<and>
              comma_crt_eval phase
                  (comma_crt_shift rebase ((column#columns)!j)))"
          using disjoint_at_zero zero_bound by blast
        have disjoint_at_suc:
          "Suc i<length (column#columns) \<longrightarrow>
            (0\<noteq>Suc i \<longrightarrow>
              \<not> (comma_crt_eval phase
                    (comma_crt_shift rebase ((column#columns)!0)) \<and>
                comma_crt_eval phase
                    (comma_crt_shift rebase ((column#columns)!Suc i))))"
          using all_disjoint_at_zero by (rule spec)
        have suc_bound: "Suc i<length (column#columns)"
          using i_bound by simp
        show "\<not> comma_crt_eval phase (comma_crt_shift rebase (columns!i))"
          using disjoint_at_suc suc_bound different True by simp
      qed
      have tail_same:
        "comma_crt_mdd_eval phase (comma_crt_split_control
            (comma_crt_occurrence_split_from_bindings rebase columns outcomes' ?painted)) =
          comma_crt_mdd_eval phase (comma_crt_split_control ?painted) \<and>
         comma_crt_mdd_eval phase (comma_crt_split_weight
            (comma_crt_occurrence_split_from_bindings rebase columns outcomes' ?painted)) =
          comma_crt_mdd_eval phase (comma_crt_split_weight ?painted)"
        by (rule comma_crt_occurrence_split_from_bindings_no_hit
          [OF tail_width tail_admitted painted_consistent tail_no_hit])
      have head_values:
        "comma_crt_mdd_eval phase (comma_crt_split_control ?painted) =
            Some (comma_crt_control_of_result result) \<and>
         comma_crt_mdd_eval phase (comma_crt_split_weight ?painted) =
            Some (comma_crt_weight_of_result result)"
        using comma_crt_mdd_paint_binding_control_eval
            [OF head_admitted consistent_assm, of phase]
          comma_crt_mdd_paint_binding_weight_eval
            [OF head_admitted consistent_assm, of phase] True head_binding by simp
      show ?thesis using tail_same head_values Cons by simp
    next
      case False
      obtain index where index_bound: "index<length (column#columns)"
        and selected_index:
          "comma_crt_eval phase (comma_crt_shift rebase ((column#columns)!index))"
        using selected_assm by blast
      have not_head: "index\<noteq>0"
      proof (cases index)
        case 0
        then show ?thesis using False selected_index by simp
      next
        case (Suc tail_index)
        then show ?thesis by simp
      qed
      obtain tail_index where index_eq: "index=Suc tail_index"
        using not_head by (cases index) auto
      have tail_bound: "tail_index<length columns"
        using index_bound index_eq by simp
      have tail_selected:
        "\<exists>i<length columns.
          comma_crt_eval phase (comma_crt_shift rebase (columns!i))"
        by (rule exI[of _ tail_index])
          (use tail_bound selected_index index_eq in simp)
      have tail_disjoint:
        "\<forall>i<length columns. \<forall>j<length columns. i\<noteq>j \<longrightarrow>
          \<not> (comma_crt_eval phase (comma_crt_shift rebase (columns!i)) \<and>
            comma_crt_eval phase (comma_crt_shift rebase (columns!j)))"
      proof (intro allI impI impI)
        fix i j assume i_bound: "i<length columns"
          and j_bound: "j<length columns" and different: "i\<noteq>j"
        have i_suc_bound: "Suc i<length (column#columns)"
          using i_bound by simp
        have j_suc_bound: "Suc j<length (column#columns)"
          using j_bound by simp
        have at_i:
          "\<forall>j<length (column#columns). Suc i\<noteq>j \<longrightarrow>
            \<not> (comma_crt_eval phase
                (comma_crt_shift rebase ((column#columns)!Suc i)) \<and>
              comma_crt_eval phase
                (comma_crt_shift rebase ((column#columns)!j)))"
          using disjoint_assm i_suc_bound by blast
        have at_j:
          "Suc i\<noteq>Suc j \<longrightarrow>
            \<not> (comma_crt_eval phase
                (comma_crt_shift rebase ((column#columns)!Suc i)) \<and>
              comma_crt_eval phase
                (comma_crt_shift rebase ((column#columns)!Suc j)))"
          using at_i j_suc_bound by blast
        show "\<not> (comma_crt_eval phase
              (comma_crt_shift rebase (columns!i)) \<and>
            comma_crt_eval phase (comma_crt_shift rebase (columns!j)))"
          using at_j different by simp
      qed
      have tail_binding:
        "\<forall>i<length columns.
          comma_crt_eval phase (comma_crt_shift rebase (columns!i)) \<longrightarrow>
          outcomes'!i=result"
      proof (intro allI impI)
        fix i assume i_bound: "i<length columns"
          and hit: "comma_crt_eval phase
            (comma_crt_shift rebase (columns!i))"
        have i_suc_bound: "Suc i<length (column#columns)"
          using i_bound by simp
        have at_i:
          "comma_crt_eval phase
              (comma_crt_shift rebase ((column#columns)!Suc i)) \<longrightarrow>
            outcomes!Suc i=result"
          using binding_assm i_suc_bound by blast
        have outcomes_eq: "outcomes=outcome#outcomes'"
          using Cons by simp
        show "outcomes'!i=result"
          using at_i hit outcomes_eq by simp
      qed
      have tail_values:
        "comma_crt_mdd_eval phase (comma_crt_split_control
            (comma_crt_occurrence_split_from_bindings rebase columns outcomes' ?painted)) =
            Some (comma_crt_control_of_result result) \<and>
         comma_crt_mdd_eval phase (comma_crt_split_weight
            (comma_crt_occurrence_split_from_bindings rebase columns outcomes' ?painted)) =
            Some (comma_crt_weight_of_result result)"
        by (rule induct_ih[OF tail_width tail_admitted painted_consistent
          tail_selected tail_disjoint tail_binding])
      show ?thesis using tail_values Cons by simp
    qed
  qed
qed

lemma comma_crt_occurrence_split_initial_consistent:
  "comma_crt_mdd_split_consistent 0
    (comma_crt_split_control comma_crt_occurrence_split_initial)
    (comma_crt_split_weight comma_crt_occurrence_split_initial)"
  by (simp add: comma_crt_mdd_split_consistent_def
      comma_crt_occurrence_split_initial_def
      comma_crt_split_invalid_action_def
      comma_crt_split_value_consistent.simps)

lemma comma_crt_occurrence_split_from_bindings_preserves_consistency:
  fixes rebase :: nat
    and columns :: "comma_crt_column list"
    and outcomes :: "comma_semantic_b1_result list"
    and current :: comma_crt_split_action
  assumes width: "length columns=length outcomes"
    and admitted: "list_all (comma_crt_admitted 0) columns"
    and current_consistent: "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control current) (comma_crt_split_weight current)"
  shows "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control
        (comma_crt_occurrence_split_from_bindings rebase columns outcomes
          current))
      (comma_crt_split_weight
        (comma_crt_occurrence_split_from_bindings rebase columns outcomes
          current))"
  using width admitted current_consistent
proof (induction columns arbitrary: outcomes current)
  case Nil
  then show ?case by simp
next
  case (Cons column columns)
  note width_assm = Cons.prems(1)
  note admitted_assm = Cons.prems(2)
  note consistent_assm = Cons.prems(3)
  note induct_ih = Cons.IH
  show ?case
  proof (cases outcomes)
    case Nil
    then show ?thesis using width_assm by simp
  next
    case (Cons outcome outcomes')
    have head_admitted: "comma_crt_admitted 0 column"
      using admitted_assm by simp
    have tail_admitted: "list_all (comma_crt_admitted 0) columns"
      using admitted_assm by simp
    have current_consistent: "comma_crt_mdd_split_consistent 0
        (comma_crt_split_control
          (comma_crt_mdd_paint_binding rebase column outcome current))
        (comma_crt_split_weight
          (comma_crt_mdd_paint_binding rebase column outcome current))"
      by (rule comma_crt_mdd_paint_binding_admitted[OF head_admitted consistent_assm])
    have tail_width: "length columns=length outcomes'"
      using width_assm Cons by simp
    show ?thesis
      using induct_ih[OF tail_width tail_admitted current_consistent] Cons by simp
  qed
qed

theorem comma_crt_occurrence_split_from_bindings_consistent:
  fixes rebase :: nat
    and columns :: "comma_crt_column list"
    and outcomes :: "comma_semantic_b1_result list"
  assumes width: "length columns=length outcomes"
    and admitted: "list_all (comma_crt_admitted 0) columns"
  shows "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control
        (comma_crt_occurrence_split_from_bindings rebase columns outcomes
          comma_crt_occurrence_split_initial))
      (comma_crt_split_weight
        (comma_crt_occurrence_split_from_bindings rebase columns outcomes
          comma_crt_occurrence_split_initial))"
  by (rule comma_crt_occurrence_split_from_bindings_preserves_consistency
    [OF width admitted comma_crt_occurrence_split_initial_consistent])

theorem comma_crt_occurrence_split_from_bindings_exact:
  fixes rebase :: nat
    and columns :: "comma_crt_column list"
    and outcomes :: "comma_semantic_b1_result list"
    and action :: "nat \<Rightarrow> comma_semantic_b1_result"
  assumes width: "length columns=length outcomes"
    and admitted: "list_all (comma_crt_admitted 0) columns"
    and distinct_outcomes: "distinct outcomes"
    and fibers: "\<forall>i<length columns.
      comma_crt_set (comma_crt_shift rebase (columns!i)) =
        {phase. phase<924 \<and> action phase=outcomes!i}"
    and covers: "\<Union> (comma_crt_set `
      set (map (comma_crt_shift rebase) columns)) = {..<924}"
  shows "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control
        (comma_crt_occurrence_split_from_bindings rebase columns outcomes
          comma_crt_occurrence_split_initial))
      (comma_crt_split_weight
        (comma_crt_occurrence_split_from_bindings rebase columns outcomes
          comma_crt_occurrence_split_initial)) \<and>
    (\<forall>phase<924. comma_crt_split_mdd_result_at phase
        (comma_crt_split_control
          (comma_crt_occurrence_split_from_bindings rebase columns outcomes
            comma_crt_occurrence_split_initial))
        (comma_crt_split_weight
          (comma_crt_occurrence_split_from_bindings rebase columns outcomes
            comma_crt_occurrence_split_initial)) = Some (action phase))"
proof -
  let ?fold = "comma_crt_occurrence_split_from_bindings rebase columns outcomes
    comma_crt_occurrence_split_initial"
  have consistent:
    "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control ?fold) (comma_crt_split_weight ?fold)"
    by (rule comma_crt_occurrence_split_from_bindings_consistent[OF width admitted])
  have projections:
    "\<forall>phase<924.
      comma_crt_mdd_eval phase (comma_crt_split_control ?fold) =
        Some (comma_crt_control_of_result (action phase)) \<and>
      comma_crt_mdd_eval phase (comma_crt_split_weight ?fold) =
        Some (comma_crt_weight_of_result (action phase))"
  proof (intro allI impI)
    fix phase :: nat assume phase_bound: "phase<924"
    have selected:
      "\<exists>i<length columns.
        comma_crt_eval phase (comma_crt_shift rebase (columns!i))"
    proof -
      have member: "phase \<in> \<Union> (comma_crt_set `
          set (map (comma_crt_shift rebase) columns))"
        using phase_bound covers by simp
      obtain mask where mask_member:
          "mask \<in> set (map (comma_crt_shift rebase) columns)"
        and phase_member: "phase \<in> comma_crt_set mask"
        using member by blast
      obtain column where column_member: "column\<in>set columns"
        and mask_eq: "mask=comma_crt_shift rebase column"
        using mask_member by auto
      obtain i where i_bound: "i<length columns" and column_eq: "columns!i=column"
        using column_member by (auto simp: in_set_conv_nth)
      have eval_column: "comma_crt_eval phase (comma_crt_shift rebase column)"
        using phase_member mask_eq by (simp add: comma_crt_set_def)
      show ?thesis
        by (rule exI[of _ i]) (use i_bound eval_column column_eq in simp)
    qed
    have binding:
      "\<forall>i<length columns.
        comma_crt_eval phase (comma_crt_shift rebase (columns!i)) \<longrightarrow>
          outcomes!i=action phase"
    proof (intro allI impI)
      fix i assume i_bound: "i<length columns"
        and hit: "comma_crt_eval phase (comma_crt_shift rebase (columns!i))"
      have fiber_i:
        "comma_crt_set (comma_crt_shift rebase (columns!i)) =
          {point. point<924 \<and> action point=outcomes!i}"
        using fibers i_bound by blast
      have phase_member: "phase\<in>comma_crt_set (comma_crt_shift rebase (columns!i))"
        using phase_bound hit by (simp add: comma_crt_set_def)
      have label: "action phase=outcomes!i"
        using fiber_i phase_member by simp
      show "outcomes!i=action phase" using label by (rule sym)
    qed
    have disjoint:
      "\<forall>i<length columns. \<forall>j<length columns. i\<noteq>j \<longrightarrow>
        \<not> (comma_crt_eval phase (comma_crt_shift rebase (columns!i)) \<and>
          comma_crt_eval phase (comma_crt_shift rebase (columns!j)))"
    proof (intro allI impI impI)
      fix i j assume i_bound: "i<length columns" and j_bound: "j<length columns"
        and different: "i\<noteq>j"
      show "\<not> (comma_crt_eval phase (comma_crt_shift rebase (columns!i)) \<and>
          comma_crt_eval phase (comma_crt_shift rebase (columns!j)))"
      proof
        assume both: "comma_crt_eval phase (comma_crt_shift rebase (columns!i)) \<and>
          comma_crt_eval phase (comma_crt_shift rebase (columns!j))"
        have left_label: "outcomes!i=action phase"
          using binding i_bound both by blast
        have right_label: "outcomes!j=action phase"
          using binding j_bound both by blast
        have outcomes_equal: "outcomes!i=outcomes!j"
          using left_label right_label by simp
        have outcome_i_bound: "i<length outcomes"
          using i_bound width by simp
        have outcome_j_bound: "j<length outcomes"
          using j_bound width by simp
        have index_equivalence: "outcomes!i=outcomes!j \<longleftrightarrow> i=j"
          by (rule nth_eq_iff_index_eq
            [OF distinct_outcomes outcome_i_bound outcome_j_bound])
        have same: "i=j"
          using outcomes_equal index_equivalence by blast
        show False using different same by contradiction
      qed
    qed
    have evaluated:
      "comma_crt_mdd_eval phase (comma_crt_split_control ?fold) =
          Some (comma_crt_control_of_result (action phase)) \<and>
       comma_crt_mdd_eval phase (comma_crt_split_weight ?fold) =
          Some (comma_crt_weight_of_result (action phase))"
      by (rule comma_crt_occurrence_split_from_bindings_eval_at
        [OF width admitted comma_crt_occurrence_split_initial_consistent
          selected disjoint binding])
    show "comma_crt_mdd_eval phase (comma_crt_split_control ?fold) =
          Some (comma_crt_control_of_result (action phase)) \<and>
       comma_crt_mdd_eval phase (comma_crt_split_weight ?fold) =
          Some (comma_crt_weight_of_result (action phase))"
      by (rule evaluated)
  qed
  show ?thesis
  proof (intro conjI)
    show "comma_crt_mdd_split_consistent 0
        (comma_crt_split_control ?fold) (comma_crt_split_weight ?fold)"
      by (rule consistent)
    show "\<forall>phase<924. comma_crt_split_mdd_result_at phase
        (comma_crt_split_control ?fold) (comma_crt_split_weight ?fold) =
          Some (action phase)"
    proof (intro allI impI)
      fix phase :: nat assume phase_bound: "phase<924"
      have evals:
        "comma_crt_mdd_eval phase (comma_crt_split_control ?fold) =
          Some (comma_crt_control_of_result (action phase))"
        "comma_crt_mdd_eval phase (comma_crt_split_weight ?fold) =
          Some (comma_crt_weight_of_result (action phase))"
      proof -
        have projection_implication:
          "phase<924 \<longrightarrow>
            (comma_crt_mdd_eval phase (comma_crt_split_control ?fold) =
                Some (comma_crt_control_of_result (action phase)) \<and>
             comma_crt_mdd_eval phase (comma_crt_split_weight ?fold) =
                Some (comma_crt_weight_of_result (action phase)))"
          using projections by (rule spec[where x=phase])
        have phase_projection:
          "comma_crt_mdd_eval phase (comma_crt_split_control ?fold) =
              Some (comma_crt_control_of_result (action phase)) \<and>
           comma_crt_mdd_eval phase (comma_crt_split_weight ?fold) =
              Some (comma_crt_weight_of_result (action phase))"
          using projection_implication phase_bound by blast
        show "comma_crt_mdd_eval phase (comma_crt_split_control ?fold) =
              Some (comma_crt_control_of_result (action phase))"
          and "comma_crt_mdd_eval phase (comma_crt_split_weight ?fold) =
              Some (comma_crt_weight_of_result (action phase))"
          using phase_projection by blast+
      qed
      show "comma_crt_split_mdd_result_at phase
          (comma_crt_split_control ?fold) (comma_crt_split_weight ?fold) =
          Some (action phase)"
        using evals by (simp add: comma_crt_split_mdd_result_at_def
          comma_crt_split_result_of_source)
    qed
  qed
qed

theorem comma_crt_occurrence_split_action_lookup:
  fixes occurrence :: comma_semantic_b1_crt_occurrence and clock :: nat
  assumes wellformed: "comma_semantic_b1_crt_occurrence_wellformed occurrence"
    and clock: "clock<924"
  shows "comma_crt_split_mdd_result_at clock
      (comma_crt_split_control (comma_crt_occurrence_split_action occurrence))
      (comma_crt_split_weight (comma_crt_occurrence_split_action occurrence)) =
    comma_semantic_b1_crt_occurrence_lookup occurrence clock"
proof -
  let ?columns = "comma_semantic_b1_crt_occurrence_columns occurrence"
  let ?outcomes = "comma_semantic_b1_crt_occurrence_beta occurrence"
  let ?rebase = "comma_semantic_b1_crt_occurrence_rebase occurrence"
  let ?phase = "(clock + ?rebase) mod 924"
  let ?fold = "comma_crt_occurrence_split_from_bindings ?rebase ?columns
    ?outcomes comma_crt_occurrence_split_initial"
  have width: "length ?columns=length ?outcomes"
    and admitted: "list_all (comma_crt_admitted 0) ?columns"
    and disjoint_columns: "comma_semantic_b1_crt_occurrence_disjoint ?columns"
    and covered: "comma_semantic_b1_crt_occurrence_covered ?columns"
    using wellformed
    by (auto simp: comma_semantic_b1_crt_occurrence_wellformed_def)
  have phase_bound: "?phase<924" by simp
  obtain index where index_bound: "index<length ?columns"
    and found: "comma_semantic_b1_crt_occurrence_find_index ?phase ?columns =
      Some index"
    using comma_semantic_b1_crt_occurrence_find_index_total
      [OF phase_bound covered] by blast
  have selected_entry:
    "index<length ?columns \<and> comma_crt_eval ?phase (?columns!index)"
    by (rule comma_semantic_b1_crt_occurrence_find_index_entry[OF found])
  have beta_bound: "index<length ?outcomes" using index_bound width by simp
  have lookup:
    "comma_semantic_b1_crt_occurrence_lookup occurrence clock =
      Some (?outcomes!index)"
    using found beta_bound
    by (simp add: comma_semantic_b1_crt_occurrence_lookup_def)
  have shifted_to_phase:
    "\<And>i. i<length ?columns \<Longrightarrow>
      comma_crt_eval clock (comma_crt_shift ?rebase (?columns!i)) =
        comma_crt_eval ?phase (?columns!i)"
  proof -
    fix i assume i_bound: "i<length ?columns"
    have column_admitted: "comma_crt_admitted 0 (?columns!i)"
      using admitted i_bound nth_mem[OF i_bound]
      by (auto simp: list_all_iff)
    have shift_eval:
      "comma_crt_eval clock (comma_crt_shift ?rebase (?columns!i)) =
        comma_crt_eval (clock+?rebase) (?columns!i)"
      by (rule comma_crt_shift_refines[OF column_admitted])
    have periodic:
      "comma_crt_eval ((clock+?rebase) mod 924) (?columns!i) =
        comma_crt_eval (clock+?rebase) (?columns!i)"
      by (rule comma_crt_eval_periodic[OF column_admitted])
    show "comma_crt_eval clock (comma_crt_shift ?rebase (?columns!i)) =
        comma_crt_eval ?phase (?columns!i)"
      using shift_eval periodic by simp
  qed
  have selected:
    "\<exists>i<length ?columns.
      comma_crt_eval clock (comma_crt_shift ?rebase (?columns!i))"
    using selected_entry shifted_to_phase by blast
  have disjoint:
    "\<forall>i<length ?columns. \<forall>j<length ?columns. i\<noteq>j \<longrightarrow>
      \<not> (comma_crt_eval clock (comma_crt_shift ?rebase (?columns!i)) \<and>
        comma_crt_eval clock (comma_crt_shift ?rebase (?columns!j)))"
  proof (intro allI impI impI)
    fix i j assume i_bound: "i<length ?columns"
      and j_bound: "j<length ?columns" and different: "i\<noteq>j"
    have indexed_i:
      "(i,?columns!i)\<in>
        set (comma_semantic_b1_crt_occurrence_indexed_columns ?columns)"
    proof -
      have zip_bound: "i<length (zip [0..<length ?columns] ?columns)"
        using i_bound by simp
      have zip_nth:
        "(zip [0..<length ?columns] ?columns)!i=(i,?columns!i)"
        using i_bound by simp
      show ?thesis using nth_mem[OF zip_bound] zip_nth
        by (simp add: comma_semantic_b1_crt_occurrence_indexed_columns_def)
    qed
    have indexed_j:
      "(j,?columns!j)\<in>
        set (comma_semantic_b1_crt_occurrence_indexed_columns ?columns)"
    proof -
      have zip_bound: "j<length (zip [0..<length ?columns] ?columns)"
        using j_bound by simp
      have zip_nth:
        "(zip [0..<length ?columns] ?columns)!j=(j,?columns!j)"
        using j_bound by simp
      show ?thesis using nth_mem[OF zip_bound] zip_nth
        by (simp add: comma_semantic_b1_crt_occurrence_indexed_columns_def)
    qed
    have disjoint_indexed:
      "\<forall>left\<in>set (comma_semantic_b1_crt_occurrence_indexed_columns ?columns).
        \<forall>right\<in>set (comma_semantic_b1_crt_occurrence_indexed_columns ?columns).
          fst left\<noteq>fst right \<longrightarrow>
            comma_crt_set (snd left) \<inter> comma_crt_set (snd right) = {}"
      using disjoint_columns
      by (simp only: comma_semantic_b1_crt_occurrence_disjoint_def)
    have disjoint_left:
      "\<forall>right\<in>set (comma_semantic_b1_crt_occurrence_indexed_columns ?columns).
        fst (i,?columns!i)\<noteq>fst right \<longrightarrow>
          comma_crt_set (snd (i,?columns!i)) \<inter>
            comma_crt_set (snd right) = {}"
      by (rule bspec[OF disjoint_indexed indexed_i])
    have disjoint_pair:
      "fst (i,?columns!i)\<noteq>fst (j,?columns!j) \<longrightarrow>
        comma_crt_set (snd (i,?columns!i)) \<inter>
          comma_crt_set (snd (j,?columns!j)) = {}"
      by (rule bspec[OF disjoint_left indexed_j])
    have pair_indices: "fst (i,?columns!i)\<noteq>fst (j,?columns!j)"
      using different by simp
    show "\<not> (comma_crt_eval clock (comma_crt_shift ?rebase (?columns!i)) \<and>
        comma_crt_eval clock (comma_crt_shift ?rebase (?columns!j)))"
    proof
      assume both:
        "comma_crt_eval clock (comma_crt_shift ?rebase (?columns!i)) \<and>
          comma_crt_eval clock (comma_crt_shift ?rebase (?columns!j))"
      have left_hit:
        "comma_crt_eval clock (comma_crt_shift ?rebase (?columns!i))"
        using both by blast
      have right_hit:
        "comma_crt_eval clock (comma_crt_shift ?rebase (?columns!j))"
        using both by blast
      have no_intersection:
        "comma_crt_set (?columns!i) \<inter> comma_crt_set (?columns!j) = {}"
        using disjoint_pair pair_indices by simp
      have in_left: "?phase\<in>comma_crt_set (?columns!i)"
        using shifted_to_phase[OF i_bound] left_hit phase_bound
        by (simp add: comma_crt_set_def)
      have in_right: "?phase\<in>comma_crt_set (?columns!j)"
        using shifted_to_phase[OF j_bound] right_hit phase_bound
        by (simp add: comma_crt_set_def)
      show False using no_intersection in_left in_right by blast
    qed
  qed
  have binding:
    "\<forall>i<length ?columns.
      comma_crt_eval clock (comma_crt_shift ?rebase (?columns!i)) \<longrightarrow>
        ?outcomes!i=?outcomes!index"
  proof (intro allI impI)
    fix i assume i_bound: "i<length ?columns"
      and hit: "comma_crt_eval clock (comma_crt_shift ?rebase (?columns!i))"
    show "?outcomes!i=?outcomes!index"
    proof (cases "i=index")
      case True
      then show ?thesis by simp
    next
      case False
      have index_hit:
        "comma_crt_eval clock (comma_crt_shift ?rebase (?columns!index))"
        using selected_entry shifted_to_phase index_bound by blast
      have separated:
        "\<not> (comma_crt_eval clock (comma_crt_shift ?rebase (?columns!i)) \<and>
          comma_crt_eval clock (comma_crt_shift ?rebase (?columns!index)))"
        using disjoint i_bound index_bound False by blast
      show ?thesis using separated hit index_hit by blast
    qed
  qed
  have initial_consistent:
    "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control comma_crt_occurrence_split_initial)
      (comma_crt_split_weight comma_crt_occurrence_split_initial)"
    by (rule comma_crt_occurrence_split_initial_consistent)
  have evals:
    "comma_crt_mdd_eval clock (comma_crt_split_control ?fold) =
        Some (comma_crt_control_of_result (?outcomes!index)) \<and>
     comma_crt_mdd_eval clock (comma_crt_split_weight ?fold) =
        Some (comma_crt_weight_of_result (?outcomes!index))"
    by (rule comma_crt_occurrence_split_from_bindings_eval_at
      [OF width admitted initial_consistent selected disjoint binding])
  show ?thesis
    unfolding comma_crt_occurrence_split_action_def
    using evals lookup
    by (simp add: comma_crt_split_mdd_result_at_def
      comma_crt_split_result_of_source)
qed

lemma comma_crt_split_fold_slot_invariant:
  fixes period selected_slot phase :: nat
    and paint :: "nat \<Rightarrow> 'piece \<Rightarrow> comma_crt_split_action \<Rightarrow>
      comma_crt_split_action"
    and entries :: "(nat \<times> 'piece) list"
    and valid_entry :: "(nat \<times> 'piece) \<Rightarrow> bool"
    and target :: "comma_semantic_b1_result option"
    and initial :: comma_crt_split_action
  assumes initial_consistent:
      "comma_crt_mdd_split_consistent 0
        (comma_crt_split_control initial) (comma_crt_split_weight initial)"
    and entries_bounded:
      "list_all (\<lambda>entry. fst entry < period) entries"
    and entries_valid: "list_all valid_entry entries"
    and paint_effect:
      "\<And>slot piece current.
        valid_entry (slot,piece) \<Longrightarrow>
        slot < period \<Longrightarrow>
        comma_crt_mdd_split_consistent 0
          (comma_crt_split_control current) (comma_crt_split_weight current) \<Longrightarrow>
        comma_crt_mdd_split_consistent 0
          (comma_crt_split_control (paint slot piece current))
          (comma_crt_split_weight (paint slot piece current)) \<and>
        comma_crt_split_mdd_result_at phase
          (comma_crt_split_control (paint slot piece current))
          (comma_crt_split_weight (paint slot piece current)) =
          (if selected_slot = slot then target else
            comma_crt_split_mdd_result_at phase
              (comma_crt_split_control current) (comma_crt_split_weight current))"
  shows "comma_crt_mdd_split_consistent 0
      (comma_crt_split_control (foldl (\<lambda>current entry.
        paint (fst entry) (snd entry) current) initial entries))
      (comma_crt_split_weight (foldl (\<lambda>current entry.
        paint (fst entry) (snd entry) current) initial entries)) \<and>
    comma_crt_split_mdd_result_at phase
      (comma_crt_split_control (foldl (\<lambda>current entry.
        paint (fst entry) (snd entry) current) initial entries))
      (comma_crt_split_weight (foldl (\<lambda>current entry.
        paint (fst entry) (snd entry) current) initial entries)) =
      (if selected_slot \<in> set (map fst entries) then target else
        comma_crt_split_mdd_result_at phase
          (comma_crt_split_control initial) (comma_crt_split_weight initial))"
proof -
  let ?consistent = "\<lambda>action. comma_crt_mdd_split_consistent 0
    (comma_crt_split_control action) (comma_crt_split_weight action)"
  let ?result = "\<lambda>action. comma_crt_split_mdd_result_at phase
    (comma_crt_split_control action) (comma_crt_split_weight action)"
  show ?thesis
    using initial_consistent entries_bounded entries_valid paint_effect
  proof (induction entries arbitrary: initial)
    case Nil
    then show ?case by simp
  next
    case (Cons entry entries)
    obtain slot piece where entry: "entry=(slot,piece)"
      by (cases entry) auto
    have slot_bound: "slot<period"
      using Cons.prems(2) entry by simp
    have valid: "valid_entry (slot,piece)"
      using Cons.prems(3) entry by simp
    have tail_bounded: "list_all (\<lambda>entry. fst entry < period) entries"
      using Cons.prems(2) by simp
    have tail_valid: "list_all valid_entry entries"
      using Cons.prems(3) by simp
    have transition:
      "?consistent (paint slot piece initial) \<and>
       ?result (paint slot piece initial) =
         (if selected_slot=slot then target else ?result initial)"
      by (rule Cons.prems(4)[OF valid slot_bound Cons.prems(1)])
    have tail:
      "?consistent (foldl (\<lambda>current entry.
          paint (fst entry) (snd entry) current) (paint slot piece initial) entries) \<and>
       ?result (foldl (\<lambda>current entry.
          paint (fst entry) (snd entry) current) (paint slot piece initial) entries) =
         (if selected_slot \<in> set (map fst entries) then target else
           ?result (paint slot piece initial))"
      by (rule Cons.IH[OF conjunct1[OF transition] tail_bounded tail_valid
        Cons.prems(4)])
    show ?case
      using tail transition entry
      by (cases "selected_slot=slot";
          cases "selected_slot \<in> set (map fst entries)") (auto simp: entry)
  qed
qed

end
