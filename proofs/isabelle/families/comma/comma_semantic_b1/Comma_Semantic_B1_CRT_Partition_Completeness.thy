theory Comma_Semantic_B1_CRT_Partition_Completeness
  imports Comma_Semantic_B1_CRT_Indexed_Labels Comma_CRT_Support
begin

ML \<open>
structure Comma_Semantic_B1_CRT_Completeness_Profile =
struct
  val mark = Comma_Proof_Profile.timer "CRT partition completeness"
end
\<close>

text \<open>
Semantic partitions of admitted CRT columns are complete for the recursive
cofactor checker.  The key step replaces one CRT digit while preserving all
later coordinates: pairwise coprimality supplies one clock with the chosen
digit and the later residues of the original clock.  Thus every cofactor
branch is again a partition of the full clock universe.
\<close>

definition comma_semantic_b1_crt_partition_replacement_path ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "comma_semantic_b1_crt_partition_replacement_path level digit phase =
    (level,digit) # map (\<lambda>k. (k,phase mod comma_crt_period k))
      [Suc level..<4]"

lemma comma_semantic_b1_crt_partition_replacement_path_levels:
  assumes level: "level<4"
  shows "distinct (map fst
      (comma_semantic_b1_crt_partition_replacement_path level digit phase))"
    "\<forall>entry\<in>set
      (comma_semantic_b1_crt_partition_replacement_path level digit phase).
      fst entry<4"
  using level
  by (simp_all add: comma_semantic_b1_crt_partition_replacement_path_def
      distinct_upt o_def)

lemma comma_semantic_b1_crt_partition_replacement_path_pairwise:
  assumes level: "level<4"
    and digit: "digit<comma_crt_period level"
  shows "\<forall>i\<in>set
        (comma_semantic_b1_crt_partition_replacement_path level digit phase).
       \<forall>j\<in>set
        (comma_semantic_b1_crt_partition_replacement_path level digit phase).
       i\<noteq>j \<longrightarrow>
         coprime (comma_crt_period (fst i)) (comma_crt_period (fst j))"
proof (intro ballI allI impI)
  fix i j
  assume i: "i\<in>set
      (comma_semantic_b1_crt_partition_replacement_path level digit phase)"
    and j: "j\<in>set
      (comma_semantic_b1_crt_partition_replacement_path level digit phase)"
    and different: "i\<noteq>j"
  have distinct_levels:
      "distinct (map fst
        (comma_semantic_b1_crt_partition_replacement_path level digit phase))"
    by (rule comma_semantic_b1_crt_partition_replacement_path_levels(1)[OF level])
  have injective:
      "inj_on fst (set
        (comma_semantic_b1_crt_partition_replacement_path level digit phase))"
    using distinct_levels by (auto simp: distinct_map)
  have levels_different: "fst i\<noteq>fst j"
  proof
    assume equal: "fst i=fst j"
    have "i=j" by (rule inj_onD[OF injective equal i j])
    with different show False by simp
  qed
  have i_bound: "fst i<4" and j_bound: "fst j<4"
    using comma_semantic_b1_crt_partition_replacement_path_levels(2)[OF level]
      i j by blast+
  show "coprime (comma_crt_period (fst i)) (comma_crt_period (fst j))"
    by (rule comma_crt_period_pairwise_coprime[OF i_bound j_bound levels_different])
qed

lemma comma_semantic_b1_crt_partition_phase_replacement:
  assumes level: "level<4"
    and digit: "digit<comma_crt_period level"
  obtains replacement where
    "replacement<924"
    "replacement mod comma_crt_period level=digit"
    "\<And>later. level<later \<Longrightarrow> later<4 \<Longrightarrow>
      replacement mod comma_crt_period later=phase mod comma_crt_period later"
proof -
  let ?path =
    "comma_semantic_b1_crt_partition_replacement_path level digit phase"
  have crt:
      "\<exists>witness. \<forall>entry\<in>set ?path.
        [witness=snd entry] (mod comma_crt_period (fst entry))"
  proof (rule chinese_remainder_nat)
    show "finite (set ?path)" by simp
    show "\<forall>i\<in>set ?path. \<forall>j\<in>set ?path. i\<noteq>j \<longrightarrow>
        coprime (comma_crt_period (fst i)) (comma_crt_period (fst j))"
      by (rule comma_semantic_b1_crt_partition_replacement_path_pairwise
        [OF level digit])
  qed
  then obtain witness where congruences:
      "\<forall>entry\<in>set ?path.
        [witness=snd entry] (mod comma_crt_period (fst entry))"
    by blast
  let ?replacement = "witness mod 924"
  have replacement_bound: "?replacement<924" by simp
  have residue:
      "?replacement mod comma_crt_period (fst entry)=snd entry"
    if entry: "entry\<in>set ?path" for entry
  proof -
    have entry_level: "fst entry<4"
      using comma_semantic_b1_crt_partition_replacement_path_levels(2)[OF level]
        entry by blast
    have target_bound: "snd entry<comma_crt_period (fst entry)"
    proof -
      have entry_cases:
          "entry=(level,digit) \<or>
           (\<exists>later. later\<in>set [Suc level..<4] \<and>
             entry=(later,phase mod comma_crt_period later))"
        using entry by (auto simp: comma_semantic_b1_crt_partition_replacement_path_def)
      consider (current) "entry=(level,digit)"
        | (later) k where "k\<in>set [Suc level..<4]"
            "entry=(k,phase mod comma_crt_period k)"
        using entry_cases by blast
      then show ?thesis
      proof cases
        case current
        then show ?thesis using digit by simp
      next
        case (later k)
        have later_bound: "k<4" using later(1) by simp
        have positive: "0<comma_crt_period k"
          by (rule comma_crt_period_positive[OF later_bound])
        show ?thesis using later(2) positive by simp
      qed
    qed
    have congruent:
        "[witness=snd entry] (mod comma_crt_period (fst entry))"
      using congruences entry by blast
    have witness_residue:
        "witness mod comma_crt_period (fst entry)=snd entry"
      using congruent target_bound by (simp add: cong_def)
    have divides: "comma_crt_period (fst entry) dvd 924"
      by (rule comma_crt_period_divides[OF entry_level])
    have reduce:
        "(witness mod 924) mod comma_crt_period (fst entry)=
          witness mod comma_crt_period (fst entry)"
      by (rule mod_mod_cancel[OF divides])
    show ?thesis using reduce witness_residue by simp
  qed
  have current: "(level,digit)\<in>set ?path"
    by (simp add: comma_semantic_b1_crt_partition_replacement_path_def)
  have current_residue: "?replacement mod comma_crt_period level=digit"
    using residue[OF current] by simp
  have later_residue:
      "?replacement mod comma_crt_period later=phase mod comma_crt_period later"
    if later: "level<later" "later<4" for later
  proof -
    have range: "later\<in>set [Suc level..<4]"
      using later by simp
    have entry:
        "(later,phase mod comma_crt_period later)\<in>set ?path"
      using range by (auto simp: comma_semantic_b1_crt_partition_replacement_path_def)
    show ?thesis using residue[OF entry] by simp
  qed
  show thesis
    by (rule that[OF replacement_bound current_residue later_residue])
qed

ML \<open>
  val _ = Thm.consolidate [@{thm comma_semantic_b1_crt_partition_phase_replacement}];
  val _ = Comma_Semantic_B1_CRT_Completeness_Profile.mark "phase-replacement";
\<close>

lemma comma_semantic_b1_crt_eval_equal_on_later_residues:
  assumes admitted: "comma_crt_admitted lower column"
    and residues: "\<And>level. lower\<le>level \<Longrightarrow> level<4 \<Longrightarrow>
      left mod comma_crt_period level=right mod comma_crt_period level"
  shows "comma_crt_eval left column=comma_crt_eval right column"
  using admitted residues
proof (induction column arbitrary: lower)
  case (Comma_CRT_Bool payload)
  then show ?case by simp
next
  case (Comma_CRT_Node node_level children)
  have lower: "lower\<le>node_level"
    and level: "node_level<4"
    and width: "length children=comma_crt_period node_level"
    and child_admitted:
      "\<forall>child\<in>set children.
        comma_crt_admitted (Suc node_level) child"
    using Comma_CRT_Node.prems(1) by (auto simp: list_all_iff)
  have index_left:
      "left mod comma_crt_period node_level<length children"
    using comma_crt_period_positive[OF level] width by simp
  have index_right:
      "right mod comma_crt_period node_level<length children"
    using comma_crt_period_positive[OF level] width by simp
  have indices:
      "left mod comma_crt_period node_level=
       right mod comma_crt_period node_level"
    by (rule Comma_CRT_Node.prems(2)[where level=node_level, OF lower level])
  have left_child:
      "children!(left mod comma_crt_period node_level)\<in>set children"
    by (rule nth_mem[OF index_left])
  have child_valid:
      "comma_crt_admitted (Suc node_level)
        (children!(left mod comma_crt_period node_level))"
    using child_admitted left_child by blast
  have child_residues:
      "\<And>later. Suc node_level\<le>later \<Longrightarrow> later<4 \<Longrightarrow>
        left mod comma_crt_period later=right mod comma_crt_period later"
  proof -
    fix later
    assume child_lower: "Suc node_level\<le>later" and later: "later<4"
    have original_lower: "lower\<le>later" using lower child_lower by arith
    show "left mod comma_crt_period later=right mod comma_crt_period later"
      by (rule Comma_CRT_Node.prems(2)[OF original_lower later])
  qed
  have child_equal:
      "comma_crt_eval left (children!(left mod comma_crt_period node_level))=
       comma_crt_eval right (children!(left mod comma_crt_period node_level))"
    using Comma_CRT_Node.IH[OF left_child child_valid] child_residues by blast
  show ?case
    using level width indices index_left index_right child_equal
    by (simp add: comma_crt_eval_node_selected)
qed

ML \<open>
  val _ = Thm.consolidate
    [@{thm comma_semantic_b1_crt_eval_equal_on_later_residues}];
  val _ = Comma_Semantic_B1_CRT_Completeness_Profile.mark "eval-invariance";
\<close>

lemma comma_semantic_b1_crt_partition_cofactor_eval_replacement:
  assumes admitted: "comma_crt_admitted level column"
    and level: "level<4"
    and digit: "digit<comma_crt_period level"
    and digit_at_replacement:
      "replacement mod comma_crt_period level=digit"
    and later_residues:
      "\<And>later. level<later \<Longrightarrow> later<4 \<Longrightarrow>
        replacement mod comma_crt_period later=phase mod comma_crt_period later"
  shows "comma_crt_eval phase (comma_crt_cofactor_or_false level digit column)=
    comma_crt_eval replacement column"
proof -
  obtain child where cofactor:
      "comma_crt_cofactor level digit column=Some child"
    and child_admitted: "comma_crt_admitted (Suc level) child"
    and child_eval:
      "comma_crt_eval replacement child=comma_crt_eval replacement column"
    by (rule comma_crt_cofactor_exact[OF admitted level
        digit_at_replacement[symmetric]])
  have cofactor_or_false:
      "comma_crt_cofactor_or_false level digit column=child"
    using cofactor by (simp add: comma_crt_cofactor_or_false_def)
  have child_phase:
      "comma_crt_eval phase child=comma_crt_eval replacement child"
    by (rule comma_semantic_b1_crt_eval_equal_on_later_residues
      [OF child_admitted])
      (use later_residues in auto)
  show ?thesis using child_phase child_eval cofactor_or_false by simp
qed

lemma comma_semantic_b1_crt_partition_cofactor_cells_partition:
  assumes partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map comma_crt_set columns)"
    and admitted: "list_all (comma_crt_admitted level) columns"
    and level: "level<4"
    and digit: "digit<comma_crt_period level"
  shows "comma_semantic_b1_crt_cells_partition {..<924}
      (map comma_crt_set
        (map (comma_crt_cofactor_or_false level digit) columns))"
proof -
  let ?source = "map comma_crt_set columns"
  let ?cofactored =
    "map comma_crt_set (map (comma_crt_cofactor_or_false level digit) columns)"
  have replacement:
      "\<exists>source_phase<924.
        source_phase mod comma_crt_period level=digit \<and>
        (\<forall>later. level<later \<longrightarrow> later<4 \<longrightarrow>
          source_phase mod comma_crt_period later=phase mod comma_crt_period later)"
    for phase :: nat
    using comma_semantic_b1_crt_partition_phase_replacement[OF level digit, of phase]
    by blast
  have pointwise:
      "\<exists>source_phase<924.
        source_phase mod comma_crt_period level=digit \<and>
        (\<forall>later. level<later \<longrightarrow> later<4 \<longrightarrow>
          source_phase mod comma_crt_period later=phase mod comma_crt_period later) \<and>
        (\<forall>i<length columns.
          comma_crt_eval phase
            (comma_crt_cofactor_or_false level digit (columns!i))=
          comma_crt_eval source_phase (columns!i))"
    for phase :: nat
  proof -
    obtain source_phase where source_bound: "source_phase<924"
      and current: "source_phase mod comma_crt_period level=digit"
      and later:
        "\<And>later. level<later \<Longrightarrow> later<4 \<Longrightarrow>
          source_phase mod comma_crt_period later=phase mod comma_crt_period later"
      using replacement[of phase] by blast
    have each:
        "comma_crt_eval phase
            (comma_crt_cofactor_or_false level digit (columns!i))=
          comma_crt_eval source_phase (columns!i)"
      if i: "i<length columns" for i
    proof -
      have column_admitted: "comma_crt_admitted level (columns!i)"
        using admitted i by (simp add: list_all_iff)
      show ?thesis
        by (rule comma_semantic_b1_crt_partition_cofactor_eval_replacement
          [OF column_admitted level digit current later])
    qed
    show ?thesis
      using source_bound current later each by blast
  qed
  have bounded:
      "\<forall>i<length ?cofactored. ?cofactored!i\<subseteq>{..<924}"
    by (auto simp: comma_crt_set_def)
  have covered:
      "\<forall>phase\<in>{..<924}. \<exists>i<length ?cofactored. phase\<in>?cofactored!i"
  proof (intro ballI)
    fix phase :: nat
    assume phase: "phase\<in>{..<924}"
    obtain source_phase where source_bound: "source_phase<924"
      and current: "source_phase mod comma_crt_period level=digit"
      and later:
        "\<forall>later. level<later \<longrightarrow> later<4 \<longrightarrow>
          source_phase mod comma_crt_period later=phase mod comma_crt_period later"
      and evals:
        "\<forall>i<length columns.
          comma_crt_eval phase
            (comma_crt_cofactor_or_false level digit (columns!i))=
          comma_crt_eval source_phase (columns!i)"
      using pointwise[where phase = phase] by blast
    have source_covered:
        "\<exists>i<length ?source. source_phase\<in>?source!i"
      using partition source_bound
      by (auto simp: comma_semantic_b1_crt_cells_partition_def)
    then obtain i where i: "i<length ?source"
      and member: "source_phase\<in>?source!i" by blast
    have i_columns: "i<length columns" using i by simp
    have eval_source: "comma_crt_eval source_phase (columns!i)"
      using member i_columns by (simp add: comma_crt_set_def nth_map)
    have eval_cofactor:
        "comma_crt_eval phase
          (comma_crt_cofactor_or_false level digit (columns!i))"
      using evals i_columns eval_source by blast
    show "\<exists>i<length ?cofactored. phase\<in>?cofactored!i"
      using i eval_cofactor phase
      by (intro exI[of _ i]) (simp add: comma_crt_set_def nth_map)
  qed
  have pairwise:
      "\<forall>i<length ?cofactored. \<forall>j<length ?cofactored.
        i\<noteq>j \<longrightarrow> ?cofactored!i\<inter>?cofactored!j={}"
  proof (intro allI impI allI impI impI)
    fix i j
    assume i: "i<length ?cofactored" and j: "j<length ?cofactored"
      and different: "i\<noteq>j"
    show "?cofactored!i\<inter>?cofactored!j={}"
    proof (rule ccontr)
      assume nonempty: "?cofactored!i\<inter>?cofactored!j\<noteq>{}"
      then obtain phase where phase_i: "phase\<in>?cofactored!i"
        and phase_j: "phase\<in>?cofactored!j" by blast
      have phase_bound: "phase<924"
        using bounded i phase_i by blast
      obtain source_phase where source_bound: "source_phase<924"
        and current: "source_phase mod comma_crt_period level=digit"
        and later:
          "\<forall>later. level<later \<longrightarrow> later<4 \<longrightarrow>
            source_phase mod comma_crt_period later=phase mod comma_crt_period later"
        and evals:
          "\<forall>k<length columns.
            comma_crt_eval phase
              (comma_crt_cofactor_or_false level digit (columns!k))=
            comma_crt_eval source_phase (columns!k)"
        using pointwise[where phase = phase] by blast
      have i_columns: "i<length columns" and j_columns: "j<length columns"
        using i j by simp_all
      have eval_i: "comma_crt_eval source_phase (columns!i)"
        using phase_i evals i_columns source_bound
        by (auto simp: comma_crt_set_def nth_map)
      have eval_j: "comma_crt_eval source_phase (columns!j)"
        using phase_j evals j_columns source_bound
        by (auto simp: comma_crt_set_def nth_map)
      have source_i: "source_phase\<in>?source!i"
        using eval_i source_bound i_columns
        by (simp add: comma_crt_set_def nth_map)
      have source_j: "source_phase\<in>?source!j"
        using eval_j source_bound j_columns
        by (simp add: comma_crt_set_def nth_map)
      have disjoint: "?source!i\<inter>?source!j={}"
        using partition i_columns j_columns different
        by (auto simp: comma_semantic_b1_crt_cells_partition_def)
      show False using disjoint source_i source_j by blast
    qed
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_cells_partition_def
    using bounded covered pairwise by blast
qed

ML \<open>
  val _ = Thm.consolidate
    [@{thm comma_semantic_b1_crt_partition_cofactor_cells_partition}];
  val _ = Comma_Semantic_B1_CRT_Completeness_Profile.mark "cofactor-partition";
\<close>

lemma comma_semantic_b1_crt_partition_witness_of_cells_partition:
  assumes level: "level\<le>4"
    and admitted: "list_all (comma_crt_admitted level) columns"
    and partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map comma_crt_set columns)"
  shows "comma_semantic_b1_crt_partition_witness level columns"
  using level admitted partition
proof (induction "4-level" arbitrary: level columns rule: less_induct)
  case less
  ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness induction entered"\<close>
  show ?case
  proof (cases "level=4")
  case terminal_level: True
  ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness terminal entered"\<close>
  have level_eq: "level=4" using terminal_level .
  have all_bool: "list_all (\<lambda>column. \<exists>truth. column=Comma_CRT_Bool truth) columns"
  proof (unfold list_all_iff)
    show "\<forall>column\<in>set columns. \<exists>truth. column=Comma_CRT_Bool truth"
    proof (intro ballI)
      fix column
      assume column: "column\<in>set columns"
      have valid: "comma_crt_admitted 4 column"
        using less.prems(2) column level_eq by (simp add: list_all_iff)
      show "\<exists>truth. column=Comma_CRT_Bool truth"
      proof (cases column)
        case (Comma_CRT_Bool truth)
        then show ?thesis by blast
      next
        case (Comma_CRT_Node node_level children)
        have "4\<le>node_level \<and> node_level<4"
          using valid Comma_CRT_Node by simp
        then show ?thesis by arith
      qed
    qed
  qed
  ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness terminal shape checked"\<close>
  have covered_zero: "\<exists>i<length columns. 0\<in>comma_crt_set (columns!i)"
  proof -
    have partition_parts:
        "(\<forall>i<length (map comma_crt_set columns).
            (map comma_crt_set columns)!i\<subseteq>{..<924}) \<and>
         (\<forall>phase\<in>{..<924}. \<exists>i<length (map comma_crt_set columns).
            phase\<in>(map comma_crt_set columns)!i) \<and>
         (\<forall>i<length (map comma_crt_set columns).
            \<forall>j<length (map comma_crt_set columns).
              i\<noteq>j \<longrightarrow>
                (map comma_crt_set columns)!i \<inter> (map comma_crt_set columns)!j = {})"
      using less.prems(3)
      by (simp only: comma_semantic_b1_crt_cells_partition_def)
    have coverage:
        "\<forall>phase\<in>{..<924}. \<exists>i<length (map comma_crt_set columns).
          phase\<in>(map comma_crt_set columns)!i"
      using partition_parts by blast
    have zero_in: "(0::nat)\<in>{..<924}" by simp
    have zero_covered:
        "\<exists>i<length (map comma_crt_set columns).
          (0::nat)\<in>(map comma_crt_set columns)!i"
      by (rule coverage[rule_format, OF zero_in])
    then obtain i where i: "i<length (map comma_crt_set columns)"
      and member: "(0::nat)\<in>(map comma_crt_set columns)!i" by blast
    have i_columns: "i<length columns" using i by simp
    have member_column: "(0::nat)\<in>comma_crt_set (columns!i)"
      using member i_columns by (simp only: nth_map)
    show ?thesis
    proof (rule exI[where x=i])
      show "i<length columns \<and> (0::nat)\<in>comma_crt_set (columns!i)"
        by (rule conjI[OF i_columns member_column])
    qed
  qed
  ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness terminal zero covered"\<close>
  from covered_zero obtain selected where selected_bound: "selected<length columns"
    and selected_member: "0\<in>comma_crt_set (columns!selected)" by blast
  have selected_eval: "comma_crt_eval 0 (columns!selected)"
    using selected_member by (simp add: comma_crt_set_def)
  ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness terminal selector chosen"\<close>
  have terminal_partition_parts:
      "(\<forall>j<length (map comma_crt_set columns).
          (map comma_crt_set columns)!j\<subseteq>{..<924}) \<and>
       (\<forall>phase\<in>{..<924}. \<exists>j<length (map comma_crt_set columns).
          phase\<in>(map comma_crt_set columns)!j) \<and>
       (\<forall>j<length (map comma_crt_set columns).
          \<forall>k<length (map comma_crt_set columns).
            j\<noteq>k \<longrightarrow>
              (map comma_crt_set columns)!j \<inter>
                (map comma_crt_set columns)!k = {})"
    using less.prems(3)
    by (simp only: comma_semantic_b1_crt_cells_partition_def)
  have terminal_pairwise:
      "\<forall>j<length (map comma_crt_set columns).
        \<forall>k<length (map comma_crt_set columns).
          j\<noteq>k \<longrightarrow>
            (map comma_crt_set columns)!j \<inter>
              (map comma_crt_set columns)!k = {}"
    using terminal_partition_parts by blast
  ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: terminal pairwise cells extracted"\<close>
  have one_hot:
      "columns!i=Comma_CRT_Bool (i=selected)" if i: "i<length columns" for i
  proof -
    have all_bool_set:
        "\<forall>column\<in>set columns. \<exists>truth.
          column=Comma_CRT_Bool truth"
      using all_bool by (simp only: list_all_iff)
    have ith_mem: "columns!i\<in>set columns"
      by (rule nth_mem[OF i])
    have bool_at: "\<exists>truth. columns!i=Comma_CRT_Bool truth"
      by (rule all_bool_set[rule_format, OF ith_mem])
    obtain truth where shape: "columns!i=Comma_CRT_Bool truth"
      using bool_at by blast
    ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: terminal selector shape specialized"\<close>
    show ?thesis
    proof (cases "i=selected")
      case True
      have truth: "truth=True"
        using selected_eval True shape by simp
      show ?thesis using shape True truth by simp
    next
      case False
      have eval_false: "\<not> comma_crt_eval 0 (columns!i)"
      proof
        assume eval_true: "comma_crt_eval 0 (columns!i)"
        have member_i: "0\<in>comma_crt_set (columns!i)"
          using eval_true by (simp add: comma_crt_set_def)
        have member_selected: "0\<in>comma_crt_set (columns!selected)"
          using selected_eval by (simp add: comma_crt_set_def)
        have selected_map_bound:
            "selected<length (map comma_crt_set columns)"
          using selected_bound by simp
        have i_map_bound: "i<length (map comma_crt_set columns)"
          using i by simp
        have selected_neq_i: "selected\<noteq>i" using False by blast
        have disjoint:
            "comma_crt_set (columns!selected)\<inter>
             comma_crt_set (columns!i)={}"
          using terminal_pairwise[rule_format,
              OF selected_map_bound i_map_bound selected_neq_i]
            selected_bound i
          by (simp only: nth_map)
        ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: terminal selector disjointness specialized"\<close>
        show False using disjoint member_selected member_i by blast
      qed
      have truth_false: "truth=False" using eval_false shape by simp
      show ?thesis using shape False truth_false by simp
    qed
  qed
  ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness terminal one-hot checked"\<close>
  have code:
      "columns=map (\<lambda>i. Comma_CRT_Bool (i=selected)) [0..<length columns]"
  proof (rule nth_equalityI)
    show "length columns=length (map (\<lambda>i. Comma_CRT_Bool (i=selected))
        [0..<length columns])" by simp
    fix i
    assume i: "i<length columns"
    have range_index: "i<length [0..<length columns]" using i by simp
    show "columns!i=(map (\<lambda>i. Comma_CRT_Bool (i=selected))
        [0..<length columns])!i"
      using one_hot[OF i] range_index by (simp add: nth_map)
  qed
  ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness terminal code checked"\<close>
  show "comma_semantic_b1_crt_partition_witness level columns"
    unfolding level_eq
    by (rule comma_semantic_b1_crt_partition_witness_terminal[OF selected_bound code])
  ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness terminal finished"\<close>
  next
  case nonterminal_level: False
  ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness nonterminal entered"\<close>
  have level_lt: "level<4" using less.prems(1) nonterminal_level by arith
  have next_level: "Suc level\<le>4" using level_lt by arith
  have smaller: "4-Suc level<4-level" using level_lt by arith
  show "comma_semantic_b1_crt_partition_witness level columns"
  proof (cases "comma_semantic_b1_crt_partition_has_node_at level columns")
    case no_node: False
    ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness skip entered"\<close>
    have advanced:
        "list_all (comma_crt_admitted (Suc level)) columns"
      by (rule comma_semantic_b1_crt_partition_admitted_advance
        [OF less.prems(2) level_lt no_node])
    have child_witness:
        "comma_semantic_b1_crt_partition_witness (Suc level) columns"
      by (rule less.hyps[OF smaller next_level advanced less.prems(3)])
    ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness skip child derived"\<close>
    show ?thesis
      by (rule comma_semantic_b1_crt_partition_witness_skip
        [OF level_lt less.prems(2) no_node child_witness])
    ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness skip assembled"\<close>
  next
    case has_node: True
    ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness node entered"\<close>
    have branch_witness:
      "comma_semantic_b1_crt_partition_witness (Suc level)
        (map (comma_crt_cofactor_or_false level digit) columns)"
      if digit_bound: "digit<comma_crt_period level" for digit
    proof -
      have branch_partition:
          "comma_semantic_b1_crt_cells_partition {..<924}
            (map comma_crt_set
              (map (comma_crt_cofactor_or_false level digit) columns))"
        by (rule comma_semantic_b1_crt_partition_cofactor_cells_partition
          [OF less.prems(3) less.prems(2) level_lt digit_bound])
      ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness branch partition derived"\<close>
      have branch_admitted:
          "list_all (comma_crt_admitted (Suc level))
            (map (comma_crt_cofactor_or_false level digit) columns)"
        by (rule comma_semantic_b1_crt_partition_cofactor_admitted
          [OF less.prems(2) level_lt digit_bound])
      ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness branch admission derived"\<close>
      show ?thesis
        by (rule less.hyps[OF smaller next_level branch_admitted branch_partition])
    qed
    ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness branch child derived"\<close>
    have branches:
        "list_all (\<lambda>digit.
          comma_semantic_b1_crt_partition_witness (Suc level)
            (map (comma_crt_cofactor_or_false level digit) columns))
          [0..<comma_crt_period level]"
      using branch_witness by (simp add: list_all_iff)
    ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness branches collected"\<close>
    show ?thesis
      by (rule comma_semantic_b1_crt_partition_witness_node
        [OF level_lt less.prems(2) has_node branches])
  qed
  ML_prf \<open>Comma_Proof_Profile.report "CRT partition completeness: witness case closed"\<close>
  qed
qed

ML \<open>
  val _ = Thm.consolidate
    [@{thm comma_semantic_b1_crt_partition_witness_of_cells_partition}];
  val _ = Comma_Semantic_B1_CRT_Completeness_Profile.mark "partition-witness";
\<close>

theorem comma_semantic_b1_crt_columns_partition_certified_complete:
  assumes admitted: "list_all (comma_crt_admitted 0) columns"
    and partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map comma_crt_set columns)"
  shows "comma_semantic_b1_crt_columns_partition_certified columns"
proof -
  have witness: "comma_semantic_b1_crt_partition_witness 0 columns"
  proof -
    have level_bound: "0\<le>(4::nat)" by simp
    show ?thesis
      by (rule comma_semantic_b1_crt_partition_witness_of_cells_partition
      [OF level_bound admitted partition])
  qed
  have checked:
      "comma_semantic_b1_crt_partition_cofactor_checked [0..<4] columns=True"
    by (rule comma_semantic_b1_crt_partition_witness_checker_true[OF witness])
  show ?thesis
    using admitted checked
    by (simp add: comma_semantic_b1_crt_columns_partition_certified_def)
qed

ML \<open>
  val _ = Thm.consolidate
    [@{thm comma_semantic_b1_crt_columns_partition_certified_complete}];
  val _ = Comma_Semantic_B1_CRT_Completeness_Profile.mark "checker-complete";
\<close>

ML \<open>
  val checked = @{thm comma_semantic_b1_crt_columns_partition_certified_complete};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Semantic B1 CRT partition completeness" [checked];
\<close>

end
