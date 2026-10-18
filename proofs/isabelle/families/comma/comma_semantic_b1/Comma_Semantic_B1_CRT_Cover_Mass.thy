theory Comma_Semantic_B1_CRT_Cover_Mass
  imports Comma_Semantic_B1_CRT_Parent_Partition
    Comma_Semantic_B1_CRT_Cardinality
begin

lemma comma_semantic_b1_crt_cells_partition_from_eval_cover_mass:
  fixes columns :: "comma_crt_column list"
  assumes admitted:
      "list_all (comma_crt_admitted 0) columns"
    and covered:
      "\<forall>phase<924. \<exists>i<length columns.
        comma_crt_eval phase (columns!i)"
    and mass:
      "sum_list (map comma_semantic_b1_crt_column_mass columns)=924"
  shows "comma_semantic_b1_crt_cells_partition {..<924}
    (map comma_crt_set columns)"
proof -
  let ?cells = "map comma_crt_set columns"
  have bounded:
      "list_all (\<lambda>cell. cell\<subseteq>{..<924}) ?cells"
    by (auto simp: list_all_iff comma_crt_set_def)
  have cell_cover:
      "\<forall>phase\<in>{..<924}. \<exists>i<length ?cells. phase\<in>?cells!i"
  proof (intro ballI)
    fix phase :: nat
    assume phase: "phase\<in>{..<924}"
    then have phase_bound: "phase<924" by simp
    obtain i where index: "i<length columns"
      and active: "comma_crt_eval phase (columns!i)"
      using covered phase_bound by blast
    have index_cells: "i<length ?cells" using index by simp
    have member: "phase\<in>?cells!i"
      using phase_bound active index
      by (simp add: nth_map comma_crt_set_def)
    show "\<exists>i<length ?cells. phase\<in>?cells!i"
      by (rule exI[of _ i], rule conjI[OF index_cells member])
  qed
  have union_eq:
      "comma_semantic_b1_crt_list_union ?cells={..<924}"
  proof (rule subset_antisym)
    show "comma_semantic_b1_crt_list_union ?cells\<subseteq>{..<924}"
      by (rule comma_semantic_b1_crt_list_union_subset[OF bounded])
    show "{..<924}\<subseteq>comma_semantic_b1_crt_list_union ?cells"
    proof
      fix phase :: nat
      assume phase: "phase\<in>{..<924}"
      obtain i where index: "i<length ?cells"
        and member: "phase\<in>?cells!i"
        using cell_cover phase by blast
      have cell_in_list: "?cells!i\<in>set ?cells"
        by (rule nth_mem[OF index])
      show "phase\<in>comma_semantic_b1_crt_list_union ?cells"
        using cell_in_list member
        by (auto simp: comma_semantic_b1_crt_list_union_def)
    qed
  qed
  have card_mass:
      "sum_list (map card ?cells)=924"
    using comma_semantic_b1_crt_column_list_card_mass[OF admitted] mass
    by simp
  have exact:
      "card (comma_semantic_b1_crt_list_union ?cells)=
        sum_list (map card ?cells)"
    using union_eq card_mass by simp
  have pairwise_list:
      "comma_semantic_b1_crt_list_pairwise_disjoint ?cells"
    by (rule comma_semantic_b1_crt_list_pairwise_disjoint_of_card_eq
      [OF bounded finite_lessThan exact])
  have pairwise:
      "\<forall>i<length ?cells. \<forall>j<length ?cells.
        i\<noteq>j \<longrightarrow> ?cells!i\<inter>?cells!j={}"
    by (rule comma_semantic_b1_crt_list_pairwise_disjoint_nth[OF pairwise_list])
  have bounded_nth:
      "\<forall>i<length ?cells. ?cells!i\<subseteq>{..<924}"
  proof (intro allI impI)
    fix i
    assume i: "i<length ?cells"
    have cell_in_list: "?cells!i\<in>set ?cells"
      by (rule nth_mem[OF i])
    show "?cells!i\<subseteq>{..<924}"
      using bounded cell_in_list by (auto simp: list_all_iff)
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_cells_partition_def
    using bounded_nth cell_cover pairwise by blast
qed

lemma comma_semantic_b1_crt_occurrence_wellformed_from_partition:
  fixes occurrence :: comma_semantic_b1_crt_occurrence
  assumes binding:
      "comma_semantic_b1_crt_occurrence_binding_check occurrence"
    and admitted:
      "list_all (comma_crt_admitted 0)
        (comma_semantic_b1_crt_occurrence_columns occurrence)"
    and supported:
      "list_all comma_crt_supported
        (comma_semantic_b1_crt_occurrence_columns occurrence)"
    and partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map comma_crt_set (comma_semantic_b1_crt_occurrence_columns occurrence))"
  shows "comma_semantic_b1_crt_occurrence_wellformed occurrence"
proof -
  let ?columns = "comma_semantic_b1_crt_occurrence_columns occurrence"
  let ?cells = "map comma_crt_set ?columns"
  have binding_facts:
      "comma_semantic_b1_crt_occurrence_rebase occurrence < 924 \<and>
       length ?columns = length (comma_semantic_b1_crt_occurrence_beta occurrence) \<and>
       ?columns \<noteq> []"
    using binding by (simp add: comma_semantic_b1_crt_occurrence_binding_check_def)
  have covered: "comma_semantic_b1_crt_occurrence_covered ?columns"
  proof -
    have cells_cover:
        "\<forall>phase\<in>{..<924}. \<exists>index<length ?cells. phase\<in>?cells!index"
      using partition by (auto simp: comma_semantic_b1_crt_cells_partition_def)
    show ?thesis
      unfolding comma_semantic_b1_crt_occurrence_covered_def
        comma_semantic_b1_crt_occurrence_indexed_columns_def
    proof (intro allI impI)
      fix phase :: nat
      assume phase_bound: "phase < 924"
      obtain index where index_bound: "index < length ?cells"
        and phase_cell: "phase\<in>?cells!index"
        using cells_cover phase_bound by blast
      have column_bound: "index < length ?columns"
        using index_bound by simp
      have phase_eval: "comma_crt_eval phase (?columns!index)"
        using phase_cell phase_bound column_bound
        by (simp add: nth_map comma_crt_set_def)
      have entry:
          "(index, ?columns!index) \<in> set (zip [0..<length ?columns] ?columns)"
        using column_bound by (auto simp: in_set_conv_nth nth_zip)
      show "\<exists>entry\<in>set (zip [0..<length ?columns] ?columns).
          phase \<in> comma_crt_set (snd entry)"
      proof
        show "(index, ?columns!index) \<in>
            set (zip [0..<length ?columns] ?columns)" by (rule entry)
        show "phase \<in> comma_crt_set (snd (index, ?columns!index))"
          using phase_eval phase_bound by (simp add: comma_crt_set_def)
      qed
    qed
  qed
  have disjoint: "comma_semantic_b1_crt_occurrence_disjoint ?columns"
  proof -
    show ?thesis
      unfolding comma_semantic_b1_crt_occurrence_disjoint_def
        comma_semantic_b1_crt_occurrence_indexed_columns_def
    proof (intro ballI impI)+
      fix left right
      assume left: "left\<in>set (zip [0..<length ?columns] ?columns)"
        and right: "right\<in>set (zip [0..<length ?columns] ?columns)"
        and different: "fst left \<noteq> fst right"
      have left_facts:
          "fst left < length ?columns \<and> snd left = ?columns!fst left"
        using left by (auto simp: in_set_conv_nth nth_zip)
      have right_facts:
          "fst right < length ?columns \<and> snd right = ?columns!fst right"
        using right by (auto simp: in_set_conv_nth nth_zip)
      have cells_disjoint:
          "?cells!fst left \<inter> ?cells!fst right = {}"
        using partition left_facts right_facts different
        by (auto simp: comma_semantic_b1_crt_cells_partition_def nth_map)
      show "comma_crt_set (snd left) \<inter> comma_crt_set (snd right) = {}"
        using cells_disjoint left_facts right_facts by simp
    qed
  qed
  show ?thesis
    using binding_facts admitted supported covered disjoint
    by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms comma_semantic_b1_crt_cells_partition_from_eval_cover_mass
        comma_semantic_b1_crt_occurrence_wellformed_from_partition})
    then () else error "Comma cover/mass oracle audit failed"
\<close>

end
