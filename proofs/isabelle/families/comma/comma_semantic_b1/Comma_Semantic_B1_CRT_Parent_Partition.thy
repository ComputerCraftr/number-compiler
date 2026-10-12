theory Comma_Semantic_B1_CRT_Parent_Partition
  imports Comma_Semantic_B1_CRT_Partition_Coverage
begin

text \<open>
A parent geometry is certified from source coverage and its finite size,
rather than by replaying every cofactor vector.  The cardinality premise is
on the ordered list (so repeated cells are counted with multiplicity).  The
admission premise in the column adapter is retained as a separate caller
contract; the set-level cardinality argument only needs the resulting cells
to be bounded by the clock.
\<close>

definition comma_semantic_b1_crt_list_union :: "nat set list \<Rightarrow> nat set" where
  "comma_semantic_b1_crt_list_union cells =
    (\<Union>cell\<in>set cells. cell)"

fun comma_semantic_b1_crt_list_pairwise_disjoint :: "nat set list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_list_pairwise_disjoint [] = True"
| "comma_semantic_b1_crt_list_pairwise_disjoint (cell#cells) =
    (cell \<inter> comma_semantic_b1_crt_list_union cells = {} \<and>
      comma_semantic_b1_crt_list_pairwise_disjoint cells)"

lemma comma_semantic_b1_crt_list_union_subset:
  assumes bounded: "list_all (\<lambda>cell. cell\<subseteq>universe) cells"
  shows "comma_semantic_b1_crt_list_union cells\<subseteq>universe"
  using bounded by (auto simp: comma_semantic_b1_crt_list_union_def list_all_iff)

lemma comma_semantic_b1_crt_list_union_card_le:
  assumes bounded: "list_all (\<lambda>cell. cell\<subseteq>universe) cells"
    and finite_universe: "finite universe"
  shows "card (comma_semantic_b1_crt_list_union cells) \<le>
    sum_list (map card cells)"
  using bounded finite_universe
proof (induction cells)
  case Nil
  then show ?case by (simp add: comma_semantic_b1_crt_list_union_def)
next
  case (Cons cell cells)
  have cell_subset: "cell\<subseteq>universe" using Cons.prems(1) by simp
  have cells_bounded:
      "list_all (\<lambda>cell. cell\<subseteq>universe) cells"
    using Cons.prems(1) by simp
  have finite_cell: "finite cell"
    by (rule finite_subset[OF cell_subset finite_universe])
  have cells_subset:
      "comma_semantic_b1_crt_list_union cells\<subseteq>universe"
    by (rule comma_semantic_b1_crt_list_union_subset[OF cells_bounded])
  have finite_cells:
      "finite (comma_semantic_b1_crt_list_union cells)"
    by (rule finite_subset[OF cells_subset finite_universe])
  have tail_bound:
      "card (comma_semantic_b1_crt_list_union cells) \<le>
        sum_list (map card cells)"
    by (rule Cons.IH[OF cells_bounded finite_universe])
  have union_bound:
      "card (cell \<union> comma_semantic_b1_crt_list_union cells) \<le>
        card cell + card (comma_semantic_b1_crt_list_union cells)"
    by (rule card_Un_le)
  show ?case
    using union_bound tail_bound
    by (simp add: comma_semantic_b1_crt_list_union_def sum_list_simps; linarith)
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_list_union_card_le}]; Comma_Proof_Profile.report "Parent partition checked comma_semantic_b1_crt_list_union_card_le"\<close>


lemma comma_semantic_b1_crt_list_pairwise_disjoint_of_card_eq:
  assumes bounded: "list_all (\<lambda>cell. cell\<subseteq>universe) cells"
    and finite_universe: "finite universe"
    and exact:
      "card (comma_semantic_b1_crt_list_union cells) =
        sum_list (map card cells)"
  shows "comma_semantic_b1_crt_list_pairwise_disjoint cells"
proof -
  have aux:
      "list_all (\<lambda>cell. cell\<subseteq>universe) cells \<Longrightarrow>
        card (comma_semantic_b1_crt_list_union cells) =
          sum_list (map card cells) \<Longrightarrow>
        comma_semantic_b1_crt_list_pairwise_disjoint cells" for cells
  proof (induction cells)
    case Nil
    then show ?case by simp
  next
    case (Cons cell cells)
    have cell_subset: "cell\<subseteq>universe" using Cons.prems(1) by simp
    have cells_bounded:
        "list_all (\<lambda>cell. cell\<subseteq>universe) cells"
      using Cons.prems(1) by simp
    have finite_cell: "finite cell"
      by (rule finite_subset[OF cell_subset finite_universe])
    have cells_subset:
        "comma_semantic_b1_crt_list_union cells\<subseteq>universe"
      by (rule comma_semantic_b1_crt_list_union_subset[OF cells_bounded])
    have finite_cells:
        "finite (comma_semantic_b1_crt_list_union cells)"
      by (rule finite_subset[OF cells_subset finite_universe])
    have tail_bound:
        "card (comma_semantic_b1_crt_list_union cells) \<le>
          sum_list (map card cells)"
      by (rule comma_semantic_b1_crt_list_union_card_le
        [OF cells_bounded finite_universe])
    have union_eq:
        "comma_semantic_b1_crt_list_union (cell#cells) =
          cell \<union> comma_semantic_b1_crt_list_union cells"
      by (simp add: comma_semantic_b1_crt_list_union_def)
    have total_exact:
        "card (cell \<union> comma_semantic_b1_crt_list_union cells) =
          card cell + sum_list (map card cells)"
      using Cons.prems(2) by (simp add: union_eq sum_list_simps)
    have tail_exact:
        "card (comma_semantic_b1_crt_list_union cells) =
          sum_list (map card cells)"
    proof (rule le_antisym)
      show "card (comma_semantic_b1_crt_list_union cells) \<le>
          sum_list (map card cells)" by (rule tail_bound)
      have union_upper:
          "card (cell \<union> comma_semantic_b1_crt_list_union cells) \<le>
            card cell + card (comma_semantic_b1_crt_list_union cells)"
        by (rule card_Un_le)
      show "sum_list (map card cells) \<le>
          card (comma_semantic_b1_crt_list_union cells)"
        using union_upper total_exact by linarith
    qed
    have head_inter_card_zero:
        "card (cell \<inter> comma_semantic_b1_crt_list_union cells) = 0"
    proof -
      have union_identity:
          "card (cell \<union> comma_semantic_b1_crt_list_union cells) +
             card (cell \<inter> comma_semantic_b1_crt_list_union cells) =
             card cell + card (comma_semantic_b1_crt_list_union cells)"
        by (rule sym[OF card_Un_Int[OF finite_cell finite_cells]])
      show ?thesis using union_identity total_exact tail_exact by linarith
    qed
    have head_disjoint:
        "cell \<inter> comma_semantic_b1_crt_list_union cells = {}"
    proof -
      have finite_inter:
          "finite (cell \<inter> comma_semantic_b1_crt_list_union cells)"
        by (rule finite_subset[OF Int_lower1 finite_cell])
      show ?thesis
        using head_inter_card_zero finite_inter
        by (simp add: card_eq_0_iff)
    qed
    have tail_pairwise:
        "comma_semantic_b1_crt_list_pairwise_disjoint cells"
      by (rule Cons.IH[OF cells_bounded tail_exact])
    show ?case using head_disjoint tail_pairwise by simp
  qed
  show ?thesis by (rule aux[OF bounded exact])
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_list_pairwise_disjoint_of_card_eq}]; Comma_Proof_Profile.report "Parent partition checked comma_semantic_b1_crt_list_pairwise_disjoint_of_card_eq"\<close>


lemma comma_semantic_b1_crt_list_pairwise_disjoint_nth:
  assumes pairwise:
    "comma_semantic_b1_crt_list_pairwise_disjoint cells"
  shows "\<forall>i<length cells. \<forall>j<length cells.
      i\<noteq>j \<longrightarrow> cells!i \<inter>cells!j={}"
  using pairwise
proof (induction cells)
  case Nil
  then show ?case by simp
next
  case (Cons cell cells)
  have head_disjoint:
      "cell\<inter>comma_semantic_b1_crt_list_union cells={}"
    using Cons.prems by simp
  have tail_pairwise:
      "comma_semantic_b1_crt_list_pairwise_disjoint cells"
    using Cons.prems by simp
  have tail_nth:
      "\<forall>i<length cells. \<forall>j<length cells.
        i\<noteq>j \<longrightarrow> cells!i \<inter> cells!j={}"
    by (rule Cons.IH[OF tail_pairwise])
  have head_nth: "cell\<inter>cells!k={}" if "k<length cells" for k
    using head_disjoint nth_mem[OF that]
    by (auto simp: comma_semantic_b1_crt_list_union_def)
  show ?case
  proof (intro allI impI allI impI impI)
    fix i j
    assume i_bound: "i<length (cell#cells)"
      and j_bound: "j<length (cell#cells)"
      and different: "i\<noteq>j"
    show "(cell#cells)!i \<inter> (cell#cells)!j={}"
    using head_nth tail_nth i_bound j_bound different
    by (cases i; cases j) (auto simp: Int_commute)
  qed
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_list_pairwise_disjoint_nth}]; Comma_Proof_Profile.report "Parent partition checked comma_semantic_b1_crt_list_pairwise_disjoint_nth"\<close>


lemma comma_semantic_b1_crt_list_cardinality_rejects_overlap:
  assumes bounded: "list_all (\<lambda>cell. cell\<subseteq>universe) cells"
    and finite_universe: "finite universe"
    and exact:
      "card (comma_semantic_b1_crt_list_union cells) =
        sum_list (map card cells)"
    and i_bound: "i<length cells"
    and j_bound: "j<length cells"
    and different: "i\<noteq>j"
    and overlap: "cells!i \<inter> cells!j\<noteq>{}"
  shows False
proof -
  have pairwise_list:
      "comma_semantic_b1_crt_list_pairwise_disjoint cells"
    by (rule comma_semantic_b1_crt_list_pairwise_disjoint_of_card_eq
      [OF bounded finite_universe exact])
  have pairwise:
      "\<forall>i<length cells. \<forall>j<length cells.
        i\<noteq>j \<longrightarrow> cells!i \<inter> cells!j={}"
    by (rule comma_semantic_b1_crt_list_pairwise_disjoint_nth[OF pairwise_list])
  have empty: "cells!i \<inter> cells!j={}"
    using pairwise i_bound j_bound different by blast
  show False using overlap empty by blast
qed

ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_list_cardinality_rejects_overlap}]; Comma_Proof_Profile.report "Parent overlap rejection checked"\<close>

lemma comma_semantic_b1_crt_parent_cells_partition_from_cover:
  assumes source_partition:
      "comma_semantic_b1_crt_cells_partition {..<924} source_cells"
    and same_width: "length source_cells=length parent_cells"
    and local_coverage:
      "\<forall>i<length source_cells. source_cells!i\<subseteq>parent_cells!i"
    and parent_bounded:
      "\<forall>i<length parent_cells. parent_cells!i\<subseteq>{..<924}"
    and parent_cardinality:
      "sum_list (map card parent_cells)=924"
  shows "comma_semantic_b1_crt_cells_partition {..<924} parent_cells"
proof -
  have parent_list_bounded:
      "list_all (\<lambda>cell. cell\<subseteq>{..<924}) parent_cells"
    using parent_bounded by (auto simp: list_all_iff in_set_conv_nth; blast)
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: parent bounded"\<close>
  have source_covered:
      "\<forall>phase\<in>{..<924}. \<exists>i<length source_cells.
        phase\<in>source_cells!i"
    using source_partition by (auto simp: comma_semantic_b1_crt_cells_partition_def)
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: source covered"\<close>
  have parent_covered:
      "\<forall>phase\<in>{..<924}. \<exists>i<length parent_cells.
        phase\<in>parent_cells!i"
  proof (intro ballI)
    fix phase :: nat
    assume phase: "phase\<in>{..<924}"
    obtain i where i: "i<length source_cells" and member: "phase\<in>source_cells!i"
      using source_covered[rule_format, OF phase] by blast
    have inclusion: "source_cells!i\<subseteq>parent_cells!i"
      by (rule local_coverage[rule_format, OF i])
    have parent_member: "phase\<in>parent_cells!i"
      by (rule subsetD[OF inclusion member])
    have parent_index: "i<length parent_cells" using i same_width by simp
    show "\<exists>i<length parent_cells. phase\<in>parent_cells!i"
      by (rule exI[of _ i], rule conjI[OF parent_index parent_member])
  qed
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: parent covered"\<close>
  have parent_union:
      "comma_semantic_b1_crt_list_union parent_cells={..<924}"
  proof (rule subset_antisym)
    show "comma_semantic_b1_crt_list_union parent_cells\<subseteq>{..<924}"
      by (rule comma_semantic_b1_crt_list_union_subset[OF parent_list_bounded])
    show "{..<924}\<subseteq>comma_semantic_b1_crt_list_union parent_cells"
    proof
      fix phase :: nat
      assume phase: "phase\<in>{..<924}"
      obtain i where index: "i<length parent_cells"
        and member: "phase\<in>parent_cells!i"
        using parent_covered[rule_format, OF phase] by blast
      have cell: "parent_cells!i\<in>set parent_cells"
        by (rule nth_mem[OF index])
      show "phase\<in>comma_semantic_b1_crt_list_union parent_cells"
        using cell member by (auto simp: comma_semantic_b1_crt_list_union_def)
    qed
  qed
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: parent union"\<close>
  have finite_clock: "finite ({..<924}::nat set)" by simp
  have exact_union:
      "card (comma_semantic_b1_crt_list_union parent_cells) =
        sum_list (map card parent_cells)"
    using parent_union parent_cardinality by simp
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: parent exact union"\<close>
  have pairwise_list:
      "comma_semantic_b1_crt_list_pairwise_disjoint parent_cells"
    by (rule comma_semantic_b1_crt_list_pairwise_disjoint_of_card_eq
      [OF parent_list_bounded finite_clock exact_union])
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: parent pairwise list"\<close>
  have pairwise:
      "\<forall>i<length parent_cells. \<forall>j<length parent_cells.
        i\<noteq>j \<longrightarrow> parent_cells!i \<inter> parent_cells!j={}"
    by (rule comma_semantic_b1_crt_list_pairwise_disjoint_nth[OF pairwise_list])
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: parent pairwise nth"\<close>
  show ?thesis
    unfolding comma_semantic_b1_crt_cells_partition_def
    using parent_bounded parent_covered pairwise by blast
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_parent_cells_partition_from_cover}]; Comma_Proof_Profile.report "Parent partition checked comma_semantic_b1_crt_parent_cells_partition_from_cover"\<close>


text \<open>
This adapter is the exact result-directed bridge used after grouping.  The
source groups are a partition by distinct result labels.  Local containment
is stated in the existing rebased direction; applying the inverse rebase
produces the direct containment required by the cardinality theorem.
\<close>

lemma comma_semantic_b1_crt_parent_cells_partition_from_grouped_cover:
  assumes source_width: "length labels=length source_cells"
    and source_partition:
      "comma_semantic_b1_crt_cells_partition {..<924} source_cells"
    and label_set: "set labels=set results"
    and results_distinct: "distinct results"
    and parent_width: "length results=length parent_cells"
    and rebase: "rebase<924"
    and parent_bounded:
      "\<forall>i<length parent_cells. parent_cells!i\<subseteq>{..<924}"
    and local_coverage:
      "\<forall>i<length results.
        comma_semantic_b1_crt_group_support labels source_cells (results!i) \<subseteq>
          comma_semantic_b1_crt_rebase_set rebase (parent_cells!i)"
    and parent_cardinality:
      "sum_list (map card parent_cells)=924"
  shows "comma_semantic_b1_crt_cells_partition {..<924} parent_cells"
proof -
  have grouped_partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (comma_semantic_b1_crt_group_supports labels source_cells results)"
    by (rule comma_semantic_b1_crt_grouping_preserves_partition
      [OF source_width source_partition label_set results_distinct])
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: grouped partition"\<close>
  have inverse_partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map (comma_semantic_b1_crt_rebase_set ((924-rebase) mod 924))
          (comma_semantic_b1_crt_group_supports labels source_cells results))"
    by (rule comma_semantic_b1_crt_rebase_cells_partition[OF grouped_partition])
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: inverse partition"\<close>
  have inverse_width:
      "length (map (comma_semantic_b1_crt_rebase_set ((924-rebase) mod 924))
        (comma_semantic_b1_crt_group_supports labels source_cells results)) =
        length parent_cells"
    using parent_width by (simp add: comma_semantic_b1_crt_group_supports_def)
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: inverse width"\<close>
  have inverse_coverage:
      "\<forall>i<length
        (map (comma_semantic_b1_crt_rebase_set ((924-rebase) mod 924))
          (comma_semantic_b1_crt_group_supports labels source_cells results)).
        (map (comma_semantic_b1_crt_rebase_set ((924-rebase) mod 924))
          (comma_semantic_b1_crt_group_supports labels source_cells results))!i
          \<subseteq>parent_cells!i"
  proof (intro allI impI)
    fix i
    assume i:
      "i<length
        (map (comma_semantic_b1_crt_rebase_set ((924-rebase) mod 924))
          (comma_semantic_b1_crt_group_supports labels source_cells results))"
    have i_results: "i<length results"
      using i by (simp add: comma_semantic_b1_crt_group_supports_def)
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: inverse index"\<close>
    have source_subset:
        "(comma_semantic_b1_crt_group_supports labels source_cells results)!i
          \<subseteq>comma_semantic_b1_crt_rebase_set rebase
          (parent_cells!i)"
      using local_coverage i_results
      by (simp add: comma_semantic_b1_crt_group_supports_def)
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: source subset"\<close>
    have target_index: "i<length parent_cells" using i inverse_width by simp
    have target_bounded: "parent_cells!i\<subseteq>{..<924}"
      by (rule parent_bounded[rule_format, OF target_index])
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: target bounded"\<close>
    have inverse_target:
        "comma_semantic_b1_crt_rebase_set ((924-rebase) mod 924)
          (comma_semantic_b1_crt_rebase_set rebase (parent_cells!i)) =
          parent_cells!i"
      by (rule comma_semantic_b1_crt_rebase_inverse_set_left[OF rebase target_bounded])
  ML_prf \<open>Comma_Proof_Profile.report "Parent bridge: inverse target"\<close>
    show "(map (comma_semantic_b1_crt_rebase_set ((924-rebase) mod 924))
        (comma_semantic_b1_crt_group_supports labels source_cells results))!i
          \<subseteq>parent_cells!i"
      using source_subset inverse_target i
      by (auto simp: comma_semantic_b1_crt_rebase_set_def)
  qed
  show ?thesis
    by (rule comma_semantic_b1_crt_parent_cells_partition_from_cover
      [OF inverse_partition inverse_width inverse_coverage parent_bounded
        parent_cardinality])
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_parent_cells_partition_from_grouped_cover}]; Comma_Proof_Profile.report "Parent partition checked comma_semantic_b1_crt_parent_cells_partition_from_grouped_cover"\<close>


text \<open>
For concrete parent columns, admission is an explicit input to the bridge;
set boundedness follows from the CRT set definition.  No checker result is
invented by this theorem, and a later caller still has to establish the
cardinality certificate for the ordered parent list.
\<close>

lemma comma_semantic_b1_crt_parent_columns_partition_from_grouped_cover:
  assumes source_width: "length labels=length source_cells"
    and source_partition:
      "comma_semantic_b1_crt_cells_partition {..<924} source_cells"
    and label_set: "set labels=set results"
    and results_distinct: "distinct results"
    and parent_width: "length results=length parent_columns"
    and rebase: "rebase<924"
    and parent_admitted:
      "list_all (comma_crt_admitted 0) parent_columns"
    and local_coverage:
      "\<forall>i<length results.
        comma_semantic_b1_crt_group_support labels source_cells (results!i) \<subseteq>
          comma_semantic_b1_crt_rebase_set rebase
            (comma_crt_set (parent_columns!i))"
    and parent_cardinality:
      "sum_list (map card (map comma_crt_set parent_columns))=924"
  shows "comma_semantic_b1_crt_cells_partition {..<924}
    (map comma_crt_set parent_columns)"
proof -
  have parent_bounded:
      "\<forall>i<length (map comma_crt_set parent_columns).
        (map comma_crt_set parent_columns)!i\<subseteq>{..<924}"
    by (auto simp: comma_crt_set_def)
  have partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map comma_crt_set parent_columns)"
    by (rule comma_semantic_b1_crt_parent_cells_partition_from_grouped_cover
      [OF source_width source_partition label_set results_distinct _ rebase
        parent_bounded _ parent_cardinality])
      (use parent_width local_coverage in auto)
  show ?thesis using partition .
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_parent_columns_partition_from_grouped_cover}]; Comma_Proof_Profile.report "Parent partition checked comma_semantic_b1_crt_parent_columns_partition_from_grouped_cover"\<close>


ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Semantic B1 constructor parent partition"
    @{thms comma_semantic_b1_crt_parent_columns_partition_from_grouped_cover
      comma_semantic_b1_crt_list_cardinality_rejects_overlap}
\<close>

end
