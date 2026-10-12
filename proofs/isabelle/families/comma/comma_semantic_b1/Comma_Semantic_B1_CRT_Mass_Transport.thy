theory Comma_Semantic_B1_CRT_Mass_Transport
  imports Comma_Semantic_B1_CRT_Cardinality Comma_Semantic_B1_CRT_Column_DAG
begin

text \<open>
The recursive mass equation is instantiated structurally from a checked
column step and an exact map of already-certified child masses.  Arithmetic
on the resulting closed numeral vector is a separate proof obligation.
\<close>

lemma comma_semantic_b1_crt_column_mass_node_from_map:
  assumes child_masses:
    "map comma_semantic_b1_crt_column_mass children = masses"
  shows "comma_semantic_b1_crt_column_mass (Comma_CRT_Node level children) =
    sum_list masses div comma_crt_period level"
  using child_masses by simp

lemma comma_semantic_b1_crt_column_mass_step:
  assumes step:
      "comma_semantic_b1_crt_column_at dag cid = Comma_CRT_Node level children"
    and child_masses:
      "map comma_semantic_b1_crt_column_mass children = masses"
  shows "comma_semantic_b1_crt_column_mass
      (comma_semantic_b1_crt_column_at dag cid) =
    sum_list masses div comma_crt_period level"
proof -
  have "comma_semantic_b1_crt_column_mass
      (comma_semantic_b1_crt_column_at dag cid) =
    comma_semantic_b1_crt_column_mass (Comma_CRT_Node level children)"
    by (simp only: step)
  also have "... = sum_list masses div comma_crt_period level"
    by (rule comma_semantic_b1_crt_column_mass_node_from_map[OF child_masses])
  finally show ?thesis .
qed

lemma comma_semantic_b1_crt_column_mass_repeated_children:
  "comma_semantic_b1_crt_column_mass (Comma_CRT_Node level [column, column]) =
    (comma_semantic_b1_crt_column_mass column +
      comma_semantic_b1_crt_column_mass column) div comma_crt_period level"
  by (simp only: comma_semantic_b1_crt_column_mass.simps(2) sum_list.Cons
      sum_list.Nil list.map add_0_right)

lemma comma_semantic_b1_crt_sum_list_mset:
  fixes xs ys :: "nat list"
  assumes "mset xs = mset ys"
  shows "sum_list xs = sum_list ys"
proof -
  have left: "sum_list xs = sum_mset (mset xs)"
    by (simp only: sum_mset_sum_list)
  have middle: "sum_mset (mset xs) = sum_mset (mset ys)"
    by (rule arg_cong[OF assms])
  have right: "sum_mset (mset ys) = sum_list ys"
    by (simp only: sum_mset_sum_list)
  have chain: "sum_list xs = sum_mset (mset ys)"
    by (rule trans[OF left middle])
  show ?thesis by (rule trans[OF chain right])
qed

lemma comma_semantic_b1_crt_list_all_subset:
  assumes covered: "set xs \<subseteq> set ys"
    and checked: "list_all P ys"
  shows "list_all P xs"
  using covered checked by (auto simp only: list_all_iff)

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_column_mass_node_from_map
    comma_semantic_b1_crt_column_mass_step
    comma_semantic_b1_crt_column_mass_repeated_children
    comma_semantic_b1_crt_sum_list_mset
    comma_semantic_b1_crt_list_all_subset};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "B1 CRT mass transport theorem has an oracle dependency";
  val _ = Thm.consolidate checked;
  val _ = Comma_Proof_Profile.report
    "B1 CRT mass transport stage=closed-kernel-checked";
\<close>

end
