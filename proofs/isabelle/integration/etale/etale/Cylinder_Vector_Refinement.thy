theory Cylinder_Vector_Refinement
  imports Runtime_Cylinder_Refinement
begin

text \<open>Coefficient semantics of the runtime's signed fold and shifted join.
These are vector equalities, not equality after scalar evaluation. Width is
positive; the signs +1 and -1 are special cases of the integer parameter.\<close>

definition cylinder_basis :: "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "cylinder_basis w s i k = (if i mod w = k then s^(i div w) else 0)"

definition cylinder_vector :: "nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int" where
  "cylinder_vector w s xs k = (\<Sum>i<length xs. xs!i * cylinder_basis w s i k)"

definition cylinder_shift ::
  "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" where
  "cylinder_shift w s n A k = (\<Sum>j<w. A j * cylinder_basis w s (n+j) k)"

lemma cylinder_basis_shift:
  assumes w: "0<w"
  shows "cylinder_shift w s n (cylinder_basis w s i) k = cylinder_basis w s (n+i) k"
proof -
  have rem: "(n+i mod w) mod w = (n+i) mod w" by presburger
  have quo: "i div w + (n+i mod w) div w = (n+i) div w"
    using div_add1_eq[of n i w] div_add1_eq[of n "i mod w" w]
    by (simp only: mod_mod_trivial mod_div_trivial add_0_right; arith)
  have summand: "\<And>j. cylinder_basis w s i j * cylinder_basis w s (n+j) k =
      (if i mod w=j then s^(i div w) * cylinder_basis w s (n+j) k else 0)"
    by (simp add: cylinder_basis_def)
  have eval: "cylinder_shift w s n (cylinder_basis w s i) k =
      cylinder_basis w s i (i mod w) * cylinder_basis w s (n+i mod w) k"
    unfolding cylinder_shift_def
    by (simp only: summand sum.delta' finite_lessThan; simp add: cylinder_basis_def w)
  show ?thesis
    using eval by (simp add: cylinder_basis_def rem quo flip: power_add)
qed

lemma cylinder_shift_vector:
  assumes "0<w"
  shows "cylinder_shift w s n (cylinder_vector w s xs) k =
    (\<Sum>i<length xs. xs!i * cylinder_basis w s (n+i) k)"
proof -
  have "cylinder_shift w s n (cylinder_vector w s xs) k =
      (\<Sum>i<length xs. xs!i * cylinder_shift w s n (cylinder_basis w s i) k)"
    unfolding cylinder_shift_def cylinder_vector_def
    by (simp only: sum_distrib_right sum_distrib_left mult.assoc) (rule sum.swap)
  then show ?thesis using cylinder_basis_shift[OF assms] by simp
qed

lemma cylinder_sum_prefix_add:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i<n+m. f i) = (\<Sum>i<n. f i) + (\<Sum>i<m. f (n+i))"
  by (induction m) (simp_all add: add.assoc)

theorem cylinder_vector_append_refinement:
  assumes "0<w"
  shows "cylinder_vector w s (xs@ys) k = cylinder_vector w s xs k +
    cylinder_shift w s (length xs) (cylinder_vector w s ys) k"
  by (simp add: cylinder_shift_vector[OF assms] cylinder_sum_prefix_add nth_append
      cylinder_vector_def)

theorem cylinder_vector_clip_refinement:
  assumes "0<w"
  shows "cylinder_vector w s (take n (xs@ys)) k =
    cylinder_vector w s (take n xs) k + cylinder_shift w s (length (take n xs))
      (cylinder_vector w s (take (n-length xs) ys)) k"
  by (simp add: take_append cylinder_vector_append_refinement[OF assms])

theorem cylinder_vector_mirror_refinement:
  "cylinder_vector w s xs k - cylinder_vector w s (rev xs) k =
    folded_difference (length xs) s (\<lambda>i. xs!i) w k"
  by (simp add: cylinder_vector_def cylinder_basis_def folded_difference_def
      rev_nth flip: sum_subtractf)
     (rule sum.cong; auto simp: algebra_simps split: if_splits)

theorem cylinder_vector_terminal_zero_iff_palindrome:
  assumes "length xs \<le> w"
  shows "(\<forall>k<w. cylinder_vector w s xs k - cylinder_vector w s (rev xs) k=0)
    = (xs=rev xs)"
  using terminal_mirror_vector_zero_iff_palindrome[OF assms, of s "\<lambda>i. xs!i"]
  by (simp add: cylinder_vector_mirror_refinement list_eq_iff_nth_eq rev_nth)

ML \<open>
 val _ = if null (Thm_Deps.all_oracles @{thms cylinder_basis_shift
   cylinder_shift_vector cylinder_vector_append_refinement
   cylinder_vector_clip_refinement cylinder_vector_mirror_refinement
   cylinder_vector_terminal_zero_iff_palindrome})
   then () else error "Cylinder vector refinement oracle dependency";
\<close>
end
