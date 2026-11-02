theory Reverse_Invariant
  imports Reverse_Residuals
begin

definition valid_pair :: "nat list \<Rightarrow> bool" where
  "valid_pair ss \<longleftrightarrow> ss \<noteq> [] \<and> rev ss = ss \<and>
     (\<forall>s\<in>set ss. s \<le> 18)"

lemma length_emit [simp]: "length (emit c ss) = length ss"
  by (induction ss arbitrary: c) auto

lemma emit_empty [simp]: "emit c ss = [] \<longleftrightarrow> ss = []"
  by (cases ss) auto

lemma emit_bounded:
  "x \<in> set (emit c ss) \<Longrightarrow> x < 10"
  by (induction ss arbitrary: c) auto

lemma digits_bounded:
  "x \<in> set (digits ss) \<Longrightarrow> x < 10"
  by (auto simp: digits_def dest: emit_bounded)

lemma step_symmetric: "rev (step ss) = step ss"
proof -
  let ?d = "digits ss"
  let ?sum = "\<lambda>(a,b). a+b"
  have "rev (step ss) = map ?sum (zip (rev ?d) ?d)"
    by (simp add: step_def rev_map zip_rev[symmetric])
  also have "... = map ?sum (zip ?d (rev ?d))"
    by (subst zip_commute) (simp add: comp_def case_prod_unfold add.commute)
  finally show ?thesis by (simp add: step_def)
qed

lemma step_bounded:
  assumes "x \<in> set (step ss)"
  shows "x \<le> 18"
proof -
  obtain a b where pair: "(a,b) \<in> set (zip (digits ss) (rev (digits ss)))"
      and x: "x = a+b"
    using assms by (auto simp: step_def)
  have "a < 10" using pair by (meson digits_bounded set_zip_leftD)
  moreover have "b < 10"
    using set_zip_rightD[OF pair] digits_bounded by simp
  ultimately show ?thesis using x by arith
qed

lemma length_digits_exact:
  "length (digits ss) =
    length ss + (if carry_out False ss then 1 else 0)"
  by (simp add: digits_def)

lemma length_step_exact [simp]:
  "length (step ss) = length (digits ss)"
  by (simp add: step_def)

lemma run_commutes_with_step:
  "run step count (step source) = step (run step count source)"
  by (induction count arbitrary: source) simp_all

lemma reverse_add_step_width_bounds:
  "length ss \<le> length (step ss) \<and>
   length (step ss) \<le> length ss + 1"
  by (simp add: length_digits_exact; arith)

theorem reverse_add_run_width_bounds:
  "length ss \<le> length (run step n ss) \<and>
   length (run step n ss) \<le> length ss + n"
proof (induction n arbitrary: ss)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have step_bounds: "length ss \<le> length (step ss) \<and>
      length (step ss) \<le> length ss + 1"
    by (rule reverse_add_step_width_bounds)
  have later_bounds:
    "length (step ss) \<le> length (run step n (step ss)) \<and>
     length (run step n (step ss)) \<le> length (step ss) + n"
    by (rule Suc.IH)
  show ?case
    using step_bounds later_bounds
    by (simp; arith)
qed

theorem reverse_add_run_output_width_bounds:
  "length (digits ss) \<le> length (digits (run step n ss)) \<and>
   length (digits (run step n ss)) \<le> length (digits ss) + n"
proof -
  have output_bounds:
    "length (step ss) \<le> length (step (run step n ss)) \<and>
     length (step (run step n ss)) \<le> length (step ss) + n"
    using reverse_add_run_width_bounds[of "step ss" n]
    by (simp add: run_commutes_with_step)
  show ?thesis using output_bounds by simp
qed

lemma step_nonempty:
  "ss \<noteq> [] \<Longrightarrow> step ss \<noteq> []"
  by (auto simp: step_def digits_def zip_eq_Nil_iff)

theorem valid_pair_successor:
  assumes "valid_pair ss"
  shows "valid_pair (step ss)"
proof -
  have "step ss \<noteq> []" using assms step_nonempty unfolding valid_pair_def by blast
  moreover have "rev (step ss) = step ss" by (rule step_symmetric)
  moreover have "\<forall>x\<in>set (step ss). x \<le> 18" using step_bounded by blast
  ultimately show ?thesis by (simp add: valid_pair_def)
qed

lemma valid_pair_run:
  assumes "valid_pair ss"
  shows "valid_pair (run step n ss)"
  using assms
  by (induction n arbitrary: ss) (auto intro: valid_pair_successor)

lemma initial_196_valid: "valid_pair [7,18,7]"
  by (simp add: valid_pair_def)

lemma initial_196_successor: "step [7,18,7] = [15,16,15]"
  by (simp add: step_def digits_def carry_out_def domain_def)

theorem all_196_pair_fields_valid: "valid_pair (run step n [7,18,7])"
proof -
  have "valid_pair (run step n ss)" if "valid_pair ss" for ss
    using that by (induction n arbitrary: ss) (auto intro: valid_pair_successor)
  then show ?thesis using initial_196_valid by blast
qed

text \<open>This invariant proves exact pair-field closure. It retains every
pair value and therefore does not certify the desired information-losing
contextual quotient.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms valid_pair_successor initial_196_valid initial_196_successor
      valid_pair_run reverse_add_step_width_bounds
      reverse_add_run_width_bounds reverse_add_run_output_width_bounds
      all_196_pair_fields_valid}) then ()
    else error "Pair invariant depends on an oracle";
\<close>

end
