theory Uniform_Pair_Field_Grammar
  imports "Reverse_Residuals.Reverse_Uniform_Runs"
begin

text \<open>
  Width-parametric identities for uniform decimal pair-field projections.
  The historical theory name does not make these emitted shapes the state of
  a source-cylinder grammar. This theory does not provide a normal form for
  arbitrary 196 temporal transforms or authorize production publication.
\<close>

definition uniform_pair_field :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "uniform_pair_field s m = replicate m s"

definition uniform_no_growth_admissible :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "uniform_no_growth_admissible s k = (\<forall>j<k. 2^j * s \<le> 9)"

lemma emit_uniform_equal:
  "emit False (replicate n 9) = replicate n 9"
  by (induction n) (simp_all add: domain_def)

lemma carry_uniform_equal:
  "carry_out False (replicate n 9) = False"
  by (induction n) (simp_all add: carry_out_def domain_def)

lemma uniform_at_most_nine_digits:
  assumes "s \<le> 9"
  shows "digits (replicate n s) = replicate n s"
proof (cases "s < 9")
  case True
  then show ?thesis
    by (simp add: digits_def emit_uniform_below carry_uniform_below)
next
  case False
  have "s = 9" using assms False by arith
  then show ?thesis
    by (simp add: digits_def emit_uniform_equal carry_uniform_equal)
qed

theorem uniform_at_most_nine_successor:
  assumes "s \<le> 9"
  shows "step (replicate n s) = replicate n (2*s)"
  using assms
proof (cases "s < 9")
  case True
  then show ?thesis using uniform_below_successor by simp
next
  case False
  have "s = 9" using assms False by arith
  then show ?thesis
    by (simp add: step_def uniform_at_most_nine_digits pair_uniform)
qed

lemma emit_uniform_high_true:
  assumes "10 \<le> s" "s \<le> 18"
  shows "emit True (replicate n s) = replicate n (s-9)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have digit_mod: "(s + 1) mod 10 = s - 9"
  proof -
    have split: "s + 1 = 10 + (s - 9)" using assms by arith
    have small: "s - 9 < 10" using assms by arith
    have "(s + 1) mod 10 = (10 + (s - 9)) mod 10"
      using split by (rule arg_cong)
    also have "... = s - 9" using small by simp
    finally show ?thesis .
  qed
  show ?case
    using Suc.IH digit_mod assms
    by (simp add: domain_def)
qed

lemma emit_uniform_high_false:
  assumes "10 \<le> s" "s \<le> 18"
  shows "emit False (replicate (Suc n) s) =
      (s-10) # replicate n (s-9)"
proof -
  have digit_mod: "s mod 10 = s - 10"
  proof -
    have split: "s = 10 + (s - 10)" using assms by arith
    have small: "s - 10 < 10" using assms by arith
    have "s mod 10 = (10 + (s - 10)) mod 10"
      using split by (rule arg_cong)
    also have "... = s - 10" using small by simp
    finally show ?thesis .
  qed
  show ?thesis
    using emit_uniform_high_true[OF assms, of n] digit_mod assms
    by (simp add: domain_def)
qed

lemma carry_uniform_high_true:
  assumes "10 \<le> s"
  shows "carry_out True (replicate n s) = True"
  using assms by (induction n) (simp_all add: carry_out_def domain_def)

lemma carry_uniform_high:
  assumes "10 \<le> s" "s \<le> 18"
  shows "carry_out False (replicate (Suc n) s) = True"
proof -
  have first: "carry_out False (replicate (Suc n) s) =
      carry_out True (replicate n s)"
    using assms by (simp add: carry_out_def domain_def)
  show ?thesis using first carry_uniform_high_true[OF assms(1), of n] by simp
qed

lemma uniform_high_digits:
  assumes "10 \<le> s" "s \<le> 18"
  shows "digits (replicate (Suc n) s) =
      (s-10) # replicate n (s-9) @ [1]"
  using emit_uniform_high_false[OF assms, of n]
    carry_uniform_high[OF assms, of n]
  by (simp add: digits_def)

lemma uniform_ends_pair:
  fixes a b c :: nat
  shows
  "map (\<lambda>(a,b). a+b)
      (zip (a # replicate n b @ [c]) (rev (a # replicate n b @ [c]))) =
    (a+c) # replicate n (2*b) @ [c+a]"
proof -
  have reverse:
    "rev (a # replicate n b @ [c]) = c # replicate n b @ [a]"
    by simp
  have tail:
    "map (\<lambda>(x,y). x+y)
       (zip (replicate n b @ [c]) (replicate n b @ [a])) =
       replicate n (2*b) @ [c+a]"
    using sum_uniform_tail[of n b c a] .
  show ?thesis
    using reverse tail by (simp add: add.commute)
qed

theorem uniform_high_successor:
  assumes "10 \<le> s" "s \<le> 18"
  shows "step (replicate (Suc n) s) =
      (s-9) # replicate n (2*s-18) @ [s-9]"
proof -
  have digits:
    "digits (replicate (Suc n) s) =
      (s-10) # replicate n (s-9) @ [1]"
    using uniform_high_digits[OF assms] .
  have pairs:
    "map (\<lambda>(a,b). a+b)
      (zip ((s-10) # replicate n (s-9) @ [1])
        (rev ((s-10) # replicate n (s-9) @ [1]))) =
      (s-9) # replicate n (2*s-18) @ [s-9]"
    proof -
    have left_edge: "s - 10 + 1 = s - 9" using assms by arith
    have right_edge: "1 + (s - 10) = s - 9" using assms by arith
    have middle: "2 * (s - 9) = 2*s - 18" using assms by arith
    show ?thesis
      using uniform_ends_pair[where a="s-10" and b="s-9" and c=1 and n=n]
        left_edge right_edge middle by simp
  qed
  show ?thesis
    unfolding step_def
    using digits pairs by simp
qed

lemma uniform_no_growth_endpoint_bound:
  assumes "uniform_no_growth_admissible s (Suc k)"
  shows "2^k * s \<le> 9"
  using assms unfolding uniform_no_growth_admissible_def by blast

lemma uniform_no_growth_endpoint_iff:
  "uniform_no_growth_admissible s (Suc k) \<longleftrightarrow> 2^k * s \<le> 9"
proof
  show "uniform_no_growth_admissible s (Suc k) \<Longrightarrow> 2^k * s \<le> 9"
    by (rule uniform_no_growth_endpoint_bound)
next
  assume endpoint: "2^k * s \<le> 9"
  show "uniform_no_growth_admissible s (Suc k)"
    unfolding uniform_no_growth_admissible_def
  proof (intro allI impI)
    fix j assume before: "j < Suc k"
    have order: "j \<le> k" using before by simp
    have powers: "(2::nat)^j \<le> 2^k"
      by (rule power_increasing[OF order]) simp
    have "2^j * s \<le> 2^k * s" using powers by (rule mult_le_mono1)
    then show "2^j * s \<le> 9" using endpoint by arith
  qed
qed

lemma uniform_no_growth_admissible_tail:
  assumes "uniform_no_growth_admissible s (Suc k)"
  shows "uniform_no_growth_admissible (2*s) k"
  unfolding uniform_no_growth_admissible_def
proof (intro allI impI)
  fix j assume bound: "j < k"
  have source_index: "Suc j < Suc k" using bound by simp
  have source_bound: "2^Suc j * s \<le> 9"
    using assms source_index unfolding uniform_no_growth_admissible_def
    by blast
  show "2^j * (2*s) \<le> 9"
    using source_bound by (simp add: power_Suc algebra_simps)
qed

theorem uniform_no_growth_horizon:
  assumes "uniform_no_growth_admissible s k"
  shows "run step k (replicate m s) = replicate m (2^k*s)"
using assms
proof (induction k arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have h0: "2^0 * s \<le> 9"
    using Suc.prems unfolding uniform_no_growth_admissible_def by blast
  have source_bound: "s \<le> 9" using h0 by simp
  have first: "step (replicate m s) = replicate m (2*s)"
    using uniform_at_most_nine_successor[OF source_bound] .
  have tail_admitted:
    "uniform_no_growth_admissible (2*s) k"
    using uniform_no_growth_admissible_tail[OF Suc.prems] .
  have tail:
    "run step k (replicate m (2*s)) = replicate m (2^k*(2*s))"
    using Suc.IH[OF tail_admitted] .
  show ?case
    using first tail by (simp add: run.simps power_Suc algebra_simps)
qed

text \<open>
  The admissibility predicate is deliberately a source rule: it certifies the
  whole repeated no-growth prefix, while the successor theorem above remains
  the actual primitive decimal step.
\<close>

ML \<open>
  val checked = @{thms uniform_at_most_nine_successor uniform_high_successor
    uniform_no_growth_endpoint_iff uniform_no_growth_horizon};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Uniform pair-field grammar depends on an oracle";
\<close>

end
