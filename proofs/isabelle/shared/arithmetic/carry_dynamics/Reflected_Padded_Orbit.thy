theory Reflected_Padded_Orbit
  imports Reflected_Padded_Physical_Trim
begin

text \<open>The low-zero quotient acts on padded words. It does not discard a
physical endpoint zero: normalization is applied before final multiplication.\<close>

definition reflected_trim_low :: "nat list \<Rightarrow> nat list" where
  "reflected_trim_low word = dropWhile ((=) 0) word"

lemma reflected_digit_pass_decimal:
  "list_all (\<lambda>digit. digit < 10)
      (fst (decimal_block_run multiplier source incoming))"
  by (induction source arbitrary: incoming)
     (auto simp: Let_def split: prod.splits)

lemma reflected_padded_multiply_decimal:
  assumes "multiplier = 2 \<or> multiplier = 5"
    and "list_all (\<lambda>digit. digit < 10) source"
  shows "list_all (\<lambda>digit. digit < 10)
      (reflected_padded_multiply multiplier source)"
proof -
  have carry: "snd (decimal_block_run multiplier source 0) < multiplier"
    by (rule reflected_digit_pass_carry_bound[OF assms]) (use assms in auto)
  have "snd (decimal_block_run multiplier source 0) < 10"
    using carry assms by arith
  then show ?thesis
    using reflected_digit_pass_decimal[of multiplier source 0]
    by (simp add: reflected_padded_multiply_def Let_def)
qed

lemma reflected_E_low_normalization:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "list_all (\<lambda>digit. digit < 10) source"
  shows "reflected_trim_low (reflected_padded_E multiplier (reflected_trim_low source)) =
    reflected_trim_low (reflected_padded_E multiplier source)"
  using digits
proof (induction source)
  case Nil
  then show ?case by (simp add: reflected_trim_low_def)
next
  case (Cons digit rest)
  have rest_digits: "list_all (\<lambda>digit. digit < 10) rest"
    using Cons.prems by simp
  show ?case
  proof (cases "digit = 0")
    case True
    have shift: "reflected_padded_E multiplier (0 # rest) =
        0 # reflected_padded_E multiplier rest"
      by (rule reflected_padded_E_zero_transport[OF multiplier rest_digits])
    show ?thesis using Cons.IH[OF rest_digits] True shift
      by (simp add: reflected_trim_low_def)
  next
    case False
    then show ?thesis by (simp add: reflected_trim_low_def)
  qed
qed

theorem reflected_H_low_normalization:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "list_all (\<lambda>digit. digit < 10) source"
  shows "reflected_trim_low (reflected_padded_H multiplier (reflected_trim_low source)) =
    reflected_trim_low (reflected_padded_H multiplier source)"
proof -
  have trimmed_digits: "list_all (\<lambda>digit. digit < 10) (reflected_trim_low source)"
    using digits by (induction source) (auto simp: reflected_trim_low_def)
  let ?left = "reflected_padded_multiply multiplier (reflected_trim_low source)"
  let ?right = "reflected_padded_multiply multiplier source"
  have left_digits: "list_all (\<lambda>digit. digit < 10) ?left"
    by (rule reflected_padded_multiply_decimal[OF multiplier trimmed_digits])
  have right_digits: "list_all (\<lambda>digit. digit < 10) ?right"
    by (rule reflected_padded_multiply_decimal[OF multiplier digits])
  have same: "reflected_trim_low ?left = reflected_trim_low ?right"
    using reflected_padded_multiply_low_normalization[of multiplier source]
    by (simp add: reflected_trim_low_def)
  show ?thesis
    unfolding reflected_padded_H_def
    using reflected_E_low_normalization[OF multiplier left_digits]
      reflected_E_low_normalization[OF multiplier right_digits] same by simp
qed

lemma reflected_padded_E_decimal:
  assumes "multiplier = 2 \<or> multiplier = 5"
    and "list_all (\<lambda>digit. digit < 10) source"
  shows "list_all (\<lambda>digit. digit < 10) (reflected_padded_E multiplier source)"
  using reflected_padded_multiply_decimal[OF assms(1), of "rev source"] assms(2)
  by (simp add: reflected_padded_E_def)

lemma reflected_padded_H_decimal:
  assumes "multiplier = 2 \<or> multiplier = 5"
    and "list_all (\<lambda>digit. digit < 10) source"
  shows "list_all (\<lambda>digit. digit < 10) (reflected_padded_H multiplier source)"
  unfolding reflected_padded_H_def
  by (rule reflected_padded_E_decimal[OF assms(1)])
     (rule reflected_padded_multiply_decimal[OF assms])

fun reflected_padded_H_iter :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reflected_padded_H_iter multiplier 0 source = source"
| "reflected_padded_H_iter multiplier (Suc steps) source =
    reflected_padded_H multiplier (reflected_padded_H_iter multiplier steps source)"

lemma reflected_padded_H_iter_decimal:
  assumes "multiplier = 2 \<or> multiplier = 5"
    and "list_all (\<lambda>digit. digit < 10) source"
  shows "list_all (\<lambda>digit. digit < 10)
    (reflected_padded_H_iter multiplier steps source)"
  using assms(2)
  by (induction steps) (simp_all add: reflected_padded_H_decimal[OF assms(1)])

theorem reflected_padded_H_iter_low_normalization:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "list_all (\<lambda>digit. digit < 10) source"
  shows "reflected_trim_low
      (reflected_padded_H_iter multiplier steps (reflected_trim_low source)) =
    reflected_trim_low (reflected_padded_H_iter multiplier steps source)"
proof -
  have trimmed_digits: "list_all (\<lambda>digit. digit < 10) (reflected_trim_low source)"
    using digits by (induction source) (auto simp: reflected_trim_low_def)
  show ?thesis
  proof (induction steps)
    case 0
    then show ?case by (simp add: reflected_trim_low_def)
  next
    case (Suc steps)
    let ?left = "reflected_padded_H_iter multiplier steps (reflected_trim_low source)"
    let ?right = "reflected_padded_H_iter multiplier steps source"
    have left_digits: "list_all (\<lambda>digit. digit < 10) ?left"
      by (rule reflected_padded_H_iter_decimal[OF multiplier trimmed_digits])
    have right_digits: "list_all (\<lambda>digit. digit < 10) ?right"
      by (rule reflected_padded_H_iter_decimal[OF multiplier digits])
    have left_norm: "reflected_trim_low (reflected_padded_H multiplier ?left) =
        reflected_trim_low (reflected_padded_H multiplier (reflected_trim_low ?left))"
      using reflected_H_low_normalization[OF multiplier left_digits] by simp
    have right_norm: "reflected_trim_low (reflected_padded_H multiplier ?right) =
        reflected_trim_low (reflected_padded_H multiplier (reflected_trim_low ?right))"
      using reflected_H_low_normalization[OF multiplier right_digits] by simp
    show ?case using Suc.IH left_norm right_norm by simp
  qed
qed

end
