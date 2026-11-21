theory Reverse_Palindrome_Preimage_Seams
  imports Reverse_First_Hit_Composition "Reverse_Residuals.Reverse_Growth_Coboundary"
begin

text \<open>Local necessity equations for a palindrome at a decimal carry seam.
The incoming and outgoing carries are physical carries, not independent
source identities.\<close>

theorem reverse_palindrome_no_growth_mirrored_carries:
  fixes S C :: "nat \<Rightarrow> nat"
  assumes "S i = S j"
    and "C i < 2" "C (Suc i) < 2" "C j < 2" "C (Suc j) < 2"
    and "normalized_growth_digit S C i = normalized_growth_digit S C j"
  shows "C i = C j \<and> C (Suc i) = C (Suc j)"
proof -
  have equation: "int (C i) - 10 * int (C (Suc i)) =
      int (C j) - 10 * int (C (Suc j))"
    using assms(1,6) by (simp add: normalized_growth_digit_def; linarith)
  show ?thesis
    by (rule reverse_palindrome_equal_digit_carry_seam[OF assms(2-5) equation])
qed

theorem reverse_palindrome_no_growth_all_carries_zero:
  fixes S C :: "nat \<Rightarrow> nat"
  assumes start: "C 0 = 0" and finish: "C n = 0"
    and bits: "\<And>i. i \<le> n \<Longrightarrow> C i < 2"
    and symmetry: "\<And>i. i < n \<Longrightarrow> S i = S (n - Suc i)"
    and palindrome: "\<And>i. i < n \<Longrightarrow>
      normalized_growth_digit S C i = normalized_growth_digit S C (n - Suc i)"
  shows "k \<le> n \<Longrightarrow> C k = 0 \<and> C (n - k) = 0"
proof (induction k)
  case 0
  then show ?case using start finish by simp
next
  case (Suc k)
  have klt: "k < n" using Suc.prems by simp
  have previous: "C k = 0 \<and> C (n - k) = 0"
    using Suc.IH Suc.prems by simp
  let ?j = "n - Suc k"
  have jlt: "?j < n" using klt by arith
  have jnext: "Suc ?j = n - k" using klt by arith
  have carries: "C k = C ?j \<and> C (Suc k) = C (Suc ?j)"
    by (rule reverse_palindrome_no_growth_mirrored_carries
        [OF symmetry[OF klt] bits bits bits bits palindrome[OF klt]])
       (use klt jlt in auto)
  show ?case using previous carries jnext by simp
qed

theorem reverse_palindrome_no_growth_pair_bound:
  fixes S C :: "nat \<Rightarrow> nat"
  assumes start: "C 0 = 0" and finish: "C n = 0"
    and bits: "\<And>i. i \<le> n \<Longrightarrow> C i < 2"
    and symmetry: "\<And>i. i < n \<Longrightarrow> S i = S (n - Suc i)"
    and palindrome: "\<And>i. i < n \<Longrightarrow>
      normalized_growth_digit S C i = normalized_growth_digit S C (n - Suc i)"
    and recurrence: "\<And>i. i < n \<Longrightarrow> C (Suc i) = decimal_carry (S i) (C i)"
    and index: "i < n"
  shows "S i < 10"
proof -
  have left: "C i = 0" and right: "C (Suc i) = 0"
    using reverse_palindrome_no_growth_all_carries_zero
      [OF start finish bits symmetry palindrome, of i]
      reverse_palindrome_no_growth_all_carries_zero
      [OF start finish bits symmetry palindrome, of "Suc i"] index by auto
  show ?thesis using recurrence[OF index] left right
    by (auto simp: decimal_carry_def split: if_splits)
qed

theorem reverse_palindrome_growth_digit_equation:
  fixes S C :: "nat \<Rightarrow> nat"
  assumes "normalized_growth_digit S C i = normalized_growth_digit S C j"
    and "S j = 11 * C (Suc j)"
    and "C i = C (Suc j)"
  shows "S i = C j + 10 * C (Suc i)"
  using assms by (simp add: normalized_growth_digit_def; linarith)

lemma reverse_decimal_carry_one_lower_bound:
  assumes "decimal_carry value carry = 1"
  shows "10 \<le> value + carry"
  using assms by (auto simp: decimal_carry_def split: if_splits)

lemma reverse_decimal_carry_zero_upper_bound:
  assumes "decimal_carry value carry = 0"
  shows "value + carry < 10"
  using assms by (auto simp: decimal_carry_def split: if_splits)

theorem reverse_palindrome_growth_forces_equal_carries:
  fixes digit mirrored_out forward_out mirrored_in :: nat
  assumes "mirrored_out < 2" "forward_out < 2" "mirrored_in < 2"
    and "digit = mirrored_out + 10 * forward_out"
    and "mirrored_out = decimal_carry digit mirrored_in"
  shows "mirrored_out = forward_out \<and> digit = 11 * forward_out"
proof (cases "mirrored_out = 0")
  case True
  have upper: "digit + mirrored_in < 10"
    by (rule reverse_decimal_carry_zero_upper_bound) (use assms(5) True in simp)
  have "forward_out = 0" using upper assms(4) True by arith
  with assms(4) True show ?thesis by simp
next
  case False
  have one: "mirrored_out = 1" using assms(1) False by arith
  have lower: "10 \<le> digit + mirrored_in"
    by (rule reverse_decimal_carry_one_lower_bound) (use assms(5) one in simp)
  have "forward_out = 1" using lower assms(2-4) one by arith
  with assms(4) one show ?thesis by simp
qed

theorem reverse_palindrome_growth_outer:
  fixes S C :: "nat \<Rightarrow> nat"
  assumes width: "0 < n" and start: "C 0 = 0" and last: "C n = 1"
    and bits: "\<And>i. i \<le> n \<Longrightarrow> C i < 2"
    and symmetry: "S 0 = S (n - 1)"
    and edge: "normalized_growth_digit S C 0 = 1"
    and recurrence: "\<And>i. i < n \<Longrightarrow> C (Suc i) = decimal_carry (S i) (C i)"
  shows "C 1 = 1 \<and> S 0 = 11"
proof -
  have index: "n - 1 < n" using width by arith
  have mirror: "1 = decimal_carry (S 0) (C (n - 1))"
    using recurrence[OF index] symmetry last width by simp
  have lower: "10 \<le> S 0 + C (n - 1)"
    by (rule reverse_decimal_carry_one_lower_bound[OF mirror[symmetric]])
  have c1: "C 1 < 2" and cn: "C (n - 1) < 2"
    using bits width by auto
  have edge_eq: "int (S 0) - 10 * int (C 1) = 1"
    using edge start by (simp add: normalized_growth_digit_def)
  show ?thesis
  proof (cases "C 1 = 0")
    case True
    have "S 0 = 1" using edge_eq True by linarith
    with lower cn show ?thesis by arith
  next
    case False
    have "C 1 = 1" using c1 False by arith
    moreover have "S 0 = 11" using edge_eq calculation by linarith
    ultimately show ?thesis by simp
  qed
qed

theorem reverse_palindrome_growth_inward:
  fixes S C :: "nat \<Rightarrow> nat"
  assumes width: "0 < n" and first: "C 1 = 1" and last: "C n = 1"
    and outer: "S 0 = 11"
    and bits: "\<And>i. i \<le> n \<Longrightarrow> C i < 2"
    and symmetry: "\<And>i. i < n \<Longrightarrow> S i = S (n - Suc i)"
    and palindrome: "\<And>i. 0 < i \<Longrightarrow> i < n \<Longrightarrow>
      normalized_growth_digit S C i = normalized_growth_digit S C (n - i)"
    and recurrence: "\<And>i. i < n \<Longrightarrow> C (Suc i) = decimal_carry (S i) (C i)"
  shows "1 \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow>
    C k = C (n + 1 - k) \<and> S (k - 1) = 11 * C k"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases "k = 0")
    case True
    then show ?thesis using first last outer by simp
  next
    case False
    have positive: "0 < k" using False by simp
    have klt: "k < n" using Suc.prems by simp
    have prior: "C k = C (n + 1 - k) \<and> S (k - 1) = 11 * C k"
      using Suc.IH positive klt by simp
    let ?j = "n - k"
    have jpos: "0 < ?j" and jlt: "?j < n" using positive klt by arith+
    have mirror: "n - Suc ?j = k - 1" using positive klt by arith
    have reflected_index: "n - Suc k = ?j - 1" using positive klt by arith
    have prev_index: "Suc ?j = n + 1 - k" using positive klt by arith
    have source_j: "S ?j = 11 * C (Suc ?j)"
      using symmetry[OF jlt] prior mirror prev_index by simp
    have carry_j: "C k = C (Suc ?j)" using prior prev_index by simp
    have digit: "S k = C ?j + 10 * C (Suc k)"
      using reverse_palindrome_growth_digit_equation
        [OF palindrome[OF positive klt] source_j carry_j] .
    have previous_j: "?j - 1 < n" using jpos jlt by arith
    have mirrored_source: "S (?j - 1) = S k"
      using symmetry[OF klt, symmetric] by (simp only: reflected_index)
    have mirrored_successor: "Suc (?j - 1) = ?j" using jpos by arith
    have mirrored_carry: "C ?j = decimal_carry (S k) (C (?j - 1))"
      using recurrence[OF previous_j] by (simp only: mirrored_source mirrored_successor)
    have forced: "C ?j = C (Suc k) \<and> S k = 11 * C (Suc k)"
      by (rule reverse_palindrome_growth_forces_equal_carries
          [OF bits bits bits digit mirrored_carry])
         (use klt jlt previous_j in auto)
    show ?thesis using forced by simp
  qed
qed

end
