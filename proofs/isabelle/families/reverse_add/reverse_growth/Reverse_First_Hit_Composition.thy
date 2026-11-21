theory Reverse_First_Hit_Composition
  imports "Reverse_Residuals.Reverse_Invariant"
begin

lemma reverse_palindrome_equal_digit_carry_seam:
  fixes left_in left_out right_in right_out :: nat
  assumes "left_in < 2" "left_out < 2" "right_in < 2" "right_out < 2"
    and "int left_in - 10 * int left_out = int right_in - 10 * int right_out"
  shows "left_in = right_in \<and> left_out = right_out"
proof -
  have bounds: "int left_in \<le> 1" "int right_in \<le> 1"
    using assms(1,3) by simp_all
  have nonnegative: "0 \<le> int left_in" "0 \<le> int right_in" by simp_all
  have outgoing: "int left_out = int right_out"
    using bounds nonnegative assms(5) by linarith
  have incoming: "int left_in = int right_in"
    using outgoing assms(5) by linarith
  show ?thesis using incoming outgoing by simp
qed

lemma reverse_decimal_no_carry_emission:
  assumes "\<forall>d \<in> set coefficients. d < 10"
  shows "emit False coefficients = coefficients"
  using assms
  by (induction coefficients) (auto simp: domain_def)

lemma reverse_decimal_no_carry_final:
  assumes "\<forall>d \<in> set coefficients. d < 10"
  shows "\<not> carry_out False coefficients"
  using assms
  by (induction coefficients rule: rev_induct)
     (auto simp: carry_out_append carry_out_def domain_def)

theorem reverse_decimal_palindrome_preimage_no_growth:
  assumes "rev coefficients = coefficients"
    and "\<forall>d \<in> set coefficients. d < 10"
  shows "rev (digits coefficients) = digits coefficients"
proof -
  have "digits coefficients = coefficients"
    using reverse_decimal_no_carry_emission[OF assms(2)]
      reverse_decimal_no_carry_final[OF assms(2)]
    by (simp add: digits_def)
  with assms(1) show ?thesis by simp
qed

definition reverse_q19_coefficients :: "nat list \<Rightarrow> nat option \<Rightarrow> nat list" where
  "reverse_q19_coefficients pairs center =
    pairs @ (case center of None \<Rightarrow> [] | Some d \<Rightarrow> [2*d]) @ rev pairs"

theorem reverse_q19_no_growth_palindrome:
  assumes "\<forall>p \<in> set pairs. p < 10"
    and "case center of None \<Rightarrow> True | Some d \<Rightarrow> d < 5"
  shows "rev (digits (reverse_q19_coefficients pairs center)) =
    digits (reverse_q19_coefficients pairs center)"
proof (rule reverse_decimal_palindrome_preimage_no_growth)
  show "rev (reverse_q19_coefficients pairs center) =
    reverse_q19_coefficients pairs center"
    by (cases center) (simp_all add: reverse_q19_coefficients_def)
  show "\<forall>d \<in> set (reverse_q19_coefficients pairs center). d < 10"
    using assms by (cases center) (auto simp: reverse_q19_coefficients_def)
qed

definition reverse_growth_bit :: "bool \<Rightarrow> nat" where
  "reverse_growth_bit b = (if b then 1 else 0)"

lemma reverse_growth_bit_emission:
  "emit carry (map (\<lambda>b. if b then 11 else 0) bits) =
    map (\<lambda>(a,b). reverse_growth_bit a + reverse_growth_bit b)
      (zip (carry # bits) bits)"
  by (induction bits arbitrary: carry)
     (auto simp: reverse_growth_bit_def domain_def split: bool.splits)

lemma reverse_growth_bit_final:
  "carry_out carry (map (\<lambda>b. if b then 11 else 0) bits) =
    (if bits = [] then carry else last bits)"
  by (induction bits arbitrary: carry rule: rev_induct)
     (auto simp: carry_out_append carry_out_def domain_def split: bool.splits)

lemma reverse_emit_append_zero:
  "emit carry (coefficients @ [0]) =
    emit carry coefficients @ [reverse_growth_bit (carry_out carry coefficients)]"
  by (induction coefficients arbitrary: carry)
     (auto simp: carry_out_def reverse_growth_bit_def domain_def)

lemma reverse_zip_discard_extra:
  assumes "length xs = length ys"
  shows "zip (xs @ [x]) ys = zip xs ys"
  using assms by (induction xs arbitrary: ys) (auto, case_tac ys, auto)

theorem reverse_decimal_palindrome_preimage_growth:
  assumes symmetry: "rev bits = bits" and nonempty: "bits \<noteq> []"
    and outer: "last bits"
  defines "coefficients \<equiv> map (\<lambda>b. if b then 11 else 0) bits"
  shows "rev (digits coefficients) = digits coefficients"
proof -
  have growth: "carry_out False coefficients"
    using reverse_growth_bit_final[of False bits] nonempty outer
    by (simp add: coefficients_def)
  have shifted: "digits coefficients =
      map (\<lambda>(a,b). reverse_growth_bit a + reverse_growth_bit b)
        (zip (False # bits) (bits @ [False]))"
    using reverse_growth_bit_emission[of False "bits @ [False]"]
      reverse_emit_append_zero[of False coefficients] growth
      reverse_zip_discard_extra[of "False # bits" "bits @ [False]" False]
    by (simp add: coefficients_def digits_def reverse_growth_bit_def)
  let ?f = "\<lambda>(a,b). reverse_growth_bit a + reverse_growth_bit b"
  have "rev (map ?f (zip (False # bits) (bits @ [False]))) =
      map ?f (zip (bits @ [False]) (False # bits))"
    using symmetry by (simp add: rev_map zip_rev[symmetric])
  also have "... = map ?f (zip (False # bits) (bits @ [False]))"
    by (subst zip_commute) (simp add: comp_def case_prod_unfold add.commute)
  finally show ?thesis using shifted by simp
qed

text \<open>First-hit composition for chronological, completely observed spans.\<close>

fun first_true :: "bool list \<Rightarrow> nat option" where
  "first_true [] = None"
| "first_true (x # xs) = (if x then Some 0 else map_option Suc (first_true xs))"

lemma first_true_append:
  "first_true (xs @ ys) =
    (case first_true xs of None \<Rightarrow> map_option ((+) (length xs)) (first_true ys)
     | Some n \<Rightarrow> Some n)"
proof (induction xs)
  case Nil
  then show ?case by (cases "first_true ys") simp_all
next
  case (Cons a xs)
  then show ?case
    by (cases a; cases "first_true xs"; cases "first_true ys") auto
qed

lemma first_true_none_iff:
  "first_true xs = None \<longleftrightarrow> (\<forall>x \<in> set xs. \<not> x)"
  by (induction xs) (auto split: option.splits)

lemma first_true_some:
  assumes "first_true xs = Some n"
  shows "n < length xs \<and> xs ! n \<and> (\<forall>i<n. \<not> xs ! i)"
  using assms
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases a)
    case True
    with Cons.prems show ?thesis by simp
  next
    case False
    obtain k where hit: "first_true xs = Some k" and index: "n = Suc k"
      using False Cons.prems by (cases "first_true xs") auto
    have known: "k < length xs \<and> xs ! k \<and> (\<forall>i<k. \<not> xs ! i)"
      using Cons.IH[OF hit] .
    show ?thesis using known False index
      by (auto simp: less_Suc_eq_0_disj)
  qed
qed

definition first_arrival :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat option" where
  "first_arrival transition event source horizon =
    map_option Suc (first_true (map (\<lambda>n. event ((transition ^^ Suc n) source)) [0..<horizon]))"

lemma first_arrival_exact:
  assumes "first_arrival transition event source horizon = Some n"
  shows "0 < n \<and> n \<le> horizon \<and> event ((transition ^^ n) source) \<and>
    (\<forall>i. 0 < i \<and> i < n \<longrightarrow> \<not> event ((transition ^^ i) source))"
proof -
  obtain k where k: "n = Suc k" and
    hit: "first_true (map (\<lambda>j. event ((transition ^^ Suc j) source)) [0..<horizon]) = Some k"
    using assms unfolding first_arrival_def by (auto split: option.splits)
  from first_true_some[OF hit] k show ?thesis
    by (auto simp: nth_map nth_upt less_Suc_eq_0_disj)
qed

definition reverse_q19_first_arrival :: "nat list \<Rightarrow> nat \<Rightarrow> nat option" where
  "reverse_q19_first_arrival source horizon =
    map_option Suc (first_true (map (\<lambda>n.
      rev (digits ((step ^^ n) source)) = digits ((step ^^ n) source)) [0..<horizon]))"

theorem reverse_q19_first_arrival_exact:
  assumes "reverse_q19_first_arrival source horizon = Some n"
  shows "0 < n \<and> n \<le> horizon \<and>
    rev (digits ((step ^^ (n - 1)) source)) = digits ((step ^^ (n - 1)) source) \<and>
    (\<forall>i. 0 < i \<and> i < n \<longrightarrow>
      rev (digits ((step ^^ (i - 1)) source)) \<noteq> digits ((step ^^ (i - 1)) source))"
proof -
  obtain k where k: "n = Suc k" and
    hit: "first_true (map (\<lambda>j.
      rev (digits ((step ^^ j) source)) = digits ((step ^^ j) source)) [0..<horizon]) = Some k"
    using assms unfolding reverse_q19_first_arrival_def by (auto split: option.splits)
  from first_true_some[OF hit] k show ?thesis
    by (auto simp: nth_map nth_upt less_Suc_eq_0_disj)
qed

end
