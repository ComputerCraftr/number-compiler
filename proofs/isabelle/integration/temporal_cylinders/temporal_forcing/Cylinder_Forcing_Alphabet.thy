theory Cylinder_Forcing_Alphabet
  imports "Reverse_Residuals.Reverse_Residuals"
begin

text \<open>
  Finite arithmetic for the decimal forcing alphabet.  These are local carry
  identities only.  They do not establish source admission, a temporal normal
  form, or a complete refinement for the 196 trajectory.
\<close>

definition forcing_carry_step :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "forcing_carry_step source carry =
    (if 10 \<le> source + carry then 1 else 0)"

definition forcing_beta :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "forcing_beta source left right =
    int left + int right -
      10 * (int (forcing_carry_step source left) +
        int (forcing_carry_step source right))"

definition forcing_beta_alphabet :: "int set" where
  "forcing_beta_alphabet = {-20, -19, -18, -9, 0, 1, 2}"

lemma forcing_bit_cases:
  fixes bit :: nat
  assumes "bit \<le> 1"
  shows "bit = 0 \<or> bit = 1"
  using assms by linarith

theorem forcing_step_matches_shared:
  fixes source incoming :: nat
  assumes "incoming \<le> 1"
  shows "forcing_carry_step source incoming =
    (if carry_apply (domain source) (incoming = 1) then 1 else 0)"
proof -
  consider (zero) "incoming = 0" | (one) "incoming = 1"
    using forcing_bit_cases[OF assms] by blast
  then show ?thesis
    by cases (simp_all add: forcing_carry_step_def carry_apply_decimal_threshold)
qed

theorem forcing_no_growth_beta_in_alphabet:
  fixes source left right :: nat
  assumes source: "source \<le> 18"
      and left: "left \<le> 1"
      and right: "right \<le> 1"
  shows "forcing_beta source left right \<in> forcing_beta_alphabet"
proof -
  consider (left_zero) "left = 0" | (left_one) "left = 1"
    using forcing_bit_cases[OF left] by blast
  then show ?thesis
  proof cases
    case left_zero
    consider (right_zero) "right = 0" | (right_one) "right = 1"
      using forcing_bit_cases[OF right] by blast
    then show ?thesis
      using source left_zero
      by cases (auto simp: forcing_beta_def forcing_carry_step_def
          forcing_beta_alphabet_def split: if_splits)
  next
    case left_one
    consider (right_zero) "right = 0" | (right_one) "right = 1"
      using forcing_bit_cases[OF right] by blast
    then show ?thesis
      using source left_one
      by cases (auto simp: forcing_beta_def forcing_carry_step_def
          forcing_beta_alphabet_def split: if_splits)
  qed
qed

lemma forcing_beta_alphabet_witnesses:
  "forcing_beta 10 0 0 = -20 \<and>
   forcing_beta 10 0 1 = -19 \<and>
   forcing_beta 10 1 1 = -18 \<and>
   forcing_beta 9 0 1 = -9 \<and>
   forcing_beta 0 0 0 = 0 \<and>
   forcing_beta 0 0 1 = 1 \<and>
   forcing_beta 0 1 1 = 2"
  by (simp add: forcing_beta_def forcing_carry_step_def)

definition forcing_no_growth_values :: "int set" where
  "forcing_no_growth_values =
    {forcing_beta source left right |source left right.
      source \<le> 18 \<and> left \<le> 1 \<and> right \<le> 1}"

lemma forcing_no_growth_valueI:
  fixes source left right :: nat
  assumes "source \<le> 18" "left \<le> 1" "right \<le> 1"
  shows "forcing_beta source left right \<in> forcing_no_growth_values"
  using assms by (auto simp: forcing_no_growth_values_def)

theorem forcing_no_growth_values_exact:
  "forcing_no_growth_values = forcing_beta_alphabet"
proof
  show "forcing_no_growth_values \<subseteq> forcing_beta_alphabet"
    using forcing_no_growth_beta_in_alphabet
    by (auto simp: forcing_no_growth_values_def)
  show "forcing_beta_alphabet \<subseteq> forcing_no_growth_values"
  proof -
    have minus_twenty: "(-20::int) \<in> forcing_no_growth_values"
      using forcing_no_growth_valueI[of 10 0 0]
        forcing_beta_alphabet_witnesses by simp
    have minus_nineteen: "(-19::int) \<in> forcing_no_growth_values"
      using forcing_no_growth_valueI[of 10 0 1]
        forcing_beta_alphabet_witnesses by simp
    have minus_eighteen: "(-18::int) \<in> forcing_no_growth_values"
      using forcing_no_growth_valueI[of 10 1 1]
        forcing_beta_alphabet_witnesses by simp
    have minus_nine: "(-9::int) \<in> forcing_no_growth_values"
      using forcing_no_growth_valueI[of 9 0 1]
        forcing_beta_alphabet_witnesses by simp
    have zero: "(0::int) \<in> forcing_no_growth_values"
      using forcing_no_growth_valueI[of 0 0 0]
        forcing_beta_alphabet_witnesses by simp
    have one: "(1::int) \<in> forcing_no_growth_values"
      using forcing_no_growth_valueI[of 0 0 1]
        forcing_beta_alphabet_witnesses by simp
    have two: "(2::int) \<in> forcing_no_growth_values"
      using forcing_no_growth_valueI[of 0 1 1]
        forcing_beta_alphabet_witnesses by simp
    show ?thesis
      using minus_twenty minus_nineteen minus_eighteen minus_nine zero one two
      by (simp add: forcing_beta_alphabet_def)
  qed
qed

corollary forcing_no_growth_excludes_minus_ten_and_minus_eight:
  assumes "source \<le> 18" "left \<le> 1" "right \<le> 1"
  shows "forcing_beta source left right \<noteq> -10 \<and>
    forcing_beta source left right \<noteq> -8"
  using forcing_no_growth_beta_in_alphabet[OF assms]
  by (auto simp: forcing_beta_alphabet_def)

text \<open>
  The interior growth wiring has six carry ports.  The two outer bits e,f and
  the two shared source coefficients x,y determine all four internal carries;
  they are not independent Boolean choices.
\<close>

definition forcing_growth_beta ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "forcing_growth_beta x y e f =
    (let a = forcing_carry_step x e;
         b = forcing_carry_step y f;
         c = forcing_carry_step y a;
         d = forcing_carry_step x b
     in int a + int b - 10 * (int c + int d))"

theorem forcing_growth_beta_in_alphabet:
  fixes x y e f :: nat
  assumes x: "x \<le> 18" and y: "y \<le> 18"
      and e: "e \<le> 1" and f: "f \<le> 1"
  shows "forcing_growth_beta x y e f \<in> forcing_beta_alphabet"
proof -
  consider (e_zero) "e = 0" | (e_one) "e = 1"
    using forcing_bit_cases[OF e] by blast
  then show ?thesis
  proof cases
    case e_zero
    consider (f_zero) "f = 0" | (f_one) "f = 1"
      using forcing_bit_cases[OF f] by blast
    then show ?thesis
      using x y e_zero
      by cases (auto simp: forcing_growth_beta_def forcing_carry_step_def
          forcing_beta_alphabet_def Let_def split: if_splits)
  next
    case e_one
    consider (f_zero) "f = 0" | (f_one) "f = 1"
      using forcing_bit_cases[OF f] by blast
    then show ?thesis
      using x y e_one
      by cases (auto simp: forcing_growth_beta_def forcing_carry_step_def
          forcing_beta_alphabet_def Let_def split: if_splits)
  qed
qed

definition forcing_beta_difference_alphabet :: "int set" where
  "forcing_beta_difference_alphabet =
    {difference. \<exists>left\<in>forcing_beta_alphabet.
      \<exists>right\<in>forcing_beta_alphabet. difference = left-right}"

lemma forcing_beta_difference_finite:
  "finite forcing_beta_difference_alphabet"
proof -
  have finite_product:
    "finite (forcing_beta_alphabet \<times> forcing_beta_alphabet)"
    by (simp add: forcing_beta_alphabet_def)
  have image:
    "forcing_beta_difference_alphabet =
      (\<lambda>(left,right). left-right) `
        (forcing_beta_alphabet \<times> forcing_beta_alphabet)"
    by (auto simp: forcing_beta_difference_alphabet_def)
  show ?thesis unfolding image using finite_product by simp
qed

theorem forcing_beta_difference_alphabet_exact:
  "forcing_beta_difference_alphabet =
    {-22,-21,-20,-19,-18,-11,-10,-9,-2,-1,0,1,2,9,10,11,18,19,20,21,22}"
  by (auto simp: forcing_beta_difference_alphabet_def forcing_beta_alphabet_def)

corollary forcing_beta_difference_has_zero_boundary:
  "0 \<in> forcing_beta_difference_alphabet \<and>
    -21 \<in> forcing_beta_difference_alphabet \<and>
    -1 \<in> forcing_beta_difference_alphabet \<and>
    21 \<in> forcing_beta_difference_alphabet"
  by (simp add: forcing_beta_difference_alphabet_exact)

theorem reverse_196_beta_difference_counterexample:
  "forcing_beta 7 0 1 - forcing_beta 18 0 0 = 21 \<and>
    21 \<in> forcing_beta_difference_alphabet \<and>
    21 \<notin> forcing_beta_alphabet"
  by (simp add: forcing_beta_def forcing_carry_step_def
      forcing_beta_difference_alphabet_exact forcing_beta_alphabet_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms forcing_step_matches_shared
        forcing_no_growth_beta_in_alphabet
        forcing_no_growth_values_exact
        forcing_no_growth_excludes_minus_ten_and_minus_eight
        forcing_growth_beta_in_alphabet
        forcing_beta_difference_finite
        forcing_beta_difference_alphabet_exact
        reverse_196_beta_difference_counterexample})
    then () else error "Forcing alphabet depends on an oracle";
\<close>

end
