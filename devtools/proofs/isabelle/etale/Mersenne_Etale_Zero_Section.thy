theory Mersenne_Etale_Zero_Section
  imports Etale_Primality_Bridge
begin

text \<open>The exact cyclic fold of a binary square evaluated at radix two.
This double sum is the weighted coefficient word before subtracting two.
It is not the terminal Lucas--Lehmer residue.\<close>

definition binary_value :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "binary_value w d = (\<Sum>i<w. d i * 2^i)"

definition cyclic_square_value :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "cyclic_square_value w d = (\<Sum>i<w. \<Sum>j<w. d i * d j * 2^((i+j) mod w))"

definition cyclic_square_coefficient :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "cyclic_square_coefficient w d k =
    (\<Sum>i<w. \<Sum>j<w. if (i+j) mod w = k then d i * d j else 0)"

lemma cyclic_fold_evaluation:
  assumes width: "0 < w"
  shows "(\<Sum>k<w. cyclic_square_coefficient w d k * 2^k) = cyclic_square_value w d"
proof -
  have summand: "(if (i+j) mod w = k then d i*d j else 0) * 2^k =
      (if (i+j) mod w = k then d i*d j*2^k else 0)" for i j k
    by (cases "(i+j) mod w = k") simp_all
  have fold_term: "(\<Sum>k<w. (if (i+j) mod w = k then d i * d j else 0) * 2^k) =
      d i * d j * 2^((i+j) mod w)" for i j
    using width by (simp only: summand sum.delta'; simp)
  show ?thesis
    unfolding cyclic_square_coefficient_def cyclic_square_value_def
    apply (simp only: sum_distrib_right)
    apply (subst sum.swap[where g="\<lambda>k i. \<Sum>j<w.
      (if (i+j) mod w = k then d i*d j else 0) * 2^k"])
    apply (rule sum.cong)
     apply (rule refl)
    apply (subst sum.swap)
    apply (simp only: fold_term)
    done
qed

definition mersenne_square_field :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> int" where
  "mersenne_square_field w d k = int (cyclic_square_coefficient w d k) -
    (if k=0 then 2 else 0)"

lemma mersenne_square_field_evaluation:
  assumes width: "0 < w"
  shows "polynomial_prefix (mersenne_square_field w d) w 2 =
    int (cyclic_square_value w d) - 2"
proof -
  have coefficient_term: "mersenne_square_field w d k * 2^k =
      int (cyclic_square_coefficient w d k * 2^k) - (if k=0 then 2 else 0)" for k
    by (cases "k=0") (simp_all add: mersenne_square_field_def diff_mult_distrib)
  have cast_fold: "(\<Sum>k<w. int (cyclic_square_coefficient w d k) * (2::int)^k) =
      int (cyclic_square_value w d)"
    using arg_cong[OF cyclic_fold_evaluation[OF width, of d], of int] by simp
  show ?thesis
    unfolding polynomial_prefix_def
    using cast_fold width
    by (simp add: coefficient_term sum_subtractf)
qed

lemma diagonal_below_cyclic_square:
  assumes "i < w"
  shows "d i * d i * 2^((i+i) mod w) \<le> cyclic_square_value w d"
proof -
  have first: "d i * d i * 2^((i+i) mod w) \<le>
      (\<Sum>j<w. d i * d j * 2^((i+j) mod w))"
    using assms by (intro member_le_sum) auto
  have second: "(\<Sum>j<w. d i * d j * 2^((i+j) mod w)) \<le>
      cyclic_square_value w d"
    unfolding cyclic_square_value_def using assms
    by (intro member_le_sum) auto
  show ?thesis using first second by arith
qed

lemma odd_cyclic_square_small_forces_single_low_bit:
  assumes width: "0 < w" "odd w"
    and binary: "\<And>i. i<w \<Longrightarrow> d i \<le> 1"
    and small: "cyclic_square_value w d \<le> 1"
  shows "binary_value w d \<le> 1"
proof -
  have vanishes: "d i = 0" if i: "i<w" "i\<noteq>0" for i
  proof (rule ccontr)
    assume "d i \<noteq> 0"
    then have bit: "d i=1" using binary[OF i(1)] by arith
    have power: "(2::nat)^((i+i) mod w) \<le> 1"
      using diagonal_below_cyclic_square[OF i(1), of d] small bit by simp
    have zero: "(i+i) mod w = 0"
    proof (rule ccontr)
      assume "(i+i) mod w \<noteq> 0"
      then have "1 < (2::nat)^((i+i) mod w)" by (intro one_less_power) auto
      with power show False by arith
    qed
    have divides: "w dvd i*2" using zero by (simp add: dvd_eq_mod_eq_0 mult_2_right)
    have coprime: "coprime w 2" using width(2) by simp
    have "w dvd i" using divides coprime_dvd_mult_left_iff[OF coprime] by simp
    with i width show False by (auto dest: dvd_imp_le)
  qed
  have low_sum: "(\<Sum>i\<in>{0}. d i * 2^i) = (\<Sum>i<w. d i * 2^i)"
    by (rule sum.mono_neutral_cong_left) (use width vanishes in auto)
  have word_value: "binary_value w d = d 0"
    using low_sum by (simp add: binary_value_def)
  show ?thesis using word_value binary[of 0] width by simp
qed

lemma cyclic_minus_two_seam_negative_forces_small_square:
  fixes N S :: nat
  assumes N: "0 < N" and seam: "(int S - 2) div int N = -1"
  shows "S \<le> 1"
proof -
  have remainder: "(int S-2) mod int N < int N" using N by simp
  have division: "((int S-2) div int N) * int N + (int S-2) mod int N = int S-2"
    by (rule div_mult_mod_eq)
  have equation: "- int N + (int S-2) mod int N = int S-2"
    using division by (simp only: seam mult_minus1)
  have "int S < 2" using remainder equation by linarith
  then show ?thesis by linarith
qed

lemma cyclic_normalization_seam_quotient:
  fixes a r c :: "nat \<Rightarrow> int"
  assumes width: "0 < w" and modulus: "int N = (2::int)^w - 1"
    and steps: "\<And>i. i<w \<Longrightarrow> a i + c i = r i + 2*c (Suc i)"
    and boundary: "c w = c 0"
    and remainder: "0 \<le> polynomial_prefix r w 2" "polynomial_prefix r w 2 < int N"
  shows "polynomial_prefix a w 2 div int N = c 0"
proof -
  have identity: "polynomial_prefix a w 2 - polynomial_prefix r w 2 = c 0 * int N"
    using carry_normalization_identity[where a=a and c=c and r=r and L=w and z=2, OF steps]
    unfolding modulus boundary by (simp add: algebra_simps)
  have positive: "0 < int N" using remainder by linarith
  have split: "polynomial_prefix a w 2 = polynomial_prefix r w 2 + c 0 * int N"
    using identity by linarith
  show ?thesis using remainder positive
    by (simp add: split div_add_self2)
qed

theorem mersenne_primary_carry_jet_zero_section:
  fixes N w :: nat and d :: "nat \<Rightarrow> nat"
  assumes width: "0 < w" "odd w"
    and modulus: "3 < N"
    and binary: "\<And>i. i<w \<Longrightarrow> d i \<le> 1"
    and etale_root: "N dvd binary_value w d * (binary_value w d + 2)"
    and zero_seam: "(int (cyclic_square_value w d)-2) div int N = -1"
  shows "binary_value w d = 0"
proof -
  have small_square: "cyclic_square_value w d \<le> 1"
    by (rule cyclic_minus_two_seam_negative_forces_small_square[OF _ zero_seam])
      (use modulus in arith)
  have small_value: "binary_value w d \<le> 1"
    by (rule odd_cyclic_square_small_forces_single_low_bit[OF width binary small_square])
  have "binary_value w d \<noteq> 1"
  proof
    assume "binary_value w d = 1"
    then have "N dvd 3" using etale_root by (simp add: numeral_3_eq_3)
    then have "N \<le> 3" by (rule dvd_imp_le) simp
    with modulus show False by arith
  qed
  with small_value show ?thesis by arith
qed

lemma zero_fold_seam:
  assumes "3 < N"
  shows "(int (cyclic_square_value w (\<lambda>_. 0))-2) div int N = -1"
proof -
  have positive: "0 < int N" and two: "(2::int) < int N" using assms by arith+
  show ?thesis
    using positive two
    by (simp add: cyclic_square_value_def zdiv_zminus1_eq_if)
qed

corollary mersenne_equal_zero_fold_key:
  fixes N w D :: nat and d :: "nat \<Rightarrow> nat" and j j0 :: carry_jet
  assumes width: "0 < w" "odd w"
    and modulus: "3 < N"
    and binary: "\<And>i. i<w \<Longrightarrow> d i \<le> 1"
    and root: "N dvd D*(D+2)"
    and deck: "deck = (binary_value w d \<noteq> D)"
    and key: "(deck, (int (cyclic_square_value w d)-2) div int N, j) =
      (False, (int (cyclic_square_value w (\<lambda>_. 0))-2) div int N, j0)"
  shows "D=0"
proof -
  have same_word: "binary_value w d = D"
    and seam: "(int (cyclic_square_value w d)-2) div int N = -1"
    using key deck zero_fold_seam[OF modulus, of w] by auto
  have root_word: "N dvd binary_value w d * (binary_value w d+2)"
    using root same_word by simp
  have "binary_value w d=0"
    by (rule mersenne_primary_carry_jet_zero_section[OF width modulus binary root_word seam])
  with same_word show ?thesis by simp
qed

definition primary_root_key :: "bool \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow>
    bool \<times> int \<times> carry_jet" where
  "primary_root_key deck w c = (deck, c 0,
    jet_reduce (coefficient_jet (\<lambda>i. c (Suc i)) w))"

theorem mersenne_normalized_root_zero_section:
  fixes N w D :: nat and d :: "nat \<Rightarrow> nat" and r c :: "nat \<Rightarrow> int"
  assumes width: "0 < w" "odd w"
    and modulus: "3 < N" "int N = (2::int)^w - 1"
    and binary: "\<And>i. i<w \<Longrightarrow> d i \<le> 1"
    and root: "N dvd D*(D+2)"
    and deck: "deck = (binary_value w d \<noteq> D)"
    and steps: "\<And>i. i<w \<Longrightarrow> mersenne_square_field w d i + c i = r i + 2*c (Suc i)"
    and boundary: "c w = c 0"
    and remainder: "0 \<le> polynomial_prefix r w 2" "polynomial_prefix r w 2 < int N"
    and key: "primary_root_key deck w c = (False, -1, j)"
  shows "D=0"
proof -
  have same_word: "binary_value w d = D" and seam: "c 0 = -1"
    using key deck by (auto simp: primary_root_key_def)
  have quotient: "polynomial_prefix (mersenne_square_field w d) w 2 div int N = c 0"
    by (rule cyclic_normalization_seam_quotient[OF width(1) modulus(2) steps boundary remainder])
  have zero_seam: "(int (cyclic_square_value w d)-2) div int N = -1"
    using quotient seam mersenne_square_field_evaluation[OF width(1), of d] by simp
  have root_word: "N dvd binary_value w d * (binary_value w d+2)"
    using root same_word by simp
  have "binary_value w d = 0"
    by (rule mersenne_primary_carry_jet_zero_section[OF width modulus(1) binary root_word zero_seam])
  with same_word show ?thesis by simp
qed

text \<open>This proves the zero section for a zero deck bit: then the
sign-selected digit word represents D itself. Equality to the zero-root key
forces seam=-1. The two small primary-jet coordinates are unnecessary for this
Boolean separation theorem. It proves neither injectivity on all nonzero
roots nor the existence/construction of a terminal defect in this root set.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms diagonal_below_cyclic_square odd_cyclic_square_small_forces_single_low_bit
      cyclic_minus_two_seam_negative_forces_small_square
      mersenne_primary_carry_jet_zero_section cyclic_fold_evaluation
      mersenne_square_field_evaluation cyclic_normalization_seam_quotient
      mersenne_normalized_root_zero_section zero_fold_seam mersenne_equal_zero_fold_key}) then ()
    else error "Mersenne zero-section proof depends on an oracle";
\<close>
end
