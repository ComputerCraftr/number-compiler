theory Shared_Decimal_Cocycle_Core
  imports Shared_Carry_Domain
begin

text \<open>Shared scalar decimal carry/cocycle arithmetic.  This owner contains
the exact radix-five/binary coordinates and decimal carry classification;
sequence-specific temporal successor and word iteration remain in family
theories.\<close>

definition digit_value :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "digit_value a b = a + 5*b"

definition normalize_alpha :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "normalize_alpha a c = (a+c) mod 5"

definition normalization_wrap :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "normalization_wrap a c = (if a = 4 \<and> c = 1 then 1 else 0)"

definition normalize_beta :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "normalize_beta a b c = (b + normalization_wrap a c) mod 2"

lemma nat_less_five_cases:
  assumes "(n::nat) < 5"
  shows "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4"
  using assms by arith

lemma nat_less_two_cases:
  assumes "(n::nat) < 2"
  shows "n = 0 \<or> n = 1"
  using assms by arith

lemma normalization_gate_exact:
  assumes "a < 5" "b < 2" "c < 2"
  shows "digit_value (normalize_alpha a c) (normalize_beta a b c) =
    (digit_value a b + c) mod 10"
proof -
  have a_cases: "a = 0 \<or> a = 1 \<or> a = 2 \<or> a = 3 \<or> a = 4"
    using assms(1) by (rule nat_less_five_cases)
  have b_cases: "b = 0 \<or> b = 1"
    using assms(2) by (rule nat_less_two_cases)
  have c_cases: "c = 0 \<or> c = 1"
    using assms(3) by (rule nat_less_two_cases)
  show ?thesis using a_cases b_cases c_cases
    by (elim disjE; simp add: digit_value_def normalize_alpha_def normalize_beta_def
        normalization_wrap_def)
qed

definition alpha_threshold :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "alpha_threshold a1 a2 = (if 5 \<le> a1+a2 then 1 else 0)"

definition add_alpha :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add_alpha a1 a2 = (a1+a2) mod 5"

definition xor3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "xor3 x y z = (x+y+z) mod 2"

definition majority3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "majority3 x y z = (if 2 \<le> x+y+z then 1 else 0)"

definition add_beta :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add_beta a1 b1 a2 b2 = xor3 b1 b2 (alpha_threshold a1 a2)"

definition add_high :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add_high a1 b1 a2 b2 = majority3 b1 b2 (alpha_threshold a1 a2)"

definition add_domain :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> carry_domain" where
  "add_domain a1 b1 a2 b2 =
    (if add_high a1 b1 a2 b2 = 1 then Above
     else if add_alpha a1 a2 = 4 \<and> add_beta a1 b1 a2 b2 = 1
     then Equal else Below)"

lemma xor3_is_boolean_xor:
  assumes "x < 2" "y < 2" "z < 2"
  shows "xor3 x y z = 1 \<longleftrightarrow>
    (((x = 1) \<noteq> (y = 1)) \<noteq> (z = 1))"
proof -
  have x_cases: "x = 0 \<or> x = 1"
    using assms(1) by (rule nat_less_two_cases)
  have y_cases: "y = 0 \<or> y = 1"
    using assms(2) by (rule nat_less_two_cases)
  have z_cases: "z = 0 \<or> z = 1"
    using assms(3) by (rule nat_less_two_cases)
  show ?thesis using x_cases y_cases z_cases
    by (elim disjE; simp add: xor3_def)
qed

lemma majority3_is_boolean_majority:
  assumes "x < 2" "y < 2" "z < 2"
  shows "majority3 x y z = 1 \<longleftrightarrow>
    (x = 1 \<and> y = 1) \<or> (x = 1 \<and> z = 1) \<or> (y = 1 \<and> z = 1)"
proof -
  have x_cases: "x = 0 \<or> x = 1"
    using assms(1) by (rule nat_less_two_cases)
  have y_cases: "y = 0 \<or> y = 1"
    using assms(2) by (rule nat_less_two_cases)
  have z_cases: "z = 0 \<or> z = 1"
    using assms(3) by (rule nat_less_two_cases)
  show ?thesis using x_cases y_cases z_cases
    by (elim disjE; simp add: majority3_def)
qed

lemma full_adder_gate_exact:
  assumes "a1 < 5" "a2 < 5" "b1 < 2" "b2 < 2"
  shows "add_alpha a1 a2 + 5*add_beta a1 b1 a2 b2
      + 10*add_high a1 b1 a2 b2 =
    digit_value a1 b1 + digit_value a2 b2"
proof -
  have a1_cases: "a1 = 0 \<or> a1 = 1 \<or> a1 = 2 \<or> a1 = 3 \<or> a1 = 4"
    using assms(1) by (rule nat_less_five_cases)
  have a2_cases: "a2 = 0 \<or> a2 = 1 \<or> a2 = 2 \<or> a2 = 3 \<or> a2 = 4"
    using assms(2) by (rule nat_less_five_cases)
  have b1_cases: "b1 = 0 \<or> b1 = 1"
    using assms(3) by (rule nat_less_two_cases)
  have b2_cases: "b2 = 0 \<or> b2 = 1"
    using assms(4) by (rule nat_less_two_cases)
  show ?thesis using a1_cases a2_cases b1_cases b2_cases
    by (elim disjE; simp add: add_alpha_def add_beta_def add_high_def alpha_threshold_def
        xor3_def majority3_def digit_value_def)
qed

lemma full_adder_domain_exact:
  assumes "a1 < 5" "a2 < 5" "b1 < 2" "b2 < 2"
  shows "add_domain a1 b1 a2 b2 =
    domain (digit_value a1 b1 + digit_value a2 b2)"
proof -
  have a1_cases: "a1 = 0 \<or> a1 = 1 \<or> a1 = 2 \<or> a1 = 3 \<or> a1 = 4"
    using assms(1) by (rule nat_less_five_cases)
  have a2_cases: "a2 = 0 \<or> a2 = 1 \<or> a2 = 2 \<or> a2 = 3 \<or> a2 = 4"
    using assms(2) by (rule nat_less_five_cases)
  have b1_cases: "b1 = 0 \<or> b1 = 1"
    using assms(3) by (rule nat_less_two_cases)
  have b2_cases: "b2 = 0 \<or> b2 = 1"
    using assms(4) by (rule nat_less_two_cases)
  show ?thesis using a1_cases a2_cases b1_cases b2_cases
    by (elim disjE; simp add: add_domain_def add_alpha_def add_beta_def add_high_def
        alpha_threshold_def xor3_def majority3_def digit_value_def domain_def)
qed


definition crt_digit :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "crt_digit a e = (if a mod 2 = e then a else a+5)"

definition parity_normalize_alpha :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "parity_normalize_alpha a c = (a+c) mod 5"

definition parity_normalize_epsilon :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "parity_normalize_epsilon e c = (e+c) mod 2"

lemma nat_less_ten_cases:
  assumes "(n::nat) < 10"
  shows "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<or>
    n = 5 \<or> n = 6 \<or> n = 7 \<or> n = 8 \<or> n = 9"
  using assms by arith

lemma crt_digit_coordinates_exact:
  assumes "a < 5" "e < 2"
  shows "crt_digit a e < 10"
    and "crt_digit a e mod 5 = a"
    and "crt_digit a e mod 2 = e"
proof -
  have a_parity: "a mod 2 < 2" by simp
  have a_parity_cases: "a mod 2 = 0 \<or> a mod 2 = 1"
    by (rule nat_less_two_cases[OF a_parity])
  have e_cases: "e = 0 \<or> e = 1"
    by (rule nat_less_two_cases[OF assms(2)])
  show "crt_digit a e < 10"
    using assms by (simp add: crt_digit_def; arith)
  show "crt_digit a e mod 5 = a"
    using assms by (simp add: crt_digit_def mod_add_eq)
  show "crt_digit a e mod 2 = e"
  proof (cases "a mod 2 = e")
    case True
    then show ?thesis by (simp add: crt_digit_def)
  next
    case False
    have shift: "(a+5) mod 2=(a mod 2+1) mod 2"
      by (subst mod_add_eq[symmetric]; simp)
    show ?thesis using a_parity_cases e_cases False
      by (elim disjE; simp add: crt_digit_def shift)
  qed
qed

lemma crt_digit_inverse:
  assumes "d < 10"
  shows "crt_digit (d mod 5) (d mod 2) = d"
proof -
  show ?thesis
  proof (cases "d < 5")
    case True
    then show ?thesis by (simp add: crt_digit_def)
  next
    case False
    then have lower: "5 \<le> d" by simp
    let ?t = "d - 5"
    have t_bound: "?t < 5" using assms lower by arith
    have split: "d = ?t + 5" using lower by arith
    have residue: "d mod 5 = ?t"
    proof -
      have "d mod 5 = (?t+5) mod 5"
        by (rule arg_cong[OF split])
      also have "... = ?t" using t_bound by simp
      finally show ?thesis .
    qed
    have parity_shift: "(?t+5) mod 2=(?t mod 2+1) mod 2"
      by (subst mod_add_eq[symmetric]; simp)
    have d_parity: "d mod 2=(?t mod 2+1) mod 2"
      using arg_cong[OF split, of "\<lambda>n. n mod 2"] parity_shift by metis
    have t_parity_cases: "?t mod 2 = 0 \<or> ?t mod 2 = 1"
      by (rule nat_less_two_cases) simp
    have mismatch: "?t mod 2 \<noteq> d mod 2"
      using t_parity_cases d_parity by (elim disjE; simp)
    show ?thesis
      unfolding crt_digit_def
      by (simp only: residue mismatch if_False; use lower in arith)
  qed
qed

lemma parity_addition_coordinates:
  assumes "a1 < 5" "e1 < 2" "a2 < 5" "e2 < 2"
  shows "(crt_digit a1 e1 + crt_digit a2 e2) mod 5 = (a1+a2) mod 5"
    and "(crt_digit a1 e1 + crt_digit a2 e2) mod 2 = (e1+e2) mod 2"
proof -
  have a1: "crt_digit a1 e1 mod 5 = a1"
    using assms(1,2) by (rule crt_digit_coordinates_exact(2))
  have e1: "crt_digit a1 e1 mod 2 = e1"
    using assms(1,2) by (rule crt_digit_coordinates_exact(3))
  have a2: "crt_digit a2 e2 mod 5 = a2"
    using assms(3,4) by (rule crt_digit_coordinates_exact(2))
  have e2: "crt_digit a2 e2 mod 2 = e2"
    using assms(3,4) by (rule crt_digit_coordinates_exact(3))
  show "(crt_digit a1 e1 + crt_digit a2 e2) mod 5 = (a1+a2) mod 5"
    using a1 a2 by (metis mod_add_eq)
  show "(crt_digit a1 e1 + crt_digit a2 e2) mod 2 = (e1+e2) mod 2"
    using e1 e2 by (metis mod_add_eq)
qed

lemma parity_normalization_exact:
  assumes "a < 5" "e < 2" "c < 2"
  shows "crt_digit (parity_normalize_alpha a c)
      (parity_normalize_epsilon e c) = (crt_digit a e+c) mod 10"
proof -
  have a_cases: "a = 0 \<or> a = 1 \<or> a = 2 \<or> a = 3 \<or> a = 4"
    using assms(1) by (rule nat_less_five_cases)
  have e_cases: "e = 0 \<or> e = 1"
    using assms(2) by (rule nat_less_two_cases)
  have c_cases: "c = 0 \<or> c = 1"
    using assms(3) by (rule nat_less_two_cases)
  show ?thesis using a_cases e_cases c_cases
    by (elim disjE; simp add: crt_digit_def parity_normalize_alpha_def
        parity_normalize_epsilon_def)
qed

definition decimal_kappa :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "decimal_kappa x y = (if 10 \<le> x+y then 1 else 0)"

definition decimal_sum_digit :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "decimal_sum_digit x y = x+y-10*decimal_kappa x y"

definition cocycle_output_domain :: "nat \<Rightarrow> nat \<Rightarrow> carry_domain" where
  "cocycle_output_domain x y =
    (if decimal_kappa x y = 1 then Above
     else if (x+y) mod 10 = 9 then Equal else Below)"

lemma decimal_sum_digit_mod:
  assumes "x < 10" "y < 10"
  shows "decimal_sum_digit x y = (x+y) mod 10"
proof (cases "x+y < 10")
  case True
  then show ?thesis
    by (simp add: decimal_sum_digit_def decimal_kappa_def)
next
  case False
  have total: "x+y = (x+y-10)+10" using assms False by arith
  have remainder: "x+y-10 < 10" using assms by arith
  have mod_eq: "(x+y) mod 10 = x+y-10"
  proof -
    have "(x+y) mod 10 = ((x+y-10)+10) mod 10" using total by simp
    also have "... = (x+y-10) mod 10" by simp
    also have "... = x+y-10" using remainder by simp
    finally show ?thesis .
  qed
  show ?thesis using False mod_eq
    by (simp add: decimal_sum_digit_def decimal_kappa_def)
qed

lemma kappa_and_eq_domain_exact:
  assumes "x < 10" "y < 10"
  shows "decimal_kappa x y = (if 10 \<le> x+y then 1 else 0)"
    and "cocycle_output_domain x y = domain (x+y)"
proof -
  show "decimal_kappa x y = (if 10 \<le> x+y then 1 else 0)"
    by (simp add: decimal_kappa_def)
  show "cocycle_output_domain x y = domain (x+y)"
  proof (cases "10 \<le> x+y")
    case True
    then show ?thesis
      by (simp add: cocycle_output_domain_def decimal_kappa_def domain_def)
  next
    case False
    then have less: "x+y < 10" by simp
    show ?thesis using less
      by (simp add: cocycle_output_domain_def decimal_kappa_def domain_def;
          arith)
  qed
qed


lemma output_crt_threshold_exact:
  assumes "x < 10" "y < 10"
  shows "cocycle_output_domain (crt_digit (x mod 5) (x mod 2))
    (crt_digit (y mod 5) (y mod 2)) = domain (x+y)"
  using crt_digit_inverse[OF assms(1)] crt_digit_inverse[OF assms(2)]
    kappa_and_eq_domain_exact(2)[OF assms] by simp

corollary normalized_output_crt_threshold_exact:
  "cocycle_output_domain
    (crt_digit (((s+c) mod 10) mod 5) (((s+c) mod 10) mod 2))
    (crt_digit (((t+d) mod 10) mod 5) (((t+d) mod 10) mod 2)) =
    domain ((s+c) mod 10 + (t+d) mod 10)"
  by (rule output_crt_threshold_exact) simp_all

text \<open>The two carries c and d are prefix actions at two reflected
coordinates of one LSD-to-MSD carry stream. This lemma consumes their admitted
values; it does not introduce an independent carry lane or construct a future
source's threshold field. Production SourceCarryPorts uses these normalized
channels in its second-layer interval leaves, with a separate leading-one case.
\<close>

lemma decimal_kappa_cocycle_normalized:
  assumes "x < 10" "y < 10" "z < 10"
  shows "decimal_kappa x y + decimal_kappa (decimal_sum_digit x y) z =
    decimal_kappa y z + decimal_kappa x (decimal_sum_digit y z)"
  using assms
  by (simp add: decimal_kappa_def decimal_sum_digit_def split: if_splits;
      arith)

theorem decimal_kappa_cocycle:
  assumes "x < 10" "y < 10" "z < 10"
  shows "decimal_kappa x y + decimal_kappa ((x+y) mod 10) z =
    decimal_kappa y z + decimal_kappa x ((y+z) mod 10)"
  using decimal_kappa_cocycle_normalized[OF assms]
    decimal_sum_digit_mod[OF assms(1,2)]
    decimal_sum_digit_mod[OF assms(2,3)]
  by simp



type_synonym native_cocycle = "carry_domain * nat * nat"

definition encode_cocycle :: "nat \<Rightarrow> native_cocycle" where
  "encode_cocycle s = (domain s, s mod 5, s mod 2)"

definition digit_channels :: "nat \<Rightarrow> nat * nat" where
  "digit_channels d = (d mod 5, d mod 2)"


ML \<open>
  val checked = @{thms normalization_gate_exact xor3_is_boolean_xor
    majority3_is_boolean_majority full_adder_gate_exact full_adder_domain_exact
    crt_digit_coordinates_exact crt_digit_inverse parity_addition_coordinates
    parity_normalization_exact decimal_sum_digit_mod kappa_and_eq_domain_exact
    output_crt_threshold_exact normalized_output_crt_threshold_exact
    decimal_kappa_cocycle encode_cocycle_def};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Shared decimal-cocycle proof depends on an oracle";
\<close>

end
