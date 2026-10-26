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

definition decimal_base10_digit :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "decimal_base10_digit j n = (n div 10 ^ j) mod 10"

definition decimal_base10_column_carry ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "decimal_base10_column_carry j a b \<longleftrightarrow>
    ((a mod 10 ^ Suc j + b mod 10 ^ Suc j) div 10 ^ Suc j = 1)"

lemma decimal_base10_digit_quotient_expansion:
  "n div 10 ^ j =
    10 * (n div 10 ^ Suc j) + decimal_base10_digit j n"
proof -
  have power: "(10::nat) ^ Suc j = 10 ^ j * 10"
    by (simp add: power_Suc mult.commute)
  have nested: "n div 10 ^ Suc j = (n div 10 ^ j) div 10"
    by (simp only: power div_mult2_eq)
  have split: "n div 10 ^ j =
      10 * ((n div 10 ^ j) div 10) + (n div 10 ^ j) mod 10"
    by (simp add: div_mult_mod_eq mult.commute)
  show ?thesis
    unfolding decimal_base10_digit_def
    using nested split by arith
qed

lemma decimal_base10_column_carry_value:
  fixes j a b :: nat
  shows "(if decimal_base10_column_carry j a b then 1 else 0) =
    (a mod 10 ^ Suc j + b mod 10 ^ Suc j) div 10 ^ Suc j"
proof -
  let ?M = "(10::nat) ^ Suc j"
  have positive: "0 < ?M" by simp
  have remainders: "a mod ?M < ?M" "b mod ?M < ?M" by simp_all
  have sum_bound: "a mod ?M + b mod ?M < 2 * ?M"
    using remainders by arith
  have q_bound: "(a mod ?M + b mod ?M) div ?M < 2"
    using sum_bound positive by (simp add: div_less_iff_less_mult)
  then have q_cases:
    "(a mod ?M + b mod ?M) div ?M = 0 \<or>
     (a mod ?M + b mod ?M) div ?M = 1"
    by arith
  show ?thesis
    unfolding decimal_base10_column_carry_def
    using q_cases by auto
qed

lemma decimal_base10_column_addition_defect:
  fixes j a b :: nat
  shows "int (decimal_base10_digit j a) +
      int (decimal_base10_digit j b) -
      int (decimal_base10_digit j (a+b)) =
    10 * int (if decimal_base10_column_carry j a b then 1 else 0) -
      int (if j=0 then 0 else
        if decimal_base10_column_carry (j-1) a b then 1 else 0)"
proof -
  let ?M = "(10::nat) ^ Suc j"
  let ?m = "(10::nat) ^ j"
  let ?q = "(a mod ?M + b mod ?M) div ?M"
  let ?r = "(a mod ?m + b mod ?m) div ?m"
  have power: "?M = 10 * ?m"
    by (simp add: power_Suc)
  have digit_a:
    "a div ?m = 10 * (a div ?M) + decimal_base10_digit j a"
    by (rule decimal_base10_digit_quotient_expansion)
  have digit_b:
    "b div ?m = 10 * (b div ?M) + decimal_base10_digit j b"
    by (rule decimal_base10_digit_quotient_expansion)
  have digit_sum:
    "(a+b) div ?m =
      10 * ((a+b) div ?M) + decimal_base10_digit j (a+b)"
    by (rule decimal_base10_digit_quotient_expansion)
  have quotient_M:
    "(a+b) div ?M = a div ?M + b div ?M + ?q"
    by (rule div_add1_eq)
  have quotient_m:
    "(a+b) div ?m = a div ?m + b div ?m + ?r"
    by (rule div_add1_eq)
  have prior:
    "?r = (if j=0 then 0 else
      (if decimal_base10_column_carry (j-1) a b then 1 else 0))"
  proof (cases j)
    case 0
    then show ?thesis by simp
  next
    case (Suc k)
    have carry_fact:
      "(if decimal_base10_column_carry k a b then 1 else 0) =
        (a mod 10 ^ Suc k + b mod 10 ^ Suc k) div 10 ^ Suc k"
      by (rule decimal_base10_column_carry_value)
    show ?thesis using Suc carry_fact by simp
  qed
  have current:
    "(if decimal_base10_column_carry j a b then 1 else 0) = ?q"
    by (rule decimal_base10_column_carry_value)
  have natural:
    "decimal_base10_digit j a + decimal_base10_digit j b + ?r =
      decimal_base10_digit j (a+b) + 10 * ?q"
    using digit_a digit_b digit_sum quotient_M quotient_m
    by arith
  show ?thesis using natural current prior
    by (simp only: of_nat_add of_nat_mult of_nat_numeral; linarith)
qed

lemma decimal_base10_column_defect_telescope:
  fixes j n :: nat and k increment :: "nat \<Rightarrow> nat"
  assumes step: "\<And>t. t<n \<Longrightarrow> k (Suc t) = k t + increment t"
  shows "int (decimal_base10_digit j (k 0)) +
      (\<Sum>t<n. int (decimal_base10_digit j (increment t))) -
      int (decimal_base10_digit j (k n)) =
    10 * (\<Sum>t<n. int (if decimal_base10_column_carry j (k t) (increment t)
      then 1 else 0)) -
      (if j=0 then 0 else
        (\<Sum>t<n. int (if decimal_base10_column_carry (j-1) (k t)
          (increment t) then 1 else 0)))"
  using step
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have priorstep: "\<And>t. t<n \<Longrightarrow> k (Suc t) = k t + increment t"
    using Suc.prems by auto
  have induction_hypothesis:
    "int (decimal_base10_digit j (k 0)) +
      (\<Sum>t<n. int (decimal_base10_digit j (increment t))) -
      int (decimal_base10_digit j (k n)) =
    10 * (\<Sum>t<n. int (if decimal_base10_column_carry j (k t) (increment t)
      then 1 else 0)) -
      (if j=0 then 0 else
        (\<Sum>t<n. int (if decimal_base10_column_carry (j-1) (k t)
          (increment t) then 1 else 0)))"
    by (rule Suc.IH[OF priorstep])
  have step_eq: "k (Suc n) = k n + increment n"
    using Suc.prems by simp
  have local:
    "int (decimal_base10_digit j (k n)) +
      int (decimal_base10_digit j (increment n)) -
      int (decimal_base10_digit j (k n + increment n)) =
      10 * int (if decimal_base10_column_carry j (k n) (increment n)
        then 1 else 0) -
      int (if j=0 then 0 else
        if decimal_base10_column_carry (j-1) (k n) (increment n)
          then 1 else 0)"
    by (rule decimal_base10_column_addition_defect)
  have prior_distribute:
    "(if j=0 then (0::int) else
       (\<Sum>t<n. int (if decimal_base10_column_carry (j-1) (k t)
         (increment t) then 1 else 0)) +
       int (if decimal_base10_column_carry (j-1) (k n) (increment n)
         then 1 else 0)) =
     (if j=0 then 0 else
       (\<Sum>t<n. int (if decimal_base10_column_carry (j-1) (k t)
         (increment t) then 1 else 0))) +
       int (if j=0 then 0 else
         if decimal_base10_column_carry (j-1) (k n) (increment n)
           then 1 else 0)"
    by (cases "j=0") simp_all
  note combined = arg_cong2[where f="(+) :: int \<Rightarrow> int \<Rightarrow> int",
    OF induction_hypothesis local]
  show ?case
    using combined
    unfolding sum.lessThan_Suc step_eq prior_distribute
    by (simp add: algebra_simps)
qed

text \<open>
In a cyclic spatial coefficient quotient of positive period, a root z with
z^period congruent to 1 modulo 32 has inverse z^(period-1). The following
fixed five-term polynomial then inverts 10-z modulo 32. This coordinate is
spatial: it does not identify a C1 physical-time count or the separate
modulo-924 selector clock. The carry reconstruction below is only a
projection of an already supplied boundary-aware normalization identity; it
does not infer an output or branch from a residue.
\<close>

definition decimal_base_z_inverse_kernel :: "'a::comm_ring_1 \<Rightarrow> 'a" where
  "decimal_base_z_inverse_kernel w =
    -(w + 10*w^2 + 100*w^3 + 1000*w^4 + 10000*w^5)"

definition decimal_base_z_mod32_inverse ::
    "nat \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a" where
  "decimal_base_z_mod32_inverse period z =
    decimal_base_z_inverse_kernel (z^(period-1))"

lemma decimal_base_z_inverse_kernel_product:
  fixes z w :: "'a::comm_ring_1"
  shows "(10-z) * decimal_base_z_inverse_kernel w =
    1 - 100000*w^5 + (z*w-1) *
      (1 + 10*w + 100*w^2 + 1000*w^3 + 10000*w^4)"
  unfolding decimal_base_z_inverse_kernel_def
  by (simp add: power_numeral_even power_numeral_odd power2_eq_square algebra_simps)

lemma decimal_mod32_binary_nilpotent:
  assumes characteristic: "(32::'a::comm_ring_1)=0"
  shows "(2::'a)^5=0"
  using characteristic
  by (simp add: power_numeral_even power_numeral_odd power2_eq_square)

lemma decimal_mod32_coefficient_annihilator:
  fixes a b :: "'a::comm_ring_1"
  assumes characteristic: "(32::'a)=0"
    and factor: "a=2^s*b" and enough: "5 \<le> s+j"
  shows "a*10^j=0"
proof -
  have binary_zero: "(2::'a)^5=0"
    by (rule decimal_mod32_binary_nilpotent[OF characteristic])
  have exponent: "s+j=5+(s+j-5)" using enough by arith
  have binary: "(2::'a)^(s+j)=0"
    by (subst exponent) (simp only: power_add binary_zero mult_zero_left)
  have radix: "(10::'a)^j=2^j*5^j"
    using power_mult_distrib[of "2::'a" 5 j] by simp
  have factored: "a*10^j=2^(s+j)*(b*5^j)"
    by (simp add: factor radix power_add algebra_simps)
  show ?thesis using factored binary by simp
qed

lemma decimal_mod32_integer_coefficient_annihilator:
  fixes coefficient :: int
  assumes characteristic: "(32::'a::comm_ring_1)=0"
    and divisible: "(2::int)^s dvd coefficient"
    and enough: "5 \<le> s+j"
  shows "(of_int coefficient::'a)*10^j=0"
proof -
  obtain b where coefficient: "coefficient=2^s*b"
    using divisible by (auto simp: dvd_def)
  have factor: "(of_int coefficient::'a)=2^s*of_int b"
    by (simp only: coefficient of_int_mult of_int_power of_int_numeral)
  show ?thesis
    by (rule decimal_mod32_coefficient_annihilator[OF characteristic factor enough])
qed

lemma decimal_mod32_radix_nilpotent:
  assumes characteristic: "(32::'a::comm_ring_1)=0"
  shows "(10::'a)^5=0"
  using decimal_mod32_coefficient_annihilator[OF characteristic,
    where a=1 and b=1 and s=0 and j=5] by simp

lemma decimal_base_z_mod32_inverse_is_unit:
  fixes z w :: "'a::comm_ring_1"
  assumes characteristic: "(32::'a) = 0"
    and inverse_root: "z*w=1"
  shows "(10-z) * decimal_base_z_inverse_kernel w = 1"
proof -
  have nilpotent: "(100000::'a) = 0"
    using decimal_mod32_radix_nilpotent[OF characteristic]
    by (simp add: power_numeral_even power_numeral_odd power2_eq_square)
  have identity:
      "(10-z) * decimal_base_z_inverse_kernel w =
        1 - 100000*w^5 + (z*w-1) *
          (1 + 10*w + 100*w^2 + 1000*w^3 + 10000*w^4)"
    by (rule decimal_base_z_inverse_kernel_product)
  show ?thesis using identity inverse_root nilpotent by simp
qed

lemma decimal_base_z_cyclic_inverse_root:
  fixes period :: nat and z :: "'a::comm_ring_1"
  assumes positive: "0 < period" and cyclic: "z^period=1"
  shows "z * z^(period-1)=1"
proof -
  have exponent: "Suc (period-1)=period" using positive by arith
  have "z * z^(period-1) = z^(Suc (period-1))" by (simp only: power_Suc)
  also have "... = z^period" by (simp only: exponent)
  finally show ?thesis using cyclic by simp
qed

theorem decimal_base_z_mod32_carry_reconstruction_from_inverse:
  fixes z w raw normalized carry boundary :: "'a::comm_ring_1"
  assumes characteristic: "(32::'a) = 0"
    and inverse_root: "z*w=1"
    and defect: "raw-normalized = (10-z)*carry + boundary"
  shows "carry = decimal_base_z_inverse_kernel w *
      (raw-normalized-boundary)"
proof -
  have unit:
      "decimal_base_z_inverse_kernel w * (10-z) = 1"
    using decimal_base_z_mod32_inverse_is_unit
      [OF characteristic inverse_root]
    by (simp add: mult.commute)
  have defect_only: "raw-normalized-boundary = (10-z)*carry"
    using defect by simp
  show ?thesis using defect_only unit
    by (simp add: mult.assoc[symmetric])
qed

theorem decimal_base_z_mod32_carry_reconstruction:
  fixes period :: nat and z raw normalized carry boundary :: "'a::comm_ring_1"
  assumes positive: "0 < period"
    and characteristic: "(32::'a) = 0"
    and cyclic: "z^period=1"
    and defect: "raw-normalized = (10-z)*carry + boundary"
  shows "carry = decimal_base_z_mod32_inverse period z *
      (raw-normalized-boundary)"
proof -
  have inverse_root: "z * z^(period-1)=1"
    by (rule decimal_base_z_cyclic_inverse_root[OF positive cyclic])
  have reconstructed:
      "carry = decimal_base_z_inverse_kernel (z^(period-1)) *
        (raw-normalized-boundary)"
    by (rule decimal_base_z_mod32_carry_reconstruction_from_inverse
      [OF characteristic inverse_root defect])
  show ?thesis using reconstructed
    by (simp add: decimal_base_z_mod32_inverse_def)
qed


ML \<open>
  val checked = @{thms normalization_gate_exact xor3_is_boolean_xor
    majority3_is_boolean_majority full_adder_gate_exact full_adder_domain_exact
    crt_digit_coordinates_exact crt_digit_inverse parity_addition_coordinates
    parity_normalization_exact decimal_sum_digit_mod kappa_and_eq_domain_exact
    output_crt_threshold_exact normalized_output_crt_threshold_exact
    decimal_base10_digit_quotient_expansion
    decimal_base10_column_carry_value
    decimal_base10_column_addition_defect
    decimal_base10_column_defect_telescope
    decimal_kappa_cocycle decimal_base_z_inverse_kernel_product
    decimal_mod32_binary_nilpotent decimal_mod32_coefficient_annihilator
    decimal_mod32_integer_coefficient_annihilator decimal_mod32_radix_nilpotent
    decimal_base_z_cyclic_inverse_root
    decimal_base_z_mod32_inverse_is_unit
    decimal_base_z_mod32_carry_reconstruction_from_inverse
    decimal_base_z_mod32_carry_reconstruction encode_cocycle_def};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Shared decimal-cocycle proof depends on an oracle";
\<close>

end
