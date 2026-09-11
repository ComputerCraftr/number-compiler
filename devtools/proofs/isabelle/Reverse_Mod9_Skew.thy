theory Reverse_Mod9_Skew
  imports Reverse_Growth_Coboundary
begin

text \<open>The decimal threshold consumer admits a mod-9 skew coordinate.
The carry remains a projection of the carry domain.  The value coordinate is
u = S mod 9; the only lift is the geometry-derived predicate z saying that q
is the upper representative 9.  This theory proves the exact forward
factorization for arbitrary pairs of local operands, so the same theorem
applies to mirrored no-growth operands and adjacent growth operands.\<close>

definition point_q :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "point_q S c = int S - 9 * int (decimal_carry S c)"

definition threshold_residue9 :: "nat \<Rightarrow> nat" where
  "threshold_residue9 S = S mod 9"

definition point_lift :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "point_lift S c = (if point_q S c = 9 then 1 else 0)"

definition geometry_lift :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "geometry_lift S c = (if threshold_residue9 S = 0 \<and>
    (domain S = Above \<or> (domain S = Equal \<and> c = 0)) then 1 else 0)"

definition point_reset :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "point_reset S c = int (decimal_carry S c) - int c"

definition point_digit :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "point_digit S c =
    int S + int c - 10 * int (decimal_carry S c)"

definition skew_pair_value ::
    "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "skew_pair_value ua za rhoa ub zb rhob =
    int ua + int ub + 9 * (int za + int zb) - (rhoa + rhob)"

definition skew_pair_residue9 ::
    "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "skew_pair_residue9 ua rhoa ub rhob =
    (int ua + int ub - rhoa - rhob) mod 9"

definition signed_domain :: "int \<Rightarrow> carry_domain" where
  "signed_domain x = (if x < 9 then Below else if x = 9 then Equal else Above)"

definition skew_pair_domain ::
    "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> carry_domain" where
  "skew_pair_domain ua za rhoa ub zb rhob =
    signed_domain (skew_pair_value ua za rhoa ub zb rhob)"

lemma point_q_lift_factorization:
  assumes source: "S < 19" and incoming: "c < 2"
  shows "point_q S c = int (threshold_residue9 S) + 9 * int (point_lift S c)"
proof -
  have S_cases: "S = 0 \<or> S = 1 \<or> S = 2 \<or> S = 3 \<or> S = 4 \<or>
      S = 5 \<or> S = 6 \<or> S = 7 \<or> S = 8 \<or> S = 9 \<or>
      S = 10 \<or> S = 11 \<or> S = 12 \<or> S = 13 \<or> S = 14 \<or>
      S = 15 \<or> S = 16 \<or> S = 17 \<or> S = 18"
    using source by (rule nat_less_nineteen_cases)
  have c_cases: "c = 0 \<or> c = 1"
    using incoming by (rule nat_less_two_cases)
  show ?thesis using S_cases c_cases
    by (elim disjE; simp add: point_q_def threshold_residue9_def
      point_lift_def decimal_carry_def)
qed

lemma point_q_decimal_view:
  assumes "S < 19" "c < 2"
  shows "point_q S c = int ((S mod 10 + decimal_carry S c) mod 10)"
  unfolding point_q_def
  using growth_q_residue_view[OF assms] by simp

theorem point_lift_is_geometry_derived:
  assumes source: "S < 19" and incoming: "c < 2"
  shows "point_lift S c = geometry_lift S c"
proof -
  have S_cases: "S = 0 \<or> S = 1 \<or> S = 2 \<or> S = 3 \<or> S = 4 \<or>
      S = 5 \<or> S = 6 \<or> S = 7 \<or> S = 8 \<or> S = 9 \<or>
      S = 10 \<or> S = 11 \<or> S = 12 \<or> S = 13 \<or> S = 14 \<or>
      S = 15 \<or> S = 16 \<or> S = 17 \<or> S = 18"
    using source by (rule nat_less_nineteen_cases)
  have c_cases: "c = 0 \<or> c = 1"
    using incoming by (rule nat_less_two_cases)
  show ?thesis using S_cases c_cases
    by (elim disjE; simp add: point_lift_def point_q_def geometry_lift_def
      threshold_residue9_def decimal_carry_def domain_def)
qed

corollary point_q_mod9:
  assumes "S < 19" "c < 2"
  shows "point_q S c mod 9 = int (threshold_residue9 S)"
proof -
  have factorization: "point_q S c =
      int (threshold_residue9 S) + 9 * int (point_lift S c)"
    using point_q_lift_factorization[OF assms] .
  have bound: "threshold_residue9 S < 9"
    by (simp add: threshold_residue9_def)
  show ?thesis using factorization bound by simp
qed

theorem point_digit_skew_factorization:
  "point_digit S c = point_q S c - point_reset S c"
  unfolding point_digit_def point_q_def point_reset_def
  by (simp add: algebra_simps)

corollary point_digit_mod9_factorization:
  assumes "S < 19" "c < 2"
  shows "point_digit S c = int (threshold_residue9 S) +
    9 * int (point_lift S c) - point_reset S c"
  using point_digit_skew_factorization point_q_lift_factorization[OF assms]
  by simp

lemma point_digit_range:
  assumes source: "S < 19" and incoming: "c < 2"
  shows "0 \<le> point_digit S c" "point_digit S c \<le> 9"
proof -
  have S_cases: "S = 0 \<or> S = 1 \<or> S = 2 \<or> S = 3 \<or> S = 4 \<or>
      S = 5 \<or> S = 6 \<or> S = 7 \<or> S = 8 \<or> S = 9 \<or>
      S = 10 \<or> S = 11 \<or> S = 12 \<or> S = 13 \<or> S = 14 \<or>
      S = 15 \<or> S = 16 \<or> S = 17 \<or> S = 18"
    using source by (rule nat_less_nineteen_cases)
  have c_cases: "c = 0 \<or> c = 1"
    using incoming by (rule nat_less_two_cases)
  have bounds: "0 \<le> point_digit S c \<and> point_digit S c \<le> 9"
    using S_cases c_cases
    by (elim disjE; simp_all add: point_digit_def decimal_carry_def)
  show "0 \<le> point_digit S c" using bounds by simp
  show "point_digit S c \<le> 9" using bounds by simp
qed

theorem skew_pair_exact_value:
  assumes "Sa < 19" "ca < 2" "Sb < 19" "cb < 2"
  shows "point_digit Sa ca + point_digit Sb cb =
    skew_pair_value (threshold_residue9 Sa) (point_lift Sa ca)
      (point_reset Sa ca) (threshold_residue9 Sb) (point_lift Sb cb)
      (point_reset Sb cb)"
  unfolding skew_pair_value_def
  using point_digit_mod9_factorization[OF assms(1,2)]
    point_digit_mod9_factorization[OF assms(3,4)]
  by (simp add: algebra_simps)

theorem skew_pair_exact_residue9:
  assumes "Sa < 19" "ca < 2" "Sb < 19" "cb < 2"
  shows "(point_digit Sa ca + point_digit Sb cb) mod 9 =
    skew_pair_residue9 (threshold_residue9 Sa) (point_reset Sa ca)
      (threshold_residue9 Sb) (point_reset Sb cb)"
proof -
  have exact: "point_digit Sa ca + point_digit Sb cb =
      int (threshold_residue9 Sa) + int (threshold_residue9 Sb) +
      9 * (int (point_lift Sa ca) + int (point_lift Sb cb)) -
      (point_reset Sa ca + point_reset Sb cb)"
    using skew_pair_exact_value[OF assms]
    by (simp add: skew_pair_value_def)
  have rearranged: "int (threshold_residue9 Sa) + int (threshold_residue9 Sb) +
      9 * (int (point_lift Sa ca) + int (point_lift Sb cb)) -
      (point_reset Sa ca + point_reset Sb cb) =
      (int (threshold_residue9 Sa) + int (threshold_residue9 Sb) -
        (point_reset Sa ca + point_reset Sb cb)) +
      (int (point_lift Sa ca) + int (point_lift Sb cb)) * 9"
    by linarith
  show ?thesis
    unfolding skew_pair_residue9_def
    apply (subst exact)
    apply (subst rearranged)
    apply (subst mod_mult_self1)
    by (simp add: algebra_simps)
qed

lemma signed_domain_agrees:
  assumes nonnegative: "0 \<le> x"
  shows "signed_domain x = domain (nat x)"
proof (cases "x < 9")
  case True
  then have "nat x < 9" using nonnegative by linarith
  then show ?thesis using True by (simp add: signed_domain_def domain_def)
next
  case False
  then consider (equal) "x = 9" | (above) "9 < x" by linarith
  then show ?thesis
  proof cases
    case equal
    then show ?thesis by (simp add: signed_domain_def domain_def)
  next
    case above
    then have "9 < nat x" using nonnegative by linarith
    then show ?thesis using above by (simp add: signed_domain_def domain_def)
  qed
qed

theorem skew_pair_exact_domain:
  assumes "Sa < 19" "ca < 2" "Sb < 19" "cb < 2"
  shows "domain (nat (point_digit Sa ca + point_digit Sb cb)) =
    skew_pair_domain (threshold_residue9 Sa) (point_lift Sa ca)
      (point_reset Sa ca) (threshold_residue9 Sb) (point_lift Sb cb)
      (point_reset Sb cb)"
proof -
  have nonnegative: "0 \<le> point_digit Sa ca + point_digit Sb cb"
    using point_digit_range[OF assms(1,2)] point_digit_range[OF assms(3,4)]
    by linarith
  have exact: "point_digit Sa ca + point_digit Sb cb =
      skew_pair_value (threshold_residue9 Sa) (point_lift Sa ca)
        (point_reset Sa ca) (threshold_residue9 Sb) (point_lift Sb cb)
        (point_reset Sb cb)"
    using skew_pair_exact_value[OF assms] .
  show ?thesis
    unfolding skew_pair_domain_def
    using signed_domain_agrees[OF nonnegative] exact by simp
qed

lemma growth_constant_digit:
  "threshold_residue9 1 = 1"
  "point_lift 1 0 = 0"
  "point_reset 1 0 = 0"
  "point_digit 1 0 = 1"
  by (simp_all add: threshold_residue9_def point_lift_def point_q_def
    point_reset_def point_digit_def decimal_carry_def)

corollary growth_edge_skew_value:
  assumes "S < 19" "c < 2"
  shows "point_digit S c + 1 =
    skew_pair_value (threshold_residue9 S) (point_lift S c)
      (point_reset S c) 1 0 0"
  using skew_pair_exact_value[OF assms, of 1 0]
  by (simp add: threshold_residue9_def point_lift_def point_q_def
    point_reset_def point_digit_def decimal_carry_def)

corollary growth_edge_skew_residue9:
  assumes "S < 19" "c < 2"
  shows "(point_digit S c + 1) mod 9 =
    skew_pair_residue9 (threshold_residue9 S) (point_reset S c) 1 0"
  using skew_pair_exact_residue9[OF assms, of 1 0]
  by (simp add: threshold_residue9_def point_reset_def point_digit_def
    decimal_carry_def)

corollary growth_edge_skew_domain:
  assumes "S < 19" "c < 2"
  shows "domain (nat (point_digit S c + 1)) =
    skew_pair_domain (threshold_residue9 S) (point_lift S c)
      (point_reset S c) 1 0 0"
  using skew_pair_exact_domain[OF assms, of 1 0]
  by (simp only: growth_constant_digit(1) growth_constant_digit(2)
    growth_constant_digit(3) growth_constant_digit(4))

ML \<open>
  val checked = @{thms point_q_lift_factorization point_q_decimal_view
    point_lift_is_geometry_derived point_q_mod9
    point_digit_skew_factorization point_digit_mod9_factorization
    point_digit_range skew_pair_exact_value skew_pair_exact_residue9
    signed_domain_agrees skew_pair_exact_domain growth_constant_digit
    growth_edge_skew_value growth_edge_skew_residue9 growth_edge_skew_domain};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mod-9 skew proof depends on an oracle";
\<close>

end
