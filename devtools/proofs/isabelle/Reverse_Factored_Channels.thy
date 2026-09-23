theory Reverse_Factored_Channels
  imports Reverse_Uniform_Runs
begin

text \<open>The exact primitive decimal successor in separate carry-domain,
F5, and Boolean-half channels.  These are local gate laws, not a proof that a
particular recursive representation is closed under temporal squaring.\<close>

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

definition factored_pair :: "nat \<Rightarrow> carry_domain \<times> nat \<times> nat" where
  "factored_pair s = (domain s, s mod 5, (s mod 10) div 5)"

lemma repunit_factored_phases:
  "map factored_pair (replicate n 2) = replicate n (Below,2,0)"
  "map factored_pair (replicate n 4) = replicate n (Below,4,0)"
  "map factored_pair (replicate n 8) = replicate n (Below,3,1)"
  "map factored_pair (replicate n 16) = replicate n (Above,1,1)"
  by (simp_all add: factored_pair_def domain_def)

theorem repunit_factored_four_events:
  "map factored_pair (run step 4 (replicate (Suc n) 2)) =
    (Below,2,1) # replicate n (Above,4,0) @ [(Below,2,1)]"
  using repunit_four_events[of n]
  by (simp add: factored_pair_def domain_def)

text \<open>The last theorem transports the already-proved arbitrary-length
uniform-run control into the three exact channels.  It does not assert that
the channel DAGs or their output residuals remain bounded under iteration.\<close>


text \<open>Exact residual functions used by PlaneAlgebra's spatial request
normalizer. Fixed inputs and repeated views are substituted simultaneously.
The option value is part of the function: undefined inputs cannot be merged
with defined zero. These are spatial bisimulation laws, not a finite temporal
quotient or a proof of the Python interner's implementation.\<close>

datatype plane_binding = PlaneConst nat | PlaneInput nat

fun plane_binding_value :: "nat list \<Rightarrow> plane_binding \<Rightarrow> nat" where
  "plane_binding_value xs (PlaneConst c) = c"
| "plane_binding_value xs (PlaneInput port) = xs ! port"

definition plane_cofactor_table ::
  "(nat list \<Rightarrow> nat option) \<Rightarrow> plane_binding list \<Rightarrow>
    nat list list \<Rightarrow> nat option list" where
  "plane_cofactor_table gate bindings assignments =
    map (\<lambda>xs. gate (map (plane_binding_value xs) bindings)) assignments"

lemma plane_cofactor_entry_refines:
  assumes "i < length assignments"
  shows "plane_cofactor_table gate bindings assignments ! i =
    gate (map (plane_binding_value (assignments ! i)) bindings)"
  using assms by (simp add: plane_cofactor_table_def)

lemma plane_cofactor_undefined_exact:
  assumes "i < length assignments"
  shows "plane_cofactor_table gate bindings assignments ! i = None \<longleftrightarrow>
    gate (map (plane_binding_value (assignments ! i)) bindings) = None"
  using plane_cofactor_entry_refines[OF assms] by simp

lemma plane_diagonal_binding_exact:
  "map (plane_binding_value xs) [PlaneInput i, PlaneConst c, PlaneInput i] =
    [xs!i, c, xs!i]"
  by simp

lemma plane_complete_residual_bisimulation:
  "plane_cofactor_table f a assignments = plane_cofactor_table g b assignments
    \<longleftrightarrow> (\<forall>xs \<in> set assignments.
      f (map (plane_binding_value xs) a) = g (map (plane_binding_value xs) b))"
  by (simp add: plane_cofactor_table_def map_eq_conv)

lemma plane_projection_elimination:
  assumes "\<And>xs. xs \<in> set assignments \<Longrightarrow>
    gate (map (plane_binding_value xs) bindings) = Some (xs!port)"
  shows "plane_cofactor_table gate bindings assignments =
    map (\<lambda>xs. Some (xs!port)) assignments"
  unfolding plane_cofactor_table_def using assms by (intro map_cong) auto

lemma plane_constant_elimination:
  assumes "\<And>xs. xs \<in> set assignments \<Longrightarrow>
    gate (map (plane_binding_value xs) bindings) = result"
  shows "plane_cofactor_table gate bindings assignments =
    replicate (length assignments) result"
  using assms by (induction assignments) (auto simp: plane_cofactor_table_def)

lemma plane_cofactor_spatial_split:
  "plane_cofactor_table gate bindings (left @ right) =
    plane_cofactor_table gate bindings left @ plane_cofactor_table gate bindings right"
  by (simp add: plane_cofactor_table_def)

lemma plane_cofactor_interval:
  "take width (drop start (plane_cofactor_table gate bindings assignments)) =
    plane_cofactor_table gate bindings (take width (drop start assignments))"
  by (simp add: plane_cofactor_table_def take_map drop_map)

lemma automatic_sweep_charged_to_insertions:
  assumes "2 * (survivors::nat) \<le> population"
    and "population \<le> survivors + insertions"
  shows "population \<le> 2 * insertions"
  using assms by arith

section \<open>Fixed Q95 output alphabet and derived spatial carry\<close>

definition q95_encode :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "q95_encode symbol forcing = 5 * symbol + forcing"

lemma q95_decode:
  assumes "forcing < 5"
  shows "q95_encode symbol forcing div 5 = symbol"
    "q95_encode symbol forcing mod 5 = forcing"
  using assms by (simp_all add: q95_encode_def)

lemma q95_range:
  assumes "symbol < 19" "forcing < 5"
  shows "q95_encode symbol forcing < 95"
  using assms unfolding q95_encode_def by arith

lemma q95_derived_carry:
  assumes "forcing < 5"
  shows "carry_apply (domain (q95_encode symbol forcing div 5)) incoming =
    carry_apply (domain symbol) incoming"
  using q95_decode(1)[OF assms] by simp

text \<open>These are fixed leaf/projection laws. They do not construct a
future Q95 region, prove F2 erasure admission, or bound temporal grammar growth.
Incoming carry is a consumer of the three-state spatial summary, not an
additional coordinate of the Q95 alphabet.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms normalization_gate_exact xor3_is_boolean_xor
      majority3_is_boolean_majority full_adder_gate_exact
      full_adder_domain_exact repunit_factored_phases
      repunit_factored_four_events plane_cofactor_entry_refines
      plane_cofactor_undefined_exact plane_diagonal_binding_exact
      plane_complete_residual_bisimulation plane_projection_elimination
      plane_constant_elimination plane_cofactor_spatial_split
      plane_cofactor_interval automatic_sweep_charged_to_insertions
      q95_decode q95_range q95_derived_carry}) then ()
    else error "Factored channel proof depends on an oracle";
\<close>

end
