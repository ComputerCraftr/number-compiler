theory Reverse_Threshold_Cocycle
  imports Reverse_Factored_Channels
begin

text \<open>The Boolean coordinate is decimal parity.  The only nonlinear
piece left by the F5/parity sum is the ordinary decimal carry cocycle.  These
are scalar digit laws, not recursive spatial or 196-closure theorems.\<close>

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
  have a_cases: "a = 0 \<or> a = 1 \<or> a = 2 \<or> a = 3 \<or> a = 4"
    using assms(1) by (rule nat_less_five_cases)
  have e_cases: "e = 0 \<or> e = 1"
    using assms(2) by (rule nat_less_two_cases)
  show "crt_digit a e < 10"
    using a_cases e_cases by (elim disjE; simp add: crt_digit_def)
  show "crt_digit a e mod 5 = a"
    using a_cases e_cases by (elim disjE; simp add: crt_digit_def)
  show "crt_digit a e mod 2 = e"
    using a_cases e_cases by (elim disjE; simp add: crt_digit_def)
qed

lemma crt_digit_inverse:
  assumes "d < 10"
  shows "crt_digit (d mod 5) (d mod 2) = d"
proof -
  have d_cases: "d = 0 \<or> d = 1 \<or> d = 2 \<or> d = 3 \<or> d = 4 \<or>
      d = 5 \<or> d = 6 \<or> d = 7 \<or> d = 8 \<or> d = 9"
    using assms by (rule nat_less_ten_cases)
  show ?thesis using d_cases by (elim disjE; simp add: crt_digit_def)
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


text \<open>Native domain/F5/parity transducer. Carries are derived from the
one forward domain fold. A growth appends the CRT encoding of digit one before
reflection. These word semantics specify the rope gates; their proof does not
assert a bound on newly constructed rope nodes.\<close>

type_synonym native_cocycle = "carry_domain * nat * nat"

definition encode_cocycle :: "nat \<Rightarrow> native_cocycle" where
  "encode_cocycle s = (domain s, s mod 5, s mod 2)"

definition digit_channels :: "nat \<Rightarrow> nat * nat" where
  "digit_channels d = (d mod 5, d mod 2)"

fun native_emit :: "bool \<Rightarrow> native_cocycle list \<Rightarrow> (nat * nat) list" where
  "native_emit c [] = []"
| "native_emit c ((g,a,e)#xs) =
    ((a + (if c then 1 else 0)) mod 5,
     (e + (if c then 1 else 0)) mod 2) # native_emit (carry_apply g c) xs"

lemma native_emit_refines:
  "native_emit c (map encode_cocycle ss) = map digit_channels (emit c ss)"
  by (induction ss arbitrary: c)
    (simp_all add: encode_cocycle_def digit_channels_def
      mod_mod_cancel mod_add_left_eq)

definition native_growth :: "native_cocycle list \<Rightarrow> bool" where
  "native_growth xs = fold (\<lambda>(g,a,e) c. carry_apply g c) xs False"

lemma native_growth_refines:
  "native_growth (map encode_cocycle ss) = carry_out False ss"
  by (simp add: native_growth_def carry_out_def encode_cocycle_def fold_map comp_def)

definition native_digits :: "native_cocycle list \<Rightarrow> (nat * nat) list" where
  "native_digits xs = native_emit False xs @ (if native_growth xs then [(1,1)] else [])"

lemma native_digits_refines:
  "native_digits (map encode_cocycle ss) = map digit_channels (digits ss)"
  by (simp add: native_digits_def digits_def native_emit_refines
      native_growth_refines digit_channels_def)

definition native_add :: "(nat * nat) \<Rightarrow> (nat * nat) \<Rightarrow> native_cocycle" where
  "native_add x y =
    (cocycle_output_domain (crt_digit (fst x) (snd x)) (crt_digit (fst y) (snd y)),
     (fst x + fst y) mod 5, (snd x + snd y) mod 2)"

lemma native_add_refines:
  assumes "x < 10" "y < 10"
  shows "native_add (digit_channels x) (digit_channels y) = encode_cocycle (x+y)"
  using crt_digit_inverse[OF assms(1)] crt_digit_inverse[OF assms(2)]
    kappa_and_eq_domain_exact(2)[OF assms]
  by (simp add: native_add_def digit_channels_def encode_cocycle_def mod_add_eq)

definition native_step :: "native_cocycle list \<Rightarrow> native_cocycle list" where
  "native_step xs = map (\<lambda>(a,b). native_add a b)
    (zip (native_digits xs) (rev (native_digits xs)))"

theorem native_step_refines:
  "native_step (map encode_cocycle ss) = map encode_cocycle (step ss)"
proof -
  have add: "native_add (digit_channels a) (digit_channels b) = encode_cocycle (a+b)"
    if "(a,b) \<in> set (zip (digits ss) (rev (digits ss)))" for a b
    using that digits_bounded set_zip_leftD set_zip_rightD
    by (intro native_add_refines) fastforce+
  show ?thesis
    unfolding native_step_def step_def native_digits_refines rev_map zip_map_map map_map
    by (rule map_cong; auto simp: comp_def split: prod.splits; metis add)
qed

fun native_macro :: "nat \<Rightarrow> native_cocycle list \<Rightarrow> native_cocycle list" where
  "native_macro 0 xs = (native_step ^^ 4) xs"
| "native_macro (Suc level) xs = native_macro level (native_macro level xs)"

lemma native_iteration_refines:
  "(native_step ^^ n) (map encode_cocycle ss) = map encode_cocycle ((step ^^ n) ss)"
  by (induction n arbitrary: ss)
    (simp_all del: funpow.simps(2) add: funpow_Suc_right native_step_refines)

lemma native_terminal_emission_refines:
  "native_digits ((native_step ^^ n) (map encode_cocycle ss)) =
    map digit_channels (digits ((step ^^ n) ss))"
  by (simp add: native_iteration_refines native_digits_refines)

theorem native_macro_refines:
  "native_macro level (map encode_cocycle ss) =
    map encode_cocycle ((step ^^ (4*2^level)) ss)"
proof (induction level arbitrary: ss)
  case 0
  show ?case by (simp add: native_iteration_refines)
next
  case (Suc level)
  have double: "(4::nat)*2^(Suc level) = 4*2^level + 4*2^level"
    by (simp add: power_Suc algebra_simps)
  show ?case
    by (simp only: native_macro.simps Suc.IH double funpow_add comp_apply)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms crt_digit_coordinates_exact crt_digit_inverse
      parity_addition_coordinates parity_normalization_exact
      decimal_sum_digit_mod kappa_and_eq_domain_exact
      output_crt_threshold_exact normalized_output_crt_threshold_exact
      decimal_kappa_cocycle native_emit_refines native_growth_refines
      native_digits_refines native_add_refines native_step_refines
      native_iteration_refines native_terminal_emission_refines native_macro_refines}) then ()
    else error "Threshold cocycle proof depends on an oracle";
\<close>

end
