theory Comma_Native19_Carry
  imports Shared_Carry_Dynamics.Shared_Decimal_Cocycle_Core
begin

text \<open>
The Native19 word is the existing decimal domain/F5/F2 cocycle, restricted
to coefficients 0 through 18.  Its decoder chooses the unique CRT residue
below 9, at 9, or above 9 according to the existing three-state domain.
The finite bound is proved by modular arithmetic; no coefficient table is
part of the carrier.
\<close>

definition comma_native19_decode :: "native_cocycle \<Rightarrow> nat" where
  "comma_native19_decode x = (case x of
    (Below,a,e) \<Rightarrow> crt_digit a e
  | (Equal,a,e) \<Rightarrow> 9
  | (Above,a,e) \<Rightarrow> 10 + crt_digit a e)"

definition comma_native19_admitted :: "native_cocycle \<Rightarrow> bool" where
  "comma_native19_admitted x \<longleftrightarrow>
    (\<exists>s. s \<le> 18 \<and> encode_cocycle s = x)"

lemma comma_native19_decode_encode:
  assumes "s \<le> 18"
  shows "comma_native19_decode (encode_cocycle s) = s"
proof -
  show ?thesis
  proof (cases "s < 9")
    case True
    have crt: "crt_digit (s mod 5) (s mod 2) = s"
      by (rule crt_digit_inverse) (use True in arith)
    have dom: "domain s = Below"
      using True by (simp add: domain_def)
    show ?thesis using crt dom
      by (simp add: comma_native19_decode_def encode_cocycle_def)
  next
    case False
    then have lower: "9 \<le> s" by simp
    show ?thesis
    proof (cases "s = 9")
      case True
      then show ?thesis
        by (simp add: comma_native19_decode_def encode_cocycle_def domain_def)
    next
      case False
      with lower have above: "9 < s" by arith
      have t_bound: "s - 10 < 10" using assms above by arith
      have shifted: "s = (s - 10) + 10" using above by arith
      have crt: "crt_digit ((s - 10) mod 5) ((s - 10) mod 2) = s - 10"
        by (rule crt_digit_inverse[OF t_bound])
      have dom: "domain s = Above"
        using above by (simp add: domain_def)
      have shift5: "((s-10)+10) mod 5=(s-10) mod 5"
        by (subst mod_add_eq[symmetric]; simp)
      have shift2: "((s-10)+10) mod 2=(s-10) mod 2"
        by (subst mod_add_eq[symmetric]; simp)
      have residue5: "s mod 5=(s-10) mod 5"
        using arg_cong[OF shifted, of "\<lambda>n. n mod 5"] shift5 by metis
      have residue2: "s mod 2=(s-10) mod 2"
        using arg_cong[OF shifted, of "\<lambda>n. n mod 2"] shift2 by metis
      show ?thesis using above
        by (simp add: comma_native19_decode_def encode_cocycle_def
          dom residue5 residue2 crt; arith)
    qed
  qed
qed

lemma comma_native19_encode_admitted:
  assumes "s \<le> 18"
  shows "comma_native19_admitted (encode_cocycle s)"
  using assms by (auto simp: comma_native19_admitted_def)

lemma comma_native19_range:
  assumes "comma_native19_admitted x"
  shows "comma_native19_decode x \<le> 18"
proof -
  obtain s where bound: "s \<le> 18" and encoded: "encode_cocycle s = x"
    using assms unfolding comma_native19_admitted_def by blast
  show ?thesis using comma_native19_decode_encode[OF bound] encoded bound by simp
qed

lemma comma_native19_encode_decode:
  assumes "comma_native19_admitted x"
  shows "encode_cocycle (comma_native19_decode x) = x"
proof -
  obtain s where bound: "s \<le> 18" and encoded: "encode_cocycle s = x"
    using assms unfolding comma_native19_admitted_def by blast
  have decoded: "comma_native19_decode x = s"
    using comma_native19_decode_encode[OF bound] encoded by simp
  show ?thesis using encoded decoded by simp
qed

lemma comma_native19_encode_injective:
  assumes "s \<le> 18" "t \<le> 18"
      and "encode_cocycle s = encode_cocycle t"
  shows "s = t"
  using comma_native19_decode_encode[OF assms(1)]
    comma_native19_decode_encode[OF assms(2)] assms(3) by metis

text \<open>
The radix-five coordinate \<open>alpha\<close> and binary quotient \<open>beta\<close>
jointly encode the decimal value \<open>alpha + 5 * beta\<close>.  Native19 stores
the value's ordinary parity alongside its radix-five residue; the conversion
below reuses the shared decimal split laws and encoder.
\<close>

lemma comma_binary_quinary_to_native19:
  assumes "alpha < 5" "beta < 2"
  shows "digit_value alpha beta < 10"
    "digit_value alpha beta mod 5 = alpha"
    "digit_value alpha beta mod 2 = (alpha + beta) mod 2"
    "encode_cocycle (digit_value alpha beta) =
      (domain (digit_value alpha beta), alpha,
        (alpha + beta) mod 2)"
proof -
  show "digit_value alpha beta < 10"
    using assms by (simp add: decimal_binary_quinary_value; arith)
  have mod5: "digit_value alpha beta mod 5 = alpha"
    using assms(1) by (simp add: decimal_binary_quinary_value)
  then show "digit_value alpha beta mod 5 = alpha" .
  have beta_mod: "(5 * beta) mod 2 = beta mod 2"
    by (subst mod_mult_left_eq[symmetric]; simp)
  have mod2: "digit_value alpha beta mod 2 = (alpha + beta) mod 2"
    unfolding decimal_binary_quinary_value
    by (rule mod_add_cong[OF refl beta_mod])
  then show "digit_value alpha beta mod 2 = (alpha + beta) mod 2" .
  show "encode_cocycle (digit_value alpha beta) =
      (domain (digit_value alpha beta), alpha,
        (alpha + beta) mod 2)"
    using mod5 mod2 by (simp add: encode_cocycle_def)
qed

text \<open>
This polarity distinction is used by the comma reset-germ observer.  It is
kept at the family boundary because the richer comma state observes the
polarity even though the shared Boolean carry action also has generic laws.
\<close>

lemma comma_reset_polarities_distinct:
  "carry_apply Below False \<noteq> carry_apply Above False"
  by simp

lemma comma_native19_to_binary_quinary:
  assumes "q < 10"
  shows "digit_value (q mod 5) (q div 5) = q"
    "q div 5 < 2"
    "crt_digit (q mod 5) (q mod 2) = q"
proof -
  show "digit_value (q mod 5) (q div 5) = q"
    unfolding digit_value_def
    using div_mult_mod_eq[of q 5] by arith
  show "q div 5 < 2" using assms by (simp add: div_less_iff_less_mult)
  show "crt_digit (q mod 5) (q mod 2) = q"
    by (rule crt_digit_inverse[OF assms])
qed

lemma comma_native19_binary_quinary_parity:
  assumes "alpha < 5" "beta < 2"
  shows "crt_digit alpha ((alpha + beta) mod 2) =
    digit_value alpha beta"
proof -
  have q_bound: "digit_value alpha beta < 10"
    by (rule comma_binary_quinary_to_native19(1)[OF assms])
  have alpha_residue: "digit_value alpha beta mod 5 = alpha"
    by (rule comma_binary_quinary_to_native19(2)[OF assms])
  have parity_residue:
    "digit_value alpha beta mod 2 = (alpha + beta) mod 2"
    by (rule comma_binary_quinary_to_native19(3)[OF assms])
  show ?thesis
    using crt_digit_inverse[OF q_bound] alpha_residue parity_residue by simp
qed

text \<open>
The full-adder's high-half bit stays available to the Boolean gate, while
the emitted Native19 word carries its parity.  These coordinate equations
are derived from the existing exact full-adder identities, rather than from
a second proof of their finite gate cases.
\<close>

lemma comma_native19_full_adder_coordinates:
  assumes "a1 < 5" "a2 < 5" "b1 < 2" "b2 < 2"
  defines "s \<equiv> digit_value a1 b1 + digit_value a2 b2"
  shows "encode_cocycle s =
    (add_domain a1 b1 a2 b2, add_alpha a1 a2,
      (add_alpha a1 a2 + add_beta a1 b1 a2 b2) mod 2)"
proof -
  let ?alpha = "add_alpha a1 a2"
  let ?beta = "add_beta a1 b1 a2 b2"
  let ?high = "add_high a1 b1 a2 b2"
  have gate: "?alpha + 5 * ?beta + 10 * ?high = s"
    using assms(1-4) unfolding s_def by (rule full_adder_gate_exact)
  have domain: "domain s = add_domain a1 b1 a2 b2"
    using assms(1-4) unfolding s_def
    by (rule full_adder_domain_exact[symmetric])
  have alpha_bound: "?alpha<5" by (simp add: add_alpha_def)
  have beta_mod: "(5 * ?beta) mod 2 = ?beta mod 2"
    by (subst mod_mult_left_eq[symmetric]; simp)
  have pair_mod2: "(?alpha + 5 * ?beta) mod 2 = (?alpha + ?beta) mod 2"
    by (rule mod_add_cong[OF refl beta_mod])
  have high5: "(10 * ?high) mod 5 = 0"
    by (subst mod_mult_left_eq[symmetric]; simp)
  have high2: "(10 * ?high) mod 2 = 0"
    by (subst mod_mult_left_eq[symmetric]; simp)
  have mod5: "s mod 5 = ?alpha"
    unfolding gate[symmetric]
    by (subst mod_add_eq[symmetric]; simp add: high5 alpha_bound)
  have mod2: "s mod 2 = (?alpha + ?beta) mod 2"
    unfolding gate[symmetric]
    by (subst mod_add_eq[symmetric]; simp add: high2 pair_mod2)
  show ?thesis
    using domain mod5 mod2 by (simp add: encode_cocycle_def)
qed

ML \<open>
  val checked = @{thms comma_native19_decode_encode
    comma_native19_encode_admitted comma_native19_range
    comma_native19_encode_decode comma_native19_encode_injective
    comma_binary_quinary_to_native19 comma_native19_to_binary_quinary
    comma_native19_binary_quinary_parity
    comma_reset_polarities_distinct
    comma_native19_full_adder_coordinates};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Native19 carry proof depends on an oracle";
\<close>

end
