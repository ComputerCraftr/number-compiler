theory Cylinder_Live_Forcing_Reduction
  imports Cylinder_Centered_Clock
begin

text \<open>
  Executable coefficient-level facts used by the bounded live-forcing
  normalizer.  Congruence is pointwise modulo 2^bits.  The arithmetic below
  does not establish the runtime certificate that limits a growth run to
  three; that fact is an explicit premise where it is used.
\<close>

definition live_modulus :: "nat \<Rightarrow> int" where
  "live_modulus bits = 2^bits"

definition live_coefficient_normalize ::
    "nat \<Rightarrow> coefficient_function \<Rightarrow> coefficient_function" where
  "live_coefficient_normalize bits f i = f i mod live_modulus bits"

definition live_modular_equal ::
    "nat \<Rightarrow> coefficient_function \<Rightarrow> coefficient_function \<Rightarrow> bool" where
  "live_modular_equal bits f g \<longleftrightarrow>
    (\<forall>i. f i mod live_modulus bits = g i mod live_modulus bits)"

definition live_radial_scale ::
    "nat \<Rightarrow> coefficient_function \<Rightarrow> coefficient_function" where
  "live_radial_scale q f i = 2^q * f i"

lemma live_normalize_modular_equal:
  "live_modular_equal bits (live_coefficient_normalize bits f) f"
  by (simp add: live_modular_equal_def live_coefficient_normalize_def
      live_modulus_def mod_mod_trivial)

lemma live_normalize_idempotent:
  "live_coefficient_normalize bits (live_coefficient_normalize bits f) =
    live_coefficient_normalize bits f"
  by (rule ext)
     (simp add: live_coefficient_normalize_def live_modulus_def)

lemma live_radial_scale_pruned:
  assumes "bits \<le> q"
  shows "live_coefficient_normalize bits (live_radial_scale q f) = (\<lambda>i. 0)"
proof (rule ext)
  fix i
  obtain extra where q: "q = bits + extra"
    using assms by (auto simp: le_iff_add)
  show "live_coefficient_normalize bits (live_radial_scale q f) i = 0"
    unfolding live_coefficient_normalize_def live_radial_scale_def live_modulus_def
    by (simp add: q power_add algebra_simps)
qed

lemma live_modular_equal_add:
  assumes "live_modular_equal bits f f'"
      and "live_modular_equal bits g g'"
  shows "live_modular_equal bits (innovation_add f g) (innovation_add f' g')"
proof (unfold live_modular_equal_def innovation_add_def, intro allI)
  fix i
  have f_residue: "f i mod live_modulus bits = f' i mod live_modulus bits"
    using assms(1) by (simp add: live_modular_equal_def)
  have g_residue: "g i mod live_modulus bits = g' i mod live_modulus bits"
    using assms(2) by (simp add: live_modular_equal_def)
  have "(f i + g i) mod live_modulus bits =
      (f i mod live_modulus bits + g i mod live_modulus bits) mod live_modulus bits"
    by (rule mod_add_eq[symmetric])
  also have "... =
      (f' i mod live_modulus bits + g' i mod live_modulus bits) mod live_modulus bits"
    by (simp only: f_residue g_residue)
  also have "... = (f' i + g' i) mod live_modulus bits"
    by (rule mod_add_eq)
  finally show "(f i + g i) mod live_modulus bits =
      (f' i + g' i) mod live_modulus bits" .
qed

lemma live_modular_equal_scale:
  assumes "live_modular_equal bits f g"
  shows "live_modular_equal bits (\<lambda>i. c * f i) (\<lambda>i. c * g i)"
proof (unfold live_modular_equal_def, intro allI)
  fix i
  have residue: "f i mod live_modulus bits = g i mod live_modulus bits"
    using assms by (simp add: live_modular_equal_def)
  show "c * f i mod live_modulus bits = c * g i mod live_modulus bits"
  proof -
    have "(c * f i) mod live_modulus bits =
        (c mod live_modulus bits * (f i mod live_modulus bits))
          mod live_modulus bits"
      by (rule mod_mult_eq[symmetric])
    also have "... =
        (c mod live_modulus bits * (g i mod live_modulus bits))
          mod live_modulus bits"
      by (simp only: residue)
    also have "... = (c * g i) mod live_modulus bits"
      by (rule mod_mult_eq)
    finally show ?thesis .
  qed
qed

lemma live_modular_equal_reflect:
  assumes "live_modular_equal bits f g"
  shows "live_modular_equal bits
    (innovation_reflect d f) (innovation_reflect d g)"
proof (unfold live_modular_equal_def, intro allI)
  fix i
  have residue:
    "f (d-i) mod live_modulus bits = g (d-i) mod live_modulus bits"
    using assms by (simp add: live_modular_equal_def)
  show "innovation_reflect d f i mod live_modulus bits =
      innovation_reflect d g i mod live_modulus bits"
    using residue by (simp only: innovation_reflect_def)
qed

lemma live_modular_equal_radial_scale:
  assumes "live_modular_equal bits f g"
  shows "live_modular_equal bits
    (live_radial_scale q f) (live_radial_scale q g)"
  using live_modular_equal_scale[OF assms, of "2^q"]
  by (simp add: live_modular_equal_def live_radial_scale_def)

lemma live_exponent_bounds:
  fixes q r bits :: nat
  assumes live: "q < bits" and radial: "r \<le> 3 * (q+1)"
  shows "q + r < 4 * bits" and "r \<le> 3 * bits"
proof -
  have successor_bound: "q + 1 \<le> bits" using live by simp
  show "q + r < 4 * bits" using live radial successor_bound by arith
  show "r \<le> 3 * bits" using radial successor_bound by arith
qed

theorem live_growth_certificate_bounds:
  fixes q r bits growth_run :: nat
  assumes live: "q < bits"
      and certified_run: "growth_run \<le> 3"
      and radial: "r \<le> growth_run * (q+1)"
  shows "q + r < 4 * bits" and "r \<le> 3 * bits"
proof -
  have scaled_run: "growth_run * (q+1) \<le> 3 * (q+1)"
    using mult_le_mono[OF certified_run order_refl] .
  have radial_bound: "r \<le> 3 * (q+1)"
    using radial scaled_run by (rule order_trans)
  then show "q + r < 4 * bits" "r \<le> 3 * bits"
    using live_exponent_bounds[OF live] by blast+
qed

lemma decimal_live_age_bounds:
  fixes q r :: nat
  assumes "q \<le> 4" and "r \<le> 15"
  shows "q + r \<le> 19"
  using assms by arith

definition live_pair_residue :: "nat \<Rightarrow> int" where
  "live_pair_residue pair = int pair mod 32"

definition live_centered_delta :: "int \<Rightarrow> int" where
  "live_centered_delta residue = residue - 9"

lemma live_pair_residue_exact:
  assumes "pair \<le> 18"
  shows "live_pair_residue pair = int pair"
  using assms by (simp add: live_pair_residue_def)

theorem live_centered_sign_from_residue:
  assumes pair: "pair \<le> 18"
  shows "live_centered_delta (live_pair_residue pair) = int pair - 9"
    and "live_centered_delta (live_pair_residue pair) < 0 \<longleftrightarrow> pair < 9"
    and "live_centered_delta (live_pair_residue pair) = 0 \<longleftrightarrow> pair = 9"
    and "0 < live_centered_delta (live_pair_residue pair) \<longleftrightarrow> 9 < pair"
  using live_pair_residue_exact[OF pair]
  by (simp_all add: live_centered_delta_def)

definition live_local_carry_update :: "int \<Rightarrow> int \<Rightarrow> int" where
  "live_local_carry_update residue carry =
    centered_carry_step (live_centered_delta residue) carry"

lemma live_local_carry_from_pair:
  assumes "pair \<le> 18"
  shows "live_local_carry_update (live_pair_residue pair) carry =
    centered_carry_step (int pair - 9) carry"
  using live_pair_residue_exact[OF assms]
  by (simp add: live_local_carry_update_def live_centered_delta_def)

lemma live_reflected_local_carry:
  "live_local_carry_update
      (live_pair_residue pair) (innovation_reflect d carry i) =
    centered_carry_step
      (live_centered_delta (live_pair_residue pair)) (carry (d-i))"
  by (simp add: live_local_carry_update_def innovation_reflect_def)

lemma live_local_carry_range:
  assumes "carry = 0 \<or> carry = 1"
  shows "live_local_carry_update residue carry = 0 \<or>
    live_local_carry_update residue carry = 1"
  using centered_carry_step_range[OF assms]
  by (simp add: live_local_carry_update_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms live_radial_scale_pruned live_modular_equal_add
        live_modular_equal_scale live_modular_equal_reflect
        live_modular_equal_radial_scale live_exponent_bounds
        live_growth_certificate_bounds decimal_live_age_bounds
        live_pair_residue_exact live_centered_sign_from_residue
        live_local_carry_from_pair live_reflected_local_carry})
    then () else error "Live forcing reduction depends on an oracle";
\<close>

end
