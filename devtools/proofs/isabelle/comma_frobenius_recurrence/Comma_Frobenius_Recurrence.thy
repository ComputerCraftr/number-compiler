theory Comma_Frobenius_Recurrence
  imports Comma_Arithmetic.Comma_Power_Residue
begin

text \<open>The temporal coordinate is derived from the proved modular-power
semantics.  Its recurrence includes the 924-clock wrap; no table of phase
transitions is a premise of these results.\<close>

definition comma_frobenius_power :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_frobenius_power P r = comma_power_residue P r div 10"

definition comma_frobenius_factor :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_frobenius_factor P D = 10 ^ D mod (P div 10)"

lemma comma_frobenius_period_decimal:
  assumes "P \<in> comma_cycle_displacements"
  shows "10 dvd P"
  using assms by (auto simp: comma_cycle_displacements_def)

lemma comma_power_residue_unwrapped:
  assumes catalog: "P \<in> comma_cycle_displacements"
  shows "comma_power_residue P r = 10 ^ (r + 924) mod P"
proof -
  let ?T = "comma_short_period P"
  let ?k = "r + 919"
  have split: "r + 924 = (5 + (?k mod ?T)) + ?T * (?k div ?T)"
    using mod_mult_div_eq[of ?k ?T] by arith
  have base: "mod_exp (10::nat) (5 + ?T) P = mod_exp 10 5 P"
    by (rule comma_short_period_base[OF catalog])
  have repeated:
    "10 ^ ((5 + (?k mod ?T)) + ?T * (?k div ?T)) mod P =
      (10::nat) ^ (5 + (?k mod ?T)) mod P"
    by (rule comma_short_period_repeated[OF base]) simp
  have reduced: "10 ^ (r + 924) mod P = (10::nat) ^ (5 + (?k mod ?T)) mod P"
  proof -
    have "10 ^ (r + 924) mod P =
      (10::nat) ^ ((5 + (?k mod ?T)) + ?T * (?k div ?T)) mod P"
      by (rule arg_cong[OF split])
    also have "... = (10::nat) ^ (5 + (?k mod ?T)) mod P"
      by (rule repeated)
    finally show ?thesis .
  qed
  have shift: "r + 924 - 5 = r + 919" by arith
  show ?thesis
    by (simp only: comma_power_residue_def mod_exp_def shift;
      rule reduced[symmetric])
qed

lemma comma_power_residue_phase:
  assumes catalog: "P \<in> comma_cycle_displacements"
  shows "comma_power_residue P (r mod 924) = comma_power_residue P r"
proof -
  have semantic: "comma_power_residue P ((r + 924) mod 924) =
    10 ^ (r + 924) mod P"
    by (rule comma_power_residue_correct[OF catalog]) simp
  show ?thesis
    using semantic comma_power_residue_unwrapped[OF catalog, of r] by simp
qed

lemma comma_power_residue_decimal_form:
  assumes catalog: "P \<in> comma_cycle_displacements"
  shows "comma_power_residue P r = 10 * (10 ^ (r + 923) mod (P div 10))"
proof -
  have period: "P = 10 * (P div 10)"
    using comma_frobenius_period_decimal[OF catalog]
    by (simp add: dvd_mult_div_cancel)
  have power: "(10::nat) ^ (r + 924) = 10 * 10 ^ (r + 923)"
  proof -
    have exponent: "r + 924 = Suc (r + 923)" by arith
    show ?thesis by (simp only: exponent power_Suc)
  qed
  have residue: "comma_power_residue P r = (10 * 10 ^ (r + 923)) mod P"
    by (simp only: comma_power_residue_unwrapped[OF catalog] power)
  also have "... = (10 * 10 ^ (r + 923)) mod (10 * (P div 10))"
    by (rule arg_cong[OF period])
  also have "... = 10 * (10 ^ (r + 923) mod (P div 10))"
    by (rule mod_mult_mult1)
  finally show ?thesis .
qed

lemma comma_frobenius_power_semantics:
  assumes catalog: "P \<in> comma_cycle_displacements"
  shows "comma_frobenius_power P r = 10 ^ (r + 923) mod (P div 10)"
  by (simp only: comma_frobenius_power_def
    comma_power_residue_decimal_form[OF catalog]; simp)

lemma comma_power_residue_divisible_10:
  assumes catalog: "P \<in> comma_cycle_displacements"
  shows "10 dvd comma_power_residue P r"
  by (simp only: comma_power_residue_decimal_form[OF catalog]; simp)

lemma comma_frobenius_power_phase:
  assumes "P \<in> comma_cycle_displacements"
  shows "comma_frobenius_power P (r mod 924) = comma_frobenius_power P r"
  by (simp only: comma_frobenius_power_def comma_power_residue_phase[OF assms])

lemma comma_frobenius_power_step:
  assumes catalog: "P \<in> comma_cycle_displacements"
  shows "comma_frobenius_power P ((r + 1) mod 924) =
    (10 * comma_frobenius_power P r) mod (P div 10)"
proof -
  have exponent: "r + 1 + 923 = Suc (r + 923)" by arith
  show ?thesis
    by (simp only: comma_frobenius_power_phase[OF catalog];
      simp only: comma_frobenius_power_semantics[OF catalog] exponent power_Suc
      mod_mult_right_eq)
qed

lemma comma_frobenius_power_iterate:
  assumes catalog: "P \<in> comma_cycle_displacements"
  shows "comma_frobenius_power P ((r + n) mod 924) =
    ((10 ^ n mod (P div 10)) * comma_frobenius_power P r) mod (P div 10)"
proof -
  have exponent: "r + n + 923 = n + (r + 923)" by arith
  have power: "(10::nat) ^ (r + n + 923) = 10 ^ n * 10 ^ (r + 923)"
  proof -
    have "(10::nat) ^ (r + n + 923) = 10 ^ (n + (r + 923))"
      by (rule arg_cong[OF exponent])
    also have "... = 10 ^ n * 10 ^ (r + 923)"
      by (rule power_add)
    finally show ?thesis .
  qed
  show ?thesis
    by (simp only: comma_frobenius_power_phase[OF catalog];
      simp only: comma_frobenius_power_semantics[OF catalog] power mod_mult_eq)
qed

lemma comma_power_residue_fixed_period:
  assumes "comma_short_period P = 1"
  shows "comma_power_residue P r = 100000 mod P"
  using assms by (simp add: comma_power_residue_def mod_exp_def)

lemma comma_frobenius_factor_compose:
  "comma_frobenius_factor P (D + E) =
    (comma_frobenius_factor P D * comma_frobenius_factor P E) mod (P div 10)"
  by (simp add: comma_frobenius_factor_def power_add mod_mult_eq)

lemma comma_frobenius_factor_square:
  "comma_frobenius_factor P (2 * D) =
    comma_frobenius_factor P D ^ 2 mod (P div 10)"
  using comma_frobenius_factor_compose[of P D D]
  by (simp add: power2_eq_square mult_2)

lemma comma_frobenius_block_action:
  assumes "P \<in> comma_cycle_displacements"
  shows "comma_frobenius_power P ((r + D) mod 924) =
    (comma_frobenius_factor P D * comma_frobenius_power P r) mod (P div 10)"
  using comma_frobenius_power_iterate[OF assms, of r D]
  by (simp only: comma_frobenius_factor_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_frobenius_period_decimal comma_power_residue_unwrapped comma_power_residue_phase
      comma_power_residue_decimal_form comma_frobenius_power_semantics
      comma_power_residue_divisible_10
      comma_frobenius_power_phase comma_frobenius_power_step
      comma_frobenius_power_iterate comma_power_residue_fixed_period
      comma_frobenius_factor_compose
      comma_frobenius_factor_square comma_frobenius_block_action})
    then () else error "Comma Frobenius recurrence depends on an oracle";
\<close>

end
