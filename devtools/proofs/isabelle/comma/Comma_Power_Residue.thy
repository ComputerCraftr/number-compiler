theory Comma_Power_Residue
  imports Comma_Arithmetic.Comma_Boundary_Quotient
begin

text \<open>Short executable periods for the admitted phase-cycle displacements.
This refines the existing 924-class quotient. It changes only the cost of
computing a modular power, not the admitted boundary semantics.\<close>

definition comma_short_period :: "nat \<Rightarrow> nat" where
  "comma_short_period P =
    (if P = 290 then 28
     else if P = 230 \<or> P = 460 then 22
     else if P = 140 \<or> P = 210 \<or> P = 260 \<or>
             P = 280 \<or> P = 520 then 6
     else if P = 270 \<or> P = 540 then 3
     else if P = 220 then 2
     else 1)"

definition comma_power_residue :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_power_residue P r =
    mod_exp (10::nat)
      (5 + ((r + 924 - 5) mod comma_short_period P)) P"

definition comma_residue_exponent :: "nat \<Rightarrow> nat" where
  "comma_residue_exponent r = (if r < 5 then r + 924 else r)"

lemma comma_short_period_catalog:
  assumes "P \<in> comma_cycle_displacements"
  shows "0 < comma_short_period P \<and>
    comma_short_period P \<le> 28 \<and>
    comma_short_period P dvd 924"
  using assms
  by (auto simp: comma_cycle_displacements_def comma_short_period_def)

lemma comma_short_period_base:
  assumes "P \<in> comma_cycle_displacements"
  shows "mod_exp (10::nat) (5 + comma_short_period P) P =
    mod_exp 10 5 P"
  using assms
  by (auto simp: comma_cycle_displacements_def comma_short_period_def)

lemma comma_short_period_increment:
  assumes base: "mod_exp (10::nat) (5 + T) P = mod_exp 10 5 P"
    and lower: "5 \<le> u"
  shows "10 ^ (u + T) mod P = (10::nat) ^ u mod P"
proof -
  have base_power: "(10::nat) ^ (5 + T) mod P = 10 ^ 5 mod P"
    using base by (simp only: mod_exp_def)
  obtain k where u: "u = 5 + k"
    using lower by (auto simp: le_iff_add)
  have left_power: "(10::nat) ^ (u + T) = 10 ^ (5 + T) * 10 ^ k"
    using u by (simp add: algebra_simps power_add)
  have right_power: "(10::nat) ^ u = 10 ^ 5 * 10 ^ k"
    using u by (simp only: power_add)
  have "10 ^ (u + T) mod P = (10 ^ (5 + T) * 10 ^ k) mod P"
    by (simp only: left_power)
  also have "... = ((10 ^ (5 + T) mod P) * 10 ^ k) mod P"
    by (rule mod_mult_left_eq[symmetric])
  also have "... = ((10 ^ 5 mod P) * 10 ^ k) mod P"
    using base_power by (simp only: base_power)
  also have "... = (10 ^ 5 * 10 ^ k) mod P"
    by (rule mod_mult_left_eq)
  also have "... = 10 ^ u mod P"
    by (simp only: right_power)
  finally show ?thesis .
qed

lemma comma_short_period_repeated:
  assumes base: "mod_exp (10::nat) (5 + T) P = mod_exp 10 5 P"
    and lower: "5 \<le> u"
  shows "10 ^ (u + T * t) mod P = (10::nat) ^ u mod P"
proof (induction t)
  case 0
  then show ?case by simp
next
  case (Suc t)
  have lower_at: "5 \<le> u + T * t"
    using lower by simp
  have at: "10 ^ ((u + T * t) + T) mod P =
      (10::nat) ^ (u + T * t) mod P"
    using comma_short_period_increment[OF base lower_at] .
  have "10 ^ (u + T * Suc t) mod P =
      (10::nat) ^ (u + T * t) mod P"
    using at by (simp add: algebra_simps)
  also have "... = (10::nat) ^ u mod P"
    using Suc.IH .
  finally show ?case .
qed

lemma comma_short_period_924_repeated:
  assumes catalog: "P \<in> comma_cycle_displacements"
    and lower: "5 \<le> u"
  shows "10 ^ (u + 924 * t) mod P = (10::nat) ^ u mod P"
proof -
  let ?T = "comma_short_period P"
  have divides: "?T dvd 924"
    using comma_short_period_catalog[OF catalog] by blast
  then obtain k where period: "924 = ?T * k"
    by (auto simp: dvd_def)
  have base: "mod_exp (10::nat) (5 + ?T) P = mod_exp 10 5 P"
    using comma_short_period_base[OF catalog] .
  have repeated: "10 ^ (u + ?T * (k * t)) mod P = (10::nat) ^ u mod P"
    using comma_short_period_repeated[OF base lower, of "k * t"] .
  have product: "924 * t = ?T * (k * t)"
  proof -
    have "924 * t = (?T * k) * t"
      using period by simp
    also have "... = ?T * (k * t)"
      by (simp only: mult.assoc)
    finally show ?thesis .
  qed
  have "10 ^ (u + 924 * t) mod P = 10 ^ (u + ?T * (k * t)) mod P"
    by (simp only: product)
  also have "... = (10::nat) ^ u mod P"
    by (rule repeated)
  finally show ?thesis .
qed

lemma comma_power_period_924:
  assumes catalog: "P \<in> comma_cycle_displacements"
    and lower: "p \<ge> 5"
  shows "10 ^ (p + 924) mod P = 10 ^ p mod P"
  using comma_short_period_924_repeated[OF catalog lower, of 1] by simp

lemma comma_short_representative_decomposition:
  assumes lower: "5 \<le> p"
  shows "\<exists>t. p = comma_residue_exponent (p mod 924) + 924 * t"
proof -
  let ?r = "p mod 924"
  let ?q = "p div 924"
  have split: "p = ?r + 924 * ?q"
    by (simp add: mod_mult_div_eq)
  show ?thesis
  proof (cases "?r < 5")
    case True
    have nonzero: "?q \<noteq> 0"
      using lower split True by arith
    then obtain t where q: "?q = Suc t"
      by (cases ?q) auto
    show ?thesis
      using split True q
      by (intro exI[of _ t])
        (simp add: comma_residue_exponent_def algebra_simps)
  next
    case False
    show ?thesis
      using split False
      by (intro exI[of _ ?q])
        (simp add: comma_residue_exponent_def algebra_simps)
  qed
qed

lemma comma_short_representative_correct:
  assumes catalog: "P \<in> comma_cycle_displacements"
    and lower: "5 \<le> p"
  shows "10 ^ p mod P =
    (10::nat) ^ comma_residue_exponent (p mod 924) mod P"
proof -
  obtain t where p:
    "p = comma_residue_exponent (p mod 924) + 924 * t"
    using comma_short_representative_decomposition[OF lower] by blast
  have rep_lower: "5 \<le> comma_residue_exponent (p mod 924)"
    by (simp add: comma_residue_exponent_def)
  show ?thesis
    using comma_short_period_924_repeated[OF catalog rep_lower, of t]
      p by simp
qed

lemma comma_short_residue_exponent:
  assumes residue: "r < 924"
    and divides: "T dvd 924"
  shows "(comma_residue_exponent r - 5) mod T =
    (r + 924 - 5) mod T"
proof (cases "r < 5")
  case True
  then show ?thesis
    by (simp add: comma_residue_exponent_def)
next
  case False
  have arithmetic: "r + 924 - 5 = (r - 5) + 924"
    using False by arith
  have residue_zero: "924 mod T = 0"
    using divides by simp
  have periodic: "((r - 5) + 924) mod T = (r - 5) mod T"
  proof -
    have "((r - 5) + 924) mod T = ((r - 5) + 924 mod T) mod T"
      by (rule mod_add_right_eq[symmetric])
    also have "... = (r - 5) mod T"
      using residue_zero by simp
    finally show ?thesis .
  qed
  show ?thesis
    using False periodic
    by (simp only: comma_residue_exponent_def if_False arithmetic)
qed

lemma comma_power_residue_small:
  assumes "P \<in> comma_cycle_displacements"
  shows "5 + ((r + 924 - 5) mod comma_short_period P) \<le> 32"
proof -
  have bounds: "0 < comma_short_period P \<and>
    comma_short_period P \<le> 28"
    using comma_short_period_catalog[OF assms] by blast
  have rem: "(r + 924 - 5) mod comma_short_period P <
    comma_short_period P"
    using bounds by simp
  show ?thesis using bounds rem by arith
qed

lemma comma_power_residue_correct:
  assumes catalog: "P \<in> comma_cycle_displacements"
    and lower: "5 \<le> p"
  shows "comma_power_residue P (p mod 924) = 10 ^ p mod P"
proof -
  let ?r = "p mod 924"
  let ?T = "comma_short_period P"
  let ?b = "comma_residue_exponent ?r"
  let ?k = "?b - 5"
  have period: "0 < ?T \<and> ?T dvd 924"
    using comma_short_period_catalog[OF catalog] by blast
  have base: "mod_exp (10::nat) (5 + ?T) P = mod_exp 10 5 P"
    using comma_short_period_base[OF catalog] .
  have b_ge: "5 \<le> ?b"
    by (simp add: comma_residue_exponent_def)
  have split: "?b = (5 + (?k mod ?T)) + ?T * (?k div ?T)"
    using b_ge by (simp add: mod_mult_div_eq algebra_simps)
  have reduced_power:
    "10 ^ ((5 + (?k mod ?T)) + ?T * (?k div ?T)) mod P =
      (10::nat) ^ (5 + (?k mod ?T)) mod P"
    using comma_short_period_repeated[OF base, of
      "5 + (?k mod ?T)" "?k div ?T"] by simp
  have reduce: "10 ^ ?b mod P = (10::nat) ^ (5 + (?k mod ?T)) mod P"
    using reduced_power split by simp
  have original: "10 ^ p mod P = (10::nat) ^ ?b mod P"
    using comma_short_representative_correct[OF catalog lower] .
  have r_lt: "?r < 924"
    by simp
  have reduced_exponent:
    "?k mod ?T = (?r + 924 - 5) mod ?T"
    using comma_short_residue_exponent[OF r_lt] period by blast
  show ?thesis
    using original reduce reduced_exponent
    by (simp add: comma_power_residue_def mod_exp_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms comma_short_period_catalog
    comma_short_period_base comma_short_period_increment
    comma_short_period_repeated comma_short_period_924_repeated
    comma_power_period_924
    comma_short_representative_decomposition
    comma_short_representative_correct comma_short_residue_exponent
    comma_power_residue_small comma_power_residue_correct})
  then () else error "comma power residue proof used an oracle"
\<close>

end
