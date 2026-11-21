theory Collatz_Centered_Carry_Signal
  imports Collatz_Edge_Digit_Cycle_Refinement
begin

text \<open>For a receiving source with exact dyadic headroom h, the scaled
physical endpoint has correction -2^t. At every admitted tick t, adding
its lower bits increments the multiplication carry precisely at the cuts
above h. The emitted numerator uses the moving correction.\<close>

theorem collatz_centered_carry_correction:
  fixes center gain h cut tick :: nat
  assumes headroom: "2^h dvd center" "\<not> 2^(Suc h) dvd center"
    and tick: "tick \<le> h"
    and unit: "odd gain"
  shows "(gain * (center mod 2^cut) + (2^cut - 2^tick)) div 2^cut =
    (gain * (center mod 2^cut)) div 2^cut + (if h < cut then 1 else 0)"
proof (cases "h < cut")
  case False
  have order: "cut \<le> h" using False by simp
  have "2^cut dvd center"
    by (rule dvd_trans[OF dvd_power_le[OF dvd_refl order] headroom(1)])
  then have zero: "center mod 2^cut = 0" by simp
  have "2^cut - (2::nat)^tick < 2^cut" by simp
  then show ?thesis using False zero by simp
next
  case True
  let ?m = "(2::nat)^cut"
  let ?a = "gain * (center mod ?m)"
  let ?r = "?a mod ?m"
  let ?b = "?m - (2::nat)^tick"
  have h_div: "2^h dvd ?m"
    by (rule dvd_power_le[OF dvd_refl]) (use True in simp)
  have next_div: "2^(Suc h) dvd ?m"
    by (rule dvd_power_le[OF dvd_refl]) (use True in simp)
  have center_low: "2^h dvd center mod ?m"
    by (rule dvd_mod[OF headroom(1) h_div])
  have carry_low: "2^h dvd ?r"
    by (rule dvd_mod[OF _ h_div]) (use center_low in simp)
  have "coprime (2::nat) gain" using unit by simp
  then have unit_power: "coprime (2^(Suc h)) gain" by simp
  have r_nonzero: "?r \<noteq> 0"
  proof
    assume zero: "?r = 0"
    have "?m dvd ?a" by (rule dvd_eq_mod_eq_0[THEN iffD2, OF zero])
    then have "2^(Suc h) dvd ?a" by (rule dvd_trans[OF next_div])
    then have "2^(Suc h) dvd center mod ?m"
      using coprime_dvd_mult_left_iff[OF unit_power, of "center mod ?m"]
      by (simp add: mult.commute)
    then show False using headroom(2) dvd_mod_iff[OF next_div, of center] by blast
  qed
  have lower: "(2::nat)^tick \<le> ?r"
    by (rule order_trans[OF power_increasing[OF tick] dvd_imp_le[OF carry_low]])
       (use r_nonzero in simp_all)
  have bias: "?b < ?m" by simp
  have r_upper: "?r < ?m" by simp
  have tick_power: "(2::nat)^tick \<le> ?m"
    using tick True by (intro power_increasing) simp_all
  have span: "?m \<le> ?r + ?b" using lower tick_power by arith
  have small: "?r + ?b < 2 * ?m" using r_upper bias by arith
  have below: "(?r + ?b) div ?m < 2"
    using small by (simp add: div_less_iff_less_mult mult.commute)
  have positive_modulus: "0 < ?m" by simp
  have reaches: "(?r + ?b) div ?m < 1 \<longleftrightarrow> ?r + ?b < 1 * ?m"
    by (rule div_less_iff_less_mult[OF positive_modulus])
  have above: "\<not> (?r + ?b) div ?m < 1"
    using reaches span by (simp only: mult_1_left not_less)
  have carry_one: "(?r + ?b) div ?m = 1" using above below by arith
  have "(?a + ?b) div ?m = ?a div ?m + ?b div ?m +
      ((?a mod ?m + ?b mod ?m) div ?m)"
    by (rule div_add1_eq)
  also have "\<dots> = ?a div ?m + 1" using bias carry_one by simp
  finally show ?thesis using True by simp
qed

theorem collatz_carry_cut_multiplier_reduction:
  fixes gain low cut width :: nat
  assumes bound: "cut < width"
  shows "(((gain mod 2^width) * low) div 2^cut) mod 2 =
    ((gain * low) div 2^cut) mod 2"
proof -
  let ?p = "(2::nat)^cut"
  let ?a = "gain mod 2^width * low"
  let ?b = "gain * low"
  have "2^(Suc cut) dvd (2::nat)^width"
    by (rule dvd_power_le[OF dvd_refl]) (use bound in simp)
  then have mod_div: "?p * 2 dvd (2::nat)^width"
    by (simp only: power_Suc mult.commute)
  have phase: "(gain mod 2^width) mod (?p*2) = gain mod (?p*2)"
    by (rule mod_mod_cancel[OF mod_div])
  have equal: "?a mod (?p*2) = ?b mod (?p*2)"
    by (rule mod_mult_cong[OF phase refl])
  have project: "\<And>v::nat. (v mod (?p*2)) div ?p = (v div ?p) mod 2"
  proof -
    fix v :: nat
    have split: "v mod (?p*2) = ?p * (v div ?p mod 2) + v mod ?p"
      by (rule mod_mult2_eq)
    have nonzero: "?p \<noteq> 0" by simp
    have "(v mod (?p*2)) div ?p = (v div ?p mod 2) + (v mod ?p) div ?p"
      unfolding split by (rule div_mult_self4[OF nonzero])
    then show "(v mod (?p*2)) div ?p = (v div ?p) mod 2" by simp
  qed
  show ?thesis using arg_cong[OF equal, of "\<lambda>v. v div ?p"]
    by (simp only: project)
qed

theorem collatz_centered_numerator_physical:
  fixes x tick h :: nat
  assumes headroom: "2^h dvd x+1" and tick: "tick \<le> h"
  shows "(2::nat)^tick * (physical_collatz ^^ (2*tick)) x =
    3^tick * (x+1) - 2^tick"
proof -
  have admitted_div: "2^tick dvd x+1"
    by (rule dvd_trans[OF dvd_power_le[OF dvd_refl tick] headroom])
  note exact = collatz_true_run_endpoint_exact[OF admitted_div]
  have admitted:
    "collatz_guarded_normalized_word_admitted (replicate tick True) x"
    using exact by blast
  have physical:
    "collatz_guarded_normalized_word_endpoint (replicate tick True) x =
      (physical_collatz ^^ (2*tick)) x"
    using collatz_guarded_normalized_word_refines_physical[OF admitted]
    by (simp add: count_list_replicate mult_2)
  have endpoint: "(physical_collatz ^^ (2*tick)) x + 1 =
    3^tick * ((x+1) div 2^tick)"
    using exact[THEN conjunct2] by (simp only: physical)
  have split: "(2::nat)^tick * ((x+1) div 2^tick) = x+1"
    using admitted_div by simp
  have "(2::nat)^tick * ((physical_collatz ^^ (2*tick)) x + 1) =
      2^tick * (3^tick * ((x+1) div 2^tick))"
    by (simp only: endpoint)
  also have "\<dots> = 3^tick * (2^tick * ((x+1) div 2^tick))"
    by (rule mult.left_commute)
  also have "\<dots> = 3^tick * (x+1)" by (simp only: split)
  finally have scaled: "(2::nat)^tick * ((physical_collatz ^^ (2*tick)) x + 1) =
      3^tick * (x+1)" .
  show ?thesis using scaled by (simp only: distrib_left mult_1_right)
qed

lemma collatz_pending_odd_input_has_even_output:
  assumes "odd x"
  shows "even (physical_collatz x)"
  using assms by (simp add: physical_collatz_def)

ML \<open>
  val checked = @{thms collatz_centered_carry_correction
    collatz_carry_cut_multiplier_reduction collatz_centered_numerator_physical
    collatz_pending_odd_input_has_even_output};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Collatz corrected carry signal depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Collatz corrected carry signal proof" else ();
\<close>

end
