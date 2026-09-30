theory Comma_Frobenius_Entry
  imports Comma_Fast_Control.Comma_Sector_Alphabet
begin

text \<open>The first coordinate reduction is exact signed arithmetic.  It
removes the independent quotient and short residue_value from Entry headroom.  The
digit remains a coordinate here: erasing it requires an additional orbit
conjugacy theorem, and does not follow from this diagonal theorem.\<close>

definition comma_entry_diagonal ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_entry_diagonal P x residue_value =
    nat ((int (x div 10) - int (residue_value div 10)) mod int (P div 10))"

definition comma_diagonal_headroom ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_diagonal_headroom f P d eta =
    (let b=1+(if f<9 then 1 else 0)
     in b + nat ((-10 * int eta - (int d + int b)) mod int P))"

definition comma_entry_diagonal_endpoint ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_entry_diagonal_endpoint f P d eta =
    snd (comma_near_closed_germ f (comma_diagonal_headroom f P d eta))"

lemma comma_signed_diagonal_remainder:
  fixes a d b :: int
  shows "(-10*a-(d+b)) mod (10*M) =
    (-10*(a mod M)-(d+b)) mod (10*M)"
proof -
  have quotient: "a = M*(a div M) + a mod M"
    using div_mult_mod_eq[of a M] by (simp add: mult.commute)
  have difference:
    "(-10*a-(d+b))-(-10*(a mod M)-(d+b)) =
      (10*M)*(-(a div M))"
    using quotient by (simp add: algebra_simps; linarith)
  show ?thesis
    by (simp only: mod_eq_dvd_iff difference; simp)
qed

lemma comma_entry_diagonal_bound:
  assumes "0<P div 10"
  shows "comma_entry_diagonal P x residue_value < P div 10"
  using assms
  by (simp add: comma_entry_diagonal_def nat_less_iff)

lemma comma_entry_headroom_diagonal:
  assumes period: "0<P" "10 dvd P" and residue_value: "10 dvd residue_value"
  shows "1+(if f<9 then 1 else 0) +
      nat ((int residue_value-int x-int (1+(if f<9 then 1 else 0))) mod int P) =
    comma_diagonal_headroom f P (x mod 10)
      (comma_entry_diagonal P x residue_value)"
proof -
  let ?M = "P div 10"
  let ?a = "int (x div 10)-int (residue_value div 10)"
  let ?b = "1+(if f<9 then 1 else 0)"
  have P: "P=10*?M" using period(2) by (simp add: dvd_mult_div_cancel)
  have modulus: "int P=10*int ?M"
    using arg_cong[OF P, of int]
    by (simp only: of_nat_mult of_nat_numeral)
  have positive: "0<int ?M" using period(1) P by simp
  have pow: "residue_value=10*(residue_value div 10)"
    using residue_value by (simp add: dvd_mult_div_cancel)
  have x: "x=10*(x div 10)+x mod 10"
    using div_mult_mod_eq[of x 10] by (simp add: mult.commute)
  have int_x: "int x=10*int (x div 10)+int (x mod 10)"
    using arg_cong[OF x, of int]
    by (simp only: of_nat_add of_nat_mult of_nat_numeral)
  have int_power: "int residue_value=10*int (residue_value div 10)"
    using arg_cong[OF pow, of int]
    by (simp only: of_nat_mult of_nat_numeral)
  have signed:
    "int residue_value-int x-int ?b = -10*?a-(int (x mod 10)+int ?b)"
    by (subst int_power; subst int_x; simp add: algebra_simps)
  have nonnegative: "0 \<le> ?a mod int ?M"
    using positive by simp
  have eta: "int (comma_entry_diagonal P x residue_value)=?a mod int ?M"
    using nonnegative by (simp add: comma_entry_diagonal_def)
  have remainder:
    "(int residue_value-int x-int ?b) mod int P =
      (-10*int (comma_entry_diagonal P x residue_value) -
        (int (x mod 10)+int ?b)) mod int P"
    by (simp only: signed eta modulus; rule comma_signed_diagonal_remainder)
  show ?thesis
    unfolding comma_diagonal_headroom_def Let_def
    by (simp only: remainder)
qed

lemma comma_entry_period_catalog:
  assumes "1\<le>f" "f\<le>9"
  shows "comma_finite_period_fast f (x mod 10) \<in> comma_cycle_displacements"
  using comma_finite_period_in_catalog[rule_format, of f "x mod 10"] assms
  by (simp add: comma_finite_period_fast_correct[OF assms])

lemma comma_entry_period_decimal:
  assumes "P\<in>comma_cycle_displacements"
  shows "0<P" "10 dvd P" "0<P div 10"
  using assms by (auto simp: comma_cycle_displacements_def)

lemma comma_power_table_decimal:
  assumes catalog: "P\<in>comma_cycle_displacements"
    and phase: "k<comma_short_period P"
  shows "10 dvd comma_power_table P ! k"
proof -
  have all: "list_all (\<lambda>v. 10 dvd v) (comma_power_table P)"
    using catalog by (auto simp: comma_cycle_displacements_def comma_power_table_def)
  have length: "length (comma_power_table P)=comma_short_period P"
    using catalog by (auto simp: comma_cycle_displacements_def
      comma_power_table_def comma_short_period_def)
  show ?thesis using all nth_mem[of k "comma_power_table P"] phase length
    by (auto simp: list_all_iff)
qed

lemma comma_entry_alphabet_diagonal:
  assumes sector: "1\<le>f" "f\<le>9"
    and phase: "k<comma_short_period (comma_finite_period_fast f (x mod 10))"
  shows "comma_entry_alphabet_endpoint f x k =
    comma_entry_diagonal_endpoint f
      (comma_finite_period_fast f (x mod 10)) (x mod 10)
      (comma_entry_diagonal (comma_finite_period_fast f (x mod 10)) x
        (comma_power_table (comma_finite_period_fast f (x mod 10)) ! k))"
proof -
  let ?P = "comma_finite_period_fast f (x mod 10)"
  have catalog: "?P\<in>comma_cycle_displacements"
    by (rule comma_entry_period_catalog[OF sector])
  note headroom = comma_entry_headroom_diagonal
    [OF comma_entry_period_decimal(1,2)[OF catalog]
      comma_power_table_decimal[OF catalog phase], of f x]
  show ?thesis
    by (simp only: comma_entry_alphabet_endpoint_def
      comma_entry_diagonal_endpoint_def Let_def headroom)
qed

definition comma_entry_diagonal_key ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "comma_entry_diagonal_key f r delta x =
    (x mod 10, comma_entry_diagonal
      (comma_finite_period_fast f (x mod 10)) x
      (comma_power_table (comma_finite_period_fast f (x mod 10)) !
        comma_entry_alphabet_phase f r delta x))"

theorem comma_entry_diagonal_refines:
  assumes sector: "1\<le>f" "f\<le>9" and offset: "x\<le>98"
  shows "comma_fast_sector_target r (Comma_Entry f delta x) =
    (let (d,eta)=comma_entry_diagonal_key f r delta x in
      Comma_Near f delta (comma_entry_diagonal_endpoint f
        (comma_finite_period_fast f d) d eta))"
proof -
  have valid: "\<not>(f<1 \<or> 9<f \<or> 98<x)"
    using sector offset by arith
  note normalized = comma_entry_alphabet_diagonal[OF sector
    comma_entry_alphabet_phase_bound[OF sector, where r=r and delta=delta and x=x]]
  show ?thesis
    by (simp only: comma_sector_entry_alphabet valid if_False
      comma_entry_diagonal_key_def Let_def prod.case normalized)
qed

theorem comma_entry_diagonal_congruent:
  assumes sector: "1\<le>f" "f\<le>9"
    and keys: "comma_entry_diagonal_key f r delta x =
      comma_entry_diagonal_key f r' delta' y"
  shows "comma_entry_alphabet_endpoint f x (comma_entry_alphabet_phase f r delta x) =
    comma_entry_alphabet_endpoint f y (comma_entry_alphabet_phase f r' delta' y)"
proof -
  have digits: "x mod 10=y mod 10"
    and diagonals: "snd (comma_entry_diagonal_key f r delta x) =
      snd (comma_entry_diagonal_key f r' delta' y)"
    using keys by (metis fst_conv comma_entry_diagonal_key_def, metis snd_conv)
  show ?thesis
    using comma_entry_alphabet_diagonal[OF sector
      comma_entry_alphabet_phase_bound[OF sector, where r=r and delta=delta and x=x]]
      comma_entry_alphabet_diagonal[OF sector
      comma_entry_alphabet_phase_bound[OF sector, where r=r' and delta=delta' and x=y]]
      diagonals digits
    by (simp add: comma_entry_diagonal_key_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_signed_diagonal_remainder comma_entry_headroom_diagonal
      comma_entry_diagonal_bound comma_power_table_decimal
      comma_entry_alphabet_diagonal comma_entry_diagonal_refines
      comma_entry_diagonal_congruent}) then ()
    else error "Comma Entry diagonal refinement depends on an oracle";
\<close>

end
