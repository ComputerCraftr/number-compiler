theory Comma_Carry_Core_Quotient
  imports Comma_Frobenius_Recurrence Comma_Arithmetic.Comma_Finite_Period
begin

ML_file "../comma_entry_arithmetic/proof_profile.ML"

text \<open>The orbit residue is occurrence data for the decimal phase, not
an argument of its normalized carry action. These equations refine the existing
phase and period definitions. They do not identify weighted sector locators or
their seam consumers: those require a separate potential/admission transport.
All division below is exact under the stated source decomposition.\<close>

lemma comma_phase_carry_orbit_conjugacy:
  fixes g L f a d orbit j n :: nat
  assumes positive: "0<g" and decimal: "g*L=10"
    and sector: "f=g*a" and source: "d=orbit+g*j"
    and residue: "orbit<g"
  shows "comma_phase_digit f d n=orbit+g*((j+n*a) mod L)"
    "(d+n*f) div 10=(j+n*a) div L"
proof -
  have expanded: "d+n*f=orbit+g*(j+n*a)"
    by (simp only: sector source; simp add: algebra_simps)
  have inner_div: "(d+n*f) div g=j+n*a"
    using positive residue by (simp add: expanded)
  have inner_mod: "(d+n*f) mod g=orbit"
    using residue by (simp add: expanded)
  have phase: "(d+n*f) mod 10=g*((j+n*a) mod L)+orbit"
    by (simp only: decimal[symmetric] mod_mult2_eq inner_div inner_mod)
  show "comma_phase_digit f d n=orbit+g*((j+n*a) mod L)"
    by (simp only: comma_phase_digit_def phase; simp add: add.commute)
  show "(d+n*f) div 10=(j+n*a) div L"
    by (simp only: decimal[symmetric] div_mult2_eq inner_div)
qed

lemma comma_normalized_phase_orbit_independent:
  fixes g L f a d orbit j n :: nat
  assumes "0<g" "g*L=10" "f=g*a" "d=orbit+g*j" "orbit<g"
  shows "(comma_phase_digit f d n-orbit) div g=(j+n*a) mod L"
  by (simp only: comma_phase_carry_orbit_conjugacy(1)[OF assms];
    simp add: assms(1))

lemma comma_one_step_carry_orbit_independent:
  fixes g L f a d orbit j :: nat
  assumes "0<g" "g*L=10" "f=g*a" "d=orbit+g*j" "orbit<g"
  shows "((d+f) mod 10-orbit) div g=(j+a) mod L"
    "(d+f) div 10=(j+a) div L"
  using comma_normalized_phase_orbit_independent[OF assms, of 1]
    comma_phase_carry_orbit_conjugacy(2)[OF assms, of 1]
  by (simp_all add: comma_phase_digit_def)

lemma comma_finite_period_normalized_orbit:
  fixes g L f a d orbit j :: nat
  assumes positive: "0<g" and gcd: "g=gcd f 10"
    and decimal: "g*L=10" and sector: "f=g*a"
    and source: "d=orbit+g*j" and residue: "orbit<g"
  shows "comma_finite_period f d=10*(L*orbit+5*(L-1)+a)"
    "comma_finite_period f d div 10=L*orbit+5*(L-1)+a"
proof -
  have cycle: "10 div g=L"
    using positive by (simp only: decimal[symmetric]; simp)
  have phase: "d mod g=orbit" using residue by (simp add: source)
  have sum: "g*L*(L-1) div 2=5*(L-1)"
    by (simp only: decimal; simp)
  have scaled_sector: "L*f=10*a"
  proof -
    have reverse_decimal: "L*g=10" using decimal by (simp only: mult.commute)
    show ?thesis by (simp only: sector mult.assoc[symmetric] reverse_decimal)
  qed
  show period: "comma_finite_period f d=10*(L*orbit+5*(L-1)+a)"
    by (simp only: comma_finite_period_def gcd[symmetric] Let_def cycle phase
      sum scaled_sector; simp add: algebra_simps)
  show "comma_finite_period f d div 10=L*orbit+5*(L-1)+a"
    by (simp only: period; simp)
qed

text \<open>Removing a primary modulus requires an actual divisibility bound.
The following CRT equality retains that premise explicitly. It does not assume
that the 17 concrete moduli have been factored or replace a full residue by its
core residue without the corresponding lift.\<close>

lemma comma_coprime_residue_pair:
  fixes h c x y :: int
  assumes independent: "coprime h c"
  shows "x mod (h*c)=y mod (h*c) \<longleftrightarrow>
    x mod h=y mod h \<and> x mod c=y mod c"
proof -
  have forward: "h dvd x-y \<and> c dvd x-y" if "h*c dvd x-y"
    using that dvd_trans[of h "h*c" "x-y"]
      dvd_trans[of c "h*c" "x-y"] by simp
  have backward: "h*c dvd x-y" if "h dvd x-y" "c dvd x-y"
    by (rule divides_mult[OF that independent])
  show ?thesis by (simp only: mod_eq_dvd_iff; use forward backward in blast)
qed

lemma comma_primary_power_vanishes:
  fixes h :: int and v e :: nat
  assumes primary: "h dvd 10^v" and exponent: "v\<le>e"
  shows "h dvd 10^e"
proof -
  obtain delta where "e=v+delta" using exponent by (auto simp: le_iff_add)
  then show ?thesis using primary by (simp add: power_add)
qed

lemma comma_frobenius_core_crt_lift:
  fixes h c :: int and v e e' :: nat
  assumes independent: "coprime h c" and primary: "h dvd 10^v"
    and exponents: "v\<le>e" "v\<le>e'"
  shows "(10::int)^e mod (h*c)=10^e' mod (h*c) \<longleftrightarrow>
    (10::int)^e mod c=10^e' mod c"
proof -
  have zeros: "(10::int)^e mod h=0" "(10::int)^e' mod h=0"
    using comma_primary_power_vanishes[OF primary exponents(1)]
      comma_primary_power_vanishes[OF primary exponents(2)] by simp_all
  show ?thesis by (simp only: comma_coprime_residue_pair[OF independent] zeros; simp)
qed


lemma comma_frobenius_core_multiplicative_lift:
  fixes h c v t :: nat
  assumes positive: "0<h" and primary: "h dvd 10^v"
  shows "10^(v+t) mod (h*c)=
    h*((((10^v div h) mod c)*(10^t mod c)) mod c)"
proof -
  have seed: "10^v=h*(10^v div h)"
    using primary by (simp add: dvd_mult_div_cancel)
  have factor: "10^(v+t)=h*((10^v div h)*10^t)"
  proof -
    have "(10::nat)^(v+t)=10^v*10^t" by (rule power_add)
    also have "...=(h*(10^v div h))*10^t"
      by (rule arg_cong[OF seed, of "\<lambda>value. value*10^t"])
    also have "...=h*((10^v div h)*10^t)" by (simp only: mult.assoc)
    finally show ?thesis .
  qed
  have residues: "((10^v div h)*10^t) mod c=
    (((10^v div h) mod c)*(10^t mod c)) mod c"
    by (rule mod_mult_eq[symmetric])
  show ?thesis by (simp only: factor mod_mult_mult1 residues)
qed

definition comma_core_primary :: "nat \<Rightarrow> nat" where
  "comma_core_primary P=gcd P 100000"

definition comma_core_modulus :: "nat \<Rightarrow> nat" where
  "comma_core_modulus P=P div comma_core_primary P"

definition comma_core_seed :: "nat \<Rightarrow> nat" where
  "comma_core_seed P=(100000 div comma_core_primary P) mod comma_core_modulus P"

definition comma_core_period :: "nat \<Rightarrow> nat" where
  "comma_core_period c=(if c=29 then 28 else if c=23 then 22
    else if c=7 \<or> c=13 \<or> c=21 then 6 else if c=27 then 3
    else if c=11 then 2 else 1)"

definition comma_core_lift_admitted :: "nat \<Rightarrow> bool" where
  "comma_core_lift_admitted P=(let h=comma_core_primary P;
    c=comma_core_modulus P; T=comma_core_period c in
    0<h \<and> 0<c \<and> P=h*c \<and> h dvd 100000 \<and> coprime h c \<and>
    c\<in>{1,3,7,11,13,21,23,27,29} \<and>
    0<T \<and> T dvd 924 \<and> T=comma_short_period P \<and>
    mod_exp (10::nat) T c=1 mod c)"

text \<open>This is only the small arithmetic lift catalog. It contains no
source trajectories, branch choices, rank certificates or full clock table.
The primary lift and full physical displacement remain occurrence data.\<close>


lemma comma_core_lift_parameters:
  "comma_core_primary 60=20" "comma_core_modulus 60=3"
  "comma_core_period (comma_core_modulus 60)=1"
  "comma_core_primary 80=80" "comma_core_modulus 80=1"
  "comma_core_period (comma_core_modulus 80)=1"
  "comma_core_primary 100=100" "comma_core_modulus 100=1"
  "comma_core_period (comma_core_modulus 100)=1"
  "comma_core_primary 120=40" "comma_core_modulus 120=3"
  "comma_core_period (comma_core_modulus 120)=1"
  "comma_core_primary 140=20" "comma_core_modulus 140=7"
  "comma_core_period (comma_core_modulus 140)=6"
  "comma_core_primary 210=10" "comma_core_modulus 210=21"
  "comma_core_period (comma_core_modulus 210)=6"
  "comma_core_primary 220=20" "comma_core_modulus 220=11"
  "comma_core_period (comma_core_modulus 220)=2"
  "comma_core_primary 230=10" "comma_core_modulus 230=23"
  "comma_core_period (comma_core_modulus 230)=22"
  "comma_core_primary 240=80" "comma_core_modulus 240=3"
  "comma_core_period (comma_core_modulus 240)=1"
  "comma_core_primary 260=20" "comma_core_modulus 260=13"
  "comma_core_period (comma_core_modulus 260)=6"
  "comma_core_primary 270=10" "comma_core_modulus 270=27"
  "comma_core_period (comma_core_modulus 270)=3"
  "comma_core_primary 280=40" "comma_core_modulus 280=7"
  "comma_core_period (comma_core_modulus 280)=6"
  "comma_core_primary 290=10" "comma_core_modulus 290=29"
  "comma_core_period (comma_core_modulus 290)=28"
  "comma_core_primary 460=20" "comma_core_modulus 460=23"
  "comma_core_period (comma_core_modulus 460)=22"
  "comma_core_primary 480=160" "comma_core_modulus 480=3"
  "comma_core_period (comma_core_modulus 480)=1"
  "comma_core_primary 520=40" "comma_core_modulus 520=13"
  "comma_core_period (comma_core_modulus 520)=6"
  "comma_core_primary 540=20" "comma_core_modulus 540=27"
  "comma_core_period (comma_core_modulus 540)=3"
  by (simp_all add: comma_core_primary_def comma_core_modulus_def
    comma_core_period_def gcd_nat.simps)

lemma comma_core_lift_period_powers:
  "mod_exp (10::nat) 1 1=1 mod 1"
  "mod_exp (10::nat) 1 3=1 mod 3"
  "mod_exp (10::nat) 6 7=1 mod 7"
  "mod_exp (10::nat) 6 21=1 mod 21"
  "mod_exp (10::nat) 2 11=1 mod 11"
  "mod_exp (10::nat) 22 23=1 mod 23"
  "mod_exp (10::nat) 6 13=1 mod 13"
  "mod_exp (10::nat) 3 27=1 mod 27"
  "mod_exp (10::nat) 28 29=1 mod 29"
  by (simp_all add: mod_exp_def)

lemma comma_core_lift_metadata:
  "comma_core_lift_admitted 60"
  "comma_core_lift_admitted 80"
  "comma_core_lift_admitted 100"
  "comma_core_lift_admitted 120"
  "comma_core_lift_admitted 140"
  "comma_core_lift_admitted 210"
  "comma_core_lift_admitted 220"
  "comma_core_lift_admitted 230"
  "comma_core_lift_admitted 240"
  "comma_core_lift_admitted 260"
  "comma_core_lift_admitted 270"
  "comma_core_lift_admitted 280"
  "comma_core_lift_admitted 290"
  "comma_core_lift_admitted 460"
  "comma_core_lift_admitted 480"
  "comma_core_lift_admitted 520"
  "comma_core_lift_admitted 540"
  using comma_core_lift_parameters comma_core_lift_period_powers
  by (simp_all add: comma_core_lift_admitted_def comma_short_period_def
    coprime_iff_gcd_eq_1 gcd_nat.simps)

lemma comma_core_lift_catalog_checked:
  "list_all comma_core_lift_admitted
    [60,80,100,120,140,210,220,230,240,260,270,280,290,460,480,520,540]"
  by (simp only: list_all_Cons_iff list_all_Nil_iff comma_core_lift_metadata HOL.simp_thms)

lemma comma_core_lift_catalog:
  assumes "P\<in>comma_cycle_displacements"
  shows "comma_core_lift_admitted P"
  using comma_core_lift_catalog_checked assms
  by (auto simp: comma_cycle_displacements_def list_all_iff)

definition comma_core_power_residue :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_core_power_residue P r=(let h=comma_core_primary P;
    c=comma_core_modulus P; seed=comma_core_seed P;
    t=(r+924-5) mod comma_core_period c
    in h*((seed*mod_exp (10::nat) t c) mod c))"


lemma comma_core_power_residue_refines:
  assumes catalog: "P\<in>comma_cycle_displacements"
  shows "comma_core_power_residue P r=comma_power_residue P r"
proof -
  let ?h = "comma_core_primary P"
  let ?c = "comma_core_modulus P"
  let ?t = "(r+924-5) mod comma_core_period ?c"
  have admitted: "comma_core_lift_admitted P" by (rule comma_core_lift_catalog[OF catalog])
  have positive: "0<?h" and primary: "?h dvd (10::nat)^5"
    and full: "P=?h*?c" and period: "comma_core_period ?c=comma_short_period P"
    using admitted by (auto simp: comma_core_lift_admitted_def Let_def)
  have lifted: "(10::nat)^(5+?t) mod P=
    ?h*((((10^5 div ?h) mod ?c)*(10^?t mod ?c)) mod ?c)"
  proof -
    have "(10::nat)^(5+?t) mod P=10^(5+?t) mod (?h*?c)"
      by (rule arg_cong[OF full, of "\<lambda>modulus. (10::nat)^(5+?t) mod modulus"])
    also have "...=?h*((((10^5 div ?h) mod ?c)*(10^?t mod ?c)) mod ?c)"
      by (rule comma_frobenius_core_multiplicative_lift[OF positive primary])
    finally show ?thesis .
  qed
  have exponent_five: "(10::nat)^5=100000" by simp
  have old: "comma_power_residue P r=(10::nat)^(5+?t) mod P"
    by (simp only: comma_power_residue_def mod_exp_def period)
  have new: "comma_core_power_residue P r=
    ?h*((((10^5 div ?h) mod ?c)*(10^?t mod ?c)) mod ?c)"
    by (simp only: comma_core_power_residue_def comma_core_seed_def
      Let_def mod_exp_def exponent_five)
  show ?thesis by (simp only: old new lifted)
qed


lemma comma_core_power_fixed_period:
  assumes "comma_core_period (comma_core_modulus P)=1"
  shows "comma_core_power_residue P r=comma_core_primary P*comma_core_seed P"
  using assms by (simp add: comma_core_power_residue_def comma_core_seed_def
    mod_exp_def mod_mult_right_eq)

text \<open>The recursive evaluator stores only half cycles and the two
rotation factors. In particular 21 has no independent table: its residue is
lifted from 7 by the mod-3 condition. Natural subtraction in that lift uses
4-(y mod 3), which represents the signed residue 1-y without saturation.
This total HOL function returns zero outside the catalog; its refinement
theorem is restricted to the nine admitted cores. The Python API rejects
such invalid cores rather than publishing that default.\<close>

definition comma_core_halfcycle :: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_core_halfcycle c base t=(let n=length base; r=t mod (2*n);
    value=base ! (r mod n) in if r<n then value else c-value)"

definition comma_core_seven :: "nat \<Rightarrow> nat" where
  "comma_core_seven t=comma_core_halfcycle 7 [1,3,2] t"

definition comma_recursive_core_residue :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_recursive_core_residue c t=(let r=t mod comma_core_period c in
    if c=1 then 0 else if c=3 then 1
    else if c=7 then comma_core_seven r
    else if c=11 then 1+9*(r mod 2)
    else if c=13 then comma_core_halfcycle 13 [1,10,9] r
    else if c=21 then (let y=comma_core_seven r in y+7*((4-y mod 3) mod 3))
    else if c=23 then comma_core_halfcycle 23 [1,10,8,11,18,19,6,14,2,20,16] r
    else if c=27 then 1+9*(r mod 3)
    else if c=29 then ([1,10,13,14,24,8,22] ! (r mod 7) *
      [1,17,28,12] ! (r div 7)) mod 29
    else 0)"

definition comma_recursive_core_checked :: "nat \<Rightarrow> bool" where
  "comma_recursive_core_checked c=(let T=comma_core_period c in
    0<T \<and> mod_exp (10::nat) T c=1 mod c \<and>
    list_all (\<lambda>r. comma_recursive_core_residue c r=mod_exp (10::nat) r c) [0..<T])"

text \<open>The nine ground checks use kernel-producing code simplification
and bounded modular exponentiation. Splitting the checks keeps each proof
small and does not introduce a stored full-period power table.\<close>

lemma comma_recursive_core_check_one: "comma_recursive_core_checked 1"
  by code_simp

lemma comma_recursive_core_check_three: "comma_recursive_core_checked 3"
  by code_simp

lemma comma_recursive_core_check_seven: "comma_recursive_core_checked 7"
  by code_simp

lemma comma_recursive_core_check_eleven: "comma_recursive_core_checked 11"
  by code_simp

lemma comma_recursive_core_check_thirteen: "comma_recursive_core_checked 13"
  by code_simp

lemma comma_recursive_core_check_twenty_one: "comma_recursive_core_checked 21"
  by code_simp

lemma comma_recursive_core_check_twenty_three: "comma_recursive_core_checked 23"
  by code_simp

lemma comma_recursive_core_check_twenty_seven: "comma_recursive_core_checked 27"
  by code_simp

lemma comma_recursive_core_check_twenty_nine_period:
  "mod_exp (10::nat) 28 29=1 mod 29"
  by code_simp

lemma comma_mod_exp_nat_successor:
  "mod_exp a (Suc r) (m::nat)=(a*mod_exp a r m) mod m"
  unfolding mod_exp_def
  by (simp only: power_Suc; rule mod_mult_right_eq[symmetric])

lemma comma_recursive_core_residue_twenty_nine:
  "comma_recursive_core_residue 29 r =
    ([1,10,13,14,24,8,22] ! ((r mod 28) mod 7) *
      [1,17,28,12] ! ((r mod 28) div 7)) mod 29"
  by (simp add: comma_recursive_core_residue_def comma_core_period_def Let_def)

lemma comma_recursive_core_twenty_nine_steps:
  "list_all (\<lambda>r. comma_recursive_core_residue 29 (Suc r) =
      (10*comma_recursive_core_residue 29 r) mod 29) [0..<27]"
  by (simp only: comma_recursive_core_residue_twenty_nine; code_simp)

lemma comma_recursive_core_twenty_nine_step:
  assumes "r<27"
  shows "comma_recursive_core_residue 29 (Suc r) =
    (10*comma_recursive_core_residue 29 r) mod 29"
proof -
  have all_steps:
    "\<forall>r\<in>set [0..<27]. comma_recursive_core_residue 29 (Suc r) =
      (10*comma_recursive_core_residue 29 r) mod 29"
    using comma_recursive_core_twenty_nine_steps
    by (simp only: list_all_iff)
  have "r\<in>set [0..<27]" using assms by simp
  then show ?thesis using all_steps by blast
qed

lemma comma_recursive_core_twenty_nine_row:
  "r<28 \<Longrightarrow>
    comma_recursive_core_residue 29 r=mod_exp (10::nat) r 29"
proof (induction r)
  case 0
  then show ?case by (simp add: comma_recursive_core_residue_twenty_nine mod_exp_def)
next
  case (Suc r)
  have previous_bound: "r<28" using Suc.prems by simp
  have step_bound: "r<27" using Suc.prems by arith
  have residue_step:
    "comma_recursive_core_residue 29 (Suc r) =
      (10*comma_recursive_core_residue 29 r) mod 29"
    by (rule comma_recursive_core_twenty_nine_step[OF step_bound])
  have power_step:
    "mod_exp (10::nat) (Suc r) 29=(10*mod_exp 10 r 29) mod 29"
    by (rule comma_mod_exp_nat_successor)
  show ?case using Suc.IH[OF previous_bound] residue_step power_step by simp
qed

lemma comma_recursive_core_check_twenty_nine_rows:
  "list_all (\<lambda>r. comma_recursive_core_residue 29 r=mod_exp (10::nat) r 29)
    [0..<28]"
  unfolding list_all_iff
proof (intro ballI)
  fix r
  assume "r \<in> set [0..<28]"
  then have bound: "r<28" by simp
  show "comma_recursive_core_residue 29 r=mod_exp (10::nat) r 29"
    by (rule comma_recursive_core_twenty_nine_row[OF bound])
qed

lemma comma_recursive_core_check_twenty_nine: "comma_recursive_core_checked 29"
proof -
  show ?thesis
    unfolding comma_recursive_core_checked_def comma_core_period_def
    using comma_recursive_core_check_twenty_nine_period
      comma_recursive_core_check_twenty_nine_rows
    by simp
qed

lemmas comma_recursive_core_checks = comma_recursive_core_check_one
  comma_recursive_core_check_three comma_recursive_core_check_seven
  comma_recursive_core_check_eleven comma_recursive_core_check_thirteen
  comma_recursive_core_check_twenty_one comma_recursive_core_check_twenty_three
  comma_recursive_core_check_twenty_seven comma_recursive_core_check_twenty_nine

lemma comma_recursive_core_catalog_checked:
  assumes "c\<in>{1,3,7,11,13,21,23,27,29}"
  shows "comma_recursive_core_checked c"
  using assms comma_recursive_core_checks by auto

ML \<open>
  val started = Time.now ();
  val _ = Comma_Proof_Profile.report
    "Carry Core stage=catalog-and-29-rows-consolidation-start";
  val _ = Thm.consolidate @{thms comma_core_lift_catalog_checked
    comma_recursive_core_checks comma_recursive_core_check_twenty_nine_rows
    comma_recursive_core_catalog_checked};
  val _ = Comma_Proof_Profile.report
    ("Carry Core stage=catalog-and-29-rows-consolidated elapsed_ms=" ^
      Comma_Proof_Profile.elapsed_ms started);
\<close>

lemma comma_core_modular_period_repeated:
  fixes c T u q :: nat
  assumes period: "(10::nat)^T mod c=1 mod c"
  shows "(10::nat)^(u+T*q) mod c=10^u mod c"
proof (induction q)
  case 0
  then show ?case by simp
next
  case (Suc q)
  have exponent: "u+T*Suc q=(u+T*q)+T" by (simp add: algebra_simps)
  have "(10::nat)^(u+T*Suc q) mod c=(10^(u+T*q)*10^T) mod c"
    by (simp only: exponent power_add)
  also have "...=((10^(u+T*q) mod c)*(10^T mod c)) mod c"
    by (rule mod_mult_eq[symmetric])
  also have "...=(10^(u+T*q) mod c)"
    by (simp only: period mod_mult_right_eq; simp)
  also have "...=10^u mod c" by (rule Suc.IH)
  finally show ?case .
qed

lemma comma_recursive_core_phase:
  "comma_recursive_core_residue c (t mod comma_core_period c)=
    comma_recursive_core_residue c t"
  by (simp add: comma_recursive_core_residue_def)

lemma comma_recursive_core_residue_refines:
  assumes catalog: "c\<in>{1,3,7,11,13,21,23,27,29}"
  shows "comma_recursive_core_residue c t=(10::nat)^t mod c"
proof -
  let ?T = "comma_core_period c"
  have checked: "comma_recursive_core_checked c"
    by (rule comma_recursive_core_catalog_checked[OF catalog])
  have positive: "0<?T" and period: "(10::nat)^?T mod c=1 mod c"
    and rows: "list_all (\<lambda>r. comma_recursive_core_residue c r=(10::nat)^r mod c) [0..<?T]"
    using checked by (auto simp: comma_recursive_core_checked_def Let_def mod_exp_def)
  have bounded: "t mod ?T<?T" by (rule mod_less_divisor[OF positive])
  have finite: "comma_recursive_core_residue c (t mod ?T)=(10::nat)^(t mod ?T) mod c"
    using rows bounded by (auto simp: list_all_iff)
  have evaluated: "comma_recursive_core_residue c t=(10::nat)^(t mod ?T) mod c"
    using finite by (simp only: comma_recursive_core_phase)
  have split: "t=(t mod ?T)+?T*(t div ?T)"
    using mod_mult_div_eq[of t ?T] by simp
  have repeated: "(10::nat)^((t mod ?T)+?T*(t div ?T)) mod c=10^(t mod ?T) mod c"
    by (rule comma_core_modular_period_repeated[OF period])
  have reduced: "(10::nat)^t mod c=10^(t mod ?T) mod c"
    using repeated by (simp only: split[symmetric])
  show ?thesis by (simp only: evaluated reduced)
qed

ML \<open>
  val started = Time.now ();
  val _ = Comma_Proof_Profile.report
    "Carry Core stage=modular-period-and-residue-refinement-consolidation-start";
  val _ = Thm.consolidate @{thms comma_core_modular_period_repeated
    comma_recursive_core_residue_refines};
  val _ = Comma_Proof_Profile.report
    ("Carry Core stage=modular-period-and-residue-refinement-consolidated elapsed_ms=" ^
      Comma_Proof_Profile.elapsed_ms started);
\<close>

definition comma_recursive_core_power_residue :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_recursive_core_power_residue P r=(let h=comma_core_primary P;
    c=comma_core_modulus P; seed=comma_core_seed P;
    t=(r+924-5) mod comma_core_period c
    in h*((seed*comma_recursive_core_residue c t) mod c))"

lemma comma_recursive_core_power_residue_refines:
  assumes catalog: "P\<in>comma_cycle_displacements"
  shows "comma_recursive_core_power_residue P r=comma_power_residue P r"
proof -
  have core: "comma_core_modulus P\<in>{1,3,7,11,13,21,23,27,29}"
    using comma_core_lift_catalog[OF catalog]
    by (auto simp: comma_core_lift_admitted_def Let_def)
  have same: "comma_recursive_core_power_residue P r=comma_core_power_residue P r"
    by (simp only: comma_recursive_core_power_residue_def comma_core_power_residue_def
      Let_def comma_recursive_core_residue_refines[OF core] mod_exp_def)
  show ?thesis by (simp only: same comma_core_power_residue_refines[OF catalog])
qed

text \<open>The native occurrence layer retains the physical exponent, while
the carry action consumes only the finite phase residue.  This bridge is the
single point where the normalized \(5+t\) core representative is related to
an arbitrary physical exponent past primary saturation.  It deliberately
reuses the checked power-residue refinement above; no second CRT or period
calculation is performed here.\<close>

lemma comma_recursive_core_physical_exponent:
  assumes catalog: "P\<in>comma_cycle_displacements"
    and lower: "5\<le>p"
  shows "comma_recursive_core_power_residue P (p mod 924)=10^p mod P"
proof -
  have core:
    "comma_recursive_core_power_residue P (p mod 924) =
      comma_power_residue P (p mod 924)"
    by (rule comma_recursive_core_power_residue_refines[OF catalog])
  have physical:
    "comma_power_residue P (p mod 924)=10^p mod P"
    by (rule comma_power_residue_correct[OF catalog lower])
  show ?thesis using core physical by simp
qed

text \<open>Finite headroom has no physical exponent premise. The quotient
refines every phase; primary saturation belongs only to the physical occurrence
bridge above, not to each finite transition.\<close>

lemma comma_finite_headroom_recursive_core:
  fixes f r delta offset :: nat
  assumes sector: "1\<le>f" "f\<le>9"
  defines "P \<equiv> comma_finite_period f (offset mod 10)"
    and "e \<equiv> comma_finite_guard_extra f"
  shows "comma_finite_headroom f r delta offset =
    1 + e + nat ((int (comma_recursive_core_power_residue P
      ((r + delta) mod 924)) - int offset - int (1 + e)) mod int P)"
proof -
  have catalog: "P\<in>comma_cycle_displacements"
    using comma_finite_period_in_catalog sector
    unfolding P_def by auto
  have core: "comma_power_residue P ((r+delta) mod 924) =
      comma_recursive_core_power_residue P ((r+delta) mod 924)"
    by (rule comma_recursive_core_power_residue_refines[OF catalog, symmetric])
  show ?thesis
    unfolding comma_finite_headroom_def
    by (simp only: Let_def P_def[symmetric] e_def[symmetric] core)
qed

ML \<open>
  val started = Time.now ();
  val _ = Comma_Proof_Profile.report
    "Carry Core stage=physical-exponent-and-headroom-consolidation-start";
  val _ = Thm.consolidate @{thms comma_recursive_core_physical_exponent
    comma_finite_headroom_recursive_core};
  val _ = Comma_Proof_Profile.report
    ("Carry Core stage=physical-exponent-and-headroom-consolidated elapsed_ms=" ^
      Comma_Proof_Profile.elapsed_ms started);
\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_phase_carry_orbit_conjugacy
      comma_normalized_phase_orbit_independent comma_one_step_carry_orbit_independent
      comma_finite_period_normalized_orbit comma_coprime_residue_pair
      comma_primary_power_vanishes comma_frobenius_core_crt_lift
      comma_frobenius_core_multiplicative_lift comma_core_lift_catalog_checked
      comma_core_lift_catalog comma_core_power_residue_refines
      comma_core_power_fixed_period comma_recursive_core_checks
      comma_recursive_core_catalog_checked comma_core_modular_period_repeated
      comma_recursive_core_phase comma_recursive_core_residue_refines
      comma_recursive_core_power_residue_refines
      comma_recursive_core_physical_exponent
      comma_finite_headroom_recursive_core}) then ()
    else error "Comma carry/core quotient depends on an oracle";
\<close>

end
