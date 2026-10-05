theory Comma_Cyclotomic_Clock
  imports Comma_Frobenius_Recurrence.Comma_Carry_Core_Quotient
begin

text \<open>
The phase used by the nine core residue actions is an external CRT clock.
Its four characters are the residues modulo 4, 3, 7 and 11.  This theory
only projects that clock onto an admitted short period.  It does not make a
periodic endpoint table, select a branch, or carry an occurrence weight.

The subtractions in the 6, 22 and 28 projections are signed.  In
particular, using natural subtraction here would turn the pair (1,2) into
zero and would give the wrong CRT phase.
\<close>

record comma_cyclotomic_clock =
  comma_clock_mod4 :: nat
  comma_clock_mod3 :: nat
  comma_clock_mod7 :: nat
  comma_clock_mod11 :: nat

definition comma_cyclotomic_clock_of :: "nat \<Rightarrow> comma_cyclotomic_clock" where
  "comma_cyclotomic_clock_of r =
    \<lparr>comma_clock_mod4 = r mod 4,
      comma_clock_mod3 = r mod 3,
      comma_clock_mod7 = r mod 7,
      comma_clock_mod11 = r mod 11\<rparr>"

definition comma_cyclotomic_phase ::
    "comma_cyclotomic_clock \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_cyclotomic_phase C T shift =
    (if T = 1 then 0
     else if T = 2 then (comma_clock_mod4 C mod 2 + shift) mod 2
     else if T = 3 then (comma_clock_mod3 C + shift) mod 3
     else if T = 6 then
       (comma_clock_mod3 C +
        3 * nat ((int (comma_clock_mod4 C) - int (comma_clock_mod3 C)) mod 2) + shift) mod 6
     else if T = 22 then
       (comma_clock_mod11 C +
        11 * nat ((int (comma_clock_mod4 C) - int (comma_clock_mod11 C)) mod 2) + shift) mod 22
     else if T = 28 then
       (comma_clock_mod7 C +
        7 * nat ((3 * (int (comma_clock_mod4 C) - int (comma_clock_mod7 C))) mod 4) + shift) mod 28
     else 0 + shift mod 1)"


text \<open>Only the three small CRT bases are checked concretely. The arbitrary
occurrence and shift are transported symbolically; no endpoint rows are stored.\<close>

definition comma_clock_base_check :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_clock_base_check T N = list_all
    (\<lambda>q. comma_cyclotomic_phase (comma_cyclotomic_clock_of q) T 0 = q mod T)
    [0..<N]"

lemma comma_clock_base_checks:
  "comma_clock_base_check 6 12"
  "comma_clock_base_check 22 44"
  "comma_clock_base_check 28 28"
  by (code_simp)+

lemma comma_clock_shift:
  assumes "T\<in>{1,2,3,6,22,28}"
  shows "comma_cyclotomic_phase C T shift =
    (comma_cyclotomic_phase C T 0 + shift) mod T"
proof -
  consider "T=1" | "T=2" | "T=3" | "T=6" | "T=22" | "T=28"
    using assms by auto
  then show ?thesis
    by cases (simp_all add: comma_cyclotomic_phase_def mod_add_left_eq)
qed

lemma comma_clock_projection_period6:
  "comma_cyclotomic_phase (comma_cyclotomic_clock_of r) 6 0 = r mod 6"
proof -
  have d3: "(3::nat) dvd 12" by simp
  have d4: "(4::nat) dvd 12" by simp
  have d6: "(6::nat) dvd 12" by simp
  have local: "comma_cyclotomic_phase (comma_cyclotomic_clock_of (r mod 12)) 6 0 =
    (r mod 12) mod 6"
    using comma_clock_base_checks(1)
    by (auto simp: comma_clock_base_check_def list_all_iff)
  show ?thesis using local
    by (simp add: comma_cyclotomic_phase_def comma_cyclotomic_clock_of_def mod_mod_cancel[OF d3] mod_mod_cancel[OF d4] mod_mod_cancel[OF d6])
qed

lemma comma_clock_projection_period22:
  "comma_cyclotomic_phase (comma_cyclotomic_clock_of r) 22 0 = r mod 22"
proof -
  have d4: "(4::nat) dvd 44" by simp
  have d11: "(11::nat) dvd 44" by simp
  have d22: "(22::nat) dvd 44" by simp
  have local: "comma_cyclotomic_phase (comma_cyclotomic_clock_of (r mod 44)) 22 0 =
    (r mod 44) mod 22"
    using comma_clock_base_checks(2)
    by (auto simp: comma_clock_base_check_def list_all_iff)
  show ?thesis using local
    by (simp add: comma_cyclotomic_phase_def comma_cyclotomic_clock_of_def mod_mod_cancel[OF d4] mod_mod_cancel[OF d11] mod_mod_cancel[OF d22])
qed

lemma comma_clock_projection_period28:
  "comma_cyclotomic_phase (comma_cyclotomic_clock_of r) 28 0 = r mod 28"
proof -
  have d4: "(4::nat) dvd 28" by simp
  have d7: "(7::nat) dvd 28" by simp
  have d28: "(28::nat) dvd 28" by simp
  have local: "comma_cyclotomic_phase (comma_cyclotomic_clock_of (r mod 28)) 28 0 =
    (r mod 28) mod 28"
    using comma_clock_base_checks(3)
    by (auto simp: comma_clock_base_check_def list_all_iff)
  show ?thesis using local
    by (simp add: comma_cyclotomic_phase_def comma_cyclotomic_clock_of_def mod_mod_cancel[OF d4] mod_mod_cancel[OF d7] mod_mod_cancel[OF d28])
qed

theorem comma_cyclotomic_clock_projection:
  assumes period: "T\<in>{1,2,3,6,22,28}"
  shows "comma_cyclotomic_phase (comma_cyclotomic_clock_of r) T shift =
    (r + shift) mod T"
proof -
  have d2: "(2::nat) dvd 4" by simp
  have base: "comma_cyclotomic_phase (comma_cyclotomic_clock_of r) T 0 = r mod T"
  proof (cases "T=1 \<or> T=2 \<or> T=3")
    case True
    then show ?thesis
      by (auto simp: comma_cyclotomic_phase_def comma_cyclotomic_clock_of_def
        mod_mod_cancel[OF d2])
  next
    case False
    have "T=6 \<or> T=22 \<or> T=28" using period False by auto
    then show ?thesis
      using comma_clock_projection_period6[of r]
        comma_clock_projection_period22[of r] comma_clock_projection_period28[of r]
      by blast
  qed
  show ?thesis
    by (subst comma_clock_shift[OF period]) (simp only: base mod_add_left_eq)
qed

lemma comma_cyclotomic_clock_core_phase:
  assumes catalog: "P\<in>comma_cycle_displacements"
  shows "comma_cyclotomic_phase (comma_cyclotomic_clock_of r)
      (comma_core_period (comma_core_modulus P)) 919 =
    (r + 924 - 5) mod comma_core_period (comma_core_modulus P)"
proof -
  have period: "comma_core_period (comma_core_modulus P)\<in>{1,2,3,6,22,28}"
    by (auto simp: comma_core_period_def)
  show ?thesis
    using comma_cyclotomic_clock_projection[OF period, of r 919]
    by (simp add: add.commute)
qed

theorem comma_cyclotomic_clock_core_residue:
  assumes catalog: "P\<in>comma_cycle_displacements"
  shows "comma_recursive_core_power_residue P r =
    (let h=comma_core_primary P; c=comma_core_modulus P; seed=comma_core_seed P;
         t=comma_cyclotomic_phase (comma_cyclotomic_clock_of r) (comma_core_period c) 919
     in h*((seed*comma_recursive_core_residue c t) mod c))"
  by (simp only: comma_recursive_core_power_residue_def Let_def
    comma_cyclotomic_clock_core_phase[OF catalog])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_cyclotomic_clock_projection comma_cyclotomic_clock_core_residue})
    then () else error "Cyclotomic clock depends on an oracle"
\<close>
end
