theory Mahler_Safety_Ledger_Separation
  imports Generated_Mahler_Safety
begin

text \<open>The same source orbit supports two different predicates. Fractional
safety failure does not certify a failed Antihydra ledger. These exact witnesses
also prevent the surviving low residues being used as an autonomous source.\<close>

theorem source_seven_fractional_failure:
  fixes t :: real
  assumes "0 \<le> t" "t < 1/2"
  shows "\<not> safe_prefix 2 (7+t)"
proof
  assume safe: "safe_prefix 2 (7+t)"
  have lo: "of_nat 7 \<le> (7::real)+t" using assms by simp
  have hi: "(7::real)+t < of_nat 7+1/2" using assms by simp
  have bound: "of_nat (mahler_orbit 7 2) \<le> (7+t)*(3/2)^2"
    using safe_prefix_source_bounds[OF safe lo hi, of 2] by simp
  have "mahler_orbit 7 2 = 17" by (simp add: mahler_D_step_def)
  with bound assms show False by (simp add: power2_eq_square; linarith)
qed

lemma ledger_at_numeral:
  "ledger_at D (numeral n) = ledger_at D (pred_numeral n) +
    (if odd (mahler_orbit D (pred_numeral n)) then 2 else -1)"
  by (simp only: numeral_eq_Suc ledger_at.simps)

theorem source_seven_ledger_safe_through_two:
  "ledger_at 7 0 = 0" "ledger_at 7 1 = 2" "ledger_at 7 2 = 4"
  by (simp_all add: ledger_at_numeral One_nat_def mahler_D_step_def)

theorem source_seven_predicates_differ:
  "\<not> safe_prefix 2 7 \<and> (\<forall>n\<le>2. 0 \<le> ledger_at 7 n)"
proof -
  have cases: "n \<le> (2::nat) \<longleftrightarrow> n=0 \<or> n=1 \<or> n=2" for n
    by arith
  show ?thesis
    using source_seven_fractional_failure[of 0]
      source_seven_ledger_safe_through_two
    by (auto simp: cases)
qed

theorem high_fiber_changes_next_residue:
  "(0::nat) mod 64 = 64 mod 64"
  "mahler_orbit 0 6 mod 64 = 0"
  "mahler_orbit 64 6 mod 64 = 25"
  "0 \<in> surviving_residues"
  "25 \<in> rejected_residues"
  by (simp_all add: mahler_D_step_def surviving_residues_def rejected_residues_def)

text \<open>Neither witness is an all-time halting or non-halting result.
The source_seven_barrier_open proposition remains undischarged.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms source_seven_fractional_failure source_seven_ledger_safe_through_two
      source_seven_predicates_differ high_fiber_changes_next_residue})
    then () else error "Mahler safety/ledger separation depends on an oracle";
\<close>

end
