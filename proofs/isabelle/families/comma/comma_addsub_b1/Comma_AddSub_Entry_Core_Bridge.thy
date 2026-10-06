theory Comma_AddSub_Entry_Core_Bridge
  imports Comma_Entry_Port.Comma_Entry_Port_Refinement
    Comma_C1_Carry_Generator.Comma_C1_Phase
    Comma_Frobenius_Recurrence.Comma_Carry_Core_Quotient
begin

ML_file "../comma_entry_arithmetic/Proof_Dependency_Audit.ML"

text \<open>
The Entry bridge joins the existing C1 source phase to the recursive core
residue used by the Frobenius carry quotient. It reconstructs the established
diagonal key and then invokes the already-checked weighted locator. It does
not claim that this Entry observation alone determines the complete B1
decade atom or is closed under its successor relation.
\<close>

definition comma_addsub_entry_core_key ::
    "comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "comma_addsub_entry_core_key C r delta =
    (let f = c1_sector C;
         x = comma_c1_decode (c1_mod4 C) (c1_mod25 C);
         P = comma_finite_period_fast f (x mod 10)
     in (x mod 10,
       comma_entry_diagonal P x
         (comma_recursive_core_power_residue P ((r + delta) mod 924))))"

lemma comma_addsub_entry_core_key_refines:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_addsub_entry_core_key C r delta =
    comma_entry_diagonal_key (c1_sector C) r delta
      (comma_c1_decode (c1_mod4 C) (c1_mod25 C))"
proof -
  let ?f = "c1_sector C"
  let ?x = "comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
  let ?P = "comma_finite_period_fast ?f (?x mod 10)"
  let ?T = "comma_short_period ?P"
  have sector: "1 \<le> ?f" "?f \<le> 9"
    using admitted by (auto simp: comma_c1_phase_admitted_def)
  have catalog: "?P \<in> comma_cycle_displacements"
    by (rule comma_entry_period_catalog[OF sector])
  have phase:
    "comma_entry_alphabet_phase ?f r delta ?x =
      (((r + delta) mod 924 + 919) mod ?T)"
    by (simp add: comma_entry_alphabet_phase_def mod_add_left_eq)
  have table_residue:
    "comma_power_table ?P ! comma_entry_alphabet_phase ?f r delta ?x =
      comma_power_residue_fast ?P ((r + delta) mod 924)"
    by (simp only: comma_power_residue_fast_def phase)
  have power_residue:
    "comma_power_table ?P ! comma_entry_alphabet_phase ?f r delta ?x =
      comma_recursive_core_power_residue ?P ((r + delta) mod 924)"
    using comma_power_residue_fast_correct[OF catalog, of "(r + delta) mod 924"]
      comma_recursive_core_power_residue_refines[OF catalog, of "(r + delta) mod 924"]
      table_residue by simp
  show ?thesis
    by (simp only: comma_addsub_entry_core_key_def comma_entry_diagonal_key_def
        Let_def power_residue)
qed

theorem comma_addsub_entry_core_locator_refines:
  assumes admitted: "comma_c1_phase_admitted C"
    and offset: "comma_c1_decode (c1_mod4 C) (c1_mod25 C) \<le> 98"
  shows "\<exists>d eta active residual h.
    comma_addsub_entry_core_key C r delta = (d,eta) \<and>
    comma_entry_port_refined_locator (c1_sector C) d eta =
      Some (active,residual,h) \<and>
    1 \<le> active \<and> active \<le> 9 \<and>
    residual < comma_port_dwell (c1_sector C) active \<and>
    comma_fast_sector_target r
      (Comma_Entry (c1_sector C) delta
        (comma_c1_decode (c1_mod4 C) (c1_mod25 C))) =
      Comma_Near (c1_sector C) delta h"
proof -
  have sector: "1 \<le> c1_sector C" "c1_sector C \<le> 9"
    using admitted by (auto simp: comma_c1_phase_admitted_def)
  have key:
    "comma_addsub_entry_core_key C r delta =
      comma_entry_diagonal_key (c1_sector C) r delta
        (comma_c1_decode (c1_mod4 C) (c1_mod25 C))"
    by (rule comma_addsub_entry_core_key_refines[OF admitted])
  show ?thesis
    by (rule comma_entry_reduced_key_locator_refines_source
      [OF sector offset key])
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "Add/sub Entry core locator bridge"
    ["comma_recursive_core_power_residue_refines",
      "comma_entry_reduced_key_locator_refines_source"]
    @{thms comma_addsub_entry_core_locator_refines}
\<close>

end
