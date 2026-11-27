theory Double_Reverse_Reflected_Physical
  imports Double_Reverse_Four_Port_Numeric_Refinement
    "Shared_Carry_Dynamics.Reflected_Wave_Readout"
begin

theorem double_reverse_physical_word_one_step:
  assumes "list_all (\<lambda>digit. digit < 10) source"
    "source \<noteq> []" "last source > 0"
  shows "decimal_lsd_value (reflected_physical_word 2 source) =
    double_reverse_T (decimal_lsd_value source)"
  using reflected_physical_word_one_step[OF assms, of 2]
  by (simp only: double_reverse_T_def)

theorem double_reverse_prefix_fringe_readout:
  fixes grid :: "int \<Rightarrow> int \<Rightarrow> nat"
  assumes digits: "reflected_decimal entry" and canonical: "reflected_trim_high entry = entry"
    and prefix: "decimal_lsd_value entry = (double_reverse_T ^^ p) source"
    and inlet: "\<And>i. grid i (s-i) = reflected_signed_source (rev entry) i"
    and step: "\<And>u v. s<u+v \<Longrightarrow> u+v\<le>s+int (Suc t) \<Longrightarrow>
      grid u v = reflected_alternating_gate 2 (nat (u+v-s-1))
        (grid (u-1) v) (grid u (v-1))"
  shows "reflected_msf_value (reflected_wave_physical_readout 2 (Suc t)
    (map (\<lambda>i. grid (int i) (s+int (Suc t)-int i)) [0..<length entry + Suc t])) =
    (double_reverse_T ^^ (p + Suc t)) source"
proof -
  have two: "(2::nat)=2 \<or> 2=5" by simp
  have readout: "reflected_msf_value (reflected_wave_physical_readout 2 (Suc t)
      (map (\<lambda>i. grid (int i) (s+int (Suc t)-int i))
        [0..<length (reflected_me_word 2 (Suc t) (rev entry))])) =
      decimal_lsd_value ((reflected_physical_word 2 ^^ Suc t) entry)"
    by (rule reflected_fringe_word_readout[where m=2 and t=t and s=s and grid=grid and seed=entry,
          OF _ digits canonical inlet step]) simp_all
  note clock = reflected_physical_clock_value[where m=2 and ticks="Suc t", OF two digits canonical]
  have combine: "(double_reverse_T ^^ (p + Suc t)) source =
      (double_reverse_T ^^ Suc t) ((double_reverse_T ^^ p) source)"
    by (subst add.commute) (simp only: funpow_add comp_apply)
  have law: "double_reverse_T = (\<lambda>x. 2 * decimal_reverse x)"
    by (rule ext) (simp only: double_reverse_T_def)
  have final: "(double_reverse_T ^^ (p + Suc t)) source =
      ((\<lambda>x. 2 * decimal_reverse x) ^^ Suc t) (decimal_lsd_value entry)"
    unfolding combine by (simp only: law prefix)
  show ?thesis unfolding final
    using trans[OF readout clock] by (simp only: reflected_me_word_length length_rev)
qed

ML \<open>
  val checked = @{thms double_reverse_lsf_value_shared
    reflected_physical_word_one_step double_reverse_physical_word_one_step double_reverse_prefix_fringe_readout};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected physical source proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected physical source proof" else ();
\<close>

end
