theory Five_Reverse_Wave_Readout
  imports Five_Reverse "Shared_Carry_Dynamics.Reflected_Wave_Readout"
begin

lemma five_reverse_funpow_orbit:
  "((\<lambda>x. 5 * decimal_reverse x) ^^ t) seed = five_reverse_orbit t seed"
  by (induction t) (simp_all add: five_reverse_step_def)

theorem five_reverse_fringe_word_readout:
  fixes grid :: "int \<Rightarrow> int \<Rightarrow> nat"
  assumes digits: "reflected_decimal seed" and canonical: "reflected_trim_high seed = seed"
    and inlet: "\<And>i. grid i (s-i) = reflected_signed_source (rev seed) i"
    and step: "\<And>u v. s<u+v \<Longrightarrow> u+v\<le>s+int (Suc t) \<Longrightarrow>
      grid u v = reflected_alternating_gate 5 (nat (u+v-s-1))
        (grid (u-1) v) (grid u (v-1))"
  defines "raw \<equiv> map (\<lambda>i. grid (int i) (s+int (Suc t)-int i))
    [0..<length seed + Suc t]"
  shows "reflected_msf_value (reflected_wave_physical_readout 5 (Suc t) raw) =
    five_reverse_orbit (Suc t) (decimal_lsd_value seed)"
proof -
  have exact: "reflected_msf_value (reflected_wave_physical_readout 5 (Suc t)
      (map (\<lambda>i. grid (int i) (s+int (Suc t)-int i))
        [0..<length (reflected_me_word 5 (Suc t) (rev seed))])) =
      decimal_lsd_value ((reflected_physical_word 5 ^^ (Suc t)) seed)"
    by (rule reflected_fringe_word_readout[where m=5 and t=t and s=s and grid=grid and seed=seed,
          OF _ digits canonical inlet step]) simp
  have readout: "reflected_msf_value (reflected_wave_physical_readout 5 (Suc t) raw) =
      decimal_lsd_value ((reflected_physical_word 5 ^^ (Suc t)) seed)"
    using exact by (simp only: raw_def reflected_me_word_length length_rev)
  have clock: "decimal_lsd_value ((reflected_physical_word 5 ^^ (Suc t)) seed) =
      ((\<lambda>x. 5 * decimal_reverse x) ^^ (Suc t)) (decimal_lsd_value seed)"
    by (rule reflected_physical_clock_value[where m=5, OF _ digits canonical]) simp
  show ?thesis by (rule trans[OF readout trans[OF clock five_reverse_funpow_orbit]])
qed

ML \<open>
  val checked = @{thms five_reverse_fringe_word_readout};
  val _ = if null (Thm_Deps.all_oracles checked) andalso not (Thm_Deps.has_skip_proof checked)
    then () else error "Five reverse fringe readout proof audit failed";
\<close>

end
