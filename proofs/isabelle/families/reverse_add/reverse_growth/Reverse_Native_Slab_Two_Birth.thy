theory Reverse_Native_Slab_Two_Birth
  imports Reverse_Native_Slab_Physical_Packet
begin

theorem slab_core_physical_four_two_birth:
  assumes valid: "valid_pair source" and lower: "5 < i" and upper: "i + 4 < length source"
    and symbols: "\<And>j. i - 4 \<le> j \<Longrightarrow> j < i + 4 \<Longrightarrow>
      reverse_native_slab_source_symbol (source ! j)"
    and growth: "carry_out False source"
    and clock: "(\<not> carry_out False (step source) \<and> carry_out False (step (step source)) \<and> \<not> carry_out False (step (step (step source)))) \<or>
      (\<not> carry_out False (step source) \<and> \<not> carry_out False (step (step source)) \<and> carry_out False (step (step (step source)))) \<or>
      (carry_out False (step source) \<and> \<not> carry_out False (step (step source)) \<and> \<not> carry_out False (step (step (step source))))"
  defines "s1 \<equiv> step source" and "s2 \<equiv> step (step source)" and "s3 \<equiv> step (step (step source))"
    and "a \<equiv> source ! (i - 3) \<noteq> 18"
    and "b \<equiv> source ! (i - 2) \<noteq> 18"
    and "c \<equiv> source ! (i - 1) \<noteq> 18"
    and "d \<equiv> source ! i \<noteq> 18"
  shows "step s3 ! i = 18 - 4 * (slab_core_bit b + 2 * slab_core_bit c + slab_core_bit d)"
  using slab_core_physical_four_packets[OF valid lower upper symbols growth] clock
  by (simp add: s1_def s2_def s3_def a_def b_def c_def d_def)

ML \<open>
  val checked = @{thms slab_core_physical_four_two_birth};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Native slab 1010 oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped native slab 1010 proof" else ();
\<close>
end
