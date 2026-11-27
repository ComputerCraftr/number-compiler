theory Reverse_Native_Slab_Outer_Packet
  imports Reverse_Native_Slab_Physical_Packet
begin

text \<open>The actual outer source supplies the clock, so the selected
four-tick output and width do not depend on a caller-supplied growth word.\<close>
theorem slab_outer_physical_four_packet:
  assumes valid: "valid_pair (18 # z # rest)" and lower: "5 < i"
    and upper: "i + 4 < length (18 # z # rest)"
    and symbols: "\<And>j. i - 4 \<le> j \<Longrightarrow> j < i + 4 \<Longrightarrow>
      reverse_native_slab_source_symbol ((18 # z # rest) ! j)"
  shows "length (step (step (step (step (18 # z # rest))))) =
      length (18 # z # rest) + 3"
    and "step (step (step (step (18 # z # rest)))) ! i =
      18 - 2 * (slab_core_bit ((18 # z # rest) ! (i - 3) \<noteq> 18) +
        3 * slab_core_bit ((18 # z # rest) ! (i - 2) \<noteq> 18) +
        3 * slab_core_bit ((18 # z # rest) ! (i - 1) \<noteq> 18) +
        slab_core_bit ((18 # z # rest) ! i \<noteq> 18))"
proof -
  let ?s = "18 # z # rest"
  have admitted: "slab_core_clock_admitted
    [carry_out False ?s, carry_out False (step ?s),
     carry_out False (step (step ?s)), carry_out False (step (step (step ?s)))]"
    by (rule slab_outer_eighteen_physical_clock_admitted[OF valid])
  have growth: "carry_out False ?s"
    using admitted by (auto simp: slab_core_clock_admitted_def)
  have clock: "(\<not> carry_out False (step ?s) \<and> carry_out False (step (step ?s)) \<and>
        carry_out False (step (step (step ?s)))) \<or>
      (carry_out False (step ?s) \<and> carry_out False (step (step ?s)) \<and>
        \<not> carry_out False (step (step (step ?s))))"
    using admitted by (auto simp: slab_core_clock_admitted_def)
  show "length (step (step (step (step ?s)))) = length ?s + 3"
    using admitted by (auto simp: slab_core_clock_admitted_def length_digits_exact)
  show "step (step (step (step ?s))) ! i =
      18 - 2 * (slab_core_bit (?s ! (i - 3) \<noteq> 18) +
        3 * slab_core_bit (?s ! (i - 2) \<noteq> 18) +
        3 * slab_core_bit (?s ! (i - 1) \<noteq> 18) +
        slab_core_bit (?s ! i \<noteq> 18))"
    by (rule slab_core_physical_four_packet[OF valid lower upper symbols growth clock])
qed

ML \<open>
  val checked = @{thms slab_outer_physical_four_packet};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Native outer packet oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped native outer packet proof" else ();
\<close>

end
