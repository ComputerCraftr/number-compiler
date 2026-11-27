theory Reverse_Native_Slab_Fourth_Row
  imports Reverse_Native_Slab_Intervals
begin

theorem slab_core_fourth_source_cells:
  assumes valid: "valid_pair source" and growth: "carry_out False source"
      and positive: "4 < lo" and upper: "hi + 3 < length source"
      and symbols: "\<And>j. lo - 4 \<le> j \<Longrightarrow> j < hi + 3 \<Longrightarrow>
        reverse_native_slab_source_symbol (source ! j)"
  defines "third \<equiv> step (step (step source))"
  shows "\<forall>j. lo \<le> j \<and> j < hi \<longrightarrow>
    step third ! j = (if carry_out False third
      then slab_core_birth (third ! (j - 1)) (third ! j)
      else slab_core_quiet (third ! j))"
proof -
  have valid1: "valid_pair (step source)" by (rule valid_pair_successor[OF valid])
  have valid2: "valid_pair (step (step source))" by (rule valid_pair_successor[OF valid1])
  have valid3: "valid_pair third" unfolding third_def by (rule valid_pair_successor[OF valid2])
  have len1: "length source \<le> length (step source)" by (simp add: length_digits_exact)
  have len2: "length (step source) \<le> length (step (step source))" by (simp add: length_digits_exact)
  have len3: "length (step (step source)) \<le> length third" by (simp add: third_def length_digits_exact)
  have interval: "\<forall>j. lo - 1 \<le> j \<and> j < hi + 1 \<longrightarrow>
      10 \<le> third ! j \<and> third ! j \<le> 18"
  proof (unfold third_def, rule slab_core_three_physical_rows[OF valid growth])
    show "3 < lo - 1" using positive by arith
    show "hi + 1 + 2 < length source" using upper by arith
    fix j assume lower: "lo - 1 - 3 \<le> j" and high: "j < hi + 1 + 2"
    show "reverse_native_slab_source_symbol (source ! j)"
      by (rule symbols) (use lower high in arith)+
  qed
  show ?thesis
  proof (intro allI impI)
    fix j assume range: "lo \<le> j \<and> j < hi"
    have positivej: "0 < j" using range positive by arith
    have boundj: "Suc j < length third" using range upper len1 len2 len3 by arith
    have leftrange: "lo - 1 \<le> j - 1 \<and> j - 1 < hi + 1" using range positive by arith
    have middlerange: "lo - 1 \<le> j \<and> j < hi + 1" using range positive by arith
    have rightrange: "lo - 1 \<le> Suc j \<and> Suc j < hi + 1" using range positive by arith
    have left: "10 \<le> third ! (j - 1)" using interval leftrange by blast
    have middle: "10 \<le> third ! j" using interval middlerange by blast
    have right: "10 \<le> third ! Suc j" using interval rightrange by blast
    show "step third ! j = (if carry_out False third
      then slab_core_birth (third ! (j - 1)) (third ! j)
      else slab_core_quiet (third ! j))"
      by (rule slab_core_physical_step_at[OF valid3 positivej boundj left middle right])
  qed
qed

ML \<open>
  val checked = @{thms slab_core_fourth_source_cells};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Native slab fourth-row oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped native slab fourth-row proof" else ();
\<close>

end
