theory Reverse_Native_Slab_Intervals
  imports Reverse_Native_Slab_Indexed
begin

lemma slab_core_initial_bounds:
  "16 \<le> slab_core_initial a b \<and> slab_core_initial a b \<le> 18"
  by (cases a; cases b; simp add: slab_core_initial_def slab_core_bit_def)

theorem slab_core_first_source_span:
  assumes valid: "valid_pair source" and growth: "carry_out False source"
      and positive: "0 < lo" and upper: "hi \<le> length source"
      and symbols: "\<And>j. lo - 1 \<le> j \<Longrightarrow> j < hi \<Longrightarrow>
        reverse_native_slab_source_symbol (source ! j)"
  shows "\<forall>j. lo \<le> j \<and> j < hi \<longrightarrow>
    16 \<le> step source ! j \<and> step source ! j \<le> 18"
proof (intro allI impI)
  fix j assume range: "lo \<le> j \<and> j < hi"
  have jpos: "0 < j" using range positive by arith
  have jbound: "j < length source" using range upper by arith
  have prev: "lo - 1 \<le> j - 1" using range positive by arith
  have left: "reverse_native_slab_source_symbol (source ! (j - 1))"
    by (rule symbols[OF prev]) (use range in arith)
  have here_lower: "lo - 1 \<le> j" using range positive by arith
  have here: "reverse_native_slab_source_symbol (source ! j)"
    by (rule symbols[OF here_lower]) (use range in simp)
  have equation: "step source ! j =
      slab_core_initial (source ! (j - 1) \<noteq> 18) (source ! j \<noteq> 18)"
    by (rule slab_core_physical_first_birth_at[OF valid jpos jbound left here growth])
  show "16 \<le> step source ! j \<and> step source ! j \<le> 18"
    using slab_core_initial_bounds[of "source ! (j - 1) \<noteq> 18" "source ! j \<noteq> 18"] equation by simp
qed

theorem slab_core_later_source_span:
  assumes valid: "valid_pair source" and positive: "0 < lo" and upper: "hi < length source"
      and core: "\<And>j. lo - 1 \<le> j \<Longrightarrow> j \<le> hi \<Longrightarrow>
        16 \<le> source ! j \<and> source ! j \<le> 18"
  shows "\<forall>j. lo \<le> j \<and> j < hi \<longrightarrow>
    14 \<le> step source ! j \<and> step source ! j \<le> 18"
proof (intro allI impI)
  fix j assume range: "lo \<le> j \<and> j < hi"
  have jpos: "0 < j" using range positive by arith
  have jbound: "Suc j < length source" using range upper by arith
  have prev: "lo - 1 \<le> j - 1" "j - 1 \<le> hi" using range positive by arith+
  have here: "lo - 1 \<le> j" "j \<le> hi" using range positive by arith+
  have next_bounds: "lo - 1 \<le> Suc j" "Suc j \<le> hi" using range positive by arith+
  have left: "16 \<le> source ! (j - 1) \<and> source ! (j - 1) \<le> 18"
    by (rule core[OF prev])
  have middle: "16 \<le> source ! j \<and> source ! j \<le> 18" by (rule core[OF here])
  have right: "16 \<le> source ! Suc j \<and> source ! Suc j \<le> 18" by (rule core[OF next_bounds])
  have equation: "step source ! j = (if carry_out False source
      then slab_core_birth (source ! (j - 1)) (source ! j)
      else slab_core_quiet (source ! j))"
    by (rule slab_core_physical_step_at[OF valid jpos jbound]) (use left middle right in arith)+
  show "14 \<le> step source ! j \<and> step source ! j \<le> 18"
    using slab_core_second_reset[of "source ! (j - 1)" "source ! j"]
      slab_core_second_reset[of "source ! j" "source ! j"] left middle equation by auto
qed

theorem slab_core_third_source_span:
  assumes valid: "valid_pair source" and positive: "0 < lo" and upper: "hi < length source"
      and core: "\<And>j. lo - 1 \<le> j \<Longrightarrow> j \<le> hi \<Longrightarrow>
        14 \<le> source ! j \<and> source ! j \<le> 18"
  shows "\<forall>j. lo \<le> j \<and> j < hi \<longrightarrow>
    10 \<le> step source ! j \<and> step source ! j \<le> 18"
proof (intro allI impI)
  fix j assume range: "lo \<le> j \<and> j < hi"
  have jpos: "0 < j" using range positive by arith
  have jbound: "Suc j < length source" using range upper by arith
  have prev: "lo - 1 \<le> j - 1" "j - 1 \<le> hi" using range positive by arith+
  have here: "lo - 1 \<le> j" "j \<le> hi" using range positive by arith+
  have next_bounds: "lo - 1 \<le> Suc j" "Suc j \<le> hi" using range positive by arith+
  have left: "14 \<le> source ! (j - 1) \<and> source ! (j - 1) \<le> 18"
    by (rule core[OF prev])
  have middle: "14 \<le> source ! j \<and> source ! j \<le> 18" by (rule core[OF here])
  have right: "14 \<le> source ! Suc j \<and> source ! Suc j \<le> 18" by (rule core[OF next_bounds])
  have equation: "step source ! j = (if carry_out False source
      then slab_core_birth (source ! (j - 1)) (source ! j)
      else slab_core_quiet (source ! j))"
    by (rule slab_core_physical_step_at[OF valid jpos jbound]) (use left middle right in arith)+
  show "10 \<le> step source ! j \<and> step source ! j \<le> 18"
    using slab_core_third_reset[of "source ! (j - 1)" "source ! j"]
      slab_core_third_reset[of "source ! j" "source ! j"] left middle equation by auto
qed

text \<open>Three actual physical rows retain resetting coefficients on a
shrinking source interval.  The statement uses the original source symbols,
validity and the source's actual first growth bit; it does not assume an
endpoint or an independently supplied carry word.\<close>

theorem slab_core_three_physical_rows:
  assumes valid: "valid_pair source" and growth: "carry_out False source"
      and positive: "3 < lo" and upper: "hi + 2 < length source"
      and symbols: "\<And>j. lo - 3 \<le> j \<Longrightarrow> j < hi + 2 \<Longrightarrow>
        reverse_native_slab_source_symbol (source ! j)"
  shows "\<forall>j. lo \<le> j \<and> j < hi \<longrightarrow>
    10 \<le> (step (step (step source))) ! j \<and>
      (step (step (step source))) ! j \<le> 18"
proof -
  let ?s1 = "step source"
  let ?s2 = "step ?s1"
  have valid1: "valid_pair ?s1" by (rule valid_pair_successor[OF valid])
  have valid2: "valid_pair ?s2" by (rule valid_pair_successor[OF valid1])
  have len1: "length source \<le> length ?s1" by (simp add: length_digits_exact)
  have len2: "length ?s1 \<le> length ?s2" by (simp add: length_digits_exact)
  have first: "\<forall>j. lo - 2 \<le> j \<and> j < hi + 2 \<longrightarrow>
      16 \<le> ?s1 ! j \<and> ?s1 ! j \<le> 18"
  proof (rule slab_core_first_source_span[OF valid growth])
    show "0 < lo - 2" using positive by arith
    show "hi + 2 \<le> length source" using upper by arith
    fix j assume lower: "lo - 2 - 1 \<le> j" and high: "j < hi + 2"
    show "reverse_native_slab_source_symbol (source ! j)"
      by (rule symbols) (use lower high in arith)+
  qed
  have second: "\<forall>j. lo - 1 \<le> j \<and> j < hi + 1 \<longrightarrow>
      14 \<le> ?s2 ! j \<and> ?s2 ! j \<le> 18"
  proof (rule slab_core_later_source_span[OF valid1])
    show "0 < lo - 1" using positive by arith
    show "hi + 1 < length ?s1" using upper len1 by arith
    fix j assume lower: "lo - 1 - 1 \<le> j" and high: "j \<le> hi + 1"
    have range: "lo - 2 \<le> j \<and> j < hi + 2" using lower high by arith
    show "16 \<le> ?s1 ! j \<and> ?s1 ! j \<le> 18"
      using first range by blast
  qed
  show ?thesis
  proof (rule slab_core_third_source_span[OF valid2])
    show "0 < lo" using positive by arith
    show "hi < length ?s2" using upper len1 len2 by arith
    fix j assume lower: "lo - 1 \<le> j" and high: "j \<le> hi"
    have range: "lo - 1 \<le> j \<and> j < hi + 1" using lower high by arith
    show "14 \<le> ?s2 ! j \<and> ?s2 ! j \<le> 18"
      using second range by blast
  qed
qed

ML \<open>
  val checked = @{thms slab_core_initial_bounds slab_core_first_source_span slab_core_later_source_span slab_core_third_source_span slab_core_three_physical_rows};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Native slab interval oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped native slab interval proof" else ();
\<close>

end
