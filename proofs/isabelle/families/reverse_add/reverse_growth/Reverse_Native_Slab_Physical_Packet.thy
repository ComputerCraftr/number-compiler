theory Reverse_Native_Slab_Physical_Packet
  imports Reverse_Native_Slab_Fourth_Row Reverse_Native_Slab_Clock_Guard
begin

lemma slab_core_birth_commute:
  "slab_core_birth a b = slab_core_birth b a"
  by (simp add: slab_core_birth_def reverse_native_slab_birth_def add.commute)

text \<open>The checked source bounds support the indexed physical step over a
whole interval.  The carry is the one computed from that exact row.\<close>
lemma slab_core_step_interval_equations:
  assumes valid: "valid_pair row" and positive: "0 < lo" and upper: "hi < length row"
    and core: "\<And>j. lo - 1 \<le> j \<Longrightarrow> j \<le> hi \<Longrightarrow> 10 \<le> row ! j"
  shows "\<forall>j. lo \<le> j \<and> j < hi \<longrightarrow>
    step row ! j = (if carry_out False row then slab_core_birth (row ! (j - 1)) (row ! j)
      else slab_core_quiet (row ! j))"
proof (intro allI impI)
  fix j assume range: "lo \<le> j \<and> j < hi"
  have pos: "0 < j" and bound: "Suc j < length row" using range positive upper by arith+
  have left: "10 \<le> row ! (j - 1)" by (rule core) (use range positive in arith)+
  have mid: "10 \<le> row ! j" by (rule core) (use range positive in arith)+
  have right: "10 \<le> row ! Suc j" by (rule core) (use range positive in arith)+
  show "step row ! j = (if carry_out False row then slab_core_birth (row ! (j - 1)) (row ! j)
      else slab_core_quiet (row ! j))"
    by (rule slab_core_physical_step_at[OF valid pos bound left mid right])
qed

lemma slab_core_first_interval_equations:
  assumes valid: "valid_pair source" and growth: "carry_out False source"
      and positive: "0 < lo" and upper: "hi \<le> length source"
      and symbols: "\<And>j. lo - 1 \<le> j \<Longrightarrow> j < hi \<Longrightarrow>
        reverse_native_slab_source_symbol (source ! j)"
  shows "\<forall>j. lo \<le> j \<and> j < hi \<longrightarrow>
    step source ! j = slab_core_initial (source ! (j - 1) \<noteq> 18) (source ! j \<noteq> 18)"
proof (intro allI impI)
  fix j assume range: "lo \<le> j \<and> j < hi"
  have pos: "0 < j" and bound: "j < length source" using range positive upper by arith+
  have left: "reverse_native_slab_source_symbol (source ! (j - 1))"
    by (rule symbols) (use range positive in arith)+
  have here: "reverse_native_slab_source_symbol (source ! j)"
    by (rule symbols) (use range positive in arith)+
  show "step source ! j = slab_core_initial (source ! (j - 1) \<noteq> 18) (source ! j \<noteq> 18)"
    by (rule slab_core_physical_first_birth_at[OF valid pos bound left here growth])
qed

text \<open>For an authenticated resetting collar, the four physical rows
select the two closed packets using the source's actual carry clock.\<close>
lemma slab_core_1010_packet:
  fixes b c d :: bool
  shows "slab_core_quiet (slab_core_birth
      (slab_core_quiet (slab_core_initial b c))
      (slab_core_quiet (slab_core_initial c d))) =
    18 - 4 * (slab_core_bit b + 2 * slab_core_bit c + slab_core_bit d)"
  unfolding slab_core_initial_def slab_core_bit_def slab_core_birth_def
    slab_core_quiet_def reverse_native_slab_birth_def reverse_native_slab_quiet_def
    reverse_native_slab_digit_def carry_bit_def
  by (cases b; cases c; cases d; simp_all)

lemma slab_core_1001_packet:
  fixes b c d :: bool
  shows "slab_core_birth
      (slab_core_quiet (slab_core_quiet (slab_core_initial b c)))
      (slab_core_quiet (slab_core_quiet (slab_core_initial c d))) =
    18 - 4 * (slab_core_bit b + 2 * slab_core_bit c + slab_core_bit d)"
  unfolding slab_core_initial_def slab_core_bit_def slab_core_birth_def
    slab_core_quiet_def reverse_native_slab_birth_def reverse_native_slab_quiet_def
    reverse_native_slab_digit_def carry_bit_def
  by (cases b; cases c; cases d; simp_all)

lemma slab_core_1100_packet:
  fixes b c d :: bool
  shows "slab_core_quiet (slab_core_quiet (slab_core_birth
      (slab_core_initial b c) (slab_core_initial c d))) =
    18 - 4 * (slab_core_bit b + 2 * slab_core_bit c + slab_core_bit d)"
  unfolding slab_core_initial_def slab_core_bit_def slab_core_birth_def
    slab_core_quiet_def reverse_native_slab_birth_def reverse_native_slab_quiet_def
    reverse_native_slab_digit_def carry_bit_def
  by (cases b; cases c; cases d; simp_all)

lemma slab_core_1000_packet:
  fixes c d :: bool
  shows "slab_core_quiet (slab_core_quiet (slab_core_quiet
    (slab_core_initial c d))) =
    18 - 8 * (slab_core_bit c + slab_core_bit d)"
  unfolding slab_core_initial_def slab_core_bit_def
    slab_core_quiet_def reverse_native_slab_quiet_def
    reverse_native_slab_digit_def carry_bit_def
  by (cases c; cases d; simp_all)

theorem slab_core_physical_four_packets:
  assumes valid: "valid_pair source" and lower: "5 < i" and upper: "i + 4 < length source"
    and symbols: "\<And>j. i - 4 \<le> j \<Longrightarrow> j < i + 4 \<Longrightarrow>
      reverse_native_slab_source_symbol (source ! j)"
    and growth: "carry_out False source"

  defines "s1 \<equiv> step source" and "s2 \<equiv> step (step source)" and "s3 \<equiv> step (step (step source))"
    and "a \<equiv> source ! (i - 3) \<noteq> 18"
    and "b \<equiv> source ! (i - 2) \<noteq> 18"
    and "c \<equiv> source ! (i - 1) \<noteq> 18"
    and "d \<equiv> source ! i \<noteq> 18"
  shows "(((\<not> carry_out False (step source) \<and> carry_out False (step (step source)) \<and> carry_out False (step (step (step source)))) \<or>
       (carry_out False (step source) \<and> carry_out False (step (step source)) \<and> \<not> carry_out False (step (step (step source))))) \<longrightarrow> step s3 ! i = 18 - 2 * (slab_core_bit a + 3 * slab_core_bit b +
      3 * slab_core_bit c + slab_core_bit d)) \<and>
    (((\<not> carry_out False (step source) \<and> carry_out False (step (step source)) \<and> \<not> carry_out False (step (step (step source)))) \<or>
      (\<not> carry_out False (step source) \<and> \<not> carry_out False (step (step source)) \<and> carry_out False (step (step (step source)))) \<or>
      (carry_out False (step source) \<and> \<not> carry_out False (step (step source)) \<and> \<not> carry_out False (step (step (step source))))) \<longrightarrow> step s3 ! i = 18 - 4 * (slab_core_bit b + 2 * slab_core_bit c + slab_core_bit d)) \<and>
    ((\<not> carry_out False (step source) \<and> (\<not> carry_out False (step (step source)) \<and> \<not> carry_out False (step (step (step source))))) \<longrightarrow>
      step s3 ! i = 18 - 8 * (slab_core_bit c + slab_core_bit d))"
proof -
  have valid1: "valid_pair s1" unfolding s1_def by (rule valid_pair_successor[OF valid])
  have valid2: "valid_pair s2" using valid_pair_successor[OF valid1] by (simp add: s2_def s1_def)
  have valid3: "valid_pair s3" using valid_pair_successor[OF valid2] by (simp add: s3_def s2_def)
  have len1: "length source \<le> length s1" by (simp add: s1_def length_digits_exact)
  have len2: "length s1 \<le> length s2" by (simp add: s2_def s1_def length_digits_exact)
  have len3: "length s2 \<le> length s3" by (simp add: s3_def s2_def length_digits_exact)
  have first: "\<forall>j. i - 3 \<le> j \<and> j < i + 3 \<longrightarrow> 16 \<le> s1 ! j \<and> s1 ! j \<le> 18"
  proof (unfold s1_def, rule slab_core_first_source_span[OF valid growth])
    show "0 < i - 3" using lower by arith
    show "i + 3 \<le> length source" using upper by arith
    fix j assume l: "i - 3 - 1 \<le> j" and h: "j < i + 3"
    show "reverse_native_slab_source_symbol (source ! j)" by (rule symbols) (use l h in arith)+
  qed
  have second: "\<forall>j. i - 2 \<le> j \<and> j < i + 2 \<longrightarrow> 14 \<le> s2 ! j \<and> s2 ! j \<le> 18"
  proof (unfold s2_def, fold s1_def, rule slab_core_later_source_span[OF valid1])
    show "0 < i - 2" using lower by arith
    show "i + 2 < length s1" using upper len1 by arith
    fix j assume l: "i - 2 - 1 \<le> j" and h: "j \<le> i + 2"
    show "16 \<le> s1 ! j \<and> s1 ! j \<le> 18" using first l h by (auto; arith)
  qed
  have third: "\<forall>j. i - 1 \<le> j \<and> j < i + 2 \<longrightarrow> 10 \<le> s3 ! j \<and> s3 ! j \<le> 18"
  proof (unfold s3_def s2_def s1_def, rule slab_core_three_physical_rows[OF valid growth])
    show "3 < i - 1" using lower by arith
    show "i + 2 + 2 < length source" using upper by arith
    fix j assume l: "i - 1 - 3 \<le> j" and h: "j < i + 2 + 2"
    show "reverse_native_slab_source_symbol (source ! j)" by (rule symbols) (use l h in arith)+
  qed
  have e1: "\<forall>j. i - 2 \<le> j \<and> j < i + 1 \<longrightarrow>
    s1 ! j = slab_core_initial (source ! (j - 1) \<noteq> 18) (source ! j \<noteq> 18)"
  proof (unfold s1_def, rule slab_core_first_interval_equations[OF valid growth])
    show "0 < i - 2" using lower by arith
    show "i + 1 \<le> length source" using upper by arith
    fix j assume l: "i - 2 - 1 \<le> j" and h: "j < i + 1"
    show "reverse_native_slab_source_symbol (source ! j)" by (rule symbols) (use l h in arith)+
  qed
  have e2: "\<forall>j. i - 2 \<le> j \<and> j < i + 1 \<longrightarrow>
    s2 ! j = (if carry_out False s1 then slab_core_birth (s1 ! (j - 1)) (s1 ! j) else slab_core_quiet (s1 ! j))"
  proof (unfold s2_def, fold s1_def, rule slab_core_step_interval_equations[OF valid1])
    show "0 < i - 2" using lower by arith
    show "i + 1 < length s1" using upper len1 by arith
    fix j assume l: "i - 2 - 1 \<le> j" and h: "j \<le> i + 1"
    show "10 \<le> s1 ! j" using first l h by (auto; arith)
  qed
  have e3: "\<forall>j. i - 1 \<le> j \<and> j < i + 1 \<longrightarrow>
    s3 ! j = (if carry_out False s2 then slab_core_birth (s2 ! (j - 1)) (s2 ! j) else slab_core_quiet (s2 ! j))"
  proof (unfold s3_def, fold s2_def, rule slab_core_step_interval_equations[OF valid2])
    show "0 < i - 1" using lower by arith
    show "i + 1 < length s2" using upper len1 len2 by arith
    fix j assume l: "i - 1 - 1 \<le> j" and h: "j \<le> i + 1"
    have range: "i - 2 \<le> j \<and> j < i + 2" using l h lower by arith
    have bounded: "14 \<le> s2 ! j \<and> s2 ! j \<le> 18"
      by (rule second[rule_format, OF range])
    show "10 \<le> s2 ! j" using bounded[THEN conjunct1] by arith
  qed
  have e4: "step s3 ! i = (if carry_out False s3 then slab_core_birth (s3 ! (i - 1)) (s3 ! i) else slab_core_quiet (s3 ! i))"
    by (rule slab_core_physical_step_at[OF valid3]) (use lower upper len1 len2 len3 third in \<open>auto; arith\<close>)+
  have r0: "i - 2 \<le> i - 2 \<and> i - 2 < i + 1" using lower by arith
  have r1: "i - 2 \<le> i - 1 \<and> i - 1 < i + 1" using lower by arith
  have r2: "i - 2 \<le> i \<and> i < i + 1" by arith
  have t1: "i - 1 \<le> i - 1 \<and> i - 1 < i + 1" using lower by arith
  have t2: "i - 1 \<le> i \<and> i < i + 1" by arith
  have index1: "(i - 1) - 1 = i - 2" by arith
  have index2: "(i - 2) - 1 = i - 3" by arith
  have a1: "s1 ! (i - 2) = slab_core_initial a b"
    using e1[rule_format, OF r0] by (simp only: index2 a_def b_def)
  have b1: "s1 ! (i - 1) = slab_core_initial b c"
    using e1[rule_format, OF r1] by (simp only: index1 b_def c_def)
  have c1: "s1 ! i = slab_core_initial c d"
    using e1[rule_format, OF r2] by (simp add: c_def d_def)
  have z2: "s2 ! (i - 2) = (if carry_out False s1 then slab_core_birth (s1 ! (i - 3)) (s1 ! (i - 2)) else slab_core_quiet (s1 ! (i - 2)))"
    using e2[rule_format, OF r0] by (simp only: index2)
  have a2: "s2 ! (i - 1) = (if carry_out False s1 then slab_core_birth (s1 ! (i - 2)) (s1 ! (i - 1)) else slab_core_quiet (s1 ! (i - 1)))"
    using e2[rule_format, OF r1] by (simp only: index1)
  have b2: "s2 ! i = (if carry_out False s1 then slab_core_birth (s1 ! (i - 1)) (s1 ! i) else slab_core_quiet (s1 ! i))"
    using e2[rule_format, OF r2] by simp
  have a3: "s3 ! (i - 1) = (if carry_out False s2 then slab_core_birth (s2 ! (i - 2)) (s2 ! (i - 1)) else slab_core_quiet (s2 ! (i - 1)))"
    using e3[rule_format, OF t1] by (simp only: index1)
  have b3: "s3 ! i = (if carry_out False s2 then slab_core_birth (s2 ! (i - 1)) (s2 ! i) else slab_core_quiet (s2 ! i))"
    using e3[rule_format, OF t2] by simp
  show ?thesis
    using e4 a1 b1 c1 z2 a2 b2 a3 b3
      slab_core_1011_packet[where a=a and b=b and c=c and d=d]
      slab_core_1110_packet[where a=a and b=b and c=c and d=d]
      slab_core_1010_packet[where b=b and c=c and d=d]
      slab_core_1001_packet[where b=b and c=c and d=d]
      slab_core_1100_packet[where b=b and c=c and d=d]
      slab_core_1000_packet[where c=c and d=d]
    by (auto simp: slab_core_birth_commute s1_def s2_def s3_def)
qed

theorem slab_core_physical_four_packet:
  assumes valid: "valid_pair source" and lower: "5 < i" and upper: "i + 4 < length source"
    and symbols: "\<And>j. i - 4 \<le> j \<Longrightarrow> j < i + 4 \<Longrightarrow>
      reverse_native_slab_source_symbol (source ! j)"
    and growth: "carry_out False source"
    and clock: "(\<not> carry_out False (step source) \<and> carry_out False (step (step source)) \<and> carry_out False (step (step (step source)))) \<or>
       (carry_out False (step source) \<and> carry_out False (step (step source)) \<and> \<not> carry_out False (step (step (step source))))"
  defines "s1 \<equiv> step source" and "s2 \<equiv> step (step source)" and "s3 \<equiv> step (step (step source))"
    and "a \<equiv> source ! (i - 3) \<noteq> 18"
    and "b \<equiv> source ! (i - 2) \<noteq> 18"
    and "c \<equiv> source ! (i - 1) \<noteq> 18"
    and "d \<equiv> source ! i \<noteq> 18"
  shows "step s3 ! i = 18 - 2 * (slab_core_bit a + 3 * slab_core_bit b +
      3 * slab_core_bit c + slab_core_bit d)"
  using slab_core_physical_four_packets[OF valid lower upper symbols growth] clock
  by (simp add: s1_def s2_def s3_def a_def b_def c_def d_def)

ML \<open>
  val checked = @{thms slab_core_birth_commute slab_core_step_interval_equations slab_core_first_interval_equations slab_core_physical_four_packet};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Native slab packet oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped native slab packet proof" else ();
\<close>
end
