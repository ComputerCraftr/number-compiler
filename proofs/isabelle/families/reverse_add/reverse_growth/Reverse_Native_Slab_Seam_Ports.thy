theory Reverse_Native_Slab_Seam_Ports
  imports Reverse_Native_Slab_Outer_Packet
begin

text \<open>The source interval supplies both physical seam ports and the
four-tick clock. The index bounds below refer to the original physical source;
no intermediate row or selected port is assumed by the caller.\<close>

theorem slab_outer_source_seam_ports:
  assumes valid: "valid_pair (18 # z # rest)"
      and positive: "0 < left"
      and span: "left + 16 \<le> right"
      and upper: "right \<le> length (18 # z # rest)"
      and symbols: "\<And>j. left \<le> j \<Longrightarrow> j < right \<Longrightarrow>
        reverse_native_slab_source_symbol ((18 # z # rest) ! j)"
  shows "slab_core_clock_admitted
      [carry_out False (18 # z # rest),
       carry_out False (step (18 # z # rest)),
       carry_out False (step (step (18 # z # rest))),
       carry_out False (step (step (step (18 # z # rest))))]"
    and "carry_out False (18 # z # rest) \<and>
      carry_out False (step (step (18 # z # rest))) \<and>
      (carry_out False (step (18 # z # rest)) \<noteq>
        carry_out False (step (step (step (18 # z # rest)))))"
    and "length (step (step (step (step (18 # z # rest))))) =
      length (18 # z # rest) + 3"
    and "\<forall>t<4. let row = (step ^^ t) (18 # z # rest);
          fixed = left + 8; middle = right - 12 + t
        in valid_pair row \<and> fixed < length row \<and> middle < length row \<and>
          (if t = 0 then reverse_native_slab_source_symbol (row ! fixed)
            else 9 < row ! fixed) \<and>
          (if t = 0 then reverse_native_slab_source_symbol (row ! middle)
            else 9 < row ! middle)"
proof -
  let ?s = "18 # z # rest"
  let ?s1 = "step ?s"
  let ?s2 = "step ?s1"
  let ?s3 = "step ?s2"
  have admitted: "slab_core_clock_admitted
    [carry_out False ?s, carry_out False ?s1,
     carry_out False ?s2, carry_out False ?s3]"
    by (rule slab_outer_eighteen_physical_clock_admitted[OF valid])
  have growth: "carry_out False ?s"
    using admitted by (auto simp: slab_core_clock_admitted_def)
  have v1: "valid_pair ?s1" by (rule valid_pair_successor[OF valid])
  have v2: "valid_pair ?s2" by (rule valid_pair_successor[OF v1])
  have v3: "valid_pair ?s3" by (rule valid_pair_successor[OF v2])
  have l1: "length ?s1 = length ?s + 1"
    using growth by (simp add: length_digits_exact)
  have l2: "length ?s1 \<le> length ?s2" by (simp add: length_digits_exact)
  have l3: "length ?s2 \<le> length ?s3" by (simp add: length_digits_exact)
  have first: "\<forall>j. left + 1 \<le> j \<and> j < right \<longrightarrow>
      16 \<le> ?s1 ! j \<and> ?s1 ! j \<le> 18"
  proof (rule slab_core_first_source_span[OF valid growth])
    show "0 < left + 1" by simp
    show "right \<le> length ?s" by (rule upper)
    fix j assume lower: "left + 1 - 1 \<le> j" and high: "j < right"
    show "reverse_native_slab_source_symbol (?s ! j)"
      by (rule symbols) (use lower high in arith)+
  qed
  have second: "\<forall>j. left + 2 \<le> j \<and> j < right - 1 \<longrightarrow>
      14 \<le> ?s2 ! j \<and> ?s2 ! j \<le> 18"
  proof (rule slab_core_later_source_span[OF v1])
    show "0 < left + 2" by simp
    show "right - 1 < length ?s1" using upper l1 span by arith
    fix j assume lower: "left + 2 - 1 \<le> j" and high: "j \<le> right - 1"
    have range: "left + 1 \<le> j \<and> j < right"
      using lower high span by arith
    show "16 \<le> ?s1 ! j \<and> ?s1 ! j \<le> 18" using first range by blast
  qed
  have third: "\<forall>j. left + 4 \<le> j \<and> j < right - 3 \<longrightarrow>
      10 \<le> ?s3 ! j \<and> ?s3 ! j \<le> 18"
  proof (rule slab_core_three_physical_rows[OF valid growth])
    show "3 < left + 4" by simp
    show "right - 3 + 2 < length ?s" using upper span by arith
    fix j assume lower: "left + 4 - 3 \<le> j" and high: "j < right - 3 + 2"
    show "reverse_native_slab_source_symbol (?s ! j)"
      by (rule symbols) (use lower high span in arith)+
  qed
  show "slab_core_clock_admitted
      [carry_out False ?s, carry_out False ?s1,
       carry_out False ?s2, carry_out False ?s3]" by (rule admitted)
  show "carry_out False ?s \<and> carry_out False ?s2 \<and>
      (carry_out False ?s1 \<noteq> carry_out False ?s3)"
    using admitted by (auto simp: slab_core_clock_admitted_def)
  show "length (step (step (step (step ?s)))) = length ?s + 3"
    using admitted by (auto simp: slab_core_clock_admitted_def length_digits_exact)
  show "\<forall>t<4. let row = (step ^^ t) ?s; fixed = left + 8; middle = right - 12 + t
        in valid_pair row \<and> fixed < length row \<and> middle < length row \<and>
          (if t = 0 then reverse_native_slab_source_symbol (row ! fixed)
            else 9 < row ! fixed) \<and>
          (if t = 0 then reverse_native_slab_source_symbol (row ! middle)
            else 9 < row ! middle)"
  proof (intro allI impI)
    fix t :: nat assume t: "t < 4"
    have choice: "t = 0 \<or> t = 1 \<or> t = 2 \<or> t = 3" using t by arith
    have sf: "reverse_native_slab_source_symbol (?s ! (left + 8))"
      by (rule symbols) (use span in arith)+
    have sm: "reverse_native_slab_source_symbol (?s ! (right - 12))"
      by (rule symbols) (use span in arith)+
    have r1f: "left + 1 \<le> left + 8 \<and> left + 8 < right"
      using span by arith
    have r1m: "left + 1 \<le> right - 12 + 1 \<and> right - 12 + 1 < right"
      using span by arith
    have r2f: "left + 2 \<le> left + 8 \<and> left + 8 < right - 1"
      using span by arith
    have r2m: "left + 2 \<le> right - 12 + 2 \<and> right - 12 + 2 < right - 1"
      using span by arith
    have r3f: "left + 4 \<le> left + 8 \<and> left + 8 < right - 3"
      using span by arith
    have r3m: "left + 4 \<le> right - 12 + 3 \<and> right - 12 + 3 < right - 3"
      using span by arith
    have f1: "16 \<le> ?s1 ! (left + 8) \<and> ?s1 ! (left + 8) \<le> 18"
      using first r1f by blast
    have m1: "16 \<le> ?s1 ! (right - 12 + 1) \<and> ?s1 ! (right - 12 + 1) \<le> 18"
      using first r1m by blast
    have f2: "14 \<le> ?s2 ! (left + 8) \<and> ?s2 ! (left + 8) \<le> 18"
      using second r2f by blast
    have m2: "14 \<le> ?s2 ! (right - 12 + 2) \<and> ?s2 ! (right - 12 + 2) \<le> 18"
      using second r2m by blast
    have f3: "10 \<le> ?s3 ! (left + 8) \<and> ?s3 ! (left + 8) \<le> 18"
      using third r3f by blast
    have m3: "10 \<le> ?s3 ! (right - 12 + 3) \<and> ?s3 ! (right - 12 + 3) \<le> 18"
      using third r3m by blast
    have bounds: "left + 8 < length ?s" "right - 12 < length ?s"
      "right - 12 + 1 < length ?s" "right - 12 + 2 < length ?s"
      "right - 12 + 3 < length ?s" using upper span by arith+
    have case0: "valid_pair ?s \<and> left + 8 < length ?s \<and>
      right - 12 < length ?s \<and> reverse_native_slab_source_symbol (?s ! (left + 8)) \<and>
      reverse_native_slab_source_symbol (?s ! (right - 12))"
      using valid bounds sf sm by auto
    have case1: "valid_pair ?s1 \<and> left + 8 < length ?s1 \<and>
      right - 12 + 1 < length ?s1 \<and> 9 < ?s1 ! (left + 8) \<and>
      9 < ?s1 ! (right - 12 + 1)"
      using v1 bounds l1 f1 m1 by (auto; arith)
    have case2: "valid_pair ?s2 \<and> left + 8 < length ?s2 \<and>
      right - 12 + 2 < length ?s2 \<and> 9 < ?s2 ! (left + 8) \<and>
      9 < ?s2 ! (right - 12 + 2)"
      using v2 bounds l1 l2 f2 m2 by (auto; arith)
    have case3: "valid_pair ?s3 \<and> left + 8 < length ?s3 \<and>
      right - 12 + 3 < length ?s3 \<and> 9 < ?s3 ! (left + 8) \<and>
      9 < ?s3 ! (right - 12 + 3)"
      using v3 bounds l1 l2 l3 f3 m3 by (auto; arith)
    show "let row = (step ^^ t) ?s; fixed = left + 8; middle = right - 12 + t
        in valid_pair row \<and> fixed < length row \<and> middle < length row \<and>
          (if t = 0 then reverse_native_slab_source_symbol (row ! fixed)
            else 9 < row ! fixed) \<and>
          (if t = 0 then reverse_native_slab_source_symbol (row ! middle)
            else 9 < row ! middle)"
      using choice case0 case1 case2 case3
      by (auto simp: Let_def eval_nat_numeral funpow_Suc_right)
  qed
qed

ML \<open>
  val checked = @{thms slab_outer_source_seam_ports};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Native slab seam ports depend on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped native slab seam ports" else ();
\<close>

end
