theory Comma_Targeted_Continue_Power
  imports Comma_Semantic_B1_CRT_Source_Binding Comma_CRT_Phase_Clock
    Comma_CRT_Equivalence
begin

text \<open>
Build a singleton CRT phase selector from the four independent cyclotomic
coordinates.  This small owner is shared by the source-free Continue
observer; the old materialized 46-by-924 continuation power tables have been
removed in favor of the demanded observer construction.
\<close>

definition comma_crt_phase_point :: "nat \<Rightarrow> comma_crt_column" where
  "comma_crt_phase_point phase =
    comma_crt_apply Comma_CRT_And
      (comma_crt_apply Comma_CRT_And
        (comma_crt_source_axis_column 0 4 phase)
        (comma_crt_source_axis_column 1 3 phase))
      (comma_crt_apply Comma_CRT_And
        (comma_crt_source_axis_column 2 7 phase)
        (comma_crt_source_axis_column 3 11 phase))"

lemma comma_crt_phase_point_admitted:
  "comma_crt_admitted 0 (comma_crt_phase_point phase)"
  by (simp add: comma_crt_phase_point_def comma_crt_source_axis_column_admitted
      comma_crt_apply_admitted)

lemma comma_crt_four_residues_iff:
  fixes phase p :: nat
  shows "(phase mod 4=p mod 4 \<and> phase mod 3=p mod 3 \<and>
    phase mod 7=p mod 7 \<and> phase mod 11=p mod 11) \<longleftrightarrow>
    phase mod 924=p mod 924"
proof
  assume residues:
    "phase mod 4=p mod 4 \<and> phase mod 3=p mod 3 \<and>
      phase mod 7=p mod 7 \<and> phase mod 11=p mod 11"
  then have r4: "phase mod 4=p mod 4"
    and r3: "phase mod 3=p mod 3"
    and r7: "phase mod 7=p mod 7"
    and r11: "phase mod 11=p mod 11" by auto
  have clock_equal: "comma_crt_clock phase=comma_crt_clock p"
    by (simp add: comma_crt_clock_def r4 r3 r7 r11)
  show "phase mod 924=p mod 924"
    using clock_equal by (simp only: comma_crt_clock_reconstruct)
next
  assume equal: "phase mod 924=p mod 924"
  have dvd4: "(4::nat) dvd 924" by simp
  have dvd3: "(3::nat) dvd 924" by simp
  have dvd7: "(7::nat) dvd 924" by simp
  have dvd11: "(11::nat) dvd 924" by simp
  have phase4: "(phase mod 924) mod 4=phase mod 4"
    by (rule mod_mod_cancel[OF dvd4])
  have p4: "(p mod 924) mod 4=p mod 4"
    by (rule mod_mod_cancel[OF dvd4])
  have phase3: "(phase mod 924) mod 3=phase mod 3"
    by (rule mod_mod_cancel[OF dvd3])
  have p3: "(p mod 924) mod 3=p mod 3"
    by (rule mod_mod_cancel[OF dvd3])
  have phase7: "(phase mod 924) mod 7=phase mod 7"
    by (rule mod_mod_cancel[OF dvd7])
  have p7: "(p mod 924) mod 7=p mod 7"
    by (rule mod_mod_cancel[OF dvd7])
  have phase11: "(phase mod 924) mod 11=phase mod 11"
    by (rule mod_mod_cancel[OF dvd11])
  have p11: "(p mod 924) mod 11=p mod 11"
    by (rule mod_mod_cancel[OF dvd11])
  have four: "phase mod 4=p mod 4"
    using equal phase4 p4 by simp
  have three: "phase mod 3=p mod 3"
    using equal phase3 p3 by simp
  have seven: "phase mod 7=p mod 7"
    using equal phase7 p7 by simp
  have eleven: "phase mod 11=p mod 11"
    using equal phase11 p11 by simp
  show "phase mod 4=p mod 4 \<and> phase mod 3=p mod 3 \<and>
    phase mod 7=p mod 7 \<and> phase mod 11=p mod 11"
    using four three seven eleven by blast
qed

lemma comma_crt_phase_point_set:
  "comma_crt_set (comma_crt_phase_point p) =
    {phase. phase<924 \<and> phase mod 924=p mod 924}"
proof -
  have a0: "comma_crt_admitted 0 (comma_crt_source_axis_column 0 4 p)"
    by (rule comma_crt_source_axis_column_admitted) simp
  have a1: "comma_crt_admitted 0 (comma_crt_source_axis_column 1 3 p)"
    by (rule comma_crt_source_axis_column_admitted) simp
  have a2: "comma_crt_admitted 0 (comma_crt_source_axis_column 2 7 p)"
    by (rule comma_crt_source_axis_column_admitted) simp
  have a3: "comma_crt_admitted 0 (comma_crt_source_axis_column 3 11 p)"
    by (rule comma_crt_source_axis_column_admitted) simp
  have s0: "comma_crt_set (comma_crt_source_axis_column 0 4 p) =
      {phase. phase<924 \<and> phase mod 4=p mod 4}"
    using comma_crt_source_axis_column_set[of 0 4 p]
    by (simp add: comma_crt_period_def)
  have s1: "comma_crt_set (comma_crt_source_axis_column 1 3 p) =
      {phase. phase<924 \<and> phase mod 3=p mod 3}"
    using comma_crt_source_axis_column_set[of 1 3 p]
    by (simp add: comma_crt_period_def)
  have s2: "comma_crt_set (comma_crt_source_axis_column 2 7 p) =
      {phase. phase<924 \<and> phase mod 7=p mod 7}"
    using comma_crt_source_axis_column_set[of 2 7 p]
    by (simp add: comma_crt_period_def)
  have s3: "comma_crt_set (comma_crt_source_axis_column 3 11 p) =
      {phase. phase<924 \<and> phase mod 11=p mod 11}"
    using comma_crt_source_axis_column_set[of 3 11 p]
    by (simp add: comma_crt_period_def)
  have a01:
      "comma_crt_admitted 0
        (comma_crt_apply Comma_CRT_And
          (comma_crt_source_axis_column 0 4 p)
          (comma_crt_source_axis_column 1 3 p))"
    by (rule comma_crt_apply_admitted[OF a0 a1])
  have a23:
      "comma_crt_admitted 0
        (comma_crt_apply Comma_CRT_And
          (comma_crt_source_axis_column 2 7 p)
          (comma_crt_source_axis_column 3 11 p))"
    by (rule comma_crt_apply_admitted[OF a2 a3])
  have s01:
      "comma_crt_set (comma_crt_apply Comma_CRT_And
          (comma_crt_source_axis_column 0 4 p)
          (comma_crt_source_axis_column 1 3 p)) =
        {phase. phase<924 \<and>
          phase mod 4=p mod 4 \<and> phase mod 3=p mod 3}"
    using comma_crt_apply_and_set[OF a0 a1] s0 s1 by auto
  have s23:
      "comma_crt_set (comma_crt_apply Comma_CRT_And
          (comma_crt_source_axis_column 2 7 p)
          (comma_crt_source_axis_column 3 11 p)) =
        {phase. phase<924 \<and>
          phase mod 7=p mod 7 \<and> phase mod 11=p mod 11}"
    using comma_crt_apply_and_set[OF a2 a3] s2 s3 by auto
  have combined_set:
    "comma_crt_set (comma_crt_phase_point p) =
      comma_crt_set (comma_crt_apply Comma_CRT_And
          (comma_crt_source_axis_column 0 4 p)
          (comma_crt_source_axis_column 1 3 p)) \<inter>
      comma_crt_set (comma_crt_apply Comma_CRT_And
          (comma_crt_source_axis_column 2 7 p)
          (comma_crt_source_axis_column 3 11 p))"
    unfolding comma_crt_phase_point_def
    by (rule comma_crt_apply_and_set[OF a01 a23])
  show ?thesis
  proof (rule set_eqI)
    fix phase :: nat
    show "phase\<in>comma_crt_set (comma_crt_phase_point p) \<longleftrightarrow>
      phase\<in>{phase. phase<924 \<and> phase mod 924=p mod 924}"
    proof
      assume point: "phase\<in>comma_crt_set (comma_crt_phase_point p)"
      have left:
        "phase\<in>comma_crt_set (comma_crt_apply Comma_CRT_And
          (comma_crt_source_axis_column 0 4 p)
          (comma_crt_source_axis_column 1 3 p))"
        and right:
        "phase\<in>comma_crt_set (comma_crt_apply Comma_CRT_And
          (comma_crt_source_axis_column 2 7 p)
          (comma_crt_source_axis_column 3 11 p))"
        using point combined_set by auto
      have phase_bound: "phase<924"
        using left s01 by auto
      have residues:
        "phase mod 4=p mod 4 \<and> phase mod 3=p mod 3 \<and>
          phase mod 7=p mod 7 \<and> phase mod 11=p mod 11"
        using left right s01 s23 by blast
      have clock: "phase mod 924=p mod 924"
        using comma_crt_four_residues_iff residues by blast
      show "phase\<in>{phase. phase<924 \<and> phase mod 924=p mod 924}"
        using phase_bound clock by simp
    next
      assume point: "phase\<in>{phase. phase<924 \<and> phase mod 924=p mod 924}"
      have phase_bound: "phase<924" and clock: "phase mod 924=p mod 924"
        using point by auto
      have residues:
        "phase mod 4=p mod 4 \<and> phase mod 3=p mod 3 \<and>
          phase mod 7=p mod 7 \<and> phase mod 11=p mod 11"
        using comma_crt_four_residues_iff clock by blast
      have r4: "phase mod 4=p mod 4" and r3: "phase mod 3=p mod 3"
        and r7: "phase mod 7=p mod 7" and r11: "phase mod 11=p mod 11"
        using residues by blast+
      have left:
        "phase\<in>comma_crt_set (comma_crt_apply Comma_CRT_And
          (comma_crt_source_axis_column 0 4 p)
          (comma_crt_source_axis_column 1 3 p))"
        using s01 phase_bound r4 r3 by simp
      have right:
        "phase\<in>comma_crt_set (comma_crt_apply Comma_CRT_And
          (comma_crt_source_axis_column 2 7 p)
          (comma_crt_source_axis_column 3 11 p))"
        using s23 phase_bound r7 r11 by simp
      show "phase\<in>comma_crt_set (comma_crt_phase_point p)"
        using combined_set left right by blast
    qed
  qed
qed

ML \<open>
  val published = @{thms
    comma_crt_phase_point_admitted
    comma_crt_phase_point_set
    comma_crt_four_residues_iff}
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "four-residue phase point power" published
\<close>

end
