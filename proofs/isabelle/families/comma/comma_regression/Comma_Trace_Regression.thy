theory Comma_Trace_Regression
  imports Comma_Cylinder.Comma_Finite_Transition
begin

lemma comma_finite_first_period:
  "comma_finite_period 2 1 = 260"
  by (simp add: comma_finite_period_def gcd_nat.simps)

lemma comma_finite_first_power:
  "comma_power_residue 260 10 = 120"
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_finite_first_headroom:
  "comma_finite_headroom 2 10 0 91 = 29"
  by (simp add: comma_finite_headroom_def comma_finite_guard_extra_def
    comma_finite_first_period[unfolded One_nat_def] comma_finite_first_power Let_def)

lemma comma_finite_first_step:
  "comma_finite_step 10 (Comma_Entry 2 0 91) =
    Comma_Next (Comma_Near 2 0 29)"
  by (simp add: comma_finite_step_def comma_finite_first_period[unfolded One_nat_def]
    comma_finite_first_headroom Let_def)

text \<open>This 92-position witness is untrusted data.  Its local transitions
are checked below against the executable finite cylinder; the list alone
does not establish branch safety or a global rank certificate.\<close>

definition comma_first_winning_trace :: "comma_finite_position list" where
  "comma_first_winning_trace = [
      (Comma_Entry 2 0 91), (Comma_Near 2 0 29), (Comma_Near 2 0 17), (Comma_Entry 3 0 16),
      (Comma_Near 3 0 144), (Comma_Near 3 0 81), (Comma_Entry 4 0 13), (Comma_Near 4 0 267),
      (Comma_Near 4 0 233), (Comma_Near 4 0 159), (Comma_Near 4 0 145), (Comma_Near 4 0 91),
      (Comma_Entry 5 0 4), (Comma_Near 5 0 56), (Comma_Near 5 0 11), (Comma_Entry 6 0 85),
      (Comma_Near 6 0 115), (Comma_Near 6 0 59), (Comma_Near 6 0 43), (Comma_Entry 7 0 34),
      (Comma_Near 7 0 86), (Comma_Near 7 0 39), (Comma_Near 7 0 22), (Comma_Entry 8 0 66),
      (Comma_Near 8 0 94), (Comma_Near 8 0 26), (Comma_Entry 9 0 23), (Comma_Near 9 0 257),
      (Comma_Near 9 0 218), (Comma_Near 9 0 189), (Comma_Near 9 0 170), (Comma_Near 9 0 161),
      (Comma_Near 9 0 62), (Comma_Entry 1 1 19), (Comma_Near 1 1 141), (Comma_Near 1 1 50),
      (Comma_Near 1 1 49), (Comma_Near 1 1 38), (Comma_Near 1 1 17), (Comma_Entry 2 1 15),
      (Comma_Near 2 1 145), (Comma_Near 2 1 93), (Comma_Near 2 1 21), (Comma_Entry 3 1 72),
      (Comma_Near 3 1 88), (Comma_Near 3 1 65), (Comma_Near 3 1 12), (Comma_Entry 4 1 72),
      (Comma_Near 4 1 48), (Comma_Near 4 1 24), (Comma_Entry 5 1 41), (Comma_Near 5 1 39),
      (Comma_Near 5 1 24), (Comma_Entry 6 1 42), (Comma_Near 6 1 118), (Comma_Near 6 1 92),
      (Comma_Near 6 1 6), (Comma_Entry 7 1 41), (Comma_Near 7 1 119), (Comma_Near 7 1 102),
      (Comma_Near 7 1 15), (Comma_Entry 8 1 43), (Comma_Near 8 1 17), (Comma_Entry 9 1 22),
      (Comma_Near 9 1 78), (Comma_Near 9 1 49), (Comma_Near 9 1 30), (Comma_Near 9 1 21),
      (Comma_Entry 1 2 70), (Comma_Near 1 2 150), (Comma_Near 1 2 149), (Comma_Near 1 2 138),
      (Comma_Near 1 2 117), (Comma_Near 1 2 86), (Comma_Near 1 2 45), (Comma_Entry 2 2 7),
      (Comma_Near 2 2 33), (Comma_Entry 3 2 40), (Comma_Near 3 2 120), (Comma_Near 3 2 117),
      (Comma_Near 3 2 84), (Comma_Near 3 2 21), (Comma_Entry 4 2 73), (Comma_Near 4 2 117),
      (Comma_Near 4 2 83), (Comma_Near 4 2 9), (Comma_Entry 5 2 6), (Comma_Near 5 2 74),
      (Comma_Near 5 2 9), (Comma_Entry 6 2 7), (Comma_Near 6 2 113), (Comma_Near 6 2 37)
    ]"

lemma comma_first_winning_trace_length:
  "length comma_first_winning_trace = 92"
  unfolding comma_first_winning_trace_def by simp

lemma comma_first_winning_trace_head:
  "hd comma_first_winning_trace = Comma_Entry 2 0 91"
  unfolding comma_first_winning_trace_def by simp

lemma comma_first_trace_chunk_0:
  "comma_finite_step 10 (Comma_Entry 2 0 91) = Comma_Next (Comma_Near 2 0 29) \<and>
    comma_finite_step 10 (Comma_Near 2 0 29) = Comma_Next (Comma_Near 2 0 17) \<and>
    comma_finite_step 10 (Comma_Near 2 0 17) = Comma_Next (Comma_Entry 3 0 16) \<and>
    comma_finite_step 10 (Comma_Entry 3 0 16) = Comma_Next (Comma_Near 3 0 144) \<and>
    comma_finite_step 10 (Comma_Near 3 0 144) = Comma_Next (Comma_Near 3 0 81) \<and>
    comma_finite_step 10 (Comma_Near 3 0 81) = Comma_Next (Comma_Entry 4 0 13) \<and>
    comma_finite_step 10 (Comma_Entry 4 0 13) = Comma_Next (Comma_Near 4 0 267) \<and>
    comma_finite_step 10 (Comma_Near 4 0 267) = Comma_Next (Comma_Near 4 0 233)"
  apply (simp add: comma_finite_step_def comma_finite_period_def
    Let_def gcd_nat.simps)
  apply (simp add: comma_finite_headroom_def comma_finite_period_def
    comma_finite_guard_extra_def Let_def gcd_nat.simps)
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_first_trace_chunk_1:
  "comma_finite_step 10 (Comma_Near 4 0 233) = Comma_Next (Comma_Near 4 0 159) \<and>
    comma_finite_step 10 (Comma_Near 4 0 159) = Comma_Next (Comma_Near 4 0 145) \<and>
    comma_finite_step 10 (Comma_Near 4 0 145) = Comma_Next (Comma_Near 4 0 91) \<and>
    comma_finite_step 10 (Comma_Near 4 0 91) = Comma_Next (Comma_Entry 5 0 4) \<and>
    comma_finite_step 10 (Comma_Entry 5 0 4) = Comma_Next (Comma_Near 5 0 56) \<and>
    comma_finite_step 10 (Comma_Near 5 0 56) = Comma_Next (Comma_Near 5 0 11) \<and>
    comma_finite_step 10 (Comma_Near 5 0 11) = Comma_Next (Comma_Entry 6 0 85) \<and>
    comma_finite_step 10 (Comma_Entry 6 0 85) = Comma_Next (Comma_Near 6 0 115)"
  apply (simp add: comma_finite_step_def comma_finite_period_def
    Let_def gcd_nat.simps)
  apply (simp add: comma_finite_headroom_def comma_finite_period_def
    comma_finite_guard_extra_def Let_def gcd_nat.simps)
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_first_trace_chunk_2:
  "comma_finite_step 10 (Comma_Near 6 0 115) = Comma_Next (Comma_Near 6 0 59) \<and>
    comma_finite_step 10 (Comma_Near 6 0 59) = Comma_Next (Comma_Near 6 0 43) \<and>
    comma_finite_step 10 (Comma_Near 6 0 43) = Comma_Next (Comma_Entry 7 0 34) \<and>
    comma_finite_step 10 (Comma_Entry 7 0 34) = Comma_Next (Comma_Near 7 0 86) \<and>
    comma_finite_step 10 (Comma_Near 7 0 86) = Comma_Next (Comma_Near 7 0 39) \<and>
    comma_finite_step 10 (Comma_Near 7 0 39) = Comma_Next (Comma_Near 7 0 22) \<and>
    comma_finite_step 10 (Comma_Near 7 0 22) = Comma_Next (Comma_Entry 8 0 66) \<and>
    comma_finite_step 10 (Comma_Entry 8 0 66) = Comma_Next (Comma_Near 8 0 94)"
  apply (simp add: comma_finite_step_def comma_finite_period_def
    Let_def gcd_nat.simps)
  apply (simp add: comma_finite_headroom_def comma_finite_period_def
    comma_finite_guard_extra_def Let_def gcd_nat.simps)
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_first_trace_chunk_3:
  "comma_finite_step 10 (Comma_Near 8 0 94) = Comma_Next (Comma_Near 8 0 26) \<and>
    comma_finite_step 10 (Comma_Near 8 0 26) = Comma_Next (Comma_Entry 9 0 23) \<and>
    comma_finite_step 10 (Comma_Entry 9 0 23) = Comma_Next (Comma_Near 9 0 257) \<and>
    comma_finite_step 10 (Comma_Near 9 0 257) = Comma_Next (Comma_Near 9 0 218) \<and>
    comma_finite_step 10 (Comma_Near 9 0 218) = Comma_Next (Comma_Near 9 0 189) \<and>
    comma_finite_step 10 (Comma_Near 9 0 189) = Comma_Next (Comma_Near 9 0 170) \<and>
    comma_finite_step 10 (Comma_Near 9 0 170) = Comma_Next (Comma_Near 9 0 161) \<and>
    comma_finite_step 10 (Comma_Near 9 0 161) = Comma_Next (Comma_Near 9 0 62)"
  apply (simp add: comma_finite_step_def comma_finite_period_def
    Let_def gcd_nat.simps)
  apply (simp add: comma_finite_headroom_def comma_finite_period_def
    comma_finite_guard_extra_def Let_def gcd_nat.simps)
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_first_trace_chunk_4:
  "comma_finite_step 10 (Comma_Near 9 0 62) = Comma_Next (Comma_Entry 1 1 19) \<and>
    comma_finite_step 10 (Comma_Entry 1 1 19) = Comma_Next (Comma_Near 1 1 141) \<and>
    comma_finite_step 10 (Comma_Near 1 1 141) = Comma_Next (Comma_Near 1 1 50) \<and>
    comma_finite_step 10 (Comma_Near 1 1 50) = Comma_Next (Comma_Near 1 1 49) \<and>
    comma_finite_step 10 (Comma_Near 1 1 49) = Comma_Next (Comma_Near 1 1 38) \<and>
    comma_finite_step 10 (Comma_Near 1 1 38) = Comma_Next (Comma_Near 1 1 17) \<and>
    comma_finite_step 10 (Comma_Near 1 1 17) = Comma_Next (Comma_Entry 2 1 15) \<and>
    comma_finite_step 10 (Comma_Entry 2 1 15) = Comma_Next (Comma_Near 2 1 145)"
  apply (simp add: comma_finite_step_def comma_finite_period_def
    Let_def gcd_nat.simps)
  apply (simp add: comma_finite_headroom_def comma_finite_period_def
    comma_finite_guard_extra_def Let_def gcd_nat.simps)
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_first_trace_chunk_5:
  "comma_finite_step 10 (Comma_Near 2 1 145) = Comma_Next (Comma_Near 2 1 93) \<and>
    comma_finite_step 10 (Comma_Near 2 1 93) = Comma_Next (Comma_Near 2 1 21) \<and>
    comma_finite_step 10 (Comma_Near 2 1 21) = Comma_Next (Comma_Entry 3 1 72) \<and>
    comma_finite_step 10 (Comma_Entry 3 1 72) = Comma_Next (Comma_Near 3 1 88) \<and>
    comma_finite_step 10 (Comma_Near 3 1 88) = Comma_Next (Comma_Near 3 1 65) \<and>
    comma_finite_step 10 (Comma_Near 3 1 65) = Comma_Next (Comma_Near 3 1 12) \<and>
    comma_finite_step 10 (Comma_Near 3 1 12) = Comma_Next (Comma_Entry 4 1 72) \<and>
    comma_finite_step 10 (Comma_Entry 4 1 72) = Comma_Next (Comma_Near 4 1 48)"
  apply (simp add: comma_finite_step_def comma_finite_period_def
    Let_def gcd_nat.simps)
  apply (simp add: comma_finite_headroom_def comma_finite_period_def
    comma_finite_guard_extra_def Let_def gcd_nat.simps)
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_first_trace_chunk_6:
  "comma_finite_step 10 (Comma_Near 4 1 48) = Comma_Next (Comma_Near 4 1 24) \<and>
    comma_finite_step 10 (Comma_Near 4 1 24) = Comma_Next (Comma_Entry 5 1 41) \<and>
    comma_finite_step 10 (Comma_Entry 5 1 41) = Comma_Next (Comma_Near 5 1 39) \<and>
    comma_finite_step 10 (Comma_Near 5 1 39) = Comma_Next (Comma_Near 5 1 24) \<and>
    comma_finite_step 10 (Comma_Near 5 1 24) = Comma_Next (Comma_Entry 6 1 42) \<and>
    comma_finite_step 10 (Comma_Entry 6 1 42) = Comma_Next (Comma_Near 6 1 118) \<and>
    comma_finite_step 10 (Comma_Near 6 1 118) = Comma_Next (Comma_Near 6 1 92) \<and>
    comma_finite_step 10 (Comma_Near 6 1 92) = Comma_Next (Comma_Near 6 1 6)"
  apply (simp add: comma_finite_step_def comma_finite_period_def
    Let_def gcd_nat.simps)
  apply (simp add: comma_finite_headroom_def comma_finite_period_def
    comma_finite_guard_extra_def Let_def gcd_nat.simps)
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_first_trace_chunk_7:
  "comma_finite_step 10 (Comma_Near 6 1 6) = Comma_Next (Comma_Entry 7 1 41) \<and>
    comma_finite_step 10 (Comma_Entry 7 1 41) = Comma_Next (Comma_Near 7 1 119) \<and>
    comma_finite_step 10 (Comma_Near 7 1 119) = Comma_Next (Comma_Near 7 1 102) \<and>
    comma_finite_step 10 (Comma_Near 7 1 102) = Comma_Next (Comma_Near 7 1 15) \<and>
    comma_finite_step 10 (Comma_Near 7 1 15) = Comma_Next (Comma_Entry 8 1 43) \<and>
    comma_finite_step 10 (Comma_Entry 8 1 43) = Comma_Next (Comma_Near 8 1 17) \<and>
    comma_finite_step 10 (Comma_Near 8 1 17) = Comma_Next (Comma_Entry 9 1 22) \<and>
    comma_finite_step 10 (Comma_Entry 9 1 22) = Comma_Next (Comma_Near 9 1 78)"
  apply (simp add: comma_finite_step_def comma_finite_period_def
    Let_def gcd_nat.simps)
  apply (simp add: comma_finite_headroom_def comma_finite_period_def
    comma_finite_guard_extra_def Let_def gcd_nat.simps)
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_first_trace_chunk_8:
  "comma_finite_step 10 (Comma_Near 9 1 78) = Comma_Next (Comma_Near 9 1 49) \<and>
    comma_finite_step 10 (Comma_Near 9 1 49) = Comma_Next (Comma_Near 9 1 30) \<and>
    comma_finite_step 10 (Comma_Near 9 1 30) = Comma_Next (Comma_Near 9 1 21) \<and>
    comma_finite_step 10 (Comma_Near 9 1 21) = Comma_Next (Comma_Entry 1 2 70) \<and>
    comma_finite_step 10 (Comma_Entry 1 2 70) = Comma_Next (Comma_Near 1 2 150) \<and>
    comma_finite_step 10 (Comma_Near 1 2 150) = Comma_Next (Comma_Near 1 2 149) \<and>
    comma_finite_step 10 (Comma_Near 1 2 149) = Comma_Next (Comma_Near 1 2 138) \<and>
    comma_finite_step 10 (Comma_Near 1 2 138) = Comma_Next (Comma_Near 1 2 117)"
  apply (simp add: comma_finite_step_def comma_finite_period_def
    Let_def gcd_nat.simps)
  apply (simp add: comma_finite_headroom_def comma_finite_period_def
    comma_finite_guard_extra_def Let_def gcd_nat.simps)
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_first_trace_chunk_9:
  "comma_finite_step 10 (Comma_Near 1 2 117) = Comma_Next (Comma_Near 1 2 86) \<and>
    comma_finite_step 10 (Comma_Near 1 2 86) = Comma_Next (Comma_Near 1 2 45) \<and>
    comma_finite_step 10 (Comma_Near 1 2 45) = Comma_Next (Comma_Entry 2 2 7) \<and>
    comma_finite_step 10 (Comma_Entry 2 2 7) = Comma_Next (Comma_Near 2 2 33) \<and>
    comma_finite_step 10 (Comma_Near 2 2 33) = Comma_Next (Comma_Entry 3 2 40) \<and>
    comma_finite_step 10 (Comma_Entry 3 2 40) = Comma_Next (Comma_Near 3 2 120) \<and>
    comma_finite_step 10 (Comma_Near 3 2 120) = Comma_Next (Comma_Near 3 2 117) \<and>
    comma_finite_step 10 (Comma_Near 3 2 117) = Comma_Next (Comma_Near 3 2 84)"
  apply (simp add: comma_finite_step_def comma_finite_period_def
    Let_def gcd_nat.simps)
  apply (simp add: comma_finite_headroom_def comma_finite_period_def
    comma_finite_guard_extra_def Let_def gcd_nat.simps)
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_first_trace_chunk_10:
  "comma_finite_step 10 (Comma_Near 3 2 84) = Comma_Next (Comma_Near 3 2 21) \<and>
    comma_finite_step 10 (Comma_Near 3 2 21) = Comma_Next (Comma_Entry 4 2 73) \<and>
    comma_finite_step 10 (Comma_Entry 4 2 73) = Comma_Next (Comma_Near 4 2 117) \<and>
    comma_finite_step 10 (Comma_Near 4 2 117) = Comma_Next (Comma_Near 4 2 83) \<and>
    comma_finite_step 10 (Comma_Near 4 2 83) = Comma_Next (Comma_Near 4 2 9) \<and>
    comma_finite_step 10 (Comma_Near 4 2 9) = Comma_Next (Comma_Entry 5 2 6) \<and>
    comma_finite_step 10 (Comma_Entry 5 2 6) = Comma_Next (Comma_Near 5 2 74) \<and>
    comma_finite_step 10 (Comma_Near 5 2 74) = Comma_Next (Comma_Near 5 2 9)"
  apply (simp add: comma_finite_step_def comma_finite_period_def
    Let_def gcd_nat.simps)
  apply (simp add: comma_finite_headroom_def comma_finite_period_def
    comma_finite_guard_extra_def Let_def gcd_nat.simps)
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_first_trace_chunk_11:
  "comma_finite_step 10 (Comma_Near 5 2 9) = Comma_Next (Comma_Entry 6 2 7) \<and>
    comma_finite_step 10 (Comma_Entry 6 2 7) = Comma_Next (Comma_Near 6 2 113) \<and>
    comma_finite_step 10 (Comma_Near 6 2 113) = Comma_Next (Comma_Near 6 2 37) \<and>
    comma_finite_step 10 (Comma_Near 6 2 37) = Comma_Fork 7 2"
  apply (simp add: comma_finite_step_def comma_finite_period_def
    Let_def gcd_nat.simps)
  apply (simp add: comma_finite_headroom_def comma_finite_period_def
    comma_finite_guard_extra_def Let_def gcd_nat.simps)
  by (simp add: comma_power_residue_def comma_short_period_def)

lemma comma_first_winning_trace_checked:
  "comma_finite_trace_ok 10 comma_first_winning_trace
    (Comma_Fork_At 7 2)"
  using comma_first_trace_chunk_0 comma_first_trace_chunk_1
    comma_first_trace_chunk_2 comma_first_trace_chunk_3
    comma_first_trace_chunk_4 comma_first_trace_chunk_5
    comma_first_trace_chunk_6 comma_first_trace_chunk_7
    comma_first_trace_chunk_8 comma_first_trace_chunk_9
    comma_first_trace_chunk_10 comma_first_trace_chunk_11
  by (auto simp: comma_first_winning_trace_def)

text \<open>The N boundary is one literal transition before the old 92-position
suffix.  Starting at Entry 2 0 91 would silently omit the edge from
N(2,10) to its first child.  The Z boundary starts at Entry a 0 0.\<close>

lemma comma_finite_N_initial_step:
  "comma_finite_step 10 (Comma_Near 1 0 1) =
    Comma_Next (Comma_Entry 2 0 91)"
  by (simp add: comma_finite_step_def Let_def)

lemma comma_finite_first_winning_suffix_92:
  "comma_finite_run 92 10 (Comma_Entry 2 0 91) =
    Some (Comma_Fork_At 7 2)"
  using comma_finite_trace_ok_sound[OF comma_first_winning_trace_checked]
    comma_first_winning_trace_length comma_first_winning_trace_head
  by simp

lemma comma_finite_first_winning_macro_93:
  "comma_finite_macro 93 (Comma_N, 2, 10) =
    Some (Comma_Fork_At 7 2)"
proof -
  have first: "comma_finite_run 93 10 (Comma_Near 1 0 1) =
      comma_finite_run 92 10 (Comma_Entry 2 0 91)"
    using comma_finite_N_initial_step
    by (subst comma_finite_run_nat) simp
  show ?thesis
    using first comma_finite_first_winning_suffix_92
    by (simp add: comma_finite_macro_def comma_finite_initial_def
      comma_boundary_valid_def)
qed

lemma comma_finite_first_winning_macro:
  "comma_finite_macro 4096 (Comma_N, 2, 10) =
    Some (Comma_Fork_At 7 2)"
proof -
  have base: "comma_finite_run 93 10 (Comma_Near 1 0 1) =
    Some (Comma_Fork_At 7 2)"
    using comma_finite_first_winning_macro_93
    by (simp add: comma_finite_macro_def comma_finite_initial_def
      comma_boundary_valid_def)
  have more: "comma_finite_run (93 + 4003) 10
    (Comma_Near 1 0 1) = Some (Comma_Fork_At 7 2)"
    using comma_finite_run_more[OF base] .
  show ?thesis
    using more
    by (simp add: comma_finite_macro_def comma_finite_initial_def
      comma_boundary_valid_def)
qed

lemma comma_finite_first_edge_has_unit_weight:
  "comma_finite_next_weight 10 (comma_finite_initial (Comma_N,2,10)) = 1"
  by (simp add: comma_finite_initial_def comma_finite_next_weight_def
    comma_chart_weight_value_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_finite_first_period comma_finite_first_power
      comma_finite_first_headroom comma_finite_first_step
      comma_first_winning_trace_length comma_first_winning_trace_head
      comma_first_trace_chunk_0 comma_first_trace_chunk_1
      comma_first_trace_chunk_2 comma_first_trace_chunk_3
      comma_first_trace_chunk_4 comma_first_trace_chunk_5
      comma_first_trace_chunk_6 comma_first_trace_chunk_7
      comma_first_trace_chunk_8 comma_first_trace_chunk_9
      comma_first_trace_chunk_10 comma_first_trace_chunk_11
      comma_first_winning_trace_checked comma_finite_N_initial_step
      comma_finite_first_winning_suffix_92
      comma_finite_first_winning_macro_93
      comma_finite_first_winning_macro
      comma_finite_first_edge_has_unit_weight})
    then () else error "Comma trace-regression proof depends on an oracle";
\<close>

end
