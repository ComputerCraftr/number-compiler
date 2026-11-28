theory Reverse_Native_Slab_Growth_Clock
  imports Reverse_EQ_Clock_Transport "Reverse_Residuals.Reverse_Native_Slab_Core"
begin

text \<open>The 1110 branch is selected from the same physical source.  This
is one branch of the four-tick clock proof; the 1011 branch additionally
requires the born-quiet collar and its next-birth theorem.\<close>

lemma slab_outer_nine_next_reset_forces_birth:
  assumes valid: "valid_pair source" and split: "source = 9 # s # suffix"
      and decisive: "9 < s"
  shows "carry_out False source"
proof -
  have symmetric: "rev source = source" using valid by (simp add: valid_pair_def)
  show ?thesis
    using carry_out_reverse_first_reset[of False source] symmetric split decisive
    by simp
qed

theorem slab_outer_eighteen_second_birth_clock:
  assumes valid: "valid_pair source" and outer: "hd source = 18"
      and second: "carry_out False (step source)"
  shows "carry_out False source"
    and "carry_out False (step source)"
    and "carry_out False (step (step source))"
    and "\<not> carry_out False (step (step (step source)))"
proof -
  have first: "carry_out False source"
    using slab_core_outer_forces_birth[OF valid] outer by simp
  have nonempty0: "source \<noteq> []" using valid by (simp add: valid_pair_def)
  have valid1: "valid_pair (step source)" by (rule valid_pair_successor[OF valid])
  have outer1: "hd (step source) = 9"
    using source_growth_edge_successor[OF nonempty0 first] outer by simp
  have nonempty1: "step source \<noteq> []" using valid1 by (simp add: valid_pair_def)
  have valid2: "valid_pair (step (step source))" by (rule valid_pair_successor[OF valid1])
  have outer2: "hd (step (step source)) = 10"
    using source_growth_edge_successor[OF nonempty1 second] outer1 by simp
  have third: "carry_out False (step (step source))"
    using slab_core_outer_forces_birth[OF valid2] outer2 by simp
  have nonempty2: "step (step source) \<noteq> []" using valid2 by (simp add: valid_pair_def)
  have valid3: "valid_pair (step (step (step source)))"
    by (rule valid_pair_successor[OF valid2])
  have outer3: "hd (step (step (step source))) = 1"
    using source_growth_edge_successor[OF nonempty2 third] outer2 by simp
  have fourth: "\<not> carry_out False (step (step (step source)))"
  proof
    assume growth: "carry_out False (step (step (step source)))"
    have "9 \<le> hd (step (step (step source)))"
      by (rule source_growth_requires_edge(1)[OF valid3 growth])
    with outer3 show False by simp
  qed
  show "carry_out False source" by (rule first)
  show "carry_out False (step source)" by (rule second)
  show "carry_out False (step (step source))" by (rule third)
  show "\<not> carry_out False (step (step (step source)))" by (rule fourth)
qed

theorem slab_outer_eighteen_second_quiet_prefix:
  assumes valid: "valid_pair source" and outer: "hd source = 18"
      and second: "\<not> carry_out False (step source)"
  shows "carry_out False source"
    and "\<not> carry_out False (step source)"
    and "hd (step (step source)) = 18"
    and "carry_out False (step (step source))"
proof -
  have first: "carry_out False source"
    using slab_core_outer_forces_birth[OF valid] outer by simp
  have nonempty0: "source \<noteq> []" using valid by (simp add: valid_pair_def)
  have valid1: "valid_pair (step source)" by (rule valid_pair_successor[OF valid])
  have outer1: "hd (step source) = 9"
    using source_growth_edge_successor[OF nonempty0 first] outer by simp
  have valid2: "valid_pair (step (step source))" by (rule valid_pair_successor[OF valid1])
  have lower: "18 \<le> hd (step (step source))"
    using source_nongrowth_outer_coefficient_bounds(1)[OF valid1 second] outer1 by simp
  have upper: "hd (step (step source)) \<le> 18"
    using valid2 by (cases "step (step source)") (auto simp: valid_pair_def)
  have outer2: "hd (step (step source)) = 18" using lower upper by arith
  have third: "carry_out False (step (step source))"
    using slab_core_outer_forces_birth[OF valid2] outer2 by simp
  show "carry_out False source" by (rule first)
  show "\<not> carry_out False (step source)" by (rule second)
  show "hd (step (step source)) = 18" by (rule outer2)
  show "carry_out False (step (step source))" by (rule third)
qed

text \<open>For outer sums 14 through 17 the first birth leaves an
outer sum from 5 through 8. The quiet step doubles it with at most
one incoming carry, forcing the third birth and the final quiet step.\<close>

theorem slab_outer_middle_physical_clock:
  assumes valid: "valid_pair s" and edge: "14 \<le> hd s" "hd s \<le> 17"
  shows "[carry_out False s, carry_out False (step s),
          carry_out False (step (step s)), carry_out False (step (step (step s)))] =
         [True, False, True, False]"
proof -
  let ?t = "step s"
  let ?u = "step ?t"
  let ?v = "step ?u"
  have vt: "valid_pair ?t" and vu: "valid_pair ?u" and vv: "valid_pair ?v"
    using valid by (auto intro: valid_pair_successor)
  have first: "carry_out False s" using valid edge by (intro slab_core_outer_forces_birth) auto
  have e1: "hd ?t = 1 + hd s mod 10"
    using source_growth_edge_successor first valid by (auto simp: valid_pair_def)
  have bounds: "5 \<le> hd ?t" "hd ?t \<le> 8" using e1 edge by presburger+
  have quiet: "\<not> carry_out False ?t"
    using bounds source_growth_requires_edge(1)[OF vt] by force
  have e2: "10 \<le> hd ?u" "hd ?u \<le> 17"
    using source_nongrowth_outer_coefficient_bounds[OF vt quiet] bounds by linarith+
  have third: "carry_out False ?u" by (rule slab_core_outer_forces_birth[OF vu e2(1)])
  have e3: "hd ?v = 1 + hd ?u mod 10"
    using source_growth_edge_successor third vu by (auto simp: valid_pair_def)
  have "hd ?v < 9" using e3 e2 by presburger
  then have "\<not> carry_out False ?v" using source_growth_requires_edge(1)[OF vv] by force
  with first quiet third show ?thesis by simp
qed

ML \<open>
  val checked = @{thms slab_outer_middle_physical_clock slab_outer_nine_next_reset_forces_birth
    slab_outer_eighteen_second_birth_clock
    slab_outer_eighteen_second_quiet_prefix};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse native slab growth clock depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reverse native slab growth clock proof" else ();
\<close>

end
