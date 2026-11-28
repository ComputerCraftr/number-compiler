theory Double_Reverse_Odd_Border
  imports Double_Reverse_Temporal_Refinement
begin

definition double_reverse_border_low_pair ::
  "double_reverse_boundary_edge \<Rightarrow> nat \<times> nat" where
  "double_reverse_border_low_pair edge = (case edge of (a,b,y,z) \<Rightarrow> (y,z))"

theorem double_reverse_closed_border_two_physical_guard:
  assumes "edge \<in> double_reverse_closed_border" "u < 2" "v < 2"
  shows "(double_reverse_border_low_pair edge = (4,2) \<longrightarrow>
      double_reverse_border_low_pair
        (double_reverse_border_target (double_reverse_border_target edge u) v)
          \<in> {(6,8),(8,8)} \<and>
      double_reverse_border_width_growth edge = 0) \<and>
    (double_reverse_border_low_pair edge \<in> {(6,8),(8,8)} \<longrightarrow>
      double_reverse_border_low_pair
        (double_reverse_border_target (double_reverse_border_target edge u) v) = (4,2)
      \<and> double_reverse_border_width_growth edge = 1)"
proof -
  have U: "u = 0 \<or> u = 1" and V: "v = 0 \<or> v = 1" using assms by auto
  show ?thesis using assms U V
    by (auto simp: double_reverse_closed_border_def double_reverse_border_target_def
        double_reverse_border_width_growth_def threshold5_digit_def
        double_reverse_border_low_pair_def)
qed

ML \<open>

  val checked = @{thms double_reverse_closed_border_two_physical_guard};

  val _ = if null (Thm_Deps.all_oracles checked) then () else error "border uses an oracle";

  val _ = if Thm_Deps.has_skip_proof checked then error "border has skipped proofs" else ();

\<close>

end
