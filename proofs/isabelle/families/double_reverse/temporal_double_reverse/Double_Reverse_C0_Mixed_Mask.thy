theory Double_Reverse_C0_Mixed_Mask
  imports Double_Reverse_Powered_Border_Transfer
begin

definition double_reverse_low_mixed_digit :: "nat \<Rightarrow> nat" where
  "double_reverse_low_mixed_digit d = (if d < 5 then 5-d else 1)"

definition double_reverse_low_mixed_mask :: "double_reverse_boundary_edge \<Rightarrow> nat" where
  "double_reverse_low_mixed_mask edge =
    (case edge of (a,b,y,z) \<Rightarrow>
      double_reverse_low_mixed_digit z + 6 * double_reverse_low_mixed_digit y)"

definition double_reverse_phase_mixed_mask :: "nat \<Rightarrow> nat" where
  "double_reverse_phase_mixed_mask phase =
    (if phase = 0 \<or> phase = 3 then 7 else 9)"

lemma double_reverse_c0_mixed_mask_phase:
  assumes "edge \<in> double_reverse_closed_border"
  shows "double_reverse_low_mixed_mask edge =
    double_reverse_phase_mixed_mask (double_reverse_border_phase edge)"
  using assms
  by (auto simp: double_reverse_closed_border_def double_reverse_low_mixed_mask_def
    double_reverse_low_mixed_digit_def double_reverse_phase_mixed_mask_def
    double_reverse_border_phase_def)

end
