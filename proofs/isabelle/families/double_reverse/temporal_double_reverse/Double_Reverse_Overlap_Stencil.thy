theory Double_Reverse_Overlap_Stencil
  imports Double_Reverse_F_Port_Refinement Shared_Carry_Dynamics.Ordered_Overlap_Support
begin

definition double_reverse_supported_f_pair :: "nat list \<Rightarrow> nat \<times> nat" where
  "double_reverse_supported_f_pair row =
    double_reverse_f_port_pair (if 5 \<le> row ! 0 then 1 else 0)
      (row ! 1) (row ! 2) (row ! 3 mod 5)"

theorem double_reverse_ordered_support_pair:
  fixes left right :: "nat list set"
  assumes "a \<in> left" "b \<in> right"
    "k \<le> length a" "k \<le> length b"
    "drop (length a - k) a = take k b"
    "(a @ drop k b) ! 0 < 10" "(a @ drop k b) ! 1 < 10"
    "(a @ drop k b) ! 2 < 10" "(a @ drop k b) ! 3 < 10"
    "\<And>w. w \<in> ordered_overlap_support k left right \<Longrightarrow>
      double_reverse_supported_f_pair w = output"
  shows "(double_reverse_t2_digit ((a @ drop k b) ! 0) ((a @ drop k b) ! 1) ((a @ drop k b) ! 2),
      double_reverse_t2_digit ((a @ drop k b) ! 1) ((a @ drop k b) ! 2) ((a @ drop k b) ! 3)) = output"
proof -
  have joined: "a @ drop k b \<in> ordered_overlap_support k left right"
    by (rule ordered_overlap_support_member[OF assms(1-5)])
  have selected: "double_reverse_supported_f_pair (a @ drop k b) = output"
    by (rule assms(10)[OF joined])
  show ?thesis using double_reverse_f_port_pair_exact[OF assms(6-9)] selected
    by (simp add: double_reverse_supported_f_pair_def)
qed

ML \<open>
  val checked = @{thms double_reverse_ordered_support_pair};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "support uses an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "support has skipped proofs" else ();
\<close>
end
