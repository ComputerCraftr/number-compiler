theory Double_Reverse_Point_Support
  imports Double_Reverse_Temporal_Refinement.Double_Reverse_Source_Window_Refinement Double_Reverse_Temporal_Refinement.Double_Reverse_Overlap_Stencil
begin

theorem double_reverse_pointed_ordered_support_pair:
  fixes source row :: "nat list" and origin :: int and radius :: nat
    and left right :: "nat list set"
  defines "row \<equiv> double_reverse_pointed_source_window source origin radius"
  assumes "2 \<le> radius"
    "a \<in> left" "b \<in> right"
    "k \<le> length a" "k \<le> length b"
    "drop (length a - k) a = take k b"
    "row = a @ drop k b"
    "row ! 0 < 10" "row ! 1 < 10" "row ! 2 < 10" "row ! 3 < 10"
    "\<And>w. w \<in> ordered_overlap_support k left right \<Longrightarrow>
      double_reverse_supported_f_pair w = output"
  shows "(double_reverse_t2_digit (row ! 0) (row ! 1) (row ! 2),
      double_reverse_t2_digit (row ! 1) (row ! 2) (row ! 3)) = output"
proof -
  have exact: "(double_reverse_t2_digit ((a @ drop k b) ! 0)
        ((a @ drop k b) ! 1) ((a @ drop k b) ! 2),
      double_reverse_t2_digit ((a @ drop k b) ! 1)
        ((a @ drop k b) ! 2) ((a @ drop k b) ! 3)) = output"
    by (rule double_reverse_ordered_support_pair[OF assms(3-7)])
       (use assms(8-13) in simp_all)
  show ?thesis using exact assms(8) by simp
qed

ML \<open>
  val checked = @{thms double_reverse_pointed_ordered_support_pair};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "point uses an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "point has skipped proofs" else ();
\<close>
end
