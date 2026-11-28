theory Ordered_Overlap_Support
  imports Main
begin

text \<open>Supports describe complete ordered words.  A shared boundary is
checked before two relations are joined; neither a histogram nor a projected
digit alone supplies that boundary authority.\<close>

definition ordered_overlap_support ::
  "nat \<Rightarrow> 'a list set \<Rightarrow> 'a list set \<Rightarrow> 'a list set" where
  "ordered_overlap_support k left right =
    {a @ drop k b |a b. a \<in> left \<and> b \<in> right \<and>
      k \<le> length a \<and> k \<le> length b \<and>
      drop (length a - k) a = take k b}"

lemma ordered_overlap_support_finite:
  assumes "finite left" "finite right"
  shows "finite (ordered_overlap_support k left right)"
proof -
  have subset: "ordered_overlap_support k left right \<subseteq>
      (\<lambda>(a,b). a @ drop k b) ` (left \<times> right)"
    by (auto simp: ordered_overlap_support_def)
  show ?thesis
    by (rule finite_subset[OF subset]) (simp add: assms)
qed

lemma ordered_overlap_support_member:
  assumes "a \<in> left" "b \<in> right" "k \<le> length a" "k \<le> length b"
    "drop (length a - k) a = take k b"
  shows "a @ drop k b \<in> ordered_overlap_support k left right"
  using assms by (auto simp: ordered_overlap_support_def)

lemma ordered_overlap_support_mono:
  assumes "left \<subseteq> left'" "right \<subseteq> right'"
  shows "ordered_overlap_support k left right \<subseteq>
    ordered_overlap_support k left' right'"
  using assms by (auto simp: ordered_overlap_support_def)

lemma ordered_overlap_singleton_output:
  assumes "w \<in> ordered_overlap_support k left right"
    "\<And>v. v \<in> ordered_overlap_support k left right \<Longrightarrow> f v = output"
  shows "f w = output"
  using assms by blast

lemma ordered_overlap_rejects_wrong_boundary:
  "ordered_overlap_support 1 {[1::nat, 2]} {[3, 2]} = {}"
  by (auto simp: ordered_overlap_support_def)

lemma ordered_overlap_preserves_boundary_order:
  "ordered_overlap_support 2 {[1::nat, 2, 3]} {[2, 3, 4]} = {[1, 2, 3, 4]}"
  by (auto simp: ordered_overlap_support_def)

ML \<open>
  val checked = @{thms ordered_overlap_support_finite ordered_overlap_support_member
    ordered_overlap_support_mono ordered_overlap_singleton_output
    ordered_overlap_rejects_wrong_boundary ordered_overlap_preserves_boundary_order};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "overlap support uses an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "overlap support has skipped proofs" else ();
\<close>

text \<open>Multiple possible outputs do not certify a selected output.  Enlarging
either support remains sound, but can only make such a singleton check fail.\<close>

end
