theory Checked_Border_Transfer
  imports Finite_Transfer_Power Ordered_Tripling_Carry
begin

text \<open>A finite Boolean relation composes only across a checked full-state
seam. Guards remain attached to the source of each concrete transfer; these
lemmas provide finite-prefix safety and no claim about an unobserved future
input word.\<close>

definition guarded_transfer :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow>
    ('a \<times> 'a) set" where
  "guarded_transfer allowed transfer =
    {(source,target). source \<in> allowed \<and> (source,target) \<in> transfer}"

lemma guarded_transfer_then_exact:
  "guarded_transfer source_guard first O guarded_transfer seam_guard after =
    {(source,target). source \<in> source_guard \<and>
      (\<exists>middle. (source,middle) \<in> first \<and>
        middle \<in> seam_guard \<and> (middle,target) \<in> after)}"
  by (auto simp: guarded_transfer_def)

lemma guarded_transfer_seam:
  assumes first: "(source,middle) \<in> guarded_transfer source_guard before"
      and after: "(middle,target) \<in> guarded_transfer seam_guard following"
  shows "source \<in> source_guard"
    and "middle \<in> seam_guard"
    and "(source,target) \<in> before O following"
  using assms by (auto simp: guarded_transfer_def)

definition transfer_preserves :: "('a \<Rightarrow> bool) \<Rightarrow>
    ('a \<times> 'a) set \<Rightarrow> bool" where
  "transfer_preserves safe transfer \<longleftrightarrow>
    (\<forall>source target. safe source \<and> (source,target) \<in> transfer
      \<longrightarrow> safe target)"

lemma transfer_preserves_then:
  assumes first: "transfer_preserves safe before"
      and after: "transfer_preserves safe following"
  shows "transfer_preserves safe (before O following)"
  using assms unfolding transfer_preserves_def by blast

lemma transfer_preserves_power:
  assumes "transfer_preserves safe transfer"
  shows "transfer_preserves safe (transfer ^^ ticks)"
  using assms
proof (induction ticks)
  case 0
  then show ?case by (simp add: transfer_preserves_def)
next
  case (Suc ticks)
  have power: "transfer_preserves safe (transfer ^^ ticks)"
    using Suc.IH[OF Suc.prems] .
  have composed: "transfer_preserves safe (transfer ^^ ticks O transfer)"
    by (rule transfer_preserves_then[OF power Suc.prems])
  show ?case
    using composed
    by (simp only: Suc_eq_plus1 relpow_add relpow_1)
qed

theorem transfer_finite_prefix_safe:
  assumes preserves: "transfer_preserves safe transfer"
      and initial: "safe source"
      and path: "(source,target) \<in> transfer ^^ ticks"
  shows "safe target"
  using transfer_preserves_power[OF preserves, where ticks = ticks] initial path
  unfolding transfer_preserves_def by blast

theorem tripling_source_seam_refines_ordered_digit:
  fixes modulus phase left right boundary radix
  assumes boundary: "0 < boundary"
  shows "tripling_source modulus (phase + left + right) =
      (tripling_source modulus (phase + left) * 3^right) mod modulus"
    and "((3 * tripling_source modulus (phase + left)) div boundary) mod radix =
      (3 * ((tripling_source modulus (phase + left) div boundary) mod radix) +
        3 * (tripling_source modulus (phase + left) mod boundary) div boundary)
        mod radix"
proof -
  show "tripling_source modulus (phase + left + right) =
      (tripling_source modulus (phase + left) * 3^right) mod modulus"
    by (rule tripling_source_split)
  show "((3 * tripling_source modulus (phase + left)) div boundary) mod radix =
      (3 * ((tripling_source modulus (phase + left) div boundary) mod radix) +
        3 * (tripling_source modulus (phase + left) mod boundary) div boundary)
        mod radix"
    by (rule tripling_digit_with_ordered_inlet[OF boundary])
qed

ML \<open>
  val checked = @{thms guarded_transfer_then_exact guarded_transfer_seam
    transfer_preserves_then transfer_preserves_power
    transfer_finite_prefix_safe tripling_source_seam_refines_ordered_digit};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Checked border transfer depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped checked border transfer proof" else ();
\<close>

end
