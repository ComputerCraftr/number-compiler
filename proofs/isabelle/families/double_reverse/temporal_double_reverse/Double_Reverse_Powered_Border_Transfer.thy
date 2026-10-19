theory Double_Reverse_Powered_Border_Transfer
  imports Double_Reverse_Temporal_Refinement
    Shared_Carry_Dynamics.Checked_Border_Transfer
begin

text \<open>The powered CLI observer uses the finite closed-border relation as
its universal cylinder, while source-rooted endpoint cones identify the
realized point. This relation is deliberately only the set of legal local
inlet transitions: membership after powering does not assert that an
unobserved integer source realizes every choice of inlets. The theorem below
connects the relation power to the existing finite-transfer safety law and
therefore gives a checked invariant for every pointed endpoint selected from
the powered relation.\<close>

definition double_reverse_closed_border_relation ::
    "(double_reverse_boundary_edge \<times> double_reverse_boundary_edge) set" where
  "double_reverse_closed_border_relation =
    {(source,target). source \<in> double_reverse_closed_border \<and>
      (\<exists>inward<2. target = double_reverse_border_target source inward)}"

lemma double_reverse_closed_border_relation_target:
  assumes "source \<in> double_reverse_closed_border"
      "inward < 2"
  shows "(source,double_reverse_border_target source inward) \<in>
      double_reverse_closed_border_relation"
  using assms
  by (auto simp: double_reverse_closed_border_relation_def)

lemma double_reverse_closed_border_relation_preserves:
  "transfer_preserves (\<lambda>edge. edge \<in> double_reverse_closed_border)
      double_reverse_closed_border_relation"
  unfolding transfer_preserves_def double_reverse_closed_border_relation_def
  using double_reverse_closed_border_ingress_closed
  by blast

theorem double_reverse_powered_border_endpoint_closed:
  assumes source: "source \<in> double_reverse_closed_border"
      and path: "(source,target) \<in>
        double_reverse_closed_border_relation ^^ ticks"
  shows "target \<in> double_reverse_closed_border"
  using transfer_finite_prefix_safe[
      OF double_reverse_closed_border_relation_preserves source path] .

theorem double_reverse_binary_border_power_exact:
  "transfer_binary_power double_reverse_closed_border_relation bits =
    double_reverse_closed_border_relation ^^ transfer_binary_value bits"
  by (rule transfer_binary_power_exact)

text \<open>The source-specific endpoint projection must still be checked
against this complete guarded relation. A matching endpoint is necessary for
the projection, but neither this finite invariant nor the four-phase outer
border clock supplies an inner-pair period or execution authority.\<close>

ML \<open>
  val checked = @{thms double_reverse_closed_border_relation_target
    double_reverse_closed_border_relation_preserves
    double_reverse_powered_border_endpoint_closed
    double_reverse_binary_border_power_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Powered double-reverse border transfer depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped powered double-reverse border transfer proof" else ();
\<close>

end
