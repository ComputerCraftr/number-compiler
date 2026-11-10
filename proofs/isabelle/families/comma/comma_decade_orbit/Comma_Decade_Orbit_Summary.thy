theory Comma_Decade_Orbit_Summary
  imports Comma_Decade_Orbit.Comma_Decade_Orbit_Quotient
begin

text \<open>
Exact decade summaries are invariant under the already-proved orbit control
quotient. This owner contains no B1 action instance or occurrence table.
\<close>

lemma comma_semantic_future_exact_summary_control_transport:
  assumes controls: "comma_decade_control source = comma_decade_control target"
    and summary: "comma_decade_exact_summary source H terminal"
  shows "comma_decade_exact_summary target H terminal"
  using summary controls
proof (induction rule: comma_decade_exact_summary.induct)
  case (fork s a)
  have target_control:
    "comma_decade_control target = Comma_Decade_Fork a 0"
    using fork.hyps fork.prems by simp
  show ?case
    by (rule comma_decade_exact_summary.fork[OF target_control])
next
  case (landmine s)
  have target_control:
    "comma_decade_control target = Comma_Decade_Landmine 0"
    using landmine.hyps landmine.prems by simp
  show ?case
    by (rule comma_decade_exact_summary.landmine[OF target_control])
next
  case (crossing s t n terminal)
  have target_control:
    "comma_decade_control target = Comma_Decade_Continue t"
    using crossing.hyps(1) crossing.prems by simp
  show ?case
    by (rule comma_decade_exact_summary.crossing
      [OF target_control crossing.hyps(2)])
qed

lemma comma_semantic_future_exact_summary_orbit_transport:
  assumes phase: "phase<924"
    and x: "x\<le>90" and y: "y\<le>90"
    and same: "comma_offset_orbit x=comma_offset_orbit y"
    and summary:
      "comma_decade_exact_summary (Comma_Decade phase x) H terminal"
  shows "comma_decade_exact_summary (Comma_Decade phase y) H terminal"
proof -
  have controls:
    "comma_decade_control (Comma_Decade phase x) =
      comma_decade_control (Comma_Decade phase y)"
    by (rule comma_decade_control_orbit_congruent[OF x y same])
  show ?thesis
    by (rule comma_semantic_future_exact_summary_control_transport
      [OF controls summary])
qed


ML \<open>
  val published = @{thms
    comma_semantic_future_exact_summary_control_transport
    comma_semantic_future_exact_summary_orbit_transport}
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "decade exact summary orbit transport" published
\<close>

end
