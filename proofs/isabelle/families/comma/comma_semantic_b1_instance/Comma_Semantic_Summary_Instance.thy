theory Comma_Semantic_Summary_Instance
  imports Comma_Semantic_B1_Instance
    Comma_Semantic_Future.Comma_Semantic_Boundary
begin

text \<open>The foundational summary is defined using representation-independent
semantic action power. Its executable code equation consumes the authenticated
M204 weight directly. It does not reconstruct a graph-power certificate or
replay a scalar decade trajectory.\<close>

lemma comma_semantic_b1_action_power_b32_stop242:
  assumes root: "root<46" and phase: "phase<924"
  obtains D where
    "comma_semantic_b1_action_power 5 phase root =
      Comma_Semantic_B1_Stop D" and "D\<le>242"
proof -
  have certified:
      "\<exists>D. comma_semantic_b1_action_power 5 phase root =
          Comma_Semantic_B1_Stop D \<and> D\<le>242"
    using comma_semantic_b1_action_b32_stop242_checked root phase by blast
  obtain D where action_result:
      "comma_semantic_b1_action_power 5 phase root =
        Comma_Semantic_B1_Stop D"
    and bound: "D\<le>242"
    using certified by blast
  show thesis by (rule that[OF action_result bound])
qed

lemma comma_semantic_decade_summary_code:
  "comma_semantic_decade_summary s =
    (case s of Comma_Decade r x \<Rightarrow>
      if comma_decade_admitted s then
        Some (comma_terminal_weight_decode
          (comma_frontier_m204_weight r (comma_offset_orbit x)))
      else None)"
proof (cases s)
  case (Comma_Decade r x)
  show ?thesis
  proof (cases "comma_decade_admitted s")
    case False
    then show ?thesis by (simp add: comma_semantic_decade_summary_def)
  next
    case True
    have admitted_state: "comma_decade_admitted (Comma_Decade r x)"
      using True by (simp only: Comma_Decade)
    have phase: "r<924" using True Comma_Decade by simp
    have root: "comma_offset_orbit x<46" by (rule comma_offset_orbit_bound)
    have action:
      "comma_semantic_b1_action_power 5 r (comma_offset_orbit x) =
        Comma_Semantic_B1_Stop
          (comma_frontier_m204_weight r (comma_offset_orbit x))"
      by (rule comma_frontier_m204_exact_weight_from_checked_bellman
        [OF comma_frontier_m204_bellman_native phase root])
    show ?thesis
      by (simp only: comma_semantic_decade_summary_def Comma_Decade
        comma_decade_state.case admitted_state if_True action comma_semantic_b1_result.case)
  qed
qed

declare comma_semantic_decade_summary_def[code drop]
declare comma_semantic_decade_summary_code[code]

theorem comma_semantic_decade_summary_total_exact:
  assumes admitted: "comma_decade_admitted s"
  shows "\<exists>h terminal.
    comma_semantic_decade_summary s=Some (h,terminal) \<and>
    h\<le>26 \<and> comma_decade_exact_summary s h terminal"
proof (rule comma_semantic_decade_summary_total_exact_for_bound)
  show "\<And>r i. r<924 \<Longrightarrow> i<46 \<Longrightarrow>
      \<exists>D. comma_semantic_b1_action_power 5 r i =
        Comma_Semantic_B1_Stop D \<and> D\<le>242"
  proof -
    fix r i :: nat
    assume phase: "r<924" and root: "i<46"
    obtain D where action:
        "comma_semantic_b1_action_power 5 r i =
          Comma_Semantic_B1_Stop D"
      and bound: "D\<le>242"
      by (rule comma_semantic_b1_action_power_b32_stop242[OF root phase])
    show "\<exists>D. comma_semantic_b1_action_power 5 r i =
        Comma_Semantic_B1_Stop D \<and> D\<le>242"
      by (rule exI[of _ D]) (rule conjI[OF action bound])
  qed
  show "comma_decade_admitted s" by (rule admitted)
qed

theorem comma_semantic_decade_summary_provider_exact:
  "comma_semantic_decade_provider_exact comma_semantic_decade_summary"
  unfolding comma_semantic_decade_provider_exact_def
proof (intro allI impI)
  fix s assume admitted: "comma_decade_admitted s"
  obtain h terminal where lookup:
      "comma_semantic_decade_summary s=Some (h,terminal)"
    and height: "h\<le>26"
    and summary: "comma_decade_exact_summary s h terminal"
    using comma_semantic_decade_summary_total_exact[OF admitted] by blast
  show "case comma_semantic_decade_summary s of None \<Rightarrow> False
      | Some (h,terminal) \<Rightarrow>
          h\<le>26 \<and> comma_decade_exact_summary s h terminal"
    using lookup height summary by simp
qed

lemmas comma_semantic_concrete_boundary_occurrence_bridge =
  comma_semantic_boundary_occurrence_bridge
    [OF comma_semantic_decade_summary_provider_exact]

lemmas comma_semantic_concrete_boundary_strong_occurrence_bridge =
  comma_semantic_boundary_strong_occurrence_bridge
    [OF comma_semantic_decade_summary_provider_exact]

lemma comma_semantic_decade_summary_rejects_noncanonical:
  "comma_semantic_decade_summary (Comma_Decade r 98)=None"
  by (simp add: comma_semantic_decade_summary_def)

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Concrete semantic B32 decade and boundary provider"
    @{thms comma_semantic_decade_summary_total_exact
      comma_semantic_decade_summary_provider_exact
      comma_semantic_concrete_boundary_occurrence_bridge
      comma_semantic_concrete_boundary_strong_occurrence_bridge};
\<close>

end
