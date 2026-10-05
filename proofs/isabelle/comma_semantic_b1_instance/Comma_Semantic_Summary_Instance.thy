theory Comma_Semantic_Summary_Instance
  imports Comma_Semantic_B1_Instance
    Comma_Semantic_Future.Comma_Semantic_Boundary
begin

text \<open>The concrete decade provider consumes the checked semantic B32
result.  It does not construct a sparse table or consult a rank witness.
The terminal weight is decoded only after the checked Stop result has been
selected for the receiving phase and source orbit.\<close>

definition comma_semantic_decade_summary ::
  "comma_decade_state \<Rightarrow> comma_decade_residual option" where
  "comma_semantic_decade_summary s =
    (case s of Comma_Decade r x \<Rightarrow>
      if comma_decade_admitted s then
        (case comma_semantic_b1_crt_power_result 5 (comma_offset_orbit x) r of
          Some (Comma_Semantic_B1_Stop D) \<Rightarrow>
            Some (comma_terminal_weight_decode D)
        | _ \<Rightarrow> None)
      else None)"

lemma comma_semantic_decade_summary_total_exact:
  assumes admitted: "comma_decade_admitted s"
  shows "\<exists>h terminal.
    comma_semantic_decade_summary s=Some (h,terminal) \<and>
    h\<le>26 \<and> comma_decade_exact_summary s h terminal"
proof (cases s)
  case (Comma_Decade r x)
  have phase: "r<924" and offset: "x\<le>90"
    using admitted Comma_Decade by simp_all
  have root: "comma_offset_orbit x<46"
    by (rule comma_offset_orbit_bound)
  obtain D where result:
      "comma_semantic_b1_crt_power_result 5 (comma_offset_orbit x) r =
        Some (Comma_Semantic_B1_Stop D)"
    and bound: "D\<le>242"
    using comma_semantic_b1_crt_b32_stop242_checked[OF root phase] by blast
  let ?provider = "\<lambda>q i. the (comma_semantic_b1_crt_power_result 5 i q)"
  have exact: "\<And>q i. q<924 \<Longrightarrow> i<46 \<Longrightarrow>
      ?provider q i=comma_semantic_b1_of_word (comma_orbit_word 5 q i)"
    using comma_semantic_b1_crt_b32_result_exact by simp
  have stopped: "?provider r (comma_offset_orbit x)=Comma_Semantic_B1_Stop D"
    using result by simp
  have exponent: "5\<le>r+924" by simp
  have phase_match: "(r+924) mod 924=r" using phase by simp
  obtain h terminal where decode: "comma_terminal_weight_decode D=(h,terminal)"
    and height: "h\<le>26"
    and summary: "comma_decade_exact_summary (Comma_Decade r x) h terminal"
    using comma_semantic_b32_stop_exact_occurrence_for_offset
      [OF exact phase offset exponent phase_match stopped bound] by blast
  have lookup: "comma_semantic_decade_summary s=Some (h,terminal)"
    using admitted Comma_Decade result decode
    by (simp add: comma_semantic_decade_summary_def)
  show ?thesis using lookup height summary Comma_Decade by blast
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
