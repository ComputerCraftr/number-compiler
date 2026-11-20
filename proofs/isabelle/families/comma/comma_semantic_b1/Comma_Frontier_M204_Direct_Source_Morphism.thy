theory Comma_Frontier_M204_Direct_Source_Morphism
  imports Comma_Frontier_M204_Checker
begin

text \<open>
The M204 source morphism must not depend on a Frontier24 source bundle,
source-specific closure rows, or an application-ID table.  A frozen typed
one-step MDD is the only finite candidate.  Its authenticity is deliberately
separate from the generic source theorem: the candidate is not authority until
its universal 46-class/924-phase equation is kernel checked.
\<close>

definition comma_frontier_m204_direct_action ::
  "nat comma_crt_mdd_node list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_frontier_m204_direct_action nodes roots phase cid =
    comma_frontier_m204_mdd_value [3,4,7,11] nodes roots phase cid"

definition comma_frontier_m204_direct_step_checked ::
  "nat comma_crt_mdd_node list \<Rightarrow> nat list \<Rightarrow> bool" where
  "comma_frontier_m204_direct_step_checked nodes roots \<longleftrightarrow>
     comma_crt_mdd_table_wellformed [3,4,7,11] nodes \<and>
     length roots = 46 \<and>
     (\<forall>cid<46. roots ! cid < length nodes) \<and>
     (\<forall>phase<924. \<forall>cid<46.
        comma_crt_mdd_eval_phase [3,4,7,11] nodes phase (roots ! cid) =
          Some (comma_frontier_m204_action_code phase
            (comma_semantic_phase_program_class_step phase cid)))"

lemma comma_frontier_m204_direct_class_step:
  assumes checked: "comma_frontier_m204_direct_step_checked nodes roots"
    and phase: "phase < 924" and cid: "cid < 46"
  shows "comma_frontier_m204_direct_action nodes roots phase cid =
    comma_frontier_m204_action_code phase
      (comma_semantic_phase_program_class_step phase cid)"
  using checked phase cid
  by (simp add: comma_frontier_m204_direct_step_checked_def
    comma_frontier_m204_direct_action_def comma_frontier_m204_mdd_value_def)

text \<open>
The underlying mathematical source morphism is already a theorem of the
symbolic class-step algebra.  It needs NO MDD, Bellman witness, or class table.
The MDD witness is subsequently checked against this authoritative action.
\<close>

lemma comma_frontier_m204_source_control_morphism:
  assumes admitted: "comma_decade_admitted (Comma_Decade phase off)"
  shows "comma_semantic_phase_program_class_step phase (comma_offset_orbit off) =
    comma_phase_classify_decade_control comma_offset_orbit
      (comma_decade_control (Comma_Decade phase off))"
proof -
  have valid: "comma_semantic_phase_class_valid phase (comma_offset_orbit off)"
    by (rule comma_semantic_phase_class_source_valid[OF admitted])
  have phase: "phase < 924" and cid: "comma_offset_orbit off < 46"
    using valid by (auto simp: comma_semantic_phase_class_valid_def)
  have program:
    "comma_semantic_phase_program_class_step phase (comma_offset_orbit off) =
      comma_semantic_phase_class_step phase (comma_offset_orbit off)"
    by (rule comma_semantic_phase_program_class_step_exact[OF phase cid])
  have source:
    "comma_semantic_phase_class_step phase (comma_offset_orbit off) =
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control (Comma_Decade phase off))"
    by (rule comma_semantic_phase_class_source_control[OF admitted])
  show ?thesis using program source by simp
qed

theorem comma_frontier_m204_source_future_congruence:
  assumes phase: "phase < 924" and left: "left \<le> 90" and right: "right \<le> 90"
    and same: "comma_offset_orbit left = comma_offset_orbit right"
  shows "comma_decade_block_power k (Comma_Decade phase left) =
    comma_decade_block_power k (Comma_Decade phase right)"
  by (rule comma_semantic_phase_class_future_right_congruent[OF phase left right same])

text \<open>
This is the generic physical-source morphism.  It uses the EXISTING
source-independent orbit refinement and exact program/class-step theorem.
The source is never used to key, allocate, or prove the MDD representative.
\<close>

lemma comma_frontier_m204_direct_source_step:
  assumes checked: "comma_frontier_m204_direct_step_checked nodes roots"
    and admitted: "comma_decade_admitted (Comma_Decade phase off)"
  shows "comma_crt_mdd_eval_phase [3,4,7,11] nodes phase
      (roots ! comma_offset_orbit off) =
    Some (comma_frontier_m204_action_code phase
      (comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control (Comma_Decade phase off))))"
proof -
  have valid: "comma_semantic_phase_class_valid phase (comma_offset_orbit off)"
    by (rule comma_semantic_phase_class_source_valid[OF admitted])
  have phase: "phase < 924" and cid: "comma_offset_orbit off < 46"
    using valid by (auto simp: comma_semantic_phase_class_valid_def)
  have physical:
    "comma_semantic_phase_program_class_step phase (comma_offset_orbit off) =
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control (Comma_Decade phase off))"
    by (rule comma_frontier_m204_source_control_morphism[OF admitted])
  have class_code:
    "comma_crt_mdd_eval_phase [3,4,7,11] nodes phase
      (roots ! comma_offset_orbit off) =
      Some (comma_frontier_m204_action_code phase
        (comma_semantic_phase_program_class_step phase (comma_offset_orbit off)))"
    using checked phase cid
    by (simp add: comma_frontier_m204_direct_step_checked_def)
  show ?thesis using class_code physical by simp
qed

lemma comma_frontier_m204_direct_bellman:
  assumes step: "comma_frontier_m204_direct_step_checked nodes roots"
    and code: "comma_frontier_m204_code_bellman D
       (comma_frontier_m204_direct_action nodes roots)"
  shows "comma_frontier_m204_bellman D"
proof (rule comma_frontier_m204_code_to_bellman[OF code])
  fix phase cid :: nat
  assume phase: "phase < 924" and cid: "cid < 46"
  show "comma_frontier_m204_direct_action nodes roots phase cid =
    comma_frontier_m204_action_code phase
      (comma_semantic_phase_program_class_step phase cid)"
    by (rule comma_frontier_m204_direct_class_step[OF step phase cid])
qed

text \<open>
The certified class-step equation plus the SINGLE checked Bellman formula
implies exact physical summaries for every admitted source.  No individual
source row, source integer, headroom, or Frontier24 closure theorem appears as
an assumption.
\<close>

theorem comma_frontier_m204_direct_exact_source:
  fixes source :: comma_decade_state
  assumes step: "comma_frontier_m204_direct_step_checked nodes roots"
    and code: "comma_frontier_m204_code_bellman D
       (comma_frontier_m204_direct_action nodes roots)"
    and admitted: "comma_decade_admitted source"
  shows "\<exists>h tau. h \<le> 26 \<and>
    comma_decade_block_power 5 source = Comma_Block_Stop h tau \<and>
    comma_residual_block 32 (h,tau) = Comma_Residual_Stop h tau \<and>
    comma_decade_exact_summary source h tau \<and>
    comma_frontier_m204_state_value D source = comma_terminal_weight_encode h tau"
proof -
  have bellman: "comma_frontier_m204_bellman D"
    by (rule comma_frontier_m204_direct_bellman[OF step code])
  obtain h tau where bound: "h \<le> 26"
    and block: "comma_decade_block_power 5 source = Comma_Block_Stop h tau"
    and residual: "comma_residual_block 32 (h,tau) = Comma_Residual_Stop h tau"
    and summary: "comma_decade_exact_summary source h tau"
    using comma_frontier_m204_B32_from_checked_bellman[OF bellman admitted] by blast
  have exact: "comma_frontier_m204_state_value D source =
      comma_terminal_weight_encode h tau"
    by (rule comma_frontier_m204_summary_value[OF bellman summary admitted])
  show ?thesis using bound block residual summary exact by blast
qed

theorem comma_frontier_m204_direct_B1_exact:
  assumes step: "comma_frontier_m204_direct_step_checked nodes roots"
    and code: "comma_frontier_m204_code_bellman D
       (comma_frontier_m204_direct_action nodes roots)"
    and phase: "phase < 924" and cid: "cid < 46"
  shows "\<exists>h tau. h \<le> 26 \<and>
    comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives ! cid)) h tau \<and>
    D phase cid = comma_terminal_weight_encode h tau \<and>
    comma_semantic_b1_action_power 5 phase cid =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode h tau) \<and>
    comma_terminal_weight_encode h tau \<le> 242"
proof -
  have bellman: "comma_frontier_m204_bellman D"
    by (rule comma_frontier_m204_direct_bellman[OF step code])
  show ?thesis
    by (rule comma_frontier_m204_exact_stop_from_checked_bellman[OF bellman phase cid])
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Direct source-independent M204 morphism (conditional on a checked step MDD)"
    @{thms comma_frontier_m204_direct_action_def
      comma_frontier_m204_direct_step_checked_def
      comma_frontier_m204_source_control_morphism
      comma_frontier_m204_source_future_congruence
      comma_frontier_m204_direct_class_step
      comma_frontier_m204_direct_source_step
      comma_frontier_m204_direct_bellman
      comma_frontier_m204_direct_exact_source
      comma_frontier_m204_direct_B1_exact};
\<close>

end

