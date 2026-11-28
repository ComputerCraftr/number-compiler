theory Comma_Qualitative_Stop
  imports Comma_Symbolic_Class_Step
begin

definition comma_program_continue_relation_qualitative ::
    "((nat \<times> nat) \<times> (nat \<times> nat)) set" where
  "comma_program_continue_relation_qualitative = {(child,parent).
    comma_semantic_phase_class_valid (fst parent) (snd parent) \<and>
    comma_semantic_phase_program_class_step (fst parent) (snd parent) =
      Comma_Phase_Class_Continue (fst child) (snd child)}"

theorem comma_qualitative_wf_source_typed_stop:
  fixes phase offset :: nat
  assumes wellfounded: "wf comma_program_continue_relation_qualitative"
    and source: "comma_decade_admitted (Comma_Decade phase offset)"
  shows "\<exists>h terminal. comma_decade_exact_summary (Comma_Decade phase offset) h terminal"
proof -
  have all_sources: "\<And>state. \<forall>phase cid offset.
      state = (phase,cid) \<longrightarrow>
      comma_decade_admitted (Comma_Decade phase offset) \<longrightarrow>
      comma_offset_orbit offset = cid \<longrightarrow>
      (\<exists>h terminal. comma_decade_exact_summary (Comma_Decade phase offset) h terminal)"
  proof -
    fix state
    show "\<forall>phase cid offset. state = (phase,cid) \<longrightarrow>
      comma_decade_admitted (Comma_Decade phase offset) \<longrightarrow>
      comma_offset_orbit offset = cid \<longrightarrow>
      (\<exists>h terminal. comma_decade_exact_summary (Comma_Decade phase offset) h terminal)"
    proof (induction state rule: wf_induct_rule[OF wellfounded, case_names less])
      case (less state)
      show ?case
      proof (intro allI impI)
        fix phase cid offset :: nat
        assume state: "state = (phase,cid)"
          and admitted: "comma_decade_admitted (Comma_Decade phase offset)"
          and orbit: "comma_offset_orbit offset = cid"
        let ?source = "Comma_Decade phase offset"
        have valid: "comma_semantic_phase_class_valid phase cid"
          using comma_semantic_phase_class_source_valid[OF admitted] orbit by simp
        have limits: "phase < 924" "comma_offset_orbit offset < 46"
          using valid orbit by (auto simp: comma_semantic_phase_class_valid_def)
        have source_control: "comma_semantic_phase_program_class_step phase cid =
            comma_phase_classify_decade_control comma_offset_orbit
              (comma_decade_control ?source)"
          using comma_semantic_phase_program_class_step_exact[OF limits]
            comma_semantic_phase_class_source_control[OF admitted] orbit by simp
        show "\<exists>h terminal. comma_decade_exact_summary ?source h terminal"
        proof (cases "comma_decade_control ?source")
          case (Comma_Decade_Fork a delta)
          have delta: "delta = 0"
            using comma_decade_terminal_delta(1)[OF admitted] Comma_Decade_Fork by blast
          have actual: "comma_decade_control ?source = Comma_Decade_Fork a 0"
            using Comma_Decade_Fork delta by simp
          have "comma_decade_exact_summary ?source 0 (Comma_Terminal_Fork a)"
            by (rule comma_decade_exact_summary.fork[OF actual])
          then show ?thesis by blast
        next
          case (Comma_Decade_Landmine delta)
          have delta: "delta = 0"
            using comma_decade_terminal_delta(2)[OF admitted] Comma_Decade_Landmine by blast
          have actual: "comma_decade_control ?source = Comma_Decade_Landmine 0"
            using Comma_Decade_Landmine delta by simp
          have "comma_decade_exact_summary ?source 0 Comma_Terminal_Landmine"
            by (rule comma_decade_exact_summary.landmine[OF actual])
          then show ?thesis by blast
        next
          case (Comma_Decade_Continue target)
          obtain next_phase next_offset where target: "target = Comma_Decade next_phase next_offset"
            by (cases target) auto
          have child: "comma_decade_admitted (Comma_Decade next_phase next_offset)"
            using comma_decade_control_closed(2)[OF admitted Comma_Decade_Continue refl]
            by (simp only: target)
          have move: "comma_semantic_phase_program_class_step phase cid =
              Comma_Phase_Class_Continue next_phase (comma_offset_orbit next_offset)"
            using source_control Comma_Decade_Continue by (simp add: target)
          have edge: "((next_phase,comma_offset_orbit next_offset),state) \<in>
              comma_program_continue_relation_qualitative"
            using valid move state by (simp add: comma_program_continue_relation_qualitative_def)
          obtain h terminal where summary:
              "comma_decade_exact_summary (Comma_Decade next_phase next_offset) h terminal"
            using less.IH[OF edge] child by blast
          have "comma_decade_exact_summary ?source (Suc h) terminal"
            using comma_decade_exact_summary.crossing[OF Comma_Decade_Continue] summary target by simp
          then show ?thesis by blast
        next
          case Comma_Decade_Invalid
          then show ?thesis using comma_decade_control_closed(1)[OF admitted refl] by simp
        qed
      qed
    qed
  qed
  show ?thesis using all_sources[of "(phase,comma_offset_orbit offset)"] source by blast
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_paths @{context}
    "Generic wf typed Stop consumer"
    ["comma_continue_qualitative_source_typed_stop", "comma_single_source_summary_if_not_survives_draft",
     "comma_frontier_m204_bellman_native", "comma_program_absent_power_draft"]
    @{thms comma_qualitative_wf_source_typed_stop};
\<close>

end
