theory Comma_Symbolic_Decade_Provider
  imports Comma_Phase134_Qualitative_Stop
begin

text \<open>The function follows the checked semantic class actions. It does
not accept a rank, countdown, physical occurrence history or a packed Stop
value. The phase-134 well-founded relation authenticates recursion. Physical
elapsed weights are supplied by separately checked source actions.\<close>

function comma_symbolic_class_summary ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> comma_decade_terminal) option" where
  "comma_symbolic_class_summary phase cid =
    (if comma_semantic_phase_class_valid phase cid then
      (case comma_semantic_phase_program_class_step phase cid of
         Comma_Phase_Class_Invalid \<Rightarrow> None
       | Comma_Phase_Class_Fork a delta \<Rightarrow>
           (if delta=0 then Some (0,Comma_Terminal_Fork a) else None)
       | Comma_Phase_Class_Landmine delta \<Rightarrow>
           (if delta=0 then Some (0,Comma_Terminal_Landmine) else None)
       | Comma_Phase_Class_Continue next_phase next_cid \<Rightarrow>
           map_option (\<lambda>(h,terminal). (Suc h,terminal))
             (comma_symbolic_class_summary next_phase next_cid))
     else None)"
  by pat_completeness auto
termination
  apply (relation "comma_program_continue_relation_qualitative")
   apply (rule comma_continue_phase_134_qualitative_wf)
  by (auto simp: comma_program_continue_relation_qualitative_def)

theorem comma_symbolic_class_summary_source_exact:
  fixes phase offset :: nat
  assumes source: "comma_decade_admitted (Comma_Decade phase offset)"
  shows "\<exists>h terminal. comma_symbolic_class_summary phase (comma_offset_orbit offset) = Some (h,terminal)
    \<and> comma_decade_exact_summary (Comma_Decade phase offset) h terminal"
proof -
  have all_sources: "\<And>state. \<forall>phase cid offset.
      state = (phase,cid) \<longrightarrow>
      comma_decade_admitted (Comma_Decade phase offset) \<longrightarrow>
      comma_offset_orbit offset = cid \<longrightarrow>
      (\<exists>h terminal. comma_symbolic_class_summary phase cid = Some (h,terminal) \<and>
        comma_decade_exact_summary (Comma_Decade phase offset) h terminal)"
  proof -
    fix state
    show "\<forall>phase cid offset. state = (phase,cid) \<longrightarrow>
      comma_decade_admitted (Comma_Decade phase offset) \<longrightarrow>
      comma_offset_orbit offset = cid \<longrightarrow>
      (\<exists>h terminal. comma_symbolic_class_summary phase cid = Some (h,terminal) \<and>
        comma_decade_exact_summary (Comma_Decade phase offset) h terminal)"
    proof (induction state rule: wf_induct_rule[OF comma_continue_phase_134_qualitative_wf, case_names less])
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
        show "\<exists>h terminal. comma_symbolic_class_summary phase cid = Some (h,terminal) \<and>
            comma_decade_exact_summary ?source h terminal"
        proof (cases "comma_decade_control ?source")
          case (Comma_Decade_Fork a delta)
          have delta: "delta = 0"
            using comma_decade_terminal_delta(1)[OF admitted] Comma_Decade_Fork by blast
          have actual: "comma_decade_control ?source = Comma_Decade_Fork a 0"
            using Comma_Decade_Fork delta by simp
          have "comma_decade_exact_summary ?source 0 (Comma_Terminal_Fork a)"
            by (rule comma_decade_exact_summary.fork[OF actual])
          then show ?thesis using source_control Comma_Decade_Fork delta valid
            by (auto simp: comma_symbolic_class_summary.simps)
        next
          case (Comma_Decade_Landmine delta)
          have delta: "delta = 0"
            using comma_decade_terminal_delta(2)[OF admitted] Comma_Decade_Landmine by blast
          have actual: "comma_decade_control ?source = Comma_Decade_Landmine 0"
            using Comma_Decade_Landmine delta by simp
          have "comma_decade_exact_summary ?source 0 Comma_Terminal_Landmine"
            by (rule comma_decade_exact_summary.landmine[OF actual])
          then show ?thesis using source_control Comma_Decade_Landmine delta valid
            by (auto simp: comma_symbolic_class_summary.simps)
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
          obtain h terminal where result:
              "comma_symbolic_class_summary next_phase (comma_offset_orbit next_offset) = Some (h,terminal)"
            and summary: "comma_decade_exact_summary (Comma_Decade next_phase next_offset) h terminal"
            using less.IH[OF edge] child by blast
          have "comma_decade_exact_summary ?source (Suc h) terminal"
            using comma_decade_exact_summary.crossing[OF Comma_Decade_Continue] summary target by simp
          then show ?thesis using result move valid
            by (auto simp: comma_symbolic_class_summary.simps)
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
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Source-bound symbolic decade action" @{thms comma_symbolic_class_summary_source_exact};
  val _ = Comma_Proof_Dependency_Audit.require_paths @{context}
    "Symbolic decade action excludes packed termination"
    ["comma_frontier_m204_bellman_native", "comma_frontier_m204_exact_stop_from_checked_bellman",
      "comma_phase_class_survival_lengths", "comma_terminal_weight_decode"]
    @{thms comma_symbolic_class_summary_source_exact};
\<close>
end
