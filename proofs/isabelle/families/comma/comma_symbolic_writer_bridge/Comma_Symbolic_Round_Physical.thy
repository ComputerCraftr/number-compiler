theory Comma_Symbolic_Round_Physical
  imports Comma_Symbolic_Round_Action
begin

text \<open>The round receipt retains only the physical duration, terminal
source and typed control.  Its sector witnesses are source-bound functions;
no list of intermediate occurrences is materialized.\<close>

lemma comma_symbolic_sector_finish:
  assumes source: "comma_round_admitted source" and exponent: "5 \<le> p"
  shows "comma_literal_path (comma_symbolic_sector_duration p source)
      (comma_chart_value p source)
      (comma_chart_value p (comma_decisive_sector_target (p mod 924) source))"
proof -
  note cut = comma_symbolic_sector_cut_exact[OF source exponent, of "comma_symbolic_sector_duration p source"]
  show ?thesis using cut by (auto elim: comma_literal_path.cases)
qed

lemma comma_symbolic_decisive_next_physical:
  assumes source: "comma_round_admitted source" and exponent: "5 \<le> p"
    and packet: "comma_decisive_endpoint_packet (p mod 924) source = (target,Comma_Next successor)"
  shows "comma_round_admitted target"
    and "comma_round_admitted successor"
    and "comma_literal_path 1 (comma_chart_value p target) (comma_chart_value p successor)"
proof -
  have target: "target = comma_decisive_sector_target (p mod 924) source"
    using packet by (simp add: comma_decisive_endpoint_packet_def Let_def)
  have target_admitted: "comma_round_admitted target"
    using comma_decisive_packet_target_admitted[OF source, of "p mod 924"] packet by simp
  have step: "comma_finite_step (p mod 924) target = Comma_Next successor"
    using packet by (auto simp: comma_decisive_endpoint_packet_def Let_def comma_fast_step_correct)
  have target_near: "\<exists>f delta h. target = Comma_Near f delta h"
  proof (cases source)
    case (Comma_Entry f delta offset)
    have entry_admitted: "comma_round_admitted (Comma_Entry f delta offset)"
      using source Comma_Entry by simp
    note entry_target = comma_decisive_entry_target_diagonal[OF entry_admitted, of "p mod 924"]
    show ?thesis using target Comma_Entry entry_target by blast
  next
    case (Comma_Near f delta h)
    then show ?thesis using target by (simp add: comma_decisive_sector_target.simps)
  qed
  obtain f delta h where near: "target = Comma_Near f delta h" using target_near by blast
  have bounds: "1 \<le> f" "f \<le> 9" "1 \<le> h" "h \<le> 540"
    using target_admitted near by simp_all
  show "comma_round_admitted target" by (rule target_admitted)
  show "comma_round_admitted successor" by (rule comma_round_next_admitted[OF target_admitted step])
  have near_step: "comma_finite_step (p mod 924) (Comma_Near f delta h) = Comma_Next successor"
    using step near by simp
  show "comma_literal_path 1 (comma_chart_value p target) (comma_chart_value p successor)"
    using comma_near_chart_next_literal(1)[OF bounds(1,2) exponent bounds(3,4) near_step] near
    by simp
qed


theorem comma_symbolic_round_receipt_physical:
  assumes exponent: "5 \<le> p" and source: "comma_round_admitted source"
  shows "comma_literal_path (fst (comma_symbolic_round_receipt p source))
      (comma_chart_value p source)
      (comma_chart_value p (fst (snd (comma_symbolic_round_receipt p source))))"
  using source exponent
proof (induction p source rule: comma_symbolic_round_receipt.induct[case_names step])
  case (step p source)
  obtain target event where packet:
    "comma_decisive_endpoint_packet (p mod 924) source = (target,event)"
    by (cases "comma_decisive_endpoint_packet (p mod 924) source") auto
  have target: "target = comma_decisive_sector_target (p mod 924) source"
    using packet by (simp add: comma_decisive_endpoint_packet_def Let_def)
  note sector = comma_symbolic_sector_finish[OF step.prems(1) step.prems(2)]
  have prefix: "comma_literal_path (comma_symbolic_sector_duration p source)
      (comma_chart_value p source) (comma_chart_value p target)"
    using sector by (simp only: target)
  show ?case
  proof (cases event)
    case (Comma_Next successor)
    have next_packet: "comma_decisive_endpoint_packet (p mod 924) source =
        (target,Comma_Next successor)" using packet Comma_Next by simp
    have successor: "comma_round_admitted successor"
      and edge: "comma_literal_path 1 (comma_chart_value p target) (comma_chart_value p successor)"
      using comma_symbolic_decisive_next_physical[OF step.prems(1) step.prems(2) next_packet] by blast+
    have head: "comma_literal_path (Suc (comma_symbolic_sector_duration p source))
        (comma_chart_value p source) (comma_chart_value p successor)"
      using comma_literal_path_append[OF prefix edge] by simp
    show ?thesis
    proof (cases "comma_round_crossing target successor")
      case True
      have result: "comma_symbolic_round_receipt p source =
          (Suc (comma_symbolic_sector_duration p source),successor,Comma_Round_Cross successor)"
        using step.prems packet Comma_Next True
        by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
      show ?thesis using head result by simp
    next
      case False
      have tail: "comma_literal_path (fst (comma_symbolic_round_receipt p successor))
          (comma_chart_value p successor)
          (comma_chart_value p (fst (snd (comma_symbolic_round_receipt p successor))))"
        using step.IH step.prems packet Comma_Next False successor by (auto simp: Let_def)
      have full: "comma_literal_path (Suc (comma_symbolic_sector_duration p source) +
          fst (comma_symbolic_round_receipt p successor)) (comma_chart_value p source)
          (comma_chart_value p (fst (snd (comma_symbolic_round_receipt p successor))))"
        by (rule comma_literal_path_append[OF head tail])
      obtain n last outcome where tail_result:
          "comma_symbolic_round_receipt p successor = (n,last,outcome)"
        by (cases "comma_symbolic_round_receipt p successor") (auto split: prod.splits)
      have result: "comma_symbolic_round_receipt p source =
          (Suc (comma_symbolic_sector_duration p source)+n,last,outcome)"
        using step.prems packet Comma_Next False tail_result
        by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
      show ?thesis using full result tail_result by simp
    qed
  next
    case (Comma_Fork a delta)
    have result: "comma_symbolic_round_receipt p source =
        (comma_symbolic_sector_duration p source,target,Comma_Round_Fork a delta)"
      using step.prems packet Comma_Fork
      by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
    show ?thesis using prefix result by simp
  next
    case (Comma_Landmine delta)
    have result: "comma_symbolic_round_receipt p source =
        (comma_symbolic_sector_duration p source,target,Comma_Round_Landmine delta)"
      using step.prems packet Comma_Landmine
      by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
    show ?thesis using prefix result by simp
  next
    case Comma_Invalid
    have result: "comma_symbolic_round_receipt p source =
        (comma_symbolic_sector_duration p source,target,Comma_Round_Invalid)"
      using step.prems packet Comma_Invalid
      by (subst comma_symbolic_round_receipt.simps) (simp add: Let_def)
    show ?thesis using prefix result by simp
  qed
qed

ML \<open>
  val checked = @{thms comma_symbolic_sector_finish comma_symbolic_decisive_next_physical
    comma_symbolic_round_receipt_physical};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Round physical source used an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Round physical source contains skipped proofs" else ();
  val _ = Comma_Proof_Dependency_Audit.require_paths @{context}
    "Round source excludes legacy authority"
    ["comma_round_close", "comma_finite_macro", "comma_terminal_weight_decode",
     "comma_phase_class_survival_lengths", "comma_python_first_terminal_walk"] checked;
\<close>
end
