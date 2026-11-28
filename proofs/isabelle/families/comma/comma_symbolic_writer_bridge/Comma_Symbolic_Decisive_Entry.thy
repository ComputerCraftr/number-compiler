theory Comma_Symbolic_Decisive_Entry
  imports Comma_Symbolic_First_Sector_Writer
    Comma_Decisive_Endpoint_Quotient.Comma_Decisive_Endpoint_Quotient
begin

text \<open>The physical first-sector writer and the source-first decisive
round action meet at the same admitted Entry.  The packet event is selected
before any Future quotient is consulted; chronological points and remaining
duration come from the writer itself.\<close>

theorem comma_symbolic_decisive_entry_packet:
  fixes f p delta offset elapsed t j :: nat and event :: comma_finite_move
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset = (elapsed,t,event)"
    and cut: "j \<le> elapsed"
  shows "comma_decisive_endpoint_packet (p mod 924) (Comma_Entry f delta offset) =
      (Comma_Near f delta t,event)"
    and "comma_literal_path j (comma_chart_value p (Comma_Entry f delta offset))
      (comma_writer_point (comma_first_sector_writer f p delta offset elapsed t) False j)"
    and "comma_literal_path (elapsed-j)
      (comma_writer_point (comma_first_sector_writer f p delta offset elapsed t) False j)
      (comma_chart_value p (Comma_Near f delta t))"
proof -
  have admitted: "comma_round_admitted (Comma_Entry f delta offset)"
    using sector offset by simp
  have period: "comma_finite_period f (offset mod 10) \<noteq> 0"
    using comma_finite_period_in_catalog[rule_format, of f "offset mod 10"] sector
    by (auto simp: comma_cycle_displacements_def)
  let ?h = "comma_finite_headroom f (p mod 924) delta offset"
  have step: "comma_fast_step ((p mod 924) mod 924) (Comma_Entry f delta offset) =
      Comma_Next (Comma_Near f delta ?h)"
    using sector offset period
    by (simp add: comma_fast_step_correct comma_entry_control_formula)
  have target: "comma_decisive_sector_target (p mod 924) (Comma_Entry f delta offset) =
      Comma_Near f delta (snd (comma_near_closed_germ f ?h))"
    using comma_decisive_sector_target_refines_fast[OF admitted, of "p mod 924"] step
    by (simp add: comma_fast_sector_target.simps)
  have residual: "snd (comma_near_closed_germ f ?h) = t"
    using packet by (auto simp: comma_c1_first_sector_def Let_def split: prod.splits)
  have action: "event = comma_finite_step (p mod 924) (Comma_Near f delta t)"
    using comma_c1_first_sector_source(7)[OF sector exponent offset packet] .
  show "comma_decisive_endpoint_packet (p mod 924) (Comma_Entry f delta offset) =
      (Comma_Near f delta t,event)"
    using target residual action
    by (simp add: comma_decisive_endpoint_packet_def Let_def comma_fast_step_correct)
  show "comma_literal_path j (comma_chart_value p (Comma_Entry f delta offset))
      (comma_writer_point (comma_first_sector_writer f p delta offset elapsed t) False j)"
    by (rule comma_first_sector_writer_selected_cut(1)[OF sector exponent offset packet cut])
  show "comma_literal_path (elapsed-j)
      (comma_writer_point (comma_first_sector_writer f p delta offset elapsed t) False j)
      (comma_chart_value p (Comma_Near f delta t))"
    by (rule comma_first_sector_writer_selected_cut(2)[OF sector exponent offset packet cut])
qed

ML \<open>
  val checked = @{thms comma_symbolic_decisive_entry_packet};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Decisive Entry writer used an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Decisive Entry writer contains skipped proofs" else ();
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Source-issued decisive Entry writer" checked;
  val _ = Comma_Proof_Dependency_Audit.require_paths @{context}
    "Source-issued writer excludes packed or occurrence authority"
    ["comma_frontier_m204_bellman_native", "comma_terminal_weight_decode",
      "comma_phase_class_survival_lengths", "comma_python_first_terminal_walk"] checked;
\<close>
end
