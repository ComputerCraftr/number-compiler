theory Comma_Symbolic_Boundary_Source
  imports Comma_Symbolic_Boundary_Entry Comma_Symbolic_Decisive_Entry
begin

text \<open>Bind both actual Future boundary inlets to the source-issued
first-sector packet and its chronological writer cut.  North has one exact
physical inlet step; Zero is already an Entry.  The source residue is carried
by the receiving boundary, while the physical exponent remains unchanged.\<close>

theorem comma_symbolic_zero_boundary_source:
  fixes a p elapsed t j :: nat and event :: comma_finite_move
  assumes lower: "2 \<le> a" and upper: "a \<le> 9" and exponent: "5 \<le> p"
    and packet: "comma_c1_first_sector a p 0 0 = (elapsed,t,event)"
    and cut: "j \<le> elapsed"
  shows "comma_decisive_endpoint_packet (p mod 924)
      (comma_finite_initial (Comma_Z,a,p mod 924)) = (Comma_Near a 0 t,event)"
    and "comma_literal_path j
      (comma_chart_value p (comma_finite_initial (Comma_Z,a,p mod 924)))
      (comma_writer_point (comma_first_sector_writer a p 0 0 elapsed t) False j)"
    and "comma_literal_path (elapsed-j)
      (comma_writer_point (comma_first_sector_writer a p 0 0 elapsed t) False j)
      (comma_chart_value p (Comma_Near a 0 t))"
proof -
  have sector: "1 \<le> a" "a \<le> 9" using lower upper by arith+
  have offset: "(0::nat) \<le> 98" by simp
  note checked = comma_symbolic_decisive_entry_packet[OF sector exponent offset packet cut]
  show "comma_decisive_endpoint_packet (p mod 924)
      (comma_finite_initial (Comma_Z,a,p mod 924)) = (Comma_Near a 0 t,event)"
    using checked(1) by (simp add: comma_finite_initial_def)
  show "comma_literal_path j
      (comma_chart_value p (comma_finite_initial (Comma_Z,a,p mod 924)))
      (comma_writer_point (comma_first_sector_writer a p 0 0 elapsed t) False j)"
    using checked(2) by (simp add: comma_finite_initial_def)
  show "comma_literal_path (elapsed-j)
      (comma_writer_point (comma_first_sector_writer a p 0 0 elapsed t) False j)
      (comma_chart_value p (Comma_Near a 0 t))"
    using checked(3) by simp
qed

theorem comma_symbolic_north_boundary_source:
  fixes a p elapsed t j :: nat and event :: comma_finite_move
  assumes lower: "2 \<le> a" and upper: "a \<le> 9" and exponent: "5 \<le> p"
    and packet: "comma_c1_first_sector a p 0 (89+a) = (elapsed,t,event)"
    and cut: "j \<le> elapsed"
  shows "comma_finite_step (p mod 924) (comma_finite_initial (Comma_N,a,p mod 924)) =
      Comma_Next (Comma_Entry a 0 (89+a))"
    and "comma_decisive_endpoint_packet (p mod 924) (Comma_Entry a 0 (89+a)) =
      (Comma_Near a 0 t,event)"
    and "comma_literal_path (Suc j)
      (comma_chart_value p (comma_finite_initial (Comma_N,a,p mod 924)))
      (comma_writer_point (comma_first_sector_writer a p 0 (89+a) elapsed t) False j)"
    and "comma_literal_path (elapsed-j)
      (comma_writer_point (comma_first_sector_writer a p 0 (89+a) elapsed t) False j)
      (comma_chart_value p (Comma_Near a 0 t))"
proof -
  have sector: "1 \<le> a" "a \<le> 9" using lower upper by arith+
  have offset: "89+a \<le> 98" using upper by arith
  note inlet = comma_symbolic_north_entry[OF lower upper exponent]
  note decided = comma_symbolic_decisive_entry_packet[OF sector exponent offset packet cut]
  note selected = comma_symbolic_north_selected_cut[OF lower upper exponent packet cut]
  show "comma_finite_step (p mod 924) (comma_finite_initial (Comma_N,a,p mod 924)) =
      Comma_Next (Comma_Entry a 0 (89+a))"
    using inlet(1) by (simp add: comma_finite_initial_def)
  show "comma_decisive_endpoint_packet (p mod 924) (Comma_Entry a 0 (89+a)) =
      (Comma_Near a 0 t,event)" by (rule decided(1))
  show "comma_literal_path (Suc j)
      (comma_chart_value p (comma_finite_initial (Comma_N,a,p mod 924)))
      (comma_writer_point (comma_first_sector_writer a p 0 (89+a) elapsed t) False j)"
    using selected(1) by (simp add: comma_finite_initial_def)
  show "comma_literal_path (elapsed-j)
      (comma_writer_point (comma_first_sector_writer a p 0 (89+a) elapsed t) False j)
      (comma_chart_value p (Comma_Near a 0 t))" by (rule selected(2))
qed


theorem comma_symbolic_zero_boundary_round:
  fixes a p elapsed t j :: nat and event :: comma_finite_move
  assumes lower: "2 \<le> a" and upper: "a \<le> 9" and exponent: "5 \<le> p"
    and packet: "comma_c1_first_sector a p 0 0 = (elapsed,t,event)"
    and cut: "j \<le> elapsed"
  shows "comma_decisive_endpoint_round (p mod 924)
      (comma_finite_initial (Comma_Z,a,p mod 924)) =
    (case event of
       Comma_Next next \<Rightarrow>
         if comma_round_crossing (Comma_Near a 0 t) next then Comma_Round_Cross next
         else comma_decisive_endpoint_round (p mod 924) next
     | Comma_Fork target delta \<Rightarrow> Comma_Round_Fork target delta
     | Comma_Landmine delta \<Rightarrow> Comma_Round_Landmine delta
     | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)"
proof -
  have admitted: "comma_round_admitted (comma_finite_initial (Comma_Z,a,p mod 924))"
    using lower upper by (simp add: comma_finite_initial_def)
  have selected: "comma_decisive_endpoint_packet (p mod 924)
      (comma_finite_initial (Comma_Z,a,p mod 924)) = (Comma_Near a 0 t,event)"
    using comma_symbolic_zero_boundary_source(1)[OF lower upper exponent packet cut] .
  show ?thesis using comma_decisive_endpoint_round_packet[OF admitted, of "p mod 924"] selected
    by (simp split: comma_finite_move.splits)
qed

theorem comma_symbolic_north_boundary_round_entry:
  fixes a p :: nat
  assumes lower: "2 \<le> a" and upper: "a \<le> 9"
  shows "comma_decisive_endpoint_round (p mod 924)
      (comma_finite_initial (Comma_N,a,p mod 924)) =
    comma_decisive_endpoint_round (p mod 924) (Comma_Entry a 0 (89+a))"
proof -
  let ?near = "Comma_Near (a-1) 0 1"
  let ?entry = "Comma_Entry a 0 (89+a)"
  have admitted: "comma_round_admitted ?near" using lower upper by (simp; arith)
  have next_step: "comma_finite_step (p mod 924) ?near = Comma_Next ?entry"
    using lower upper by (simp add: comma_near_control_formula Let_def; arith)
  have target: "comma_decisive_sector_target (p mod 924) ?near = ?near"
    using lower upper by (simp add: comma_decisive_sector_target.simps comma_near_closed_germ_def Let_def; arith)
  have selected: "comma_decisive_endpoint_packet (p mod 924) ?near = (?near,Comma_Next ?entry)"
    using target next_step by (simp add: comma_decisive_endpoint_packet_def comma_fast_step_correct Let_def)
  have not_cross: "\<not> comma_round_crossing ?near ?entry"
    using lower upper by (simp add: comma_round_crossing_def; arith)
  show ?thesis using comma_decisive_endpoint_round_packet[OF admitted, of "p mod 924"] selected not_cross
    by (simp add: comma_finite_initial_def)
qed

ML \<open>
  val checked = @{thms comma_symbolic_zero_boundary_source comma_symbolic_north_boundary_source
    comma_symbolic_zero_boundary_round comma_symbolic_north_boundary_round_entry};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Boundary source used an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Boundary source contains skipped proofs" else ();
  val _ = Comma_Proof_Dependency_Audit.require_paths @{context}
    "Boundary source excludes packed and occurrence authority"
    ["comma_frontier_m204_bellman_native", "comma_terminal_weight_decode",
     "comma_phase_class_survival_lengths", "comma_python_first_terminal_walk",
     "comma_round_close", "comma_finite_macro", "comma_python_writer_run",
     "comma_decade_summary_unique_occurrence_exists"] checked;
\<close>
end
