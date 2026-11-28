theory Comma_Symbolic_Boundary_Entry
  imports Comma_Symbolic_First_Sector_Writer
begin

text \<open>The North source begins at headroom one. Its first physical step is
an exact Entry source for the symbolic sector writer; the positive physical
clock and resulting source offset are kept in the conclusion.\<close>

theorem comma_symbolic_north_entry:
  fixes a p :: nat
  assumes lower: "2 \<le> a" and upper: "a \<le> 9" and exponent: "5 \<le> p"
  shows "comma_finite_step (p mod 924) (Comma_Near (a-1) 0 1) =
      Comma_Next (Comma_Entry a 0 (89+a))"
    and "comma_literal_path 1 (comma_chart_value p (Comma_Near (a-1) 0 1))
      (comma_chart_value p (Comma_Entry a 0 (89+a)))"
    and "comma_large_children (a-1) p (comma_chart_value p (Comma_Near (a-1) 0 1)) =
      [comma_chart_value p (Comma_Entry a 0 (89+a))]"
    and "89+a \<le> 98"
proof -
  have sector: "1 \<le> a-1" "a-1 \<le> 9" using lower upper by arith+
  have step: "comma_finite_step (p mod 924) (Comma_Near (a-1) 0 1) =
      Comma_Next (Comma_Entry a 0 (89+a))"
    using lower upper by (simp add: comma_near_control_formula Let_def; arith)
  note physical = comma_near_chart_next_literal[OF sector exponent _ _ step]
  show "comma_finite_step (p mod 924) (Comma_Near (a-1) 0 1) =
      Comma_Next (Comma_Entry a 0 (89+a))" by (rule step)
  show "comma_literal_path 1 (comma_chart_value p (Comma_Near (a-1) 0 1))
      (comma_chart_value p (Comma_Entry a 0 (89+a)))"
    using physical(1) by simp
  show "comma_large_children (a-1) p (comma_chart_value p (Comma_Near (a-1) 0 1)) =
      [comma_chart_value p (Comma_Entry a 0 (89+a))]"
    using physical(3) by simp
  show "89+a \<le> 98" using upper by arith
qed


theorem comma_symbolic_north_selected_cut:
  fixes a p elapsed t j :: nat and event :: comma_finite_move
  assumes lower: "2 \<le> a" and upper: "a \<le> 9" and exponent: "5 \<le> p"
    and packet: "comma_c1_first_sector a p 0 (89+a) = (elapsed,t,event)"
    and cut: "j \<le> elapsed"
  shows "comma_literal_path (Suc j)
      (comma_chart_value p (Comma_Near (a-1) 0 1))
      (comma_writer_point (comma_first_sector_writer a p 0 (89+a) elapsed t) False j)"
    and "comma_literal_path (elapsed-j)
      (comma_writer_point (comma_first_sector_writer a p 0 (89+a) elapsed t) False j)
      (comma_chart_value p (Comma_Near a 0 t))"
proof -
  have sector: "1 \<le> a" "a \<le> 9" using lower upper by arith+
  have offset: "89+a \<le> 98" using upper by arith
  note first = comma_symbolic_north_entry[OF lower upper exponent]
  note cut = comma_first_sector_writer_selected_cut[OF sector exponent offset packet cut]
  note combined = comma_literal_path_append[OF first(2) cut(1)]
  show "comma_literal_path (Suc j)
      (comma_chart_value p (Comma_Near (a-1) 0 1))
      (comma_writer_point (comma_first_sector_writer a p 0 (89+a) elapsed t) False j)"
    using combined by simp
  show "comma_literal_path (elapsed-j)
      (comma_writer_point (comma_first_sector_writer a p 0 (89+a) elapsed t) False j)
      (comma_chart_value p (Comma_Near a 0 t))" by (rule cut(2))
qed

ML \<open>
  val checked = @{thms comma_symbolic_north_entry comma_symbolic_north_selected_cut};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "North source used an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "North source has skipped proofs" else ();
\<close>
end
